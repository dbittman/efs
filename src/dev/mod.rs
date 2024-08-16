//! Everything related to the devices.

use alloc::borrow::{Cow, ToOwned};
use alloc::boxed::Box;
use alloc::slice;
use alloc::vec::Vec;
use core::iter::Step;
use core::mem::{size_of, transmute_copy};
use core::ops::{Deref, DerefMut, Range};
use core::ptr::{addr_of, slice_from_raw_parts};

use self::sector::Address;
use self::size::Size;
use crate::arch::usize_to_u64;
use crate::dev::error::DevError;
use crate::error::Error;
use crate::io::{Read, Seek, SeekFrom, Write};
// use crate::io::{Base, Read, Seek, SeekFrom, Write};

pub mod error;
pub mod sector;
pub mod size;

/// Slice of a device, filled with objects of type `T`.
#[derive(Debug, Clone)]
pub struct Slice<'mem, T: Clone> {
    /// Elements of the slice.
    inner: Cow<'mem, [T]>,

    /// Starting address of the slice.
    starting_addr: Address,
}

impl<'mem, T: Clone> AsRef<[T]> for Slice<'mem, T> {
    fn as_ref(&self) -> &[T] {
        &self.inner
    }
}

impl<'mem, T: Clone> AsMut<[T]> for Slice<'mem, T> {
    fn as_mut(&mut self) -> &mut [T] {
        self.inner.to_mut().as_mut()
    }
}

impl<'mem, T: Clone> Deref for Slice<'mem, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<'mem, T: Clone> DerefMut for Slice<'mem, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut()
    }
}

impl<'mem, T: Clone> Slice<'mem, T> {
    /// Creates a new [`Slice`].
    #[must_use]
    pub const fn new(inner: &'mem [T], starting_addr: Address) -> Self {
        Self {
            inner: Cow::Borrowed(inner),
            starting_addr,
        }
    }

    /// Creates a new [`Slice`] from [`ToOwned::Owned`] objects.
    #[must_use]
    pub const fn new_owned(inner: <[T] as ToOwned>::Owned, starting_addr: Address) -> Self {
        Self {
            inner: Cow::Owned(inner),
            starting_addr,
        }
    }

    /// Returns the starting address of the slice.
    #[must_use]
    pub const fn addr(&self) -> Address {
        self.starting_addr
    }

    /// Checks whether the slice has been mutated or not.
    #[must_use]
    pub const fn is_mutated(&self) -> bool {
        match self.inner {
            Cow::Borrowed(_) => false,
            Cow::Owned(_) => true,
        }
    }

    /// Commits the write operations onto the slice and returns a [`Commit`]ed object.
    #[must_use]
    pub fn commit(self) -> Commit<T> {
        Commit::new(self.inner.into_owned(), self.starting_addr)
    }
}

impl<'mem> Slice<'mem, u8> {
    /// Returns the content of this slice as an object `T`.
    ///
    /// # Safety
    ///
    /// Must ensure that an instance of `T` is located at the begining of the slice and that the length of the slice is greater than
    /// the memory size of `T`.
    ///
    /// # Panics
    ///
    /// Panics if the starting address cannot be read.

    #[must_use]
    pub unsafe fn cast<T: Copy>(&self) -> T {
        assert!(self.inner.len() >= size_of::<T>(), "The length of the device slice is not great enough to contain an object T");
        transmute_copy(self.inner.as_ptr().as_ref().expect("Could not read the pointer of the slice"))
    }

    /// Creates a [`Slice`] from any [`Copy`] object
    pub fn from<T: Copy>(object: T, starting_addr: Address) -> Self {
        let len = size_of::<T>();
        let ptr = addr_of!(object).cast::<u8>();
        // SAFETY: the pointer is well-formed since it has been created above
        let inner_opt = unsafe { slice_from_raw_parts(ptr, len).as_ref::<'mem>() };
        // SAFETY: `inner_opt` cannot be `None` as `ptr` contains data and the call to `slice_from_raw_parts` should not return a
        // null pointer
        Self::new(unsafe { inner_opt.unwrap_unchecked() }, starting_addr)
    }
}

/// Commited slice of a device, filled with objects of type `T`.
#[derive(Debug, Clone)]
pub struct Commit<T: Clone> {
    /// Elements of the commit.
    inner: Vec<T>,

    /// Starting address of the slice.
    starting_addr: Address,
}

impl<T: Clone> Commit<T> {
    /// Creates a new [`Commit`] instance.
    #[must_use]
    pub const fn new(inner: Vec<T>, starting_addr: Address) -> Self {
        Self {
            inner,
            starting_addr,
        }
    }

    /// Returns the starting address of the commit.
    #[must_use]
    pub const fn addr(&self) -> Address {
        self.starting_addr
    }
}

impl<T: Clone> AsRef<[T]> for Commit<T> {
    fn as_ref(&self) -> &[T] {
        &self.inner
    }
}

impl<T: Clone> AsMut<[T]> for Commit<T> {
    fn as_mut(&mut self) -> &mut [T] {
        self.inner.as_mut()
    }
}

/// General interface for devices containing a file system.
pub trait Device<T: Copy, FSE: core::error::Error> {
    /// [`Size`] description of this device.
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the size of the device cannot be determined.
    fn size(&mut self) -> Size;

    /// Returns a [`Slice`] with elements of this device.
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the read could not be completed.
    fn slice(&mut self, addr_range: Range<Address>) -> Result<Slice<'_, T>, Error<FSE>>;

    /// Writes the [`Commit`] onto the device.
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the write could not be completed.
    fn commit(&mut self, commit: Commit<T>) -> Result<(), Error<FSE>>;

    /// Read an element of type `O` on the device starting at the address `starting_addr`.
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the read tries to go out of the device's bounds or if [`Device::slice`] failed.
    ///
    /// # Safety
    ///
    /// Must verifies the safety conditions of [`core::ptr::read`].
    unsafe fn read_at<O: Copy>(&mut self, starting_addr: Address) -> Result<O, Error<FSE>> {
        let length = size_of::<O>();
        let range = starting_addr..Address::forward_checked(starting_addr, length).ok_or(Error::Device(DevError::OutOfBounds {
            structure: "address",
            value: usize_to_u64(starting_addr.index() + length).into(),
            lower_bound: 0,
            upper_bound: self.size().0.into(),
        }))?;
        let slice = self.slice(range)?;
        let ptr = slice.inner.as_ptr();
        Ok(ptr.cast::<O>().read())
    }

    /// Writes an element of type `O` on the device starting at the address `starting_addr`.
    ///
    /// Beware, the `object` **must be the owned `O` object and not a borrow**, otherwise the pointer to the object will be copied,
    /// and not the object itself.
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the read tries to go out of the device's bounds or if [`Device::slice`] or [`Device::commit`]
    /// failed.
    ///
    /// # Safety
    ///
    /// Must ensure that `size_of::<O>() % size_of::<T>() == 0`.
    unsafe fn write_at<O: Copy>(&mut self, starting_addr: Address, object: O) -> Result<(), Error<FSE>> {
        let length = size_of::<O>();
        assert_eq!(
            length % size_of::<T>(),
            0,
            "Cannot write an element whose memory size is not divisible by the memory size of the elements of the device"
        );
        assert!(length > 0, "Cannot write a 0-byte object on a device");
        let object_slice = slice::from_raw_parts(addr_of!(object).cast::<T>(), length / size_of::<T>());

        let range = starting_addr..Address::forward_checked(starting_addr, length).ok_or(Error::Device(DevError::OutOfBounds {
            structure: "address",
            value: usize_to_u64(starting_addr.index() + length).into(),
            lower_bound: 0,
            upper_bound: self.size().0.into(),
        }))?;
        let mut device_slice = self.slice(range)?;
        let buffer = device_slice
            .get_mut(..)
            .unwrap_or_else(|| unreachable!("It is always possible to take all the elements of a slice"));
        buffer.copy_from_slice(object_slice);

        let commit = device_slice.commit();
        self.commit(commit).map_err(Into::into)
    }
}

impl<FSE: core::error::Error, T: Read<IOError = FSE> + Write + Seek> Device<u8, FSE> for T {
    fn size(&mut self) -> Size {
        let offset = self.seek(SeekFrom::End(0)).expect("Could not seek the device at its end");
        let size = self
            .seek(SeekFrom::Start(offset))
            .expect("Could not seek the device at its original offset");
        Size(size)
    }

    fn slice(&mut self, addr_range: Range<Address>) -> Result<Slice<'_, u8>, Error<FSE>> {
        let starting_addr = addr_range.start;
        let len = TryInto::<usize>::try_into((addr_range.end - addr_range.start).index()).map_err(|_err| {
            Error::Device(DevError::OutOfBounds {
                structure: "addr range",
                value: usize_to_u64((addr_range.end - addr_range.start).index()).into(),
                lower_bound: 0,
                upper_bound: i128::MAX,
            })
        })?;

        let mut slice = alloc::vec![0; len];
        self.seek(SeekFrom::Start(starting_addr.index().try_into().expect("Could not convert `usize` to `u64`")))?;
        self.read_exact(&mut slice)?;

        Ok(Slice::new_owned(slice, starting_addr))
    }

    fn commit(&mut self, commit: Commit<u8>) -> Result<(), Error<FSE>> {
        let offset = self.seek(SeekFrom::Start(commit.addr().index().try_into().expect("Could not convert `usize` to `u64`")))?;
        self.write_all(commit.as_ref())?;
        self.seek(SeekFrom::Start(offset))?;

        Ok(())
    }
}

/// Generic implementation of the [`Device`] trait.
macro_rules! impl_device {
    ($volume:ty) => {
        impl<T: Copy, FSE: core::error::Error> Device<T, FSE> for $volume {
            fn size(&mut self) -> Size {
                Size(usize_to_u64(self.len()))
            }

            fn slice(&mut self, addr_range: Range<Address>) -> Result<Slice<'_, T>, Error<FSE>> {
                if Device::<T, FSE>::size(self) >= usize_to_u64(usize::from(addr_range.end)) {
                    let addr_start = addr_range.start;
                    let range = addr_range.start.index()..addr_range.end.index();
                    // SAFETY: it is checked above that the wanted elements exist
                    Ok(Slice::new(unsafe { <Self as AsRef<[T]>>::as_ref(self).get_unchecked(range) }, addr_start))
                } else {
                    Err(Error::Device(DevError::OutOfBounds {
                        structure: "address",
                        value: usize_to_u64(addr_range.end.index()).into(),
                        lower_bound: 0,
                        upper_bound: <Self as Device<T, FSE>>::size(self).0.into(),
                    }))
                }
            }

            fn commit(&mut self, commit: Commit<T>) -> Result<(), Error<FSE>> {
                let addr_start = commit.addr().index();
                let addr_end = addr_start + commit.as_ref().len();

                let self_len = usize_to_u64(self.len()).into();

                let dest = &mut <Self as AsMut<[T]>>::as_mut(self).get_mut(addr_start..addr_end).ok_or_else(|| {
                    // SAFETY: `usize::MAX <= i128::MAX`
                    Error::Device(DevError::OutOfBounds {
                        structure: "address",
                        value: usize_to_u64(addr_end).into(),
                        lower_bound: 0,
                        upper_bound: self_len,
                    })
                })?;
                dest.clone_from_slice(&commit.as_ref());
                Ok(())
            }
        }
    };
}

impl_device!(&mut [T]);
impl_device!(Vec<T>);
impl_device!(Box<[T]>);

#[cfg(feature = "std")]
impl<FSE: core::error::Error> Device<u8, FSE> for std::fs::File {
    fn size(&mut self) -> Size {
        let metadata = self.metadata().expect("Could not read the file");
        Size(metadata.len())
    }

    fn slice(&mut self, addr_range: Range<Address>) -> Result<Slice<'_, u8>, Error<FSE>> {
        let starting_addr = addr_range.start;
        let len = (addr_range.end - addr_range.start).index();
        let mut slice = alloc::vec![0; len];
        std::io::Seek::seek(
            self,
            std::io::SeekFrom::Start(starting_addr.index().try_into().expect("Could not convert `usize` to `u64`")),
        )?;
        std::io::Read::read_exact(self, &mut slice)?;
        Ok(Slice::new_owned(slice, starting_addr))
    }

    fn commit(&mut self, commit: Commit<u8>) -> Result<(), Error<FSE>> {
        let offset = std::io::Seek::seek(self, std::io::SeekFrom::Start(usize_to_u64(commit.addr().index())))?;
        std::io::Write::write_all(self, commit.as_ref()).expect("Could not write on the given file");
        std::io::Seek::seek(self, std::io::SeekFrom::Start(offset))?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use alloc::string::String;
    use alloc::vec;
    use core::fmt::Display;
    use core::mem::size_of;
    use core::ptr::addr_of;
    use core::slice;
    use std::fs;
    use std::io::{Read, Seek};

    use crate::arch::usize_to_u64;
    use crate::dev::sector::Address;
    use crate::dev::Device;
    use crate::tests::copy_file;

    #[derive(Debug)]
    struct Error;

    impl Display for Error {
        fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(formatter, "")
        }
    }

    impl core::error::Error for Error {}

    #[test]
    fn device_generic_read() {
        let mut device = vec![0_u8; 1024];
        let mut slice = Device::<u8, std::io::Error>::slice(&mut device, Address::from(256_u32)..Address::from(512_u32)).unwrap();
        slice.iter_mut().for_each(|element| *element = 1);

        let commit = slice.commit();

        assert!(Device::<u8, std::io::Error>::commit(&mut device, commit).is_ok());

        for (idx, &x) in device.iter().enumerate() {
            assert_eq!(x, u8::from((256..512).contains(&idx)));
        }
    }

    #[allow(clippy::missing_asserts_for_indexing)]
    #[test]
    fn device_file_write() {
        let mut file_1 = copy_file("./tests/dev/device_file_1.txt").unwrap();

        let mut slice = Device::<u8, Error>::slice(&mut file_1, Address::new(0)..Address::new(13)).unwrap();

        let word = slice.get_mut(6..=10).unwrap();
        word[0] = b'e';
        word[1] = b'a';
        word[2] = b'r';
        word[3] = b't';
        word[4] = b'h';

        let commit = slice.commit();
        Device::<u8, Error>::commit(&mut file_1, commit).unwrap();

        file_1.rewind().unwrap();

        let mut file_1_content = String::new();
        file_1.read_to_string(&mut file_1_content).unwrap();

        let file_2_content = String::from_utf8(fs::read("./tests/dev/device_file_2.txt").unwrap()).unwrap();

        assert_eq!(file_1_content, file_2_content);
    }

    #[allow(clippy::struct_field_names)]
    #[test]
    fn device_generic_read_at() {
        const OFFSET: usize = 123;

        #[repr(C)]
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        struct Test {
            nb_1: u16,
            nb_2: u8,
            nb_3: usize,
            nb_4: u128,
        }

        let test = Test {
            nb_1: 0xabcd,
            nb_2: 0x99,
            nb_3: 0x1234,
            nb_4: 0x1234_5678_90ab_cdef,
        };
        let test_bytes = unsafe { slice::from_raw_parts(addr_of!(test).cast::<u8>(), size_of::<Test>()) };

        let mut device = vec![0_u8; 1024];
        let mut slice =
            Device::<u8, std::io::Error>::slice(&mut device, Address::from(OFFSET)..Address::from(OFFSET + size_of::<Test>()))
                .unwrap();
        let buffer = slice.get_mut(..).unwrap();
        buffer.clone_from_slice(test_bytes);

        let commit = slice.commit();
        Device::<u8, std::io::Error>::commit(&mut device, commit).unwrap();

        let read_test = unsafe { Device::<u8, std::io::Error>::read_at::<Test>(&mut device, Address::from(OFFSET)).unwrap() };
        assert_eq!(test, read_test);
    }

    #[allow(clippy::struct_field_names)]
    #[test]
    fn device_generic_write_at() {
        const OFFSET: u64 = 123;

        #[repr(C)]
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        struct Test {
            nb_1: u16,
            nb_2: u8,
            nb_3: usize,
            nb_4: u128,
        }

        let test = Test {
            nb_1: 0xabcd,
            nb_2: 0x99,
            nb_3: 0x1234,
            nb_4: 0x1234_5678_90ab_cdef,
        };
        let test_bytes = unsafe { slice::from_raw_parts(addr_of!(test).cast::<u8>(), size_of::<Test>()) };

        let mut device = vec![0_u8; 1024];
        unsafe {
            Device::<u8, std::io::Error>::write_at(&mut device, Address::from(OFFSET), test).unwrap();
        };

        let slice = Device::<u8, std::io::Error>::slice(
            &mut device,
            Address::from(OFFSET)..Address::from(OFFSET + usize_to_u64(size_of::<Test>())),
        )
        .unwrap();

        assert_eq!(test_bytes, slice.as_ref());
    }
}
