//! Interface to manipulate UNIX files on an ext2 filesystem.

use alloc::borrow::ToOwned;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt::Debug;
use core::ptr::{addr_of, addr_of_mut, slice_from_raw_parts};

use itertools::Itertools;

use super::directory::Entry;
use super::error::Ext2Error;
use super::inode::{Inode, TypePermissions};
use super::{Celled, Ext2};
use crate::dev::sector::Address;
use crate::dev::Device;
use crate::error::Error;
use crate::file::{self, DirectoryEntry, Stat, TypeWithFile};
use crate::fs::error::FsError;
use crate::fs::ext2::block::Block;
use crate::fs::ext2::indirection::IndirectedBlocks;
use crate::fs::ext2::inode::DIRECT_BLOCK_POINTER_COUNT;
use crate::fs::PATH_MAX;
use crate::io::{Base, Read, Seek, SeekFrom, Write};
use crate::types::{Blkcnt, Blksize, Gid, Ino, Mode, Nlink, Off, Time, Timespec, Uid};

/// Limit in bytes for the length of a pointed path of a symbolic link to be store in an inode and not in a separate data block.
pub const SYMBOLIC_LINK_INODE_STORE_LIMIT: usize = 60;

/// General file implementation.
pub struct File<Dev: Device<u8, Ext2Error>> {
    /// Ext2 object associated with the device containing this file.
    filesystem: Celled<Ext2<Dev>>,

    /// Inode number of the inode corresponding to the file.
    inode_number: u32,

    /// Inode corresponding to the file.
    inode: Inode,

    /// Read/Write offset in bytes (can be manipulated with [`Seek`]).
    io_offset: u64,
}

impl<Dev: Device<u8, Ext2Error>> Debug for File<Dev> {
    #[inline]
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("File")
            .field("device_id", &self.filesystem.borrow().device_id)
            .field("inode_number", &self.inode_number)
            .field("inode", &self.inode)
            .field("io_offset", &self.io_offset)
            .finish()
    }
}

impl<Dev: Device<u8, Ext2Error>> File<Dev> {
    /// Returns a new ext2's [`File`] from an [`Ext2`] instance and the inode number of the file.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Inode::parse`].
    #[inline]
    pub fn new(filesystem: &Celled<Ext2<Dev>>, inode_number: u32) -> Result<Self, Error<Ext2Error>> {
        let fs = filesystem.borrow();
        let inode = Inode::parse(&fs.device, &fs.superblock, inode_number)?;
        Ok(Self {
            filesystem: filesystem.clone(),
            inode_number,
            inode,
            io_offset: 0,
        })
    }

    /// Updates the inner [`Inode`].
    fn update_inner_inode(&mut self) -> Result<(), Error<Ext2Error>> {
        let fs = self.filesystem.borrow();
        self.inode = Inode::parse(&fs.device, &fs.superblock, self.inode_number)?;
        Ok(())
    }

    ///  Sets the file's inode to the given object.
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the device cannot be written.
    ///
    /// # Safety
    ///
    /// Must ensure that the given inode is coherent with the current state of the filesystem.
    unsafe fn set_inode(&mut self, inode: &Inode) -> Result<(), Error<Ext2Error>> {
        let fs = self.filesystem.borrow();
        let celled_device = fs.device.clone();

        let starting_addr = Inode::starting_addr(&celled_device, fs.superblock(), self.inode_number)?;

        let mut device = fs.device.borrow_mut();
        device.write_at(starting_addr, *inode)?;

        drop(device);
        drop(fs);

        self.update_inner_inode()?;

        Ok(())
    }

    /// General implementation of [`truncate`](file::Regular::truncate) for ext2's [`File`].
    ///
    /// # Errors
    ///
    /// Same as [`truncate`](file::Regular::truncate).
    #[inline]
    pub fn truncate(&mut self, size: u64) -> Result<(), Error<Ext2Error>> {
        // TODO: deallocate unused blocks

        if u64::from(self.inode.size) <= size {
            return Ok(());
        }

        let fs = self.filesystem.borrow();

        let mut new_inode = self.inode;
        // SAFETY: the result is smaller than `u32::MAX`
        new_inode.size = unsafe { u32::try_from(u64::from(u32::MAX) & size).unwrap_unchecked() };

        let starting_addr = Inode::starting_addr(&fs.device, fs.superblock(), self.inode_number)?;

        // SAFETY: this writes an inode at the starting address of the inode
        unsafe {
            fs.device.borrow_mut().write_at(starting_addr, new_inode)?;
        };

        drop(fs);

        self.update_inner_inode()
    }

    /// Reads all the content of the file and returns it in a byte vector.
    ///
    /// Does not move the offset for I/O operations used by [`Seek`].
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Inode::read_data`].
    ///
    /// # Panics
    ///
    /// This function panics if the total size of the file cannot be loaded in RAM.
    #[inline]
    pub fn read_all(&mut self) -> Result<Vec<u8>, Error<Ext2Error>> {
        let mut buffer = vec![
            0_u8;
            self.inode
                .data_size()
                .try_into()
                .expect("The size of the file's content is greater than the size representable on this computer.")
        ];
        let previous_offset = self.seek(SeekFrom::Start(0))?;
        self.read(&mut buffer)?;
        self.seek(SeekFrom::Start(previous_offset))?;
        Ok(buffer)
    }
}

impl<Dev: Device<u8, Ext2Error>> file::File for File<Dev> {
    type Error = Ext2Error;

    #[inline]
    fn stat(&self) -> file::Stat {
        let filesystem = self.filesystem.borrow();

        Stat {
            dev: crate::types::Dev(filesystem.device_id),
            ino: Ino(self.inode_number),
            mode: Mode(self.inode.mode),
            nlink: Nlink(u32::from(self.inode.links_count)),
            uid: Uid(self.inode.uid),
            gid: Gid(self.inode.gid),
            rdev: crate::types::Dev::default(),
            size: Off(self.inode.data_size().try_into().unwrap_or_default()),
            atim: Timespec {
                tv_sec: Time(self.inode.atime.try_into().unwrap_or_default()),
                tv_nsec: i32::default(),
            },
            mtim: Timespec {
                tv_sec: Time(self.inode.mtime.try_into().unwrap_or_default()),
                tv_nsec: i32::default(),
            },
            ctim: Timespec {
                tv_sec: Time(self.inode.ctime.try_into().unwrap_or_default()),
                tv_nsec: i32::default(),
            },
            blksize: Blksize(filesystem.superblock.block_size().try_into().unwrap_or_default()),
            blkcnt: Blkcnt(self.inode.blocks.try_into().unwrap_or_default()),
        }
    }

    #[inline]
    fn get_type(&self) -> file::Type {
        // SAFETY: the file type as been checked during the inode's parse
        unsafe { self.inode.file_type().unwrap_unchecked() }
    }

    fn set_mode(&mut self, mode: Mode) -> Result<(), Error<Self::Error>> {
        let mut new_inode = self.inode;
        new_inode.mode = *mode;
        // SAFETY: only the mode has changed
        unsafe { self.set_inode(&new_inode) }
    }

    fn set_uid(&mut self, uid: Uid) -> Result<(), Error<Self::Error>> {
        let mut new_inode = self.inode;
        new_inode.uid = *uid;
        // SAFETY: only the UID has changed
        unsafe { self.set_inode(&new_inode) }
    }

    fn set_gid(&mut self, gid: Gid) -> Result<(), Error<Self::Error>> {
        let mut new_inode = self.inode;
        new_inode.gid = *gid;
        // SAFETY: only the GID has changed
        unsafe { self.set_inode(&new_inode) }
    }
}

/// Implementation of a regular file.
#[derive(Debug)]
pub struct Regular<Dev: Device<u8, Ext2Error>> {
    /// Inner file containing the regular file.
    file: File<Dev>,
}

impl<Dev: Device<u8, Ext2Error>> Base for File<Dev> {
    type IOError = Ext2Error;
}

impl<Dev: Device<u8, Ext2Error>> Read for File<Dev> {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Error<Self::IOError>> {
        let filesystem = self.filesystem.borrow();
        self.inode
            .read_data(&filesystem.device, &filesystem.superblock, buf, self.io_offset)
            .map(|bytes| {
                self.io_offset += bytes as u64;
                bytes
            })
    }
}

impl<Dev: Device<u8, Ext2Error>> Write for File<Dev> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> Result<usize, Error<Self::IOError>> {
        let mut fs = self.filesystem.borrow_mut();
        let superblock = fs.superblock().clone();
        let block_size = u64::from(fs.superblock().block_size());

        let buf_len = buf.len();
        if buf_len as u64 > fs.superblock().max_file_size() {
            return Err(Error::Fs(FsError::Implementation(Ext2Error::OutOfBounds(buf_len as i128))));
        }

        // Calcul of the number of needed data blocks
        let bytes_to_write = buf_len as u64;
        let data_blocks_needed =
            // SAFETY: there are at most u32::MAX blocks on the filesystem
            1 + unsafe { u32::try_from((bytes_to_write + self.io_offset - 1) / block_size).unwrap_unchecked() };

        let indirected_blocks = self.inode.indirected_blocks(&fs.device, fs.superblock())?;

        let current_data_block_count = indirected_blocks.data_block_count();
        let data_blocks_to_request = data_blocks_needed.saturating_sub(current_data_block_count);

        let current_indirection_block_count = indirected_blocks.indirection_block_count();
        let indirection_blocks_to_request = IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::necessary_indirection_block_count(
            data_blocks_needed,
            fs.superblock().base().block_size() / 4,
        ) - current_indirection_block_count;

        let start_block_group = indirected_blocks.last_data_block_allocated().map(|(block, _)| block).unwrap_or_default()
            / superblock.base().blocks_per_group;

        #[allow(clippy::wildcard_enum_match_arm)]
        let free_blocks = fs.free_blocks_offset(data_blocks_to_request + indirection_blocks_to_request, start_block_group)?;

        fs.allocate_blocks(&free_blocks)?;

        drop(fs);

        let (new_indirected_blocks, changed_blocks) = indirected_blocks.append_blocks_with_difference(
            &free_blocks,
            // SAFETY: this result points to a block which is encoded on 32 bits
            Some(unsafe { u32::try_from(self.io_offset / u64::from(superblock.block_size())).unwrap_unchecked() }),
        );

        for (starting_index, (indirection_block, blocks)) in changed_blocks.changed_indirected_blocks() {
            let mut block = Block::new(self.filesystem.clone(), indirection_block);
            if starting_index != 0 {
                block.seek(SeekFrom::Start(starting_index as u64))?;
            }

            // SAFETY: it is always possible to cast a u32 to 4 u8
            block.write_all(unsafe { &*slice_from_raw_parts(blocks.as_ptr().cast::<u8>(), blocks.len() * 4) })?;
        }

        let mut written_bytes = 0_usize;

        let changed_data_blocks = changed_blocks.changed_data_blocks();
        let changed_data_blocks_iterator = &mut changed_data_blocks.iter();

        if let Some(block_number) = changed_data_blocks_iterator.next() {
            let mut block = Block::new(self.filesystem.clone(), *block_number);
            block.seek(SeekFrom::Start(self.io_offset % u64::from(superblock.block_size())))?;
            written_bytes += block.write(buf)?;
        }

        for block_number in changed_data_blocks_iterator {
            let mut block = Block::new(self.filesystem.clone(), *block_number);
            let buffer_end = buf
                .get(written_bytes..written_bytes + (superblock.base().blocks_per_group as usize).min(buf_len - written_bytes))
                .expect("The buffer have a size that does not correspond to the calculated number of data blocks.");

            let new_written_bytes = block.write(buffer_end)?;
            if new_written_bytes == 0 {
                break;
            }
            written_bytes += new_written_bytes;
        }

        let mut updated_inode = self.inode;

        let (
            mut direct_block_pointers,
            singly_indirected_block_pointer,
            doubly_indirected_block_pointer,
            triply_indirected_block_pointer,
        ) = new_indirected_blocks.blocks();

        direct_block_pointers.append(&mut vec![0_u32; 12].into_iter().take(12 - direct_block_pointers.len()).collect_vec());

        let mut updated_direct_block_pointers = updated_inode.direct_block_pointers;
        updated_direct_block_pointers.clone_from_slice(&direct_block_pointers);
        updated_inode.direct_block_pointers = updated_direct_block_pointers;

        updated_inode.singly_indirect_block_pointer = singly_indirected_block_pointer.0;
        updated_inode.doubly_indirect_block_pointer = doubly_indirected_block_pointer.0;
        updated_inode.triply_indirect_block_pointer = triply_indirected_block_pointer.0;

        let new_size = self.inode.data_size().max(self.io_offset + buf_len as u64);

        // SAFETY: the result cannot be greater than `u32::MAX`
        updated_inode.size = unsafe { u32::try_from(new_size & u64::from(u32::MAX)).unwrap_unchecked() };
        updated_inode.blocks = data_blocks_needed * self.filesystem.borrow().superblock().block_size() / 512;

        assert!(u32::try_from(new_size).is_ok(), "TODO: Search how to deal with bigger files");

        // SAFETY: the updated inode contains the right inode created in this function
        unsafe { self.set_inode(&updated_inode) }?;

        Ok(written_bytes)
    }

    #[inline]
    fn flush(&mut self) -> Result<(), Error<Ext2Error>> {
        Ok(())
    }
}

impl<Dev: Device<u8, Ext2Error>> Seek for File<Dev> {
    #[inline]
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Error<Ext2Error>> {
        // SAFETY: it is safe to assume that the file length is smaller than 2^63 bytes long
        let file_length = unsafe { i64::try_from(self.inode.data_size()).unwrap_unchecked() };

        let previous_offset = self.io_offset;
        match pos {
            SeekFrom::Start(offset) => self.io_offset = offset,
            SeekFrom::End(back_offset) => {
                self.io_offset = TryInto::<u64>::try_into(file_length + back_offset)
                    .map_err(|_err| Ext2Error::OutOfBounds(i128::from(file_length - back_offset)))?;
            },
            SeekFrom::Current(add_offset) => {
                // SAFETY: it is safe to assume that the file has a length smaller than 2^64 bytes.
                self.io_offset = (unsafe { TryInto::<i64>::try_into(previous_offset).unwrap_unchecked() } + add_offset)
                    .try_into()
                    .map_err(|_err| {
                        Ext2Error::OutOfBounds(i128::from(
                            // SAFETY: it is safe to assume that the file has a length smaller than 2^64 bytes.
                            unsafe { TryInto::<i64>::try_into(previous_offset).unwrap_unchecked() } + add_offset,
                        ))
                    })?;
            },
        };

        if self.io_offset > self.inode.data_size() {
            Err(Error::Fs(FsError::Implementation(Ext2Error::OutOfBounds(self.io_offset.into()))))
        } else {
            Ok(previous_offset)
        }
    }
}

impl<Dev: Device<u8, Ext2Error>> Regular<Dev> {
    /// Returns a new ext2's [`Regular`] from an [`Ext2`] instance and the inode number of the file.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Ext2::inode`].
    #[inline]
    pub fn new(filesystem: &Celled<Ext2<Dev>>, inode_number: u32) -> Result<Self, Error<Ext2Error>> {
        Ok(Self {
            file: File::new(&filesystem.clone(), inode_number)?,
        })
    }

    /// Reads all the content of the file and returns it in a byte vector.
    ///
    /// Does not move the offset for I/O operations used by [`Seek`].
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Inode::read_data`].
    ///
    /// # Panics
    ///
    /// This function panics if the total size of the file cannot be loaded in RAM.
    #[inline]
    pub fn read_all(&mut self) -> Result<Vec<u8>, Error<Ext2Error>> {
        self.file.read_all()
    }
}

impl<Dev: Device<u8, Ext2Error>> file::File for Regular<Dev> {
    type Error = Ext2Error;

    #[inline]
    fn stat(&self) -> Stat {
        self.file.stat()
    }

    #[inline]
    fn get_type(&self) -> file::Type {
        self.file.get_type()
    }

    #[inline]
    fn set_mode(&mut self, mode: Mode) -> Result<(), Error<Self::Error>> {
        self.file
            .set_mode(Mode((TypePermissions::from_bits_truncate(*mode) | TypePermissions::from(self.file.get_type())).bits()))
    }

    #[inline]
    fn set_uid(&mut self, uid: Uid) -> Result<(), Error<Self::Error>> {
        self.file.set_uid(uid)
    }

    #[inline]
    fn set_gid(&mut self, gid: Gid) -> Result<(), Error<Self::Error>> {
        self.file.set_gid(gid)
    }
}

impl<Dev: Device<u8, Ext2Error>> Base for Regular<Dev> {
    type IOError = Ext2Error;
}

impl<Dev: Device<u8, Ext2Error>> Read for Regular<Dev> {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Error<Ext2Error>> {
        self.file.read(buf)
    }
}

impl<Dev: Device<u8, Ext2Error>> Write for Regular<Dev> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> Result<usize, Error<Ext2Error>> {
        self.file.write(buf)
    }

    #[inline]
    fn flush(&mut self) -> Result<(), Error<Ext2Error>> {
        self.file.flush()
    }
}

impl<Dev: Device<u8, Ext2Error>> Seek for Regular<Dev> {
    #[inline]
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Error<Ext2Error>> {
        self.file.seek(pos)
    }
}

impl<Dev: Device<u8, Ext2Error>> file::Regular for Regular<Dev> {
    #[inline]
    fn truncate(&mut self, size: u64) -> Result<(), Error<<Self as file::File>::Error>> {
        self.file.truncate(size)
    }
}

/// Interface for ext2's directories.
#[derive(Debug)]
pub struct Directory<Dev: Device<u8, Ext2Error>> {
    /// Inner file containing the regular file.
    file: File<Dev>,

    /// Entries contained in this directory.
    entries: Vec<Entry>,
}

impl<Dev: Device<u8, Ext2Error>> Directory<Dev> {
    /// Returns the directory located at the given inode number.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Entry::parse`].
    #[inline]
    pub fn new(filesystem: &Celled<Ext2<Dev>>, inode_number: u32) -> Result<Self, Error<Ext2Error>> {
        let file = File::new(filesystem, inode_number)?;
        let fs = filesystem.borrow();

        let mut entries = Vec::new();

        let mut accumulated_size = 0_u64;
        while accumulated_size < file.inode.data_size() {
            // SAFETY: a directory will be generally one or two blocks long, it is very unlikely to have 2^32 bytes worth of entries
            let starting_addr = Address::from(unsafe {
                usize::try_from(u64::from(file.inode.direct_block_pointers[0] * fs.superblock().block_size()) + accumulated_size)
                    .unwrap_unchecked()
            });
            // SAFETY: `starting_addr` contains the beginning of an entry
            let entry = unsafe { Entry::parse(&fs.device, starting_addr) }?;
            accumulated_size += u64::from(entry.rec_len);
            entries.push(entry);
        }

        Ok(Self { file, entries })
    }
}

impl<Dev: Device<u8, Ext2Error>> file::File for Directory<Dev> {
    type Error = Ext2Error;

    #[inline]
    fn stat(&self) -> Stat {
        self.file.stat()
    }

    #[inline]
    fn get_type(&self) -> file::Type {
        self.file.get_type()
    }

    #[inline]
    fn set_mode(&mut self, mode: Mode) -> Result<(), Error<Self::Error>> {
        self.file.set_mode(mode)
    }

    #[inline]
    fn set_uid(&mut self, uid: Uid) -> Result<(), Error<Self::Error>> {
        self.file.set_uid(uid)
    }

    #[inline]
    fn set_gid(&mut self, gid: Gid) -> Result<(), Error<Self::Error>> {
        self.file.set_gid(gid)
    }
}

impl<Dev: Device<u8, Ext2Error>> file::Directory for Directory<Dev> {
    type BlockDev = BlockDevice<Dev>;
    type CharDev = CharacterDevice<Dev>;
    type Fifo = Fifo<Dev>;
    type Regular = Regular<Dev>;
    type Socket = Socket<Dev>;
    type SymbolicLink = SymbolicLink<Dev>;

    #[inline]
    fn entries(&self) -> Result<Vec<file::DirectoryEntry<Self>>, Error<Ext2Error>> {
        let mut entries = Vec::new();

        for entry in &self.entries {
            entries.push(DirectoryEntry {
                // SAFETY: it is checked at the entry creation that the name is a valid CString
                filename: unsafe { entry.name.clone().try_into().unwrap_unchecked() },
                file: self.file.filesystem.file(entry.inode)?,
            });
        }

        Ok(entries)
    }

    #[inline]
    fn add_entry(&mut self, entry: DirectoryEntry<Self>) -> Result<TypeWithFile<Self>, Error<Self::Error>> {
        todo!()
    }

    #[inline]
    fn remove_entry(&mut self, entry_name: crate::path::UnixStr) -> Result<(), Error<Self::Error>> {
        todo!()
    }
}

/// Interface for ext2's symbolic links.
#[derive(Debug)]
pub struct SymbolicLink<Dev: Device<u8, Ext2Error>> {
    /// Inner file containing the symbolic link.
    file: File<Dev>,

    /// Read/Write offset (can be manipulated with [`Seek`]).
    pointed_file: String,
}

impl<Dev: Device<u8, Ext2Error>> SymbolicLink<Dev> {
    /// Returns a new ext2's [`SymbolicLink`] from an [`Ext2`] instance and the inode number of the file.
    ///
    /// # Errors
    ///
    /// Returns a [`BadString`](Ext2Error::BadString) if the content of the given inode does not look like a valid path.
    ///
    /// Returns a [`NameTooLong`](crate::fs::error::FsError::NameTooLong) if the size of the inode's content is greater than
    /// [`PATH_MAX`].
    ///
    /// Otherwise, returns the same errors as [`Ext2::inode`].
    #[inline]
    pub fn new(filesystem: &Celled<Ext2<Dev>>, inode_number: u32) -> Result<Self, Error<Ext2Error>> {
        let fs = filesystem.borrow();
        let file = File::new(&filesystem.clone(), inode_number)?;

        let data_size = usize::try_from(file.inode.data_size()).unwrap_or(PATH_MAX);

        let mut buffer = vec![0_u8; data_size];

        if data_size < SYMBOLIC_LINK_INODE_STORE_LIMIT {
            // SAFETY: it is always possible to read a slice of u8
            buffer.clone_from_slice(unsafe {
                core::slice::from_raw_parts(addr_of!(file.inode.direct_block_pointers).cast(), data_size)
            });
        } else {
            let _: usize = file.inode.read_data(&fs.device, fs.superblock(), &mut buffer, 0)?;
        }
        let pointed_file = buffer.split(|char| *char == b'\0').next().ok_or(Ext2Error::BadString)?.to_vec();
        Ok(Self {
            file,
            pointed_file: String::from_utf8(pointed_file).map_err(|_err| Ext2Error::BadString)?,
        })
    }
}

impl<Dev: Device<u8, Ext2Error>> file::File for SymbolicLink<Dev> {
    type Error = Ext2Error;

    #[inline]
    fn stat(&self) -> Stat {
        self.file.stat()
    }

    #[inline]
    fn get_type(&self) -> file::Type {
        self.file.get_type()
    }

    #[inline]
    fn set_mode(&mut self, mode: Mode) -> Result<(), Error<Self::Error>> {
        self.file.set_mode(mode)
    }

    #[inline]
    fn set_uid(&mut self, uid: Uid) -> Result<(), Error<Self::Error>> {
        self.file.set_uid(uid)
    }

    #[inline]
    fn set_gid(&mut self, gid: Gid) -> Result<(), Error<Self::Error>> {
        self.file.set_gid(gid)
    }
}

impl<Dev: Device<u8, Ext2Error>> file::SymbolicLink for SymbolicLink<Dev> {
    #[inline]
    fn get_pointed_file(&self) -> Result<&str, Error<Self::Error>> {
        Ok(&self.pointed_file)
    }

    #[inline]
    fn set_pointed_file(&mut self, pointed_file: &str) -> Result<(), Error<Self::Error>> {
        let bytes = pointed_file.as_bytes();

        if bytes.len() > PATH_MAX {
            Err(Error::Fs(FsError::NameTooLong(pointed_file.to_owned())))
        } else if bytes.len() > SYMBOLIC_LINK_INODE_STORE_LIMIT {
            self.file.seek(SeekFrom::Start(0))?;
            self.file.write(bytes)?;
            self.file.truncate(bytes.len() as u64)
        } else {
            let mut new_inode = self.file.inode;
            // SAFETY: `bytes.len() < PATH_MAX << u32::MAX`
            new_inode.size = unsafe { u32::try_from(bytes.len()).unwrap_unchecked() };

            let data_ptr = addr_of_mut!(new_inode.blocks).cast::<u8>();
            // SAFETY: there are `SYMBOLIC_LINK_INODE_STORE_LIMIT` bytes available to store the data
            let data_slice = unsafe { core::slice::from_raw_parts_mut(data_ptr, bytes.len()) };
            data_slice.clone_from_slice(bytes);

            let fs = self.file.filesystem.borrow();
            let starting_addr = Inode::starting_addr(&fs.device, fs.superblock(), self.file.inode_number)?;
            // SAFETY: the starting address correspond to the one of this inode
            unsafe {
                fs.device.borrow_mut().write_at(starting_addr, new_inode)?;
            };

            drop(fs);

            self.file.update_inner_inode()
        }
    }
}

macro_rules! generic_file {
    ($id:ident) => {
        #[doc = concat!("Basic implementation of a [`", stringify!($id), "`](crate::file::", stringify!($id), ") for ext2.")]
        pub struct $id<Dev: Device<u8, Ext2Error>>(File<Dev>);

        impl<Dev: Device<u8, Ext2Error>> crate::file::File for $id<Dev> {
            type Error = Ext2Error;

            fn stat(&self) -> Stat {
                self.0.stat()
            }

            fn get_type(&self) -> file::Type {
                self.0.get_type()
            }

            fn set_mode(&mut self, mode: Mode) -> Result<(), Error<Self::Error>> {
                self.0.set_mode(mode)
            }

            fn set_uid(&mut self, uid: Uid) -> Result<(), Error<Self::Error>> {
                self.0.set_uid(uid)
            }

            fn set_gid(&mut self, gid: Gid) -> Result<(), Error<Self::Error>> {
                self.0.set_gid(gid)
            }
        }

        impl<Dev: Device<u8, Ext2Error>> $id<Dev> {
            #[doc = concat!("Returns a new ext2's [`", stringify!($id), "`] from an [`Ext2`] instance and the inode number of the file.")]
            ///
            /// # Errors
            ///
            /// Returns the same errors as [`File::new`].
            #[inline]
            pub fn new(filesystem: &Celled<Ext2<Dev>>, inode_number: u32) -> Result<Self, Error<Ext2Error>> {
                Ok(Self(File::new(filesystem, inode_number)?))
            }
        }

        impl<Dev: Device<u8, Ext2Error>> crate::file::$id for $id<Dev> {}
    };
}

generic_file!(Fifo);
generic_file!(CharacterDevice);
generic_file!(BlockDevice);
generic_file!(Socket);

#[cfg(test)]
mod test {
    use alloc::string::{String, ToString};
    use alloc::vec;
    use alloc::vec::Vec;
    use core::cell::RefCell;
    use std::fs::{self, File};

    use itertools::Itertools;

    use crate::dev::sector::Address;
    use crate::file::{Type, TypeWithFile};
    use crate::fs::ext2::directory::Entry;
    use crate::fs::ext2::file::Directory;
    use crate::fs::ext2::inode::{Inode, TypePermissions, ROOT_DIRECTORY_INODE};
    use crate::fs::ext2::superblock::Superblock;
    use crate::fs::ext2::{Celled, Ext2};
    use crate::io::{Seek, SeekFrom, Write};
    use crate::path::UnixStr;
    use crate::permissions::Permissions;
    use crate::types::{Gid, Mode, Uid};

    #[test]
    fn parse_root() {
        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/extended.ext2").unwrap());
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let root = Directory::new(&ext2, ROOT_DIRECTORY_INODE).unwrap();
        assert_eq!(
            root.entries
                .into_iter()
                .map(|entry| entry.name.to_string_lossy().to_string())
                .collect::<Vec<String>>(),
            vec![".", "..", "lost+found", "big_file", "symlink"]
        );
    }

    #[test]
    fn parse_root_entries() {
        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/extended.ext2").unwrap());
        let celled_file = Celled::new(file);
        let superblock = Superblock::parse(&celled_file).unwrap();
        let root_inode = Inode::parse(&celled_file, &superblock, ROOT_DIRECTORY_INODE).unwrap();

        let dot = unsafe {
            Entry::parse(&celled_file, Address::new((root_inode.direct_block_pointers[0] * superblock.block_size()) as usize))
        }
        .unwrap();
        let two_dots = unsafe {
            Entry::parse(
                &celled_file,
                Address::new((root_inode.direct_block_pointers[0] * superblock.block_size()) as usize + dot.rec_len as usize),
            )
        }
        .unwrap();
        let lost_and_found = unsafe {
            Entry::parse(
                &celled_file,
                Address::new(
                    (root_inode.direct_block_pointers[0] * superblock.block_size()) as usize
                        + (dot.rec_len + two_dots.rec_len) as usize,
                ),
            )
        }
        .unwrap();
        let big_file = unsafe {
            Entry::parse(
                &celled_file,
                Address::new(
                    (root_inode.direct_block_pointers[0] * superblock.block_size()) as usize
                        + (dot.rec_len + two_dots.rec_len + lost_and_found.rec_len) as usize,
                ),
            )
        }
        .unwrap();
        let symlink = unsafe {
            Entry::parse(
                &celled_file,
                Address::new(
                    (root_inode.direct_block_pointers[0] * superblock.block_size()) as usize
                        + (dot.rec_len + two_dots.rec_len + lost_and_found.rec_len + big_file.rec_len) as usize,
                ),
            )
        }
        .unwrap();

        assert_eq!(dot.name.as_c_str().to_string_lossy(), ".");
        assert_eq!(two_dots.name.as_c_str().to_string_lossy(), "..");
        assert_eq!(lost_and_found.name.as_c_str().to_string_lossy(), "lost+found");
        assert_eq!(big_file.name.as_c_str().to_string_lossy(), "big_file");
        assert_eq!(symlink.name.as_c_str().to_string_lossy(), "symlink");
    }

    #[test]
    fn parse_big_file_inode_data() {
        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/extended.ext2").unwrap());
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let root = Directory::new(&ext2, ROOT_DIRECTORY_INODE).unwrap();

        let fs = ext2.borrow();
        let big_file_inode_number = root
            .entries
            .iter()
            .find(|entry| entry.name.to_string_lossy() == "big_file")
            .unwrap()
            .inode;
        let big_file_inode = fs.inode(big_file_inode_number).unwrap();

        let singly_indirect_block_pointer = big_file_inode.singly_indirect_block_pointer;
        let doubly_indirect_block_pointer = big_file_inode.doubly_indirect_block_pointer;
        assert_ne!(singly_indirect_block_pointer, 0);
        assert_ne!(doubly_indirect_block_pointer, 0);

        assert_ne!(big_file_inode.data_size(), 0);

        for offset in 0_usize..1_024_usize {
            let mut buffer = [0_u8; 1_024];
            big_file_inode
                .read_data(&fs.device, fs.superblock(), &mut buffer, (offset * 1_024) as u64)
                .unwrap();

            assert_eq!(buffer.iter().all_equal_value(), Ok(&1));
        }

        let mut buffer = [0_u8; 1_024];
        big_file_inode.read_data(&fs.device, fs.superblock(), &mut buffer, 0x0010_0000).unwrap();
        assert_eq!(buffer.iter().all_equal_value(), Ok(&0));
    }

    #[test]
    fn read_file() {
        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/io_operations.ext2").unwrap());
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());

        let TypeWithFile::Directory(root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else {
            panic!("The root is always a directory.")
        };
        let TypeWithFile::Regular(mut foo) =
            crate::file::Directory::entry(&root, UnixStr::new("foo.txt").unwrap()).unwrap().unwrap()
        else {
            panic!("`foo.txt` has been created as a regular file")
        };

        assert_eq!(foo.file.read_all().unwrap(), b"Hello world!\n");
    }

    #[test]
    fn read_symlink() {
        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/extended.ext2").unwrap());
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let root = Directory::new(&ext2, ROOT_DIRECTORY_INODE).unwrap();

        let TypeWithFile::SymbolicLink(symlink) =
            crate::file::Directory::entry(&root, UnixStr::new("symlink").unwrap()).unwrap().unwrap()
        else {
            panic!("`symlink` has been created as a symbolic link")
        };

        assert_eq!(symlink.pointed_file, "big_file");
    }

    #[test]
    fn set_inode() {
        fs::copy("./tests/fs/ext2/io_operations.ext2", "./tests/fs/ext2/io_operations_copy_set_inode.ext2").unwrap();

        let file = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_copy_set_inode.ext2")
                .unwrap(),
        );
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let TypeWithFile::Directory(root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else {
            panic!("The root is always a directory.")
        };
        let TypeWithFile::Regular(mut foo) =
            crate::file::Directory::entry(&root, UnixStr::new("foo.txt").unwrap()).unwrap().unwrap()
        else {
            panic!("`foo.txt` has been created as a regular file")
        };

        let mut new_inode = foo.file.inode;
        new_inode.uid = 0x1234;
        new_inode.gid = 0x2345;
        new_inode.flags = 0xabcd;
        unsafe { foo.file.set_inode(&new_inode) }.unwrap();

        assert_eq!(foo.file.inode, Inode::parse(&ext2.borrow().device, ext2.borrow().superblock(), foo.file.inode_number).unwrap());
        assert_eq!(foo.file.inode, new_inode);

        fs::remove_file("./tests/fs/ext2/io_operations_copy_set_inode.ext2").unwrap();
    }

    #[test]
    fn write_file_dbp_replace_without_allocation() {
        fs::copy(
            "./tests/fs/ext2/io_operations.ext2",
            "./tests/fs/ext2/io_operations_copy_write_file_dbp_replace_without_allocation.ext2",
        )
        .unwrap();

        let file = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_copy_write_file_dbp_replace_without_allocation.ext2")
                .unwrap(),
        );
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let TypeWithFile::Directory(root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else {
            panic!("The root is always a directory.")
        };
        let TypeWithFile::Regular(mut foo) =
            crate::file::Directory::entry(&root, UnixStr::new("foo.txt").unwrap()).unwrap().unwrap()
        else {
            panic!("`foo.txt` has been created as a regular file")
        };

        foo.seek(SeekFrom::Start(6)).unwrap();
        let replace_text = b"earth";
        foo.write(replace_text).unwrap();
        foo.flush().unwrap();

        assert_eq!(foo.file.inode, Inode::parse(&ext2.borrow().device, ext2.borrow().superblock(), foo.file.inode_number).unwrap());

        assert_eq!(String::from_utf8(foo.read_all().unwrap()).unwrap(), "Hello earth!\n");

        fs::remove_file("./tests/fs/ext2/io_operations_copy_write_file_dbp_replace_without_allocation.ext2").unwrap();
    }

    #[test]
    fn write_file_dbp_extend_without_allocation() {
        fs::copy(
            "./tests/fs/ext2/io_operations.ext2",
            "./tests/fs/ext2/io_operations_copy_write_file_dbp_extend_without_allocation.ext2",
        )
        .unwrap();

        let file = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_copy_write_file_dbp_extend_without_allocation.ext2")
                .unwrap(),
        );
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let TypeWithFile::Directory(root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else {
            panic!("The root is always a directory.")
        };
        let TypeWithFile::Regular(mut foo) =
            crate::file::Directory::entry(&root, UnixStr::new("foo.txt").unwrap()).unwrap().unwrap()
        else {
            panic!("`foo.txt` has been created as a regular file")
        };

        foo.seek(SeekFrom::Start(6)).unwrap();
        let replace_text = b"earth!\nI love dogs!\n";
        foo.write(replace_text).unwrap();
        foo.flush().unwrap();

        assert_eq!(foo.file.inode, Inode::parse(&ext2.borrow().device, ext2.borrow().superblock(), foo.file.inode_number).unwrap());

        assert_eq!(foo.read_all().unwrap(), b"Hello earth!\nI love dogs!\n");

        fs::remove_file("./tests/fs/ext2/io_operations_copy_write_file_dbp_extend_without_allocation.ext2").unwrap();
    }

    #[test]
    fn write_file_dbp_extend_with_allocation() {
        const BYTES_TO_WRITE: usize = 12_000;

        fs::copy(
            "./tests/fs/ext2/io_operations.ext2",
            "./tests/fs/ext2/io_operations_copy_write_file_dbp_extend_with_allocation.ext2",
        )
        .unwrap();

        let file = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_copy_write_file_dbp_extend_with_allocation.ext2")
                .unwrap(),
        );
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let TypeWithFile::Directory(root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else {
            panic!("The root is always a directory.")
        };
        let TypeWithFile::Regular(mut foo) =
            crate::file::Directory::entry(&root, UnixStr::new("foo.txt").unwrap()).unwrap().unwrap()
        else {
            panic!("`foo.txt` has been created as a regular file")
        };

        let replace_text = &[b'a'; BYTES_TO_WRITE];
        foo.write(replace_text).unwrap();
        foo.flush().unwrap();

        assert_eq!(foo.file.inode, Inode::parse(&ext2.borrow().device, ext2.borrow().superblock(), foo.file.inode_number).unwrap());

        assert_eq!(foo.read_all().unwrap().len(), BYTES_TO_WRITE);
        assert_eq!(foo.read_all().unwrap().into_iter().all_equal_value(), Ok(b'a'));

        fs::remove_file("./tests/fs/ext2/io_operations_copy_write_file_dbp_extend_with_allocation.ext2").unwrap();
    }

    #[test]
    fn write_file_singly_indirect_block_pointer() {
        const BYTES_TO_WRITE: usize = 23_000;

        fs::copy(
            "./tests/fs/ext2/io_operations.ext2",
            "./tests/fs/ext2/io_operations_copy_write_file_singly_indirect_block_pointer.ext2",
        )
        .unwrap();

        let file = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_copy_write_file_singly_indirect_block_pointer.ext2")
                .unwrap(),
        );
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let TypeWithFile::Directory(root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else {
            panic!("The root is always a directory.")
        };
        let TypeWithFile::Regular(mut foo) =
            crate::file::Directory::entry(&root, UnixStr::new("foo.txt").unwrap()).unwrap().unwrap()
        else {
            panic!("`foo.txt` has been created as a regular file")
        };

        let mut replace_text = vec![];
        for i in 0..=u8::MAX {
            replace_text.append(&mut vec![i; BYTES_TO_WRITE / 256]);
        }
        replace_text.append(&mut vec![b'a'; BYTES_TO_WRITE - 256 * (BYTES_TO_WRITE / 256)]);

        foo.write(&replace_text).unwrap();
        foo.flush().unwrap();

        assert_eq!(foo.file.inode, Inode::parse(&ext2.borrow().device, ext2.borrow().superblock(), foo.file.inode_number).unwrap());
        assert_eq!(foo.read_all().unwrap().len(), BYTES_TO_WRITE);
        assert_eq!(foo.read_all().unwrap(), replace_text);

        fs::remove_file("./tests/fs/ext2/io_operations_copy_write_file_singly_indirect_block_pointer.ext2").unwrap();
    }

    #[test]
    fn write_file_doubly_indirect_block_pointer() {
        const BYTES_TO_WRITE: usize = 400_000;

        fs::copy(
            "./tests/fs/ext2/io_operations.ext2",
            "./tests/fs/ext2/io_operations_copy_write_file_doubly_indirect_block_pointer.ext2",
        )
        .unwrap();

        let file = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_copy_write_file_doubly_indirect_block_pointer.ext2")
                .unwrap(),
        );
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let TypeWithFile::Directory(root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else {
            panic!("The root is always a directory.")
        };
        let TypeWithFile::Regular(mut foo) =
            crate::file::Directory::entry(&root, UnixStr::new("foo.txt").unwrap()).unwrap().unwrap()
        else {
            panic!("`foo.txt` has been created as a regular file")
        };

        let mut replace_text = vec![];
        for i in 0..=u8::MAX {
            replace_text.append(&mut vec![i; BYTES_TO_WRITE / 256]);
        }
        replace_text.append(&mut vec![b'a'; BYTES_TO_WRITE - 256 * (BYTES_TO_WRITE / 256)]);

        foo.write(&replace_text).unwrap();
        foo.flush().unwrap();

        assert_eq!(foo.file.inode, Inode::parse(&ext2.borrow().device, ext2.borrow().superblock(), foo.file.inode_number).unwrap());
        assert_eq!(foo.read_all().unwrap().len(), BYTES_TO_WRITE);
        assert_eq!(foo.read_all().unwrap(), replace_text);

        fs::remove_file("./tests/fs/ext2/io_operations_copy_write_file_doubly_indirect_block_pointer.ext2").unwrap();
    }

    #[test]
    fn write_file_triply_indirect_block_pointer() {
        const BYTES_TO_WRITE: usize = 70_000_000;

        fs::copy(
            "./tests/fs/ext2/io_operations.ext2",
            "./tests/fs/ext2/io_operations_copy_write_file_triply_indirect_block_pointer.ext2",
        )
        .unwrap();

        let file = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_copy_write_file_triply_indirect_block_pointer.ext2")
                .unwrap(),
        );
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let TypeWithFile::Directory(root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else {
            panic!("The root is always a directory.")
        };
        let TypeWithFile::Regular(mut foo) =
            crate::file::Directory::entry(&root, UnixStr::new("foo.txt").unwrap()).unwrap().unwrap()
        else {
            panic!("`foo.txt` has been created as a regular file")
        };

        let mut replace_text = vec![b'a'; BYTES_TO_WRITE / 2];
        replace_text.append(&mut vec![b'b'; BYTES_TO_WRITE / 2]);
        foo.write(&replace_text).unwrap();
        foo.flush().unwrap();

        assert_eq!(foo.file.inode, Inode::parse(&ext2.borrow().device, ext2.borrow().superblock(), foo.file.inode_number).unwrap());
        assert_eq!(foo.read_all().unwrap().len(), BYTES_TO_WRITE);
        assert_eq!(foo.read_all().unwrap(), replace_text);

        fs::remove_file("./tests/fs/ext2/io_operations_copy_write_file_triply_indirect_block_pointer.ext2").unwrap();
    }

    #[test]
    fn write_file_twice() {
        const BYTES_TO_WRITE: usize = 23_000;

        fs::copy("./tests/fs/ext2/io_operations.ext2", "./tests/fs/ext2/io_operations_copy_write_file_twice.ext2").unwrap();

        let file = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_copy_write_file_twice.ext2")
                .unwrap(),
        );
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let TypeWithFile::Directory(root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else {
            panic!("The root is always a directory.")
        };
        let TypeWithFile::Regular(mut foo) =
            crate::file::Directory::entry(&root, UnixStr::new("foo.txt").unwrap()).unwrap().unwrap()
        else {
            panic!("`foo.txt` has been created as a regular file")
        };

        let mut replace_text = vec![];
        for i in 0..=u8::MAX {
            replace_text.append(&mut vec![i; BYTES_TO_WRITE / 256]);
        }
        replace_text.append(&mut vec![b'a'; BYTES_TO_WRITE - 256 * (BYTES_TO_WRITE / 256)]);

        foo.write(&replace_text[..BYTES_TO_WRITE / 2]).unwrap();
        foo.seek(SeekFrom::End(0)).unwrap();
        foo.write(&replace_text[BYTES_TO_WRITE / 2..]).unwrap();
        foo.flush().unwrap();

        assert_eq!(foo.file.inode, Inode::parse(&ext2.borrow().device, ext2.borrow().superblock(), foo.file.inode_number).unwrap());
        assert_eq!(foo.read_all().unwrap().len(), BYTES_TO_WRITE);
        assert_eq!(foo.read_all().unwrap(), replace_text);

        fs::remove_file("./tests/fs/ext2/io_operations_copy_write_file_twice.ext2").unwrap();
    }

    #[test]
    #[allow(clippy::similar_names)]
    fn file_mode() {
        fs::copy("./tests/fs/ext2/io_operations.ext2", "./tests/fs/ext2/io_operations_copy_file_mode.ext2").unwrap();

        let file = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_copy_file_mode.ext2")
                .unwrap(),
        );
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let TypeWithFile::Directory(root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else {
            panic!("The root is always a directory.")
        };
        let TypeWithFile::Regular(mut foo) =
            crate::file::Directory::entry(&root, UnixStr::new("foo.txt").unwrap()).unwrap().unwrap()
        else {
            panic!("`foo.txt` has been created as a regular file")
        };

        assert_eq!(crate::file::File::get_type(&foo), Type::Regular);
        assert_eq!(
            crate::file::File::permissions(&foo),
            Permissions::USER_READ | Permissions::USER_WRITE | Permissions::GROUP_READ | Permissions::OTHER_READ
        );

        crate::file::File::set_mode(&mut foo, Mode::from(Permissions::USER_READ | Permissions::USER_WRITE)).unwrap();
        crate::file::File::set_uid(&mut foo, Uid(1)).unwrap();
        crate::file::File::set_gid(&mut foo, Gid(2)).unwrap();

        let fs = ext2.borrow();
        let inode = Inode::parse(&fs.device, fs.superblock(), foo.file.inode_number).unwrap();

        let mode = inode.mode;
        assert_eq!(mode, (TypePermissions::REGULAR_FILE | TypePermissions::USER_R | TypePermissions::USER_W).bits());
        let uid = inode.uid;
        assert_eq!(uid, 1);
        let gid = inode.gid;
        assert_eq!(gid, 2);

        fs::remove_file("./tests/fs/ext2/io_operations_copy_file_mode.ext2").unwrap();
    }
}
