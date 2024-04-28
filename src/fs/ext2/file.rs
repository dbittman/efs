//! Interface to manipulate UNIX files on an ext2 filesystem.

use alloc::borrow::ToOwned;
use alloc::ffi::CString;
use alloc::string::{String, ToString};
use alloc::vec;
use alloc::vec::Vec;
use core::fmt::Debug;
use core::ptr::{addr_of, addr_of_mut, slice_from_raw_parts};

use bitflags::Flags;
use itertools::Itertools;

use super::directory::{self, Entry};
use super::error::Ext2Error;
use super::inode::{Inode, TypePermissions};
use super::{Celled, Ext2};
use crate::dev::error::DevError;
use crate::dev::sector::Address;
use crate::dev::Device;
use crate::error::Error;
use crate::file::{self, DirectoryEntry, Stat, Type, TypeWithFile};
use crate::fs::error::FsError;
use crate::fs::ext2::block::Block;
use crate::fs::ext2::indirection::IndirectedBlocks;
use crate::fs::ext2::inode::DIRECT_BLOCK_POINTER_COUNT;
use crate::fs::PATH_MAX;
use crate::io::{Base, Read, Seek, SeekFrom, Write};
use crate::path::{UnixStr, CUR_DIR, PARENT_DIR};
use crate::permissions::Permissions;
use crate::types::{Blkcnt, Blksize, Gid, Ino, Mode, Nlink, Off, Time, Timespec, Uid};

/// Minimal allocation in bytes for a file.
///
/// This does not directly come from an ext2's doc but [this paragraph](https://www.kernel.org/doc/html/v6.7/filesystems/ext4/overview.html#block-and-inode-allocation-policy) from the ext4's doc.
pub const MINIMAL_FILE_ALLOCATION: u64 = 8_192;

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

impl<Dev: Device<u8, Ext2Error>> Clone for File<Dev> {
    fn clone(&self) -> Self {
        Self {
            filesystem: self.filesystem.clone(),
            inode_number: self.inode_number,
            inode: self.inode,
            io_offset: self.io_offset,
        }
    }
}

impl<Dev: Device<u8, Ext2Error>> File<Dev> {
    /// Returns a new ext2's [`File`] from an [`Ext2`] instance and the inode number of the file.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Inode::parse`].
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
    pub fn truncate(&mut self, size: u64) -> Result<(), Error<Ext2Error>> {
        if self.inode.data_size() <= size {
            return Ok(());
        }

        let mut fs = self.filesystem.borrow_mut();

        // SAFETY: the result is a u32 as `size` is valid (it has been checked)
        let previous_data_block_number =
            unsafe { u32::try_from(self.inode.data_size() / u64::from(fs.superblock().block_size())).unwrap_unchecked() };

        let mut new_inode = self.inode;
        // SAFETY: the result is smaller than `u32::MAX`
        new_inode.size = unsafe { u32::try_from(u64::from(u32::MAX) & size).unwrap_unchecked() };

        let starting_addr = Inode::starting_addr(&fs.device, fs.superblock(), self.inode_number)?;

        // SAFETY: this writes an inode at the starting address of the inode
        unsafe {
            fs.device.borrow_mut().write_at(starting_addr, new_inode)?;
        };

        // SAFETY: the result is a u32 as `size` is valid (it has been checked)
        let kept_data_blocks_number = unsafe { u32::try_from(size / u64::from(fs.superblock().block_size())).unwrap_unchecked() };
        let mut indirection_blocks = self.inode.indirected_blocks(&fs.device, fs.superblock())?;
        indirection_blocks.truncate_back_data_blocks(previous_data_block_number);
        let symmetrical_difference =
            indirection_blocks.truncate_front_data_blocks(previous_data_block_number - kept_data_blocks_number);

        let mut deallocated_blocks = symmetrical_difference.changed_data_blocks();
        deallocated_blocks.append(
            &mut symmetrical_difference
                .changed_indirected_blocks()
                .into_iter()
                .map(|(_, (indirection_block, _))| indirection_block)
                .collect_vec(),
        );
        fs.deallocate_blocks(&deallocated_blocks)?;

        drop(fs);

        self.io_offset = 0;

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

    fn get_type(&self) -> file::Type {
        // SAFETY: the file type as been checked during the inode's parse
        unsafe { self.inode.file_type().unwrap_unchecked() }
    }

    fn set_mode(&mut self, mode: Mode) -> Result<(), Error<Self::Error>> {
        let mut new_inode = self.inode;
        new_inode.mode = *mode | self.inode.type_permissions().file_type().bits();
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

macro_rules! impl_file {
    ($id:ident) => {
        impl<Dev: Device<u8, Ext2Error>> crate::file::File for $id<Dev> {
            type Error = Ext2Error;

            fn stat(&self) -> Stat {
                self.file.stat()
            }

            fn get_type(&self) -> file::Type {
                self.file.get_type()
            }

            fn set_mode(&mut self, mode: Mode) -> Result<(), Error<Self::Error>> {
                self.file.set_mode(mode)
            }

            fn set_uid(&mut self, uid: Uid) -> Result<(), Error<Self::Error>> {
                self.file.set_uid(uid)
            }

            fn set_gid(&mut self, gid: Gid) -> Result<(), Error<Self::Error>> {
                self.file.set_gid(gid)
            }
        }
    };
}

impl<Dev: Device<u8, Ext2Error>> Base for File<Dev> {
    type IOError = Ext2Error;
}

impl<Dev: Device<u8, Ext2Error>> Read for File<Dev> {
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
    fn write(&mut self, buf: &[u8]) -> Result<usize, Error<Self::IOError>> {
        let mut fs = self.filesystem.borrow_mut();
        let superblock = fs.superblock().clone();
        let block_size = u64::from(fs.superblock().block_size());

        let buf_len = buf.len();
        if buf_len as u64 > fs.superblock().max_file_size() {
            return Err(Error::Fs(FsError::Implementation(Ext2Error::OutOfBounds(buf_len as i128))));
        }

        // Calcul of the number of needed data blocks
        let bytes_to_write =
            if self.inode.file_type()? == Type::Regular { (buf_len as u64).max(MINIMAL_FILE_ALLOCATION) } else { buf_len as u64 };
        let data_blocks_needed =
            // SAFETY: there are at most u32::MAX blocks on the filesystem
            1 + unsafe { u32::try_from((bytes_to_write + self.io_offset - 1) / block_size).unwrap_unchecked() };

        let mut indirected_blocks: IndirectedBlocks<12> = self.inode.indirected_blocks(&fs.device, fs.superblock())?;
        // SAFETY: there are at most u32::MAX blocks on the filesystem
        indirected_blocks.truncate_back_data_blocks(unsafe {
            // In case of blocks that are not used and not 0
            1 + u32::try_from((self.inode.data_size().max(MINIMAL_FILE_ALLOCATION) - 1) / block_size).unwrap_unchecked()
        });

        let current_data_block_count = indirected_blocks.data_block_count();
        let data_blocks_to_request = data_blocks_needed.saturating_sub(current_data_block_count);

        let current_indirection_block_count = indirected_blocks.indirection_block_count();
        let indirection_blocks_to_request = IndirectedBlocks::<DIRECT_BLOCK_POINTER_COUNT>::necessary_indirection_block_count(
            data_blocks_needed,
            fs.superblock().base().block_size() / 4,
        ) - current_indirection_block_count;

        let start_block_group = indirected_blocks
            .last_data_block_allocated()
            .map(|(block, _)| superblock.block_group(block))
            .unwrap_or_default();

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
            let Some(buffer_end) =
                buf.get(written_bytes..written_bytes + (superblock.base().blocks_per_group as usize).min(buf_len - written_bytes))
            else {
                break;
            };

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

        self.seek(SeekFrom::Current(i64::try_from(buf_len).expect("Could not fit the buffer length on an i64")))?;

        Ok(written_bytes)
    }

    fn flush(&mut self) -> Result<(), Error<Ext2Error>> {
        Ok(())
    }
}

impl<Dev: Device<u8, Ext2Error>> Seek for File<Dev> {
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
            #[cfg(test)]
            std::println!("{}", self.inode.data_size());
            Err(Error::Fs(FsError::Implementation(Ext2Error::OutOfBounds(self.io_offset.into()))))
        } else {
            Ok(previous_offset)
        }
    }
}

/// Implementation of a regular file.
#[derive(Debug)]
pub struct Regular<Dev: Device<u8, Ext2Error>> {
    /// Inner file containing the generic file.
    file: File<Dev>,
}

impl<Dev: Device<u8, Ext2Error>> Regular<Dev> {
    /// Returns a new ext2's [`Regular`] from an [`Ext2`] instance and the inode number of the file.
    ///
    /// # Errors
    ///
    /// Returns the same errors  as [`Ext2::inode`].
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
    pub fn read_all(&mut self) -> Result<Vec<u8>, Error<Ext2Error>> {
        self.file.read_all()
    }
}

impl<Dev: Device<u8, Ext2Error>> Clone for Regular<Dev> {
    fn clone(&self) -> Self {
        Self {
            file: self.file.clone(),
        }
    }
}

impl_file!(Regular);

impl<Dev: Device<u8, Ext2Error>> Base for Regular<Dev> {
    type IOError = Ext2Error;
}

impl<Dev: Device<u8, Ext2Error>> Read for Regular<Dev> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Error<Ext2Error>> {
        self.file.read(buf)
    }
}

impl<Dev: Device<u8, Ext2Error>> Write for Regular<Dev> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Error<Ext2Error>> {
        self.file.write(buf)
    }

    fn flush(&mut self) -> Result<(), Error<Ext2Error>> {
        self.file.flush()
    }
}

impl<Dev: Device<u8, Ext2Error>> Seek for Regular<Dev> {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Error<Ext2Error>> {
        self.file.seek(pos)
    }
}

impl<Dev: Device<u8, Ext2Error>> file::Regular for Regular<Dev> {
    fn truncate(&mut self, size: u64) -> Result<(), Error<<Self as file::File>::Error>> {
        self.file.truncate(size)
    }
}

/// Interface for ext2's directories.
#[derive(Debug)]
pub struct Directory<Dev: Device<u8, Ext2Error>> {
    /// Inner file containing the generic file.
    file: File<Dev>,

    /// Entries contained in this directory.
    ///
    /// They are stored as a list of entries in each data block.
    entries: Vec<Vec<Entry>>,
}

impl<Dev: Device<u8, Ext2Error>> Directory<Dev> {
    /// Returns the directory located at the given inode number.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Entry::parse`].
    pub fn new(filesystem: &Celled<Ext2<Dev>>, inode_number: u32) -> Result<Self, Error<Ext2Error>> {
        let file = File::new(filesystem, inode_number)?;
        let fs = filesystem.borrow();

        let block_size = u64::from(fs.superblock().block_size());
        let data_size = file.inode.data_size();
        let data_blocks = 1 + (data_size - 1) / block_size;

        let mut indirected_blocks = file.inode.indirected_blocks(&fs.device, fs.superblock())?;
        // SAFETY: there are at most u32::MAX blocks on this filesystem
        indirected_blocks.truncate_back_data_blocks(unsafe { u32::try_from(data_blocks).unwrap_unchecked() });

        let mut entries = Vec::new();

        for block in indirected_blocks.flatten_data_blocks() {
            let mut entries_in_block = Vec::new();
            let mut accumulated_size = 0_u64;
            while accumulated_size < block_size {
                let starting_addr =
                    Address::from(usize::try_from(u64::from(block) * block_size + accumulated_size).map_err(|_err| {
                        Error::Device(DevError::OutOfBounds(
                            "address",
                            (u64::from(block) * block_size + accumulated_size).into(),
                            (0_i128, fs.device.borrow().size().0.into()),
                        ))
                    })?);

                // SAFETY: `starting_addr` contains the beginning of an entry
                let entry = unsafe { Entry::parse(&fs.device, starting_addr) }?;
                accumulated_size += u64::from(entry.rec_len);
                entries_in_block.push(entry);
            }
            entries.push(entries_in_block);
        }

        Ok(Self { file, entries })
    }

    /// Writes all the entries of the block `block_index`.
    ///
    /// This function does not perform any check: the entries must be in a coherent state. It is recommanded to perform
    /// [`defragment`](struct.Directory.html#method.defragment) beforehand.
    ///
    /// # Safety
    ///
    /// Must ensure that the entries are in a valid state regarding to the completion of data blocks and the number of entry per
    /// data block. Furthermore, `block_index` must be a valid index of `self.entries`.
    unsafe fn write_block_entry(&mut self, block_index: usize) -> Result<(), Error<Ext2Error>> {
        let block_size = u64::from(self.file.filesystem.borrow().superblock().block_size());
        self.file.seek(SeekFrom::Start((block_index as u64) * block_size))?;

        let mut buffer = Vec::new();
        for entry in self.entries.get_unchecked(block_index) {
            buffer.append(&mut entry.as_bytes().clone());
            buffer.append(&mut vec![0_u8; entry.free_space() as usize]);
        }
        self.file.write(&buffer)?;

        Ok(())
    }

    /// Writes all the entries.
    ///
    /// This function does not perform any check: the entries must be in a coherent state. It is recommanded to perform
    /// [`defragment`](struct.Directory.html#method.defragment) beforehand.
    ///
    /// # Safety
    ///
    /// Must ensure that the entries are in a valid state regarding to the completion of data blocks and the number of entry per
    /// data block.
    unsafe fn write_all_entries(&mut self) -> Result<(), Error<Ext2Error>> {
        self.file.truncate(0)?;
        for block_index in 0..self.entries.len() {
            self.write_block_entry(block_index)?;
        }
        Ok(())
    }

    /// Defragments the directory by compacting (if necessary) all the entries.
    fn defragment(&mut self) {
        let block_size = u16::try_from(self.file.filesystem.borrow().superblock().block_size())
            .expect("Ill-formed superblock: block size should be castable in a u16");

        let mut new_entries = Vec::new();

        let mut entries_in_block = Vec::<Entry>::new();
        let mut accumulated_size = 0_u16;
        for mut entry in self.entries.clone().into_iter().flatten() {
            if accumulated_size + entry.minimal_size() > block_size {
                if let Some(ent) = entries_in_block.last_mut() {
                    ent.rec_len = block_size - accumulated_size;
                }
                new_entries.push(entries_in_block);
                accumulated_size = 0;
                entries_in_block = Vec::new();
            }
            entry.rec_len = entry.minimal_size();
            accumulated_size += entry.minimal_size();
            entries_in_block.push(entry);
        }

        if let Some(ent) = entries_in_block.last_mut() {
            ent.rec_len = block_size - accumulated_size;
            new_entries.push(entries_in_block);
        }

        self.entries = new_entries;
    }

    /// Returns, if it exists, the block index and the entry index containing at least `necessary_space` free space.
    fn find_space(&self, necessary_space: u16) -> Option<(usize, usize)> {
        for (block_index, entries_in_block) in self.entries.iter().enumerate() {
            for (entry_index, entry) in entries_in_block.iter().enumerate() {
                if entry.free_space() >= necessary_space {
                    return Some((block_index, entry_index));
                }
            }
        }

        None
    }
}

impl<Dev: Device<u8, Ext2Error>> Clone for Directory<Dev> {
    fn clone(&self) -> Self {
        Self {
            file: self.file.clone(),
            entries: self.entries.clone(),
        }
    }
}

impl_file!(Directory);

impl<Dev: Device<u8, Ext2Error>> file::Directory for Directory<Dev> {
    type BlockDev = BlockDevice<Dev>;
    type CharDev = CharacterDevice<Dev>;
    type Fifo = Fifo<Dev>;
    type Regular = Regular<Dev>;
    type Socket = Socket<Dev>;
    type SymbolicLink = SymbolicLink<Dev>;

    fn entries(&self) -> Result<Vec<file::DirectoryEntry<Self>>, Error<Ext2Error>> {
        let mut entries = Vec::new();

        for entry in self.entries.iter().flatten() {
            entries.push(DirectoryEntry {
                // SAFETY: it is checked at the entry creation that the name is a valid CString
                filename: unsafe { entry.name.clone().try_into().unwrap_unchecked() },
                file: self.file.filesystem.file(entry.inode)?,
            });
        }

        Ok(entries)
    }

    fn add_entry(
        &mut self,
        name: UnixStr<'_>,
        file_type: Type,
        permissions: Permissions,
        user_id: Uid,
        group_id: Gid,
    ) -> Result<TypeWithFile<Self>, Error<Self::Error>> {
        if let Ok(file) = self.entry(name.clone()) && file.is_some() {
            return Err(Error::Fs(FsError::EntryAlreadyExist(name.to_string())));
        }

        let mut fs = self.file.filesystem.borrow_mut();
        let block_size = fs.superblock().block_size();

        let inode_number = fs.free_inode()?;
        fs.allocate_inode(
            inode_number,
            TypePermissions::from(permissions) | TypePermissions::from(file_type),
            user_id.0,
            group_id.0,
            Flags::empty(),
            0,
            [0; 12],
        )?;

        drop(fs);

        if file_type == Type::Directory {
            let mut dir = File::new(&self.file.filesystem, inode_number)?;
            let self_and_parent = [
                &Entry {
                    inode: inode_number,
                    rec_len: 9,
                    name_len: 1,
                    file_type: 0, // TODO: handle `FILETYPE` feature
                    // SAFETY: "." is a valid CString
                    name: unsafe { CString::from_vec_unchecked(vec![b'.']) },
                },
                &Entry {
                    inode: self.file.inode_number,
                    rec_len: u16::try_from(block_size - 9).expect("Ill-formed superblock: block size should be castable in a u16"),
                    name_len: 2,
                    file_type: 0, // TODO: handle `FILETYPE` feature
                    // SAFETY: ".." is a valid CString
                    name: unsafe { CString::from_vec_unchecked(vec![b'.', b'.']) },
                },
            ];

            let self_and_parent_bytes = self_and_parent.map(Entry::as_bytes).concat();
            dir.seek(SeekFrom::Start(0))?;
            dir.write_all(&self_and_parent_bytes)?;
            dir.flush()?;
        }

        let mut new_entry = Entry {
            inode: inode_number,
            rec_len: 0,
            name_len: u8::try_from(name.to_string().len())
                .map_err(|_err| Error::Fs(FsError::Implementation(Ext2Error::NameTooLong(name.to_string()))))?,
            file_type: directory::FileType::from(file_type).into(),
            name: name.into(),
        };
        new_entry.rec_len = new_entry.minimal_size();
        if let Some((block_index, entry_index)) = self.find_space(new_entry.minimal_size()) {
            // SAFETY: `find_space` returns a valid block index
            let entries_in_block = unsafe { self.entries.get_unchecked_mut(block_index) };
            // SAFETY: `find_space` returs a valid entry index
            let previous_entry = unsafe { entries_in_block.get_unchecked_mut(entry_index) };

            new_entry.rec_len = previous_entry.rec_len - previous_entry.minimal_size();
            previous_entry.rec_len = previous_entry.minimal_size();

            entries_in_block.insert(entry_index + 1, new_entry);

            // SAFETY: all necessary changes have been made
            unsafe { self.write_block_entry(block_index) }?;
        } else {
            self.entries.push(vec![new_entry]);
            self.defragment();
            // SAFETY: `defragment` has been called above
            unsafe { self.write_all_entries() }?;
        }

        self.file.filesystem.file(inode_number)
    }

    fn remove_entry(&mut self, entry_name: crate::path::UnixStr) -> Result<(), Error<Self::Error>> {
        if entry_name == *CUR_DIR || entry_name == *PARENT_DIR {
            return Err(Error::Fs(FsError::RemoveRefused));
        }

        let block_size = u64::from(self.file.filesystem.borrow().superblock().block_size());
        let entry_name_cstring = entry_name.clone().into();
        for (block_index, entries_in_block) in self.entries.clone().into_iter().enumerate() {
            for (index, entry) in entries_in_block.clone().into_iter().enumerate() {
                if entry.name == entry_name_cstring {
                    // SAFETY: `block_index` is returned by `enumerate`
                    let block = unsafe { self.entries.get_unchecked_mut(block_index) };
                    block.remove(index);
                    if let Some(previous_entry) = block.get_mut(index - 1) {
                        previous_entry.rec_len += entry.rec_len;
                        // SAFETY: the content of this block is coherent
                        unsafe { self.write_block_entry(block_index) }?;
                    } else if let Some(next_entry) = block.get_mut(index + 1) {
                        next_entry.rec_len += entry.rec_len;
                        // SAFETY: the content of this block is coherent
                        unsafe { self.write_block_entry(block_index) }?;
                    } else {
                        self.entries.remove(block_index);
                        self.file.truncate(block_size * (block_index - 1) as u64)?;

                        for i in block_index..self.entries.len() {
                            // SAFETY: this block is untouched
                            unsafe { self.write_block_entry(i) }?;
                        }
                    }

                    if let TypeWithFile::Directory(mut dir) = self.file.filesystem.file(entry.inode)? {
                        let mut new_inode = self.file.inode;
                        let sub_entries = dir.entries.clone().into_iter().flatten().collect_vec();
                        for sub_entry in sub_entries {
                            // SAFETY: sub entry name has been checked at `dir` creation
                            let sub_entry_name: UnixStr<'_> = unsafe { sub_entry.name.try_into().unwrap_unchecked() };
                            if sub_entry_name != *CUR_DIR && sub_entry_name != *PARENT_DIR {
                                dir.remove_entry(sub_entry_name.clone())?;

                                let fs = self.file.filesystem.borrow();
                                let sub_entry_inode = fs.inode(sub_entry.inode)?;
                                if sub_entry_inode.file_type()? == Type::Directory {
                                    new_inode.links_count -= 1;
                                }
                                drop(fs);
                                if self.file.inode.links_count != new_inode.links_count {
                                    unsafe {
                                        self.file.set_inode(&new_inode)?;
                                    };
                                }
                            }
                        }
                    }

                    let mut fs = self.file.filesystem.borrow_mut();
                    return fs.deallocate_inode(entry.inode);
                }
            }
        }

        Err(Error::Fs(FsError::NotFound(entry_name.to_string())))
    }
}

/// Interface for ext2's symbolic links.
#[derive(Debug)]
pub struct SymbolicLink<Dev: Device<u8, Ext2Error>> {
    /// Inner file containing the generic file.
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

impl<Dev: Device<u8, Ext2Error>> Clone for SymbolicLink<Dev> {
    fn clone(&self) -> Self {
        Self {
            file: self.file.clone(),
            pointed_file: self.pointed_file.clone(),
        }
    }
}

impl_file!(SymbolicLink);

impl<Dev: Device<u8, Ext2Error>> file::SymbolicLink for SymbolicLink<Dev> {
    fn get_pointed_file(&self) -> Result<&str, Error<Self::Error>> {
        Ok(&self.pointed_file)
    }

    fn set_pointed_file(&mut self, pointed_file: &str) -> Result<(), Error<Self::Error>> {
        let bytes = pointed_file.as_bytes();

        if bytes.len() > PATH_MAX {
            return Err(Error::Fs(FsError::NameTooLong(pointed_file.to_owned())));
        } else if bytes.len() > SYMBOLIC_LINK_INODE_STORE_LIMIT {
            if self.pointed_file.len() <= SYMBOLIC_LINK_INODE_STORE_LIMIT {
                let mut new_inode = self.file.inode;

                let data_ptr = addr_of_mut!(new_inode.direct_block_pointers).cast::<u8>();
                // SAFETY: there are `SYMBOLIC_LINK_INODE_STORE_LIMIT` bytes available to store the data
                let data_slice = unsafe { core::slice::from_raw_parts_mut(data_ptr, SYMBOLIC_LINK_INODE_STORE_LIMIT) };
                data_slice.clone_from_slice(&[b'\0'; SYMBOLIC_LINK_INODE_STORE_LIMIT]);

                let fs = self.file.filesystem.borrow();
                let starting_addr = Inode::starting_addr(&fs.device, fs.superblock(), self.file.inode_number)?;
                // SAFETY: the starting address correspond to the one of this inode
                unsafe {
                    fs.device.borrow_mut().write_at(starting_addr, new_inode)?;
                };

                drop(fs);

                self.file.update_inner_inode()?;
            }

            self.file.seek(SeekFrom::Start(0))?;
            self.file.write(bytes)?;
            self.file.truncate(bytes.len() as u64)?;
        } else {
            let mut new_inode = self.file.inode;
            // SAFETY: `bytes.len() < PATH_MAX << u32::MAX`
            new_inode.size = unsafe { u32::try_from(bytes.len()).unwrap_unchecked() };

            let data_ptr = addr_of_mut!(new_inode.direct_block_pointers).cast::<u8>();
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

            self.file.update_inner_inode()?;
        }

        self.pointed_file = pointed_file.to_owned();
        Ok(())
    }
}

macro_rules! generic_file {
    ($id:ident) => {
        #[doc = concat!("Basic implementation of a [`", stringify!($id), "`](crate::file::", stringify!($id), ") for ext2.")]
        #[derive(Debug)]
        pub struct $id<Dev: Device<u8, Ext2Error>> {
            /// Inner file containing the generic file.
            file: File<Dev>,
        }

        impl<Dev: Device<u8, Ext2Error>> Clone for $id<Dev> {
            fn clone(&self) -> Self {
                Self {
                    file: self.file.clone(),
                }
            }
        }

        impl_file!($id);

        impl<Dev: Device<u8, Ext2Error>> $id<Dev> {
            #[doc = concat!("Returns a new ext2's [`", stringify!($id), "`] from an [`Ext2`] instance and the inode number of the file.")]
            ///
            /// # Errors
            ///
            /// Returns the same errors as [`File::new`].

            pub fn new(filesystem: &Celled<Ext2<Dev>>, inode_number: u32) -> Result<Self, Error<Ext2Error>> {
                Ok(Self { file: File::new(filesystem, inode_number)? })
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
    use crate::file::{Regular, SymbolicLink, Type, TypeWithFile};
    use crate::fs::ext2::directory::Entry;
    use crate::fs::ext2::file::Directory;
    use crate::fs::ext2::inode::{Inode, TypePermissions, ROOT_DIRECTORY_INODE};
    use crate::fs::ext2::superblock::Superblock;
    use crate::fs::ext2::{Celled, Ext2};
    use crate::fs::FileSystem;
    use crate::io::{Seek, SeekFrom, Write};
    use crate::path::{Path, UnixStr};
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
                .flatten()
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
            .flatten()
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

    #[test]
    fn file_truncation() {
        const BYTES_TO_WRITE: usize = 400_000;

        fs::copy("./tests/fs/ext2/io_operations.ext2", "./tests/fs/ext2/io_operations_copy_file_truncation.ext2").unwrap();

        let file = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_copy_file_truncation.ext2")
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

        let initial_free_block_number = ext2.borrow().superblock().base().free_blocks_count;
        let initial_foo_size = foo.file.inode.data_size();

        let replace_text = vec![b'a'; BYTES_TO_WRITE];
        foo.write(&replace_text).unwrap();
        foo.flush().unwrap();

        assert_eq!(foo.file.inode.data_size(), BYTES_TO_WRITE as u64);

        foo.truncate(10000).unwrap();

        assert_eq!(foo.file.inode.data_size(), 10000);
        assert_eq!(foo.read_all().unwrap().len(), 10000);

        foo.truncate(initial_foo_size).unwrap();
        let new_free_block_number = ext2.borrow().superblock().base().free_blocks_count;

        assert_eq!(foo.file.inode.data_size(), initial_foo_size);
        assert!(new_free_block_number >= initial_free_block_number); // Non used blocks could be deallocated

        fs::remove_file("./tests/fs/ext2/io_operations_copy_file_truncation.ext2").unwrap();
    }

    #[test]
    fn file_simlinks() {
        fs::copy("./tests/fs/ext2/io_operations.ext2", "./tests/fs/ext2/io_operations_copy_file_simlinks.ext2").unwrap();

        let file = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_copy_file_simlinks.ext2")
                .unwrap(),
        );
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let TypeWithFile::Directory(root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else {
            panic!("The root is always a directory.");
        };
        let TypeWithFile::SymbolicLink(mut bar) =
            crate::file::Directory::entry(&root, UnixStr::new("bar.txt").unwrap()).unwrap().unwrap()
        else {
            panic!("`bar.txt` has been created as a symbolic link");
        };

        assert_eq!(crate::file::File::get_type(&bar), Type::SymbolicLink);

        assert_eq!(bar.get_pointed_file().unwrap(), "foo.txt");
        assert_eq!(bar.file.inode.data_size(), 7);

        bar.set_pointed_file("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
            .unwrap();
        assert_eq!(bar.get_pointed_file().unwrap(), "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
        assert_eq!(bar.file.read_all().unwrap(), b"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
        assert_eq!(bar.file.inode.data_size(), 70);

        bar.set_pointed_file("foo.txt").unwrap();
        assert_eq!(bar.get_pointed_file().unwrap(), "foo.txt");
        assert!(bar.file.read_all().is_err());
        assert_eq!(bar.file.inode.data_size(), 7);

        fs::remove_file("./tests/fs/ext2/io_operations_copy_file_simlinks.ext2").unwrap();
    }

    #[test]
    fn new_files() {
        fs::copy("./tests/fs/ext2/io_operations.ext2", "./tests/fs/ext2/io_operations_new_files.ext2").unwrap();

        let file = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_new_files.ext2")
                .unwrap(),
        );
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let TypeWithFile::Directory(mut root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else {
            panic!("The root is always a directory.");
        };

        assert!(crate::file::Directory::entry(&root, UnixStr::new("boo.txt").unwrap()).is_ok_and(|res| res.is_none()));
        let TypeWithFile::Regular(mut boo) = crate::file::Directory::add_entry(
            &mut root,
            UnixStr::new("boo.txt").unwrap(),
            Type::Regular,
            Permissions::USER_READ | Permissions::USER_WRITE | Permissions::USER_EXECUTION,
            Uid(0),
            Gid(0),
        )
        .unwrap() else {
            panic!("boo has been created as a regular file.")
        };

        let TypeWithFile::Directory(root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else {
            panic!("The root is always a directory.");
        };
        assert!(crate::file::Directory::entry(&root, UnixStr::new("boo.txt").unwrap()).is_ok_and(|res| res.is_some()));

        boo.write(b"Hello earth!\n").unwrap();
        assert_eq!(boo.read_all().unwrap(), b"Hello earth!\n");

        fs::remove_file("./tests/fs/ext2/io_operations_new_files.ext2").unwrap();
    }

    #[test]
    #[allow(clippy::similar_names)]
    fn remove_files() {
        fs::copy("./tests/fs/ext2/io_operations.ext2", "./tests/fs/ext2/io_operations_remove_files.ext2").unwrap();

        let file = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_remove_files.ext2")
                .unwrap(),
        );
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let TypeWithFile::Directory(mut root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else {
            panic!("The root is always a directory.");
        };

        assert!(crate::file::Directory::entry(&root, UnixStr::new("bar.txt").unwrap()).is_ok_and(|res| res.is_some()));
        crate::file::Directory::remove_entry(&mut root, UnixStr::new("bar.txt").unwrap()).unwrap();
        let TypeWithFile::Directory(mut root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else {
            panic!("The root is always a directory.");
        };
        assert!(crate::file::Directory::entry(&root, UnixStr::new("bar.txt").unwrap()).is_ok_and(|res| res.is_none()));

        let TypeWithFile::Regular(ex1) = ext2
            .get_file(&Path::new(UnixStr::new("/folder/ex1.txt").unwrap()), root.clone(), false)
            .unwrap()
        else {
            panic!("ex1.txt is a regular file.");
        };
        let ex1_inode = ex1.file.inode_number;

        let TypeWithFile::SymbolicLink(ex2) = ext2
            .get_file(&Path::new(UnixStr::new("/folder/ex2.txt").unwrap()), root.clone(), false)
            .unwrap()
        else {
            panic!("ex2.txt is a symbolic link.");
        };
        let ex2_inode = ex2.file.inode_number;

        let fs = ext2.borrow();
        let superblock = fs.superblock();
        let ex1_bitmap = fs.get_inode_bitmap(Inode::block_group(superblock, ex1_inode)).unwrap();
        assert!(Inode::is_used(ex1_inode, superblock, &ex1_bitmap));
        let ex2_bitmap = fs.get_inode_bitmap(Inode::block_group(superblock, ex2_inode)).unwrap();
        assert!(Inode::is_used(ex2_inode, superblock, &ex2_bitmap));
        drop(fs);

        let TypeWithFile::Directory(folder) =
            ext2.get_file(&Path::new(UnixStr::new("folder").unwrap()), root.clone(), false).unwrap()
        else {
            panic!("");
        };

        std::println!("{:?}", folder.file.inode);

        crate::file::Directory::remove_entry(&mut root, UnixStr::new("folder").unwrap()).unwrap();

        let fs = ext2.borrow();
        let superblock = fs.superblock();
        let ex1_bitmap = fs.get_inode_bitmap(Inode::block_group(superblock, ex1_inode)).unwrap();
        assert!(Inode::is_free(ex1_inode, superblock, &ex1_bitmap));
        let ex2_bitmap = fs.get_inode_bitmap(Inode::block_group(superblock, ex2_inode)).unwrap();
        assert!(Inode::is_free(ex2_inode, superblock, &ex2_bitmap));

        fs::remove_file("./tests/fs/ext2/io_operations_remove_files.ext2").unwrap();
    }
}
