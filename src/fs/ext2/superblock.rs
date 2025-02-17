//! Interface with the ext2's superblock.
//!
//! See the [OSdev wiki](https://wiki.osdev.org/Ext2#Superblock) and the [*The Second Extended Filesystem* book](https://www.nongnu.org/ext2-doc/ext2.html#superblock) for more information.

use core::mem::size_of;

use bitflags::bitflags;

use super::error::Ext2Error;
use crate::arch::usize_to_u64;
use crate::celled::Celled;
use crate::dev::Device;
use crate::dev::address::Address;
use crate::error::Error;
use crate::fs::error::FsError;

/// Ext2 signature, used to help confirm the presence of an Ext2 volume.
pub const EXT2_SIGNATURE: u16 = 0xef53;

/// Starting byte of the superblock in a Ext2 storage device.
///
/// As described [here](https://www.nongnu.org/ext2-doc/ext2.html#superblock), the superblock **always** located at byte offset 1024 from the beginning of the file, block device or partition.
pub const SUPERBLOCK_START_BYTE: u64 = 1024;

/// Size in bytes of the superblock with reserved bytes.
pub const SUPERBLOCK_SIZE: u64 = 1024;

/// Base Superblock Fields.
///
/// See the [`ExtendedFields`] struct for the extended fields of the superblock (if the [`major
/// version`](struct.Base.html#structfield.rev_level) is greater than or equal to 1).
#[repr(C, packed)]
#[derive(Debug, Clone, Copy)]
pub struct Base {
    /// Total number of inodes in file system.
    pub inodes_count: u32,

    /// Total number of blocks in file system.
    pub blocks_count: u32,

    /// Number of blocks reserved for superuser (see the
    /// [`reserved_blocks_user_id`](struct.Base.html#structfield.reserved_blocks_user_id) field).
    pub r_blocks_count: u32,

    /// Total number of unallocated blocks.
    pub free_blocks_count: u32,

    /// Total number of unallocated inodes.
    pub free_inodes_count: u32,

    /// Block number of the block containing the superblock (also the starting block number, NOT always zero.).
    pub first_data_block: u32,

    /// log2(block size) - 10. (In other words, the number to shift 1,024 to the left by to obtain the block size).
    pub log_block_size: u32,

    /// log2(fragment size) - 10. (In other words, the number to shift 1,024 to the left by to obtain the fragment
    /// size).
    pub log_frag_size: u32,

    /// Number of blocks in each block group.
    pub blocks_per_group: u32,

    /// Number of fragments in each block group.
    pub frags_per_group: u32,

    /// Number of inodes in each block group.
    pub inodes_per_group: u32,

    /// Last mount time (in POSIX time).
    pub mtime: u32,

    /// Last written time (in POSIX time).
    pub wtime: u32,

    /// Number of times the volume has been mounted since its last consistency check (fsck).
    pub mnt_count: u16,

    /// Number of mounts allowed before a consistency check (fsck) must be done.
    pub max_mnt_count: u16,

    /// Ext2 signature (0xef53), used to help confirm the presence of Ext2 on a volume.
    ///
    /// This field should always be equal to [`EXT2_SIGNATURE`].
    pub magic: u16,

    /// File system state.
    ///
    /// See [`State`] for more information.
    pub state: u16,

    /// What to do when an error is detected.
    ///
    /// See [`ErrorHandlingMethod`] for more information.
    pub errors: u16,

    /// Minor portion of version (combine with Major portion below to construct full version field).
    pub minor_rev_level: u16,

    /// POSIX time of last consistency check (fsck).
    pub lastcheck: u32,

    /// Interval (in POSIX time) between forced consistency checks (fsck).
    pub checkinterval: u32,

    /// Operating system ID from which the filesystem on this volume was created.
    ///
    /// See [`OperatingSystem`] for more information.
    pub creator_os: u32,

    /// Major portion of version (combine with Minor portion above to construct full version field).
    pub rev_level: u32,

    /// User ID that can use reserved blocks.
    pub def_resuid: u16,

    /// Group ID that can use reserved blocks.
    pub def_resgid: u16,
}

#[cfg(test)]
impl PartialEq for Base {
    fn eq(&self, other: &Self) -> bool {
        self.inodes_count == other.inodes_count
            && self.blocks_count == other.blocks_count
            && self.r_blocks_count == other.r_blocks_count
            && self.free_blocks_count == other.free_blocks_count
            && self.free_inodes_count == other.free_inodes_count
            && self.first_data_block == other.first_data_block
            && self.log_block_size == other.log_block_size
            && self.log_frag_size == other.log_frag_size
            && self.blocks_per_group == other.blocks_per_group
            && self.frags_per_group == other.frags_per_group
            && self.inodes_per_group == other.inodes_per_group
            && self.max_mnt_count == other.max_mnt_count
            && self.magic == other.magic
            && self.state == other.state
            && self.errors == other.errors
            && self.minor_rev_level == other.minor_rev_level
            && self.checkinterval == other.checkinterval
            && self.creator_os == other.creator_os
            && self.rev_level == other.rev_level
            && self.def_resuid == other.def_resuid
            && self.def_resgid == other.def_resgid
    }
}

/// File System States.
///
/// See the [OSdev wiki](https://wiki.osdev.org/Ext2#File_System_States) for more information.
#[repr(u16)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum State {
    /// File system is clean.
    Clean = 0x0001,

    /// File system has errors.
    Errors = 0x0002,
}

impl State {
    /// Returns the [`State`] corresponding to the [`state`](struct.Base.html#structfield.state) field in the [`Base`]
    /// structure.
    ///
    /// # Errors
    ///
    /// Returns an [`Ext2Error::InvalidState`] error if the give bytes does not correspond to a valid state.
    pub const fn try_from_bytes(bytes: u16) -> Result<Self, Ext2Error> {
        match bytes {
            0x0001 => Ok(Self::Clean),
            0x0002 => Ok(Self::Errors),
            _ => Err(Ext2Error::InvalidState(bytes)),
        }
    }
}

impl TryFrom<u16> for State {
    type Error = Ext2Error;

    fn try_from(value: u16) -> Result<Self, Self::Error> {
        Self::try_from_bytes(value)
    }
}

impl From<State> for u16 {
    fn from(value: State) -> Self {
        value as Self
    }
}

/// Error Handling Methods.
///
/// See the [OSdev wiki](https://wiki.osdev.org/Ext2#Error_Handling_Methods) for more information.
#[repr(u16)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorHandlingMethod {
    /// Ignore the error (continue on).
    Ignore = 0x0001,

    /// Remount file system as read-only.
    Remount = 0x0002,

    /// Kernel panic.
    Panic = 0x03,
}

impl ErrorHandlingMethod {
    /// Returns the [`ErrorHandlingMethod`] corresponding to the [`error`](struct.Base.html#structfield.error) field in
    /// the [`Base`] structure.
    ///
    /// # Errors
    ///
    /// Returns an [`Ext2Error::InvalidErrorHandlingMethod`] error if the give bytes does not correspond to a valid
    /// state.
    pub const fn try_from_bytes(bytes: u16) -> Result<Self, Ext2Error> {
        match bytes {
            0x0001 => Ok(Self::Ignore),
            0x0002 => Ok(Self::Remount),
            0x0003 => Ok(Self::Panic),
            _ => Err(Ext2Error::InvalidErrorHandlingMethod(bytes)),
        }
    }
}

impl TryFrom<u16> for ErrorHandlingMethod {
    type Error = Ext2Error;

    fn try_from(value: u16) -> Result<Self, Self::Error> {
        Self::try_from_bytes(value)
    }
}

impl From<ErrorHandlingMethod> for u16 {
    fn from(value: ErrorHandlingMethod) -> Self {
        value as Self
    }
}

/// Creator Operating Systemd IDs.
///
/// See the [OSdev wiki](https://wiki.osdev.org/Ext2#Creator_Operating_System_IDs) for more information.
#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperatingSystem {
    /// [Linux](https://kernel.org/).
    Linux = 0x0000_0000,

    /// [GNU HURD](https://www.gnu.org/software/hurd/hurd.html).
    GnuHurd = 0x0000_0001,

    /// MASIX (an operating system developed by Rémy Card, one of the developers of ext2).
    Masix = 0x0000_0002,

    /// [FreeBSD](https://www.freebsd.org/).
    FreeBSD = 0x0000_0003,

    /// Other "Lites" (BSD4.4-Lite derivatives such as [NetBSD](https://www.netbsd.org/), [OpenBSD](https://www.openbsd.org/), [XNU/Darwin](https://opensource.apple.com/source/xnu/), etc.).
    OtherLites = 0x0000_0004,

    /// Unspecified operating system.
    ///
    /// This variant exists as any other operating system should be able to specify its own value.
    Other(u32),
}

impl OperatingSystem {
    /// Returns the [`OperatingSystem`] corresponding to the [`creator_os`](struct.Base.html#structfield.creator_os)
    /// field in the [`Base`] structure.
    #[must_use]
    pub const fn from_bytes(bytes: u32) -> Self {
        match bytes {
            0x0000_0000 => Self::Linux,
            0x0000_0001 => Self::GnuHurd,
            0x0000_0002 => Self::Masix,
            0x0000_0003 => Self::FreeBSD,
            0x0000_0004 => Self::OtherLites,
            _ => Self::Other(bytes),
        }
    }
}

impl From<u32> for OperatingSystem {
    fn from(value: u32) -> Self {
        Self::from_bytes(value)
    }
}

impl From<OperatingSystem> for u32 {
    fn from(value: OperatingSystem) -> Self {
        match value {
            OperatingSystem::Linux => 0x0000_0000,
            OperatingSystem::GnuHurd => 0x0000_0001,
            OperatingSystem::Masix => 0x0000_0002,
            OperatingSystem::FreeBSD => 0x0000_0003,
            OperatingSystem::OtherLites => 0x0000_0004,
            OperatingSystem::Other(id) => id,
        }
    }
}

impl Base {
    /// Returns the number of block groups.
    ///
    /// It is equal to the round up of the total number of blocks divided by the number of blocks per block group.
    #[must_use]
    pub const fn block_group_count(&self) -> u32 {
        self.blocks_count.div_ceil(self.blocks_per_group)
    }

    /// Returns the size of a block in the filesystem described by this superblock.
    #[must_use]
    pub const fn block_size(&self) -> u32 {
        1024 << self.log_block_size
    }

    /// Returns the size of a fragment in the filesystem described by this superblock.
    #[must_use]
    pub const fn frag_size(&self) -> u32 {
        1024 << self.log_frag_size
    }

    /// Returns the state of this filesystem.
    ///
    /// # Errors
    ///
    /// Returns an [`Ext2Error::InvalidState`] if an invalid state has been found.
    pub const fn state(&self) -> Result<State, Ext2Error> {
        State::try_from_bytes(self.state)
    }

    /// Returns the error handling method of this filesystem.
    ///
    /// # Errors
    ///
    /// Returns an [`Ext2Error::InvalidErrorHandlingMethod`] if an invalid state has been found.
    pub const fn error_handling_method(&self) -> Result<ErrorHandlingMethod, Ext2Error> {
        ErrorHandlingMethod::try_from_bytes(self.errors)
    }

    /// Returns the Operating system from which the filesystem on this volume was created.
    #[must_use]
    pub const fn creator_operating_system(&self) -> OperatingSystem {
        OperatingSystem::from_bytes(self.creator_os)
    }

    /// Returns the maximal size in bytes for a single file.
    #[must_use]
    pub const fn max_file_size(&self) -> u64 {
        let block_size = self.block_size() as u64;
        let direct_blocks_size = 12 * block_size;
        let simply_indirect_blocks_size = block_size * (block_size / 4);
        let doubly_indirect_blocks_size = block_size * (block_size / 4) * (block_size / 4);
        let triply_indirect_blocks_size = block_size * (block_size / 4) * (block_size / 4) * (block_size / 4);
        direct_blocks_size + simply_indirect_blocks_size + doubly_indirect_blocks_size + triply_indirect_blocks_size
    }
}

/// Extended Superblock Fields of the [`Base`].
///
/// These fields are only present if [`major`](struct.Base.html#structfield.rev_level) version is greater than or equal
/// to 1.
#[repr(C, packed)]
#[derive(Debug, Clone, Copy)]
pub struct ExtendedFields {
    /// First non-reserved inode in file system. (In versions < 1.0, this is fixed as 11).
    pub first_ino: u32,

    /// Size of each inode structure in bytes. (In versions < 1.0, this is fixed as 128).
    pub inode_size: u16,

    /// Block group that this superblock is part of (if backup copy).
    pub block_group_nr: u16,

    /// Optional features present (features that are not required to read or write, but usually result in a performance
    /// increase).
    pub feature_compat: u32,

    /// Required features present (features that are required to be supported to read or write).
    pub feature_incompat: u32,

    /// Features that if not supported, the volume must be mounted read-only.
    pub feature_ro_compat: u32,

    /// File system ID (what is output by blkid).
    pub uuid: u128,

    /// Volume name (C-style string: characters terminated by a 0 byte).
    pub volume_name: [u8; 16],

    /// Path volume was last mounted to (C-style string: characters terminated by a 0 byte).
    pub last_mounted: [u8; 64],

    /// Compression algorithms used (see
    /// [`required_features`](struct.ExtendedFields.html#structfield.required_features)).
    pub algo_bitmap: u32,

    /// Number of blocks to preallocate for files.
    pub prealloc_blocks: u8,

    /// Number of blocks to preallocate for directories.
    pub prealloc_dir_blocks: u8,

    /// Alignement.
    pub alignment: u16,

    /// Journal ID (same style as the File system ID above).
    pub journal_uuid: u128,

    /// Journal inode.
    pub journal_inum: u32,

    /// Journal device.
    pub journal_dev: u32,

    /// Head of orphan inode list.
    pub last_orphan: u32,

    /// Seeds used for the hash algorithm for directory indexing.
    pub hash_seed: [u32; 4],

    /// Default hash version used for directory indexing.
    pub def_hash_version: u8,

    /// Padding.
    pub padding: [u8; 3],

    /// Default mount options for this file system.
    pub default_mount_options: u32,

    /// Block group ID of the first meta block group.
    pub first_meta_bg: u32,
}

#[cfg(test)]
impl PartialEq for ExtendedFields {
    fn eq(&self, other: &Self) -> bool {
        let self_hash_seed = self.hash_seed;
        let other_hash_seed = other.hash_seed;
        self.first_ino == other.first_ino
            && self.inode_size == other.inode_size
            && self.block_group_nr == other.block_group_nr
            && self.feature_compat == other.feature_compat
            && self.feature_incompat == other.feature_incompat
            && self.feature_ro_compat == other.feature_ro_compat
            && self.uuid == other.uuid
            && self.volume_name == other.volume_name
            && self.algo_bitmap == other.algo_bitmap
            && self.prealloc_blocks == other.prealloc_blocks
            && self.prealloc_dir_blocks == other.prealloc_dir_blocks
            && self.journal_uuid == other.journal_uuid
            && self.journal_inum == other.journal_inum
            && self.journal_dev == other.journal_dev
            && self.last_orphan == other.last_orphan
            && self_hash_seed == other_hash_seed
            && self.def_hash_version == other.def_hash_version
            && self.default_mount_options == other.default_mount_options
            && self.first_meta_bg == other.first_meta_bg
    }
}

bitflags! {
    /// These are optional features for an implementation to support, but offer performance or reliability gains to
    /// implementations that do support them.
    pub struct OptionalFeatures: u32 {
        ///  Preallocate some number of (contiguous?) blocks (see byte 205 in the superblock) to a directory when creating
        /// a new one.
        const DIR_PREALLOC  =   0x0000_0001;

        /// AFS server inodes exist.
        const IMAGIC_INODES =   0x0000_0002;

        /// File system has a journal (Ext3).
        const HAS_JOURNAL   =   0x0000_0004;

        /// Inodes have extended attributes.
        const EXT_ATTR      =   0x0000_0008;

        /// File system can resize itself for larger partitions.
        const RESIZE_INO    =   0x0000_0010;

        /// Directories use hash index.
        const DIR_INDEX     =   0x0000_0020;
    }
}

bitflags! {
    /// These features if present on a file system are required to be supported by an implementation in order to correctly
    /// read from or write to the file system.
    pub struct RequiredFeatures: u32 {
        /// Compression is used
        const COMPRESSION   =   0x0000_0001;

        /// Directory entries contain a type field.
        const FILETYPE      =   0x0000_0002;

        /// File system needs to replay its journal.
        const RECOVER       =   0x0000_0004;

        /// File system uses a journal device.
        const JOURNAL_DEV   =   0x0000_0008;

        /// Meta Block Groups option (see [this paragraph](https://docs.kernel.org/filesystems/ext4/overview.html#meta-block-groups) from the ext4 documentation).
        const META_BG       =   0x0000_0010;
    }
}

bitflags! {
    /// These features, if present on a file system, are required in order for an implementation to write to the file system,
    /// but are not required to read from the file system.
    pub struct ReadOnlyFeatures: u32 {
        /// Sparse superblocks and group descriptor tables.
        const SPARSE_SUPER  =   0x0000_0001;

        /// File system uses a 64-bit file size.
        const LARGE_FILE    =   0x0000_0002;

        /// Directory contents are stored in the form of a Binary Tree.
        const BTREE_DIR     =   0x0000_0004;
    }
}

/// Compression Algorithm.
///
/// See the [*The Second Extended Filesystem* book](https://www.nongnu.org/ext2-doc/ext2.html#s-algo-bitmap) for more information.
#[repr(u32)]
#[derive(Debug, Clone, Copy)]
pub enum CompressionAlgorithm {
    /// [Lempi-Ziv-Welch compression algorithm](https://en.wikipedia.org/wiki/Lempel-Ziv-Welch).
    LZV1 = 0x0000_0001,

    /// [LZRW compression algorithm](https://en.wikipedia.org/wiki/LZRW) variant LZRW3-A.
    LZRW3A = 0x0000_0002,

    /// [GZIP algorithm](https://en.wikipedia.org/wiki/Gzip).
    GZIP = 0x0000_0004,

    /// [bzip2 algorithm](https://en.wikipedia.org/wiki/Bzip2).
    BZIP2 = 0x0000_0008,

    /// [Lempel-Zip-Oberhumer algorithm](https://en.wikipedia.org/wiki/Lempel-Ziv-Oberhumer).
    LZO = 0x0000_0010,
}

impl TryFrom<u32> for CompressionAlgorithm {
    type Error = Ext2Error;

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        match value {
            0x0000_0001 => Ok(Self::LZV1),
            0x0000_0002 => Ok(Self::LZRW3A),
            0x0000_0004 => Ok(Self::GZIP),
            0x0000_0008 => Ok(Self::BZIP2),
            0x0000_0010 => Ok(Self::LZO),
            _ => Err(Ext2Error::InvalidCompressionAlgorithm(value)),
        }
    }
}

impl From<CompressionAlgorithm> for u32 {
    fn from(value: CompressionAlgorithm) -> Self {
        value as Self
    }
}

impl ExtendedFields {
    /// Returns the [`OptionalFeatures`] described in thoses extended fields.
    ///
    /// Returns [`None`] if an unknown feature is set.
    #[must_use]
    pub const fn optional_features(&self) -> OptionalFeatures {
        OptionalFeatures::from_bits_truncate(self.feature_compat)
    }

    /// Returns the [`RequiredFeatures`] described in thoses extended fields.
    ///
    /// Returns [`None`] if an unknown feature is set.
    #[must_use]
    pub const fn required_features(&self) -> RequiredFeatures {
        RequiredFeatures::from_bits_truncate(self.feature_incompat)
    }

    /// Returns the [`ReadOnlyFeatures`] described in thoses extended fields.
    ///
    /// Returns [`None`] if an unknown feature is set.
    #[must_use]
    pub const fn read_only_features(&self) -> ReadOnlyFeatures {
        ReadOnlyFeatures::from_bits_truncate(self.feature_ro_compat)
    }
}

/// Superblock of the Ext2 filesystem.
#[derive(Debug, Clone)]
pub enum Superblock {
    /// Basic superblock (with a [`major version`](struct.Base.html#structfield.rev_level) lower than 1).
    Basic(Base),

    /// Extended superblock (with a [`major_version`](struct.Base.html#structfield.rev_level) greater than or equal to
    /// 1).
    Extended(Base, ExtendedFields),
}

impl Superblock {
    /// Parse the superblock from the given device.
    ///
    /// # Errors
    ///
    /// Returns [`Ext2Error::BadMagic`] if the magic number found in the superblock is not equal to [`EXT2_SIGNATURE`].
    ///
    /// Returns an [`Error::Device`] if the device could not be read.
    pub fn parse<Dev: Device<u8, Ext2Error>>(celled_device: &Celled<Dev>) -> Result<Self, Error<Ext2Error>> {
        let mut device = celled_device.lock();

        // SAFETY: all the possible failures are catched in the resulting error
        let superblock_base = unsafe { device.read_at::<Base>(Address::from(SUPERBLOCK_START_BYTE)) }?;

        if superblock_base.magic != EXT2_SIGNATURE {
            Err(Error::Fs(FsError::Implementation(Ext2Error::BadMagic(superblock_base.magic))))
        } else if superblock_base.rev_level == 0 {
            Ok(Self::Basic(superblock_base))
        } else {
            let superblock_extended_fields =
                // SAFETY: all the possible failures are catched in the resulting error
                unsafe { device.read_at::<ExtendedFields>(Address::from(SUPERBLOCK_START_BYTE + usize_to_u64(size_of::<Base>()))) }?;
            Ok(Self::Extended(superblock_base, superblock_extended_fields))
        }
    }

    /// Does the superblock contain the extended fields ?
    #[must_use]
    pub const fn is_extended(&self) -> bool {
        match self {
            Self::Basic(_) => false,
            Self::Extended(_, _) => true,
        }
    }

    /// Returns the base fields of the superblock.
    #[must_use]
    pub const fn base(&self) -> &Base {
        match self {
            Self::Basic(base) | Self::Extended(base, _) => base,
        }
    }

    /// Returns the mutable base fields of the superblock.
    #[must_use]
    pub(super) const fn base_mut(&mut self) -> &mut Base {
        match self {
            Self::Basic(base) | Self::Extended(base, _) => base,
        }
    }

    /// Returns the extended fields of the superblock (if they exist).
    #[must_use]
    pub const fn extended_fields(&self) -> Option<&ExtendedFields> {
        match self {
            Self::Basic(_) => None,
            Self::Extended(_, extended_fields) => Some(extended_fields),
        }
    }

    /// Returns the state of this filesystem.
    ///
    /// # Errors
    ///
    /// Returns an [`Ext2Error::InvalidState`] if an invalid state has been found.
    pub const fn state(&self) -> Result<State, Ext2Error> {
        self.base().state()
    }

    /// Returns the error handling method of this filesystem.
    ///
    /// # Errors
    ///
    /// Returns an [`Ext2Error::InvalidState`] if an invalid state has been found.
    pub const fn error_handling_method(&self) -> Result<ErrorHandlingMethod, Ext2Error> {
        self.base().error_handling_method()
    }

    /// Returns the Operating system from which the filesystem on this volume was created.
    #[must_use]
    pub const fn creator_operating_system(&self) -> OperatingSystem {
        self.base().creator_operating_system()
    }

    /// Returns the number of block groups.
    ///
    /// It is equal to the round up of the total number of blocks divided by the number of blocks per block group.
    #[must_use]
    pub const fn block_group_count(&self) -> u32 {
        self.base().block_group_count()
    }

    /// Returns the size of a block in the filesystem described by this superblock.
    #[must_use]
    pub const fn block_size(&self) -> u32 {
        self.base().block_size()
    }

    /// Returns the size of a fragment in the filesystem described by this superblock.
    #[must_use]
    pub const fn frag_size(&self) -> u32 {
        self.base().frag_size()
    }

    /// Returns the first non-reserved inode in file system.
    #[must_use]
    pub const fn first_non_reserved_inode(&self) -> u32 {
        match self {
            Self::Basic(_) => 11,
            Self::Extended(_, extended_fields) => extended_fields.first_ino,
        }
    }

    /// Returns the size of each inode in bytes.
    #[must_use]
    pub const fn inode_size(&self) -> u16 {
        match self {
            Self::Basic(_) => 128,
            Self::Extended(_, extended_fields) => extended_fields.inode_size,
        }
    }

    /// Returns the maximal size in bytes for a single file.
    #[must_use]
    pub const fn max_file_size(&self) -> u64 {
        self.base().max_file_size()
    }

    /// Returns the [`OptionalFeatures`] described in thoses extended fields.
    ///
    /// Returns [`None`] if an unknown feature is set.
    ///
    /// # Errors
    ///
    /// Returns a [`Ext2Error::NoExtendedFields`] if the given superblock does not contain the extended fields.
    pub const fn optional_features(&self) -> Result<OptionalFeatures, Ext2Error> {
        match self {
            Self::Basic(_) => Err(Ext2Error::NoExtendedFields),
            Self::Extended(_, extended_fields) => Ok(extended_fields.optional_features()),
        }
    }

    /// Returns the [`RequiredFeatures`] described in thoses extended fields.
    ///
    /// Returns [`None`] if an unknown feature is set.
    ///
    /// # Errors
    ///
    /// Returns a [`Ext2Error::NoExtendedFields`] if the given superblock does not contain the extended fields.
    pub const fn required_features(&self) -> Result<RequiredFeatures, Ext2Error> {
        match self {
            Self::Basic(_) => Err(Ext2Error::NoExtendedFields),
            Self::Extended(_, extended_fields) => Ok(extended_fields.required_features()),
        }
    }

    /// Returns the [`ReadOnlyFeatures`] described in thoses extended fields.
    ///
    /// Returns [`None`] if an unknown feature is set.
    ///
    /// # Errors
    ///
    /// Returns a [`Ext2Error::NoExtendedFields`] if the given superblock does not contain the extended fields.
    pub const fn read_only_features(&self) -> Result<ReadOnlyFeatures, Ext2Error> {
        match self {
            Self::Basic(_) => Err(Ext2Error::NoExtendedFields),
            Self::Extended(_, extended_fields) => Ok(extended_fields.read_only_features()),
        }
    }

    /// Returns the containing block group of the given block.
    #[must_use]
    pub const fn block_group(&self, block_number: u32) -> u32 {
        (block_number - self.base().first_data_block) / self.base().blocks_per_group
    }

    /// Returns the offset of this block in its containing block group.
    #[must_use]
    pub const fn group_index(&self, block_number: u32) -> u32 {
        (block_number - self.base().first_data_block) % self.base().blocks_per_group
    }
}

#[cfg(test)]
mod test {
    use alloc::vec;
    use core::mem::size_of;
    use std::fs::File;

    use super::Superblock;
    use crate::celled::Celled;
    use crate::fs::ext2::superblock::{Base, ExtendedFields};

    #[test]
    fn struct_size() {
        assert_eq!(size_of::<Base>(), 84);
        assert_eq!(size_of::<Base>() + size_of::<ExtendedFields>(), 264);
    }

    fn basic_superblock(file: File) {
        let celled_file = Celled::new(file);
        let superblock = Superblock::parse(&celled_file).unwrap();
        assert!(!superblock.is_extended());
        let base = superblock.base();
        let major_version = base.rev_level;
        assert_eq!(major_version, 0);
    }

    fn extended_superblock(file: File) {
        let celled_file = Celled::new(file);
        let superblock = Superblock::parse(&celled_file).unwrap();
        assert!(superblock.is_extended());
        let base = superblock.base();
        let major_version = base.rev_level;
        assert_eq!(major_version, 1);
    }

    #[test]
    fn failed_parse() {
        let device = vec![0_u8; 2048];
        let celled_device = Celled::new(device);
        assert!(Superblock::parse(&celled_device).is_err());
    }

    mod generated {
        use crate::tests::generate_fs_test;

        generate_fs_test!(basic_superblock, "./tests/fs/ext2/base.ext2");
        generate_fs_test!(extended_superblock, "./tests/fs/ext2/extended.ext2");
    }
}
