//! Path manipulation for UNIX-like filesystems

use alloc::borrow::{Cow, ToOwned};
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::str::FromStr;

use once_cell::sync::Lazy;
use regex::Regex;

/// A general structure to implement paths.
///
/// A [`UnixStr`] cannot be empty nor contain <NUL> character ('\0')! It is guaranteed at creation time.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnixStr<'path>(Cow<'path, str>);

impl<'path> UnixStr<'path> {
    /// Creates a new [`UnixStr`] from a string.
    ///
    /// # Examples
    ///
    /// ```
    /// use efs::path::UnixStr;
    ///
    /// let valid = UnixStr::new("/").unwrap();
    /// ```
    ///
    /// ```should_panic
    /// use efs::path::UnixStr;
    ///
    /// let not_valid = UnixStr::new("").unwrap();
    /// ```
    #[inline]
    #[must_use]
    pub fn new(str: &'path str) -> Option<Self> {
        if str.is_empty() || str.contains('\0') { None } else { Some(Self(Cow::from(str))) }
    }

    /// Checks whether the inner string contains exactly two leading '/' characters
    fn starts_with_two_slashes(&self) -> bool {
        self.0.starts_with("//") && !self.0.starts_with("///")
    }
}

impl FromStr for UnixStr<'_> {
    type Err = &'static str;

    #[inline]
    fn from_str(str: &str) -> Result<Self, Self::Err> {
        if str.is_empty() || str.contains('\0') {
            Err("Tried to make a UnixStr from an empty string")
        } else {
            Ok(Self(Cow::Owned(str.to_owned())))
        }
    }
}

impl ToString for UnixStr<'_> {
    #[inline]
    fn to_string(&self) -> String {
        self.0.to_string()
    }
}

impl<'path> From<Component<'path>> for UnixStr<'path> {
    #[inline]
    fn from(value: Component<'path>) -> Self {
        match value {
            Component::RootDir => Self(Cow::from("/")),
            Component::DoubleSlashRootDir => Self(Cow::from("//")),
            Component::CurDir => Self(Cow::from(".")),
            Component::ParentDir => Self(Cow::from("..")),
            Component::Normal(name) => name,
        }
    }
}

/// A slice of a path
///
/// It is represented by a string that is used to identify a file. It has optional beginning `/`, followed by zero or more filenames
/// separated by `/`. A pathname can optionally contain one or more trailing `/`. Multiple successive `/` characters are considered
/// to be the same as one `/`, except for the case of exactly two leading `/`.
///
/// See [the POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_271) for more informations.
#[derive(Debug, Clone)]
#[cfg_attr(not(doc), repr(transparent))]
pub struct Path<'path> {
    /// Inner representation of a bath by a [`UnixStr`].
    name: UnixStr<'path>,
}

impl<'path> Path<'path> {
    /// Directly wraps a [`UnixStr`] slice as a [`Path`] slice.
    #[inline]
    #[must_use]
    pub fn new<US: Into<UnixStr<'path>>>(str: US) -> Self {
        Self { name: str.into() }
    }

    /// Checks if the path is absolute.
    ///
    /// Defined in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_02).
    ///
    /// Examples
    ///
    /// ```
    /// use core::str::FromStr;
    ///
    /// use efs::path::Path;
    ///
    /// assert!(Path::from_str("/home").unwrap().is_absolute());
    /// assert!(!Path::from_str("./foo/bar").unwrap().is_absolute());
    /// assert!(!Path::from_str("//home").unwrap().is_absolute());
    /// ```
    #[inline]
    #[must_use]
    pub fn is_absolute(&self) -> bool {
        self.name.0.starts_with('/') && !self.name.starts_with_two_slashes()
    }

    /// Checks if the path is absolute.
    ///
    /// Defined in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_324).
    ///
    /// # Examples
    ///
    /// ```
    /// use core::str::FromStr;
    ///
    /// use efs::path::Path;
    ///
    /// assert!(Path::from_str("./foo/bar").unwrap().is_relative());
    /// assert!(!Path::from_str("/home").unwrap().is_relative());
    /// assert!(!Path::from_str("//home").unwrap().is_relative());
    /// ```
    #[inline]
    #[must_use]
    pub fn is_relative(&self) -> bool {
        !self.name.0.starts_with('/')
    }

    /// Returns the canonical path associated with `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::str::FromStr;
    ///
    /// use efs::path::Path;
    ///
    /// assert_eq!(
    ///     Path::from_str("/home/user/foo").unwrap(),
    ///     Path::from_str("/home//user///foo").unwrap().canonical()
    /// );
    ///
    /// assert_eq!(
    ///     Path::from_str("//bin/foo").unwrap(),
    ///     Path::from_str("//bin///foo").unwrap().canonical()
    /// );
    ///
    /// assert_eq!(Path::from_str("foo/bar").unwrap(), Path::from_str("foo/bar").unwrap().canonical());
    /// assert_eq!(
    ///     Path::from_str("foo/bar/").unwrap(),
    ///     Path::from_str("foo///bar//").unwrap().canonical()
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn canonical(&self) -> Self {
        /// Regex matching one slash or more.
        static SLASHES: Lazy<Regex> = Lazy::new(|| Regex::new("/+").unwrap_or_else(|_| unreachable!()));

        let almost_canonical = SLASHES.replace_all(self.name.0.to_string().as_str(), "/").to_string();
        if self.name.starts_with_two_slashes() {
            let mut canon = "/".to_owned();
            canon.push_str(&almost_canonical);
            Self {
                name: UnixStr(Cow::from(canon)),
            }
        } else {
            Self {
                name: UnixStr(Cow::from(almost_canonical)),
            }
        }
    }

    /// Yields the underlying [`UnixStr`] slice.
    #[inline]
    #[must_use]
    pub const fn as_unix_str(&self) -> &UnixStr<'path> {
        &self.name
    }

    /// Yields a mutable referebce to the underlying [`UnixStr`] slice.
    #[inline]
    #[must_use]
    pub const fn as_mut_unix_str(&mut self) -> &mut UnixStr<'path> {
        &mut self.name
    }

    /// Produces an iterator over the Components of the path.
    #[inline]
    #[must_use]
    pub fn components(&'path self) -> Components<'path> {
        Components::new(self)
    }
}

impl FromStr for Path<'_> {
    type Err = &'static str;

    #[inline]
    fn from_str(str: &str) -> Result<Self, Self::Err> {
        Ok(Self::new(UnixStr::from_str(str)?))
    }
}

impl ToString for Path<'_> {
    #[inline]
    fn to_string(&self) -> String {
        self.as_unix_str().to_string()
    }
}

impl<'path> From<UnixStr<'path>> for Path<'path> {
    #[inline]
    fn from(value: UnixStr<'path>) -> Self {
        Self { name: value }
    }
}

impl PartialEq for Path<'_> {
    /// This method tests for `self` and `other` values to be equal, and is used by `==`.
    ///
    /// This checks for equivalence in the pathname, not strict equality or pathname resolution.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::str::FromStr;
    ///
    /// use efs::path::{Path, UnixStr};
    ///
    /// assert_eq!(Path::from_str("/").unwrap(), Path::from_str("///").unwrap());
    ///
    /// assert_eq!(Path::from_str("/home//").unwrap(), Path::from_str("///home/").unwrap());
    ///
    /// assert_eq!(Path::from_str("//").unwrap(), Path::from_str("//").unwrap());
    ///
    /// assert_ne!(Path::from_str("/").unwrap(), Path::from_str("//").unwrap());
    /// assert_ne!(Path::from_str("//home").unwrap(), Path::from_str("/home").unwrap());
    /// ```
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        if (self.name.starts_with_two_slashes() && !other.name.starts_with_two_slashes())
            || (!self.name.starts_with_two_slashes() && other.name.starts_with_two_slashes())
        {
            return false;
        }

        match (self.name.0.strip_prefix('/'), other.name.0.strip_prefix('/')) {
            (None, None) | (Some(_), Some(_)) => {},
            _ => return false,
        }

        match (self.name.0.strip_suffix('/'), other.name.0.strip_suffix('/')) {
            (None, None) | (Some(_), Some(_)) => {},
            _ => return false,
        }

        let self_chars = self.name.0.chars().filter(|ch| ch != &'/').collect::<Vec<char>>();
        let other_chars = other.name.0.chars().filter(|ch| ch != &'/').collect::<Vec<char>>();

        self_chars == other_chars
    }
}

impl Eq for Path<'_> {}

/// Component parsing works by a double-ended state machine; the cursors at the
/// front and back of the path each keep track of what parts of the path have
/// been consumed so far.
///
/// Going front to back, a path is made up of a starting directory component, and a body (of normal components).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum State {
    /// `/` or `.` or nothing
    StartDir,

    /// `foo/bar/baz`
    Body,

    /// Everything has been consumed
    Done,
}

/// A single component of a path.
///
/// A Component roughly corresponds to a substring between path separators (`/`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Component<'path> {
    /// The root directory component, appears before anything else.
    ///
    ///It represents a `/` that designates that a path starts from root.
    RootDir,

    /// The root directory component on its two-slashes version, appears before anything else.
    ///
    /// It represents `//` that designates that a path starts from the special root `//`.
    DoubleSlashRootDir,

    /// A reference to the current directory, i.e., `.`.
    CurDir,

    /// A reference to the parent directory, i.e., `..`.
    ParentDir,

    /// A normal component, e.g., `a` and `b` in `a/b`.
    ///
    /// This variant is the most common one, it represents references to files or directories.
    Normal(UnixStr<'path>),
}

impl FromStr for Component<'_> {
    type Err = &'static str;

    #[inline]
    fn from_str(str: &str) -> Result<Self, Self::Err> {
        match str {
            "" => Err("Tried to create a path component from an empty string"),
            "/" => Ok(Self::RootDir),
            "//" => Ok(Self::DoubleSlashRootDir),
            "." => Ok(Self::CurDir),
            ".." => Ok(Self::ParentDir),
            _ => Ok(Self::Normal(UnixStr::from_str(str)?)),
        }
    }
}

/// An iterator over the [`Component`]s of a [`Path`].
#[derive(Debug)]
pub struct Components<'path> {
    /// The path left to parse components from.
    ///
    /// It must be ensure that the given `path` is under a canonical form.
    path: &'path [u8],

    /// Is the *original* path rooted ?
    has_root: bool,

    /// Keeps track of what has been consumed on the left side of the path.
    front: State,

    /// Keeps track of what has been consumed on the right side of the path.
    back: State,
}

impl<'path> Components<'path> {
    /// Returns the [`Components`] associated to a [`Path`]
    #[inline]
    #[must_use]
    pub fn new(path: &'path Path<'path>) -> Self {
        Self {
            path: path.name.0.as_bytes(),
            has_root: path.is_absolute(),
            front: State::StartDir,
            back: State::StartDir,
        }
    }

    /// Is the iteration complete ?
    #[inline]
    #[must_use]
    pub fn is_finished(&self) -> bool {
        self.front == State::Done || self.back == State::Done
    }

    /// Should the normalized path include a leading `.` ?
    fn include_cur_dir(&self) -> bool {
        if self.has_root {
            return false;
        };

        let mut iter = self.path.iter();
        match (iter.next(), iter.next()) {
            (Some(&b'.'), None) => true,
            (Some(&b'.'), Some(&byte)) => byte == b'/',
            _ => false,
        }
    }

    /// Parse a component from the left, saying how many bytes to consume to remove it.
    fn parse_next_component(&self) -> (usize, Option<Component<'path>>) {
        let (extra, comp) = self.path.iter().position(|byte| byte == &b'/').map_or((0_usize, self.path), |idx| {
            (
                1_usize,
                &self
                    .path
                    .get(..idx)
                    .unwrap_or_else(|| unreachable!("The index exists since it is returned by the find function")),
            )
        });

        // SAFETY: `comp` is a valid substring since it is split on `/`
        (comp.len() + extra, Component::from_str(&unsafe { String::from_utf8_unchecked(comp.to_vec()) }).ok())
    }
}

impl<'path> Iterator for Components<'path> {
    type Item = Component<'path>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        while !self.is_finished() {
            match self.front {
                State::StartDir => {
                    self.front = State::Body;
                    if self.path.starts_with(&[b'/', b'/']) {
                        // SAFETY: `self.path` contains at least 2 element
                        self.path = unsafe { &self.path.get_unchecked(2..) };
                        return Some(Component::DoubleSlashRootDir);
                    } else if self.path.starts_with(&[b'/']) {
                        // SAFETY: `self.path` contains at least 1 element
                        self.path = unsafe { &self.path.get_unchecked(1..) };
                        return Some(Component::RootDir);
                    } else if self.include_cur_dir() {
                        // SAFETY: `self.path` contains at least 1 element
                        self.path = unsafe { &self.path.get_unchecked(1..) };
                        return Some(Component::CurDir);
                    }
                },
                State::Body if !self.path.is_empty() => {
                    let (size, comp) = self.parse_next_component();
                    // SAFETY: It is ensure in `parse_next_component` that `self.path` contains at least `size` characters
                    self.path = unsafe { &self.path.get_unchecked(size..) };
                    if comp.is_some() {
                        return comp;
                    }
                },
                State::Body => {
                    self.front = State::Done;
                },
                State::Done => unreachable!(),
            }
        }

        None
    }
}

/// Root directory
pub static ROOT: Lazy<Path> = Lazy::new(|| Path::from_str("/").unwrap_or_else(|_| unreachable!("ROOT is a non-empty path")));

#[cfg(test)]
mod test {
    use core::str::FromStr;

    use crate::path::{Component, Path, UnixStr};

    #[test]
    fn unix_str_creation() {
        assert!(UnixStr::new("/").is_some());
        assert!(UnixStr::new("/home//user///foo").is_some());

        assert!(UnixStr::new("").is_none());
        assert!(UnixStr::new("/home//user///\0foo").is_none());
    }

    #[test]
    fn path_eq() {
        assert_eq!(Path::from_str("/").unwrap(), Path::from_str("/").unwrap());
        assert_eq!(Path::from_str("/").unwrap(), Path::from_str("///").unwrap());
        assert_eq!(Path::from_str("///").unwrap(), Path::from_str("/").unwrap());

        assert_eq!(Path::from_str("/home").unwrap(), Path::from_str("/home").unwrap());
        assert_eq!(Path::from_str("/home//").unwrap(), Path::from_str("///home/").unwrap());

        assert_eq!(Path::from_str("//").unwrap(), Path::from_str("//").unwrap());
        assert_eq!(Path::from_str("//home/").unwrap(), Path::from_str("//home/").unwrap());

        assert_ne!(Path::from_str("/").unwrap(), Path::from_str("//").unwrap());
        assert_ne!(Path::from_str("//home").unwrap(), Path::from_str("/home").unwrap());
    }

    #[test]
    fn path_canonical() {
        assert_eq!(Path::from_str("/").unwrap(), Path::from_str("/").unwrap());
        assert_eq!(Path::from_str("/").unwrap(), Path::from_str("///").unwrap());
        assert_eq!(Path::from_str("///").unwrap(), Path::from_str("/").unwrap());

        assert_eq!(Path::from_str("/home").unwrap(), Path::from_str("/home").unwrap());
        assert_eq!(Path::from_str("/home//").unwrap(), Path::from_str("///home/").unwrap());

        assert_eq!(Path::from_str("//").unwrap(), Path::from_str("//").unwrap());
        assert_eq!(Path::from_str("//home/").unwrap(), Path::from_str("//home/").unwrap());

        assert_ne!(Path::from_str("/").unwrap(), Path::from_str("//").unwrap());
        assert_ne!(Path::from_str("//home").unwrap(), Path::from_str("/home").unwrap());
    }

    #[test]
    fn path_components() {
        let path = Path::from_str("/home/user/foo").unwrap();
        let mut components = path.components();

        assert_eq!(components.next(), Some(Component::RootDir));
        assert_eq!(components.next(), Some(Component::Normal(UnixStr::from_str("home").unwrap())));
        assert_eq!(components.next(), Some(Component::Normal(UnixStr::from_str("user").unwrap())));
        assert_eq!(components.next(), Some(Component::Normal(UnixStr::from_str("foo").unwrap())));
        assert_eq!(components.next(), None);

        let path = Path::from_str("./foo//../baz").unwrap();
        let mut components = path.components();

        assert_eq!(components.next(), Some(Component::CurDir));
        assert_eq!(components.next(), Some(Component::Normal(UnixStr::from_str("foo").unwrap())));
        assert_eq!(components.next(), Some(Component::ParentDir));
        assert_eq!(components.next(), Some(Component::Normal(UnixStr::from_str("baz").unwrap())));
        assert_eq!(components.next(), None);

        let path = Path::from_str("foo/bar///..").unwrap();
        let mut components = path.components();

        assert_eq!(components.next(), Some(Component::Normal(UnixStr::from_str("foo").unwrap())));
        assert_eq!(components.next(), Some(Component::Normal(UnixStr::from_str("bar").unwrap())));
        assert_eq!(components.next(), Some(Component::ParentDir));
        assert_eq!(components.next(), None);

        let path = Path::from_str("//home/foo/.././").unwrap();
        let mut components = path.components();

        assert_eq!(components.next(), Some(Component::DoubleSlashRootDir));
        assert_eq!(components.next(), Some(Component::Normal(UnixStr::from_str("home").unwrap())));
        assert_eq!(components.next(), Some(Component::Normal(UnixStr::from_str("foo").unwrap())));
        assert_eq!(components.next(), Some(Component::ParentDir));
        assert_eq!(components.next(), Some(Component::CurDir));
        assert_eq!(components.next(), None);
    }
}
