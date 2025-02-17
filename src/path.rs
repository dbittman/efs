//! Path manipulation for UNIX-like filesystems.

use alloc::borrow::{Cow, ToOwned};
use alloc::ffi::CString;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::iter::FusedIterator;
use core::ops::Deref;
use core::str::FromStr;
use core::{error, fmt};

use derive_more::derive::Display;
use once_cell::sync::Lazy;
use regex::Regex;

/// Enumeration of possible errors encountered with [`Path`]s' manipulation.
#[allow(clippy::module_name_repetitions)]
#[derive(Debug, PartialEq, Eq, Display)]
#[display("Path Error: {_variant}")]
pub enum PathError {
    /// Indicates that the given path is relative while an absolute one is needed.
    #[display("Invalid Filename: \"{_0}\" is either empty or contains a \"\0\" character")]
    AbsolutePathRequired(String),

    /// Indicates that a given [`CString`] is ill-formed and cannot be converted to a [`UnixStr`].
    #[display("Invalid CString: \"{_0:?}\" is ill-formed")]
    InvalidCString(CString),

    /// Indicates that a given filename is either empty or contains a `\0` character.
    #[display("Absolute Path Needed: \"{_0}\" is relative while an absolute path is requested")]
    InvalidFilename(String),
}

impl error::Error for PathError {}

/// A general structure to implement paths.
///
/// A [`UnixStr`] cannot be empty nor contain `<NUL>` character ('\0')! It is guaranteed at creation time.
#[repr(transparent)]
#[derive(Debug, Clone, PartialEq, Eq, Display)]
pub struct UnixStr<'path>(Cow<'path, str>);

impl<'path> Deref for UnixStr<'path> {
    type Target = Cow<'path, str>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'path> UnixStr<'path> {
    /// Creates a new [`UnixStr`] from a string.
    ///
    /// # Errors
    ///
    /// Returns an [`InvalidFilename`](PathError::InvalidFilename) if the given string is empty or contains a `\0`
    /// character.
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
    pub fn new(str: &'path str) -> Result<Self, PathError> {
        (!str.is_empty() && !str.contains('\0'))
            .then_some(Self(Cow::from(str)))
            .ok_or_else(|| PathError::InvalidFilename(str.to_owned()))
    }

    /// Checks whether the inner string contains exactly two leading '/' characters.
    fn starts_with_two_slashes(&self) -> bool {
        self.0.starts_with("//") && !self.0.starts_with("///")
    }

    /// Returns whether the [`UnixStr`] ends with a trailing backslash.
    #[must_use]
    pub fn has_trailing_backslash(&self) -> bool {
        self.0.ends_with('/')
    }

    /// Creates a copy of this object whose lifetime is arbitrary.
    ///
    /// # Examples
    ///
    /// ```
    /// use efs::path::UnixStr;
    ///
    /// let root = UnixStr::new("/").unwrap();
    /// let static_root: UnixStr<'static> = root.to_owned();
    /// ```
    #[must_use]
    pub fn to_owned<'out>(&self) -> UnixStr<'out> {
        UnixStr(Cow::Owned(self.0.to_string()))
    }
}

impl FromStr for UnixStr<'_> {
    type Err = PathError;

    fn from_str(str: &str) -> Result<Self, Self::Err> {
        (!str.is_empty() && !str.contains('\0'))
            .then_some(Self(Cow::Owned(str.to_owned())))
            .ok_or_else(|| PathError::InvalidFilename(str.to_owned()))
    }
}

impl TryFrom<CString> for UnixStr<'_> {
    type Error = <Self as FromStr>::Err;

    fn try_from(value: CString) -> Result<Self, Self::Error> {
        UnixStr::from_str(value.clone().into_string().map_err(|_err| PathError::InvalidCString(value))?.as_str())
    }
}

impl From<UnixStr<'_>> for CString {
    fn from(value: UnixStr) -> Self {
        // SAFETY: `value` cannot contain any <NUL> char
        unsafe { Self::from_vec_unchecked(value.0.as_bytes().to_vec()) }
    }
}

impl<'path> From<Component<'path>> for UnixStr<'path> {
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

/// A slice of a path.
///
/// It is represented by a string that is used to identify a file. It has optional beginning `/`, followed by zero or
/// more filenames separated by `/`. A pathname can optionally contain one or more trailing `/`. Multiple successive `/`
/// characters are considered to be the same as one `/`, except for the case of exactly two leading `/`.
///
/// See [the POSIX definition](https://pubs.opengroup.org/onlinepubs/9799919799/basedefs/V1_chap03.html#tag_03_254) for more information.
#[derive(Debug, Clone, Display)]
#[display("{}", self.as_unix_str())]
#[cfg_attr(not(doc), repr(transparent))]
pub struct Path<'path> {
    /// Inner representation of a bath by a [`UnixStr`].
    name: UnixStr<'path>,
}

impl<'path> Path<'path> {
    /// Directly wraps a [`UnixStr`] slice as a [`Path`] slice.
    #[must_use]
    pub fn new<US: Into<UnixStr<'path>>>(str: US) -> Self {
        Self { name: str.into() }
    }

    /// Creates a path from an unchecked UTF-8 sequence of bytes.
    ///
    /// # Safety
    ///
    /// Must ensure that the given slice is a valie UTF-8 sequence.
    unsafe fn from_ut8_slice(slice: &[u8]) -> Result<Self, PathError> {
        Ok(Self::new(UnixStr::from_str(&String::from_utf8_unchecked(slice.to_vec()))?))
    }

    /// Checks if the path is absolute.
    ///
    /// Defined in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9799919799/basedefs/V1_chap03.html#tag_03_02).
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
    /// assert!(Path::from_str("//home").unwrap().is_absolute());
    /// ```
    #[must_use]
    pub fn is_absolute(&self) -> bool {
        self.name.0.starts_with('/')
    }

    /// Checks if the path is relative.
    ///
    /// Defined in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9799919799/basedefs/V1_chap03.html#tag_03_311).
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
    #[must_use]
    pub const fn as_unix_str(&self) -> &UnixStr<'path> {
        &self.name
    }

    /// Yields a mutable reference to the underlying [`UnixStr`] slice.
    #[must_use]
    pub const fn as_mut_unix_str(&mut self) -> &mut UnixStr<'path> {
        &mut self.name
    }

    /// Returns a new [`Path`] which is obtained from `self` after extending it with `path`.
    ///
    /// If `path` is absolute, does not take `self` into account.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::str::FromStr;
    ///
    /// use efs::path::Path;
    ///
    /// let first_path = Path::from_str("/home").unwrap();
    /// let second_path = Path::from_str("user").unwrap();
    /// assert_eq!(first_path.join(&second_path).canonical(), Path::from_str("/home/user").unwrap());
    ///
    /// let first_path = Path::from_str("/home/").unwrap();
    /// let second_path = Path::from_str("user").unwrap();
    /// assert_eq!(first_path.join(&second_path).canonical(), Path::from_str("/home/user").unwrap());
    ///
    /// let first_path = Path::from_str("./foo").unwrap();
    /// let second_path = Path::from_str("/bar/baz").unwrap();
    /// assert_eq!(first_path.join(&second_path).canonical(), Path::from_str("/bar/baz").unwrap());
    /// ```
    #[must_use]
    pub fn join(&self, path: &Self) -> Self {
        if path.is_absolute() {
            path.clone()
        } else {
            let self_unix_str = self.as_unix_str();
            let mut unix_str = self_unix_str.0.to_string();
            if !self_unix_str.has_trailing_backslash() {
                unix_str.push('/');
            }
            unix_str.extend(path.as_unix_str().0.chars());
            let Ok(new_path) = Path::from_str(&unix_str) else {
                unreachable!("`self` and `path` are both Path so their concatenation is also a valid Path")
            };
            new_path
        }
    }

    /// Returns the size of the string representation.
    #[allow(clippy::len_without_is_empty)]
    #[must_use]
    pub fn len(&self) -> usize {
        self.as_unix_str().0.len()
    }

    /// Returns the `Path` without its final component, if there is one.
    ///
    /// Returns [`None`] if the path terminates in a root or double root.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::str::FromStr;
    ///
    /// use efs::path::Path;
    ///
    /// let path = Path::from_str("/foo/bar").unwrap();
    /// let parent = path.parent().unwrap();
    /// assert_eq!(parent, Path::from_str("/foo").unwrap());
    ///
    /// let grand_parent = parent.parent().unwrap();
    /// assert_eq!(grand_parent, Path::from_str("/").unwrap());
    /// assert_eq!(grand_parent.parent(), None);
    ///
    /// let relative_path = Path::from_str("foo/bar").unwrap();
    /// let parent = relative_path.parent().unwrap();
    /// assert_eq!(parent, Path::from_str("foo").unwrap());
    /// let grand_parent = parent.parent();
    /// assert_eq!(grand_parent, None);
    /// ```
    #[must_use]
    pub fn parent(&self) -> Option<Path<'_>> {
        let mut components = self.components();
        components.into_iter().next_back().and_then(|comp| match comp {
            Component::RootDir | Component::DoubleSlashRootDir => None,
            Component::CurDir | Component::ParentDir | Component::Normal(_) => {
                if components.is_finished() {
                    None
                } else {
                    Some(components.into())
                }
            },
        })
    }

    /// Returns the file name of the final component of this path, **if it's a regular file**.
    ///
    /// Otherwise, it returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// use core::str::FromStr;
    ///
    /// use efs::path::{Path, UnixStr};
    ///
    /// let path = Path::from_str("/foo/bar").unwrap();
    /// assert_eq!(path.file_name(), Some(UnixStr::from_str("bar").unwrap()));
    ///
    /// let path = Path::from_str("foo/bar").unwrap();
    /// assert_eq!(path.file_name(), Some(UnixStr::from_str("bar").unwrap()));
    ///
    /// let path = Path::from_str(".").unwrap();
    /// assert_eq!(path.file_name(), None);
    ///
    /// let path = Path::from_str("..").unwrap();
    /// assert_eq!(path.file_name(), None);
    ///
    /// let path = Path::from_str("/").unwrap();
    /// assert_eq!(path.file_name(), None);
    /// ```
    #[must_use]
    pub fn file_name(&self) -> Option<UnixStr<'_>> {
        self.components().into_iter().next_back().and_then(|p| match p {
            Component::Normal(p) => Some(p),
            _ => None,
        })
    }

    /// Produces an iterator over the Components of the path.
    #[must_use]
    pub fn components(&'path self) -> Components<'path> {
        Components::new(self)
    }
}

impl FromStr for Path<'_> {
    type Err = PathError;

    fn from_str(str: &str) -> Result<Self, Self::Err> {
        Ok(Self::new(UnixStr::from_str(str)?))
    }
}

impl<'path> From<UnixStr<'path>> for Path<'path> {
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

impl TryFrom<&Components<'_>> for Path<'_> {
    type Error = <Self as FromStr>::Err;

    fn try_from(value: &Components<'_>) -> Result<Self, Self::Error> {
        Path::from_str(&value.to_string())
    }
}

/// Root Unix string.
pub static ROOT: Lazy<UnixStr> =
    Lazy::new(|| UnixStr::from_str("/").unwrap_or_else(|_| unreachable!("ROOT is a non-empty path")));

/// Curent directory Unix string.
pub static CUR_DIR: Lazy<UnixStr> =
    Lazy::new(|| UnixStr::from_str(".").unwrap_or_else(|_| unreachable!("CUR_DIR is a non-empty path")));

/// Parent directory Unix string.
pub static PARENT_DIR: Lazy<UnixStr> =
    Lazy::new(|| UnixStr::from_str("..").unwrap_or_else(|_| unreachable!("CUR_DIR is a non-empty path")));

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
/// A [`Component`] roughly corresponds to a substring between path separators (`/`).
#[derive(Debug, Clone, PartialEq, Eq, Display)]
pub enum Component<'path> {
    /// The root directory component, appears before anything else.
    ///
    ///It represents a `/` that designates that a path starts from root.
    #[display("/")]
    RootDir,

    /// The root directory component on its two-slashes version, appears before anything else.
    ///
    /// It represents `//` that designates that a path starts from the special root `//`.
    #[display("//")]
    DoubleSlashRootDir,

    /// A reference to the current directory, i.e., `.`.
    #[display(".")]
    CurDir,

    /// A reference to the parent directory, i.e., `..`.
    #[display("..")]
    ParentDir,

    /// A normal component, e.g., `a` and `b` in `a/b`.
    ///
    /// This variant is the most common one, it represents references to files or directories.
    #[display("{_0}")]
    Normal(UnixStr<'path>),
}

impl FromStr for Component<'_> {
    type Err = PathError;

    fn from_str(str: &str) -> Result<Self, Self::Err> {
        match str {
            "" => Err(PathError::InvalidFilename(str.to_owned())),
            "/" => Ok(Self::RootDir),
            "//" => Ok(Self::DoubleSlashRootDir),
            "." => Ok(Self::CurDir),
            ".." => Ok(Self::ParentDir),
            _ => Ok(Self::Normal(UnixStr::from_str(str)?)),
        }
    }
}

impl<'path> From<Component<'path>> for Path<'path> {
    fn from(value: Component<'path>) -> Self {
        // SAFETY: a valid component can always be converted into a path
        unsafe { Self::new(UnixStr::from_str(&value.to_string()).unwrap_unchecked()) }
    }
}

/// An iterator over the [`Component`]s of a [`Path`].
#[derive(Debug, Clone)]
pub struct Components<'path> {
    /// The path left to parse components from.
    ///
    /// It must be ensure that the given `path` is under a canonical form.
    path: &'path [u8],

    /// Starting dir of the path.
    ///
    /// If [`Some`], can only contain [`RootDir`](enum.Component.html#variant.RootDir),
    /// [`DoubleSlashRootDir`](enum.Component.html#variant.DoubleSlashRootDir) or
    /// [`CurDir`](enum.Component.html#variant.CurDir).
    start_dir: Option<Component<'path>>,

    /// Keeps track of what has been consumed on the left side of the path.
    front: State,

    /// Keeps track of what has been consumed on the right side of the path.
    back: State,
}

impl<'path> Components<'path> {
    /// Returns the [`Components`] associated to a [`Path`].
    #[must_use]
    pub fn new(path: &'path Path<'path>) -> Self {
        let bytes = path.name.0.as_bytes();

        let start_dir = if path.as_unix_str().starts_with_two_slashes() {
            Some(Component::DoubleSlashRootDir)
        } else if path.is_absolute() {
            Some(Component::RootDir)
        } else {
            let mut iter = bytes.iter();
            match (iter.next(), iter.next()) {
                (Some(&b'.'), None | Some(&b'/')) => Some(Component::CurDir),
                _ => None,
            }
        };
        Self {
            path: bytes,
            start_dir,
            front: State::StartDir,
            back: State::Body,
        }
    }

    /// Trims away repetead separators on the left.
    fn trim_left(&mut self) {
        while !self.path.is_empty() {
            let (size, comp) = self.parse_next_component();
            if comp.is_some() {
                return;
            }
            self.path = &self.path[size..];
        }
    }

    /// Trims away repetead separators on the right.
    fn trim_right(&mut self) {
        while self.path.len() > self.len_before_body() {
            let (size, comp) = self.parse_next_component_back();
            if comp.is_some() {
                return;
            }
            self.path = &self.path[..self.path.len() - size];
        }
    }

    /// Does the original path starts with [`RootDir`](Component::RootDir)?
    fn has_root(&self) -> bool {
        self.start_dir == Some(Component::RootDir)
    }

    /// Does the original path starts with [`DoubleSlashRootDir`](Component::DoubleSlashRootDir)?
    fn has_double_slash_root(&self) -> bool {
        self.start_dir == Some(Component::DoubleSlashRootDir)
    }

    /// Does the original path starts with [`CurDir`](Component::CurDir)?
    fn include_cur_dir(&self) -> bool {
        self.start_dir == Some(Component::CurDir)
    }

    /// Is the iteration complete?
    #[must_use]
    pub fn is_finished(&self) -> bool {
        self.front == State::Done || self.back == State::Done || self.path.is_empty()
    }

    /// Number of bytes before the [`Path`]'s body.
    fn len_before_body(&self) -> usize {
        if self.front == State::StartDir {
            match self.start_dir {
                None => 0,
                Some(Component::RootDir | Component::CurDir) => 1,
                Some(Component::DoubleSlashRootDir) => 2,
                _ => unreachable!(),
            }
        } else {
            0
        }
    }

    /// Parse a component from the left, saying how many bytes to consume to remove it.
    fn parse_next_component(&self) -> (usize, Option<Component<'path>>) {
        let (extra, comp) = self.path.iter().position(|byte| byte == &b'/').map_or((0_usize, self.path), |idx| {
            (
                1_usize,
                self.path
                    .get(..idx)
                    .unwrap_or_else(|| unreachable!("The index exists since it is returned by the find function")),
            )
        });

        // SAFETY: `comp` is a valid substring since it is split on `/`
        (comp.len() + extra, Component::from_str(&unsafe { String::from_utf8_unchecked(comp.to_vec()) }).ok())
    }

    /// Parse a component from the right, saying how many bytes to consume to remove it.
    fn parse_next_component_back(&self) -> (usize, Option<Component<'path>>) {
        let start = self.len_before_body();
        let body = self
            .path
            .get(start..)
            .unwrap_or_else(|| unreachable!("This function is only called with `self.back == State::Body`"));
        let (extra, comp) = body.iter().rposition(|byte| byte == &b'/').map_or((0_usize, body), |idx| {
            (
                1_usize,
                self.path
                    .get(start + idx + 1..)
                    .unwrap_or_else(|| unreachable!("The index exists since it is returned by the find function")),
            )
        });

        // SAFETY: `comp` is a valid substring since it is split on `/`
        (comp.len() + extra, Component::from_str(&unsafe { String::from_utf8_unchecked(comp.to_vec()) }).ok())
    }
}

impl<'path> Iterator for &mut Components<'path> {
    type Item = Component<'path>;

    fn next(&mut self) -> Option<Self::Item> {
        while !self.is_finished() {
            match self.front {
                State::StartDir => {
                    self.front = State::Body;
                    if self.has_double_slash_root() {
                        // SAFETY: `self.path` contains at least 2 element
                        self.path = unsafe { self.path.get_unchecked(2..) };
                        return Some(Component::DoubleSlashRootDir);
                    } else if self.has_root() {
                        // SAFETY: `self.path` contains at least 1 element
                        self.path = unsafe { self.path.get_unchecked(1..) };
                        return Some(Component::RootDir);
                    } else if self.include_cur_dir() {
                        // SAFETY: `self.path` contains at least 1 element
                        self.path = unsafe { self.path.get_unchecked(1..) };
                        return Some(Component::CurDir);
                    }
                },
                State::Body if !self.path.is_empty() => {
                    let (size, comp) = self.parse_next_component();
                    // SAFETY: It is ensure in `parse_next_component` that `self.path` contains at least `size`
                    // characters
                    self.path = unsafe { self.path.get_unchecked(size..) };
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

    fn size_hint(&self) -> (usize, Option<usize>) {
        // SAFETY: the remaining `path` always contains a complete string
        let Ok(path) = Path::from_str(unsafe { &String::from_utf8_unchecked(self.path.to_vec()) }) else {
            // If a `Path` cannot be built from the remaining sequence, then it is empty.
            return (0, Some(0));
        };

        let mut canonical_path = path.canonical();
        let mut canonical_str = canonical_path.as_mut_unix_str().0.as_ref();
        let mut extra = 0_usize;

        if canonical_str.starts_with("//") {
            // SAFETY: `canonical_str` begins with two '/'
            unsafe {
                canonical_str = canonical_str.strip_prefix("//").unwrap_unchecked();
            };
            extra += 1;
        } else if canonical_str.starts_with('/') {
            // SAFETY: `canonical_str` begins with one '/'
            unsafe {
                canonical_str = canonical_str.strip_prefix('/').unwrap_unchecked();
            };
            extra += 1;
        }
        if canonical_str.ends_with('/') {
            // SAFETY: `canonical_str` ends with one '/'
            unsafe {
                canonical_str = canonical_str.strip_suffix('/').unwrap_unchecked();
            };
        }

        let nb_components = if canonical_str.is_empty() { extra } else { canonical_str.split('/').count() + extra };
        (nb_components, Some(nb_components))
    }
}

impl DoubleEndedIterator for &mut Components<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        while !self.is_finished() {
            match self.back {
                State::Body if self.path.len() > self.len_before_body() => {
                    let (size, comp) = self.parse_next_component_back();
                    // SAFETY: It is ensure in `parse_next_component_back` that `self.path` contains at least `size`
                    // characters
                    self.path = unsafe { self.path.get_unchecked(..self.path.len() - size) };
                    if comp.is_some() {
                        return comp;
                    }
                },
                State::Body => {
                    self.back = State::StartDir;
                    if self.front == State::StartDir {
                        if self.has_double_slash_root() {
                            self.path = &[];
                            return Some(Component::DoubleSlashRootDir);
                        } else if self.has_root() {
                            self.path = &[];
                            return Some(Component::RootDir);
                        } else if self.include_cur_dir() {
                            self.path = &[];
                            return Some(Component::CurDir);
                        }
                    }
                },
                State::StartDir => {
                    self.back = State::Done;
                    return None;
                },
                State::Done => unreachable!(),
            }
        }

        None
    }
}

impl FusedIterator for &mut Components<'_> {}

impl ExactSizeIterator for &mut Components<'_> {}

impl core::fmt::Display for Components<'_> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        // SAFETY: at each step of the iteration over self, self.path remains a valid string
        write!(fmt, "{}", unsafe { String::from_utf8_unchecked(self.path.to_vec()) })
    }
}

impl<'path> From<Components<'path>> for Path<'path> {
    fn from(value: Components<'path>) -> Self {
        let mut comps = value.clone();
        if comps.front == State::Body {
            comps.trim_left();
        }
        if comps.back == State::Body {
            comps.trim_right();
        }
        // SAFETY: the rest of the path is a valid UTF-8 sequence
        let path = unsafe { Path::from_ut8_slice(comps.path) };
        // SAFETY: `path` in not empty nor containing the `<NUL>` character
        unsafe { path.unwrap_unchecked() }
    }
}

#[cfg(test)]
mod test {
    use alloc::string::ToString;
    use core::str::FromStr;

    use crate::path::{Component, Path, UnixStr};

    #[test]
    fn unix_str_creation() {
        assert!(UnixStr::new("/").is_ok());
        assert!(UnixStr::new("/home//user///foo").is_ok());

        assert!(UnixStr::new("").is_err());
        assert!(UnixStr::new("/home//user///\0foo").is_err());
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
    fn path_extension() {
        let first_path = Path::from_str("/home").unwrap();
        let second_path = Path::from_str("user").unwrap();
        assert_eq!(first_path.join(&second_path).canonical(), Path::from_str("/home/user").unwrap());

        let first_path = Path::from_str("/home/").unwrap();
        let second_path = Path::from_str("user").unwrap();
        assert_eq!(first_path.join(&second_path).canonical(), Path::from_str("/home/user").unwrap());

        let first_path = Path::from_str("//home//").unwrap();
        let second_path = Path::from_str("user/").unwrap();
        assert_eq!(first_path.join(&second_path).canonical(), Path::from_str("//home/user/").unwrap());

        let first_path = Path::from_str("/foo/bar").unwrap();
        let second_path = Path::from_str("/home/user/").unwrap();
        assert_eq!(first_path.join(&second_path).canonical(), Path::from_str("/home/user/").unwrap());

        let first_path = Path::from_str("./foo").unwrap();
        let second_path = Path::from_str("bar/baz").unwrap();
        assert_eq!(first_path.join(&second_path).canonical(), Path::from_str("./foo/bar/baz").unwrap());

        let first_path = Path::from_str("foo").unwrap();
        let second_path = Path::from_str("//bar/baz").unwrap();
        assert_eq!(first_path.join(&second_path).canonical(), Path::from_str("//bar/baz").unwrap());

        let first_path = Path::from_str("/foo").unwrap();
        let second_path = Path::from_str("/bar/baz").unwrap();
        assert_eq!(first_path.join(&second_path).canonical(), Path::from_str("/bar/baz").unwrap());
    }

    #[allow(clippy::cognitive_complexity)]
    #[test]
    fn path_components() {
        let path = Path::from_str("/home/user/foo").unwrap();
        let mut components = path.components();
        let mut iterator = components.into_iter();

        assert_eq!(iterator.len(), 4);
        assert_eq!(iterator.to_string().as_str(), "/home/user/foo");
        assert_eq!(iterator.next(), Some(Component::RootDir));
        assert_eq!(iterator.len(), 3);
        assert_eq!(iterator.to_string().as_str(), "home/user/foo");
        assert_eq!(iterator.next(), Some(Component::Normal(UnixStr::from_str("home").unwrap())));
        assert_eq!(iterator.len(), 2);
        assert_eq!(iterator.to_string().as_str(), "user/foo");
        assert_eq!(iterator.next(), Some(Component::Normal(UnixStr::from_str("user").unwrap())));
        assert_eq!(iterator.len(), 1);
        assert_eq!(iterator.to_string().as_str(), "foo");
        assert_eq!(iterator.next(), Some(Component::Normal(UnixStr::from_str("foo").unwrap())));
        assert_eq!(iterator.len(), 0);
        assert!(iterator.to_string().is_empty());
        assert_eq!(iterator.next(), None);
        assert_eq!(iterator.len(), 0);

        let path = Path::from_str("./foo//../baz").unwrap();
        let mut components = path.components();
        let mut iterator = components.into_iter();

        assert_eq!(iterator.next(), Some(Component::CurDir));
        assert_eq!(iterator.next(), Some(Component::Normal(UnixStr::from_str("foo").unwrap())));
        assert_eq!(iterator.next(), Some(Component::ParentDir));
        assert_eq!(iterator.next(), Some(Component::Normal(UnixStr::from_str("baz").unwrap())));
        assert_eq!(iterator.next(), None);

        let path = Path::from_str("foo/bar///..").unwrap();
        let mut components = path.components();
        let mut iterator = components.into_iter();

        assert_eq!(iterator.len(), 3);
        assert_eq!(iterator.next(), Some(Component::Normal(UnixStr::from_str("foo").unwrap())));
        assert_eq!(iterator.next(), Some(Component::Normal(UnixStr::from_str("bar").unwrap())));
        assert_eq!(iterator.next(), Some(Component::ParentDir));
        assert_eq!(iterator.next(), None);

        let path = Path::from_str("//home/foo/.././").unwrap();
        let mut components = path.components();
        let mut iterator = components.into_iter();

        assert_eq!(iterator.len(), 5);
        assert_eq!(iterator.next(), Some(Component::DoubleSlashRootDir));
        assert_eq!(iterator.next(), Some(Component::Normal(UnixStr::from_str("home").unwrap())));
        assert_eq!(iterator.next(), Some(Component::Normal(UnixStr::from_str("foo").unwrap())));
        assert_eq!(iterator.next(), Some(Component::ParentDir));
        assert_eq!(iterator.next(), Some(Component::CurDir));
        assert_eq!(iterator.next(), None);
    }

    #[allow(clippy::cognitive_complexity)]
    #[test]
    fn path_components_back() {
        let path = Path::from_str("/home/user/foo").unwrap();
        let mut components = path.components();
        let mut iterator = components.into_iter();

        assert_eq!(iterator.len(), 4);
        assert_eq!(iterator.to_string().as_str(), "/home/user/foo");
        assert_eq!(iterator.next_back(), Some(Component::Normal(UnixStr::from_str("foo").unwrap())));
        assert_eq!(iterator.len(), 3);
        assert_eq!(iterator.to_string().as_str(), "/home/user");
        assert_eq!(iterator.next_back(), Some(Component::Normal(UnixStr::from_str("user").unwrap())));
        assert_eq!(iterator.len(), 2);
        assert_eq!(iterator.to_string().as_str(), "/home");
        assert_eq!(iterator.next_back(), Some(Component::Normal(UnixStr::from_str("home").unwrap())));
        assert_eq!(iterator.len(), 1);
        assert_eq!(iterator.to_string().as_str(), "/");
        assert_eq!(iterator.next_back(), Some(Component::RootDir));
        assert_eq!(iterator.len(), 0);
        assert!(iterator.to_string().is_empty());
        assert_eq!(iterator.next_back(), None);
        assert_eq!(iterator.len(), 0);

        let path = Path::from_str("./foo//../baz").unwrap();
        let mut components = path.components();
        let mut iterator = components.into_iter();

        assert_eq!(iterator.next_back(), Some(Component::Normal(UnixStr::from_str("baz").unwrap())));
        assert_eq!(iterator.next_back(), Some(Component::ParentDir));
        assert_eq!(iterator.next_back(), Some(Component::Normal(UnixStr::from_str("foo").unwrap())));
        assert_eq!(iterator.next_back(), Some(Component::CurDir));
        assert_eq!(iterator.next_back(), None);

        let path = Path::from_str("foo/bar///..").unwrap();
        let mut components = path.components();
        let mut iterator = components.into_iter();

        assert_eq!(iterator.next_back(), Some(Component::ParentDir));
        assert_eq!(iterator.next_back(), Some(Component::Normal(UnixStr::from_str("bar").unwrap())));
        assert_eq!(iterator.next_back(), Some(Component::Normal(UnixStr::from_str("foo").unwrap())));
        assert_eq!(iterator.next_back(), None);

        let path = Path::from_str("//home/foo/.././").unwrap();
        let mut components = path.components();
        let mut iterator = components.into_iter();

        assert_eq!(iterator.next_back(), Some(Component::CurDir));
        assert_eq!(iterator.next_back(), Some(Component::ParentDir));
        assert_eq!(iterator.next_back(), Some(Component::Normal(UnixStr::from_str("foo").unwrap())));
        assert_eq!(iterator.next_back(), Some(Component::Normal(UnixStr::from_str("home").unwrap())));
        assert_eq!(iterator.next_back(), Some(Component::DoubleSlashRootDir));
        assert_eq!(iterator.next_back(), None);
    }

    #[allow(clippy::cognitive_complexity)]
    #[test]
    fn path_components_double_side() {
        let path = Path::from_str("/home/user/foo").unwrap();
        let mut components = path.components();
        let mut iterator = components.into_iter();

        assert_eq!(iterator.len(), 4);
        assert_eq!(iterator.to_string().as_str(), "/home/user/foo");
        assert_eq!(iterator.next(), Some(Component::RootDir));
        assert_eq!(iterator.len(), 3);
        assert_eq!(iterator.to_string().as_str(), "home/user/foo");
        assert_eq!(iterator.next_back(), Some(Component::Normal(UnixStr::from_str("foo").unwrap())));
        assert_eq!(iterator.len(), 2);
        assert_eq!(iterator.to_string().as_str(), "home/user");
        assert_eq!(iterator.next(), Some(Component::Normal(UnixStr::from_str("home").unwrap())));
        assert_eq!(iterator.len(), 1);
        assert_eq!(iterator.to_string().as_str(), "user");
        assert_eq!(iterator.next_back(), Some(Component::Normal(UnixStr::from_str("user").unwrap())));
        assert_eq!(iterator.len(), 0);
        assert!(iterator.to_string().is_empty());
        assert_eq!(iterator.next_back(), None);
        assert_eq!(iterator.len(), 0);
        assert_eq!(iterator.next(), None);
        assert_eq!(iterator.len(), 0);

        let path = Path::from_str("./foo//../baz").unwrap();
        let mut components = path.components();
        let mut iterator = components.into_iter();

        assert_eq!(iterator.next(), Some(Component::CurDir));
        assert_eq!(iterator.next_back(), Some(Component::Normal(UnixStr::from_str("baz").unwrap())));
        assert_eq!(iterator.next(), Some(Component::Normal(UnixStr::from_str("foo").unwrap())));
        assert_eq!(iterator.next_back(), Some(Component::ParentDir));
        assert_eq!(iterator.next(), None);

        let path = Path::from_str("foo/bar///..").unwrap();
        let mut components = path.components();
        let mut iterator = components.into_iter();

        assert_eq!(iterator.next_back(), Some(Component::ParentDir));
        assert_eq!(iterator.next(), Some(Component::Normal(UnixStr::from_str("foo").unwrap())));
        assert_eq!(iterator.next_back(), Some(Component::Normal(UnixStr::from_str("bar").unwrap())));
        assert_eq!(iterator.next(), None);

        let path = Path::from_str("//home/foo/.././").unwrap();
        let mut components = path.components();
        let mut iterator = components.into_iter();

        assert_eq!(iterator.next(), Some(Component::DoubleSlashRootDir));
        assert_eq!(iterator.next_back(), Some(Component::CurDir));
        assert_eq!(iterator.next(), Some(Component::Normal(UnixStr::from_str("home").unwrap())));
        assert_eq!(iterator.next_back(), Some(Component::ParentDir));
        assert_eq!(iterator.next(), Some(Component::Normal(UnixStr::from_str("foo").unwrap())));
        assert_eq!(iterator.next_back(), None);
    }

    #[test]
    fn path_components_len() {
        let path = Path::from_str("/home/user/foo").unwrap();
        let mut components = path.components();
        let iterator = components.into_iter();
        assert_eq!(iterator.len(), 4);

        let path = Path::from_str("./foo//../baz").unwrap();
        let mut components = path.components();
        let iterator = components.into_iter();
        assert_eq!(iterator.len(), 4);

        let path = Path::from_str("foo/bar///..").unwrap();
        let mut components = path.components();
        let iterator = components.into_iter();
        assert_eq!(iterator.len(), 3);

        let path = Path::from_str("//home/foo/.././").unwrap();
        let mut components = path.components();
        let iterator = components.into_iter();
        assert_eq!(iterator.len(), 5);
    }

    #[test]
    fn path_parent() {
        let path = Path::from_str("/foo/bar").unwrap();
        let parent = path.parent().unwrap();
        assert_eq!(parent, Path::from_str("/foo").unwrap());

        let grand_parent = parent.parent().unwrap();
        assert_eq!(grand_parent, Path::from_str("/").unwrap());
        assert_eq!(grand_parent.parent(), None);

        let relative_path = Path::from_str("foo/bar").unwrap();
        let parent = relative_path.parent().unwrap();
        assert_eq!(parent, Path::from_str("foo").unwrap());
        let grand_parent = parent.parent();
        assert_eq!(grand_parent, None);

        let relative_path = Path::from_str("./foo/bar").unwrap();
        let parent = relative_path.parent().unwrap();
        assert_eq!(parent, Path::from_str("./foo").unwrap());
        let grand_parent = parent.parent().unwrap();
        assert_eq!(grand_parent, Path::from(Component::CurDir));
        let great_grand_parent = grand_parent.parent();
        assert_eq!(great_grand_parent, None);
    }

    #[test]
    fn path_file_name() {
        let path = Path::from_str("/foo/bar").unwrap();
        assert_eq!(path.file_name(), Some(UnixStr::from_str("bar").unwrap()));

        let path = Path::from_str("foo/bar").unwrap();
        assert_eq!(path.file_name(), Some(UnixStr::from_str("bar").unwrap()));

        let path = Path::from_str(".").unwrap();
        assert_eq!(path.file_name(), None);

        let path = Path::from_str("..").unwrap();
        assert_eq!(path.file_name(), None);

        let path = Path::from_str("/").unwrap();
        assert_eq!(path.file_name(), None);
    }
}
