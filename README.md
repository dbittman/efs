[![crates.io-badge]][crates.io-link]

[crates.io-badge]: https://img.shields.io/crates/v/efs.svg
[crates.io-link]: https://crates.io/crates/efs

# Extended fs

An OS and architecture independent implementation of some Unix filesystems in Rust.

/!\ Warning /!\ : this crate is not at all sure enough to be used in a real context. Do **NOT** manage any important data with this library, and make backups before using it!

The purpose of this library is not to be production-ready, but to help people who make toy OS (with [Rust OSDev for example](https://os.phil-opp.com/)).

## Features

* `no_std` support (enabled by default)

* General interface for UNIX filesystems

* `read`/`write` regular files

* Read directories content

## Supported filesystems

* [`ext2`](https://en.wikipedia.org/wiki/Ext2): ✅

If you want more supported filesystems, do not hesitate to open an issue on <https://codeberg.org/RatCornu/efs/issues>.

## Usage

Add this to your `Cargo.toml`:

```
[dependencies]
efs = "0.3"
```

See examples on <https://docs.rs/efs> in [`src/lib.rs`](src/lib.rs).

## Features

* `ext2`: enable the `ext2` filesystem support

* `std`: enable the features depending on the standard library

By default, only the `ext2` feature is set.

## License

Licensed under the GNU General Public License v3.0 which can be found [here](LICENSE).
