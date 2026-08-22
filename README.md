# works

## Requirements

Rust 1.95.0 (pinned via [`rust-toolchain.toml`](rust-toolchain.toml)).

## Crates

- [`rotortree`](crates/rotortree): An n-ary leanIMT implementation with persistence, for high-throughput append-only merkle trees.
- [`sealring`](crates/sealring): A generic sealed-note envelope
- [`binius-mayo`](crates/binius-mayo): A Binius64 zk-circuit library proving MAYO-2 post-quantum signature verification
- [`chainfold`](crates/chainfold): A sans-io fold engine for ordered chain events, with fork recovery and durable snapshots.

## Examples

Each crate carries its own examples in its `examples/` directory. Examples that span
more than one crate live in [`crates/examples`](crates/examples), so no published crate
has to take a dev-dependency on a sibling.

```sh
cargo run --release -p examples --example merkle_log
```

## Security

See [SECURITY.md](SECURITY.md) for our vulnerability disclosure policy.

## Publishing

See [PUBLISH.md](PUBLISH.md) for how maintainers release a crate.

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in this project by you, as defined in the Apache-2.0 license,
shall be dual licensed as above, without any additional terms or conditions.
