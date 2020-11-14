# 💫 tryhard

<!--- FIXME: Update crate, repo and CI workflow names here! Remove any that are not relevant --->
[![Embark](https://img.shields.io/badge/embark-open%20source-blueviolet.svg)](https://embark.dev)
[![Embark](https://img.shields.io/badge/discord-ark-%237289da.svg?logo=discord)](https://discord.gg/dAuKfZS)
[![Crates.io](https://img.shields.io/crates/v/tryhard.svg)](https://crates.io/crates/tryhard)
[![Docs](https://docs.rs/tryhard/badge.svg)](https://docs.rs/tryhard)
[![dependency status](https://deps.rs/repo/github/EmbarkStudios/tryhard/status.svg)](https://deps.rs/repo/github/EmbarkStudios/tryhard)
[![Build status](https://github.com/EmbarkStudios/tryhard/workflows/CI/badge.svg)](https://github.com/EmbarkStudios/tryhard/actions)

Easily retry futures.

## Example usage

```rust
use std::time::Duration;
use tryhard::RetryFutureExt;

// some async function that can fail
async fn read_file(path: &str) -> Result<String, std::io::Error> {
    // ...
}

let contents = (|| read_file("Cargo.toml"))
    // retry at most 10 times
    .retry(10)
    // using exponential backoff which doubles the delay between each attempt starting with 10ms
    // other types of backoff are also supported such as fixed, linear, and custom
    .exponential_backoff(Duration::from_millis(10))
    // but with a max delay of 1s
    .max_delay(Duration::from_secs(1))
    // go!
    .await?;

assert!(contents.contains("tryhard"));
```

See [the docs](https://docs.rs/tryhard) for more details.

## Contributing

[![Contributor Covenant](https://img.shields.io/badge/contributor%20covenant-v1.4-ff69b4.svg)](../CODE_OF_CONDUCT.md)

We welcome community contributions to this project.

Please read our [Contributor Guide](CONTRIBUTING.md) for more information on how to get started.

## License

Licensed under either of

* Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
