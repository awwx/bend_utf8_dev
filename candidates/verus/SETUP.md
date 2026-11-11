# Setup: Verus + Rust 1.99.1 + wasm32 (Linux x86_64, Ubuntu, Node 26.13.0)

Started 10:47:48, complete 10:49:05 (+07, 2026-11-11): about 1m20s wall clock
(fast network; most of it was the rustup toolchain download).

Versions: Verus release 0.2026.11.02.8bf68ee (commit 8bf68ee), Rust 1.99.1
(58cf8f9c3 2026-10-13), rustup 1.29.3, bundled Z3 (inside the zip), vstd
prebuilt in the zip (for verification) and vstd crate 0.0.0-2026-11-01-0251
from crates.io (for the wasm build, erased).

Disk: /root/verus-install 167 MB (zip 35 MB + extracted), ~/.rustup 692 MB
(shared with another agent's toolchains; the 1.99.1 minimal + wasm32 target
part is roughly 400-500 MB), ~/.cargo 36 MB, spike/target 85 MB.

## Commands

```sh
# 1. Verus prebuilt release (no `unzip` on this box; python works)
mkdir -p /root/verus-install && cd /root/verus-install
curl -sL -o verus.zip https://github.com/verus-lang/verus/releases/download/release/0.2026.11.02.8bf68ee/verus-0.2026.11.02.8bf68ee-x86-linux.zip
mkdir x && cd x && python3 -c "import zipfile;zipfile.ZipFile('../verus.zip').extractall('.')"
chmod +x verus-x86-linux/{verus,cargo-verus,rust_verify,z3}   # zip loses the exec bits
# 2. rustup (skip if ~/.cargo/bin/rustup exists), no toolchain yet
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal --default-toolchain none
export PATH=$HOME/.cargo/bin:$PATH
# 3. toolchain Verus demands (`./verus` prints this exact command) + wasm target
rustup toolchain install 1.99.1-x86_64-unknown-linux-gnu --profile minimal -t wasm32-unknown-unknown
# 4. check
/root/verus-install/x/verus-x86-linux/verus --version
```

Note: because no default toolchain existed, rustup's first `toolchain install`
printed "default toolchain set to 1.99.1". Run `rustup default none`-style
cleanup yourself if you need no default (we did not change it afterwards).

## Use

```sh
cd candidates/verus/spike
V=/root/verus-install/x/verus-x86-linux/verus
$V spike.rs --crate-type=lib            # verify (host target)  ~1.3 s
cargo build --release --target wasm32-unknown-unknown -j2   # wasm, ~23 s cold, 3 s warm
command cp target/wasm32-unknown-unknown/release/spike.wasm spike.wasm
node test.mjs
```
