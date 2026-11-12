# Aeneas + Charon setup (replayable)

Measured on this VM (4 cores, 7 GB, Linux x86_64), 2026-11-11, 10:48:04 to 10:55:34 = **7.5 min wall-clock**
(network bound: about 5.5 min of it is `lake exe cache get`; the Rust toolchain install, 1m48s, ran concurrently).
No source build of anything was needed.

Prerequisites already on the machine: elan (default toolchain left untouched), rustup (installed by another
agent; not reinstalled), git, curl, node 26.

```sh
# 1. Prebuilt Aeneas nightly (contains `aeneas`, `charon`, `charon-driver`, backends/lean = Lean library sources)
#    plus the prebuilt Lean build of the Aeneas library.
T=nightly-2026.11.10-0d21a9e
mkdir -p ~/aeneas-nightly/dl && cd ~/aeneas-nightly/dl
for f in aeneas-linux-x86_64 lean-build-aeneas-x86_64-unknown-linux-gnu; do
  curl -sL -O https://github.com/AeneasVerif/aeneas/releases/download/$T/$f.tar.gz; done
mkdir ../bin-x && tar xzf aeneas-linux-x86_64.tar.gz -C ../bin-x          # bin-x/{aeneas,charon,backends/lean,rust-toolchain}
# 2. Lean library project = backends/lean, with the prebuilt Aeneas build unpacked into .lake/build
mkdir -p ../lib && cp -r ../bin-x/backends/lean ../lib/aeneas-lean && cd ../lib/aeneas-lean
mkdir -p .lake/build && tar xzf ../../dl/lean-build-aeneas-x86_64-unknown-linux-gnu.tar.gz -C .lake/build
# 3. Lean toolchain (from lean-toolchain: leanprover/lean4:v4.36.0-rc2) is installed by elan on first `lake` use;
#    Mathlib (git clone) + prebuilt cache:
lake exe cache get          # 9081 files, ~5.5 min; afterwards `lake build Aeneas` is a no-op (3590 jobs up to date)
# 4. Rust toolchain pinned by Charon (bin-x/rust-toolchain): rustc-dev needed by charon-driver
rustup toolchain install nightly-2026-09-17 --profile minimal -c rustc-dev -c llvm-tools -c rust-src -t wasm32-unknown-unknown
#    (the pin also lists `miri`; charon only warns "cargo miri setup failed" without it, harmless here)
```

Versions: aeneas nightly-2026.11.10-0d21a9e; charon 0.1.315 (454586e9); Lean v4.36.0-rc2; Mathlib rev 9d581dfff (tag v4.36.0-rc2);
rustc 1.100.0-nightly (923c95cdf 2026-09-16), `nightly-2026-09-17`.

Note: `lake exe cache get` clones Mathlib via git and does not touch the default elan toolchain. Do not use the default
`lean` (v4.34 here) on these files: `.olean` headers are incompatible. `spike/lean/build.sh` runs
`elan run leanprover/lean4:v4.36.0-rc2 lean` with `LEAN_PATH` from `lake env` in the library directory.
A separate `lakefile` that `require`s aeneas would clone Mathlib a second time (about 7 GB), so we compile our files with
plain `lean -o` against the existing library instead.

Disk (du): ~/aeneas-nightly 9.0 GB (downloads 218 MB, extracted binaries 581 MB, unused extra copy of the Lean build `lean-x`
434 MB, library+Mathlib+cache `lib` 7.8 GB); Lean v4.36.0-rc2 toolchain 3.1 GB (in ~/.elan); Rust nightly 1.7 GB (~/.rustup).
Total added about 13.8 GB.

## Running the spike
```sh
cd spike
./charon.sh                                  # Rust -> spike.llbc -> lean/Spike/{Types,Funs}.lean
cargo build --release --target wasm32-unknown-unknown -j2
(cd lean && ./build.sh)                      # ~30 s; prints axioms
node test.mjs
```

## Ubuntu 26.04 / EC2 (2026-11-11)
Replayed on a fresh Ubuntu 26.04 x86-64 EC2 instance (8 vCPU, 30 GB). Setup took about 3 min wall-clock (10:59:41 to 11:02:12;
`lake exe cache get` ran 1.3 min, much faster than before). No steps differed from above, except:
- rustup was not preinstalled: `curl -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain 1.99.1 -t wasm32-unknown-unknown`,
  then the `nightly-2026-09-17` command from step 4. No extra apt packages were needed (gcc, make, git were present).
- PATH must include `$HOME/.cargo/bin:$HOME/.elan/bin` (non-login shells do not have cargo on PATH).
- `spike/charon.sh` runs `rm -f lean/Spike/*.lean`, which also deletes the tracked `Spec.lean` and `Proofs.lean`. After running it,
  `git checkout -- lean/Spike/Spec.lean lean/Spike/Proofs.lean` before `lean/build.sh`. (Types.lean/Funs.lean regenerate identically.)
