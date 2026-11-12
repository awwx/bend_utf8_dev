# Talos setup (feasibility spike)

Machine: 4 cores, 7.3 GB RAM, Linux. All paths are under
`/root/bend/utf8/candidates/talos/`. The default elan toolchain (4.34.0) is
unchanged; the clone's `lean-toolchain` and a copy in `spike/lean-toolchain`
select Lean 4.35.0.

## Versions
- Talos: `https://github.com/cajal-technologies/talos`, `main` at
  `d7c84ac660757953b752bdfc9cb8dae3dab623ed` (2026-11-02, "chore: bump toolchain to Lean v4.35.0 (#266)").
- Lean `leanprover/lean4:v4.35.0` (elan installed it on first use, about 3.0 GB in `~/.elan/toolchains`).
- Mathlib `v4.35.0` (only a dependency of `interpreter`'s lakefile; not imported by the modules the spike uses).
- wasm-tools 1.251.0 (version pinned in the repo's `justfile`), prebuilt release binary.
- Node v26.13.0 (already installed).
- `just` not installed: its recipes are two-line wrappers around `lake`.

## Commands (replayable)
```bash
cd /root/bend/utf8/candidates/talos
git clone https://github.com/cajal-technologies/talos.git          # 6 s, 25 MB
git -C talos checkout d7c84ac660757953b752bdfc9cb8dae3dab623ed

# wasm-tools (prebuilt binary; `cargo install wasm-tools --version 1.251.0` also works)
mkdir -p tools && cd tools
curl -sSL -o wt.tgz https://github.com/bytecodealliance/wasm-tools/releases/download/v1.251.0/wasm-tools-1.251.0-x86_64-linux.tar.gz
tar xzf wt.tgz && cd ..

# Dependencies: same as the repo's `just lake-shared`
cd talos/interpreter
lake update            # clones mathlib etc. into ../.lake/packages
lake exe cache get     # Mathlib prebuilt cache, 9031 files
# Build only the modules the spike imports (no Mathlib, no CodeLib, no iris-lean):
lake build Interpreter.Wasm.SmallStep Interpreter.Wasm.Host.Run \
  Interpreter.Wasm.Examples.Harness Interpreter.Wasm.Decoder.ProofEval \
  Interpreter.Wasm.Examples.UIntLemmas
cd ../..

# Check the spike (rebuilds spike.wasm, checks the printed text, runs Lean, runs Node tests)
cp talos/lean-toolchain spike/        # already present
spike/check.sh
```
`lake build` has no `-j` flag; this build is mostly sequential anyway
(one large file at a time).

## Times and resources
| step | wall clock | peak RSS |
|---|---|---|
| `git clone` | 6 s | |
| `lake update` + `lake exe cache get` | 2 min 53 s (11:43:01 to 11:45:54) | |
| minimal `lake build` (16 jobs) | 14 min 25 s (11:46:24 to 12:00:48) | 3.9 GB |
| of which `Interpreter/Wasm/SmallStep.lean` (8,078 lines) | 764 s | about 3.7 GB |
| of which `Interpreter/Wasm/Decoder/ProofEval.lean` | 445 s | |
| of which `Semantics.lean` / `Decoder/Wat.lean` / `Validate.lean` | 74 s / 38 s / 25 s | |
| `UIntLemmas` (added later) | 3 s | |
| `spike/check.sh` (Lean part) | 27.9 s | 1.9 GB |

Setup start 11:40:35, **setup complete 12:00:48 (+07)**, about 20 minutes.
No memory problems (the minimum available was about 3.6 GB, logged every 10 s in `mem.log`).

## Disk
- `talos/.lake/packages`: 6.9 GB (almost all of it the Mathlib cache, which the
  spike's import path never loads. `lake exe cache get` can probably be skipped
  for this route, but `lake` still needs the dependency checked out. Not tested).
- `talos/interpreter/.lake`: 475 MB (build outputs of the 16 modules).
- Lean 4.35.0 toolchain: 3.0 GB. wasm-tools: 24 MB.

## What need not be built
The whole repo (`just build`: interpreter + codelib (iris-lean) + programs,
CI around 2 h) is not needed. A proof about a hand-written WAT module needs only
`Interpreter.Wasm.SmallStep` (semantics), `Host.Run` (the `RunsExportWith`
export-call predicate) and `Decoder.ProofEval` (kernel-checked evaluation of the WAT
decoder). `CodeLib.Generated`'s `watModule%` elaborator would need CodeLib and so
iris-lean. The spike copies that elaborator into its own file (about 40 lines) instead.

The spike is not a Lake package. It is checked with `lean` and the interpreter's
`LEAN_PATH` (`lake env printenv LEAN_PATH` run in `talos/interpreter`).

## Ubuntu 26.04 / EC2 (2026-11-11)

Machine: 8 vCPU, 30 GB, Ubuntu 26.04 x86-64, root. Nothing in the steps above
needed to change; the existing `talos/` checkout (with its `.lake` build) and
`tools/wasm-tools-1.251.0-x86_64-linux/` were copied from the Debian 13 VM and
worked as is.

Differences:
- elan was installed fresh: `curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none`
  (elan 4.2.4), then `elan toolchain install leanprover/lean4:v4.35.0` and
  `leanprover/lean4:v4.36.0-rc2` (the latter for Aeneas). No default toolchain
  is set; the `lean-toolchain` files select 4.35.0. Add `~/.elan/bin` to PATH.
- Commands must run via the path `/root/bend/utf8/...` (symlink to `/root/utf8`),
  because `lean_path.txt` and the copied `.lake` contain that absolute path.
- Needed `git config --global --add safe.directory '*'` (the copied checkout is
  owned by another uid, so git refuses it and lake's manifest check can fail).
- No rebuild was needed: `lake build` of the five spike modules finished in 29 s
  (all up to date), `lake update` and `lake exe cache get` were not rerun.
  `spike/check.sh` passed in about 18 s ("all tests passed"). Node comes from nvm
  (v26.13.0, `~/.nvm/versions/node/v26.13.0/bin`).
