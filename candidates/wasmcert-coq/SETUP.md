# Setup: Rocq + WasmCert-Coq (coq-wasm 2.2.1)

Machine: Debian 13 (trixie) userland, 4 cores, 7.3 GB RAM, Node v26.13.0
preinstalled. Another agent was running Lean builds at the same time.

## Versions obtained

| component | version |
|---|---|
| opam | 2.3.0 (Debian package `2.3.0-1+deb13u2`) |
| OCaml | 5.3.0 (Debian system compiler, opam switch `wasmcert` on `ocaml-system`) |
| Rocq | 9.2.0 (`rocq-core`, `rocq-stdlib`, `coq` 9.2.0 compat package) |
| coq-wasm (WasmCert-Coq) | 2.2.1 |
| coq-compcert | 3.18 (x86_64 configuration, pulled in by opam) |
| coq-flocq | 4.2.2 |
| rocq-mathcomp-ssreflect | 2.6.0 (with elpi 3.7.3, rocq-elpi 3.5.1, HB 1.10.3) |
| rocq-parseque | 0.3.1 |
| coq-ext-lib | 0.13.2 |
| wasm (OCaml reference interpreter) | 2.0.2 |

opam picked Rocq 9.2 (the newest that coq-wasm 2.2.1 allows: `coq >= 9.0 & < 9.3~`).

## Replayable commands (the path that works)

```sh
# 1. system packages
apt-get install -y opam libgmp-dev pkg-config time
# IMPORTANT on Debian 13 with the system compiler: 'apt install opam' pulls
# in Debian's camlp-streams runtime package, which shadows opam's copy and
# breaks biniou/mdx (and, if you add the -dev package, elpi/HB with
# "Dynlink error: implementation mismatch on Stream").  Remove it:
apt-get remove -y libcamlp-streams-ocaml libcamlp-streams-ocaml-dev

# 2. opam
opam init --bare -n --disable-sandboxing -y
opam switch create wasmcert ocaml-system -y
eval $(opam env --switch=wasmcert)
opam repo add coq-released https://coq.inria.fr/opam/released --this-switch -y
opam install -y -j 2 coq-wasm

# 3. reference sources (read-only, for lemmas/examples)
git clone https://github.com/WasmCert/WasmCert-Coq.git ref-WasmCert-Coq
git -C ref-WasmCert-Coq checkout v2.2.1     # 58a3d3f8b7af4dc8aa9351f254a9e672643b21f8

# 4. the spike
cd spike && make && make test && make crosscheck
```

Alternative that avoids the camlp-streams trap entirely (not tried; costs
~5 more minutes to build the compiler):
`opam switch create wasmcert ocaml-base-compiler.5.3.0`.

## What actually happened (times are wall clock)

| step | start | duration | notes |
|---|---|---|---|
| apt install opam, gmp, pkg-config | 10:52 | 65 s | |
| opam init --bare | 10:53 | 21 s | |
| switch on ocaml-system + coq-released repo | 10:54 | 17 s | |
| opam install coq-wasm, attempt 1 | 10:55 | 0 s | `/usr/bin/time` missing; `apt install time` |
| attempt 2 | 10:55 | 19 min 20 s | built Rocq 9.2, stdlib, CompCert 3.18, Flocq, ...; **failed** in biniou and mdx (camlp-streams, see above) |
| attempt 3 (with Debian -dev package) | 11:15 | 1 min | **failed** in rocq-hierarchy-builder: Dynlink mismatch on Stream |
| remove Debian camlp-streams, `opam reinstall camlp-streams`, `opam install coq-wasm` | 11:17 | 7 min 28 s | success: elpi, HB, mathcomp, coq-wasm |
| **setup complete** | **11:24:40** | **32.5 min total** | |

On a clean replay with the camlp-streams packages removed up front, expect
roughly 25-27 minutes on this kind of machine with `-j 2` (attempt 2 +
attempt 4 minus the rebuilds).  CompCert 3.18 is the single largest item
(about 10 minutes; opam builds the whole compiler, although WasmCert only
needs `Integers`, `Memdata`, `Floats`).

A separate rebuild of only the coq-wasm theories (all 46 files) from the
clone, `nice dune build -j 2 --cache=disabled @theories/all`, took
**2 min 15 s** wall clock, max RSS 1.2 GB.  So the survey's "11-14
minutes" is CI time including dependencies; coq-wasm itself is cheap.

Peak memory (sampled every 5 s with `free -m`, includes the other agent's
usage): highest "used" 2.6 GB system-wide, lowest "available" 4.8 GB.
`/usr/bin/time` max RSS of a single process: 1.35 GB (attempt 2), 1.8 GB
(attempt 4).  The README's "at least 8 GB" was not needed at `-j 2`.

Disk: `~/.opam` 1.9 GB (switch 1.6 GB); reference clone 7.7 MB (plus its
`_build` if rebuilt); the spike is < 1 MB.

## Installed (everything)

- apt: `opam`, `libgmp-dev`, `pkg-config`, `time` (and their dependencies,
  which include Debian's `ocaml` 5.3.0 compiler and `bubblewrap` etc.);
  `libcamlp-streams-ocaml{,-dev}` were installed and then removed.
- opam: `~/.opam`, switch `wasmcert` with the packages in the table above
  (63 packages).
- git clone: `candidates/wasmcert-coq/ref-WasmCert-Coq` at v2.2.1.

## Ubuntu 26.04 / EC2 (2026-11-11)

Machine: Ubuntu 26.04, x86-64, 8 vCPU, 30 GB, root. Replayed the commands
above; the spike (`make && make test && make crosscheck`) passes
("spike tests passed"; crosscheck prints 0,0,1,1,1,0).

Differences from the Debian 13 run:

- apt gives opam 2.5.0 and system OCaml 5.4.0 (not 2.3.0 / 5.3.0). The
  `ocaml-system` switch works as is: opam resolved the same package set
  (Rocq 9.2.0, coq-wasm 2.2.1, coq-compcert 3.18, mathcomp 2.6.0, wasm
  2.0.2; camlp-streams 5.0.1 from opam). No opam-compiled OCaml needed.
- The camlp-streams trap still applies in principle: `apt install opam`
  pulled in `libcamlp-streams-ocaml` (5.0.1-3build8), which was removed
  right after (`apt-get remove -y libcamlp-streams-ocaml
  libcamlp-streams-ocaml-dev`) and before the opam install, so the install
  succeeded first time with no rebuilds.
- `opam install -y -j 4 coq-wasm`: 7 min 10 s wall clock (11:01:59 to
  11:09:09), versus 25-27 min estimated for `-j 2` on the old VM. Whole
  setup (apt, opam init, switch, install, spike) took about 10 min.
  Only the install step was timed this way; the spike rebuild took ~7 s.
- npm tools: nothing in SETUP.md, the spike or the decoder directory refers
  to `wabt` or `binaryen`, so none were installed. Node is v26.13.0 via nvm.
- Not run here: the full decoder check and the pure-rocq check.

Activate: `eval $(opam env --switch=wasmcert)` (prints a harmless "Running as
root" warning).
