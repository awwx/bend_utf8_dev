Run spec/check and impl/check as a non-root user on Linux with elan
and bubblewrap installed. Both scripts accept an optional --paranoid flag.
The selected toolchain is leanprover/lean4:v4.35.0; it includes comparator
and all the external kernels used by --paranoid. Bubblewrap must be able
to create user, mount, PID, and network namespaces. Failure to sandbox is
a check failure; the script has no unsandboxed fallback.

Reviewed inputs
---------------
Utf8Laws.lean is the specification. Utf8Challenge.lean declares the 16
specification obligations and a Decoder-valued implementation hole with
its correctness obligation. The challenge's proof holes are intentional;
they are never accepted as solution proofs. Review the challenge and the
comparator JSON files alongside the specification. The checker script,
lakefile.toml, lake-manifest.json, lean-toolchain, installed toolchain,
and the libraries imported by the specification are also trusted inputs.

Unreviewed inputs
-----------------
Utf8Check.lean supplies the specification proofs. Utf8Ref.lean and the
other implementation/proof modules supply RefDecoder and its correctness
proof. Utf8Solution.lean collects the implementation proofs, downstream
facts, and the Utf8Eval.lean evaluation smoke test. The evaluation test
uses #guard so a mismatch causes its sandboxed build to fail.

Verification
------------
From this directory, run:

    ./spec/build
    ./impl/build
    ./spec/check [--paranoid]
    ./impl/check [--paranoid]

The build scripts run incremental Lake builds and accept Lake build
targets, such as +Utf8Proofs for the implementation.

The specification project in spec/ contains Utf8Laws, Utf8Challenge, and
Utf8Check. Its comparator checks all 16 properties. The challenge's decoder
hole is outside that run's targets. In a checkout under /home, /root,
/run/user, or /tmp, comparator masks the containing directory and mounts
the selected project back into the sandbox. This keeps implementation
files outside the specification sandbox.

The implementation project is in impl/. Both of its scripts replace
impl/spec/ with copies of the Lean sources from spec/ before running Lake.
The copy is git ignored and stays on disk after each run so diagnostic
paths remain available. Edit the originals in spec/.

The implementation comparator checks the 16 properties and
RefDecoder_correct, with RefDecoder designated as a definition supplied
by the solution. Each project keeps its own .lake build directory.

Comparator compares theorem statements and their underlying definitions
against the separately exported challenge, checks the permitted axioms,
and rechecks the exported proof dependencies with Lean. With --paranoid,
it also runs the additional bundled kernel checkers. Only propext,
Classical.choice, and Quot.sound are permitted. Comparator verifies the
requested obligations and their dependencies. It may skip unrelated,
unused declarations.

No generated proof is committed or made trusted by passing these checks.
