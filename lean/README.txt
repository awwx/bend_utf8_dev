Run ./check as a non-root user on Linux with elan and bubblewrap installed.
The selected toolchain is leanprover/lean4:v4.35.0; it includes comparator
and all the external kernels used by --paranoid. Bubblewrap must be able
to create user, mount, PID, and network namespaces. Failure to sandbox is
a check failure; the script has no unsandboxed fallback.

Reviewed inputs
---------------
Utf8Laws.lean is the specification. Utf8Challenge.lean declares the 15
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
The script snapshots sources into temporary projects, without copying
compiled artifacts or a .lake directory, and runs comparator twice:

1. spec-comparator.json checks all 15 properties in a project containing
   only Utf8Laws, Utf8Challenge, and Utf8Check. The sandbox hides the original
   repository. In particular, implementation modules are unavailable to
   these proofs. The challenge's decoder hole is not a target of this run.
2. comparator.json checks the 15 properties and RefDecoder_correct, with
   RefDecoder explicitly designated as a definition supplied by the solution.
   This uses a separate clean project so the first build cannot seed its
   build artifacts.

Comparator compares theorem statements and their underlying definitions
against the separately exported challenge, checks the permitted axioms,
and rechecks the exported proof dependencies with Lean and every bundled
external kernel (--paranoid). Only propext, Classical.choice, and Quot.sound
are permitted. It replaces the previous source-word filter, hand-written
axiom/type checks, and custom kernel replay. It verifies the requested
obligations and their dependencies; unrelated, unused declarations are not
necessarily exported or checked.

The runner leaves the repository's sources and build directories untouched
and removes its temporary projects on exit. No generated proof is committed
or made trusted by passing these checks.
