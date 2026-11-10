This VM is a sandbox dedicated to your use.  You may install any
software that would be useful for your task, but leave the installed
`bend` as it is.  In your final message for the turn, say what you
installed.  (No need to say that you didn't install anything.)

The user makes commits; don't commit unless asked.

In this shell, `cp`, `mv` and `rm` are aliased to their `-i`
(interactive) versions. In scripts and one-off commands, use
`command cp`, `command mv` and `rm -f`, so that nothing waits for
confirmation.

## Working with Bend

Bend files have the extension ".bend".

The `bend` program is available on the command line. Run
`bend version` for the installed version; `/root/mirror/bend` is
checked out at the matching tag.

Read `/root/mirror/bend/guide/GUIDE.md`, which `bend guide` also
prints. `bend base <name>` prints a Base definition.

## This project

The following rules don't apply to the `io_http_streaming_fetch.bend`
demo.  It wasn't built by the process described here, and isn't
covered by verification.

### Laws

`LAWS.bend` and `*_LAWS.bend` files are reviewed by the user.

Laws must define correctness independently of implementation
details. They may use implementation functions when the behavior
relied upon is established by other independently specified and proved
laws. Do not rely on behavior that those laws leave unspecified.

Write the laws files as a clear specification: state what the
correct outcome is in an understandable way.  Prefer the clearer
specification even when it needs more proofs; so far coding agents
have written proofs quickly and easily.

### Guide

Tips for writing laws and proofs, and for laying out the files, are
in `AGENT_BEND_GUIDE.md` in this directory. It supplements Bend's
`GUIDE.md`. These are not requirements; use your own judgment about
when to use something from the file.

### Implementations and `PROOF.bend`

The user doesn't read implementations or `PROOF.bend`.  Write them for
maintainability by future coding-agent sessions.

### Verification

Verify by running `bend PROOF.bend`; it must print "ALL PROOFS CHECK".
"N TODOs found" means some laws don't have proofs yet.

`bend PROOF.bend --verdict` isn't needed. It currently fails because
of a Bend bug: a mismatch between its TypeScript checker and its
kernel.
