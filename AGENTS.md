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

Laws must define correctness independently of implementation
details. They may use implementation functions when the behavior
relied upon is established by other independently specified and proved
laws. Do not rely on behavior that those laws leave unspecified.

Verify by running `bend PROOF.bend`; it must print "ALL PROOFS CHECK".
"N TODOs found" means some laws don't have proofs yet.

`bend PROOF.bend --verdict` isn't needed. It currently fails in
`hex_u32_agrees` because of a Bend bug: a mismatch between its
TypeScript checker and its kernel.

Tips and suggestions are available in `BEND_LAWS_GUIDE.md` in this
directory. These are not requirements; use your own judgment about
when to use something from the file.

The user doesn't read `PROOF.bend`.  Write `PROOF.bend` for coding
agents.
