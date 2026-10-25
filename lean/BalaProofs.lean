/-!
# BalaProofs

Lean proofs of Peter Bala's conjectures on the OEIS entries A333561, A333562, A333565, A352275,
A352373, A361711, A363983, A364175, A364178, A370092, A376462 and A386548. The final theorem of
each entry is in the module of the same name, for example `BalaProofs.A361711`.

The entry modules are not imported here: several of them define a top-level `a`, as their
benchmark statements do, so they cannot be imported into one file. `lake build` builds every
module of the library (see `globs` in `lakefile.toml`).
-/
