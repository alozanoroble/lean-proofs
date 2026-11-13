# Proofs a Computer Checks

An introduction to proof formalization, Lean, Mathlib and proof certificates,
for students of mathematics, built around small Lean proofs you can step
through: uniqueness of the identity and of inverses in a group, `n + 0 = n`,
Euclid's infinitude of primes, and more.

**Live page:** https://alozanoroble.github.io/lean-proofs/

Every Lean source, goal state, error message, axiom list and proof term on the
page was produced by Lean (4.34.0, Mathlib `db00fb39`) and inserted by a
script, not typed by hand.

- `index.html`: the page (static, self-contained)
- `certificate.txt`: what was checked, by which Lean and Mathlib, with which axioms
- `lean/`: the Lean project; `cd lean && lake exe cache get && lake build`
- `results/`: the raw Lean output the certificate cites

`lean/LeanProofs/Broken.lean` is deliberately wrong and is excluded from the build.
