module
public import CoxeterGrowth.Plastic
public import CoxeterGrowth.TwoThreeInf
public import CoxeterGrowth.TriangleNF
public import CoxeterGrowth.Triangle
public import CoxeterGrowth.Instances
public import CoxeterGrowth.Family

@[expose] public section
/-!
# Growth series of the triangle Coxeter groups `(p, q, ∞)`

* `CoxeterGrowth.Plastic` — the plastic number (real root `> 1` of `x³ − x − 1`).
* `CoxeterGrowth.TriangleNF` — normal-form combinatorics and counting for general `p, q`.
* `CoxeterGrowth.Triangle` — the lift to the Coxeter group, length additivity, and the
  general growth-series identity `CoxeterGrowth.Triangle.growth_series`.
* `CoxeterGrowth.Instances` — `(2,3,∞)`, `(2,4,∞)`, `(3,3,∞)`; Padovan; growth rate.
* `CoxeterGrowth.Family` — the family: monotonicity and symmetry in `(p, q)`, the bound
  `2ρⁿ ≤ a(n)` for every hyperbolic member, the rate `τ_{p,q}` of every member
  (`a(n)^{1/n} → τ_{p,q}`), its strict monotonicity, `ρ = min τ_{p,q}` (only at `(2,3)`,
  `(3,2)`), `τ_{p,q} < 2` and `τ_{p,q} → 2`.
* `CoxeterGrowth.TwoThreeInf` — an independent, earlier proof of the `(2,3,∞)` case by a
  three-state automaton (kept as a cross-check; not used by the general development).
-/
