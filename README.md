# Growth series of the triangle Coxeter groups (p, q, ∞)

Kernel-checked, in Lean 4 + Mathlib, for every Coxeter system on three
generators `a, b, c` with `m(a,c) = p`, `m(b,c) = q`, `m(a,b) = ∞` and
`p, q ≥ 2` (hyperbolic exactly when `(p, q) ≠ (2, 2)`; the affine
`(2, 2, ∞) ≅ D_∞ × C₂` is included): the growth series `W(t) = Σ a(n) tⁿ`, `a(n)` the number of
elements of Coxeter length `n`, satisfies

```
W(t) · (1 − (t + ⋯ + t^{p−1})(t + ⋯ + t^{q−1})) = (1 + t)(1 + ⋯ + t^{p−1})(1 + ⋯ + t^{q−1})
```

as an identity in `ℤ⟦X⟧` — the general theorem — with the instances
`(2,3,∞)`, `(2,4,∞)`, `(3,3,∞)`, and, for `(2,3,∞) ≅ PGL(2,ℤ)`, the sphere
sizes `1, 3, 5, 7, 9, 12, 16, 21, 28, 37, …`, the Padovan identity
`a(n) = Pad(n+5)` for `n ≥ 2`, the two-sided bounds `2ρⁿ ≤ a(n) ≤ 4ρⁿ` for
`n ≥ 2`, and the growth rate `a(n)^{1/n} → ρ`, the plastic number, the
real root of `x³ = x + 1`. For the whole family, `a(n)` is monotone in
`(p, q)` and symmetric, every hyperbolic member has `2ρⁿ ≤ a(n)` for
`n ≥ 2`, and its growth rate
is the unique `τ_{p,q} > 1` with
`(τ⁻¹ + ⋯ + τ^{−(p−1)})(τ⁻¹ + ⋯ + τ^{−(q−1)}) = 1`, strictly increasing
in `p` and `q`, below 2 and tending to 2; so ρ is the minimal growth rate
of the family, attained only at `(2,3,∞)` and `(3,2,∞)`. Twenty compared
theorems; every one on the axioms `propext`, `Classical.choice`,
`Quot.sound` alone.

## The compared statements

1. `growth_series` — the identity above, for all `p, q ≥ 2`.
2. `triangle_matrix_exists` — a Coxeter matrix of type `(p, q, ∞)` exists
   for all `p, q ≥ 2`, so (1) is not vacuous.
3. `growth_series_23` — `(2,3,∞)`: `W(t)(1 − t² − t³) = (1+t)²(1+t+t²)`.
4. `growth_series_24` — `(2,4,∞)`: `W(t)(1 − t² − t³ − t⁴) = (1+t)²(1+t+t²+t³)`.
5. `growth_series_33` — `(3,3,∞)`: `W(t)(1 − t² − 2t³ − t⁴) = (1+t)(1+t+t²)²`.
6. `sphere23_values` — `(2,3,∞)`: `a(0..4) = 1, 3, 5, 7, 9` and
   `a(n+5) = a(n+3) + a(n+2)` for all `n`.
7. `sphere23_rec_fails_at_4` — that recursion fails one step earlier:
   `a(4) ≠ a(2) + a(1)` (`9 ≠ 8`), because the numerator has degree 4.
8. `sphere23_padovan` — `a(n) = Pad(n+5)` for `n ≥ 2`, for any sequence
   with `Pad(0) = Pad(1) = Pad(2) = 1` and `Pad(n+3) = Pad(n+1) + Pad(n)`
   (`Pad(n) = OEIS A000931(n+5)`, so `a(n) = A000931(n+10)` for `n ≥ 2`;
   the sphere sequence itself is OEIS A096231).
9. `plastic_exists_unique` — exactly one real `ρ > 1` satisfies `ρ³ = ρ + 1`.
10. `sphere23_growth_bounds` — `2ρⁿ ≤ a(n) ≤ 4ρⁿ` for all `n ≥ 2`.
11. `sphere23_root_tendsto` — `a(n)^{1/n} → ρ`.
12. `sphere_mono` — monotonicity in `(p, q)`: for `p ≤ p'`, `q ≤ q'` (all
    `≥ 2`), `a(n)` of any `(p, q, ∞)` system is at most `a(n)` of any
    `(p', q', ∞)` system, for every `n`.
13. `sphere_symm` — symmetry: `(p, q, ∞)` and `(q, p, ∞)` have the same
    `a(n)` for every `n`.
14. `sphere_ge_plastic` — for every hyperbolic `(p, q) ≠ (2, 2)`,
    `2ρⁿ ≤ a(n)` for all `n ≥ 2`.
15. `rate_exists_unique` — for every `(p, q) ≠ (2, 2)` there is exactly one
    real `τ > 1` with `(τ⁻¹ + ⋯ + τ^{−(p−1)})(τ⁻¹ + ⋯ + τ^{−(q−1)}) = 1`,
    i.e. exactly one root `t = τ⁻¹ ∈ (0, 1)` of the denominator in (1);
    call it `τ_{p,q}`. So 16–20 are not vacuous.
16. `sphere_root_tendsto_rate` — `a(n)^{1/n} → τ_{p,q}`: the growth rate
    of every hyperbolic `(p, q, ∞)` (for `(2, 2)` no `τ > 1` solves the
    equation, so the hypothesis excludes it).
17. `rate_lt_rate` — `τ_{p,q}` is strictly increasing: `τ_{p,q} < τ_{p',q'}`
    for `p ≤ p'`, `q ≤ q'`, `(p, q) ≠ (p', q')`.
18. `plastic_le_rate` — `ρ ≤ τ_{p,q}`, with equality exactly for
    `(p, q) = (2, 3)` and `(3, 2)`: the plastic number is the minimal growth
    rate of the family, attained only there.
19. `rate_lt_two` — `τ_{p,q} < 2`.
20. `rate_tendsto_two` — `τ_{p,q} → 2` as `p, q → ∞`: for every `σ < 2`
    there is `N` with `τ_{p,q} > σ` whenever `p, q ≥ N`.

Numerical values of `τ_{p,q}` (BUILD.txt, mpmath at 50 digits, shown to six
decimals; not compared statements; `(2,2)` excluded, growth rate 1): `τ_{2,3} = ρ = 1.324718`, `τ_{2,4} = 1.465571` (the root of
`x³ = x² + 1`), `τ_{2,5} = 1.534158`, `τ_{3,3} = 1.618034` (the golden
ratio, since `1 − (t + t²)² = (1 − t − t²)(1 + t + t²)`), `τ_{3,4} = 1.734691`,
`τ_{4,4} = 1.839287`, `τ_{6,6} = 1.965948`, `τ_{20,20} = 1.999998`.

The mathematics is classical and no novelty is claimed for it. The growth
series of any Coxeter group is rational and is determined by its finite
parabolic subgroups (Steinberg 1968; Humphreys 1990, §5.12); the growth
of planar hyperbolic Coxeter groups is the subject of Floyd (1992) and
Cannon–Wagreich (1992) (OEIS A096231, A179070 and A054886 list the
`(2,3,∞)`, `(2,4,∞)` and `(3,3,∞)` sphere sequences, with generating
functions derived from Cannon–Wagreich Prop. 3.1, and A096231 records the
Padovan form `a(n) = A000931(n+10)`); Floyd (1992, p. 482) proves that
`(2,3,∞)` has the minimal growth rate among cusped planar hyperbolic
Coxeter groups, and Kellerhals (2013, §5.2) gives an elementary
alternative proof (statements 14–18 kernel-check this minimality within
the `(p, q, ∞)` family; Floyd's theorem over all cusped planar groups is
not formalized); Bucher–Talambutsa (2016, Prop. 18) prove statement 11
itself by a normal form and, with Mann's bound, that ρ is the minimal
growth rate of `PGL(2,ℤ)` over ALL generating sets; Terragni (2016)
records the value (§5.8) and proves (Thm. A) that sphere sizes are
monotone in the Coxeter labels — statement 12 is its identity-map case,
and 14 follows with 10; Yukita (2024, Thm. 3.5) proves the growth rate
continuous on the space of Coxeter systems, which with the rate 2 of
`(∞, ∞, ∞)` gives statement 20; Kellerhals (2013, (5.5) and Lemma 1)
prints the family's growth function and the strict comparison behind 17.
The `(p, q, ∞)` formula is the growth of the amalgam
`D_p *_{C₂} D_q`. What the
entry contributes is a kernel-checked proof of the general identity for
all `p, q` at once, from Mathlib's `CoxeterSystem` alone: Mathlib at this
pin has no growth series, no exchange or deletion property, and no
parabolic-subgroup API, so the proof builds the amalgam normal forms
`c^ε · x₁ ⋯ x_k` (blocks alternating between the two dihedral factors,
each block an alternating word ending in `a` or in `b` of length below
`p` or `q`), lifts their left action to `W` by the universal property of
the Coxeter group, shows the Coxeter length equals the normal-form length,
and counts normal forms by length.

## Application (cited; not a claim of the entry)

The `(2,3,∞)` triangle group is the Weyl group of the hyperbolic
Kac–Moody algebra `AE₃`, isomorphic to `PGL(2,ℤ)` (Feingold–Frenkel,
Math. Ann. 263 (1983)), and it is the reflection group of the billiard of
`3+1`-dimensional vacuum gravity near a spacelike singularity
(conjecturally, for generic singularities: Henneaux–Persson–Spindel §2.9):
the Belinski–Khalatnikov–Lifshitz dynamics reduces, in the
Damour–Henneaux–Nicolai description, to a billiard in the Weyl chamber of
`AE₃`, whose three walls are the two symmetry walls and the curvature
wall (Damour–Henneaux–Nicolai, Class. Quantum Grav. 20 (2003) R145, §8;
Henneaux–Persson–Spindel, Living Rev. Relativity 11 (2008) 1, §3.1).
There `a(n)` is the number of chambers at gallery distance `n` from the
fundamental chamber — the number of distinct chambers billiard
trajectories from the fundamental chamber can occupy after exactly `n`
wall collisions, over all initial data — so statements 10 and 11 give the
exponential growth rate of those outcomes: the plastic number. That count
is elementary reflection-group geometry (a geodesic crosses each wall at
most once, so from `C` to `wC` it crosses exactly the `ℓ(w)` separating
walls); it is not part of the formal content, and nothing here is a claim
about the physics beyond the cited identification of the group.

## Layout and build

`Challenge.lean` states the twenty results with placeholder proofs and
imports Mathlib only; `Solution.lean` proves them by direct transfer from
the proof modules; `comparator.json` is the machine comparison surface;
`formalization.yaml` carries sources, classification and disclosure;
`BUILD.txt` is the build and axiom record (toolchain, Mathlib revision,
file hashes, `#print axioms` for every compared declaration, brute-force
table).

Proof modules, under `CoxeterGrowth/`:
- `Plastic.lean` — the plastic number: existence (intermediate value
  theorem on `[1, 2]`), uniqueness among roots `> 1` and among all real
  roots, the cubic identity.
- `TriangleNF.lean` — the normal forms for general `p, q`: the encoding,
  the dihedral relation on forms through an explicit orbit coordinate,
  the three generator actions and their Coxeter relations, the descent
  lemma, and the count of forms by length giving the series identity on
  the normal-form side.
- `Triangle.lean` — the group side: the lift of the action to `W`,
  Coxeter length = normal-form length, the sphere/normal-form bijection,
  and `growth_series`.
- `Instances.lean` — the three instances, the sphere table and its
  recursion, Padovan, the growth bounds and the root limit.
- `Family.lean` — the family: monotonicity and symmetry of the
  normal-form counts, the recursion `a(n) = Σ_{1≤i<p} Σ_{1≤j<q} a(n−i−j)`
  for `n ≥ p+q` extracted from the series, the bounds
  `τ^{n−(p+q)} ≤ a(n) ≤ Cτⁿ`, the rate equation (intermediate value
  theorem, strict monotonicity), and the comparisons of rates.
- `TwoThreeInf.lean` — an independent, self-contained proof of the
  `(2,3,∞)` case by a three-state automaton (ported from a 2026-10-15
  development on Lean 4.31); it is not on the compared surface and
  nothing depends on it. It is included as a second, independent kernel
  check of the instance.

```
lake exe cache get
lake build
```

(pinned toolchain `leanprover/lean4:v4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; a green build is the kernel
verification).

## Context

This repository is a complete, self-contained proof development; nothing
is imported from any other project. It belongs to the kernel-verified
project [stalex444/pdt-lean](https://github.com/stalex444/pdt-lean)
(Zenodo concept DOI
[10.5281/zenodo.21210683](https://doi.org/10.5281/zenodo.21210683)), the
formal spine of Pisot Dimensional Theory, in which ρ is assigned to the
three-dimensional sector; that is why the author looked at the growth of
the billiard group of `3+1`-dimensional gravity. Registered entries of
that project certify, independently of this one, that `x³ − x − 1` is the
cubic Mahler minimiser (PALOMAR-2026-08-31-000004), that ρ and the golden
ratio are the only morphic numbers (PALOMAR-2026-09-01-000008), and that
the largest roots of the Bedford–Kim family
`x^{n+1}(x³ − x − 1) + (x³ + x² − 1)` increase to ρ
(PALOMAR-2026-09-01-000005; that these are the Coxeter-element spectral
radii of the `E_{n+3}` star trees is McMullen's, cited there). Nothing in
any compared statement here depends on any of that.
