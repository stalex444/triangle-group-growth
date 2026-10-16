module
public import Mathlib

@[expose] public section
/-!
# Growth series of the triangle Coxeter groups `(p, q, ∞)`

Let `W` be a Coxeter group on three generators `a = 0`, `b = 1`, `c = 2` with Coxeter matrix
`m(a, c) = p`, `m(b, c) = q`, `m(a, b) = ∞` (encoded `M 0 1 = 0`), `p, q ≥ 2` (hyperbolic exactly
when `(p, q) ≠ (2, 2)`; the affine `(2, 2, ∞) ≅ D_∞ × C₂` is included), and let
`a(n) = #{w ∈ W : ℓ(w) = n}` be the number of elements of length `n`. The entry states and
proves, for every such Coxeter system (`CoxeterSystem M W` in Mathlib), the growth-series
identity in `ℤ⟦X⟧`

  `(Σₙ a(n) Xⁿ) · (1 − (X + ⋯ + X^{p−1})(X + ⋯ + X^{q−1})) = (1 + X)(1 + ⋯ + X^{p−1})(1 + ⋯ + X^{q−1})`,

i.e. `W(t) = (1+t)[p]_t[q]_t / (1 − (t + ⋯ + t^{p−1})(t + ⋯ + t^{q−1}))`, together with its
instances and, for `(2, 3, ∞)`, the sphere sizes and growth rate; and, for the whole family,
monotonicity and symmetry in `(p, q)`, the growth rate of every hyperbolic member, and the
minimality of the plastic number. The compared statements are:

1. `growth_series` — the identity above, for all `p, q ≥ 2`.
2. `triangle_matrix_exists` — for all `p, q ≥ 2` a Coxeter matrix with `M 0 1 = 0`,
   `M 0 2 = p`, `M 1 2 = q` exists, so 1 is not vacuous.
3. `growth_series_23` — `(2,3,∞)`: `(Σ a(n)Xⁿ)(1 − X² − X³) = (1 + X)²(1 + X + X²)`.
4. `growth_series_24` — `(2,4,∞)`: `(Σ a(n)Xⁿ)(1 − X² − X³ − X⁴) = (1 + X)²(1 + X + X² + X³)`.
5. `growth_series_33` — `(3,3,∞)`: `(Σ a(n)Xⁿ)(1 − X² − 2X³ − X⁴) = (1 + X)(1 + X + X²)²`.
6. `sphere23_values` — `(2,3,∞)`: `a(0), …, a(4) = 1, 3, 5, 7, 9` and
   `a(n+5) = a(n+3) + a(n+2)` for all `n`.
7. `sphere23_rec_fails_at_4` — the recursion fails one step earlier: `a(4) ≠ a(2) + a(1)`.
8. `sphere23_padovan` — `a(n) = Pad(n+5)` for `n ≥ 2`, `Pad` the Padovan sequence
   (`Pad 0 = Pad 1 = Pad 2 = 1`, `Pad (n+3) = Pad (n+1) + Pad n`; so `Pad(n) = OEIS A000931(n+5)`
   and `a(n) = A000931(n+10)` for `n ≥ 2` — the sphere sequence itself is OEIS A096231).
9. `plastic_exists_unique` — there is exactly one real `ρ > 1` with `ρ³ = ρ + 1` (the plastic
   number), so 10 and 11 are not vacuous.
10. `sphere23_growth_bounds` — `2ρⁿ ≤ a(n) ≤ 4ρⁿ` for all `n ≥ 2`.
11. `sphere23_root_tendsto` — `a(n)^{1/n} → ρ`: the growth rate of `(2, 3, ∞)` is the plastic
    number.
12. `sphere_mono` — monotonicity in `(p, q)`: for `p ≤ p'`, `q ≤ q'` (all `≥ 2`), `a(n)` of any
    `(p, q, ∞)` system is at most `a(n)` of any `(p', q', ∞)` system, for every `n`.
13. `sphere_symm` — symmetry: `(p, q, ∞)` and `(q, p, ∞)` have the same `a(n)` for every `n`.
14. `sphere_ge_plastic` — for every hyperbolic `(p, q) ≠ (2, 2)`, `2ρⁿ ≤ a(n)` for all `n ≥ 2`.
15. `rate_exists_unique` — for every `(p, q) ≠ (2, 2)` there is exactly one real `τ > 1` with
    `(τ⁻¹ + ⋯ + τ^{−(p−1)})(τ⁻¹ + ⋯ + τ^{−(q−1)}) = 1`, i.e. exactly one root `t = τ⁻¹ ∈ (0, 1)`
    of the denominator in (1); call it `τ_{p,q}`. In 16–20 it is not a defined constant: those
    statements take any real `τ > 1` satisfying the equation as a hypothesis, and 15 makes it
    unique. So 16–20 are not vacuous.
16. `sphere_root_tendsto_rate` — `a(n)^{1/n} → τ_{p,q}`: the growth rate of every hyperbolic
    `(p, q, ∞)` (for `(2, 2)` no `τ > 1` solves the equation, so the hypothesis excludes it).
17. `rate_lt_rate` — `τ_{p,q}` is strictly increasing: `τ_{p,q} < τ_{p',q'}` for `p ≤ p'`,
    `q ≤ q'`, `(p, q) ≠ (p', q')`.
18. `plastic_le_rate` — `ρ ≤ τ_{p,q}`, with equality exactly for `(p, q) = (2, 3)` and `(3, 2)`:
    the plastic number is the minimal growth rate of the family, attained only there.
19. `rate_lt_two` — `τ_{p,q} < 2`.
20. `rate_tendsto_two` — `τ_{p,q} → 2` as `p, q → ∞`: for every `σ < 2` there is `N` with
    `τ_{p,q} > σ` whenever `p, q ≥ N` (with 19, `τ_{p,q} → 2`).

The mathematics is classical and no novelty is claimed for it: the growth series of a Coxeter
group is a rational function determined by its finite parabolic subgroups (Steinberg 1968), and
growth of planar hyperbolic Coxeter groups is treated by Floyd (1992) and Cannon–Wagreich (1992);
the `(p, q, ∞)` formula is the amalgam computation for `D_p *_{C₂} D_q`. The `(2,3,∞)`,
`(2,4,∞)` and `(3,3,∞)` sphere sequences are OEIS A096231, A179070 (shifted) and A054886, with
generating functions derived there from Cannon–Wagreich Prop. 3.1, and A096231 records
`a(n) = A000931(n+10)` (the Padovan form of statement 8) and the recursion of statement 6;
Bucher–Talambutsa (2016, Prop. 18) prove statement 11 by a normal form and, with Mann's bound,
that ρ is the minimal growth rate of `PGL(2, ℤ)` over all generating sets. Statement 12 is the
identity-map case of Terragni (2016, Thm. A), 18 is Floyd's minimality restricted to the
family, and 20 is a case of Yukita (2024, Thm. 3.5). What the entry contributes is a kernel-checked proof of the general
identity for all `p, q`, from Mathlib's `CoxeterSystem` alone (Mathlib at this pin has no
exchange/deletion property and no parabolic-subgroup API). The proof constructs
the amalgam normal forms `c^ε · x₁ ⋯ x_k`, lifts their left action to `W` by the universal
property, shows the Coxeter length is the normal-form length, and counts normal forms.

Application (cited, not a claim of the entry). The `(2, 3, ∞)` triangle group is the Weyl
group of the hyperbolic Kac–Moody algebra `AE₃`, isomorphic to `PGL(2, ℤ)` (Feingold–Frenkel,
Math. Ann. 263 (1983) 87), and, in the Damour–Henneaux–Nicolai billiard description of the
Belinski–Khalatnikov–Lifshitz limit (a conjecture for generic singularities;
Henneaux–Persson–Spindel, Living Rev. Relativity 11 (2008) 1, §2.9), it is the reflection group
of the billiard of `3+1`-dimensional vacuum gravity near a spacelike singularity
(Damour–Henneaux–Nicolai, Class. Quantum Grav. 20 (2003) R145, §8; Henneaux–Persson–Spindel
§3.1). There `a(n)` is the number of chambers at gallery distance `n` from the fundamental
chamber, i.e. the number of distinct chambers billiard trajectories from the fundamental chamber
can occupy after exactly `n` wall collisions (over all initial data), so statements 10 and 11
give the exponential growth rate of those outcomes; the count is elementary reflection-group
geometry (a geodesic crosses each wall at most once, so from `C` to `wC` it crosses exactly the
`ℓ(w)` separating walls), not part of the formal content.
-/

open PowerSeries Finset Filter Topology

namespace TriangleGrowth

/-- **(1) The growth series of the triangle Coxeter group `(p, q, ∞)`.** -/
theorem growth_series {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)} (cs : CoxeterSystem M W)
    {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (h01 : M 0 1 = 0) (h02 : M 0 2 = p) (h12 : M 1 2 = q) :
    (PowerSeries.mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) *
        (1 - (∑ i ∈ Ico 1 p, (X : ℤ⟦X⟧) ^ i) * (∑ i ∈ Ico 1 q, (X : ℤ⟦X⟧) ^ i)) =
      (1 + X) * (∑ i ∈ range p, (X : ℤ⟦X⟧) ^ i) * (∑ i ∈ range q, (X : ℤ⟦X⟧) ^ i) := by
  sorry

/-- **(2) Non-vacuity**: the Coxeter matrix of type `(p, q, ∞)` exists for all `p, q ≥ 2`. -/
theorem triangle_matrix_exists (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    ∃ M : CoxeterMatrix (Fin 3), M 0 1 = 0 ∧ M 0 2 = p ∧ M 1 2 = q := by
  sorry

/-- **(3) `(2,3,∞)`.** -/
theorem growth_series_23 {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3) :
    (PowerSeries.mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) * (1 - X ^ 2 - X ^ 3) =
      (1 + X) ^ 2 * (1 + X + X ^ 2) := by
  sorry

/-- **(4) `(2,4,∞)`.** -/
theorem growth_series_24 {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 4) :
    (PowerSeries.mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) *
        (1 - X ^ 2 - X ^ 3 - X ^ 4) = (1 + X) ^ 2 * (1 + X + X ^ 2 + X ^ 3) := by
  sorry

/-- **(5) `(3,3,∞)`.** -/
theorem growth_series_33 {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (h01 : M 0 1 = 0) (h02 : M 0 2 = 3) (h12 : M 1 2 = 3) :
    (PowerSeries.mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) *
        (1 - X ^ 2 - 2 * X ^ 3 - X ^ 4) = (1 + X) * (1 + X + X ^ 2) ^ 2 := by
  sorry

/-- **(6) `(2,3,∞)` sphere sizes**: `1, 3, 5, 7, 9`, then `a(n+5) = a(n+3) + a(n+2)`. -/
theorem sphere23_values {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3) :
    Nat.card {w : W // cs.length w = 0} = 1 ∧ Nat.card {w : W // cs.length w = 1} = 3 ∧
      Nat.card {w : W // cs.length w = 2} = 5 ∧ Nat.card {w : W // cs.length w = 3} = 7 ∧
      Nat.card {w : W // cs.length w = 4} = 9 ∧
      ∀ n : ℕ, Nat.card {w : W // cs.length w = n + 5} =
        Nat.card {w : W // cs.length w = n + 3} + Nat.card {w : W // cs.length w = n + 2} := by
  sorry

/-- **(7)** The recursion of (6) fails one step earlier: `a(4) ≠ a(2) + a(1)`. -/
theorem sphere23_rec_fails_at_4 {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3) :
    Nat.card {w : W // cs.length w = 4} ≠
      Nat.card {w : W // cs.length w = 2} + Nat.card {w : W // cs.length w = 1} := by
  sorry

/-- **(8) Padovan**: `a(n) = Pad(n + 5)` for `n ≥ 2`. -/
theorem sphere23_padovan {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3)
    (pad : ℕ → ℕ) (hp0 : pad 0 = 1) (hp1 : pad 1 = 1) (hp2 : pad 2 = 1)
    (hpr : ∀ n, pad (n + 3) = pad (n + 1) + pad n) (n : ℕ) (hn : 2 ≤ n) :
    Nat.card {w : W // cs.length w = n} = pad (n + 5) := by
  sorry

/-- **(9)** The plastic number exists and is unique. -/
theorem plastic_exists_unique : ∃! ρ : ℝ, 1 < ρ ∧ ρ ^ 3 = ρ + 1 := by
  sorry

/-- **(10) Two-sided growth bound** for `(2,3,∞)`: `2ρⁿ ≤ a(n) ≤ 4ρⁿ`, `n ≥ 2`. -/
theorem sphere23_growth_bounds {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3)
    (ρ : ℝ) (hρ : 1 < ρ) (hρ3 : ρ ^ 3 = ρ + 1) (n : ℕ) :
    2 * ρ ^ (n + 2) ≤ (Nat.card {w : W // cs.length w = n + 2} : ℝ) ∧
      (Nat.card {w : W // cs.length w = n + 2} : ℝ) ≤ 4 * ρ ^ (n + 2) := by
  sorry

/-- **(11) Growth rate** of `(2,3,∞)`: `a(n)^{1/n} → ρ`, the plastic number. -/
theorem sphere23_root_tendsto {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3)
    (ρ : ℝ) (hρ : 1 < ρ) (hρ3 : ρ ^ 3 = ρ + 1) :
    Tendsto (fun n : ℕ => (Nat.card {w : W // cs.length w = n} : ℝ) ^ ((n : ℝ)⁻¹)) atTop
      (𝓝 ρ) := by
  sorry

/-- **(12) Monotonicity** in `(p, q)`: `a_{p,q}(n) ≤ a_{p',q'}(n)` for `p ≤ p'`, `q ≤ q'`. -/
theorem sphere_mono {W W' : Type*} [Group W] [Group W'] {M M' : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W') {p q p' q' : ℕ} (hp : 2 ≤ p)
    (hq : 2 ≤ q) (hpp : p ≤ p') (hqq : q ≤ q') (h01 : M 0 1 = 0) (h02 : M 0 2 = p)
    (h12 : M 1 2 = q) (h01' : M' 0 1 = 0) (h02' : M' 0 2 = p') (h12' : M' 1 2 = q') (n : ℕ) :
    Nat.card {w : W // cs.length w = n} ≤ Nat.card {w : W' // cs'.length w = n} := by
  sorry

/-- **(13) Symmetry**: `a_{p,q}(n) = a_{q,p}(n)`. -/
theorem sphere_symm {W W' : Type*} [Group W] [Group W'] {M M' : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W') {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (h01 : M 0 1 = 0) (h02 : M 0 2 = p) (h12 : M 1 2 = q) (h01' : M' 0 1 = 0)
    (h02' : M' 0 2 = q) (h12' : M' 1 2 = p) (n : ℕ) :
    Nat.card {w : W // cs.length w = n} = Nat.card {w : W' // cs'.length w = n} := by
  sorry

/-- **(14) The plastic number bounds the whole family from below**: for every hyperbolic
`(p, q, ∞)`, `2ρⁿ ≤ a(n)` for `n ≥ 2`. -/
theorem sphere_ge_plastic {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : (p, q) ≠ (2, 2))
    (h01 : M 0 1 = 0) (h02 : M 0 2 = p) (h12 : M 1 2 = q)
    (ρ : ℝ) (hρ : 1 < ρ) (hρ3 : ρ ^ 3 = ρ + 1) (n : ℕ) :
    2 * ρ ^ (n + 2) ≤ (Nat.card {w : W // cs.length w = n + 2} : ℝ) := by
  sorry

/-- **(15) The rate equation** has exactly one root `τ > 1` for every hyperbolic `(p, q)`. -/
theorem rate_exists_unique {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : (p, q) ≠ (2, 2)) :
    ∃! τ : ℝ, 1 < τ ∧ (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) = 1 := by
  sorry

/-- **(16) Growth rate of every member**: `a(n)^{1/n} → τ`, the root of the rate equation. -/
theorem sphere_root_tendsto_rate {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (h01 : M 0 1 = 0) (h02 : M 0 2 = p) (h12 : M 1 2 = q) (τ : ℝ) (hτ : 1 < τ)
    (hτeq : (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) = 1) :
    Tendsto (fun n : ℕ => (Nat.card {w : W // cs.length w = n} : ℝ) ^ ((n : ℝ)⁻¹)) atTop
      (𝓝 τ) := by
  sorry

/-- **(17) The rate is strictly increasing** in `(p, q)`. -/
theorem rate_lt_rate {p q p' q' : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpp : p ≤ p') (hqq : q ≤ q')
    (hne : (p, q) ≠ (p', q')) (τ τ' : ℝ) (hτ : 1 < τ) (hτ' : 1 < τ')
    (hτeq : (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) = 1)
    (hτeq' : (∑ i ∈ Ico 1 p', τ'⁻¹ ^ i) * (∑ i ∈ Ico 1 q', τ'⁻¹ ^ i) = 1) : τ < τ' := by
  sorry

/-- **(18) The plastic number is the minimal rate**: `ρ ≤ τ`, with equality exactly for
`(p, q) = (2, 3)` and `(3, 2)`. -/
theorem plastic_le_rate {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (τ : ℝ) (hτ : 1 < τ)
    (hτeq : (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) = 1)
    (ρ : ℝ) (hρ : 1 < ρ) (hρ3 : ρ ^ 3 = ρ + 1) :
    ρ ≤ τ ∧ (τ = ρ ↔ (p = 2 ∧ q = 3) ∨ (p = 3 ∧ q = 2)) := by
  sorry

/-- **(19)** Every rate is below `2`. -/
theorem rate_lt_two {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (τ : ℝ) (hτ : 1 < τ)
    (hτeq : (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) = 1) : τ < 2 := by
  sorry

/-- **(20)** The rates tend to `2` as `p, q → ∞`. -/
theorem rate_tendsto_two (σ : ℝ) (hσ : σ < 2) :
    ∃ N : ℕ, ∀ p q : ℕ, N ≤ p → N ≤ q → ∀ τ : ℝ, 1 < τ →
      (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) = 1 → σ < τ := by
  sorry

end TriangleGrowth
