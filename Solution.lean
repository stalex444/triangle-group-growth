module
public import CoxeterGrowth.Instances
public import CoxeterGrowth.Family

@[expose] public section
/-
Solution: proofs of the challenge statements, transferred from the CoxeterGrowth development
(`CoxeterGrowth.Triangle` for the general identity, `CoxeterGrowth.Instances` for the instances,
`CoxeterGrowth.Plastic` for the plastic number, `CoxeterGrowth.Family` for the family statements
(12)–(20)).
-/

open PowerSeries Finset Filter Topology

namespace TriangleGrowth

/-- **(1) The growth series of the triangle Coxeter group `(p, q, ∞)`.** -/
theorem growth_series {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)} (cs : CoxeterSystem M W)
    {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (h01 : M 0 1 = 0) (h02 : M 0 2 = p) (h12 : M 1 2 = q) :
    (PowerSeries.mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) *
        (1 - (∑ i ∈ Ico 1 p, (X : ℤ⟦X⟧) ^ i) * (∑ i ∈ Ico 1 q, (X : ℤ⟦X⟧) ^ i)) =
      (1 + X) * (∑ i ∈ range p, (X : ℤ⟦X⟧) ^ i) * (∑ i ∈ range q, (X : ℤ⟦X⟧) ^ i) :=
  CoxeterGrowth.Triangle.growth_series cs ⟨hp, hq, h01, h02, h12⟩

/-- **(2) Non-vacuity**: the Coxeter matrix of type `(p, q, ∞)` exists for all `p, q ≥ 2`. -/
theorem triangle_matrix_exists (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    ∃ M : CoxeterMatrix (Fin 3), M 0 1 = 0 ∧ M 0 2 = p ∧ M 1 2 = q :=
  CoxeterGrowth.Triangle.triM_exists p q hp hq

/-- **(3) `(2,3,∞)`.** -/
theorem growth_series_23 {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3) :
    (PowerSeries.mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) * (1 - X ^ 2 - X ^ 3) =
      (1 + X) ^ 2 * (1 + X + X ^ 2) :=
  CoxeterGrowth.Triangle.growth_series_23 cs h01 h02 h12

/-- **(4) `(2,4,∞)`.** -/
theorem growth_series_24 {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 4) :
    (PowerSeries.mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) *
        (1 - X ^ 2 - X ^ 3 - X ^ 4) = (1 + X) ^ 2 * (1 + X + X ^ 2 + X ^ 3) :=
  CoxeterGrowth.Triangle.growth_series_24 cs h01 h02 h12

/-- **(5) `(3,3,∞)`.** -/
theorem growth_series_33 {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (h01 : M 0 1 = 0) (h02 : M 0 2 = 3) (h12 : M 1 2 = 3) :
    (PowerSeries.mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) *
        (1 - X ^ 2 - 2 * X ^ 3 - X ^ 4) = (1 + X) * (1 + X + X ^ 2) ^ 2 :=
  CoxeterGrowth.Triangle.growth_series_33 cs h01 h02 h12

/-- **(6) `(2,3,∞)` sphere sizes**: `1, 3, 5, 7, 9`, then `a(n+5) = a(n+3) + a(n+2)`. -/
theorem sphere23_values {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3) :
    Nat.card {w : W // cs.length w = 0} = 1 ∧ Nat.card {w : W // cs.length w = 1} = 3 ∧
      Nat.card {w : W // cs.length w = 2} = 5 ∧ Nat.card {w : W // cs.length w = 3} = 7 ∧
      Nat.card {w : W // cs.length w = 4} = 9 ∧
      ∀ n : ℕ, Nat.card {w : W // cs.length w = n + 5} =
        Nat.card {w : W // cs.length w = n + 3} + Nat.card {w : W // cs.length w = n + 2} :=
  CoxeterGrowth.Triangle.sphere23_facts cs h01 h02 h12

/-- **(7)** The recursion of (6) fails one step earlier: `a(4) ≠ a(2) + a(1)`. -/
theorem sphere23_rec_fails_at_4 {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3) :
    Nat.card {w : W // cs.length w = 4} ≠
      Nat.card {w : W // cs.length w = 2} + Nat.card {w : W // cs.length w = 1} :=
  CoxeterGrowth.Triangle.sphere23_rec_fails_at_4 cs h01 h02 h12

/-- **(8) Padovan**: `a(n) = Pad(n + 5)` for `n ≥ 2`. -/
theorem sphere23_padovan {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3)
    (pad : ℕ → ℕ) (hp0 : pad 0 = 1) (hp1 : pad 1 = 1) (hp2 : pad 2 = 1)
    (hpr : ∀ n, pad (n + 3) = pad (n + 1) + pad n) (n : ℕ) (hn : 2 ≤ n) :
    Nat.card {w : W // cs.length w = n} = pad (n + 5) := by
  rw [CoxeterGrowth.Triangle.eq_padovan pad hp0 hp1 hp2 hpr]
  exact CoxeterGrowth.Triangle.sphere23_padovan cs h01 h02 h12 n hn

/-- **(9)** The plastic number exists and is unique. -/
theorem plastic_exists_unique : ∃! ρ : ℝ, 1 < ρ ∧ ρ ^ 3 = ρ + 1 :=
  ⟨CoxeterGrowth.plasticNumber,
    ⟨CoxeterGrowth.one_lt_plasticNumber, CoxeterGrowth.plasticNumber_cubic⟩,
    fun _ hy => CoxeterGrowth.plasticNumber_unique hy.1 hy.2⟩

/-- **(10) Two-sided growth bound** for `(2,3,∞)`: `2ρⁿ ≤ a(n) ≤ 4ρⁿ`, `n ≥ 2`. -/
theorem sphere23_growth_bounds {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3)
    (ρ : ℝ) (hρ : 1 < ρ) (hρ3 : ρ ^ 3 = ρ + 1) (n : ℕ) :
    2 * ρ ^ (n + 2) ≤ (Nat.card {w : W // cs.length w = n + 2} : ℝ) ∧
      (Nat.card {w : W // cs.length w = n + 2} : ℝ) ≤ 4 * ρ ^ (n + 2) :=
  CoxeterGrowth.Triangle.sphere23_growth cs h01 h02 h12 hρ hρ3 n

/-- **(11) Growth rate** of `(2,3,∞)`: `a(n)^{1/n} → ρ`, the plastic number. -/
theorem sphere23_root_tendsto {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3)
    (ρ : ℝ) (hρ : 1 < ρ) (hρ3 : ρ ^ 3 = ρ + 1) :
    Tendsto (fun n : ℕ => (Nat.card {w : W // cs.length w = n} : ℝ) ^ ((n : ℝ)⁻¹)) atTop
      (𝓝 ρ) :=
  CoxeterGrowth.Triangle.sphere23_root_tendsto cs h01 h02 h12 hρ hρ3

/-- **(12) Monotonicity** in `(p, q)`: `a_{p,q}(n) ≤ a_{p',q'}(n)` for `p ≤ p'`, `q ≤ q'`. -/
theorem sphere_mono {W W' : Type*} [Group W] [Group W'] {M M' : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W') {p q p' q' : ℕ} (hp : 2 ≤ p)
    (hq : 2 ≤ q) (hpp : p ≤ p') (hqq : q ≤ q') (h01 : M 0 1 = 0) (h02 : M 0 2 = p)
    (h12 : M 1 2 = q) (h01' : M' 0 1 = 0) (h02' : M' 0 2 = p') (h12' : M' 1 2 = q') (n : ℕ) :
    Nat.card {w : W // cs.length w = n} ≤ Nat.card {w : W' // cs'.length w = n} :=
  CoxeterGrowth.Triangle.sphere_mono cs cs' ⟨hp, hq, h01, h02, h12⟩
    ⟨le_trans hp hpp, le_trans hq hqq, h01', h02', h12'⟩ hpp hqq n

/-- **(13) Symmetry**: `a_{p,q}(n) = a_{q,p}(n)`. -/
theorem sphere_symm {W W' : Type*} [Group W] [Group W'] {M M' : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W') {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (h01 : M 0 1 = 0) (h02 : M 0 2 = p) (h12 : M 1 2 = q) (h01' : M' 0 1 = 0)
    (h02' : M' 0 2 = q) (h12' : M' 1 2 = p) (n : ℕ) :
    Nat.card {w : W // cs.length w = n} = Nat.card {w : W' // cs'.length w = n} :=
  CoxeterGrowth.Triangle.sphere_symm cs cs' ⟨hp, hq, h01, h02, h12⟩ ⟨hq, hp, h01', h02', h12'⟩ n

/-- **(14) The plastic number bounds the whole family from below**: for every hyperbolic
`(p, q, ∞)`, `2ρⁿ ≤ a(n)` for `n ≥ 2`. -/
theorem sphere_ge_plastic {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : (p, q) ≠ (2, 2))
    (h01 : M 0 1 = 0) (h02 : M 0 2 = p) (h12 : M 1 2 = q)
    (ρ : ℝ) (hρ : 1 < ρ) (hρ3 : ρ ^ 3 = ρ + 1) (n : ℕ) :
    2 * ρ ^ (n + 2) ≤ (Nat.card {w : W // cs.length w = n + 2} : ℝ) :=
  CoxeterGrowth.Triangle.sphere_ge_plastic cs ⟨hp, hq, h01, h02, h12⟩ hpq hρ hρ3 n

/-- **(15) The rate equation** has exactly one root `τ > 1` for every hyperbolic `(p, q)`. -/
theorem rate_exists_unique {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : (p, q) ≠ (2, 2)) :
    ∃! τ : ℝ, 1 < τ ∧ (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) = 1 :=
  CoxeterGrowth.Triangle.rate_exists_unique hp hq hpq

/-- **(16) Growth rate of every member**: `a(n)^{1/n} → τ`, the root of the rate equation. -/
theorem sphere_root_tendsto_rate {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (h01 : M 0 1 = 0) (h02 : M 0 2 = p) (h12 : M 1 2 = q) (τ : ℝ) (hτ : 1 < τ)
    (hτeq : (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) = 1) :
    Tendsto (fun n : ℕ => (Nat.card {w : W // cs.length w = n} : ℝ) ^ ((n : ℝ)⁻¹)) atTop
      (𝓝 τ) :=
  CoxeterGrowth.Triangle.sphere_root_tendsto_rate cs ⟨hp, hq, h01, h02, h12⟩ hτ hτeq

/-- **(17) The rate is strictly increasing** in `(p, q)`. -/
theorem rate_lt_rate {p q p' q' : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpp : p ≤ p') (hqq : q ≤ q')
    (hne : (p, q) ≠ (p', q')) (τ τ' : ℝ) (hτ : 1 < τ) (hτ' : 1 < τ')
    (hτeq : (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) = 1)
    (hτeq' : (∑ i ∈ Ico 1 p', τ'⁻¹ ^ i) * (∑ i ∈ Ico 1 q', τ'⁻¹ ^ i) = 1) : τ < τ' :=
  CoxeterGrowth.Triangle.rate_lt_rate hp hq hpp hqq hne hτ hτ' hτeq hτeq'

/-- **(18) The plastic number is the minimal rate**: `ρ ≤ τ`, with equality exactly for
`(p, q) = (2, 3)` and `(3, 2)`. -/
theorem plastic_le_rate {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (τ : ℝ) (hτ : 1 < τ)
    (hτeq : (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) = 1)
    (ρ : ℝ) (hρ : 1 < ρ) (hρ3 : ρ ^ 3 = ρ + 1) :
    ρ ≤ τ ∧ (τ = ρ ↔ (p = 2 ∧ q = 3) ∨ (p = 3 ∧ q = 2)) :=
  CoxeterGrowth.Triangle.plastic_le_rate hp hq hτ hτeq hρ hρ3

/-- **(19)** Every rate is below `2`. -/
theorem rate_lt_two {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (τ : ℝ) (hτ : 1 < τ)
    (hτeq : (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) = 1) : τ < 2 :=
  CoxeterGrowth.Triangle.rate_lt_two hp hq hτ hτeq

/-- **(20)** The rates tend to `2` as `p, q → ∞`. -/
theorem rate_tendsto_two (σ : ℝ) (hσ : σ < 2) :
    ∃ N : ℕ, ∀ p q : ℕ, N ≤ p → N ≤ q → ∀ τ : ℝ, 1 < τ →
      (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) = 1 → σ < τ :=
  CoxeterGrowth.Triangle.rate_tendsto_two σ hσ

end TriangleGrowth
