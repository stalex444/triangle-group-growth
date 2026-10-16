module
public import CoxeterGrowth.Triangle
public import CoxeterGrowth.Plastic

@[expose] public section
/-!
# Instances of the triangle growth series

* closed forms for `(2,3,∞)`, `(2,4,∞)`, `(3,3,∞)`;
* for `(2,3,∞)`: the sphere sizes `1, 3, 5, 7, 9`, the recursion `a(n+5) = a(n+3) + a(n+2)`
  (which fails at `n = 4`), the Padovan identification `a(n) = Pad(n+5)` for `n ≥ 2`, the
  two-sided bound `2ρⁿ ≤ a(n) ≤ 4ρⁿ` (`n ≥ 2`) and `a(n)^{1/n} → ρ`, `ρ` the plastic number.
-/

namespace CoxeterGrowth.Triangle

open Finset PowerSeries Filter Topology

/-- The Coxeter matrix of type `(p, q, ∞)` on `Fin 3` (`∞` encoded as `0`). -/
def triM (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) : CoxeterMatrix (Fin 3) where
  M := !![1, 0, p; 0, 1, q; p, q, 1]
  isSymm := Matrix.IsSymm.ext fun i j => by fin_cases i <;> fin_cases j <;> rfl
  diagonal i := by fin_cases i <;> rfl
  off_diagonal i i' h := by
    fin_cases i <;> fin_cases i' <;>
      first | exact absurd rfl h | (show (0 : ℕ) ≠ 1; omega) | (show p ≠ 1; omega) |
        (show q ≠ 1; omega)

/-- Non-vacuity: the hypotheses of `growth_series` are satisfiable for all `p, q ≥ 2`. -/
theorem triM_exists (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    ∃ M : CoxeterMatrix (Fin 3), M 0 1 = 0 ∧ M 0 2 = p ∧ M 1 2 = q :=
  ⟨triM p q hp hq, rfl, rfl, rfl⟩

section Closed

variable {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)} (cs : CoxeterSystem M W)

/-- Sphere sizes `a(n) = #{w : ℓ(w) = n}`. -/
noncomputable def sphere (n : ℕ) : ℕ := Nat.card {w : W // cs.length w = n}

theorem sum_Ico_1_2 : ∑ i ∈ Ico 1 2, (X : ℤ⟦X⟧) ^ i = X := by
  simp [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]

theorem sum_Ico_1_3 : ∑ i ∈ Ico 1 3, (X : ℤ⟦X⟧) ^ i = X + X ^ 2 := by
  simp [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]

theorem sum_Ico_1_4 : ∑ i ∈ Ico 1 4, (X : ℤ⟦X⟧) ^ i = X + X ^ 2 + X ^ 3 := by
  simp [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ, add_assoc]

theorem sum_range_2 : ∑ i ∈ range 2, (X : ℤ⟦X⟧) ^ i = 1 + X := by
  simp [Finset.sum_range_succ]

theorem sum_range_3 : ∑ i ∈ range 3, (X : ℤ⟦X⟧) ^ i = 1 + X + X ^ 2 := by
  simp [Finset.sum_range_succ]

theorem sum_range_4 : ∑ i ∈ range 4, (X : ℤ⟦X⟧) ^ i = 1 + X + X ^ 2 + X ^ 3 := by
  simp [Finset.sum_range_succ]

/-- `(2,3,∞)`: `Σ a(n) tⁿ · (1 − t² − t³) = (1+t)²(1+t+t²)`. -/
theorem growth_series_23 (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3) :
    (PowerSeries.mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) * (1 - X ^ 2 - X ^ 3) =
      (1 + X) ^ 2 * (1 + X + X ^ 2) := by
  have h := growth_series cs ⟨le_refl 2, by norm_num, h01, h02, h12⟩
  rw [sum_Ico_1_2, sum_Ico_1_3, sum_range_2, sum_range_3] at h
  rw [show (1 : ℤ⟦X⟧) - X ^ 2 - X ^ 3 = 1 - X * (X + X ^ 2) by ring, h]
  ring

/-- `(2,4,∞)`: `Σ a(n) tⁿ · (1 − t² − t³ − t⁴) = (1+t)²(1+t+t²+t³)`. -/
theorem growth_series_24 (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 4) :
    (PowerSeries.mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) *
        (1 - X ^ 2 - X ^ 3 - X ^ 4) = (1 + X) ^ 2 * (1 + X + X ^ 2 + X ^ 3) := by
  have h := growth_series cs ⟨le_refl 2, by norm_num, h01, h02, h12⟩
  rw [sum_Ico_1_2, sum_Ico_1_4, sum_range_2, sum_range_4] at h
  rw [show (1 : ℤ⟦X⟧) - X ^ 2 - X ^ 3 - X ^ 4 = 1 - X * (X + X ^ 2 + X ^ 3) by ring, h]
  ring

/-- `(3,3,∞)`: `Σ a(n) tⁿ · (1 − t² − 2t³ − t⁴) = (1+t)(1+t+t²)²`. -/
theorem growth_series_33 (h01 : M 0 1 = 0) (h02 : M 0 2 = 3) (h12 : M 1 2 = 3) :
    (PowerSeries.mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) *
        (1 - X ^ 2 - 2 * X ^ 3 - X ^ 4) = (1 + X) * (1 + X + X ^ 2) ^ 2 := by
  have h := growth_series cs ⟨by norm_num, by norm_num, h01, h02, h12⟩
  rw [sum_Ico_1_3, sum_range_3] at h
  rw [show (1 : ℤ⟦X⟧) - X ^ 2 - 2 * X ^ 3 - X ^ 4 = 1 - (X + X ^ 2) * (X + X ^ 2) by ring, h]
  ring

/-- Coefficient extraction for `(2,3,∞)`. -/
theorem sphere23_facts (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3) :
    sphere cs 0 = 1 ∧ sphere cs 1 = 3 ∧ sphere cs 2 = 5 ∧ sphere cs 3 = 7 ∧ sphere cs 4 = 9 ∧
      ∀ n, sphere cs (n + 5) = sphere cs (n + 3) + sphere cs (n + 2) := by
  have H := growth_series_23 cs h01 h02 h12
  have hexp : (1 + X : ℤ⟦X⟧) ^ 2 * (1 + X + X ^ 2) =
      1 + X + X + X + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 3 + X ^ 3 + X ^ 3 + X ^ 4 := by ring
  rw [hexp, mul_sub, mul_sub, mul_one] at H
  have c : ∀ n, coeff n (PowerSeries.mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) -
      coeff n ((PowerSeries.mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) * X ^ 2) -
      coeff n ((PowerSeries.mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) * X ^ 3) =
      coeff n (1 + X + X + X + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 3 + X ^ 3 + X ^ 3 + X ^ 4 :
        ℤ⟦X⟧) := by
    intro n; rw [← map_sub, ← map_sub, H]
  have c0 := c 0
  have c1 := c 1
  have c2 := c 2
  have c3 := c 3
  have c4 := c 4
  simp [coeff_mul_X_pow', coeff_X_pow, coeff_one, coeff_X] at c0 c1 c2 c3 c4
  unfold sphere
  refine ⟨by first | exact_mod_cast c0 | simp, by exact_mod_cast c1, by omega, by omega, by omega,
    fun n => ?_⟩
  have cn := c (n + 5)
  simp [coeff_mul_X_pow', coeff_X_pow, coeff_one, coeff_X] at cn
  omega

theorem sphere23_rec_fails_at_4 (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3) :
    sphere cs 4 ≠ sphere cs 2 + sphere cs 1 := by
  obtain ⟨-, h1, h2, -, h4, -⟩ := sphere23_facts cs h01 h02 h12
  omega

end Closed

/-! ## Padovan -/

/-- The Padovan sequence `1, 1, 1, 2, 2, 3, 4, 5, 7, 9, 12, …`. -/
def padovan : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | n + 3 => padovan (n + 1) + padovan n

/-- Any sequence with the Padovan initial values and recursion is the Padovan sequence. -/
theorem eq_padovan (pad : ℕ → ℕ) (h0 : pad 0 = 1) (h1 : pad 1 = 1) (h2 : pad 2 = 1)
    (hr : ∀ n, pad (n + 3) = pad (n + 1) + pad n) : ∀ n, pad n = padovan n
  | 0 => h0
  | 1 => h1
  | 2 => h2
  | n + 3 => by
    rw [hr, eq_padovan pad h0 h1 h2 hr (n + 1), eq_padovan pad h0 h1 h2 hr n]
    rfl

/-- A sequence with values `5, 7, 9` at `2, 3, 4` and the recursion `f(n+5) = f(n+3) + f(n+2)`
is `Pad(n+5)` from `n = 2` on. -/
theorem eq_padovan_shift (f : ℕ → ℕ) (h2 : f 2 = 5) (h3 : f 3 = 7) (h4 : f 4 = 9)
    (hrec : ∀ n, f (n + 5) = f (n + 3) + f (n + 2)) : ∀ n, 2 ≤ n → f n = padovan (n + 5)
  | 0, h => absurd h (by norm_num)
  | 1, h => absurd h (by norm_num)
  | 2, _ => by rw [h2]; rfl
  | 3, _ => by rw [h3]; rfl
  | 4, _ => by rw [h4]; rfl
  | m + 5, _ => by
    rw [hrec, eq_padovan_shift f h2 h3 h4 hrec (m + 3) (by omega),
      eq_padovan_shift f h2 h3 h4 hrec (m + 2) (by omega)]
    rfl

/-- **Padovan**: for `(2,3,∞)`, `a(n) = Pad(n+5)` for `n ≥ 2`. -/
theorem sphere23_padovan {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3)
    (n : ℕ) (hn : 2 ≤ n) : sphere cs n = padovan (n + 5) := by
  obtain ⟨-, -, h2, h3, h4, hrec⟩ := sphere23_facts cs h01 h02 h12
  exact eq_padovan_shift (sphere cs) h2 h3 h4 hrec n hn

/-! ## Exponential growth rate -/

theorem rho_gt {ρ : ℝ} (h1 : 1 < ρ) (h3 : ρ ^ 3 = ρ + 1) : (1.32 : ℝ) < ρ := by
  by_contra hle
  rw [not_lt] at hle
  have hq : (0:ℝ) ≤ ρ ^ 2 + 1.32 * ρ + 0.7424 := by nlinarith [sq_nonneg ρ]
  nlinarith [mul_nonneg (sub_nonneg.2 hle) hq]

theorem rho_lt {ρ : ℝ} (h1 : 1 < ρ) (h3 : ρ ^ 3 = ρ + 1) : ρ < (1.33 : ℝ) := by
  by_contra hle
  rw [not_lt] at hle
  have hq : (0:ℝ) ≤ ρ ^ 2 + 1.33 * ρ + 0.7689 := by nlinarith [sq_nonneg ρ]
  nlinarith [mul_nonneg (sub_nonneg.2 hle) hq]

/-- Two-sided bound for any sequence with the `(2,3,∞)` values and recursion. -/
theorem growth_bounds_of_rec (f : ℕ → ℕ) (h2 : f 2 = 5) (h3' : f 3 = 7) (h4 : f 4 = 9)
    (hrec : ∀ n, f (n + 5) = f (n + 3) + f (n + 2)) {ρ : ℝ} (h1 : 1 < ρ) (h3 : ρ ^ 3 = ρ + 1)
    (n : ℕ) : 2 * ρ ^ (n + 2) ≤ (f (n + 2) : ℝ) ∧ (f (n + 2) : ℝ) ≤ 4 * ρ ^ (n + 2) := by
  have hlo := rho_gt h1 h3
  have hhi := rho_lt h1 h3
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | _ | m
    · rw [h2]; push_cast
      constructor <;> nlinarith
    · rw [h3']; push_cast
      rw [h3]; constructor <;> nlinarith
    · rw [h4]; push_cast
      have h4' : ρ ^ 4 = ρ ^ 2 + ρ := by
        rw [show ρ ^ 4 = ρ * ρ ^ 3 by ring, h3]; ring
      rw [h4']; constructor <;> nlinarith
    · have ha := ih (m + 1) (by omega)
      have hb := ih m (by omega)
      show 2 * ρ ^ (m + 5) ≤ (f (m + 5) : ℝ) ∧ (f (m + 5) : ℝ) ≤ 4 * ρ ^ (m + 5)
      rw [hrec m]
      push_cast
      have hpow : ρ ^ (m + 5) = ρ ^ (m + 3) + ρ ^ (m + 2) := by
        rw [show ρ ^ (m + 5) = ρ ^ (m + 2) * ρ ^ 3 by ring, h3]; ring
      rw [hpow]
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

theorem const_rpow_inv_mul_tendsto {ρ c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => c ^ ((n : ℝ)⁻¹) * ρ) atTop (𝓝 ρ) := by
  have h : Tendsto (fun n : ℕ => c ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    have hcont := Real.continuousAt_const_rpow (b := 0) hc.ne'
    have := hcont.tendsto.comp tendsto_inv_atTop_nhds_zero_nat
    simpa [Function.comp_def, Real.rpow_zero] using this
  simpa using h.mul_const ρ

/-- `f(n)^{1/n} → ρ` for any sequence with `2ρⁿ ≤ f(n) ≤ 4ρⁿ` eventually. -/
theorem root_tendsto_of_bounds (f : ℕ → ℕ) {ρ : ℝ} (h1 : 1 < ρ)
    (hb : ∀ n, 2 * ρ ^ (n + 2) ≤ (f (n + 2) : ℝ) ∧ (f (n + 2) : ℝ) ≤ 4 * ρ ^ (n + 2)) :
    Tendsto (fun n : ℕ => (f n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 ρ) := by
  have hρ0 : 0 ≤ ρ := by linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (const_rpow_inv_mul_tendsto (ρ := ρ) (c := 2) (by norm_num))
    (const_rpow_inv_mul_tendsto (ρ := ρ) (c := 4) (by norm_num)) ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hb' := (hb m).1
    have hn0 : (m + 2 : ℕ) ≠ 0 := by omega
    calc (2:ℝ) ^ (((m + 2 : ℕ) : ℝ))⁻¹ * ρ
        = (2 * ρ ^ (m + 2)) ^ (((m + 2 : ℕ) : ℝ))⁻¹ := by
          rw [Real.mul_rpow (by norm_num) (pow_nonneg hρ0 _), Real.pow_rpow_inv_natCast hρ0 hn0]
      _ ≤ (f (m + 2) : ℝ) ^ (((m + 2 : ℕ) : ℝ))⁻¹ :=
          Real.rpow_le_rpow (by positivity) hb' (by positivity)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hb' := (hb m).2
    have hn0 : (m + 2 : ℕ) ≠ 0 := by omega
    calc (f (m + 2) : ℝ) ^ (((m + 2 : ℕ) : ℝ))⁻¹
        ≤ (4 * ρ ^ (m + 2)) ^ (((m + 2 : ℕ) : ℝ))⁻¹ :=
          Real.rpow_le_rpow (by positivity) hb' (by positivity)
      _ = (4:ℝ) ^ (((m + 2 : ℕ) : ℝ))⁻¹ * ρ := by
          rw [Real.mul_rpow (by norm_num) (pow_nonneg hρ0 _), Real.pow_rpow_inv_natCast hρ0 hn0]

section Rate

variable {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)} (cs : CoxeterSystem M W)

/-- `(2,3,∞)`: `2ρⁿ ≤ a(n) ≤ 4ρⁿ` for `n ≥ 2`, for every real `ρ > 1` with `ρ³ = ρ + 1`. -/
theorem sphere23_growth (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3)
    {ρ : ℝ} (h1 : 1 < ρ) (h3 : ρ ^ 3 = ρ + 1) (n : ℕ) :
    2 * ρ ^ (n + 2) ≤ (sphere cs (n + 2) : ℝ) ∧ (sphere cs (n + 2) : ℝ) ≤ 4 * ρ ^ (n + 2) := by
  obtain ⟨-, -, h2, h3', h4, hrec⟩ := sphere23_facts cs h01 h02 h12
  exact growth_bounds_of_rec (sphere cs) h2 h3' h4 hrec h1 h3 n

/-- `(2,3,∞)`: `a(n)^{1/n} → ρ`. -/
theorem sphere23_root_tendsto (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3)
    {ρ : ℝ} (h1 : 1 < ρ) (h3 : ρ ^ 3 = ρ + 1) :
    Tendsto (fun n : ℕ => (sphere cs n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 ρ) :=
  root_tendsto_of_bounds (sphere cs) h1 (sphere23_growth cs h01 h02 h12 h1 h3)

/-- `(2,3,∞)`: the growth rate is the plastic number of `CoxeterGrowth.Plastic`. -/
theorem sphere23_root_tendsto_plastic (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3) :
    Tendsto (fun n : ℕ => (sphere cs n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 plasticNumber) :=
  sphere23_root_tendsto cs h01 h02 h12 one_lt_plasticNumber plasticNumber_cubic

end Rate

end CoxeterGrowth.Triangle
