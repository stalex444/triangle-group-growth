module
public import CoxeterGrowth.Instances

@[expose] public section
/-!
# The `(p, q, ∞)` family: monotonicity, minimality of `ρ`, and the growth rates

Write `a_{p,q}(n)` for the number of elements of length `n` in a Coxeter system of type
`(p, q, ∞)` (`CoxeterGrowth.Triangle.IsTri`).

* **Monotonicity and symmetry** (`sphere_mono`, `sphere_symm`): the normal-form validity
  predicate `V p q` is monotone in the block bounds, so `NFs p q n ⊆ NFs p' q' n` for `p ≤ p'`,
  `q ≤ q'`; and `swap` is a length-preserving bijection `NFs p q n ≃ NFs q p n`. Both transfer to
  the Coxeter systems through `sphere_eq_card`.
* **Minimality of the plastic number** (`sphere_ge_plastic`): every hyperbolic member dominates
  `(2, 3, ∞)` or `(3, 2, ∞)`, hence `2ρⁿ ≤ a_{p,q}(n)` for `n ≥ 2`.
* **The growth rate of every member** (`rate_exists_unique`, `sphere_root_tendsto_rate`): for
  `(p, q) ≠ (2, 2)` there is exactly one `τ > 1` with
  `(τ⁻¹ + ⋯ + τ^{−(p−1)})(τ⁻¹ + ⋯ + τ^{−(q−1)}) = 1`, and `a_{p,q}(n)^{1/n} → τ`. The proof
  extracts from the growth series the recursion
  `a(n) = Σ_{1≤i<p} Σ_{1≤j<q} a(n − i − j)` for `n ≥ p + q` (`rec_of_series`), whose
  coefficients are non-negative, and runs it as an induction for `τ^{n−(p+q)} ≤ a(n) ≤ C τⁿ`.
* **The rates as a function of `(p, q)`** (`rate_lt_rate`, `plastic_le_rate`, `rate_lt_two`,
  `rate_tendsto_two`): strictly increasing in each argument, so `ρ = τ_{2,3} = τ_{3,2}` is the
  minimum over the hyperbolic members, attained only there; every rate is `< 2` and the rates
  tend to `2`.
-/

namespace CoxeterGrowth.Triangle

open Finset PowerSeries Filter Topology

/-! ## Monotonicity and symmetry of the normal-form counts -/

theorem VT_mono (r : List ℕ) :
    ∀ {m₁ m₂ m₁' m₂' : ℕ}, m₁ ≤ m₁' → m₂ ≤ m₂' → VT m₁ m₂ r → VT m₁' m₂' r := by
  induction r with
  | nil => intro _ _ _ _ _ _ _; exact VT_nil.2 trivial
  | cons k r ih =>
    intro m₁ m₂ m₁' m₂' h1 h2 h
    rw [VT_cons] at h ⊢
    exact ⟨h.1, lt_of_lt_of_le h.2.1 h1, ih h2 h1 h.2.2⟩

theorem V_mono {p q p' q' : ℕ} (hp : p ≤ p') (hq : q ≤ q') (v : Raw) (h : V p q v) :
    V p' q' v :=
  ⟨⟨h.1.1, lt_of_lt_of_le h.1.2 hp⟩, VT_mono v.2 hq hp h.2⟩

theorem NFs_mono {p q p' q' : ℕ} (hp : p ≤ p') (hq : q ≤ q') (n : ℕ) :
    NFs p q n ⊆ NFs p' q' n := fun v hv => by
  rw [mem_NFs] at hv ⊢
  exact ⟨V_mono hp hq v hv.1, hv.2⟩

theorem card_NFs_swap_le {p q : ℕ} (hq : 1 ≤ q) (n : ℕ) :
    (NFs p q n).card ≤ (NFs q p n).card := by
  refine card_le_card_of_injOn swap (fun v hv => ?_) (fun v hv w hw h => ?_)
  · have hv' := (mem_NFs p q n v).1 (Finset.mem_coe.1 hv)
    exact Finset.mem_coe.2
      ((mem_NFs q p n _).2 ⟨swap_V hq v hv'.1, by rw [len_swap]; exact hv'.2⟩)
  · have hv' := (mem_NFs p q n v).1 (Finset.mem_coe.1 hv)
    have hw' := (mem_NFs p q n w).1 (Finset.mem_coe.1 hw)
    calc v = swap (swap v) := (swap_swap v hv'.1).symm
      _ = swap (swap w) := by rw [h]
      _ = w := swap_swap w hw'.1

theorem card_NFs_swap {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (n : ℕ) :
    (NFs p q n).card = (NFs q p n).card :=
  le_antisymm (card_NFs_swap_le hq n) (card_NFs_swap_le hp n)

theorem VT_ones (n : ℕ) : ∀ {m₁ m₂ : ℕ}, 2 ≤ m₁ → 2 ≤ m₂ → VT m₁ m₂ (List.replicate n 1) := by
  induction n with
  | zero => intro _ _ _ _; exact VT_nil.2 trivial
  | succ n ih =>
    intro m₁ m₂ h1 h2
    rw [List.replicate_succ, VT_cons]
    exact ⟨Nat.one_pos, h1, ih h2 h1⟩

/-- Every length carries a normal form (the alternating word with all blocks of length one). -/
theorem card_NFs_pos {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (n : ℕ) : 0 < (NFs p q n).card := by
  apply Finset.card_pos.2
  refine ⟨((0, 0), List.replicate n 1), (mem_NFs p q n _).2 ⟨?_, ?_⟩⟩
  · rw [V_mk]
    exact ⟨⟨by omega, by omega⟩, VT_ones n hq hp⟩
  · rw [len_mk]
    simp

/-- The `(p, q, ∞)` hypotheses are met by `triM p q`. -/
theorem isTri_triM (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) : IsTri (triM p q hp hq) p q :=
  ⟨hp, hq, rfl, rfl, rfl⟩

theorem card_NFs23_lower {ρ : ℝ} (h1 : 1 < ρ) (h3 : ρ ^ 3 = ρ + 1) (n : ℕ) :
    2 * ρ ^ (n + 2) ≤ ((NFs 2 3 (n + 2)).card : ℝ) := by
  have h := (sphere23_growth (triM 2 3 le_rfl (by norm_num)).toCoxeterSystem rfl rfl rfl h1 h3
    n).1
  unfold sphere at h
  rwa [sphere_eq_card _ (isTri_triM 2 3 le_rfl (by norm_num))] at h

/-- Every hyperbolic member dominates `(2, 3, ∞)` (if `p = 2`) or `(3, 2, ∞)` (if `p ≥ 3`). -/
theorem card_NFs23_le {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hne : (p, q) ≠ (2, 2)) (n : ℕ) :
    (NFs 2 3 n).card ≤ (NFs p q n).card := by
  rcases Nat.lt_or_ge 2 p with hp3 | hp2
  · rw [card_NFs_swap (by norm_num) (by norm_num) n]
    exact card_le_card (NFs_mono hp3 hq n)
  · obtain rfl : p = 2 := le_antisymm hp2 hp
    have hq3 : 3 ≤ q := by
      by_contra hc
      have h2 : q = 2 := by omega
      exact hne (by rw [h2])
    exact card_le_card (NFs_mono le_rfl hq3 n)

section Family

variable {W W' : Type*} [Group W] [Group W'] {M M' : CoxeterMatrix (Fin 3)}
  (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')

/-- **Monotonicity**: `a_{p,q}(n) ≤ a_{p',q'}(n)` for `p ≤ p'`, `q ≤ q'`. -/
theorem sphere_mono {p q p' q' : ℕ} (hT : IsTri M p q) (hT' : IsTri M' p' q') (hp : p ≤ p')
    (hq : q ≤ q') (n : ℕ) : sphere cs n ≤ sphere cs' n := by
  unfold sphere
  rw [sphere_eq_card cs hT, sphere_eq_card cs' hT']
  exact card_le_card (NFs_mono hp hq n)

/-- **Symmetry**: `a_{p,q}(n) = a_{q,p}(n)`. -/
theorem sphere_symm {p q : ℕ} (hT : IsTri M p q) (hT' : IsTri M' q p) (n : ℕ) :
    sphere cs n = sphere cs' n := by
  unfold sphere
  rw [sphere_eq_card cs hT, sphere_eq_card cs' hT']
  exact card_NFs_swap (by have := hT.hp; omega) (by have := hT.hq; omega) n

/-- **Minimality of the plastic number in the family**: `2ρⁿ ≤ a_{p,q}(n)` for `n ≥ 2` and every
hyperbolic `(p, q, ∞)`. -/
theorem sphere_ge_plastic {p q : ℕ} (hT : IsTri M p q) (hne : (p, q) ≠ (2, 2)) {ρ : ℝ}
    (h1 : 1 < ρ) (h3 : ρ ^ 3 = ρ + 1) (n : ℕ) : 2 * ρ ^ (n + 2) ≤ (sphere cs (n + 2) : ℝ) := by
  unfold sphere
  rw [sphere_eq_card cs hT]
  calc 2 * ρ ^ (n + 2) ≤ ((NFs 2 3 (n + 2)).card : ℝ) := card_NFs23_lower h1 h3 n
    _ ≤ ((NFs p q (n + 2)).card : ℝ) := by
      exact_mod_cast card_NFs23_le hT.hp hT.hq hne (n + 2)

end Family

/-! ## The recursion of the sphere sizes -/

theorem coeff_numer_eq_zero (p q n : ℕ) (hn : p + q ≤ n) :
    coeff n ((1 + X) * (∑ i ∈ range p, (X : ℤ⟦X⟧) ^ i) * (∑ i ∈ range q, (X : ℤ⟦X⟧) ^ i)) =
      0 := by
  have h2 : (1 + X : ℤ⟦X⟧) = ∑ e ∈ range 2, X ^ e := by simp [sum_range_succ]
  rw [h2]
  simp only [sum_mul, mul_sum, ← pow_add, map_sum, coeff_X_pow]
  refine sum_eq_zero fun a ha => sum_eq_zero fun b hb => sum_eq_zero fun c hc => ?_
  rw [mem_range] at ha hb hc
  rw [ite_eq_right (by omega)]

theorem coeff_denom (f : ℕ → ℤ) (p q n : ℕ) (hn : p + q ≤ n) :
    coeff n (mk f * (1 - (∑ i ∈ Ico 1 p, (X : ℤ⟦X⟧) ^ i) * (∑ i ∈ Ico 1 q, (X : ℤ⟦X⟧) ^ i))) =
      f n - ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q, f (n - (i + j)) := by
  rw [mul_sub, mul_one, map_sub, coeff_mk, sum_mul_sum, mul_sum, map_sum]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  rw [mul_sum, map_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_Ico] at hi hj
  rw [← pow_add, coeff_mul_X_pow', coeff_mk, ite_eq_left (by omega)]

/-- **The recursion**: a sequence with the `(p, q, ∞)` growth series satisfies
`f(n) = Σ_{1≤i<p} Σ_{1≤j<q} f(n − i − j)` for `n ≥ p + q`. -/
theorem rec_of_series (f : ℕ → ℕ) (p q : ℕ)
    (H : (PowerSeries.mk fun n => (f n : ℤ)) *
        (1 - (∑ i ∈ Ico 1 p, (X : ℤ⟦X⟧) ^ i) * (∑ i ∈ Ico 1 q, (X : ℤ⟦X⟧) ^ i)) =
      (1 + X) * (∑ i ∈ range p, (X : ℤ⟦X⟧) ^ i) * (∑ i ∈ range q, (X : ℤ⟦X⟧) ^ i))
    (n : ℕ) (hn : p + q ≤ n) : f n = ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q, f (n - (i + j)) := by
  have h := congrArg (coeff n) H
  rw [coeff_denom _ p q n hn, coeff_numer_eq_zero p q n hn] at h
  have h' : (f n : ℤ) = ((∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q, f (n - (i + j)) : ℕ) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast h'

/-! ## Exponential bounds from the recursion -/

theorem pow_sub_eq {τ : ℝ} (hτ : τ ≠ 0) {n i j : ℕ} (h : i + j ≤ n) :
    τ ^ (n - (i + j)) = τ ^ n * (τ⁻¹ ^ i * τ⁻¹ ^ j) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + (i + j) := ⟨n - (i + j), by omega⟩
  rw [Nat.add_sub_cancel]
  have hi : τ ^ i * τ⁻¹ ^ i = 1 := by rw [← mul_pow, mul_inv_cancel₀ hτ, one_pow]
  have hj : τ ^ j * τ⁻¹ ^ j = 1 := by rw [← mul_pow, mul_inv_cancel₀ hτ, one_pow]
  calc τ ^ m = τ ^ m * ((τ ^ i * τ⁻¹ ^ i) * (τ ^ j * τ⁻¹ ^ j)) := by rw [hi, hj]; ring
    _ = τ ^ (m + (i + j)) * (τ⁻¹ ^ i * τ⁻¹ ^ j) := by ring

theorem sum_pow_sub {p q n : ℕ} (hn : p + q ≤ n) {τ : ℝ} (hτ : τ ≠ 0)
    (heq : (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) = 1) :
    ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q, τ ^ (n - (i + j)) = τ ^ n := by
  calc ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q, τ ^ (n - (i + j))
      = ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q, τ ^ n * (τ⁻¹ ^ i * τ⁻¹ ^ j) := by
        refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
        rw [mem_Ico] at hi hj
        exact pow_sub_eq hτ (by omega)
    _ = τ ^ n * ((∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i)) := by
        rw [sum_mul_sum, mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [mul_sum]
    _ = τ ^ n := by rw [heq, mul_one]

/-- Lower bound `τⁿ ≤ τ^{p+q} f(n)` from the recursion and positivity. -/
theorem lower_of_rec (f : ℕ → ℕ) {p q : ℕ} (hpos : ∀ n, 1 ≤ f n)
    (hrec : ∀ n, p + q ≤ n → f n = ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q, f (n - (i + j)))
    {τ : ℝ} (hτ : 1 < τ) (heq : (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) = 1)
    (n : ℕ) : τ ^ n ≤ τ ^ (p + q) * f n := by
  have hτ0 : 0 < τ := by linarith
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n (p + q) with hn | hn
    · have h1 : τ ^ n ≤ τ ^ (p + q) := pow_le_pow_right₀ hτ.le hn.le
      have h2 : (1 : ℝ) ≤ f n := by exact_mod_cast hpos n
      calc τ ^ n ≤ τ ^ (p + q) := h1
        _ = τ ^ (p + q) * 1 := (mul_one _).symm
        _ ≤ τ ^ (p + q) * f n := mul_le_mul_of_nonneg_left h2 (pow_nonneg hτ0.le _)
    · rw [hrec n hn]
      push_cast
      calc τ ^ n = ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q, τ ^ (n - (i + j)) :=
            (sum_pow_sub hn hτ0.ne' heq).symm
        _ ≤ ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q, τ ^ (p + q) * (f (n - (i + j)) : ℝ) := by
            refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
            rw [mem_Ico] at hi hj
            exact ih _ (by omega)
        _ = τ ^ (p + q) * ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q, (f (n - (i + j)) : ℝ) := by
            simp only [mul_sum]

/-- Upper bound `f(n) ≤ C τⁿ`, `C = f(0) + ⋯ + f(p+q−1)`, from the recursion. -/
theorem upper_of_rec (f : ℕ → ℕ) {p q : ℕ}
    (hrec : ∀ n, p + q ≤ n → f n = ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q, f (n - (i + j)))
    {τ : ℝ} (hτ : 1 < τ) (heq : (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) = 1)
    (n : ℕ) : (f n : ℝ) ≤ (∑ m ∈ range (p + q), (f m : ℝ)) * τ ^ n := by
  have hτ0 : 0 < τ := by linarith
  have hC0 : 0 ≤ ∑ m ∈ range (p + q), (f m : ℝ) := sum_nonneg fun m _ => Nat.cast_nonneg _
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n (p + q) with hn | hn
    · have h1 : (f n : ℝ) ≤ ∑ m ∈ range (p + q), (f m : ℝ) :=
        single_le_sum (f := fun m => (f m : ℝ)) (fun m _ => Nat.cast_nonneg _) (mem_range.2 hn)
      have h2 : (1 : ℝ) ≤ τ ^ n := one_le_pow₀ hτ.le
      calc (f n : ℝ) ≤ ∑ m ∈ range (p + q), (f m : ℝ) := h1
        _ = (∑ m ∈ range (p + q), (f m : ℝ)) * 1 := (mul_one _).symm
        _ ≤ (∑ m ∈ range (p + q), (f m : ℝ)) * τ ^ n := mul_le_mul_of_nonneg_left h2 hC0
    · rw [hrec n hn]
      push_cast
      calc ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q, (f (n - (i + j)) : ℝ)
          ≤ ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q,
              (∑ m ∈ range (p + q), (f m : ℝ)) * τ ^ (n - (i + j)) := by
            refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
            rw [mem_Ico] at hi hj
            exact ih _ (by omega)
        _ = (∑ m ∈ range (p + q), (f m : ℝ)) * τ ^ n := by
            rw [← sum_pow_sub hn hτ0.ne' heq]
            simp only [mul_sum]

/-- `f(n)^{1/n} → τ` for any sequence with `c τⁿ ≤ f(n) ≤ C τⁿ`, `c, C > 0`. -/
theorem root_tendsto_of_bounds' (f : ℕ → ℕ) {τ c C : ℝ} (hτ : 0 ≤ τ) (hc : 0 < c) (hC : 0 < C)
    (hlo : ∀ n, c * τ ^ n ≤ f n) (hhi : ∀ n, (f n : ℝ) ≤ C * τ ^ n) :
    Tendsto (fun n : ℕ => (f n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 τ) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (const_rpow_inv_mul_tendsto (ρ := τ) hc) (const_rpow_inv_mul_tendsto (ρ := τ) hC) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : n ≠ 0 := by omega
    calc c ^ ((n : ℝ))⁻¹ * τ = (c * τ ^ n) ^ ((n : ℝ))⁻¹ := by
          rw [Real.mul_rpow hc.le (pow_nonneg hτ _), Real.pow_rpow_inv_natCast hτ hn0]
      _ ≤ (f n : ℝ) ^ ((n : ℝ))⁻¹ :=
          Real.rpow_le_rpow (mul_nonneg hc.le (pow_nonneg hτ _)) (hlo n) (by positivity)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : n ≠ 0 := by omega
    calc (f n : ℝ) ^ ((n : ℝ))⁻¹ ≤ (C * τ ^ n) ^ ((n : ℝ))⁻¹ :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) (hhi n) (by positivity)
      _ = C ^ ((n : ℝ))⁻¹ * τ := by
          rw [Real.mul_rpow hC.le (pow_nonneg hτ _), Real.pow_rpow_inv_natCast hτ hn0]

/-! ## The rate equation -/

theorem sumIco_nonneg (m : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ ∑ i ∈ Ico 1 m, x ^ i :=
  sum_nonneg fun i _ => pow_nonneg hx i

theorem sumIco_pos {m : ℕ} (hm : 2 ≤ m) {x : ℝ} (hx : 0 < x) : 0 < ∑ i ∈ Ico 1 m, x ^ i := by
  have h := single_le_sum (f := fun i => x ^ i) (fun i _ => pow_nonneg hx.le i)
    (mem_Ico.2 ⟨le_rfl, hm⟩ : 1 ∈ Ico 1 m)
  simp only [pow_one] at h
  exact lt_of_lt_of_le hx h

theorem sumIco_lt {m : ℕ} (hm : 2 ≤ m) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    ∑ i ∈ Ico 1 m, x ^ i < ∑ i ∈ Ico 1 m, y ^ i :=
  sum_lt_sum (fun i _ => pow_le_pow_left₀ hx hxy.le i)
    ⟨1, mem_Ico.2 ⟨le_rfl, hm⟩, by simpa using hxy⟩

theorem sumIco_le_of_le {m m' : ℕ} (h : m ≤ m') {x : ℝ} (hx : 0 ≤ x) :
    ∑ i ∈ Ico 1 m, x ^ i ≤ ∑ i ∈ Ico 1 m', x ^ i :=
  sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right h) fun i _ _ => pow_nonneg hx i

theorem sumIco_lt_of_lt {m m' : ℕ} (hm : 1 ≤ m) (h : m < m') {x : ℝ} (hx : 0 < x) :
    ∑ i ∈ Ico 1 m, x ^ i < ∑ i ∈ Ico 1 m', x ^ i :=
  sum_lt_sum_of_subset (Ico_subset_Ico_right h.le) (i := m) (mem_Ico.2 ⟨hm, h⟩)
    (by simp) (pow_pos hx m) (fun j _ _ => pow_nonneg hx.le j)

/-- `x ↦ S_p(x) S_q(x)` is strictly increasing on `[0, ∞)`. -/
theorem rateFn_lt {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    (∑ i ∈ Ico 1 p, x ^ i) * (∑ i ∈ Ico 1 q, x ^ i) <
      (∑ i ∈ Ico 1 p, y ^ i) * (∑ i ∈ Ico 1 q, y ^ i) :=
  mul_lt_mul'' (sumIco_lt hp hx hxy) (sumIco_lt hq hx hxy) (sumIco_nonneg p hx)
    (sumIco_nonneg q hx)

theorem rateFn_le {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (∑ i ∈ Ico 1 p, x ^ i) * (∑ i ∈ Ico 1 q, x ^ i) ≤
      (∑ i ∈ Ico 1 p, y ^ i) * (∑ i ∈ Ico 1 q, y ^ i) := by
  rcases hxy.lt_or_eq with h | h
  · exact (rateFn_lt hp hq hx h).le
  · rw [h]

theorem rateFn_inj {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hgx : (∑ i ∈ Ico 1 p, x ^ i) * (∑ i ∈ Ico 1 q, x ^ i) = 1)
    (hgy : (∑ i ∈ Ico 1 p, y ^ i) * (∑ i ∈ Ico 1 q, y ^ i) = 1) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · have := rateFn_lt hp hq hx h; linarith
  · exact h
  · have := rateFn_lt hp hq hy h; linarith

theorem sumIco_zero (m : ℕ) : ∑ i ∈ Ico 1 m, (0 : ℝ) ^ i = 0 :=
  sum_eq_zero fun i hi => zero_pow (by rw [mem_Ico] at hi; omega)

theorem sumIco_one (m : ℕ) : ∑ i ∈ Ico 1 m, (1 : ℝ) ^ i = ((m - 1 : ℕ) : ℝ) := by
  simp

/-- **Existence and uniqueness of the rate**: for `(p, q) ≠ (2, 2)` exactly one `τ > 1` solves
`S_p(τ⁻¹) S_q(τ⁻¹) = 1`. -/
theorem rate_exists_unique {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hne : (p, q) ≠ (2, 2)) :
    ∃! τ : ℝ, 1 < τ ∧ (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) = 1 := by
  have hcont : ContinuousOn
      (fun x : ℝ => (∑ i ∈ Ico 1 p, x ^ i) * (∑ i ∈ Ico 1 q, x ^ i)) (Set.Icc 0 1) :=
    ((continuous_finsetSum _ fun i _ => continuous_pow i).mul
      (continuous_finsetSum _ fun i _ => continuous_pow i)).continuousOn
  have h2 : 2 ≤ (p - 1) * (q - 1) := by
    rcases Nat.lt_or_ge 2 p with hp3 | hp2
    · calc 2 = 2 * 1 := rfl
        _ ≤ (p - 1) * (q - 1) := Nat.mul_le_mul (by omega) (by omega)
    · obtain rfl : p = 2 := le_antisymm hp2 hp
      have hq3 : 3 ≤ q := by
        by_contra hc
        have h2 : q = 2 := by omega
        exact hne (by rw [h2])
      calc 2 = 1 * 2 := rfl
        _ ≤ (2 - 1) * (q - 1) := Nat.mul_le_mul (by omega) (by omega)
  have g1 : (1 : ℝ) < (∑ i ∈ Ico 1 p, (1 : ℝ) ^ i) * (∑ i ∈ Ico 1 q, (1 : ℝ) ^ i) := by
    rw [sumIco_one, sumIco_one, ← Nat.cast_mul]
    exact_mod_cast h2
  have g0 : (∑ i ∈ Ico 1 p, (0 : ℝ) ^ i) * (∑ i ∈ Ico 1 q, (0 : ℝ) ^ i) = 0 := by
    rw [sumIco_zero, zero_mul]
  obtain ⟨x, hx, hgx⟩ := intermediate_value_Icc zero_le_one hcont
    (⟨by rw [g0]; exact zero_le_one, g1.le⟩ :
      (1 : ℝ) ∈ Set.Icc ((∑ i ∈ Ico 1 p, (0 : ℝ) ^ i) * (∑ i ∈ Ico 1 q, (0 : ℝ) ^ i))
        ((∑ i ∈ Ico 1 p, (1 : ℝ) ^ i) * (∑ i ∈ Ico 1 q, (1 : ℝ) ^ i)))
  simp only at hgx
  have hx0 : 0 < x := by
    rcases hx.1.lt_or_eq with h | h
    · exact h
    · rw [← h, g0] at hgx; exact absurd hgx zero_ne_one
  have hx1 : x < 1 := by
    rcases hx.2.lt_or_eq with h | h
    · exact h
    · rw [h] at hgx; linarith
  refine ⟨x⁻¹, ⟨(one_lt_inv₀ hx0).2 hx1, by rw [inv_inv]; exact hgx⟩, fun τ hτ => ?_⟩
  have hτ0 : 0 < τ := by linarith [hτ.1]
  have := rateFn_inj hp hq (inv_pos.2 hτ0).le hx0.le hτ.2 hgx
  rw [← this, inv_inv]

/-! ## The growth rate of every member -/

section Rate

variable {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)} (cs : CoxeterSystem M W)

theorem sphere_rec {p q : ℕ} (hT : IsTri M p q) (n : ℕ) (hn : p + q ≤ n) :
    sphere cs n = ∑ i ∈ Ico 1 p, ∑ j ∈ Ico 1 q, sphere cs (n - (i + j)) :=
  rec_of_series (sphere cs) p q (growth_series cs hT) n hn

theorem one_le_sphere {p q : ℕ} (hT : IsTri M p q) (n : ℕ) : 1 ≤ sphere cs n := by
  unfold sphere
  rw [sphere_eq_card cs hT]
  exact card_NFs_pos hT.hp hT.hq n

/-- **The growth rate of `(p, q, ∞)`**: `a(n)^{1/n} → τ`, the root of the rate equation. -/
theorem sphere_root_tendsto_rate {p q : ℕ} (hT : IsTri M p q) {τ : ℝ} (hτ : 1 < τ)
    (heq : (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) = 1) :
    Tendsto (fun n : ℕ => (sphere cs n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 τ) := by
  have hrec := sphere_rec cs hT
  have hτ0 : 0 < τ := by linarith
  have hK : 0 < τ ^ (p + q) := pow_pos hτ0 _
  have hC : (0 : ℝ) < ∑ m ∈ range (p + q), (sphere cs m : ℝ) := by
    have h0 : (0 : ℝ) < (sphere cs 0 : ℝ) := by exact_mod_cast one_le_sphere cs hT 0
    have h1 := single_le_sum (f := fun m => (sphere cs m : ℝ)) (fun m _ => Nat.cast_nonneg _)
      (mem_range.2 (show 0 < p + q by have := hT.hp; omega))
    exact lt_of_lt_of_le h0 h1
  refine root_tendsto_of_bounds' (sphere cs) hτ0.le (inv_pos.2 hK) hC (fun n => ?_)
    (fun n => upper_of_rec (sphere cs) hrec hτ heq n)
  have h := lower_of_rec (sphere cs) (one_le_sphere cs hT) hrec hτ heq n
  calc (τ ^ (p + q))⁻¹ * τ ^ n ≤ (τ ^ (p + q))⁻¹ * (τ ^ (p + q) * sphere cs n) :=
        mul_le_mul_of_nonneg_left h (inv_pos.2 hK).le
    _ = sphere cs n := inv_mul_cancel_left₀ hK.ne' _

end Rate

/-! ## The rates as a function of `(p, q)` -/

/-- **Strict monotonicity of the rate** in `(p, q)`. -/
theorem rate_lt_rate {p q p' q' : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpp : p ≤ p') (hqq : q ≤ q')
    (hne : (p, q) ≠ (p', q')) {τ τ' : ℝ} (hτ : 1 < τ) (hτ' : 1 < τ')
    (heq : (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) = 1)
    (heq' : (∑ i ∈ Ico 1 p', τ'⁻¹ ^ i) * (∑ i ∈ Ico 1 q', τ'⁻¹ ^ i) = 1) : τ < τ' := by
  have hx : 0 < τ⁻¹ := inv_pos.2 (by linarith)
  have hx' : 0 < τ'⁻¹ := inv_pos.2 (by linarith)
  have hp' : 2 ≤ p' := le_trans hp hpp
  have hq' : 2 ≤ q' := le_trans hq hqq
  have A := sumIco_le_of_le hpp hx.le
  have B := sumIco_le_of_le hqq hx.le
  have A0 := sumIco_pos hp hx
  have B0 := sumIco_pos hq hx
  have hstep : (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) <
      (∑ i ∈ Ico 1 p', τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q', τ⁻¹ ^ i) := by
    rcases Nat.lt_or_ge p p' with h | h
    · have A' := sumIco_lt_of_lt (by omega) h hx
      calc _ < (∑ i ∈ Ico 1 p', τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) :=
            mul_lt_mul_of_pos_right A' B0
        _ ≤ _ := mul_le_mul_of_nonneg_left B (by linarith)
    · have hpe : p = p' := le_antisymm hpp h
      have hq'' : q < q' := lt_of_le_of_ne hqq (fun h' => hne (by rw [hpe, h']))
      have B' := sumIco_lt_of_lt (by omega) hq'' hx
      calc _ ≤ (∑ i ∈ Ico 1 p', τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) :=
            mul_le_mul_of_nonneg_right A B0.le
        _ < _ := mul_lt_mul_of_pos_left B' (by linarith)
  have hlt : τ'⁻¹ < τ⁻¹ := not_le.mp fun h => by
    have := rateFn_le hp' hq' hx.le h
    linarith
  exact (inv_lt_inv₀ (by linarith) (by linarith)).1 hlt

theorem sum_Ico_1_2_real (x : ℝ) : ∑ i ∈ Ico 1 2, x ^ i = x := by
  simp

theorem sum_Ico_1_3_real (x : ℝ) : ∑ i ∈ Ico 1 3, x ^ i = x + x ^ 2 := by
  simp [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]

/-- The `(2, 3)` rate equation is the plastic cubic. -/
theorem rate23_iff {τ : ℝ} (hτ : 0 < τ) :
    (∑ i ∈ Ico 1 2, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 3, τ⁻¹ ^ i) = 1 ↔ τ ^ 3 = τ + 1 := by
  rw [sum_Ico_1_2_real, sum_Ico_1_3_real]
  have hi : τ⁻¹ * τ = 1 := inv_mul_cancel₀ hτ.ne'
  have key : τ⁻¹ * (τ⁻¹ + τ⁻¹ ^ 2) * τ ^ 3 = τ + 1 := by
    calc τ⁻¹ * (τ⁻¹ + τ⁻¹ ^ 2) * τ ^ 3 = (τ⁻¹ * τ) ^ 2 * τ + (τ⁻¹ * τ) ^ 3 := by ring
      _ = τ + 1 := by rw [hi]; ring
  have h3ne : τ ^ 3 ≠ 0 := pow_ne_zero _ hτ.ne'
  constructor
  · intro h
    rw [h, one_mul] at key
    exact key
  · intro h
    have h' : τ⁻¹ * (τ⁻¹ + τ⁻¹ ^ 2) * τ ^ 3 = 1 * τ ^ 3 := by rw [key, h, one_mul]
    exact mul_right_cancel₀ h3ne h'

/-- A rate `τ > 1` excludes the affine `(2, 2)`. -/
theorem ne22_of_rate {p q : ℕ} {τ : ℝ} (hτ : 1 < τ)
    (heq : (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) = 1) : (p, q) ≠ (2, 2) := by
  intro h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  rw [sum_Ico_1_2_real] at heq
  have hx0 : 0 < τ⁻¹ := inv_pos.2 (by linarith)
  have hx1 : τ⁻¹ < 1 := (inv_lt_one₀ (by linarith)).2 hτ
  nlinarith

/-- **The plastic number is the minimal rate** of the hyperbolic `(p, q, ∞)`, attained only at
`(2, 3)` and `(3, 2)`. -/
theorem plastic_le_rate {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) {τ : ℝ} (hτ : 1 < τ)
    (heq : (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) = 1) {ρ : ℝ} (hρ : 1 < ρ)
    (hρ3 : ρ ^ 3 = ρ + 1) : ρ ≤ τ ∧ (τ = ρ ↔ (p = 2 ∧ q = 3) ∨ (p = 3 ∧ q = 2)) := by
  have hne := ne22_of_rate hτ heq
  have hρ23 : (∑ i ∈ Ico 1 2, ρ⁻¹ ^ i) * (∑ i ∈ Ico 1 3, ρ⁻¹ ^ i) = 1 :=
    (rate23_iff (by linarith)).2 hρ3
  have hρ32 : (∑ i ∈ Ico 1 3, ρ⁻¹ ^ i) * (∑ i ∈ Ico 1 2, ρ⁻¹ ^ i) = 1 := by
    rw [mul_comm]; exact hρ23
  by_cases h23 : (p = 2 ∧ q = 3) ∨ (p = 3 ∧ q = 2)
  · have hτρ : τ = ρ := by
      rcases h23 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have h3 := (rate23_iff (by linarith)).1 heq
        rw [plasticNumber_unique hτ h3, plasticNumber_unique hρ hρ3]
      · rw [mul_comm] at heq
        have h3 := (rate23_iff (by linarith)).1 heq
        rw [plasticNumber_unique hτ h3, plasticNumber_unique hρ hρ3]
    exact ⟨hτρ.ge, iff_of_true hτρ h23⟩
  · have hlt : ρ < τ := by
      rcases Nat.lt_or_ge 2 p with hp3 | hp2
      · refine rate_lt_rate (by norm_num) le_rfl hp3 hq ?_ hρ hτ hρ32 heq
        intro h
        exact h23 (Or.inr ⟨(Prod.mk.inj h).1.symm, (Prod.mk.inj h).2.symm⟩)
      · obtain rfl : p = 2 := le_antisymm hp2 hp
        have hq3 : 3 ≤ q := by
          by_contra hc
          have h2 : q = 2 := by omega
          exact hne (by rw [h2])
        refine rate_lt_rate le_rfl (by norm_num) le_rfl hq3 ?_ hρ hτ hρ23 heq
        intro h
        exact h23 (Or.inl ⟨rfl, (Prod.mk.inj h).2.symm⟩)
    exact ⟨hlt.le, iff_of_false hlt.ne' h23⟩

theorem sumIco_half_lt {m : ℕ} (hm : 1 ≤ m) : ∑ i ∈ Ico 1 m, (2⁻¹ : ℝ) ^ i < 1 := by
  have h := geom_sum_Ico_mul_neg (2⁻¹ : ℝ) hm
  have hpos : 0 < (2⁻¹ : ℝ) ^ m := by positivity
  rw [pow_one] at h
  linarith

/-- **Every rate is below 2.** -/
theorem rate_lt_two {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) {τ : ℝ} (hτ : 1 < τ)
    (heq : (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) = 1) : τ < 2 := by
  have hx : 0 < τ⁻¹ := inv_pos.2 (by linarith)
  have hA := sumIco_half_lt (show 1 ≤ p by omega)
  have hB := sumIco_half_lt (show 1 ≤ q by omega)
  have hA0 := sumIco_nonneg p (by norm_num : (0 : ℝ) ≤ 2⁻¹)
  have hg : (∑ i ∈ Ico 1 p, (2⁻¹ : ℝ) ^ i) * (∑ i ∈ Ico 1 q, (2⁻¹ : ℝ) ^ i) < 1 :=
    calc _ ≤ (∑ i ∈ Ico 1 p, (2⁻¹ : ℝ) ^ i) * 1 := mul_le_mul_of_nonneg_left hB.le hA0
      _ < 1 := by rw [mul_one]; exact hA
  have hlt : 2⁻¹ < τ⁻¹ := not_le.mp fun h => by
    have := rateFn_le hp hq hx.le h
    linarith
  exact (inv_lt_inv₀ (by norm_num) (by linarith)).1 hlt

/-- **The rates tend to 2**: for every `σ < 2`, all `(p, q)` with `p, q ≥ N` have rate `> σ`. -/
theorem rate_tendsto_two (σ : ℝ) (hσ : σ < 2) : ∃ N : ℕ, ∀ p q : ℕ, N ≤ p → N ≤ q →
    ∀ τ : ℝ, 1 < τ → (∑ i ∈ Ico 1 p, τ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, τ⁻¹ ^ i) = 1 → σ < τ := by
  rcases le_or_gt σ 1 with h1 | h1
  · exact ⟨0, fun p q _ _ τ hτ _ => lt_of_le_of_lt h1 hτ⟩
  have hσ0 : 0 < σ := by linarith
  have hy0 : 0 < σ⁻¹ := inv_pos.2 hσ0
  have hy1 : σ⁻¹ < 1 := (inv_lt_one₀ hσ0).2 h1
  have hhalf : (2 : ℝ)⁻¹ < σ⁻¹ := (inv_lt_inv₀ (by norm_num) hσ0).2 hσ
  have hy2 : 0 < 2 * σ⁻¹ - 1 := by linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hy2 hy1
  refine ⟨max N 2, fun p q hp hq τ hτ heq => ?_⟩
  have hS : ∀ m, max N 2 ≤ m → 1 < ∑ i ∈ Ico 1 m, σ⁻¹ ^ i := fun m hm => by
    have hNm : N ≤ m := le_trans (le_max_left _ _) hm
    have h2m : 2 ≤ m := le_trans (le_max_right _ _) hm
    have h := geom_sum_Ico_mul_neg σ⁻¹ (show 1 ≤ m by omega)
    have hym : σ⁻¹ ^ m ≤ σ⁻¹ ^ N := pow_le_pow_of_le_one hy0.le hy1.le hNm
    rw [pow_one] at h
    refine not_le.mp fun hc => ?_
    have h' : (∑ i ∈ Ico 1 m, σ⁻¹ ^ i) * (1 - σ⁻¹) ≤ 1 * (1 - σ⁻¹) :=
      mul_le_mul_of_nonneg_right hc (by linarith)
    linarith
  have hp2 : 2 ≤ p := le_trans (le_max_right _ _) hp
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hSp := hS p hp
  have hSq := hS q hq
  have hg : 1 < (∑ i ∈ Ico 1 p, σ⁻¹ ^ i) * (∑ i ∈ Ico 1 q, σ⁻¹ ^ i) :=
    calc (1 : ℝ) < ∑ i ∈ Ico 1 p, σ⁻¹ ^ i := hSp
      _ = (∑ i ∈ Ico 1 p, σ⁻¹ ^ i) * 1 := (mul_one _).symm
      _ < _ := mul_lt_mul_of_pos_left hSq (by linarith)
  have hx : 0 < τ⁻¹ := inv_pos.2 (by linarith)
  have hlt : τ⁻¹ < σ⁻¹ := not_le.mp fun h => by
    have := rateFn_le hp2 hq2 hy0.le h
    linarith
  exact (inv_lt_inv₀ (by linarith) hσ0).1 hlt

end CoxeterGrowth.Triangle
