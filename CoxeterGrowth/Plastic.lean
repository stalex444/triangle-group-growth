module
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

@[expose] public section
/-!
# The plastic number

`plasticNumber` is the unique real root `> 1` of `x³ − x − 1`.  Existence is the intermediate
value theorem on `[1, 2]` (the cubic is `−1` at `1` and `5` at `2`); uniqueness holds because
`x³ − x` is strictly increasing on `[1, ∞)` (in fact the cubic has no other real root at all,
`plasticNumber_unique'`).
-/

namespace CoxeterGrowth

theorem exists_plastic_root : ∃ x ∈ Set.Icc (1 : ℝ) 2, x ^ 3 - x - 1 = 0 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3 - x - 1) (Set.Icc 1 2) := by fun_prop
  have h := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hcont
  have h0 : (0 : ℝ) ∈ Set.Icc ((1 : ℝ) ^ 3 - 1 - 1) ((2 : ℝ) ^ 3 - 2 - 1) := by
    constructor <;> norm_num
  obtain ⟨x, hx, hfx⟩ := h h0
  exact ⟨x, hx, hfx⟩

/-- The plastic number: the real root `> 1` of `x³ − x − 1`. -/
noncomputable def plasticNumber : ℝ := Classical.choose exists_plastic_root

theorem plasticNumber_mem : plasticNumber ∈ Set.Icc (1 : ℝ) 2 :=
  (Classical.choose_spec exists_plastic_root).1

theorem plasticNumber_cubic : plasticNumber ^ 3 = plasticNumber + 1 := by
  have h := (Classical.choose_spec exists_plastic_root).2
  have : plasticNumber ^ 3 - plasticNumber - 1 = 0 := h
  linarith

theorem one_lt_plasticNumber : 1 < plasticNumber := by
  have h1 := plasticNumber_mem.1
  have h3 := plasticNumber_cubic
  rcases h1.lt_or_eq with h | h
  · exact h
  · rw [← h] at h3; norm_num at h3

/-- Uniqueness among roots `> 1`. -/
theorem plasticNumber_unique {x : ℝ} (hx : 1 < x) (h : x ^ 3 = x + 1) : x = plasticNumber := by
  have hρ := one_lt_plasticNumber
  have h3 := plasticNumber_cubic
  have key : (x - plasticNumber) * (x ^ 2 + x * plasticNumber + plasticNumber ^ 2 - 1) = 0 := by
    have : (x - plasticNumber) * (x ^ 2 + x * plasticNumber + plasticNumber ^ 2 - 1)
        = (x ^ 3 - x) - (plasticNumber ^ 3 - plasticNumber) := by ring
    rw [this, h, h3]; ring
  rcases mul_eq_zero.1 key with h' | h'
  · linarith
  · nlinarith

/-- Every real root of `x³ − x − 1` exceeds `1`. -/
theorem one_lt_of_cubic {x : ℝ} (h : x ^ 3 = x + 1) : 1 < x := by
  by_contra hle
  rw [not_lt] at hle
  rcases le_or_gt x 0 with h0 | h0
  · rcases le_or_gt x (-1) with h1 | h1
    · nlinarith [sq_nonneg x, mul_nonneg (sub_nonneg.2 h1) (sq_nonneg x)]
    · -- `x ∈ (-1, 0]`: `x³ − x = (-x)(1 − x²) ≤ -x < 1`
      nlinarith [mul_nonneg (neg_nonneg.2 h0) (sq_nonneg x)]
  · nlinarith [mul_pos h0 h0, mul_nonneg h0.le (sub_nonneg.2 hle)]

/-- The cubic `x³ − x − 1` has exactly one real root. -/
theorem plasticNumber_unique' {x : ℝ} (h : x ^ 3 = x + 1) : x = plasticNumber :=
  plasticNumber_unique (one_lt_of_cubic h) h

end CoxeterGrowth
