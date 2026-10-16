module
public import Mathlib

@[expose] public section
/-!
# Triangle Coxeter groups `(p, q, ∞)`: normal-form combinatorics

Generators `a = 0`, `b = 1`, `c = 2`, with `m(a,c) = p`, `m(b,c) = q`, `m(a,b) = ∞`.
The group is the amalgam `D_p *_{⟨c⟩} D_q`.  A normal form is

  `c^ε · x₁ x₂ ⋯ x_k`

where the blocks `x_i` alternate between the alternating words `a c a ⋯` (length `1 … p−1`) and
`b c b ⋯` (length `1 … q−1`).  We encode it as a raw triple `((ε, j), r)`: `j < p` is the length
of a leading `a`-block (possibly `0`) and `r` is the list of lengths of the remaining blocks, which
start with a `b`-block.  The *head* `(ε, j)` is a coordinate on the dihedral group `D_p`; the left
action of `a` and `c` only moves the head (`da`, `dc`).  To act by `b` we re-read the normal form
with a `b`-head (`swap`), act on that head, and swap back.

This file contains everything that does not mention the Coxeter group: the head actions and the
dihedral relation `(da ∘ dc)^m = id` (proved through an explicit orbit coordinate `sig`), the raw
actions with their relations and length changes, and the counting of normal forms by length,
assembled into an identity of formal power series.
-/

namespace CoxeterGrowth.Triangle

open Finset PowerSeries

/-! ## Dihedral heads -/

/-- Left action of the non-`c` generator `s` of `D_m = ⟨s, c⟩` on heads
`(ε, j) ↔ c^ε · (s c s ⋯)` (`j` letters). -/
def da (m : ℕ) (x : ℕ × ℕ) : ℕ × ℕ :=
  if x.1 = 0 then
    (if x.2 = 0 then (0, 1) else if x.2 = 1 then (0, 0) else (1, x.2 - 2))
  else
    (if x.2 + 2 < m then (0, x.2 + 2) else (1, 2 * m - x.2 - 3))

/-- Left action of `c` on heads. -/
def dc (x : ℕ × ℕ) : ℕ × ℕ := (1 - x.1, x.2)

/-- Valid heads of `D_m`: `ε ≤ 1`, `j < m`. -/
abbrev HV (m : ℕ) (x : ℕ × ℕ) : Prop := x.1 ≤ 1 ∧ x.2 < m

/-- Length of a head. -/
def hl (x : ℕ × ℕ) : ℕ := x.1 + x.2

theorem HV_mk {m e j : ℕ} : HV m (e, j) ↔ e ≤ 1 ∧ j < m := Iff.rfl
theorem hl_mk {e j : ℕ} : hl (e, j) = e + j := rfl

theorem pair_eq {a b c d : ℕ} (h1 : a = c) (h2 : b = d) : (a, b) = (c, d) := by
  subst h1; subst h2; rfl

theorem da_00 (m : ℕ) : da m (0, 0) = (0, 1) := by simp [da]
theorem da_01 (m : ℕ) : da m (0, 1) = (0, 0) := by simp [da]
theorem da_0 (m j : ℕ) : da m (0, j + 2) = (1, j) := by simp [da]
theorem da_1_lt {m e j : ℕ} (h : j + 2 < m) : da m (e + 1, j) = (0, j + 2) := by simp [da, h]
theorem da_1_ge {m e j : ℕ} (h : ¬ j + 2 < m) : da m (e + 1, j) = (1, 2 * m - j - 3) := by
  simp [da, h]
theorem dc_0 (j : ℕ) : dc (0, j) = (1, j) := rfl
theorem dc_1 (e j : ℕ) : dc (e + 1, j) = (0, j) := by
  show (1 - (e + 1), j) = (0, j)
  rw [show 1 - (e + 1) = 0 by omega]

theorem da_HV {m : ℕ} (hm : 2 ≤ m) : ∀ x : ℕ × ℕ, HV m x → HV m (da m x)
  | (0, 0), _ => by rw [da_00, HV_mk]; omega
  | (0, 1), _ => by rw [da_01, HV_mk]; omega
  | (0, j + 2), hx => by rw [HV_mk] at hx; rw [da_0, HV_mk]; omega
  | (e + 1, j), hx => by
    rw [HV_mk] at hx
    by_cases h : j + 2 < m
    · rw [da_1_lt h, HV_mk]; omega
    · rw [da_1_ge h, HV_mk]; omega

theorem dc_HV {m : ℕ} (x : ℕ × ℕ) (hx : HV m x) : HV m (dc x) := by
  obtain ⟨e, j⟩ := x
  rw [HV_mk] at hx
  show 1 - e ≤ 1 ∧ j < m
  omega

theorem da_da {m : ℕ} (hm : 2 ≤ m) : ∀ x : ℕ × ℕ, HV m x → da m (da m x) = x
  | (0, 0), _ => by rw [da_00, da_01]
  | (0, 1), _ => by rw [da_01, da_00]
  | (0, j + 2), hx => by
    rw [HV_mk] at hx
    have h : j + 2 < m := by omega
    rw [da_0, da_1_lt h]
  | (e + 1, j), hx => by
    rw [HV_mk] at hx
    by_cases h : j + 2 < m
    · rw [da_1_lt h, da_0]
      exact pair_eq (by omega) rfl
    · have h2 : ¬ (2 * m - j - 3 + 2 < m) := by omega
      rw [da_1_ge h, da_1_ge h2]
      exact pair_eq (by omega) (by omega)

theorem dc_dc (x : ℕ × ℕ) (hx : x.1 ≤ 1) : dc (dc x) = x := by
  obtain ⟨e, j⟩ := x
  exact pair_eq (show 1 - (1 - e) = e by (try simp only at hx); omega) rfl

/-- Each head action changes the head length by exactly one. -/
theorem da_hl {m : ℕ} (hm : 2 ≤ m) : ∀ x : ℕ × ℕ, HV m x →
    (hl (da m x) + 1 = hl x ∨ hl (da m x) = hl x + 1)
  | (0, 0), _ => by rw [da_00]; simp only [hl_mk, or_true, true_or, false_or, or_false] <;> omega
  | (0, 1), _ => by rw [da_01]; simp only [hl_mk, or_true, true_or, false_or, or_false] <;> omega
  | (0, j + 2), _ => by rw [da_0]; simp only [hl_mk, or_true, true_or, false_or, or_false] <;> omega
  | (e + 1, j), hx => by
    rw [HV_mk] at hx
    by_cases h : j + 2 < m
    · rw [da_1_lt h]; simp only [hl_mk, or_true, true_or, false_or, or_false] <;> omega
    · rw [da_1_ge h]; simp only [hl_mk, or_true, true_or, false_or, or_false] <;> omega

theorem dc_hl (x : ℕ × ℕ) (hx : x.1 ≤ 1) : hl (dc x) + 1 = hl x ∨ hl (dc x) = hl x + 1 := by
  obtain ⟨e, j⟩ := x
  show (1 - e) + j + 1 = e + j ∨ (1 - e) + j = e + j + 1
  (try simp only at hx)
  omega

/-! ### The dihedral relation `(da ∘ dc)^m = id`, via an orbit coordinate -/

/-- Orbit coordinate: `T = da ∘ dc` acts on `sig` as `(o, s) ↦ (o, s + 1 mod m)`. -/
def sig (m : ℕ) : ℕ × ℕ → ℕ × ℕ
  | (e, j) =>
    if j % 2 = 1 then (if e = 0 then (1, (j - 1) / 2) else (0, m - (j + 1) / 2))
    else (if e = 0 then (0, j / 2) else (1, m - 1 - j / 2))

/-- The cyclic step. -/
def step (m : ℕ) : ℕ × ℕ → ℕ × ℕ
  | (o, s) => (o, if s + 1 = m then 0 else s + 1)

theorem sig_0_odd {m j : ℕ} (h : j % 2 = 1) : sig m (0, j) = (1, (j - 1) / 2) := by
  simp [sig, h]
theorem sig_0_even {m j : ℕ} (h : j % 2 = 0) : sig m (0, j) = (0, j / 2) := by
  simp [sig, h]
theorem sig_1_odd {m e j : ℕ} (h : j % 2 = 1) : sig m (e + 1, j) = (0, m - (j + 1) / 2) := by
  simp [sig, h]
theorem sig_1_even {m e j : ℕ} (h : j % 2 = 0) : sig m (e + 1, j) = (1, m - 1 - j / 2) := by
  simp [sig, h]
theorem step_ne {m o s : ℕ} (h : s + 1 ≠ m) : step m (o, s) = (o, s + 1) := by
  simp [step, h]
theorem step_eq {m o s : ℕ} (h : s + 1 = m) : step m (o, s) = (o, 0) := by
  simp [step, h]

theorem sig_T {m : ℕ} (hm : 2 ≤ m) : ∀ x : ℕ × ℕ, HV m x → sig m (da m (dc x)) = step m (sig m x)
  | (0, j), hx => by
    rw [HV_mk] at hx
    rw [dc_0]
    by_cases h : j + 2 < m
    · rw [da_1_lt h]
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj
      · rw [sig_0_even (show (j + 2) % 2 = 0 by omega), sig_0_even hj,
          step_ne (show j / 2 + 1 ≠ m by omega)]
        exact pair_eq rfl (by omega)
      · rw [sig_0_odd (show (j + 2) % 2 = 1 by omega), sig_0_odd hj,
          step_ne (show (j - 1) / 2 + 1 ≠ m by omega)]
        exact pair_eq rfl (by omega)
    · rw [da_1_ge h]
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj
      · rw [sig_1_odd (show (2 * m - j - 3) % 2 = 1 by omega), sig_0_even hj,
          step_ne (show j / 2 + 1 ≠ m by omega)]
        exact pair_eq rfl (by omega)
      · rw [sig_1_even (show (2 * m - j - 3) % 2 = 0 by omega), sig_0_odd hj,
          step_ne (show (j - 1) / 2 + 1 ≠ m by omega)]
        exact pair_eq rfl (by omega)
  | (e + 1, 0), hx => by
    rw [HV_mk] at hx
    rw [dc_1, da_00, sig_0_odd (show 1 % 2 = 1 by norm_num),
      sig_1_even (show 0 % 2 = 0 by norm_num), step_eq (show m - 1 - 0 / 2 + 1 = m by omega)]
    all_goals exact pair_eq rfl (by omega)
  | (e + 1, 1), hx => by
    rw [HV_mk] at hx
    rw [dc_1, da_01, sig_0_even (show 0 % 2 = 0 by norm_num),
      sig_1_odd (show 1 % 2 = 1 by norm_num), step_eq (show m - (1 + 1) / 2 + 1 = m by omega)]
    all_goals exact pair_eq rfl (by omega)
  | (e + 1, j + 2), hx => by
    rw [HV_mk] at hx
    rw [dc_1, da_0]
    rcases Nat.mod_two_eq_zero_or_one j with hj | hj
    · rw [sig_1_even hj, sig_1_even (show (j + 2) % 2 = 0 by omega),
        step_ne (show m - 1 - (j + 2) / 2 + 1 ≠ m by omega)]
      exact pair_eq rfl (by omega)
    · rw [sig_1_odd hj, sig_1_odd (show (j + 2) % 2 = 1 by omega),
        step_ne (show m - (j + 2 + 1) / 2 + 1 ≠ m by omega)]
      exact pair_eq rfl (by omega)

theorem sig_inj {m : ℕ} (hm : 2 ≤ m) :
    ∀ x y : ℕ × ℕ, HV m x → HV m y → sig m x = sig m y → x = y
  | (e, j), (e', j'), hx, hy, h => by
    rw [HV_mk] at hx hy
    simp only [sig] at h
    apply pair_eq
    · split_ifs at h <;> simp only [Prod.mk.injEq, true_and, and_true] at h <;> omega
    · split_ifs at h <;> simp only [Prod.mk.injEq, true_and, and_true] at h <;> omega

theorem sig_lt {m : ℕ} (hm : 2 ≤ m) : ∀ x : ℕ × ℕ, HV m x → (sig m x).2 < m
  | (e, j), hx => by
    rw [HV_mk] at hx
    simp only [sig]
    (try split_ifs) <;> (try simp only) <;> omega

theorem step_iter (m o s : ℕ) : ∀ n : ℕ, s + n < m → (step m)^[n] (o, s) = (o, s + n)
  | 0, _ => rfl
  | n + 1, h => by
    rw [Function.iterate_succ_apply', step_iter m o s n (by omega)]
    simp only [step]
    split_ifs <;> first | rfl | omega

theorem step_iter_self (m o s : ℕ) (hs : s < m) : (step m)^[m] (o, s) = (o, s) := by
  obtain ⟨k, hk⟩ : ∃ k, m = s + (1 + k) := ⟨m - 1 - s, by omega⟩
  have h1 : (step m)^[k] (o, s) = (o, m - 1) := by
    rw [step_iter m o s k (by omega)]; exact pair_eq rfl (by omega)
  have h2 : step m (o, m - 1) = (o, 0) := by
    simp only [step]; split_ifs <;> first | rfl | omega
  have h3 : (step m)^[s] (o, 0) = (o, s) := by
    rw [step_iter m o 0 s (by omega)]; exact pair_eq rfl (by omega)
  calc (step m)^[m] (o, s) = (step m)^[s + (1 + k)] (o, s) := by rw [← hk]
    _ = (o, s) := by
      rw [Function.iterate_add_apply, Function.iterate_add_apply, h1, Function.iterate_one, h2, h3]

theorem T_iter {m : ℕ} (hm : 2 ≤ m) (x : ℕ × ℕ) (hx : HV m x) : ∀ n : ℕ,
    HV m ((fun y => da m (dc y))^[n] x) ∧
      sig m ((fun y => da m (dc y))^[n] x) = (step m)^[n] (sig m x)
  | 0 => ⟨hx, rfl⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := T_iter hm x hx n
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact ⟨da_HV hm _ (dc_HV _ h1), (sig_T hm _ h1).trans (congrArg (step m) h2)⟩

/-- **The dihedral relation** on heads: `(s c)^m` acts trivially. -/
theorem T_pow {m : ℕ} (hm : 2 ≤ m) (x : ℕ × ℕ) (hx : HV m x) :
    (fun y => da m (dc y))^[m] x = x := by
  have hl' := sig_lt hm x hx
  apply sig_inj hm _ _ (T_iter hm x hx m).1 hx
  rw [(T_iter hm x hx m).2]
  generalize sig m x = y at hl' ⊢
  obtain ⟨o, s⟩ := y
  exact step_iter_self m o s hl'

/-! ## Raw normal forms -/

/-- Raw normal forms `((ε, j), r)`. -/
abbrev Raw := (ℕ × ℕ) × List ℕ

/-- Validity of a block list whose first block is bounded by `m₁`, the next by `m₂`, … -/
def VT : ℕ → ℕ → List ℕ → Prop
  | _, _, [] => True
  | m₁, m₂, k :: r => 0 < k ∧ k < m₁ ∧ VT m₂ m₁ r

theorem VT_nil {m₁ m₂ : ℕ} : VT m₁ m₂ [] ↔ True := Iff.rfl
theorem VT_cons {m₁ m₂ k : ℕ} {r : List ℕ} : VT m₁ m₂ (k :: r) ↔ 0 < k ∧ k < m₁ ∧ VT m₂ m₁ r :=
  Iff.rfl

/-- Validity of a raw normal form read with an `m₁`-head followed by `m₂, m₁, …` blocks. -/
abbrev V (m₁ m₂ : ℕ) (v : Raw) : Prop := HV m₁ v.1 ∧ VT m₂ m₁ v.2

theorem V_mk {m₁ m₂ e j : ℕ} {r : List ℕ} : V m₁ m₂ ((e, j), r) ↔ (e ≤ 1 ∧ j < m₁) ∧ VT m₂ m₁ r :=
  Iff.rfl

/-- Length (number of letters) of a normal form. -/
def len (v : Raw) : ℕ := v.1.1 + v.1.2 + v.2.sum

theorem len_mk {e j : ℕ} {r : List ℕ} : len ((e, j), r) = e + j + r.sum := rfl

/-- Re-read a normal form with a head of the other type. -/
def swap : Raw → Raw
  | ((e, 0), []) => ((e, 0), [])
  | ((e, 0), k :: r) => ((e, k), r)
  | ((e, j + 1), r) => ((e, 0), (j + 1) :: r)

theorem swap_V {m₁ m₂ : ℕ} (hm : 1 ≤ m₂) : ∀ v : Raw, V m₁ m₂ v → V m₂ m₁ (swap v)
  | ((e, 0), []), h => by
    rw [V_mk] at h
    show V m₂ m₁ ((e, 0), [])
    rw [V_mk]
    exact ⟨⟨h.1.1, by omega⟩, trivial⟩
  | ((e, 0), k :: r), h => by
    rw [V_mk, VT_cons] at h
    show V m₂ m₁ ((e, k), r)
    rw [V_mk]
    exact ⟨⟨h.1.1, h.2.2.1⟩, h.2.2.2⟩
  | ((e, j + 1), r), h => by
    rw [V_mk] at h
    show V m₂ m₁ ((e, 0), (j + 1) :: r)
    rw [V_mk, VT_cons]
    exact ⟨⟨h.1.1, by omega⟩, by omega, h.1.2, h.2⟩

theorem swap_swap {m₁ m₂ : ℕ} : ∀ v : Raw, V m₁ m₂ v → swap (swap v) = v
  | ((e, 0), []), _ => rfl
  | ((e, 0), k :: r), h => by
    rw [V_mk, VT_cons] at h
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rfl
  | ((e, j + 1), r), _ => rfl

theorem len_swap : ∀ v : Raw, len (swap v) = len v
  | ((e, 0), []) => rfl
  | ((e, 0), k :: r) => by simp only [swap, len_mk, List.sum_cons] <;> omega
  | ((e, j + 1), r) => by simp only [swap, len_mk, List.sum_cons] <;> omega

/-- `a`/`b` (head generator) acting on the head. -/
def actH (m : ℕ) (v : Raw) : Raw := (da m v.1, v.2)
/-- `c` acting on the head. -/
def actC (v : Raw) : Raw := (dc v.1, v.2)
/-- The other head generator: swap, act, swap back. -/
def actB (m : ℕ) (v : Raw) : Raw := swap (actH m (swap v))

/-- The left action of the three generators on raw normal forms. -/
def act (p q : ℕ) : Fin 3 → Raw → Raw
  | 0 => actH p
  | 1 => actB q
  | 2 => actC

theorem swap_actC : ∀ v : Raw, swap (actC v) = actC (swap v)
  | ((e, 0), []) => rfl
  | ((e, 0), k :: r) => rfl
  | ((e, j + 1), r) => rfl

theorem actH_V {m₁ m₂ : ℕ} (hm : 2 ≤ m₁) (v : Raw) (h : V m₁ m₂ v) : V m₁ m₂ (actH m₁ v) :=
  ⟨da_HV hm v.1 h.1, h.2⟩

theorem actC_V {m₁ m₂ : ℕ} (v : Raw) (h : V m₁ m₂ v) : V m₁ m₂ (actC v) :=
  ⟨dc_HV v.1 h.1, h.2⟩

theorem actB_V {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (v : Raw) (h : V p q v) :
    V p q (actB q v) :=
  swap_V (by omega) _ (actH_V hq _ (swap_V (by omega) v h))

theorem act_V {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (i : Fin 3) (v : Raw) (h : V p q v) :
    V p q (act p q i v) := by
  match i with
  | 0 => exact actH_V hp v h
  | 1 => exact actB_V hp hq v h
  | 2 => exact actC_V v h

theorem actH_actH {m₁ m₂ : ℕ} (hm : 2 ≤ m₁) (v : Raw) (h : V m₁ m₂ v) : actH m₁ (actH m₁ v) = v := by
  obtain ⟨x, r⟩ := v
  show (da m₁ (da m₁ x), r) = (x, r)
  rw [da_da hm x h.1]

theorem actC_actC {m₁ m₂ : ℕ} (v : Raw) (h : V m₁ m₂ v) : actC (actC v) = v := by
  obtain ⟨x, r⟩ := v
  show (dc (dc x), r) = (x, r)
  rw [dc_dc x h.1.1]

theorem actB_actB {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (v : Raw) (h : V p q v) :
    actB q (actB q v) = v := by
  have h1 : V q p (swap v) := swap_V (by omega) v h
  have h2 : V q p (actH q (swap v)) := actH_V hq _ h1
  unfold actB
  rw [swap_swap _ h2, actH_actH hq _ h1, swap_swap _ h]

theorem act_act {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (i : Fin 3) (v : Raw) (h : V p q v) :
    act p q i (act p q i v) = v := by
  match i with
  | 0 => exact actH_actH hp v h
  | 1 => exact actB_actB hp hq v h
  | 2 => exact actC_actC v h

/-! ### Length changes -/

theorem len_actH {m₁ m₂ : ℕ} (hm : 2 ≤ m₁) (v : Raw) (h : V m₁ m₂ v) :
    len (actH m₁ v) + 1 = len v ∨ len (actH m₁ v) = len v + 1 := by
  obtain ⟨⟨e, j⟩, r⟩ := v
  have := da_hl hm (e, j) h.1
  show len (da m₁ (e, j), r) + 1 = len ((e, j), r) ∨ len (da m₁ (e, j), r) = len ((e, j), r) + 1
  generalize da m₁ (e, j) = y at this ⊢
  obtain ⟨y1, y2⟩ := y
  simp only [hl_mk] at this
  simp only [len_mk]
  omega

theorem len_actC {m₁ m₂ : ℕ} (v : Raw) (h : V m₁ m₂ v) :
    len (actC v) + 1 = len v ∨ len (actC v) = len v + 1 := by
  obtain ⟨⟨e, j⟩, r⟩ := v
  have := dc_hl (e, j) h.1.1
  show len (dc (e, j), r) + 1 = len ((e, j), r) ∨ len (dc (e, j), r) = len ((e, j), r) + 1
  generalize dc (e, j) = y at this ⊢
  obtain ⟨y1, y2⟩ := y
  simp only [hl_mk] at this
  simp only [len_mk]
  omega

theorem len_act {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (i : Fin 3) (v : Raw) (h : V p q v) :
    len (act p q i v) + 1 = len v ∨ len (act p q i v) = len v + 1 := by
  match i with
  | 0 => exact len_actH hp v h
  | 1 =>
    show len (swap (actH q (swap v))) + 1 = len v ∨ len (swap (actH q (swap v))) = len v + 1
    rw [len_swap, ← len_swap v]
    exact len_actH hq _ (swap_V (by omega) v h)
  | 2 => exact len_actC v h

theorem len_act_le {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (i : Fin 3) (v : Raw) (h : V p q v) :
    len (act p q i v) ≤ len v + 1 := by
  have := len_act hp hq i v h; omega

/-- The only normal form of length `0` is the empty one. -/
theorem eq_nil_of_len {p q : ℕ} (v : Raw) (h : V p q v) (hl0 : len v = 0) : v = ((0, 0), []) := by
  obtain ⟨⟨e, j⟩, r⟩ := v
  rw [len_mk] at hl0
  cases r with
  | nil => exact Prod.ext (pair_eq (by omega) (by omega)) rfl
  | cons k r =>
    rw [V_mk, VT_cons] at h
    simp only [List.sum_cons] at hl0
    omega

/-- **Descent**: a nonempty normal form has a generator shortening it by one. -/
theorem descent {p q : ℕ} :
    ∀ v : Raw, V p q v → len v ≠ 0 → ∃ i : Fin 3, len (act p q i v) + 1 = len v
  | ((0, 0), []), _, hl0 => (hl0 rfl).elim
  | ((0, 0), 0 :: r), h, _ => by rw [V_mk, VT_cons] at h; omega
  | ((0, 0), 1 :: r), _, _ => ⟨1, by
      show len (swap (actH q ((0, 1), r))) + 1 = len ((0, 0), 1 :: r)
      rw [len_swap]
      show len (da q (0, 1), r) + 1 = len ((0, 0), 1 :: r)
      rw [da_01]; simp only [len_mk, List.sum_cons] <;> omega⟩
  | ((0, 0), (k + 2) :: r), _, _ => ⟨1, by
      show len (swap (actH q ((0, k + 2), r))) + 1 = len ((0, 0), (k + 2) :: r)
      rw [len_swap]
      show len (da q (0, k + 2), r) + 1 = len ((0, 0), (k + 2) :: r)
      rw [da_0]; simp only [len_mk, List.sum_cons] <;> omega⟩
  | ((0, 1), r), _, _ => ⟨0, by
      show len (da p (0, 1), r) + 1 = len ((0, 1), r)
      rw [da_01]; simp only [len_mk] <;> omega⟩
  | ((0, j + 2), r), _, _ => ⟨0, by
      show len (da p (0, j + 2), r) + 1 = len ((0, j + 2), r)
      rw [da_0]; simp only [len_mk] <;> omega⟩
  | ((e + 1, j), r), h, _ => ⟨2, by
      rw [V_mk] at h
      show len (dc (e + 1, j), r) + 1 = len ((e + 1, j), r)
      rw [dc_1]; simp only [len_mk] <;> omega⟩

/-! ### The Coxeter relations on raw normal forms -/

theorem iter_actH_actC (m : ℕ) (v : Raw) : ∀ n : ℕ,
    (fun u => actH m (actC u))^[n] v = ((fun y => da m (dc y))^[n] v.1, v.2)
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iter_actH_actC m v n]
    rfl

theorem rel_ac {p q : ℕ} (hp : 2 ≤ p) (v : Raw) (h : V p q v) :
    (fun u => act p q 0 (act p q 2 u))^[p] v = v := by
  show (fun u => actH p (actC u))^[p] v = v
  rw [iter_actH_actC, T_pow hp v.1 h.1]

theorem iter_actHC_V {m₁ m₂ : ℕ} (hm : 2 ≤ m₁) (v : Raw) (h : V m₁ m₂ v) : ∀ n : ℕ,
    V m₁ m₂ ((fun u => actH m₁ (actC u))^[n] v)
  | 0 => h
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact actH_V hm _ (actC_V _ (iter_actHC_V hm v h n))

theorem iter_bc {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (v : Raw) (h : V p q v) : ∀ n : ℕ,
    (fun u => act p q 1 (act p q 2 u))^[n] v =
      swap ((fun u => actH q (actC u))^[n] (swap v))
  | 0 => (swap_swap v h).symm
  | n + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iter_bc hp hq v h n]
    have hY := iter_actHC_V hq (swap v) (swap_V (by omega) v h) n
    show swap (actH q (swap (actC (swap _)))) = _
    rw [swap_actC, swap_swap _ hY]

theorem rel_bc {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (v : Raw) (h : V p q v) :
    (fun u => act p q 1 (act p q 2 u))^[q] v = v := by
  have h1 : V q p (swap v) := swap_V (by omega) v h
  rw [iter_bc hp hq v h q, iter_actH_actC, T_pow hq _ h1.1]
  exact swap_swap v h

/-! ## Counting normal forms -/

theorem mem_ite_empty {α : Type*} {x : α} {P : Prop} [Decidable P] {s : Finset α} :
    x ∈ (if P then s else ∅) ↔ P ∧ x ∈ s := by
  split_ifs with h <;> simp [h]

/-- Block lists of total length `n` whose blocks are bounded alternately by `m₁, m₂, m₁, …`. -/
def tails (m₁ m₂ n : ℕ) : Finset (List ℕ) :=
  (if n = 0 then {[]} else ∅) ∪
    (range (n + 1)).biUnion fun k =>
      if h : 0 < k ∧ k ≤ n ∧ k < m₁ then (tails m₂ m₁ (n - k)).image (List.cons k) else ∅
termination_by n
decreasing_by omega

theorem tails_eq (m₁ m₂ n : ℕ) : tails m₁ m₂ n = (if n = 0 then {[]} else ∅) ∪
    (range (n + 1)).biUnion fun k =>
      if 0 < k ∧ k ≤ n ∧ k < m₁ then (tails m₂ m₁ (n - k)).image (List.cons k) else ∅ := by
  rw [tails]; simp only [dite_eq_ite]

theorem mem_tails (n : ℕ) : ∀ (m₁ m₂ : ℕ) (r : List ℕ),
    r ∈ tails m₁ m₂ n ↔ VT m₁ m₂ r ∧ r.sum = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m₁ m₂ r
    rw [tails_eq, mem_union, mem_ite_empty, mem_biUnion]
    constructor
    · rintro (⟨hn, hr⟩ | ⟨k, hk, hr⟩)
      · rw [mem_singleton] at hr
        subst hr
        exact ⟨trivial, by simp [hn]⟩
      · rw [mem_ite_empty, mem_image] at hr
        obtain ⟨⟨hk0, hkn, hkm⟩, r', hr', rfl⟩ := hr
        rw [ih (n - k) (by omega)] at hr'
        refine ⟨⟨hk0, hkm, hr'.1⟩, ?_⟩
        rw [List.sum_cons, hr'.2]; omega
    · rintro ⟨hv, hs⟩
      cases r with
      | nil =>
        left
        exact ⟨by simp at hs; omega, mem_singleton_self _⟩
      | cons k r' =>
        right
        rw [VT_cons] at hv
        rw [List.sum_cons] at hs
        refine ⟨k, mem_range.2 (by omega), ?_⟩
        rw [mem_ite_empty, mem_image]
        exact ⟨⟨hv.1, by omega, hv.2.1⟩, r', (ih (n - k) (by omega) m₂ m₁ r').2 ⟨hv.2.2, by omega⟩,
          rfl⟩

theorem card_biUnion_ite {α : Type*} [DecidableEq α] (s : Finset ℕ) (P : ℕ → Prop)
    [DecidablePred P] (T : ℕ → Finset α) (key : α → ℕ)
    (hkey : ∀ k, P k → ∀ x ∈ T k, key x = k) :
    (s.biUnion fun k => if P k then T k else ∅).card =
      ∑ k ∈ s, if P k then (T k).card else 0 := by
  rw [card_biUnion]
  · exact sum_congr rfl fun k _ => by split_ifs <;> simp
  · intro k _ k' _ hkk'
    show Disjoint (if P k then T k else ∅) (if P k' then T k' else ∅)
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [mem_ite_empty] at hx hx'
    exact hkk' ((hkey k hx.1 x hx.2).symm.trans (hkey k' hx'.1 x hx'.2))

theorem tails_card (m₁ m₂ n : ℕ) : ((tails m₁ m₂ n).card : ℤ) =
    (if n = 0 then 1 else 0) +
      ∑ k ∈ range (n + 1),
        (if 0 < k ∧ k < m₁ then (1 : ℤ) else 0) * ((tails m₂ m₁ (n - k)).card : ℤ) := by
  rw [tails_eq, card_union_of_disjoint]
  · rw [card_biUnion_ite _ (fun k => 0 < k ∧ k ≤ n ∧ k < m₁) _ (fun x => x.headI)]
    · push_cast
      congr 1
      · split_ifs <;> simp
      · refine sum_congr rfl fun k hk => ?_
        rw [mem_range] at hk
        split_ifs <;> first | omega | simp [card_image_of_injective _ List.cons_injective]
    · intro k _ x hx
      rw [mem_image] at hx
      obtain ⟨r, -, rfl⟩ := hx
      rfl
  · rw [Finset.disjoint_left]
    intro x hx hx'
    rw [mem_ite_empty, mem_singleton] at hx
    rw [mem_biUnion] at hx'
    obtain ⟨k, -, hk⟩ := hx'
    rw [mem_ite_empty, mem_image] at hk
    obtain ⟨-, r, -, rfl⟩ := hk
    exact List.cons_ne_nil _ _ hx.2

/-- Headed sequences `(j, r)`: a leading `a`-block of length `j < p` (possibly empty) followed by
a block list starting with a `b`-block. -/
def Hs (p q n : ℕ) : Finset (ℕ × List ℕ) :=
  (range (n + 1)).biUnion fun k =>
    if k < p then (tails q p (n - k)).image (fun r => (k, r)) else ∅

/-- All raw normal forms of length `n`. -/
def NFs (p q n : ℕ) : Finset Raw :=
  (range (n + 1)).biUnion fun e =>
    if e ≤ 1 then (Hs p q (n - e)).image (fun x => ((e, x.1), x.2)) else ∅

theorem mem_Hs (p q n j : ℕ) (r : List ℕ) :
    (j, r) ∈ Hs p q n ↔ j < p ∧ VT q p r ∧ j + r.sum = n := by
  rw [Hs, mem_biUnion]
  constructor
  · rintro ⟨k, hk, hx⟩
    rw [mem_ite_empty, mem_image] at hx
    obtain ⟨hkp, r', hr', he⟩ := hx
    rw [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [mem_tails] at hr'
    rw [mem_range] at hk
    exact ⟨hkp, hr'.1, by omega⟩
  · rintro ⟨hj, hr, hs⟩
    refine ⟨j, mem_range.2 (by omega), ?_⟩
    rw [mem_ite_empty, mem_image]
    exact ⟨hj, r, (mem_tails _ _ _ _).2 ⟨hr, by omega⟩, rfl⟩

theorem mem_NFs (p q n : ℕ) (v : Raw) : v ∈ NFs p q n ↔ V p q v ∧ len v = n := by
  obtain ⟨⟨e, j⟩, r⟩ := v
  rw [NFs, mem_biUnion, V_mk, len_mk]
  constructor
  · rintro ⟨k, hk, hx⟩
    rw [mem_ite_empty, mem_image] at hx
    obtain ⟨hk1, ⟨j', r'⟩, hx, he⟩ := hx
    simp only [Prod.mk.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
    rw [mem_Hs] at hx
    rw [mem_range] at hk
    exact ⟨⟨⟨hk1, hx.1⟩, hx.2.1⟩, by omega⟩
  · rintro ⟨⟨⟨he, hj⟩, hr⟩, hs⟩
    refine ⟨e, mem_range.2 (by omega), ?_⟩
    rw [mem_ite_empty, mem_image]
    exact ⟨he, (j, r), (mem_Hs _ _ _ _ _).2 ⟨hj, hr, by omega⟩, rfl⟩

theorem card_Hs (p q n : ℕ) : ((Hs p q n).card : ℤ) =
    ∑ k ∈ range (n + 1), (if k < p then (1 : ℤ) else 0) * ((tails q p (n - k)).card : ℤ) := by
  rw [Hs, card_biUnion_ite _ (fun k => k < p) _ Prod.fst]
  · push_cast
    refine sum_congr rfl fun k _ => ?_
    have hinj : Function.Injective (fun r : List ℕ => (k, r)) := fun _ _ h => (Prod.mk.inj h).2
    split_ifs <;> simp [card_image_of_injective _ hinj]
  · intro k _ x hx
    rw [mem_image] at hx
    obtain ⟨r, -, rfl⟩ := hx
    rfl

theorem card_NFs (p q n : ℕ) : ((NFs p q n).card : ℤ) =
    ∑ k ∈ range (n + 1), (if k ≤ 1 then (1 : ℤ) else 0) * ((Hs p q (n - k)).card : ℤ) := by
  rw [NFs, card_biUnion_ite _ (fun k => k ≤ 1) _ (fun v => v.1.1)]
  · push_cast
    refine sum_congr rfl fun k _ => ?_
    have hinj : Function.Injective (fun x : ℕ × List ℕ => ((k, x.1), x.2)) := by
      intro x y h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1.2 h.2
    split_ifs <;> simp [card_image_of_injective _ hinj]
  · intro k _ x hx
    rw [mem_image] at hx
    obtain ⟨y, -, rfl⟩ := hx
    rfl

/-! ### Generating functions -/

theorem coeff_mk_mul_mk (f g : ℕ → ℤ) (n : ℕ) :
    coeff n (mk f * mk g) = ∑ k ∈ range (n + 1), f k * g (n - k) := by
  rw [coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => coeff a (mk f) * coeff b (mk g))]
  simp only [coeff_mk, Nat.succ_eq_add_one]

/-- `X + X² + ⋯ + X^{m-1}`, coefficientwise. -/
def Pm (m : ℕ) : ℤ⟦X⟧ := mk fun k => if 0 < k ∧ k < m then 1 else 0
/-- `1 + X + ⋯ + X^{m-1}`, coefficientwise. -/
def Rm (m : ℕ) : ℤ⟦X⟧ := mk fun k => if k < m then 1 else 0
/-- `1 + X`, coefficientwise. -/
def E2 : ℤ⟦X⟧ := mk fun k => if k ≤ 1 then 1 else 0
/-- The generating function of a counting sequence. -/
def ser (f : ℕ → ℕ) : ℤ⟦X⟧ := mk fun n => (f n : ℤ)

theorem tails_series (m₁ m₂ : ℕ) :
    ser (fun n => (tails m₁ m₂ n).card) = 1 + Pm m₁ * ser (fun n => (tails m₂ m₁ n).card) := by
  ext n
  simp only [ser, Pm, map_add, coeff_one, coeff_mk_mul_mk, coeff_mk]
  exact tails_card m₁ m₂ n

theorem Hs_series (p q : ℕ) :
    ser (fun n => (Hs p q n).card) = Rm p * ser (fun n => (tails q p n).card) := by
  ext n
  simp only [ser, Rm, coeff_mk_mul_mk, coeff_mk]
  exact card_Hs p q n

theorem NFs_series (p q : ℕ) :
    ser (fun n => (NFs p q n).card) = E2 * ser (fun n => (Hs p q n).card) := by
  ext n
  simp only [ser, E2, coeff_mk_mul_mk, coeff_mk]
  exact card_NFs p q n

theorem Rm_eq (m : ℕ) (hm : 1 ≤ m) : Rm m = 1 + Pm m := by
  ext n
  simp only [Rm, Pm, map_add, coeff_one, coeff_mk]
  split_ifs <;> omega

/-- **The series identity for normal forms**:
`(Σ #NF_n Xⁿ) · (1 − P_p P_q) = (1 + X) [p] [q]`. -/
theorem nf_series (p q : ℕ) (hq : 1 ≤ q) :
    ser (fun n => (NFs p q n).card) * (1 - Pm p * Pm q) = E2 * Rm p * Rm q := by
  have hA := tails_series p q
  have hB := tails_series q p
  rw [NFs_series, Hs_series, Rm_eq q hq]
  linear_combination (E2 * Rm p) * hB + (E2 * Rm p * Pm q) * hA

theorem sum_Ico_X_pow (m : ℕ) : ∑ i ∈ Ico 1 m, (X : ℤ⟦X⟧) ^ i = Pm m := by
  ext n
  rw [map_sum]
  simp only [coeff_X_pow, Pm, coeff_mk]
  rw [sum_ite_eq]
  simp only [mem_Ico]
  split_ifs <;> omega

theorem sum_range_X_pow (m : ℕ) : ∑ i ∈ range m, (X : ℤ⟦X⟧) ^ i = Rm m := by
  ext n
  rw [map_sum]
  simp only [coeff_X_pow, Rm, coeff_mk]
  rw [sum_ite_eq]
  simp only [mem_range]

theorem one_add_X_eq : (1 + X : ℤ⟦X⟧) = E2 := by
  ext n
  simp only [map_add, coeff_one, coeff_X, E2, coeff_mk]
  split_ifs <;> omega

/-- The normal-form series identity in closed form. -/
theorem nf_series' (p q : ℕ) (hq : 1 ≤ q) :
    ser (fun n => (NFs p q n).card) *
        (1 - (∑ i ∈ Ico 1 p, (X : ℤ⟦X⟧) ^ i) * (∑ i ∈ Ico 1 q, (X : ℤ⟦X⟧) ^ i)) =
      (1 + X) * (∑ i ∈ range p, (X : ℤ⟦X⟧) ^ i) * (∑ i ∈ range q, (X : ℤ⟦X⟧) ^ i) := by
  rw [sum_Ico_X_pow, sum_Ico_X_pow, sum_range_X_pow, sum_range_X_pow, one_add_X_eq]
  exact nf_series p q hq

end CoxeterGrowth.Triangle
