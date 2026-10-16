module
public import Mathlib
public import CoxeterGrowth.Plastic

@[expose] public section
/-!
# Growth of the (2,3,∞) Coxeter group  (≅ PGL(2,ℤ); for the cited billiard application see README)

Generators `a b c` with `m(a,c) = 2`, `m(b,c) = 3`, `m(a,b) = ∞`.
Sphere sizes `a(n) = #{w : ℓ(w) = n}` satisfy `a(0..4) = 1,3,5,7,9` and
`a(n) = a(n-2) + a(n-3)` for `n ≥ 5`; hence `a(n) = Θ(ρⁿ)`, ρ the plastic number.

Method: the amalgam `⟨a,c⟩ *_{⟨c⟩} ⟨b,c⟩` has the left normal form
`y₁ ⋯ y_k · c^ε`, `y_i` alternating between `a` and `{b, cb}`.  We realise these normal
forms as a concrete set `NF` of lists, define the left action of each generator on `NF`,
check the Coxeter relations for that action, and lift it to `W` by the universal property.
The orbit map `W → NF` is then a bijection under which `ℓ` is the list length, because each
generator changes the normal-form length by exactly one.  Counting is a 3-state automaton.
-/

set_option linter.unusedSimpArgs false

namespace CoxeterGrowth.TwoThreeInf

inductive L | a | b | c
  deriving DecidableEq, Repr

inductive St | start | afterA | afterB
  deriving DecidableEq, Repr

open L St

def canA : St → Bool
  | start => true
  | afterA => false
  | afterB => true

def canB : St → Bool
  | start => true
  | afterA => true
  | afterB => false

/-- Normal forms: syllables alternating between `a` and `{b, cb}`, then `[]` or `[c]`. -/
def Valid : St → List L → Bool
  | _, [] => true
  | st, a :: r => canA st && Valid afterA r
  | st, b :: r => canB st && Valid afterB r
  | _, [c] => true
  | _, c :: a :: _ => false
  | st, c :: b :: r => canB st && Valid afterB r
  | _, c :: c :: _ => false

/-- Left multiplication by `c`. -/
def pushC : List L → List L
  | [] => [c]
  | a :: r => a :: pushC r
  | b :: r => c :: b :: r
  | [c] => []
  | c :: a :: r => c :: a :: r
  | c :: b :: r => b :: r
  | c :: c :: r => c :: c :: r

/-- Left multiplication by `a`. -/
def actA : List L → List L
  | a :: r => r
  | [] => [a]
  | b :: r => a :: b :: r
  | c :: r => a :: c :: r

/-- Left multiplication by `b`. -/
def actB : List L → List L
  | b :: r => r
  | c :: b :: r => c :: b :: pushC r
  | [] => [b]
  | a :: r => b :: a :: r
  | [c] => [b, c]
  | c :: a :: r => b :: c :: a :: r
  | c :: c :: r => b :: c :: c :: r

def act : L → List L → List L
  | a => actA
  | b => actB
  | c => pushC

/-! ### Validity lemmas -/

theorem valid_start_of_valid {st : St} {w : List L} (h : Valid st w = true) :
    Valid start w = true := by
  cases w with
  | nil => rfl
  | cons x r =>
    cases x with
    | a => simp_all [Valid, canA]
    | b => simp_all [Valid, canB]
    | c =>
      cases r with
      | nil => rfl
      | cons y r' => cases y <;> simp_all [Valid, canB]

theorem valid_tail {x : L} {r : List L} (h : Valid start (x :: r) = true) :
    Valid start r = true := by
  cases x with
  | a => simp [Valid, canA] at h; exact valid_start_of_valid h
  | b => simp [Valid, canB] at h; exact valid_start_of_valid h
  | c =>
    cases r with
    | nil => rfl
    | cons y r' => cases y <;> simp_all [Valid, canB]

/-- The defining property of a normal form: consing a letter is the group action. -/
theorem act_cons_of_valid {x : L} {r : List L} (h : Valid start (x :: r) = true) :
    act x r = x :: r := by
  cases x with
  | a =>
    cases r with
    | nil => rfl
    | cons y r' => cases y <;> simp_all [Valid, canA, act, actA]
  | b =>
    cases r with
    | nil => rfl
    | cons y r' =>
      cases y with
      | a => rfl
      | b => simp_all [Valid, canB]
      | c =>
        cases r' with
        | nil => rfl
        | cons z r'' => cases z <;> simp_all [Valid, canB]
  | c =>
    cases r with
    | nil => rfl
    | cons y r' => cases y <;> simp_all [Valid, canB, act, pushC]

theorem pushC_valid : ∀ (st : St) (w : List L), Valid st w = true → Valid st (pushC w) = true
  | st, [], _ => by simp [pushC, Valid]
  | st, a :: r, h => by
    simp only [Valid, Bool.and_eq_true] at h
    simp only [pushC, Valid, Bool.and_eq_true]
    exact ⟨h.1, pushC_valid afterA r h.2⟩
  | st, b :: r, h => by simpa [pushC, Valid] using h
  | st, [c], _ => by simp [pushC, Valid]
  | st, c :: a :: r, h => by simp [Valid] at h
  | st, c :: b :: r, h => by simpa [pushC, Valid] using h
  | st, c :: c :: r, h => by simp [Valid] at h

theorem actA_valid {w : List L} (h : Valid start w = true) : Valid start (actA w) = true := by
  cases w with
  | nil => rfl
  | cons x r =>
    cases x with
    | a => simp [Valid, canA] at h; exact valid_start_of_valid h
    | b => simpa [actA, Valid, canA, canB] using h
    | c =>
      cases r with
      | nil => rfl
      | cons y r' => cases y <;> simp_all [actA, Valid, canA, canB]

theorem actB_valid {w : List L} (h : Valid start w = true) : Valid start (actB w) = true := by
  cases w with
  | nil => rfl
  | cons x r =>
    cases x with
    | a => simpa [actB, Valid, canA, canB] using h
    | b => simp [Valid, canB] at h; exact valid_start_of_valid h
    | c =>
      cases r with
      | nil => rfl
      | cons y r' =>
        cases y with
        | a => simp [Valid] at h
        | b =>
          simp only [Valid, canB, Bool.true_and] at h
          simpa [actB, Valid, canB] using pushC_valid afterB r' h
        | c => simp [Valid] at h

theorem act_valid (x : L) {w : List L} (h : Valid start w = true) :
    Valid start (act x w) = true := by
  cases x with
  | a => exact actA_valid h
  | b => exact actB_valid h
  | c => exact pushC_valid start w h

/-! ### Length changes by exactly one -/

theorem pushC_length : ∀ (st : St) (w : List L), Valid st w = true →
    (pushC w).length = w.length + 1 ∨ (pushC w).length + 1 = w.length
  | st, [], _ => by simp [pushC]
  | st, a :: r, h => by
    simp only [Valid, Bool.and_eq_true] at h
    have := pushC_length afterA r h.2
    simp only [pushC, List.length_cons]
    omega
  | st, b :: r, h => by simp [pushC]
  | st, [c], _ => by simp [pushC]
  | st, c :: a :: r, h => by simp [Valid] at h
  | st, c :: b :: r, h => by simp [pushC]
  | st, c :: c :: r, h => by simp [Valid] at h

theorem actA_length {w : List L} (_h : Valid start w = true) :
    (actA w).length = w.length + 1 ∨ (actA w).length + 1 = w.length := by
  cases w with
  | nil => simp [actA]
  | cons x r => cases x <;> simp [actA]

theorem actB_length {w : List L} (h : Valid start w = true) :
    (actB w).length = w.length + 1 ∨ (actB w).length + 1 = w.length := by
  cases w with
  | nil => simp [actB]
  | cons x r =>
    cases x with
    | a => simp [actB]
    | b => simp [actB]
    | c =>
      cases r with
      | nil => simp [actB]
      | cons y r' =>
        cases y with
        | a => simp [actB]
        | b =>
          simp only [Valid, canB, Bool.true_and] at h
          have := pushC_length afterB r' h
          simp only [actB, List.length_cons]
          omega
        | c => simp [actB]

theorem act_length_le (x : L) {w : List L} (h : Valid start w = true) :
    (act x w).length ≤ w.length + 1 := by
  cases x with
  | a => have := actA_length h; simp only [act]; omega
  | b => have := actB_length h; simp only [act]; omega
  | c => have := pushC_length start w h; simp only [act]; omega

/-! ### Involutions, commutation and braid relation on normal forms -/

theorem pushC_pushC : ∀ (st : St) (w : List L), Valid st w = true → pushC (pushC w) = w
  | st, [], _ => by simp [pushC]
  | st, a :: r, h => by
    simp only [Valid, Bool.and_eq_true] at h
    simp [pushC, pushC_pushC afterA r h.2]
  | st, b :: r, h => by simp [pushC]
  | st, [c], _ => by simp [pushC]
  | st, c :: a :: r, h => by simp [Valid] at h
  | st, c :: b :: r, h => by simp [pushC]
  | st, c :: c :: r, h => by simp [Valid] at h

theorem actA_actA {w : List L} (h : Valid start w = true) : actA (actA w) = w := by
  cases w with
  | nil => rfl
  | cons x r =>
    cases x with
    | a =>
      cases r with
      | nil => rfl
      | cons y r' => cases y <;> simp_all [Valid, canA, actA]
    | b => rfl
    | c => rfl

theorem actB_actB {w : List L} (h : Valid start w = true) : actB (actB w) = w := by
  cases w with
  | nil => rfl
  | cons x r =>
    cases x with
    | a => rfl
    | b =>
      cases r with
      | nil => rfl
      | cons y r' =>
        cases y with
        | a => rfl
        | b => simp_all [Valid, canB]
        | c =>
          cases r' with
          | nil => rfl
          | cons z r'' => cases z <;> simp_all [Valid, canB]
    | c =>
      cases r with
      | nil => rfl
      | cons y r' =>
        cases y with
        | a => simp [Valid] at h
        | b =>
          simp only [Valid, canB, Bool.true_and] at h
          simp [actB, pushC_pushC afterB r' h]
        | c => simp [Valid] at h

/-- `a` and `c` commute on normal forms. -/
theorem actA_pushC {w : List L} (h : Valid start w = true) :
    actA (pushC w) = pushC (actA w) := by
  cases w with
  | nil => rfl
  | cons x r =>
    cases x with
    | a => rfl
    | b => rfl
    | c =>
      cases r with
      | nil => rfl
      | cons y r' => cases y <;> simp_all [Valid, actA, pushC]

/-- Braid relation `bcb = cbc` on normal forms. -/
theorem braid {w : List L} (h : Valid start w = true) :
    actB (pushC (actB w)) = pushC (actB (pushC w)) := by
  cases w with
  | nil => rfl
  | cons x r =>
    cases x with
    | a => rfl
    | b =>
      simp only [Valid, canB, Bool.true_and] at h
      cases r with
      | nil => rfl
      | cons y r' =>
        cases y with
        | a => rfl
        | b => simp [Valid, canB] at h
        | c =>
          cases r' with
          | nil => rfl
          | cons z r'' => cases z <;> simp_all [Valid, canB]
    | c =>
      cases r with
      | nil => rfl
      | cons y r' =>
        cases y with
        | a => simp [Valid] at h
        | b => rfl
        | c => simp [Valid] at h


/-! ### The Coxeter group `W = ⟨a,b,c | a²,b²,c²,(ac)²,(bc)³⟩` and the lifted action -/

/-- Coxeter matrix of type (2,3,∞): `m(a,c)=2`, `m(b,c)=3`, `m(a,b)=∞` (encoded `0`). -/
def M23 : CoxeterMatrix (Fin 3) where
  M := !![1, 0, 2;
          0, 1, 3;
          2, 3, 1]
  off_diagonal i i' h := by
    fin_cases i <;> fin_cases i' <;> first | exact absurd rfl h | decide

abbrev W := M23.Group
def cs : CoxeterSystem M23 W := M23.toCoxeterSystem

/-- Normal forms as a subtype of lists. -/
abbrev NF := {w : List L // Valid start w = true}

def nfAct (x : L) (v : NF) : NF := ⟨act x v.1, act_valid x v.2⟩

def ltr : Fin 3 → L
  | 0 => a
  | 1 => b
  | 2 => c

def idx : L → Fin 3
  | a => 0
  | b => 1
  | c => 2

@[simp] theorem idx_ltr (i : Fin 3) : idx (ltr i) = i := by fin_cases i <;> rfl
@[simp] theorem ltr_idx (x : L) : ltr (idx x) = x := by cases x <;> rfl

/-- The generators acting on normal forms, as elements of the endomorphism monoid. -/
def gen (i : Fin 3) : Function.End NF := nfAct (ltr i)

theorem nfAct_a_a (v : NF) : nfAct a (nfAct a v) = v := Subtype.ext (actA_actA v.2)
theorem nfAct_b_b (v : NF) : nfAct b (nfAct b v) = v := Subtype.ext (actB_actB v.2)
theorem nfAct_c_c (v : NF) : nfAct c (nfAct c v) = v := Subtype.ext (pushC_pushC start v.1 v.2)
theorem nfAct_a_c (v : NF) : nfAct a (nfAct c v) = nfAct c (nfAct a v) :=
  Subtype.ext (actA_pushC v.2)
theorem nfAct_bcb (v : NF) :
    nfAct b (nfAct c (nfAct b v)) = nfAct c (nfAct b (nfAct c v)) :=
  Subtype.ext (braid v.2)

theorem gen_sq (i : Fin 3) : gen i * gen i = 1 := by
  funext v
  fin_cases i
  · exact nfAct_a_a v
  · exact nfAct_b_b v
  · exact nfAct_c_c v

theorem gen_ac_pow : (gen 0 * gen 2) ^ 2 = 1 := by
  rw [pow_two]; funext v
  show nfAct a (nfAct c (nfAct a (nfAct c v))) = v
  rw [nfAct_a_c, nfAct_a_a, nfAct_c_c]

theorem gen_ca_pow : (gen 2 * gen 0) ^ 2 = 1 := by
  rw [pow_two]; funext v
  show nfAct c (nfAct a (nfAct c (nfAct a v))) = v
  rw [nfAct_a_c, nfAct_a_a, nfAct_c_c]

theorem gen_bc_pow : (gen 1 * gen 2) ^ 3 = 1 := by
  rw [pow_three]; funext v
  show nfAct b (nfAct c (nfAct b (nfAct c (nfAct b (nfAct c v))))) = v
  simp only [nfAct_bcb, nfAct_c_c, nfAct_b_b]

theorem gen_cb_pow : (gen 2 * gen 1) ^ 3 = 1 := by
  rw [pow_three]; funext v
  show nfAct c (nfAct b (nfAct c (nfAct b (nfAct c (nfAct b v))))) = v
  simp only [nfAct_bcb, nfAct_c_c, nfAct_b_b]

theorem gen_liftable : M23.IsLiftable gen := by
  intro i i'
  fin_cases i <;> fin_cases i'
  · exact (pow_one _).trans (gen_sq _)
  · exact pow_zero _
  · exact gen_ac_pow
  · exact pow_zero _
  · exact (pow_one _).trans (gen_sq _)
  · exact gen_bc_pow
  · exact gen_ca_pow
  · exact gen_cb_pow
  · exact (pow_one _).trans (gen_sq _)

/-- The lifted action `W →* End(NF)` (universal property of the Coxeter group). -/
noncomputable def φ : W →* Function.End NF := cs.lift ⟨gen, gen_liftable⟩

theorem φ_simple (i : Fin 3) : φ (cs.simple i) = gen i := cs.lift_apply_simple gen_liftable i

def nf0 : NF := ⟨[], rfl⟩

/-- The orbit map: the normal form of `w`. -/
noncomputable def ev (w : W) : List L := (φ w nf0).1

theorem ev_valid (w : W) : Valid start (ev w) = true := (φ w nf0).2

theorem ev_one : ev 1 = [] := by
  show (φ 1 nf0).1 = []
  rw [map_one]; rfl

theorem ev_simple_mul (i : Fin 3) (w : W) : ev (cs.simple i * w) = act (ltr i) (ev w) := by
  show (φ (cs.simple i * w) nf0).1 = _
  rw [map_mul, φ_simple]; rfl

/-- Reading a list of letters as a group element. -/
noncomputable def πL (w : List L) : W := cs.wordProd (w.map idx)

theorem πL_nil : πL [] = 1 := by simp [πL]
theorem πL_cons (x : L) (r : List L) : πL (x :: r) = cs.simple (idx x) * πL r := by
  simp [πL, CoxeterSystem.wordProd_cons]

theorem s_mul_s (i : Fin 3) : cs.simple i * cs.simple i = 1 := cs.simple_mul_simple_self i

theorem s_ac : cs.simple 0 * cs.simple 2 = cs.simple 2 * cs.simple 0 := by
  have h : (cs.simple 0 * cs.simple 2) ^ 2 = 1 := cs.simple_mul_simple_pow 0 2
  rw [pow_two] at h
  calc cs.simple 0 * cs.simple 2 = (cs.simple 0 * cs.simple 2)⁻¹ := mul_eq_one_iff_eq_inv.mp h
    _ = cs.simple 2 * cs.simple 0 := by rw [mul_inv_rev, cs.inv_simple, cs.inv_simple]

theorem s_bcb : cs.simple 1 * cs.simple 2 * cs.simple 1 = cs.simple 2 * cs.simple 1 * cs.simple 2 := by
  have h : (cs.simple 1 * cs.simple 2) ^ 3 = 1 := cs.simple_mul_simple_pow 1 2
  rw [pow_three] at h
  have h' : (cs.simple 1 * cs.simple 2 * cs.simple 1) * (cs.simple 2 * cs.simple 1 * cs.simple 2) = 1 := by
    rw [← h]; simp only [mul_assoc]
  calc cs.simple 1 * cs.simple 2 * cs.simple 1
      = (cs.simple 2 * cs.simple 1 * cs.simple 2)⁻¹ := mul_eq_one_iff_eq_inv.mp h'
    _ = cs.simple 2 * cs.simple 1 * cs.simple 2 := by
        simp only [mul_inv_rev, cs.inv_simple, mul_assoc]

theorem πL_pushC : ∀ (st : St) (w : List L), Valid st w = true →
    πL (pushC w) = cs.simple 2 * πL w
  | st, [], _ => by rw [pushC, πL_cons, πL_nil]; rfl
  | st, a :: r, h => by
    simp only [Valid, Bool.and_eq_true] at h
    rw [pushC, πL_cons, πL_cons, πL_pushC afterA r h.2]
    simp only [idx]
    rw [← mul_assoc, s_ac, mul_assoc]
  | st, b :: r, h => by simp only [pushC, πL_cons]; rfl
  | st, [c], _ => by rw [pushC, πL_cons, πL_nil, mul_one]; exact (s_mul_s 2).symm
  | st, c :: a :: r, h => by simp [Valid] at h
  | st, c :: b :: r, h => by simp [pushC, πL_cons, idx, cs.simple_mul_simple_cancel_left]
  | st, c :: c :: r, h => by simp [Valid] at h

theorem πL_actA {w : List L} (_h : Valid start w = true) : πL (actA w) = cs.simple 0 * πL w := by
  cases w with
  | nil => simp [actA, πL_cons, πL_nil, idx]
  | cons x r =>
    cases x with
    | a => simp [actA, πL_cons, idx, cs.simple_mul_simple_cancel_left]
    | b => simp [actA, πL_cons, idx]
    | c => simp [actA, πL_cons, idx]

theorem πL_actB {w : List L} (h : Valid start w = true) : πL (actB w) = cs.simple 1 * πL w := by
  cases w with
  | nil => simp [actB, πL_cons, πL_nil, idx]
  | cons x r =>
    cases x with
    | a => simp [actB, πL_cons, idx]
    | b => simp [actB, πL_cons, idx, cs.simple_mul_simple_cancel_left]
    | c =>
      cases r with
      | nil => simp [actB, πL_cons, πL_nil, idx]
      | cons y r' =>
        cases y with
        | a => simp [actB, πL_cons, idx]
        | b =>
          simp only [Valid, canB, Bool.true_and] at h
          rw [actB, πL_cons, πL_cons, πL_pushC afterB r' h, πL_cons, πL_cons]
          simp only [idx, ← mul_assoc]
          rw [s_bcb]
        | c => simp [actB, πL_cons, idx]

theorem πL_act (x : L) {w : List L} (h : Valid start w = true) :
    πL (act x w) = cs.simple (idx x) * πL w := by
  cases x with
  | a => exact πL_actA h
  | b => exact πL_actB h
  | c => exact πL_pushC start w h

/-- Every element is represented by its normal form. -/
theorem πL_ev (w : W) : πL (ev w) = w := by
  induction w using cs.simple_induction_left with
  | one => rw [ev_one, πL_nil]
  | mul_simple_left w i ih => rw [ev_simple_mul, πL_act _ (ev_valid w), idx_ltr, ih]

/-- Distinct normal forms are distinct elements. -/
theorem ev_πL : ∀ (v : List L), Valid start v = true → ev (πL v) = v
  | [], _ => by rw [πL_nil, ev_one]
  | x :: r, h => by
    rw [πL_cons, ev_simple_mul, ltr_idx, ev_πL r (valid_tail h), act_cons_of_valid h]

theorem length_ev_wordProd_le : ∀ (ω : List (Fin 3)),
    (ev (cs.wordProd ω)).length ≤ ω.length
  | [] => by simp [ev_one]
  | i :: ω => by
    rw [CoxeterSystem.wordProd_cons, ev_simple_mul]
    have h1 := act_length_le (ltr i) (ev_valid (cs.wordProd ω))
    have h2 := length_ev_wordProd_le ω
    simp only [List.length_cons]
    omega

/-- **Key lemma**: Coxeter length is the length of the normal form. -/
theorem length_eq_ev (w : W) : cs.length w = (ev w).length := by
  apply le_antisymm
  · calc cs.length w = cs.length (πL (ev w)) := by rw [πL_ev]
      _ ≤ ((ev w).map idx).length := cs.length_wordProd_le _
      _ = (ev w).length := by simp
  · obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
    rw [hω.eq]
    exact length_ev_wordProd_le ω

/-- The sphere of radius `n` is in bijection with normal forms of length `n`. -/
noncomputable def sphereEquiv (n : ℕ) :
    {w : W // cs.length w = n} ≃ {v : List L // Valid start v = true ∧ v.length = n} where
  toFun w := ⟨ev w.1, ev_valid w.1, by rw [← length_eq_ev]; exact w.2⟩
  invFun v := ⟨πL v.1, by rw [length_eq_ev, ev_πL v.1 v.2.1]; exact v.2.2⟩
  left_inv w := Subtype.ext (πL_ev w.1)
  right_inv v := Subtype.ext (ev_πL v.1 v.2.1)

/-! ### Counting normal forms: a three-state automaton -/

def NFs : ℕ → St → Finset (List L)
  | 0, _ => {[]}
  | 1, st => ({[c]} ∪ (if canA st then {[a]} else ∅)) ∪ (if canB st then {[b]} else ∅)
  | n+2, st => (if canA st then (NFs (n+1) afterA).image (a :: ·) else ∅)
      ∪ (if canB st then (NFs (n+1) afterB).image (b :: ·)
                          ∪ (NFs n afterB).image (fun r => c :: b :: r) else ∅)

theorem mem_NFs : ∀ (n : ℕ) (st : St) (w : List L),
    w ∈ NFs n st ↔ (Valid st w = true ∧ w.length = n)
  | 0, st, w => by
    cases w with
    | nil => simp [NFs, Valid]
    | cons x r => simp [NFs]
  | 1, st, w => by
    cases w with
    | nil => cases st <;> simp [NFs, Valid, canA, canB]
    | cons x r =>
      cases r with
      | nil => cases x <;> cases st <;> simp [NFs, Valid, canA, canB]
      | cons y r' => cases x <;> cases y <;> cases st <;> simp [NFs, Valid, canA, canB]
  | n+2, st, w => by
    cases w with
    | nil => cases st <;> simp [NFs, canA, canB]
    | cons x r =>
      cases x with
      | a => cases st <;> simp [NFs, Valid, canA, canB, mem_NFs (n+1)]
      | b => cases st <;> simp [NFs, Valid, canA, canB, mem_NFs (n+1)]
      | c =>
        cases r with
        | nil => cases st <;> simp [NFs, Valid, canA, canB]
        | cons y r' => cases y <;> cases st <;> simp [NFs, Valid, canA, canB, mem_NFs n]

theorem cb_injective : Function.Injective (fun r : List L => c :: b :: r) :=
  fun _ _ h => by simpa using h

theorem card_NFs_start (n : ℕ) : (NFs (n+2) start).card =
    (NFs (n+1) afterA).card + ((NFs (n+1) afterB).card + (NFs n afterB).card) := by
  simp only [NFs, canA, canB, ite_true]
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
    Finset.card_image_of_injective _ List.cons_injective,
    Finset.card_image_of_injective _ List.cons_injective,
    Finset.card_image_of_injective _ cb_injective]
  · rw [Finset.disjoint_left]
    rintro w hw hw'
    simp only [Finset.mem_image] at hw hw'
    obtain ⟨r, -, rfl⟩ := hw
    obtain ⟨r', -, h⟩ := hw'
    simp at h
  · rw [Finset.disjoint_union_right]
    constructor
    · rw [Finset.disjoint_left]
      rintro w hw hw'
      simp only [Finset.mem_image] at hw hw'
      obtain ⟨r, -, rfl⟩ := hw
      obtain ⟨r', -, h⟩ := hw'
      simp at h
    · rw [Finset.disjoint_left]
      rintro w hw hw'
      simp only [Finset.mem_image] at hw hw'
      obtain ⟨r, -, rfl⟩ := hw
      obtain ⟨r', -, h⟩ := hw'
      simp at h

theorem card_NFs_afterA (n : ℕ) : (NFs (n+2) afterA).card =
    (NFs (n+1) afterB).card + (NFs n afterB).card := by
  simp only [NFs, canA, canB, ite_true, Bool.false_eq_true, ite_false, Finset.empty_union]
  rw [Finset.card_union_of_disjoint,
    Finset.card_image_of_injective _ List.cons_injective,
    Finset.card_image_of_injective _ cb_injective]
  rw [Finset.disjoint_left]
  rintro w hw hw'
  simp only [Finset.mem_image] at hw hw'
  obtain ⟨r, -, rfl⟩ := hw
  obtain ⟨r', -, h⟩ := hw'
  simp at h

theorem card_NFs_afterB (n : ℕ) : (NFs (n+2) afterB).card = (NFs (n+1) afterA).card := by
  simp only [NFs, canA, canB, ite_true, Bool.false_eq_true, ite_false, Finset.union_empty]
  rw [Finset.card_image_of_injective _ List.cons_injective]

theorem cA_rec (n : ℕ) : (NFs (n+4) afterA).card =
    (NFs (n+2) afterA).card + (NFs (n+1) afterA).card := by
  have h1 : (NFs (n+4) afterA).card = (NFs (n+3) afterB).card + (NFs (n+2) afterB).card :=
    card_NFs_afterA (n+2)
  have h2 : (NFs (n+3) afterB).card = (NFs (n+2) afterA).card := card_NFs_afterB (n+1)
  have h3 : (NFs (n+2) afterB).card = (NFs (n+1) afterA).card := card_NFs_afterB n
  omega

theorem cS_eq (n : ℕ) : (NFs (n+2) start).card =
    (NFs (n+1) afterA).card + (NFs (n+2) afterA).card := by
  have h1 := card_NFs_start n
  have h2 := card_NFs_afterA n
  omega

theorem NFs_rec (n : ℕ) : (NFs (n+5) start).card =
    (NFs (n+3) start).card + (NFs (n+2) start).card := by
  have h1 : (NFs (n+5) start).card = (NFs (n+4) afterA).card + (NFs (n+5) afterA).card :=
    cS_eq (n+3)
  have h2 : (NFs (n+3) start).card = (NFs (n+2) afterA).card + (NFs (n+3) afterA).card :=
    cS_eq (n+1)
  have h3 : (NFs (n+2) start).card = (NFs (n+1) afterA).card + (NFs (n+2) afterA).card :=
    cS_eq n
  have h4 : (NFs (n+5) afterA).card = (NFs (n+3) afterA).card + (NFs (n+2) afterA).card :=
    cA_rec (n+1)
  have h5 : (NFs (n+4) afterA).card = (NFs (n+2) afterA).card + (NFs (n+1) afterA).card :=
    cA_rec n
  omega

/-! ### Main theorems -/

/-- Sphere sizes of `W(2,3,∞)` in its three simple reflections. -/
noncomputable def sphere (n : ℕ) : ℕ := Nat.card {w : W // cs.length w = n}

theorem sphere_eq_card (n : ℕ) : sphere n = (NFs n start).card := by
  unfold sphere
  rw [Nat.card_congr (sphereEquiv n), ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun v => (mem_NFs n start v).symm))

theorem sphere_zero : sphere 0 = 1 := by rw [sphere_eq_card]; decide
theorem sphere_one : sphere 1 = 3 := by rw [sphere_eq_card]; decide
theorem sphere_two : sphere 2 = 5 := by rw [sphere_eq_card]; decide
theorem sphere_three : sphere 3 = 7 := by rw [sphere_eq_card]; decide
theorem sphere_four : sphere 4 = 9 := by rw [sphere_eq_card]; decide

/-- **Padovan recurrence** of the sphere sizes, valid from `n = 5` on. -/
theorem sphere_rec (n : ℕ) : sphere (n+5) = sphere (n+3) + sphere (n+2) := by
  simp only [sphere_eq_card]; exact NFs_rec n

theorem sphere_rec' {n : ℕ} (hn : 5 ≤ n) : sphere n = sphere (n-2) + sphere (n-3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  simpa using sphere_rec m

/-- Growth series `∑ a(n) tⁿ = (1+t)²(1+t+t²)/(1−t²−t³)`, coefficient form:
`a(n) − a(n−2) − a(n−3)` is the coefficient of `tⁿ` in `1 + 3t + 4t² + 3t³ + t⁴`. -/
theorem sphere_numerator :
    sphere 0 = 1 ∧ sphere 1 = 3 ∧ sphere 2 - sphere 0 = 4 ∧
    sphere 3 - sphere 1 - sphere 0 = 3 ∧ sphere 4 - sphere 2 - sphere 1 = 1 ∧
    ∀ n, sphere (n+5) - sphere (n+3) - sphere (n+2) = 0 := by
  refine ⟨sphere_zero, sphere_one, ?_, ?_, ?_, fun n => ?_⟩
  · rw [sphere_two, sphere_zero]
  · rw [sphere_three, sphere_one, sphere_zero]
  · rw [sphere_four, sphere_two, sphere_one]
  · rw [sphere_rec]; omega

/-! ### Exponential growth rate: `a(n) = Θ(ρⁿ)` for the plastic number `ρ³ = ρ + 1` -/

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

/-- `2ρⁿ ≤ a(n) ≤ 4ρⁿ` for all `n ≥ 2`: the growth rate of the billiard group is exactly `ρ`. -/
theorem sphere_growth {ρ : ℝ} (h1 : 1 < ρ) (h3 : ρ ^ 3 = ρ + 1) (n : ℕ) :
    2 * ρ ^ (n+2) ≤ (sphere (n+2) : ℝ) ∧ (sphere (n+2) : ℝ) ≤ 4 * ρ ^ (n+2) := by
  have hlo := rho_gt h1 h3
  have hhi := rho_lt h1 h3
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | _ | m
    · rw [sphere_two]; push_cast
      constructor <;> nlinarith
    · rw [sphere_three]; push_cast
      rw [h3]; constructor <;> nlinarith
    · rw [sphere_four]; push_cast
      have h4 : ρ ^ 4 = ρ ^ 2 + ρ := by
        rw [show ρ ^ 4 = ρ * ρ ^ 3 by ring, h3]; ring
      rw [h4]; constructor <;> nlinarith
    · have ha := ih (m+1) (by omega)
      have hb := ih m (by omega)
      show 2 * ρ ^ (m+5) ≤ (sphere (m+5) : ℝ) ∧ (sphere (m+5) : ℝ) ≤ 4 * ρ ^ (m+5)
      rw [sphere_rec m]
      push_cast
      have hpow : ρ ^ (m+5) = ρ ^ (m+3) + ρ ^ (m+2) := by
        rw [show ρ ^ (m+5) = ρ ^ (m+2) * ρ ^ 3 by ring, h3]; ring
      rw [hpow]
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

/-- Cross-check against the brute-force PGL(2,ℤ) enumeration: 12, 16, 21, 28, 37. -/
theorem sphere_values :
    sphere 5 = 12 ∧ sphere 6 = 16 ∧ sphere 7 = 21 ∧ sphere 8 = 28 ∧ sphere 9 = 37 := by
  have h0 := sphere_zero; have h1 := sphere_one; have h2 := sphere_two
  have h3 := sphere_three; have h4 := sphere_four
  have r0 : sphere 5 = sphere 3 + sphere 2 := sphere_rec 0
  have r1 : sphere 6 = sphere 4 + sphere 3 := sphere_rec 1
  have r2 : sphere 7 = sphere 5 + sphere 4 := sphere_rec 2
  have r3 : sphere 8 = sphere 6 + sphere 5 := sphere_rec 3
  have r4 : sphere 9 = sphere 7 + sphere 6 := sphere_rec 4
  omega

/-- Summary statement. -/
theorem main :
    sphere 0 = 1 ∧ sphere 1 = 3 ∧ sphere 2 = 5 ∧ sphere 3 = 7 ∧ sphere 4 = 9 ∧
    (∀ n, sphere (n+5) = sphere (n+3) + sphere (n+2)) ∧
    (∀ ρ : ℝ, 1 < ρ → ρ ^ 3 = ρ + 1 → ∀ n,
      2 * ρ ^ (n+2) ≤ (sphere (n+2) : ℝ) ∧ (sphere (n+2) : ℝ) ≤ 4 * ρ ^ (n+2)) :=
  ⟨sphere_zero, sphere_one, sphere_two, sphere_three, sphere_four, sphere_rec,
   fun _ h1 h3 n => sphere_growth h1 h3 n⟩

section GrowthRate
open Filter Topology

theorem const_rpow_inv_mul_tendsto {ρ c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => c ^ ((n : ℝ)⁻¹) * ρ) atTop (𝓝 ρ) := by
  have h : Tendsto (fun n : ℕ => c ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    have hcont := Real.continuousAt_const_rpow (b := 0) hc.ne'
    have := hcont.tendsto.comp tendsto_inv_atTop_nhds_zero_nat
    simpa [Function.comp_def, Real.rpow_zero] using this
  simpa using h.mul_const ρ

/-- **Growth rate**: `a(n)^{1/n} → ρ`, the plastic number. -/
theorem sphere_root_tendsto {ρ : ℝ} (h1 : 1 < ρ) (h3 : ρ ^ 3 = ρ + 1) :
    Tendsto (fun n : ℕ => (sphere n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 ρ) := by
  have hρ0 : 0 ≤ ρ := by linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (const_rpow_inv_mul_tendsto (ρ := ρ) (c := 2) (by norm_num))
    (const_rpow_inv_mul_tendsto (ρ := ρ) (c := 4) (by norm_num)) ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hb := (sphere_growth h1 h3 m).1
    have hn0 : (m + 2 : ℕ) ≠ 0 := by omega
    calc (2:ℝ) ^ (((m + 2 : ℕ) : ℝ))⁻¹ * ρ
        = (2 * ρ ^ (m + 2)) ^ (((m + 2 : ℕ) : ℝ))⁻¹ := by
          rw [Real.mul_rpow (by norm_num) (pow_nonneg hρ0 _), Real.pow_rpow_inv_natCast hρ0 hn0]
      _ ≤ (sphere (m + 2) : ℝ) ^ (((m + 2 : ℕ) : ℝ))⁻¹ :=
          Real.rpow_le_rpow (by positivity) hb (by positivity)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hb := (sphere_growth h1 h3 m).2
    have hn0 : (m + 2 : ℕ) ≠ 0 := by omega
    calc (sphere (m + 2) : ℝ) ^ (((m + 2 : ℕ) : ℝ))⁻¹
        ≤ (4 * ρ ^ (m + 2)) ^ (((m + 2 : ℕ) : ℝ))⁻¹ :=
          Real.rpow_le_rpow (by positivity) hb (by positivity)
      _ = (4:ℝ) ^ (((m + 2 : ℕ) : ℝ))⁻¹ * ρ := by
          rw [Real.mul_rpow (by norm_num) (pow_nonneg hρ0 _), Real.pow_rpow_inv_natCast hρ0 hn0]

/-- Instantiated with the plastic number of `CoxeterGrowth.Plastic`. -/
theorem sphere_root_tendsto_plastic :
    Tendsto (fun n : ℕ => (sphere n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 CoxeterGrowth.plasticNumber) :=
  sphere_root_tendsto CoxeterGrowth.one_lt_plasticNumber CoxeterGrowth.plasticNumber_cubic

end GrowthRate

end CoxeterGrowth.TwoThreeInf

#print axioms CoxeterGrowth.TwoThreeInf.sphere_root_tendsto_plastic

#print axioms CoxeterGrowth.TwoThreeInf.sphere_root_tendsto
#print axioms CoxeterGrowth.TwoThreeInf.main
#print axioms CoxeterGrowth.TwoThreeInf.sphere_rec
#print axioms CoxeterGrowth.TwoThreeInf.length_eq_ev
#print axioms CoxeterGrowth.TwoThreeInf.sphere_values
#print axioms CoxeterGrowth.TwoThreeInf.sphere_growth
#print axioms CoxeterGrowth.TwoThreeInf.sphere_eq_card
