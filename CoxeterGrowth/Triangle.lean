module
public import CoxeterGrowth.TriangleNF

@[expose] public section
/-!
# Growth series of the triangle Coxeter groups `(p, q, ∞)`

Let `cs : CoxeterSystem M W` with `M : CoxeterMatrix (Fin 3)`, `M 0 1 = 0` (`∞`), `M 0 2 = p`,
`M 1 2 = q`, `2 ≤ p, q`.  We prove, as an identity in `ℤ⟦X⟧`,

  `(Σ_n a(n) Xⁿ) · (1 − (X + ⋯ + X^{p−1})(X + ⋯ + X^{q−1})) = (1 + X)(1 + ⋯ + X^{p−1})(1 + ⋯ + X^{q−1})`

where `a(n) = #{w ∈ W : ℓ(w) = n}`.

Method.  The raw normal forms of `TriangleNF` carry the left action `act` of the generators,
which satisfies the Coxeter relations; by the universal property it lifts to `W →* End(NF)`, and
the orbit map `ev : W → NF` is inverse to the evaluation `piA : NF → W`.  Since each generator
changes the normal-form length by exactly one, `ℓ(w) = len (ev w)`: spheres in `W` are in bijection
with normal forms of the given length, which are counted in `TriangleNF`.
-/

namespace CoxeterGrowth.Triangle

open Finset PowerSeries

/-! ## A dihedral identity -/

/-- The wrap-around identity in a dihedral group: if `s² = c² = 1` and `(sc)^m = 1`, then
`s · c (sc)^a s^e = c (sc)^b s^{e'}` whenever `a + b + 2 = m` and `e + e' = 1`. -/
theorem wrap {G : Type*} [Group G] {s c : G} (hs : s * s = 1) (hc : c * c = 1) {m a b e e' : ℕ}
    (hm : (s * c) ^ m = 1) (hab : a + b + 2 = m) (he : e + e' = 1) :
    s * (c * ((s * c) ^ a * s ^ e)) = c * ((s * c) ^ b * s ^ e') := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hc' : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hcr : SemiconjBy c (s * c) (s * c)⁻¹ := by
    show c * (s * c) = (s * c)⁻¹ * c
    rw [mul_inv_rev, hs', hc', mul_assoc]
  have hcrb : c * (s * c) ^ b = (s * c) ^ (a + 2) * c := by
    have h1 : c * (s * c) ^ b = ((s * c)⁻¹) ^ b * c := hcr.pow_right b
    have h2 : ((s * c)⁻¹) ^ b = (s * c) ^ (a + 2) := by
      rw [inv_pow]
      apply inv_eq_of_mul_eq_one_left
      rw [← pow_add, show a + 2 + b = m by omega, hm]
    rw [h1, h2]
  have hL : s * (c * ((s * c) ^ a * s ^ e)) = (s * c) ^ (a + 1) * s ^ e := by
    rw [pow_succ']; simp only [mul_assoc]
  have hR : c * ((s * c) ^ b * s ^ e') = (s * c) ^ (a + 1) * (s * s ^ e') := by
    rw [← mul_assoc, hcrb, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc c c, hc, one_mul]
  rw [hL, hR]
  congr 1
  rcases e' with _ | _ | e'
  · obtain rfl : e = 1 := by omega
    simp
  · obtain rfl : e = 0 := by omega
    simp [hs]
  · omega

/-! ## Evaluating normal forms in a group -/

section Eval

variable {G : Type*} [Group G] (s : Fin 3 → G)

/-- The block `s_i c s_i c ⋯` with `j` letters (`c = s 2`). -/
def blockP (i : Fin 3) (j : ℕ) : G := (s i * s 2) ^ (j / 2) * s i ^ (j % 2)

/-- The head `c^ε · (s_i c s_i ⋯)`. -/
def headP (i : Fin 3) (x : ℕ × ℕ) : G := s 2 ^ x.1 * blockP s i x.2

/-- The tail: blocks alternating between `s_i`-blocks and `s_{i'}`-blocks. -/
def tailP : Fin 3 → Fin 3 → List ℕ → G
  | _, _, [] => 1
  | i, i', k :: r => blockP s i k * tailP i' i r

/-- A normal form with an `s_i`-head, followed by blocks starting with `s_{i'}`. -/
def piH (i i' : Fin 3) (v : Raw) : G := headP s i v.1 * tailP s i' i v.2

theorem blockP_zero (i : Fin 3) : blockP s i 0 = 1 := by simp [blockP]

theorem blockP_add_two (i : Fin 3) (j : ℕ) : blockP s i (j + 2) = s i * s 2 * blockP s i j := by
  unfold blockP
  rw [show (j + 2) / 2 = j / 2 + 1 by omega, show (j + 2) % 2 = j % 2 by omega, pow_succ']
  simp only [mul_assoc]

theorem piH_swap (i i' : Fin 3) : ∀ v : Raw, piH s i' i (swap v) = piH s i i' v
  | ((e, 0), []) => by simp [swap, piH, headP, tailP, blockP_zero]
  | ((e, 0), k :: r) => by simp [swap, piH, headP, tailP, blockP_zero, mul_assoc]
  | ((e, j + 1), r) => by simp [swap, piH, headP, tailP, blockP_zero, mul_assoc]

/-- **Head identity**: the head action `da` is left multiplication by `s_i`. -/
theorem headP_da (hs : ∀ k, s k * s k = 1) (i : Fin 3) {m : ℕ} (hm : 2 ≤ m)
    (hrel : (s i * s 2) ^ m = 1) : ∀ x : ℕ × ℕ, HV m x → headP s i (da m x) = s i * headP s i x
  | (0, 0), _ => by rw [da_00]; simp [headP, blockP]
  | (0, 1), _ => by rw [da_01]; simp [headP, blockP, hs]
  | (0, j + 2), _ => by
    rw [da_0]
    simp only [headP, blockP_add_two, pow_one, pow_zero, one_mul, ← mul_assoc, hs]
  | (e + 1, j), hx => by
    rw [HV_mk] at hx
    obtain rfl : e = 0 := by omega
    by_cases h : j + 2 < m
    · rw [da_1_lt h]
      simp only [headP, blockP_add_two, pow_zero, zero_add, pow_one, one_mul, mul_assoc]
    · rw [da_1_ge h]
      simp only [headP, zero_add, pow_one]
      unfold blockP
      exact (wrap (hs i) (hs 2) hrel (by omega) (by omega)).symm

end Eval

/-! ## The triangle Coxeter group -/

section Coxeter

variable {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)} (cs : CoxeterSystem M W) {p q : ℕ}

/-- The hypotheses: `M` is the Coxeter matrix of type `(p, q, ∞)`. -/
structure IsTri (M : CoxeterMatrix (Fin 3)) (p q : ℕ) : Prop where
  hp : 2 ≤ p
  hq : 2 ≤ q
  h01 : M 0 1 = 0
  h02 : M 0 2 = p
  h12 : M 1 2 = q

/-- Evaluation of a raw normal form in `W`. -/
def piA (v : Raw) : W := piH cs.simple 0 1 v

theorem piA_act (hT : IsTri M p q) (i : Fin 3) (v : Raw) (hv : V p q v) :
    piA cs (act p q i v) = cs.simple i * piA cs v := by
  have hs : ∀ k, cs.simple k * cs.simple k = 1 := cs.simple_mul_simple_self
  match i with
  | 0 =>
    have hrel : (cs.simple 0 * cs.simple 2) ^ p = 1 := hT.h02 ▸ cs.simple_mul_simple_pow 0 2
    show headP cs.simple 0 (da p v.1) * tailP cs.simple 1 0 v.2 =
      cs.simple 0 * (headP cs.simple 0 v.1 * tailP cs.simple 1 0 v.2)
    rw [headP_da cs.simple hs 0 hT.hp hrel v.1 hv.1, mul_assoc]
  | 1 =>
    have hrel : (cs.simple 1 * cs.simple 2) ^ q = 1 := hT.h12 ▸ cs.simple_mul_simple_pow 1 2
    have hsv : V q p (swap v) := swap_V (m₁ := p) (m₂ := q) (by have := hT.hq; omega) v hv
    show piH cs.simple 0 1 (swap (actH q (swap v))) = cs.simple 1 * piH cs.simple 0 1 v
    rw [piH_swap cs.simple 1 0, ← piH_swap cs.simple 0 1 v]
    show headP cs.simple 1 (da q (swap v).1) * tailP cs.simple 0 1 (swap v).2 =
      cs.simple 1 * (headP cs.simple 1 (swap v).1 * tailP cs.simple 0 1 (swap v).2)
    rw [headP_da cs.simple hs 1 hT.hq hrel (swap v).1 hsv.1, mul_assoc]
  | 2 =>
    obtain ⟨⟨e, j⟩, r⟩ := v
    rw [V_mk] at hv
    show cs.simple 2 ^ (1 - e) * blockP cs.simple 0 j * tailP cs.simple 1 0 r =
      cs.simple 2 * (cs.simple 2 ^ e * blockP cs.simple 0 j * tailP cs.simple 1 0 r)
    rcases e with _ | _ | e
    · simp [mul_assoc]
    · simp [← mul_assoc, hs]
    · omega

/-- The space of normal forms. -/
abbrev NF (p q : ℕ) := {v : Raw // V p q v}

/-- The generators acting on normal forms. -/
def gen (hT : IsTri M p q) (i : Fin 3) : Function.End (NF p q) :=
  fun v => ⟨act p q i v.1, act_V hT.hp hT.hq i v.1 v.2⟩

theorem end_pow_val (f : Function.End (NF p q)) (g : Raw → Raw) (hfg : ∀ v, (f v).1 = g v.1) :
    ∀ (n : ℕ) (v : NF p q), ((f ^ n) v).1 = g^[n] v.1
  | 0, _ => rfl
  | n + 1, v => by
    rw [pow_succ]
    show ((f ^ n) (f v)).1 = g^[n + 1] v.1
    rw [end_pow_val f g hfg n (f v), hfg, Function.iterate_succ_apply]

theorem pow_swap_of_sq {N : Type*} [Monoid N] {x y : N} (hx : x * x = 1) (n : ℕ)
    (h : (x * y) ^ n = 1) : (y * x) ^ n = 1 := by
  have hsc : SemiconjBy x (y * x) (x * y) := by
    show x * (y * x) = x * y * x
    rw [mul_assoc]
  have h1 : x * (y * x) ^ n = (x * y) ^ n * x := hsc.pow_right n
  calc (y * x) ^ n = x * x * (y * x) ^ n := by rw [hx, one_mul]
    _ = x * (x * (y * x) ^ n) := mul_assoc _ _ _
    _ = 1 := by rw [h1, h, one_mul, hx]

theorem gen_sq (hT : IsTri M p q) (i : Fin 3) : gen hT i * gen hT i = 1 := by
  funext v
  exact Subtype.ext (act_act hT.hp hT.hq i v.1 v.2)

theorem gen_ac (hT : IsTri M p q) : (gen hT 0 * gen hT 2) ^ p = 1 := by
  funext v
  apply Subtype.ext
  rw [end_pow_val _ (fun u => act p q 0 (act p q 2 u)) (fun _ => rfl)]
  exact rel_ac hT.hp v.1 v.2

theorem gen_bc (hT : IsTri M p q) : (gen hT 1 * gen hT 2) ^ q = 1 := by
  funext v
  apply Subtype.ext
  rw [end_pow_val _ (fun u => act p q 1 (act p q 2 u)) (fun _ => rfl)]
  exact rel_bc hT.hp hT.hq v.1 v.2

theorem gen_liftable (hT : IsTri M p q) : M.IsLiftable (gen hT) := fun i i' =>
  match i, i' with
  | 0, 0 => by rw [M.diagonal]; exact (pow_one _).trans (gen_sq hT 0)
  | 1, 1 => by rw [M.diagonal]; exact (pow_one _).trans (gen_sq hT 1)
  | 2, 2 => by rw [M.diagonal]; exact (pow_one _).trans (gen_sq hT 2)
  | 0, 1 => by rw [hT.h01]; exact pow_zero _
  | 1, 0 => by rw [M.symmetric, hT.h01]; exact pow_zero _
  | 0, 2 => by rw [hT.h02]; exact gen_ac hT
  | 2, 0 => by rw [M.symmetric, hT.h02]; exact pow_swap_of_sq (gen_sq hT 0) p (gen_ac hT)
  | 1, 2 => by rw [hT.h12]; exact gen_bc hT
  | 2, 1 => by rw [M.symmetric, hT.h12]; exact pow_swap_of_sq (gen_sq hT 1) q (gen_bc hT)

/-- The lifted action `W →* End(NF)`. -/
noncomputable def φ (hT : IsTri M p q) : W →* Function.End (NF p q) :=
  cs.lift ⟨gen hT, gen_liftable hT⟩

theorem φ_simple (hT : IsTri M p q) (i : Fin 3) : φ cs hT (cs.simple i) = gen hT i :=
  cs.lift_apply_simple (gen_liftable hT) i

/-- The empty normal form. -/
def nf0 (hT : IsTri M p q) : NF p q := ⟨((0, 0), []), by
  rw [V_mk]; exact ⟨⟨by omega, by have := hT.hp; omega⟩, trivial⟩⟩

/-- The normal form of `w`. -/
noncomputable def ev (hT : IsTri M p q) (w : W) : Raw := (φ cs hT w (nf0 hT)).1

theorem ev_valid (hT : IsTri M p q) (w : W) : V p q (ev cs hT w) := (φ cs hT w (nf0 hT)).2

theorem ev_one (hT : IsTri M p q) : ev cs hT 1 = ((0, 0), []) := by
  unfold ev; rw [map_one]; rfl

theorem ev_simple_mul (hT : IsTri M p q) (i : Fin 3) (w : W) :
    ev cs hT (cs.simple i * w) = act p q i (ev cs hT w) := by
  unfold ev; rw [map_mul, φ_simple]; rfl

theorem piA_nil : piA cs ((0, 0), []) = 1 := by
  simp [piA, piH, headP, tailP, blockP]

/-- Every element is the value of its normal form. -/
theorem piA_ev (hT : IsTri M p q) (w : W) : piA cs (ev cs hT w) = w := by
  induction w using cs.simple_induction_left with
  | one => rw [ev_one, piA_nil]
  | mul_simple_left w i ih =>
    rw [ev_simple_mul, piA_act cs hT i _ (ev_valid cs hT w), ih]

theorem length_piA_le (hT : IsTri M p q) : ∀ (n : ℕ) (v : Raw), V p q v → len v = n →
    cs.length (piA cs v) ≤ n
  | 0, v, hv, hl0 => by
    rw [eq_nil_of_len v hv hl0, piA_nil, cs.length_one]
  | n + 1, v, hv, hl0 => by
    obtain ⟨i, hi⟩ := descent v hv (by omega)
    have hv' := act_V hT.hp hT.hq i v hv
    have hvv : act p q i (act p q i v) = v := act_act hT.hp hT.hq i v hv
    have ih := length_piA_le hT n (act p q i v) hv' (by omega)
    calc cs.length (piA cs v) = cs.length (cs.simple i * piA cs (act p q i v)) := by
          rw [← piA_act cs hT i _ hv', hvv]
      _ ≤ cs.length (cs.simple i) + cs.length (piA cs (act p q i v)) := cs.length_mul_le _ _
      _ ≤ n + 1 := by rw [cs.length_simple]; omega

/-- Distinct normal forms are distinct elements. -/
theorem ev_piA (hT : IsTri M p q) : ∀ (n : ℕ) (v : Raw), V p q v → len v = n →
    ev cs hT (piA cs v) = v
  | 0, v, hv, hl0 => by
    rw [eq_nil_of_len v hv hl0, piA_nil, ev_one]
  | n + 1, v, hv, hl0 => by
    obtain ⟨i, hi⟩ := descent v hv (by omega)
    have hv' := act_V hT.hp hT.hq i v hv
    have hvv : act p q i (act p q i v) = v := act_act hT.hp hT.hq i v hv
    have ih := ev_piA hT n (act p q i v) hv' (by omega)
    calc ev cs hT (piA cs v) = ev cs hT (cs.simple i * piA cs (act p q i v)) := by
          rw [← piA_act cs hT i _ hv', hvv]
      _ = act p q i (act p q i v) := by rw [ev_simple_mul, ih]
      _ = v := hvv

theorem len_ev_wordProd_le (hT : IsTri M p q) : ∀ ω : List (Fin 3),
    len (ev cs hT (cs.wordProd ω)) ≤ ω.length
  | [] => by rw [CoxeterSystem.wordProd_nil, ev_one]; rfl
  | i :: ω => by
    rw [CoxeterSystem.wordProd_cons, ev_simple_mul]
    have h1 := len_act_le hT.hp hT.hq i _ (ev_valid cs hT (cs.wordProd ω))
    have h2 := len_ev_wordProd_le hT ω
    simp only [List.length_cons]
    omega

/-- **Length additivity**: the Coxeter length is the length of the normal form. -/
theorem length_eq_len_ev (hT : IsTri M p q) (w : W) : cs.length w = len (ev cs hT w) := by
  apply le_antisymm
  · calc cs.length w = cs.length (piA cs (ev cs hT w)) := by rw [piA_ev]
      _ ≤ len (ev cs hT w) := length_piA_le cs hT _ _ (ev_valid cs hT w) rfl
  · obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
    rw [hω.eq]
    exact len_ev_wordProd_le cs hT ω

/-- Spheres of `W` are in bijection with normal forms of the same length. -/
noncomputable def sphereEquiv (hT : IsTri M p q) (n : ℕ) :
    {w : W // cs.length w = n} ≃ {v : Raw // V p q v ∧ len v = n} where
  toFun w := ⟨ev cs hT w.1, ev_valid cs hT w.1, by rw [← length_eq_len_ev]; exact w.2⟩
  invFun v := ⟨piA cs v.1, by rw [length_eq_len_ev cs hT, ev_piA cs hT _ v.1 v.2.1 rfl]; exact v.2.2⟩
  left_inv w := Subtype.ext (piA_ev cs hT w.1)
  right_inv v := Subtype.ext (ev_piA cs hT _ v.1 v.2.1 rfl)

theorem sphere_eq_card (hT : IsTri M p q) (n : ℕ) :
    Nat.card {w : W // cs.length w = n} = (NFs p q n).card := by
  rw [Nat.card_congr (sphereEquiv cs hT n), ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun v => (mem_NFs p q n v).symm))

/-- **Growth series of the triangle Coxeter group `(p, q, ∞)`** (coefficient form in `ℤ⟦X⟧`). -/
theorem growth_series (hT : IsTri M p q) :
    (PowerSeries.mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) *
        (1 - (∑ i ∈ Ico 1 p, (X : ℤ⟦X⟧) ^ i) * (∑ i ∈ Ico 1 q, (X : ℤ⟦X⟧) ^ i)) =
      (1 + X) * (∑ i ∈ range p, (X : ℤ⟦X⟧) ^ i) * (∑ i ∈ range q, (X : ℤ⟦X⟧) ^ i) := by
  have h := nf_series' p q (by have := hT.hq; omega)
  simp only [ser] at h
  simp only [sphere_eq_card cs hT]
  exact h

end Coxeter

end CoxeterGrowth.Triangle
