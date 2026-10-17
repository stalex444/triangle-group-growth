module
public import Mathlib

@[expose] public section
/-!
# Audit of the imported definitions

The compared statements in `Challenge.lean` rest on five definitions imported from Mathlib (pinned
revision `065356127b1dc0016f66b7283ce0ce2c4055aa55`): `CoxeterMatrix` with its Coxeter group,
`CoxeterSystem`, `CoxeterSystem.length`, `Nat.card` and `PowerSeries.mk`. Their pinned source
text is quoted verbatim, with permalinks, in `MATHLIB_DEFINITIONS.md`; the remaining vocabulary
(`Finset` sums, `PowerSeries.X`, `Filter.Tendsto`, `Filter.atTop`, `𝓝`, real powers) is standard
Mathlib and is not quoted. This file is not
part of the compared set. It records, as kernel-checked theorems, the facts about those
definitions that the informal account relies on, so that the correspondence can be audited from
this repository alone:

* `relation_eq`, `relation_eq_one_of_eq_zero`, `group_eq` — the Coxeter group of `M` is the
  presented group `⟨sᵢ | (sᵢ sⱼ)^{M i j}⟩`, and an entry `M i j = 0` imposes no relation between
  `sᵢ` and `sⱼ`. This is Mathlib's encoding of the entry `∞`, so `M 0 1 = 0` in the Challenge
  means `m(a, b) = ∞`.
* `simple_sq`, `simple_mul_simple_pow` — the simple reflections of a Coxeter system square to
  `1` and satisfy the Coxeter relations; they are nontrivial, by `length_simple` and
  `length_one`, so they are involutions.
* `system_nonempty` — every Coxeter matrix has a Coxeter system (its own Coxeter group), so the
  Challenge's hypotheses are satisfiable for each matrix of statement 2.
* `length_isLeast`, `length_one`, `length_simple` — `cs.length w` is the least number of simple
  reflections whose product is `w`. Mathlib marks the body of `CoxeterSystem.length` as
  `@[no_expose]`, so this characterization is stated here from Mathlib's public lemmas.
* `sphere_finite`, `sphere_card_eq_finset_card` — for finitely many generators every sphere
  `{w : W // cs.length w = n}` is finite, and `Nat.card` of it (which would be `0` for an
  infinite type) is the cardinality of the finite set of elements of length `n`.
* `coeff_growth` — the `n`-th coefficient of the growth series in the Challenge is `a(n)`.
-/

namespace DefinitionAudit

variable {B : Type*}

/-- The Coxeter relation of `M` at `(i, i')` is `(sᵢ sᵢ')^{M i i'}` in the free group. -/
theorem relation_eq (M : CoxeterMatrix B) (i i' : B) :
    M.relation i i' = (FreeGroup.of i * FreeGroup.of i') ^ M i i' := rfl

/-- An entry `0` imposes no relation: Mathlib's encoding of the Coxeter-matrix entry `∞`. -/
theorem relation_eq_one_of_eq_zero (M : CoxeterMatrix B) {i i' : B} (h : M i i' = 0) :
    M.relation i i' = 1 := by
  rw [relation_eq, h, pow_zero]

/-- The Coxeter group of `M` is the group presented by the Coxeter relations. -/
theorem group_eq (M : CoxeterMatrix B) : M.Group = PresentedGroup M.relationsSet := rfl

/-- Every Coxeter matrix has a Coxeter system: its own Coxeter group. -/
theorem system_nonempty (M : CoxeterMatrix B) : Nonempty (CoxeterSystem M M.Group) :=
  ⟨M.toCoxeterSystem⟩

variable {W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- The simple reflections square to `1`. -/
theorem simple_sq (i : B) : cs.simple i ^ 2 = 1 := cs.simple_sq i

/-- The simple reflections satisfy the Coxeter relations. -/
theorem simple_mul_simple_pow (i i' : B) : (cs.simple i * cs.simple i') ^ M i i' = 1 :=
  cs.simple_mul_simple_pow i i'

/-- `cs.length w` is the least length of a word in the simple reflections whose product is `w`. -/
theorem length_isLeast (w : W) :
    IsLeast {n : ℕ | ∃ ω : List B, ω.length = n ∧ cs.wordProd ω = w} (cs.length w) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
    exact ⟨ω, hω.eq.symm, rfl⟩
  · rintro n ⟨ω, rfl, rfl⟩
    exact cs.length_wordProd_le ω

/-- The identity has length `0`. -/
theorem length_one : cs.length 1 = 0 := cs.length_one

/-- Every simple reflection has length `1`. -/
theorem length_simple (i : B) : cs.length (cs.simple i) = 1 := cs.length_simple i

/-- For finitely many generators, every sphere of the word metric is finite. -/
theorem sphere_finite [Finite B] (n : ℕ) : Finite {w : W // cs.length w = n} := by
  have hsub : {w : W | cs.length w = n} ⊆ cs.wordProd '' {ω : List B | ω.length = n} := by
    intro w hw
    obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
    exact ⟨ω, hω.eq.symm.trans hw, rfl⟩
  exact (((List.finite_length_eq B n).image cs.wordProd).subset hsub).to_subtype

/-- Hence `Nat.card` of a sphere is the cardinality of the finite set of elements of length `n`. -/
theorem sphere_card_eq_finset_card [Finite B] (n : ℕ) :
    ∃ s : Finset W, (∀ w, w ∈ s ↔ cs.length w = n) ∧
      Nat.card {w : W // cs.length w = n} = s.card := by
  have hfin : {w : W | cs.length w = n}.Finite := Set.finite_coe_iff.mp (sphere_finite cs n)
  exact ⟨hfin.toFinset, fun w => by simp, Nat.card_eq_card_finite_toFinset hfin⟩

/-- The `n`-th coefficient of the growth series used in the Challenge is the sphere size `a(n)`. -/
theorem coeff_growth (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) =
      Nat.card {w : W // cs.length w = n} :=
  PowerSeries.coeff_mk _ _

end DefinitionAudit
