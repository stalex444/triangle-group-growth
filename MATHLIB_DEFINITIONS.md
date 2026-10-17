# Imported Mathlib definitions

The compared statements in `Challenge.lean` rest on the Mathlib definitions below: those behind the Coxeter matrix, its Coxeter group, the Coxeter system and its simple reflections, the length, the sphere count `Nat.card` and `PowerSeries.mk`. The remaining vocabulary (`Finset` sums over `range` and `Ico`, `PowerSeries.X`, `Filter.Tendsto`, `Filter.atTop`, `𝓝`, real powers) is standard Mathlib and is not quoted. Each excerpt is copied verbatim from Mathlib at the pinned revision `065356127b1dc0016f66b7283ce0ce2c4055aa55` (the revision required in `lakefile.toml` and recorded in `lake-manifest.json`), with its file path, line numbers and a permalink. Mathlib is released under the Apache 2.0 license; copyright of these excerpts remains with the Mathlib authors named in each file's header.

The file `DefinitionAudit.lean` in this repository is built with the package (it is a default target) and checks, as theorems, the facts about these definitions that the informal account relies on. It is not part of the compared set and imports Mathlib only. All its theorems use only the standard axioms `propext`, `Classical.choice` and `Quot.sound` (see `BUILD.txt`).

## 1. Coxeter matrices: the entry ∞ is encoded as 0

`Mathlib/GroupTheory/Coxeter/Matrix.lean`, lines 26–31: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/GroupTheory/Coxeter/Matrix.lean#L26-L31>

```lean
## Implementation details

In some texts on Coxeter groups, each entry $M_{i,i'}$ of a Coxeter matrix can be either a
positive integer or $\infty$. In our treatment of Coxeter matrices, we use the value $0$ instead of
$\infty$. This will turn out to have some fortunate consequences when defining the Coxeter group of
a Coxeter matrix and the standard geometric representation of a Coxeter group.
```

In the Challenge, `M 0 1 = 0` therefore means `m(a, b) = ∞`. Kernel-checked consequence: `DefinitionAudit.relation_eq_one_of_eq_zero` (an entry 0 imposes no relation).

## 2. `CoxeterMatrix`

`Mathlib/GroupTheory/Coxeter/Matrix.lean`, lines 66–74: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/GroupTheory/Coxeter/Matrix.lean#L66-L74>

```lean
/-- A *Coxeter matrix* is a symmetric matrix of natural numbers whose diagonal entries are equal to
1 and whose off-diagonal entries are not equal to 1. -/
@[ext]
structure CoxeterMatrix (B : Type*) where
  /-- The underlying matrix of the Coxeter matrix. -/
  M : Matrix B B ℕ
  isSymm : M.IsSymm := by decide
  diagonal i : M i i = 1 := by decide
  off_diagonal i i' : i ≠ i' → M i i' ≠ 1 := by decide
```

A symmetric ℕ-valued matrix with 1 on the diagonal and no off-diagonal 1. The Challenge's `M : CoxeterMatrix (Fin 3)` with `M 0 1 = 0`, `M 0 2 = p`, `M 1 2 = q` is the `(p, q, ∞)` triangle matrix; `triangle_matrix_exists` (statement 2) shows one exists for every `p, q ≥ 2`.

## 3. Coercion of a Coxeter matrix to its entries

`Mathlib/GroupTheory/Coxeter/Matrix.lean`, lines 80–81: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/GroupTheory/Coxeter/Matrix.lean#L80-L81>

```lean
/-- A Coxeter matrix can be coerced to a matrix. -/
instance : CoeFun (CoxeterMatrix B) fun _ ↦ (Matrix B B ℕ) := ⟨M⟩
```

This is why the Challenge can write the entries as `M 0 1`, `M 0 2`, `M 1 2`.

## 4. The Coxeter relations, the Coxeter group, its simple reflections

`Mathlib/GroupTheory/Coxeter/Basic.lean`, lines 99–115: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/GroupTheory/Coxeter/Basic.lean#L99-L115>

```lean
/-- The Coxeter relation associated to a Coxeter matrix $M$ and two indices $i, i' \in B$.
That is, the relation $(s_i s_{i'})^{M_{i, i'}}$, considered as an element of the free group
on $\{s_i\}_{i \in B}$.
If $M_{i, i'} = 0$, then this is the identity, indicating that there is no relation between
$s_i$ and $s_{i'}$. -/
def relation (i i' : B) : FreeGroup B := (FreeGroup.of i * FreeGroup.of i') ^ M i i'

/-- The set of all Coxeter relations associated to the Coxeter matrix $M$. -/
def relationsSet : Set (FreeGroup B) := range <| uncurry M.relation

/-- The Coxeter group associated to a Coxeter matrix $M$; that is, the group
$$\langle \{s_i\}_{i \in B} \vert \{(s_i s_{i'})^{M_{i, i'}}\}_{i, i' \in B} \rangle.$$ -/
protected def Group : Type _ := PresentedGroup M.relationsSet
deriving Group

/-- The simple reflection of the Coxeter group `M.Group` at the index `i`. -/
def simple (i : B) : M.Group := PresentedGroup.of i
```

The Coxeter group is the presented group ⟨sᵢ | (sᵢ sⱼ)^{M i j}⟩. Kernel-checked: `DefinitionAudit.relation_eq`, `DefinitionAudit.group_eq`.

## 5. `CoxeterSystem`

`Mathlib/GroupTheory/Coxeter/Basic.lean`, lines 152–159: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/GroupTheory/Coxeter/Basic.lean#L152-L159>

```lean
variable {B : Type*} (M : CoxeterMatrix B)

/-- A Coxeter system `CoxeterSystem M W` is a structure recording the isomorphism between
a group `W` and the Coxeter group associated to a Coxeter matrix `M`. -/
@[ext]
structure CoxeterSystem (W : Type*) [Group W] where
  /-- The isomorphism between `W` and the Coxeter group associated to `M`. -/
  mulEquiv : W ≃* M.Group
```

A Coxeter system on `W` is an isomorphism `W ≃* M.Group`. The Challenge quantifies over every group `W` with a Coxeter system `cs : CoxeterSystem M W`, so its statements hold for every Coxeter system with the given matrix (length depends on the generating set, so the system, not just the group, is the object).

## 6. The canonical Coxeter system

`Mathlib/GroupTheory/Coxeter/Basic.lean`, lines 165–166: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/GroupTheory/Coxeter/Basic.lean#L165-L166>

```lean
/-- The canonical Coxeter system on the Coxeter group associated to `M`. -/
def CoxeterMatrix.toCoxeterSystem : CoxeterSystem M M.Group := ⟨.refl _⟩
```

Every Coxeter matrix has a Coxeter system, on its own Coxeter group, so the hypotheses of the Challenge are satisfiable for each matrix that statement 2 provides. Kernel-checked: `DefinitionAudit.system_nonempty`.

## 7. `CoxeterSystem.simple`

`Mathlib/GroupTheory/Coxeter/Basic.lean`, lines 189–190: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/GroupTheory/Coxeter/Basic.lean#L189-L190>

```lean
/-- The simple reflection of `W` at the index `i`. -/
def simple (i : B) : W := cs.mulEquiv.symm (PresentedGroup.of i)
```

The generator `sᵢ` of `W`. Kernel-checked: `DefinitionAudit.simple_sq` (each squares to 1; nontrivial by `DefinitionAudit.length_simple` and `DefinitionAudit.length_one`, so involutions) and `DefinitionAudit.simple_mul_simple_pow` (the Coxeter relations hold in `W`).

## 8. `CoxeterSystem.wordProd`

`Mathlib/GroupTheory/Coxeter/Basic.lean`, lines 369–370: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/GroupTheory/Coxeter/Basic.lean#L369-L370>

```lean
/-- The product of the simple reflections of `W` corresponding to the indices in `ω`. -/
def wordProd (ω : List B) : W := prod (map cs.simple ω)
```

The product of the simple reflections along a word.

## 9. `CoxeterSystem.length` and reduced words

`Mathlib/GroupTheory/Coxeter/Length.lean`, lines 63–95: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/GroupTheory/Coxeter/Length.lean#L63-L95>

```lean
local prefix:100 "s " => cs.simple
local prefix:100 "π " => cs.wordProd

/-! ### Length -/

private theorem exists_word_with_prod (w : W) : ∃ n ω, n = ω.length ∧ π ω = w := by
  rcases cs.wordProd_surjective w with ⟨ω, rfl⟩
  use ω.length, ω

open scoped Classical in
/-- The length of `w`; i.e., the minimum number of simple reflections that
must be multiplied to form `w`. -/
@[no_expose] noncomputable def length (w : W) : ℕ := Nat.find (cs.exists_word_with_prod w)

local prefix:100 "ℓ " => cs.length

/-- The proposition that `ω` is reduced; that is, it has minimal length among all words that
represent the same element of `W`. -/
def IsReduced (ω : List B) : Prop := ℓ (π ω) = ω.length

theorem IsReduced.eq {ω : List B} (hω : cs.IsReduced ω) : ℓ (π ω) = ω.length := hω

theorem exists_isReduced (w : W) : ∃ ω : List B, cs.IsReduced ω ∧ w = π ω := by
  classical
  obtain ⟨ω, hω, rfl⟩ := Nat.find_spec (cs.exists_word_with_prod w)
  exact ⟨ω, hω, rfl⟩

@[deprecated (since := "2026-03-25")] alias exists_reduced_word := exists_isReduced
@[deprecated (since := "2026-03-25")] alias exists_reduced_word' := exists_isReduced

theorem length_wordProd_le (ω : List B) : ℓ (π ω) ≤ ω.length := by
  classical
  exact Nat.find_min' (cs.exists_word_with_prod (π ω)) ⟨ω, rfl, rfl⟩
```

`cs.length w` is the minimum number of simple reflections whose product is `w` (the word length ℓ(w) of the informal account). The body of `length` is marked `@[no_expose]` at this pin, so it does not unfold in importing modules. `DefinitionAudit.length_isLeast` states the characterization from Mathlib's public lemmas: `cs.length w` is the least element of `{n | ∃ ω, ω.length = n ∧ cs.wordProd ω = w}`. Also `DefinitionAudit.length_one`, `DefinitionAudit.length_simple`.

## 10. `Nat.card`

`Mathlib/SetTheory/Cardinal/Finite.lean`, lines 39–42: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/SetTheory/Cardinal/Finite.lean#L39-L42>

```lean
/-- `Nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `Nat.card α = 0`. -/
protected def card (α : Type*) : ℕ :=
  toNat (mk α)
```

`Nat.card` of an infinite type is 0. The sphere size `a(n) = Nat.card {w : W // cs.length w = n}` is nevertheless the number of elements of length `n`, because every sphere is finite for finitely many generators: `DefinitionAudit.sphere_finite`, and `DefinitionAudit.sphere_card_eq_finset_card` (`Nat.card` of the sphere equals the cardinality of a finite set whose members are exactly the elements of length `n`).

## 11. `PowerSeries.mk` and its coefficients

`Mathlib/RingTheory/PowerSeries/Basic.lean`, lines 114–119: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RingTheory/PowerSeries/Basic.lean#L114-L119>

```lean
/-- Constructor for formal power series. -/
def mk {R} (f : ℕ → R) : R⟦X⟧ := fun s => f (s ())

@[simp]
theorem coeff_mk (n : ℕ) (f : ℕ → R) : coeff n (mk f) = f n :=
  congr_arg f Finsupp.single_eq_same
```

`PowerSeries.mk f` is the series `Σ f(n) Xⁿ`. Kernel-checked for the growth series of the Challenge: `DefinitionAudit.coeff_growth` (its `n`-th coefficient is `a(n)`).
