/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Matrix–vector products for arbitrary index types

`Matrix.mulVec` needs a finite column index, since `(M *ᵥ v)ᵢ = ∑ⱼ Mᵢⱼ vⱼ` is a `Finset` sum.
`Matrix.finsumMulVec` is the same product with the sum taken as a `finsum`, so it makes sense
for arbitrary index types. Each entry is a genuine finite sum when `v` is finitely supported,
and the result is again finitely supported when `M` is column-finite.

## Main declarations

* `Matrix.finsumMulVec M v`: the product `∑ᶠ j, M i j * v j`.
* `Matrix.finsumMulVec_eq_mulVec`: for a finite column index it agrees with `M *ᵥ v`.
* `Matrix.finite_support_finsumMulVec`: a column-finite matrix maps finitely supported vectors
  to finitely supported vectors.
-/

@[expose] public section

noncomputable section

namespace Matrix

variable {α : Type*} {m n : Type*}

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α]

/-- The matrix–vector product `(M v)ᵢ = ∑ⱼ Mᵢⱼ vⱼ` for arbitrary index types, with the sum
taken as a `finsum`. For a finite column index it agrees with `M *ᵥ v`
(`Matrix.finsumMulVec_eq_mulVec`). -/
def finsumMulVec (M : Matrix m n α) (v : n → α) : m → α :=
  fun i ↦ ∑ᶠ j, M i j * v j

theorem finsumMulVec_apply (M : Matrix m n α) (v : n → α) (i : m) :
    M.finsumMulVec v i = ∑ᶠ j, M i j * v j :=
  rfl

@[simp]
theorem finsumMulVec_zero (M : Matrix m n α) : M.finsumMulVec 0 = 0 := by
  funext i
  simp [finsumMulVec]

@[simp]
theorem zero_finsumMulVec (v : n → α) : (0 : Matrix m n α).finsumMulVec v = 0 := by
  funext i
  simp [finsumMulVec]

/-- For a finite column index, `finsumMulVec` is `mulVec`. -/
theorem finsumMulVec_eq_mulVec [Fintype n] (M : Matrix m n α) (v : n → α) :
    M.finsumMulVec v = M *ᵥ v := by
  funext i
  simp [finsumMulVec, mulVec, dotProduct, finsum_eq_sum_of_fintype]

/-- An entry of `M.finsumMulVec v` can be nonzero only in a row where `M` has a nonzero entry
in a column in the support of `v`. -/
theorem support_finsumMulVec_subset (M : Matrix m n α) (v : n → α) :
    Function.support (M.finsumMulVec v) ⊆ ⋃ j ∈ Function.support v, {i | M i j ≠ 0} := by
  intro i hi
  obtain ⟨j, hj⟩ : ∃ j, M i j * v j ≠ 0 := by
    by_contra! h
    exact hi (finsum_eq_zero_of_forall_eq_zero h)
  exact Set.mem_biUnion (right_ne_zero_of_mul hj) (left_ne_zero_of_mul hj)

/-- A column-finite matrix maps finitely supported vectors to finitely supported vectors. -/
theorem finite_support_finsumMulVec {M : Matrix m n α} (hM : ∀ j, {i | M i j ≠ 0}.Finite)
    {v : n → α} (hv : (Function.support v).Finite) :
    (Function.support (M.finsumMulVec v)).Finite :=
  (hv.biUnion fun j _ ↦ hM j).subset (M.support_finsumMulVec_subset v)

end NonUnitalNonAssocSemiring

section NonAssocSemiring

variable [NonAssocSemiring α] [DecidableEq n]

@[simp]
theorem one_finsumMulVec (v : n → α) : (1 : Matrix n n α).finsumMulVec v = v := by
  funext i
  rw [finsumMulVec_apply, finsum_eq_single _ i fun j hj ↦ by simp [one_apply_ne' hj]]
  simp

end NonAssocSemiring

end Matrix
