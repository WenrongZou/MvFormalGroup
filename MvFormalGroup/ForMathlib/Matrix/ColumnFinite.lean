/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Two-sided inverses of column-finite matrices

For an infinite index type, `Matrix n n R` has no multiplication, so `Invertible` and `IsUnit`
do not apply. A matrix whose columns have finitely many nonzero entries is still the matrix of a
linear map of free modules `R^(τ) → R^(ι)`, and products with such a matrix on the right are
finite sums. `Matrix.IsCofiniteInverse K J` says that the column-finite matrix `K` is a two-sided
inverse of `J`, with products written as `finsum`.

## Main declarations

* `Matrix.IsCofiniteInverse K J`: `K` is column-finite, `K J = 1` and `J K = 1`.
* `Matrix.IsCofiniteInverse.one`: the identity matrix is its own cofinite inverse.
* `Matrix.IsCofiniteInverse.of_isUnit`: for a finite index type, the inverse of an invertible
  matrix is a cofinite inverse.
* `Matrix.IsCofiniteInverse.of_isUnit_det`: for a finite index type, if `J` has invertible
  determinant, then the nonsingular inverse `J⁻¹` is a cofinite inverse.
-/

@[expose] public section

noncomputable section

namespace Matrix

variable {R : Type*} [Semiring R] {ι τ : Type*}

/-- The column-finite `τ × ι` matrix `K` is a two-sided inverse of the `ι × τ` matrix `J`:
`K J = 1` and `J K = 1`. Products are taken with `finsum`. The product `J K` is a finite sum
because `K` is column-finite; the product `K J` is a finite sum when `J` is column-finite too.

Column-finite matrices are the matrices of linear maps between free modules `R^(τ) → R^(ι)`. When
`J` is column-finite, this says that `J` induces an isomorphism `R^(τ) ≅ R^(ι)`. -/
structure IsCofiniteInverse [DecidableEq ι] [DecidableEq τ] (M : Matrix τ ι R)
    (N : Matrix ι τ R) : Prop where
  /-- Every column of `K` has finitely many nonzero entries. -/
  col_finite j : {i | M i j ≠ 0}.Finite
  /-- `M N = 1`. -/
  mul_left i k : ∑ᶠ j, M i j * N j k = (1 : Matrix τ τ R) i k
  /-- `N M = 1`. -/
  mul_right i k : ∑ᶠ j, N i j * M j k = (1 : Matrix ι ι R) i k

theorem IsCofiniteInverse.one [DecidableEq τ] : IsCofiniteInverse (1 : Matrix τ τ R) 1 where
  col_finite j := (Set.finite_singleton j).subset fun i hi ↦ by
    by_contra h
    exact hi (Matrix.one_apply_ne h)
  mul_left i k := by
    rw [finsum_eq_single _ i fun j hj ↦ by simp [Matrix.one_apply_ne' hj]]
    simp
  mul_right i k := by
    rw [finsum_eq_single _ i fun j hj ↦ by simp [Matrix.one_apply_ne' hj]]
    simp

/-- For a finite index type, the inverse of an invertible matrix is a cofinite inverse. -/
theorem IsCofiniteInverse.of_isUnit [Fintype τ] [DecidableEq τ] {J : Matrix τ τ R}
    (hJ : IsUnit J) : IsCofiniteInverse (↑hJ.unit⁻¹ : Matrix τ τ R) J where
  col_finite _ := Set.toFinite _
  mul_left i k := by
    have : (↑hJ.unit⁻¹ : Matrix τ τ R) * J = 1 := by
      simpa only [hJ.unit_spec] using hJ.unit.inv_mul
    rw [finsum_eq_sum_of_fintype, ← Matrix.mul_apply, this]
  mul_right i k := by
    have : J * (↑hJ.unit⁻¹ : Matrix τ τ R) = 1 := by
      simpa only [hJ.unit_spec] using hJ.unit.mul_inv
    rw [finsum_eq_sum_of_fintype, ← Matrix.mul_apply, this]

/-- For a finite index type, if `J` has invertible determinant, then the nonsingular inverse
`J⁻¹` is a cofinite inverse. -/
theorem IsCofiniteInverse.of_isUnit_det {R : Type*} [CommRing R] [Fintype τ] [DecidableEq τ]
    {J : Matrix τ τ R} (hJ : IsUnit J.det) : IsCofiniteInverse J⁻¹ J where
  col_finite _ := Set.toFinite _
  mul_left i k := by rw [finsum_eq_sum_of_fintype, ← Matrix.mul_apply, J.nonsing_inv_mul hJ]
  mul_right i k := by rw [finsum_eq_sum_of_fintype, ← Matrix.mul_apply, J.mul_nonsing_inv hJ]

end Matrix
