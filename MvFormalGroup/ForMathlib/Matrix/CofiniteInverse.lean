/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import MvFormalGroup.ForMathlib.Matrix.ColumnFinite

/-!
# Uniqueness of cofinite inverses

A column-finite matrix `J` has at most one cofinite inverse: if `K` and `K'` are both
cofinite inverses of `J`, then `K = K (J K') = (K J) K' = K'`. The middle step is associativity
of `finsum` products, which needs `J` and `K'` to be column-finite.

No inverse is chosen here: getting a matrix out of `∃ K, IsCofiniteInverse K J` would need
`Classical.choose`. Instead, definitions take the inverse `K` as an argument, and uniqueness
shows that they do not depend on it.

## Main declarations

* `Matrix.finsum_mul_finsum_assoc`: associativity of `finsum` matrix products.
* `Matrix.IsCofiniteInverse.eq`: a column-finite matrix has at most one cofinite inverse.
* `Matrix.IsCofiniteInvertible J`: `J` has a cofinite inverse.
* `Matrix.IsCofiniteInvertible.existsUnique`: a column-finite `J` with a cofinite inverse has
  exactly one.
* `Matrix.IsCofiniteInverse.eq_nonsing_inv`: for a finite index type, every cofinite inverse is
  the nonsingular inverse `J⁻¹`.
-/

@[expose] public section

noncomputable section

namespace Matrix

variable {R : Type*} [Semiring R] {ι τ : Type*}

section Assoc

variable {l m n o : Type*}

/-- Associativity of `finsum` matrix products, `A (B C) = (A B) C`, when `B` and `C` are
column-finite. Each sum on the right is then finite; the sums on the left are finite for
`j` outside a finite set. -/
theorem finsum_mul_finsum_assoc (A : Matrix l m R) {B : Matrix m n R} {C : Matrix n o R}
    (hB : ∀ j, {i | B i j ≠ 0}.Finite) (hC : ∀ j, {i | C i j ≠ 0}.Finite) (i : l) (k : o) :
    ∑ᶠ j, A i j * ∑ᶠ p, B j p * C p k = ∑ᶠ p, (∑ᶠ j, A i j * B j p) * C p k := by
  classical
  let P := (hC k).toFinset
  let S := P.biUnion fun p ↦ (hB p).toFinset
  have hBC (j : m) : ∑ᶠ p, B j p * C p k = ∑ p ∈ P, B j p * C p k :=
    finsum_eq_sum_of_support_subset _ <| Function.support_subset_iff'.mpr <| by
      simp +contextual [P]
  have hS : ∀ j ∉ S, ∀ p ∈ P, B j p = 0 := fun j hj p hp ↦ by
    by_contra h
    exact hj (Finset.mem_biUnion.mpr ⟨p, hp, by simpa using h⟩)
  have hAB : ∀ p ∈ P, ∑ᶠ j, A i j * B j p = ∑ j ∈ S, A i j * B j p := fun p hp ↦
    finsum_eq_sum_of_support_subset _ <| Function.support_subset_iff'.mpr fun j hj ↦ by
      simp [hS j hj p hp]
  rw [finsum_eq_sum_of_support_subset _ (s := S), finsum_eq_sum_of_support_subset _ (s := P)]
  · simp_rw [hBC, Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p hp ↦ by rw [hAB p hp, Finset.sum_mul]
  · exact Function.support_subset_iff'.mpr <| by simp +contextual [P]
  · exact Function.support_subset_iff'.mpr fun j hj ↦ by
      rw [hBC, Finset.sum_eq_zero fun p hp ↦ by simp [hS j hj p hp], mul_zero]

end Assoc

private theorem finsum_mul_one_apply [DecidableEq ι] (A : Matrix τ ι R) (i : τ) (k : ι) :
    ∑ᶠ j, A i j * (1 : Matrix ι ι R) j k = A i k := by
  rw [finsum_eq_single _ k fun j hj ↦ by simp [one_apply_ne hj]]
  simp

private theorem finsum_one_apply_mul [DecidableEq τ] (A : Matrix τ ι R) (i : τ) (k : ι) :
    ∑ᶠ j, (1 : Matrix τ τ R) i j * A j k = A i k := by
  rw [finsum_eq_single _ i fun j hj ↦ by simp [one_apply_ne' hj]]
  simp

variable [DecidableEq ι] [DecidableEq τ]

/-- A column-finite matrix has at most one cofinite inverse. -/
theorem IsCofiniteInverse.eq {K K' : Matrix τ ι R} {J : Matrix ι τ R}
    (hJ : ∀ k, {j | J j k ≠ 0}.Finite) (hK : IsCofiniteInverse K J)
    (hK' : IsCofiniteInverse K' J) : K = K' := by
  ext i k
  have h := finsum_mul_finsum_assoc K hJ hK'.col_finite i k
  simp_rw [hK'.mul_right, hK.mul_left, finsum_mul_one_apply, finsum_one_apply_mul] at h
  exact h

/-- If `K` is a cofinite inverse of the column-finite matrix `J`, then `J` is a cofinite inverse
of `K`. -/
theorem IsCofiniteInverse.symm {K : Matrix τ ι R} {J : Matrix ι τ R}
    (hJ : ∀ k, {j | J j k ≠ 0}.Finite) (hK : IsCofiniteInverse K J) : IsCofiniteInverse J K :=
  ⟨hJ, hK.mul_right, hK.mul_left⟩

/-- `J` has a cofinite inverse. If `J` is column-finite, the inverse is unique
(`Matrix.IsCofiniteInvertible.existsUnique`). -/
def IsCofiniteInvertible (J : Matrix ι τ R) : Prop :=
  ∃ K : Matrix τ ι R, IsCofiniteInverse K J

theorem IsCofiniteInverse.isCofiniteInvertible {K : Matrix τ ι R} {J : Matrix ι τ R}
    (hK : IsCofiniteInverse K J) : J.IsCofiniteInvertible :=
  ⟨K, hK⟩

/-- A column-finite matrix with a cofinite inverse has exactly one. -/
theorem IsCofiniteInvertible.existsUnique {J : Matrix ι τ R}
    (hJ : ∀ k, {j | J j k ≠ 0}.Finite) (h : J.IsCofiniteInvertible) :
    ∃! K : Matrix τ ι R, IsCofiniteInverse K J :=
  let ⟨K, hK⟩ := h
  ⟨K, hK, fun _ hK' ↦ hK'.eq hJ hK⟩

/-- The only cofinite inverse of `1` is `1`. -/
@[simp]
theorem isCofiniteInverse_one_iff {K : Matrix τ τ R} : IsCofiniteInverse K 1 ↔ K = 1 :=
  ⟨fun hK ↦ hK.eq IsCofiniteInverse.one.col_finite .one, fun hK ↦ hK ▸ .one⟩

/-! ### Finite index types -/

section Finite

variable {R : Type*} [CommRing R] [Fintype τ] {K J : Matrix τ τ R}

/-- For a finite index type, a cofinite inverse is a left inverse in `Matrix τ τ R`. -/
theorem IsCofiniteInverse.mul_eq_one (hK : IsCofiniteInverse K J) : K * J = 1 := by
  ext i k
  rw [mul_apply, ← finsum_eq_sum_of_fintype]
  exact hK.mul_left i k

theorem IsCofiniteInverse.isUnit_det (hK : IsCofiniteInverse K J) : IsUnit J.det :=
  isUnit_det_of_left_inverse hK.mul_eq_one

/-- For a finite index type, `J` has a cofinite inverse if and only if its determinant is a
unit. -/
theorem isCofiniteInvertible_iff_isUnit_det : J.IsCofiniteInvertible ↔ IsUnit J.det :=
  ⟨fun ⟨_, hK⟩ ↦ hK.isUnit_det,
    fun hJ ↦ (IsCofiniteInverse.of_isUnit_det hJ).isCofiniteInvertible⟩

/-- For a finite index type, every cofinite inverse is the nonsingular inverse. -/
theorem IsCofiniteInverse.eq_nonsing_inv (hK : IsCofiniteInverse K J) : K = J⁻¹ :=
  hK.eq (fun _ ↦ Set.toFinite _) (.of_isUnit_det hK.isUnit_det)

end Finite

end Matrix
