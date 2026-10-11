/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import MvFormalGroup.ForMathlib.MvPowerSeries.Substitution
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
# The formal implicit function theorem

For a finite system of formal power series `F(X, Y)` over a commutative ring,
an invertible matrix of linear `Y` coefficients gives a unique solution
`Y = α(X)` with zero constant coefficients.

`implicitApprox` iterates `a ↦ a - J⁻¹ F(X, a)` from zero. The coefficients
of these approximations stabilize and define `implicitFunction`. We prove that
this function solves the system, then prove uniqueness and deduce
`existsUnique_implicitFunction`.

Swapping the variable blocks gives `implicitFunctionLeft` and
`existsUnique_implicitFunctionLeft`, which solve `F(α(X), X) = 0`.

The two variable blocks are indexed by `σ ⊕ τ`, and the equations by `τ`.
The zero-constant-term condition on the solution is essential: uniqueness is
asserted for formal solutions through the origin.
-/

@[expose] public section

noncomputable section

open Finsupp Function

namespace MvPowerSeries

variable {R : Type*} [CommRing R] {σ τ : Type*}

/-- The coefficientwise limit of successive approximations starting at zero. -/
private def fixedPoint (T : (τ → MvPowerSeries σ R) → τ → MvPowerSeries σ R)
    (i : τ) : MvPowerSeries σ R :=
  fun d ↦ coeff d ((T^[d.degree + 1]) 0 i)

section FixedPoint

variable [Finite σ]
    (T : (τ → MvPowerSeries σ R) → τ → MvPowerSeries σ R)
    (hzero : ∀ a, (∀ i, constantCoeff (a i) = 0) → ∀ i, constantCoeff (T a i) = 0)
    (hT : ∀ n a b, (∀ i, constantCoeff (a i) = 0) →
      (∀ i, constantCoeff (b i) = 0) →
      (∀ i, (a i).truncTotal n = (b i).truncTotal n) →
      ∀ i, (T a i).truncTotal (n + 1) = (T b i).truncTotal (n + 1))

omit [Finite σ] in
include hzero in
private theorem constantCoeff_iterate (n : ℕ) (i : τ) :
    constantCoeff ((T^[n]) 0 i) = 0 := by
  induction n generalizing i with
  | zero => simp
  | succ n ih => exact iterate_succ_apply' T n 0 ▸ hzero _ ih i

include hzero hT in
private theorem truncTotal_fixedPoint (n : ℕ) (i : τ) :
    (fixedPoint T i).truncTotal n = ((T^[n]) 0 i).truncTotal n := by
  have h (m k : ℕ) (j : τ) : ((T^[m + k]) 0 j).truncTotal k = ((T^[k]) 0 j).truncTotal k := by
    induction k generalizing j with
    | zero =>
      ext d
      simp [coeff_truncTotal_eq_zero _ (Nat.zero_le _)]
    | succ k ih =>
      simpa [← add_assoc, iterate_succ_apply'] using hT k _ _
        (constantCoeff_iterate T hzero _) (constantCoeff_iterate T hzero k) ih j
  refine truncTotal_eq_iff.mpr fun d hd ↦ ?_
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hd
  exact (truncTotal_eq_iff.mp (h m _ i) d (lt_add_one _)).symm

omit [Finite σ] in
include hzero in
private theorem constantCoeff_fixedPoint (i : τ) : constantCoeff (fixedPoint T i) = 0 := by
  simpa [fixedPoint, ← coeff_zero_eq_constantCoeff_apply, coeff_apply] using
    constantCoeff_iterate T hzero 1 i

include hzero hT in
private theorem map_fixedPoint : T (fixedPoint T) = fixedPoint T := by
  ext i d
  have h := hT _ _ _ (constantCoeff_fixedPoint T hzero) (constantCoeff_iterate T hzero _)
    (truncTotal_fixedPoint T hzero hT d.degree) i
  rw [← iterate_succ_apply' T, ← truncTotal_fixedPoint T hzero hT] at h
  exact truncTotal_eq_iff.mp h d (lt_add_one _)

include hzero hT in
private theorem eq_fixedPoint (b : τ → MvPowerSeries σ R)
    (hb0 : ∀ i, constantCoeff (b i) = 0) (hbfix : T b = b) : b = fixedPoint T := by
  have heq (n : ℕ) (i : τ) : (b i).truncTotal n = (fixedPoint T i).truncTotal n := by
    induction n generalizing i with
    | zero => ext d; simp only [coeff_truncTotal_eq_zero _ (Nat.zero_le _)]
    | succ n ih =>
      simpa only [hbfix, map_fixedPoint T hzero hT] using
        hT n b (fixedPoint T) hb0 (constantCoeff_fixedPoint T hzero) ih i
  ext i d
  exact truncTotal_eq_iff.mp (heq _ i) d (lt_add_one _)

end FixedPoint

private theorem constantCoeff_elim_X {a : τ → MvPowerSeries σ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (j : σ ⊕ τ) : constantCoeff (Sum.elim X a j) = 0 := by
  cases j <;> simp [ha]

/-- The matrix of coefficients of the linear terms in the `Y` variables. -/
def implicitJacobian (F : τ → MvPowerSeries (σ ⊕ τ) R) : Matrix τ τ R :=
  fun i j ↦ coeff (single (Sum.inr j) 1) (F i)

/-- The matrix of coefficients of the linear terms in the first variable block. -/
def implicitJacobianLeft (F : τ → MvPowerSeries (τ ⊕ σ) R) : Matrix τ τ R :=
  fun i j ↦ coeff (single (Sum.inl j) 1) (F i)

/-- Swapping the variable blocks turns the left Jacobian into the right Jacobian. -/
@[simp]
theorem implicitJacobian_rename_sumComm (F : τ → MvPowerSeries (τ ⊕ σ) R) :
    implicitJacobian (fun i ↦ rename (Equiv.sumComm τ σ) (F i)) =
      implicitJacobianLeft F := by
  ext i j
  simpa [implicitJacobian, implicitJacobianLeft] using
    coeff_embDomain_rename (Equiv.sumComm τ σ).toEmbedding (F i) (single (Sum.inl j) 1)

private theorem subst_rename_sumComm [Finite σ] [Finite τ] (f : MvPowerSeries (τ ⊕ σ) R)
    (a : τ → MvPowerSeries σ R) (ha : ∀ i, constantCoeff (a i) = 0) :
    (rename (Equiv.sumComm τ σ) f).subst (Sum.elim X a) =
      f.subst (Sum.elim a X) := by
  have hs := hasSubst_of_constantCoeff_zero (constantCoeff_elim_X ha)
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) hs]
  congr 1
  ext (j | j) : 1 <;> simp [subst_X hs]

section Matrix

variable [Finite σ] [Fintype τ] [DecidableEq τ]

/-- The fixed-point system `Y - J⁻¹ F(X, Y)`. -/
private def implicitSystem (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (J : (Matrix τ τ R)ˣ) (i : τ) : MvPowerSeries (σ ⊕ τ) R :=
  X (Sum.inr i) - ∑ j, (↑J⁻¹ : Matrix τ τ R) i j • F j

private theorem constantCoeff_subst_implicitSystem (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (J : (Matrix τ τ R)ˣ) (hF : ∀ i, constantCoeff (F i) = 0) (a : τ → MvPowerSeries σ R)
    (ha : ∀ i, constantCoeff (a i) = 0) (i : τ) :
    constantCoeff ((implicitSystem F J i).subst (Sum.elim X a)) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (constantCoeff_elim_X ha))
    (constantCoeff_elim_X ha) (by simp [implicitSystem, hF])

private theorem subst_implicitSystem (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (J : (Matrix τ τ R)ˣ) (a : τ → MvPowerSeries σ R)
    (ha : ∀ i, constantCoeff (a i) = 0) (i : τ) :
    (implicitSystem F J i).subst (Sum.elim X a) =
      a i - ∑ j, (↑J⁻¹ : Matrix τ τ R) i j • (F j).subst (Sum.elim X a) := by
  simp only [implicitSystem, ← substAlgHom_apply (hasSubst_of_constantCoeff_zero
    (constantCoeff_elim_X ha)), map_sub, map_sum, AlgHom.map_smul_of_tower, substAlgHom_X,
    Sum.elim_inr]

omit [Finite σ] in
private theorem implicitSystem_coeff (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (J : (Matrix τ τ R)ˣ) (hJ : ↑J = implicitJacobian F) (i j : τ) :
    coeff (single (Sum.inr j) 1) (implicitSystem F J i) = 0 := by
  classical
  simp only [implicitSystem, map_sub, map_sum, map_smul, smul_eq_mul, coeff_index_single_X]
  have hmul : (∑ k, (↑J⁻¹ : Matrix τ τ R) i k * coeff (single (Sum.inr j) 1) (F k)) =
      (1 : Matrix τ τ R) i j := by rw [← J.inv_val, hJ]; rfl
  rw [hmul]
  simp [Matrix.one_apply, eq_comm]

omit [Finite σ] in
private theorem matrix_smul_eq_zero (J : (Matrix τ τ R)ˣ)
    (v : τ → MvPowerSeries σ R)
    (h : ∀ i, ∑ j, (↑J : Matrix τ τ R) i j • v j = 0) : ∀ i, v i = 0 := by
  intro i
  ext d
  have hz : (fun j ↦ coeff d (v j)) = 0 := Matrix.mulVec_injective_of_isUnit J.isUnit <| by
    rw [Matrix.mulVec_zero]
    funext j
    simpa [Matrix.mulVec, dotProduct] using congrArg (coeff d) (h j)
  exact congrFun hz i

private theorem implicitSystem_subst_iff (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (J : (Matrix τ τ R)ˣ) (a : τ → MvPowerSeries σ R)
    (ha : ∀ i, constantCoeff (a i) = 0) :
    (fun i ↦ (implicitSystem F J i).subst (Sum.elim X a)) = a ↔
      ∀ i, (F i).subst (Sum.elim X a) = 0 := by
  simp only [funext_iff, subst_implicitSystem F J a ha, sub_eq_self]
  exact ⟨matrix_smul_eq_zero J⁻¹ _, fun h i ↦ by simp [h]⟩

/-- The `n`th successive approximation to the implicit function, starting at zero
and iterating `a ↦ a - J⁻¹ F(X, a)`, where `J` is the implicit Jacobian. -/
def implicitApprox (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hJ : IsUnit (implicitJacobian F)) (n : ℕ) : τ → MvPowerSeries σ R :=
  ((fun a i ↦ (X (Sum.inr i) - ∑ j,
    (↑hJ.unit⁻¹ : Matrix τ τ R) i j • F j).subst (Sum.elim X a))^[n]) 0

omit [Finite σ] in
@[simp]
theorem implicitApprox_zero (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hJ : IsUnit (implicitJacobian F)) : implicitApprox F hJ 0 = 0 := rfl

@[simp]
theorem constantCoeff_implicitApprox (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobian F))
    (n : ℕ) (i : τ) : constantCoeff (implicitApprox F hJ n i) = 0 :=
  constantCoeff_iterate _ (constantCoeff_subst_implicitSystem F hJ.unit hF) n i

private theorem truncTotal_subst_implicitSystem (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hJ : IsUnit (implicitJacobian F)) (n : ℕ) (a b : τ → MvPowerSeries σ R)
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0)
    (h : ∀ i, (a i).truncTotal n = (b i).truncTotal n) (i : τ) :
    ((implicitSystem F hJ.unit i).subst (Sum.elim X a)).truncTotal (n + 1) =
      ((implicitSystem F hJ.unit i).subst (Sum.elim X b)).truncTotal (n + 1) :=
  truncTotal_subst_sum_succ _ (implicitSystem_coeff F hJ.unit hJ.unit_spec i)
    (fun j ↦ constantCoeff_X j) ha hb h

/-- Each step corrects the current approximation using the inverse Jacobian. -/
theorem implicitApprox_succ (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobian F))
    (n : ℕ) (i : τ) :
    implicitApprox F hJ (n + 1) i = implicitApprox F hJ n i -
      ∑ j, (↑hJ.unit⁻¹ : Matrix τ τ R) i j •
        (F j).subst (Sum.elim X (implicitApprox F hJ n)) := by
  rw [implicitApprox, iterate_succ_apply']
  exact subst_implicitSystem F hJ.unit _ (constantCoeff_implicitApprox F hF hJ n) i

/-- The formal solution is constructed coefficientwise: a coefficient of degree `d`
is taken from the `(d + 1)`st successive approximation. -/
def implicitFunction (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (_hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobian F)) :
    τ → MvPowerSeries σ R :=
  fun i d ↦ coeff d (implicitApprox F hJ (d.degree + 1) i)

omit [Finite σ] in
/-- Each coefficient of the implicit function is obtained after finitely many iterations. -/
theorem coeff_implicitFunction (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobian F))
    (i : τ) (d : σ →₀ ℕ) :
    coeff d (implicitFunction F hF hJ i) =
      coeff d (implicitApprox F hJ (d.degree + 1) i) :=
  coeff_apply (implicitFunction F hF hJ i) d

/-- The `n`th approximation agrees with the implicit function in degrees below `n`. -/
theorem truncTotal_implicitFunction (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobian F))
    (n : ℕ) (i : τ) :
    (implicitFunction F hF hJ i).truncTotal n = (implicitApprox F hJ n i).truncTotal n :=
  truncTotal_fixedPoint _ (constantCoeff_subst_implicitSystem F hJ.unit hF)
    (truncTotal_subst_implicitSystem F hJ) n i

@[simp]
theorem constantCoeff_implicitFunction (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobian F)) (i : τ) :
    constantCoeff (implicitFunction F hF hJ i) = 0 :=
  constantCoeff_fixedPoint _ (constantCoeff_subst_implicitSystem F hJ.unit hF) i

/-- Substitution of the implicit function is defined. -/
theorem hasSubst_implicitFunction (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobian F)) :
    HasSubst (Sum.elim X (implicitFunction F hF hJ)) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_elim_X (constantCoeff_implicitFunction F hF hJ))

/-- The implicit function solves the original system of equations. -/
@[simp]
theorem subst_implicitFunction (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobian F)) (i : τ) :
    (F i).subst (Sum.elim X (implicitFunction F hF hJ)) = 0 :=
  (implicitSystem_subst_iff F hJ.unit _ (constantCoeff_implicitFunction F hF hJ)).mp
    (map_fixedPoint _ (constantCoeff_subst_implicitSystem F hJ.unit hF)
      (truncTotal_subst_implicitSystem F hJ)) i

/-- Any zero-constant-term solution is the implicit function. -/
theorem eq_implicitFunction (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobian F))
    (a : τ → MvPowerSeries σ R) (ha0 : ∀ i, constantCoeff (a i) = 0)
    (ha : ∀ i, (F i).subst (Sum.elim X a) = 0) : a = implicitFunction F hF hJ :=
  eq_fixedPoint _ (constantCoeff_subst_implicitSystem F hJ.unit hF)
    (truncTotal_subst_implicitSystem F hJ) a ha0 ((implicitSystem_subst_iff F hJ.unit a ha0).mpr ha)

/-- **Formal implicit function theorem** over a commutative ring.

If `F(0, 0) = 0` and its matrix of linear `Y` coefficients is invertible, there
is a unique tuple `α(X)` with `α(0) = 0` and `F(X, α(X)) = 0`.
No topology on the coefficient ring, field hypothesis, or characteristic
assumption is required. -/
theorem existsUnique_implicitFunction (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobian F)) :
    ∃! a : τ → MvPowerSeries σ R,
      (∀ i, constantCoeff (a i) = 0) ∧
      (∀ i, (F i).subst (Sum.elim X a) = 0) :=
  ⟨_, ⟨constantCoeff_implicitFunction F hF hJ, subst_implicitFunction F hF hJ⟩,
    fun a h ↦ eq_implicitFunction F hF hJ a h.1 h.2⟩

/-- A determinant formulation of the formal implicit function theorem. -/
theorem existsUnique_implicitFunction_of_isUnit_det (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobian F).det) :
    ∃! a : τ → MvPowerSeries σ R,
      (∀ i, constantCoeff (a i) = 0) ∧
      (∀ i, (F i).subst (Sum.elim X a) = 0) :=
  existsUnique_implicitFunction F hF ((Matrix.isUnit_iff_isUnit_det _).mpr hJ)

/-! ## Solving for the first variable block -/

/-- The solution of `F(α(X), X) = 0`, constructed by applying `implicitFunction`
to the system with its two variable blocks exchanged. -/
def implicitFunctionLeft (F : τ → MvPowerSeries (τ ⊕ σ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobianLeft F)) :
    τ → MvPowerSeries σ R :=
  implicitFunction (fun i ↦ rename (Equiv.sumComm τ σ) (F i))
    (by simpa only [constantCoeff_rename] using hF)
    (by simpa only [implicitJacobian_rename_sumComm] using hJ)

@[simp]
theorem constantCoeff_implicitFunctionLeft (F : τ → MvPowerSeries (τ ⊕ σ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobianLeft F)) (i : τ) :
    constantCoeff (implicitFunctionLeft F hF hJ i) = 0 :=
  constantCoeff_implicitFunction _ _ _ i

/-- Substitution of the left implicit function is defined. -/
theorem hasSubst_implicitFunctionLeft (F : τ → MvPowerSeries (τ ⊕ σ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobianLeft F)) :
    HasSubst (Sum.elim (implicitFunctionLeft F hF hJ) X) :=
  hasSubst_of_constantCoeff_zero <| by rintro (i | i) <;> simp

/-- The left implicit function solves `F(α(X), X) = 0`. -/
@[simp]
theorem subst_implicitFunctionLeft (F : τ → MvPowerSeries (τ ⊕ σ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobianLeft F)) (i : τ) :
    (F i).subst (Sum.elim (implicitFunctionLeft F hF hJ) X) = 0 :=
  (subst_rename_sumComm _ _ (constantCoeff_implicitFunctionLeft F hF hJ)).symm.trans
    (subst_implicitFunction _ _ _ i)

/-- Any zero-constant-term solution of `F(a(X), X) = 0` is the left implicit function. -/
theorem eq_implicitFunctionLeft (F : τ → MvPowerSeries (τ ⊕ σ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobianLeft F))
    (a : τ → MvPowerSeries σ R) (ha0 : ∀ i, constantCoeff (a i) = 0)
    (ha : ∀ i, (F i).subst (Sum.elim a X) = 0) : a = implicitFunctionLeft F hF hJ :=
  eq_implicitFunction _ _ _ a ha0 fun i ↦ (subst_rename_sumComm _ _ ha0).trans (ha i)

/-- **Formal implicit function theorem**, solving for the first variable block.
Invertibility of its linear coefficient matrix gives a unique zero-constant-term
solution of `F(α(X), X) = 0`. -/
theorem existsUnique_implicitFunctionLeft (F : τ → MvPowerSeries (τ ⊕ σ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobianLeft F)) :
    ∃! a : τ → MvPowerSeries σ R,
      (∀ i, constantCoeff (a i) = 0) ∧
      (∀ i, (F i).subst (Sum.elim a X) = 0) :=
  ⟨_, ⟨constantCoeff_implicitFunctionLeft F hF hJ, subst_implicitFunctionLeft F hF hJ⟩,
    fun a h ↦ eq_implicitFunctionLeft F hF hJ a h.1 h.2⟩

/-- A determinant formulation of the implicit function theorem for the first variable block. -/
theorem existsUnique_implicitFunctionLeft_of_isUnit_det (F : τ → MvPowerSeries (τ ⊕ σ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobianLeft F).det) :
    ∃! a : τ → MvPowerSeries σ R,
      (∀ i, constantCoeff (a i) = 0) ∧
      (∀ i, (F i).subst (Sum.elim a X) = 0) :=
  existsUnique_implicitFunctionLeft F hF ((Matrix.isUnit_iff_isUnit_det _).mpr hJ)

end Matrix

end MvPowerSeries
