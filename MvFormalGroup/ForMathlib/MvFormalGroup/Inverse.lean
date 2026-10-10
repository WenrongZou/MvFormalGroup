/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import MvFormalGroup.ForMathlib.MvFormalGroup.Basic
public import MvFormalGroup.ForMathlib.MvPowerSeries.Implicit

/-!
# The inverse series of a multidimensional formal group law

The inverse is the zero-constant-term solution of `F(α(X), X) = 0`, constructed
using `MvPowerSeries.implicitFunctionLeft`. The linear coefficient axioms give
the identity matrix as the Jacobian in the first variable block.

We rename the variables from `Fin 2 × σ` to `σ ⊕ σ` to apply the formal implicit
function theorem. The construction requires neither associativity nor
commutativity. Its main properties are `MvFormalGroup.constantCoeff_inv`,
`MvFormalGroup.inv_left`, and `MvFormalGroup.eq_inv`.
-/

@[expose] public section

noncomputable section

open MvPowerSeries Finsupp Function

namespace MvFormalGroup

variable {R : Type*} [CommRing R] {σ : Type*}

/-- Identify the two blocks of variables with a disjoint sum. -/
private def sumVarsEquiv (σ : Type*) : (Fin 2 × σ) ≃ (σ ⊕ σ) where
  toFun p := if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
  invFun := Sum.elim (fun i ↦ (0, i)) (fun i ↦ (1, i))
  left_inv := by rintro ⟨b, i⟩; fin_cases b <;> simp
  right_inv := by rintro (i | i) <;> simp

variable [Finite σ] [DecidableEq σ]

/-- The group law with variables indexed by `σ ⊕ σ`. -/
private def toSumPowerSeries (F : MvFormalGroup σ R) (i : σ) : MvPowerSeries (σ ⊕ σ) R :=
  rename (sumVarsEquiv σ) (F.toPowerSeries i)

private theorem constantCoeff_toSumPowerSeries (F : MvFormalGroup σ R) (i : σ) :
    constantCoeff (toSumPowerSeries F i) = 0 := by
  simpa only [toSumPowerSeries, constantCoeff_rename] using F.zero_constantCoeff i

private theorem implicitJacobianLeft_toSumPowerSeries (F : MvFormalGroup σ R) :
    implicitJacobianLeft (toSumPowerSeries F) = 1 := by
  ext i j
  have h : coeff (single (Sum.inl j) 1) (toSumPowerSeries F i) =
      coeff (single (0, j) 1) (F.toPowerSeries i) := by
    simpa [sumVarsEquiv, toSumPowerSeries] using
      coeff_embDomain_rename (sumVarsEquiv σ).toEmbedding (F.toPowerSeries i) (single (0, j) 1)
  change coeff (single (Sum.inl j) 1) (toSumPowerSeries F i) = _
  rw [h, F.lin_coeff_X]
  simp [Matrix.one_apply, eq_comm]

private theorem subst_toSumPowerSeries (F : MvFormalGroup σ R)
    (a b : σ → MvPowerSeries σ R)
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) (i : σ) :
    (toSumPowerSeries F i).subst (Sum.elim a b) =
      (F.toPowerSeries i).subst (uncurry ![a, b]) := by
  have hp : ∀ j, constantCoeff (Sum.elim a b j) = 0 := by
    rintro (j | j) <;> simp [ha, hb]
  have hs := hasSubst_of_constantCoeff_zero hp
  rw [toSumPowerSeries, rename_eq_subst,
    subst_comp_subst_apply (HasSubst.X_comp _) hs]
  congr 1
  funext ⟨k, j⟩
  fin_cases k <;> simp [subst_X hs, sumVarsEquiv, uncurry]

/-- The inverse series, constructed by the formal implicit function theorem
applied to the first variable block of the group law. -/
@[no_expose]
def inv (F : MvFormalGroup σ R) : σ → MvPowerSeries σ R := by
  letI := Fintype.ofFinite σ
  exact implicitFunctionLeft (toSumPowerSeries F) (constantCoeff_toSumPowerSeries F)
    (by rw [implicitJacobianLeft_toSumPowerSeries]; exact isUnit_one)

@[simp]
theorem constantCoeff_inv (F : MvFormalGroup σ R) (i : σ) :
    constantCoeff (F.inv i) = 0 := by
  let := Fintype.ofFinite σ
  exact constantCoeff_implicitFunctionLeft _ _ _ i

/-- The inverse coordinates can be substituted into a power series. -/
theorem hasSubst_inv (F : MvFormalGroup σ R) : HasSubst F.inv :=
  hasSubst_of_constantCoeff_zero (constantCoeff_inv F)

/-- The constructed series is a left inverse for the formal group law. -/
theorem inv_left (F : MvFormalGroup σ R) (i : σ) :
    (F.toPowerSeries i).subst (uncurry ![F.inv, X]) = 0 := by
  let := Fintype.ofFinite σ
  rw [← subst_toSumPowerSeries F F.inv X (constantCoeff_inv F) (fun j ↦ constantCoeff_X j)]
  exact subst_implicitFunctionLeft _ _ _ i

/-- Any zero-constant-term left inverse is the constructed inverse series. -/
theorem eq_inv (F : MvFormalGroup σ R) (a : σ → MvPowerSeries σ R)
    (ha0 : ∀ i, constantCoeff (a i) = 0)
    (ha : ∀ i, (F.toPowerSeries i).subst (uncurry ![a, X]) = 0) : a = F.inv := by
  let := Fintype.ofFinite σ
  apply eq_implicitFunctionLeft _ _ _ a ha0
  intro i
  rw [subst_toSumPowerSeries F a X ha0 (fun j ↦ constantCoeff_X j)]
  exact ha i

/-- The inverse of the additive formal group is coordinatewise negation. -/
@[simp]
theorem inv_additive (i : σ) : (additive σ R).inv i = -X i := by
  have hs := hasSubst_pair (constantCoeff_inv (additive σ R))
    (fun j : σ ↦ constantCoeff_X (R := R) j)
  have h := inv_left (additive σ R) i
  change (X (0, i) + X (1, i) : MvPowerSeries (Fin 2 × σ) R).subst
    (uncurry ![(additive σ R).inv, X]) = 0 at h
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [subst_add hs, subst_X hs, uncurry, Matrix.cons_val_zero,
    Matrix.cons_val_one] using h

end MvFormalGroup
