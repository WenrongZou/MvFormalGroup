/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Pullback of formal one-forms

In a fixed coordinate, we represent `P(T) dT` by its coefficient `P : PowerSeries R`.
`pullbackDifferential g P` represents `g*(P(T) dT) = P(g(X)) g'(X) dX`.
For admissible substitutions this operation is `R`-linear and contravariantly functorial.

For a multivariate series `g`, `pullbackDifferentialCoeff g i P` is the coefficient
of `dXᵢ` in the full pullback `P(g) dg`. It also describes the relative pullback in
which all variables other than `Xᵢ` are held fixed. Taking one such coefficient
does not assert equality of the full multivariate differential forms.

These definitions use formal differentiation and do not require analytic convergence.
They do not identify the coefficient model with ordinary algebraic Kähler differentials.
-/

@[expose] public section

noncomputable section

namespace PowerSeries

variable {R : Type*} [CommRing R] {σ : Type*}

/-- The coefficient of `dXᵢ` in the pullback of `P(T) dT` along a multivariate series `g`. -/
def pullbackDifferentialCoeff (g : MvPowerSeries σ R) (i : σ) (P : PowerSeries R) :
    MvPowerSeries σ R :=
  P.subst g * MvPowerSeries.pderiv i g

@[simp]
theorem pullbackDifferentialCoeff_X_self (i : σ) (P : PowerSeries R) :
    pullbackDifferentialCoeff (MvPowerSeries.X i) i P = P.subst (MvPowerSeries.X i) := by
  simp [pullbackDifferentialCoeff]

@[simp]
theorem pullbackDifferentialCoeff_X_of_ne {i j : σ} (h : j ≠ i) (P : PowerSeries R) :
    pullbackDifferentialCoeff (MvPowerSeries.X j) i P = 0 := by
  simp [pullbackDifferentialCoeff, MvPowerSeries.pderiv_X_of_ne h]

@[simp]
theorem pullbackDifferentialCoeff_zero {g : MvPowerSeries σ R} (hg : HasSubst g) (i : σ) :
    pullbackDifferentialCoeff g i 0 = 0 := by
  simp only [pullbackDifferentialCoeff, ← coe_substAlgHom hg, map_zero, zero_mul]

@[simp]
theorem pullbackDifferentialCoeff_add {g : MvPowerSeries σ R} (hg : HasSubst g) (i : σ)
    (P Q : PowerSeries R) :
    pullbackDifferentialCoeff g i (P + Q) =
      pullbackDifferentialCoeff g i P + pullbackDifferentialCoeff g i Q := by
  simp only [pullbackDifferentialCoeff, subst_add hg, add_mul]

@[simp]
theorem pullbackDifferentialCoeff_smul {g : MvPowerSeries σ R} (hg : HasSubst g) (i : σ)
    (r : R) (P : PowerSeries R) :
    pullbackDifferentialCoeff g i (r • P) = r • pullbackDifferentialCoeff g i P := by
  simp only [pullbackDifferentialCoeff, subst_smul hg, smul_mul_assoc]

/-- A component of formal pullback, as an `R`-linear map on coefficients of one-forms. -/
def pullbackDifferentialCoeffLinearMap (g : MvPowerSeries σ R) (hg : HasSubst g) (i : σ) :
    PowerSeries R →ₗ[R] MvPowerSeries σ R where
  toFun := pullbackDifferentialCoeff g i
  map_add' := pullbackDifferentialCoeff_add hg i
  map_smul' := pullbackDifferentialCoeff_smul hg i

@[simp]
theorem pullbackDifferentialCoeffLinearMap_apply (g : MvPowerSeries σ R) (hg : HasSubst g)
    (i : σ) (P : PowerSeries R) :
    pullbackDifferentialCoeffLinearMap g hg i P = pullbackDifferentialCoeff g i P := rfl

/-- The coefficient of the formal pullback `g*(P(T) dT) = P(g(X)) g'(X) dX`. -/
def pullbackDifferential (g P : PowerSeries R) : PowerSeries R :=
  P.subst g * derivative g

/-- In one variable, the sole component is the coefficient of the pulled-back one-form. -/
theorem pullbackDifferentialCoeff_unit (g P : PowerSeries R) :
    pullbackDifferentialCoeff g () P = pullbackDifferential g P := rfl

@[simp]
theorem pullbackDifferential_X (P : PowerSeries R) : pullbackDifferential X P = P := by
  simp only [pullbackDifferential, derivative_X, mul_one, PowerSeries.subst,
    show (fun _ : Unit ↦ (X : PowerSeries R)) = MvPowerSeries.X by
      funext ⟨⟩; rfl, MvPowerSeries.subst_self, id_eq]

@[simp]
theorem pullbackDifferential_zero {g : PowerSeries R} (hg : HasSubst g) :
    pullbackDifferential g 0 = 0 :=
  pullbackDifferentialCoeff_zero hg ()

@[simp]
theorem pullbackDifferential_one {g : PowerSeries R} (hg : HasSubst g) :
    pullbackDifferential g 1 = derivative g := by
  simp only [pullbackDifferential, ← coe_substAlgHom hg, map_one, one_mul]

@[simp]
theorem pullbackDifferential_add {g : PowerSeries R} (hg : HasSubst g) (P Q : PowerSeries R) :
    pullbackDifferential g (P + Q) = pullbackDifferential g P + pullbackDifferential g Q :=
  pullbackDifferentialCoeff_add hg () P Q

@[simp]
theorem pullbackDifferential_smul {g : PowerSeries R} (hg : HasSubst g) (r : R)
    (P : PowerSeries R) :
    pullbackDifferential g (r • P) = r • pullbackDifferential g P :=
  pullbackDifferentialCoeff_smul hg () r P

/-- Formal pullback as an `R`-linear map on coefficients of one-forms. -/
def pullbackDifferentialLinearMap (g : PowerSeries R) (hg : HasSubst g) :
    PowerSeries R →ₗ[R] PowerSeries R :=
  pullbackDifferentialCoeffLinearMap g hg ()

@[simp]
theorem pullbackDifferentialLinearMap_apply (g : PowerSeries R) (hg : HasSubst g)
    (P : PowerSeries R) :
    pullbackDifferentialLinearMap g hg P = pullbackDifferential g P := rfl

/-- Pullback reverses composition: `h* (g* ω) = (g ∘ h)* ω`. -/
theorem pullbackDifferential_comp {g h : PowerSeries R} (hg : HasSubst g) (hh : HasSubst h)
    (P : PowerSeries R) :
    pullbackDifferential h (pullbackDifferential g P) =
      pullbackDifferential (g.subst h) P := by
  simp only [pullbackDifferential, subst_mul hh, subst_comp_subst_apply hg hh,
    derivative_subst hh, mul_assoc]

/-- The differential of a substituted series is the pullback of its differential. -/
theorem pullbackDifferential_derivative {g : PowerSeries R} (hg : HasSubst g)
    (P : PowerSeries R) :
    pullbackDifferential g (derivative P) = derivative (P.subst g) :=
  (derivative_subst hg).symm

end PowerSeries
