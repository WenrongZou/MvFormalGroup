/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import MvFormalGroup.ForMathlib.FormalGroup.Basic
public import MvFormalGroup.ForMathlib.MvFormalGroup.Inverse

/-!
# The inverse of a one-dimensional formal group law

`FormalGroup.inv` is the unique coordinate of `MvFormalGroup.inv`, viewed as a
one-variable power series. It has zero constant term and satisfies both
`F(inv(X), X) = 0` and `F(X, inv(X)) = 0`. Neither identity requires commutativity.
-/

@[expose] public section

noncomputable section

open MvPowerSeries Function

namespace FormalGroup

variable {R : Type*} [CommRing R]

/-- The inverse series, obtained by specializing the multivariate inverse construction. -/
def inv (F : FormalGroup R) : PowerSeries R := MvFormalGroup.inv F ()

@[simp]
theorem constantCoeff_inv (F : FormalGroup R) : F.inv.constantCoeff = 0 :=
  MvFormalGroup.constantCoeff_inv F ()

/-- The inverse series is admissible for substitution. -/
theorem hasSubst_inv (F : FormalGroup R) : PowerSeries.HasSubst F.inv :=
  .of_constantCoeff_zero' F.constantCoeff_inv

/-- The inverse solves `F(inv(X), X) = 0`. -/
@[simp]
theorem inv_left (F : FormalGroup R) :
    F.toPowerSeries.subst ![F.inv, PowerSeries.X] = 0 :=
  (F.subst_toPowerSeries _ _ F.hasSubst_inv .X').trans (MvFormalGroup.inv_left F ())

/-- A zero-constant-term left inverse equals the constructed inverse. -/
theorem eq_inv (F : FormalGroup R) (a : PowerSeries R)
    (ha0 : PowerSeries.constantCoeff a = 0)
    (ha : F.toPowerSeries.subst ![a, PowerSeries.X] = 0) : a = F.inv :=
  congrFun (MvFormalGroup.eq_inv F (fun _ ↦ a) (fun _ ↦ ha0) fun _ ↦
    (F.subst_toPowerSeries _ _ (.of_constantCoeff_zero' ha0) .X').symm.trans ha) ()

/-- The left inverse equation after any admissible substitution. -/
@[simp]
theorem inv_left_subst {τ : Type*} (F : FormalGroup R) {a : MvPowerSeries τ R}
    (ha : PowerSeries.HasSubst a) : F.toPowerSeries.subst ![F.inv.subst a, a] = 0 := by
  have h := congrArg (subst fun _ : Unit ↦ a) F.inv_left
  rw [subst_comp_subst_apply (hasSubst_pair F.hasSubst_inv .X') ha.const] at h
  convert h using 2
  · funext i
    fin_cases i
    · rfl
    · exact (subst_X ha.const ()).symm
  · rw [← substAlgHom_apply ha.const, map_zero]

/-- Applying the inverse twice gives the original variable. -/
@[simp]
theorem inv_subst_inv (F : FormalGroup R) : F.inv.subst F.inv = PowerSeries.X := by
  have h0 := PowerSeries.constantCoeff_subst_eq_zero F.constantCoeff_inv _ F.constantCoeff_inv
  simpa [F.hasSubst_inv, PowerSeries.HasSubst.of_constantCoeff_zero h0] using
    (F.assoc_subst _ F.inv PowerSeries.X h0 F.constantCoeff_inv (constantCoeff_X ())).symm

/-- The inverse also solves `F(X, inv(X)) = 0`. -/
@[simp]
theorem inv_right (F : FormalGroup R) :
    F.toPowerSeries.subst ![PowerSeries.X, F.inv] = 0 :=
  F.inv_subst_inv ▸ F.inv_left_subst F.hasSubst_inv

/-- The inverse is the unique zero-constant-term solution of the left inverse equation. -/
theorem existsUnique_inv (F : FormalGroup R) :
    ∃! a : PowerSeries R, PowerSeries.constantCoeff a = 0 ∧
      F.toPowerSeries.subst ![a, PowerSeries.X] = 0 :=
  ⟨F.inv, ⟨F.constantCoeff_inv, F.inv_left⟩, fun a h ↦ F.eq_inv a h.1 h.2⟩

/-- The inverse of the additive one-dimensional formal group is `-X`. -/
@[simp]
theorem inv_additive : (additive R).inv = -PowerSeries.X :=
  MvFormalGroup.inv_additive ()

end FormalGroup
