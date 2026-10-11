/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import MvFormalGroup.ForMathlib.FormalGroup.Basic
public import MvFormalGroup.ForMathlib.MvFormalGroup.Hom

/-!
# Homomorphisms of one-dimensional formal group laws

For one-dimensional formal group laws `F` and `G`, `FormalGroup.Hom F G` is
`MvFormalGroup.Hom F G`. Its unique coordinate `f.toPowerSeries : R⟦X⟧` is a power series
`f(T)` without constant term satisfying `f(F(X, Y)) = G(f(X), f(Y))`
(`FormalGroup.Hom.map_add`). Conversely, `FormalGroup.Hom.mk'` builds a homomorphism from such
a power series.

Identity, composition and the zero homomorphism come from `MvFormalGroup.Hom`. In terms of
power series they are `T`, substitution and `0`.
-/

@[expose] public section

noncomputable section

open MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R]

/-- A homomorphism of one-dimensional formal group laws. -/
abbrev Hom (F G : FormalGroup R) := MvFormalGroup.Hom F G

/-- Substitution into `F(X, Y)` is substitution into the underlying one-coordinate law. -/
private theorem subst_toPowerSeries_eq (F : FormalGroup R) {τ : Type*}
    {c : Fin 2 → MvPowerSeries τ R} (hc : HasSubst c) :
    F.toPowerSeries.subst c =
      (MvFormalGroup.toPowerSeries F ()).subst (fun p : Fin 2 × Unit ↦ c p.1) := by
  change (rename (Equiv.prodUnique (Fin 2) Unit) (MvFormalGroup.toPowerSeries F ())).subst c = _
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) hc]
  simp only [Function.comp_apply, subst_X hc]
  rfl

namespace Hom

variable {F G H : FormalGroup R}

/-- The power series `f(T)` of a homomorphism `f`. -/
def toPowerSeries (f : Hom F G) : PowerSeries R := MvFormalGroup.Hom.toPowerSeries f ()

@[ext]
theorem ext {f g : Hom F G} (h : f.toPowerSeries = g.toPowerSeries) : f = g :=
  MvFormalGroup.Hom.ext_apply fun _ ↦ h

@[simp]
theorem constantCoeff_toPowerSeries (f : Hom F G) :
    PowerSeries.constantCoeff f.toPowerSeries = 0 :=
  f.zero_constantCoeff ()

/-- The power series of a homomorphism is admissible for substitution. -/
theorem hasSubst (f : Hom F G) : PowerSeries.HasSubst f.toPowerSeries :=
  .of_constantCoeff_zero' f.constantCoeff_toPowerSeries

private theorem hasSubst_subst_X (f : PowerSeries R) (hf : PowerSeries.constantCoeff f = 0)
    (i : Fin 2) : PowerSeries.HasSubst (f.subst (X i : MvPowerSeries (Fin 2) R)) :=
  .of_constantCoeff_zero (PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) f hf)

/-- A homomorphism satisfies `f(F(X, Y)) = G(f(X), f(Y))`. -/
theorem map_add (f : Hom F G) :
    f.toPowerSeries.subst F.toPowerSeries =
      G.toPowerSeries.subst ![f.toPowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R),
        f.toPowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R)] := by
  have ha : HasSubst (fun p : Fin 2 × Unit ↦ (X p.1 : MvPowerSeries (Fin 2) R)) :=
    hasSubst_of_constantCoeff_zero fun _ ↦ constantCoeff_X _
  have hx := hasSubst_subst_X _ f.constantCoeff_toPowerSeries
  have hF : F.toPowerSeries = (MvFormalGroup.toPowerSeries F ()).subst
      (fun p : Fin 2 × Unit ↦ (X p.1 : MvPowerSeries (Fin 2) R)) := by
    rw [← subst_toPowerSeries_eq F (c := X) (hasSubst_of_constantCoeff_zero constantCoeff_X)]
    exact (congrFun subst_self _).symm
  rw [subst_toPowerSeries_eq G (FormalGroup.hasSubst_pair (hx 0) (hx 1)), hF]
  refine (MvFormalGroup.Hom.map_add_subst f ha ()).trans ?_
  congr 1
  funext p
  fin_cases p <;> rfl

/-- Build a homomorphism from a power series `f` without constant term satisfying
`f(F(X, Y)) = G(f(X), f(Y))`. -/
def mk' (f : PowerSeries R) (hf : PowerSeries.constantCoeff f = 0)
    (hadd : f.subst F.toPowerSeries =
      G.toPowerSeries.subst ![f.subst (X 0 : MvPowerSeries (Fin 2) R),
        f.subst (X 1 : MvPowerSeries (Fin 2) R)]) : Hom F G where
  toPowerSeries _ := f
  zero_constantCoeff _ := hf
  map_add _ := by
    -- substitute `X i ↦ X (i, ())` into `hadd`
    set b : Fin 2 → MvPowerSeries (Fin 2 × Unit) R := fun i ↦ X (i, ())
    have hb : HasSubst b := hasSubst_of_constantCoeff_zero fun _ ↦ constantCoeff_X _
    have hx := hasSubst_subst_X f hf
    have h := congrArg (subst b) hadd
    have hpair := FormalGroup.hasSubst_pair (hx 0) (hx 1)
    have hc := hpair.comp hb
    simp only [substAlgHom_apply] at hc
    rw [PowerSeries.subst, subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero
        F.zero_constantCoeff).const hb, subst_comp_subst_apply hpair hb,
      subst_toPowerSeries_eq G hc, subst_toPowerSeries_eq F hb] at h
    have hF : (MvFormalGroup.toPowerSeries F ()).subst (fun p : Fin 2 × Unit ↦ b p.1) =
        MvFormalGroup.toPowerSeries F () :=
      congrFun subst_self _
    rw [hF] at h
    refine h.trans ?_
    congr 1
    funext p
    fin_cases p <;>
      exact (subst_comp_subst_apply (PowerSeries.HasSubst.X _).const hb f).trans
        (by congr 1; funext _; exact subst_X hb _)

@[simp]
theorem toPowerSeries_mk' (f : PowerSeries R) (hf hadd) :
    (mk' (F := F) (G := G) f hf hadd).toPowerSeries = f :=
  rfl

/-- The identity homomorphism, given by the power series `T`. -/
abbrev id (F : FormalGroup R) : Hom F F := MvFormalGroup.Hom.id F

/-- Composition of homomorphisms, with `g.comp f` representing `g ∘ f`. -/
abbrev comp (g : Hom G H) (f : Hom F G) : Hom F H := MvFormalGroup.Hom.comp g f

@[simp]
theorem toPowerSeries_id : (id F).toPowerSeries = PowerSeries.X :=
  rfl

@[simp]
theorem toPowerSeries_comp (g : Hom G H) (f : Hom F G) :
    (g.comp f).toPowerSeries = g.toPowerSeries.subst f.toPowerSeries :=
  rfl

@[simp]
theorem toPowerSeries_zero : (0 : Hom F G).toPowerSeries = 0 :=
  rfl

@[simp]
theorem id_comp (f : Hom F G) : (id G).comp f = f :=
  MvFormalGroup.Hom.id_comp f

@[simp]
theorem comp_id (f : Hom F G) : f.comp (id F) = f :=
  MvFormalGroup.Hom.comp_id f

theorem comp_assoc {K : FormalGroup R} (h : Hom H K) (g : Hom G H) (f : Hom F G) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  MvFormalGroup.Hom.comp_assoc h g f

end Hom

end FormalGroup
