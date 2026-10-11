/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import MvFormalGroup.ForMathlib.MvFormalGroup.Hom

/-!
# Isomorphisms of multidimensional formal group laws

An isomorphism consists of two homomorphisms inverse to each other under
substitution. `Iso.refl`, `Iso.symm`, and `Iso.trans` provide the identity, inverse,
and composition. `e.trans f` means first `e`, then `f`.
-/

@[expose] public section

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {R : Type*} [CommRing R]
variable {σ τ υ ω : Type*}
variable [Finite σ] [DecidableEq σ] [Finite τ] [DecidableEq τ]
variable [Finite υ] [DecidableEq υ] [Finite ω] [DecidableEq ω]

/-- An isomorphism of formal group laws is a pair of mutually inverse homomorphisms. -/
structure Iso (F : MvFormalGroup σ R) (G : MvFormalGroup τ R) where
  /-- The forward homomorphism. -/
  toHom : Hom F G
  /-- The inverse homomorphism. -/
  invHom : Hom G F
  /-- The forward homomorphism is a left inverse to the inverse homomorphism. -/
  hom_inv_id : toHom.comp invHom = Hom.id G
  /-- The inverse homomorphism is a left inverse to the forward homomorphism. -/
  inv_hom_id : invHom.comp toHom = Hom.id F

namespace Iso

variable {F : MvFormalGroup σ R} {G : MvFormalGroup τ R}
variable {H : MvFormalGroup υ R} {K : MvFormalGroup ω R}

instance : Coe (Iso F G) (Hom F G) := ⟨Iso.toHom⟩

instance : CoeFun (Iso F G) (fun _ ↦ τ → MvPowerSeries σ R) := ⟨fun e ↦ e.toHom⟩

/-- An isomorphism is determined by its forward homomorphism. -/
theorem toHom_injective : Function.Injective (toHom : Iso F G → Hom F G) := by
  intro e f h
  have hi : e.invHom = f.invHom := by
    calc
      e.invHom = e.invHom.comp (Hom.id G) := (Hom.comp_id _).symm
      _ = e.invHom.comp (f.toHom.comp f.invHom) := by rw [f.hom_inv_id]
      _ = (e.invHom.comp e.toHom).comp f.invHom := by rw [h, Hom.comp_assoc]
      _ = f.invHom := by rw [e.inv_hom_id, Hom.id_comp]
  cases e
  cases f
  cases h
  cases hi
  rfl

@[ext]
theorem ext {e f : Iso F G} (h : ∀ i, e i = f i) : e = f :=
  toHom_injective (Hom.ext (funext h))

/-- The identity isomorphism. -/
def refl (F : MvFormalGroup σ R) : Iso F F where
  toHom := Hom.id F
  invHom := Hom.id F
  hom_inv_id := Hom.id_comp _
  inv_hom_id := Hom.id_comp _

@[simp]
theorem refl_toHom : (refl F).toHom = Hom.id F := rfl

@[simp]
theorem refl_apply (i : σ) : refl F i = X i := rfl

/-- The inverse isomorphism. -/
def symm (e : Iso F G) : Iso G F where
  toHom := e.invHom
  invHom := e.toHom
  hom_inv_id := e.inv_hom_id
  inv_hom_id := e.hom_inv_id

@[simp]
theorem symm_toHom (e : Iso F G) : e.symm.toHom = e.invHom := rfl

@[simp]
theorem symm_symm (e : Iso F G) : e.symm.symm = e := rfl

@[simp]
theorem symm_refl : (refl F).symm = refl F := rfl

/-- Applying the forward series to the inverse series gives the variables. -/
@[simp]
theorem subst_symm (e : Iso F G) (i : τ) :
    (e i).subst e.symm.toHom.toPowerSeries = X i :=
  congrArg (fun f : Hom G G ↦ f i) e.hom_inv_id

/-- Applying the inverse series to the forward series gives the variables. -/
@[simp]
theorem symm_subst (e : Iso F G) (i : σ) :
    (e.symm i).subst e.toHom.toPowerSeries = X i :=
  congrArg (fun f : Hom F F ↦ f i) e.inv_hom_id

/-- Composition of isomorphisms: first `e`, then `f`. -/
def trans (e : Iso F G) (f : Iso G H) : Iso F H where
  toHom := f.toHom.comp e.toHom
  invHom := e.invHom.comp f.invHom
  hom_inv_id := by
    calc
      (f.toHom.comp e.toHom).comp (e.invHom.comp f.invHom) =
          f.toHom.comp ((e.toHom.comp e.invHom).comp f.invHom) := by
        rw [Hom.comp_assoc, Hom.comp_assoc]
      _ = Hom.id H := by rw [e.hom_inv_id, Hom.id_comp, f.hom_inv_id]
  inv_hom_id := by
    calc
      (e.invHom.comp f.invHom).comp (f.toHom.comp e.toHom) =
          e.invHom.comp ((f.invHom.comp f.toHom).comp e.toHom) := by
        rw [Hom.comp_assoc, Hom.comp_assoc]
      _ = Hom.id F := by rw [f.inv_hom_id, Hom.id_comp, e.inv_hom_id]

@[simp]
theorem trans_toHom (e : Iso F G) (f : Iso G H) :
    (e.trans f).toHom = f.toHom.comp e.toHom := rfl

@[simp]
theorem trans_apply (e : Iso F G) (f : Iso G H) (i : υ) :
    e.trans f i = (f i).subst e.toHom.toPowerSeries := rfl

@[simp]
theorem refl_trans (e : Iso F G) : (refl F).trans e = e :=
  toHom_injective (Hom.comp_id _)

@[simp]
theorem trans_refl (e : Iso F G) : e.trans (refl G) = e :=
  toHom_injective (Hom.id_comp _)

theorem trans_assoc (e : Iso F G) (f : Iso G H) (g : Iso H K) :
    (e.trans f).trans g = e.trans (f.trans g) :=
  toHom_injective (Hom.comp_assoc _ _ _).symm

@[simp]
theorem self_trans_symm (e : Iso F G) : e.trans e.symm = refl F :=
  toHom_injective e.inv_hom_id

@[simp]
theorem symm_trans_self (e : Iso F G) : e.symm.trans e = refl G :=
  toHom_injective e.hom_inv_id

@[simp]
theorem symm_trans (e : Iso F G) (f : Iso G H) :
    (e.trans f).symm = f.symm.trans e.symm := rfl

/-- Composition with an isomorphism on the left can be cancelled. -/
theorem cancel_left (e : Iso G H) {f g : Hom F G}
    (h : e.toHom.comp f = e.toHom.comp g) : f = g := by
  have := congrArg (Hom.comp e.invHom) h
  simpa only [← Hom.comp_assoc, e.inv_hom_id, Hom.id_comp] using this

/-- Composition with an isomorphism on the right can be cancelled. -/
theorem cancel_right (e : Iso F G) {f g : Hom G H}
    (h : f.comp e.toHom = g.comp e.toHom) : f = g := by
  have := congrArg (fun k : Hom F H ↦ k.comp e.invHom) h
  simpa only [Hom.comp_assoc, e.hom_inv_id, Hom.comp_id] using this

end Iso

end MvFormalGroup
