/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import MvFormalGroup.ForMathlib.MvFormalGroup.Basic
public import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
# Homomorphisms of multidimensional formal group laws

A homomorphism `f : Hom F G` is a family of power series, indexed by the coordinates
of `G`, in the variables of `F`. Both index sets may be infinite. Each source monomial
occurs in only finitely many coordinates, its constant coefficients vanish, and it satisfies
`f(F(X, Y)) = G(f(X), f(Y))`. Source and target can have different dimensions.

Composition `g.comp f` is substitution, representing `g ∘ f`. The identity is the
family of variables. No commutativity assumption on either formal group is needed.
-/

@[expose] public section

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {R : Type*} [CommRing R]
variable {σ τ υ ω : Type*}
variable [DecidableEq σ] [DecidableEq τ]
variable [DecidableEq υ] [DecidableEq ω]

/-- A homomorphism of formal group laws over the same coefficient ring. -/
@[ext]
structure Hom (F : MvFormalGroup σ R) (G : MvFormalGroup τ R) where
  /-- The target coordinates, as power series in the source variables. -/
  toPowerSeries : τ → MvPowerSeries σ R
  /-- A homomorphism takes the origin to the origin. -/
  zero_constantCoeff : ∀ i, constantCoeff (toPowerSeries i) = 0
  /-- Each source monomial occurs in only finitely many target coordinates. -/
  coeff_finite d : {i | coeff d (toPowerSeries i) ≠ 0}.Finite
  /-- Compatibility with the formal group laws. -/
  map_add i :
    (toPowerSeries i).subst F.toPowerSeries =
      (G.toPowerSeries i).subst
        (fun p : Fin 2 × τ ↦ (toPowerSeries p.2).subst (fun j ↦ X (p.1, j)))

namespace Hom

variable {F : MvFormalGroup σ R} {G : MvFormalGroup τ R}
variable {H : MvFormalGroup υ R} {K : MvFormalGroup ω R}

instance : CoeFun (Hom F G) (fun _ ↦ τ → MvPowerSeries σ R) := ⟨Hom.toPowerSeries⟩

/-- Homomorphisms are equal when all their coordinate series are equal. -/
@[ext]
theorem ext_apply {f g : Hom F G} (h : ∀ i, f i = g i) : f = g :=
  Hom.ext (funext h)

@[simp]
theorem coe_mk (a h0 hfinite hadd) : ⇑(Hom.mk a h0 hfinite hadd : Hom F G) = a := rfl

@[simp]
theorem constantCoeff_apply (f : Hom F G) (i : τ) : constantCoeff (f i) = 0 :=
  f.zero_constantCoeff i

/-- The coordinate family of a homomorphism is admissible for substitution. -/
theorem hasSubst (f : Hom F G) : HasSubst f.toPowerSeries where
  const_coeff i := by simp [f.zero_constantCoeff]
  coeff_zero := f.coeff_finite

private theorem hasSubst_blocks (f : Hom F G) :
    HasSubst (fun p : Fin 2 × τ ↦ (f p.2).subst (fun j ↦ X (R := R) (p.1, j))) :=
  HasSubst.uncurry (fun b ↦ f.hasSubst.subst (HasSubst.curry_X b))

omit [DecidableEq σ] in
private theorem subst_block {κ : Type*} (b : Fin 2) (f : MvPowerSeries σ R)
    {a : Fin 2 × σ → MvPowerSeries κ R} (ha : HasSubst a) :
    (f.subst (fun j ↦ X (R := R) (b, j))).subst a =
      f.subst (fun j ↦ a (b, j)) := by
  have hb : HasSubst (fun j : σ ↦ X (R := R) (b, j)) := .curry_X b
  rw [subst_comp_subst_apply hb ha]
  simp only [subst_X ha]

omit [DecidableEq σ] in
private theorem subst_X_block (b : Fin 2) (i : σ) :
    (X i : MvPowerSeries σ R).subst (fun j ↦ X (R := R) (b, j)) = X (b, i) :=
  subst_X (HasSubst.curry_X b) i

/-- The homomorphism identity remains valid after any admissible substitution
for the two blocks of source variables. -/
theorem map_add_subst (f : Hom F G) {κ : Type*}
    {a : Fin 2 × σ → MvPowerSeries κ R} (ha : HasSubst a) (i : τ) :
    (f i).subst (fun j ↦ (F.toPowerSeries j).subst a) =
      (G.toPowerSeries i).subst
        (fun p : Fin 2 × τ ↦ (f p.2).subst (fun j ↦ a (p.1, j))) := by
  have h := congrArg (subst a) (f.map_add i)
  rw [subst_comp_subst_apply F.hasSubst ha,
    subst_comp_subst_apply f.hasSubst_blocks ha] at h
  simpa only [subst_block _ _ ha] using h

/-- The identity homomorphism. -/
def id (F : MvFormalGroup σ R) : Hom F F where
  toPowerSeries := X
  zero_constantCoeff := constantCoeff_X
  coeff_finite := HasSubst.X.coeff_zero
  map_add i := by
    rw [subst_X F.hasSubst]
    simp only [subst_X_block]
    exact (congrFun subst_self (F.toPowerSeries i)).symm

@[simp]
theorem id_apply (i : σ) : id F i = X i := rfl

/-- Composition of homomorphisms, with `g.comp f` representing `g ∘ f`. -/
def comp (g : Hom G H) (f : Hom F G) : Hom F H where
  toPowerSeries i := (g i).subst f.toPowerSeries
  zero_constantCoeff i :=
    constantCoeff_subst_eq_zero f.hasSubst f.zero_constantCoeff (g.zero_constantCoeff i)
  coeff_finite := (g.hasSubst.subst f.hasSubst).coeff_zero
  map_add i := by
    rw [subst_comp_subst_apply f.hasSubst F.hasSubst]
    simp only [f.map_add]
    rw [g.map_add_subst f.hasSubst_blocks]
    congr 1
    funext p
    have hb := HasSubst.curry_X (R := R) (σ := σ) p.1
    exact (subst_comp_subst_apply f.hasSubst hb (g p.2)).symm

@[simp]
theorem comp_apply (g : Hom G H) (f : Hom F G) (i : υ) :
    g.comp f i = (g i).subst f.toPowerSeries := rfl

@[simp]
theorem id_comp (f : Hom F G) : (id G).comp f = f := by
  apply Hom.ext
  funext i
  exact subst_X f.hasSubst i

@[simp]
theorem comp_id (f : Hom F G) : f.comp (id F) = f := by
  apply Hom.ext
  funext i
  exact congrFun subst_self (f i)

theorem comp_assoc (h : Hom H K) (g : Hom G H) (f : Hom F G) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  apply Hom.ext
  funext i
  exact subst_comp_subst_apply g.hasSubst f.hasSubst (h i)

/-- The homomorphism which sends every coordinate to zero. -/
instance : Zero (Hom F G) where
  zero :=
    { toPowerSeries := 0
      zero_constantCoeff := by simp
      coeff_finite := HasSubst.zero.coeff_zero
      map_add i := by
        have hF := F.hasSubst
        have hz (b : Fin 2) :
            (0 : MvPowerSeries σ R).subst (fun j ↦ X (R := R) (b, j)) = 0 := by
          have hb : HasSubst (fun j : σ ↦ X (R := R) (b, j)) := .curry_X b
          rw [← substAlgHom_apply hb, map_zero]
        simp only [Pi.zero_apply, hz]
        rw [← substAlgHom_apply hF, map_zero, ← Pi.zero_def,
          subst_zero_of_constantCoeff_zero (G.zero_constantCoeff i)] }


@[simp]
theorem zero_apply (i : τ) : (0 : Hom F G) i = 0 := rfl

@[simp]
theorem zero_comp (f : Hom F G) : (0 : Hom G H).comp f = 0 := by
  apply Hom.ext
  funext i
  change (0 : MvPowerSeries τ R).subst f.toPowerSeries = 0
  rw [← substAlgHom_apply f.hasSubst, map_zero]

@[simp]
theorem comp_zero (g : Hom G H) : g.comp (0 : Hom F G) = 0 := by
  apply Hom.ext
  funext i
  exact subst_zero_of_constantCoeff_zero (g.zero_constantCoeff i)

end Hom

end MvFormalGroup
