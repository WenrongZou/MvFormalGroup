/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import MvFormalGroup.Basic
public import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
# One-dimensional formal group laws

Just as `PowerSeries R` is `MvPowerSeries Unit R`, `FormalGroup R` is
`MvFormalGroup Unit R`. All axioms and results for multidimensional formal groups
therefore apply directly. Commutativity remains a separate property.

`FormalGroup.toPowerSeries` selects the unique coordinate and renames its variables
along `Fin 2 × Unit ≃ Fin 2`: `0` is `X` and `1` is `Y`.
-/

@[expose] public section

noncomputable section

open MvPowerSeries Finsupp Function

/-- A one-dimensional formal group law over a commutative ring `R`. -/
abbrev FormalGroup (R : Type*) [CommRing R] := MvFormalGroup Unit R

namespace FormalGroup

variable {R : Type*} [CommRing R]

/-- The power series `F(X, Y)` of a one-dimensional formal group law. -/
def toPowerSeries (F : FormalGroup R) : MvPowerSeries (Fin 2) R :=
  renameEquiv R (Equiv.prodUnique _ _) (MvFormalGroup.toPowerSeries F ())

@[ext]
theorem ext {F G : FormalGroup R} (h : F.toPowerSeries = G.toPowerSeries) : F = G := by
  apply MvFormalGroup.ext
  funext i
  cases i
  exact (renameEquiv R (Equiv.prodUnique (Fin 2) Unit)).injective h

@[simp]
theorem zero_constantCoeff (F : FormalGroup R) : constantCoeff F.toPowerSeries = 0 := by
  simpa [toPowerSeries] using MvFormalGroup.zero_constantCoeff F ()

/-- Renaming the variables preserves the corresponding coefficients. -/
theorem coeff_toPowerSeries (F : FormalGroup R) (d : (Fin 2 × Unit) →₀ ℕ) :
    coeff (d.embDomain (Equiv.prodUnique (Fin 2) Unit).toEmbedding) F.toPowerSeries =
      coeff d (MvFormalGroup.toPowerSeries F ()) :=
  coeff_embDomain_rename (Equiv.prodUnique (Fin 2) Unit).toEmbedding _ d

@[simp]
theorem lin_coeff_X (F : FormalGroup R) : coeff (single 0 1) F.toPowerSeries = 1 := by
  simpa using (F.coeff_toPowerSeries (single (0, ()) 1)).trans (MvFormalGroup.lin_coeff_X F () ())

@[simp]
theorem lin_coeff_Y (F : FormalGroup R) : coeff (single 1 1) F.toPowerSeries = 1 := by
  simpa using (F.coeff_toPowerSeries (single (1, ()) 1)).trans (MvFormalGroup.lin_coeff_Y F () ())

private theorem rename_subst {n m : ℕ} (f : MvPowerSeries (Fin n × Unit) R)
    (a : Fin n → MvPowerSeries (Fin m × Unit) R)
    (ha : ∀ i, constantCoeff (a i) = 0) :
    rename Prod.fst (f.subst (fun p ↦ a p.1)) =
      (rename Prod.fst f).subst (fun i ↦ rename Prod.fst (a i)) := by
  have ha' : HasSubst (fun p : Fin n × Unit ↦ a p.1) :=
    hasSubst_of_constantCoeff_zero (fun p ↦ ha p.1)
  have hb : HasSubst (fun i ↦ rename Prod.fst (a i)) :=
    hasSubst_of_constantCoeff_zero (by simpa using ha)
  rw [rename_eq_subst, subst_comp_subst_apply ha' (HasSubst.X_comp _)]
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) hb]
  simp only [Function.comp_apply, subst_X hb]
  congr 1
  funext p
  exact (rename_eq_subst _ _).symm

private theorem constantCoeff_subst_vec {n : ℕ}
    (f : MvPowerSeries (Fin 2 × Unit) R) (hf : constantCoeff f = 0)
    (a : Fin 2 → MvPowerSeries (Fin n × Unit) R)
    (ha : ∀ i, constantCoeff (a i) = 0) :
    constantCoeff (f.subst (fun p ↦ a p.1)) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (fun p : Fin 2 × Unit ↦ ha p.1))
    (fun p ↦ ha p.1) hf

private theorem rename_vec {n : ℕ} (x y : MvPowerSeries (Fin n × Unit) R) :
    (fun i ↦ rename Prod.fst (![x, y] i)) = ![rename Prod.fst x, rename Prod.fst y] := by
  funext i
  fin_cases i <;> rfl

/-- Associativity specialized to the unique coordinate. -/
private theorem assoc_raw (F : FormalGroup R) :
    let f := MvFormalGroup.toPowerSeries F ()
    let V : Fin 3 → MvPowerSeries (Fin 3 × Unit) R := fun b ↦ X (b, ())
    f.subst (fun p ↦ ![f.subst (fun q ↦ ![V 0, V 1] q.1), V 2] p.1) =
    f.subst (fun p ↦ ![V 0, f.subst (fun q ↦ ![V 1, V 2] q.1)] p.1) := by
  have h := MvFormalGroup.assoc F ()
  dsimp only at h ⊢
  convert h using 1 <;>
    congr 1 <;> funext ⟨b, ⟨⟩⟩ <;> fin_cases b
  all_goals try rfl
  all_goals
    change subst _ _ = subst _ _
    congr 1
    funext ⟨b, ⟨⟩⟩
    fin_cases b <;> rfl

/-- Associativity in three variables, indexed by `Fin 3`. -/
theorem assoc (F : FormalGroup R) :
    let V : Fin 3 → MvPowerSeries (Fin 3) R := X
    F.toPowerSeries.subst ![F.toPowerSeries.subst ![V 0, V 1], V 2] =
      F.toPowerSeries.subst ![V 0, F.toPowerSeries.subst ![V 1, V 2]] := by
  have h := congrArg (rename (R := R) (Prod.fst : Fin 3 × Unit → Fin 3)) (assoc_raw F)
  have hv (b c : Fin 3) :
      ∀ i, constantCoeff (![X (b, ()), X (c, ())] i : MvPowerSeries (Fin 3 × Unit) R) = 0 := by
    intro i
    fin_cases i <;> simp
  have hc (b c : Fin 3) := constantCoeff_subst_vec
    (MvFormalGroup.toPowerSeries F ()) (MvFormalGroup.zero_constantCoeff F ()) _ (hv b c)
  dsimp only at h ⊢
  rw [rename_subst _ _ (by intro i; fin_cases i <;> simp [hc]),
    rename_subst _ _ (by intro i; fin_cases i <;> simp [hc])] at h
  simpa [toPowerSeries, rename_vec,
    rename_subst _ _ (hv 0 1), rename_subst _ _ (hv 1 2)] using h

/-- Commutativity of a one-dimensional formal group law. -/
abbrev IsComm (F : FormalGroup R) : Prop := MvFormalGroup.IsComm F

/-- Commutativity specialized to the unique coordinate. -/
theorem comm (F : FormalGroup R) [F.IsComm] :
    F.toPowerSeries = F.toPowerSeries.subst ![X 1, X 0] := by
  have hraw : MvFormalGroup.toPowerSeries F () =
      (MvFormalGroup.toPowerSeries F ()).subst (fun p ↦ ![X (1, ()), X (0, ())] p.1) := by
    convert MvFormalGroup.IsComm.comm (F := F) () using 1
    congr 1
    funext ⟨b, ⟨⟩⟩
    fin_cases b <;> rfl
  have h := congrArg (rename (R := R) (Prod.fst : Fin 2 × Unit → Fin 2)) hraw
  rw [rename_subst _ _ (by intro i; fin_cases i <;> simp)] at h
  simpa [toPowerSeries, rename_vec] using h

/-- The linear part of a one-dimensional formal group law is `X + Y`. -/
theorem truncTotal_two (F : FormalGroup R) :
    F.toPowerSeries.truncTotal 2 = MvPolynomial.X 0 + MvPolynomial.X 1 := by
  classical
  ext d
  by_cases hd : d.degree < 2
  · rw [coeff_truncTotal _ hd]
    rcases show d.degree = 0 ∨ d.degree = 1 by omega with hzero | hone
    · have : d = 0 := d.degree_eq_zero_iff.mp hzero
      simp [this, MvPolynomial.coeff_X]
    · obtain ⟨b, rfl⟩ := (Finsupp.sum_eq_one_iff d).mp hone
      fin_cases b <;> simp [MvPolynomial.coeff_X, Finsupp.single_left_inj]
  · rw [coeff_truncTotal_eq_zero _ (by omega)]
    have hx : d ≠ single 0 1 := by rintro rfl; simp at hd
    have hy : d ≠ single 1 1 := by rintro rfl; simp at hd
    simp [MvPolynomial.coeff_X, Ne.symm hx, Ne.symm hy]

/-- The additive one-dimensional formal group law `F(X, Y) = X + Y`. -/
abbrev additive (R : Type*) [CommRing R] : FormalGroup R := MvFormalGroup.additive Unit R

@[simp]
theorem additive_toPowerSeries : (additive R).toPowerSeries = X 0 + X 1 := by
  simp [toPowerSeries, additive, MvFormalGroup.additive]

end FormalGroup
