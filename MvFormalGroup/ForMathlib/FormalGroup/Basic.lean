/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import MvFormalGroup.ForMathlib.MvFormalGroup.Basic
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# One-dimensional formal group laws

Just as `PowerSeries R` is `MvPowerSeries Unit R`, `FormalGroup R` is
`MvFormalGroup Unit R`. All axioms and results for multidimensional formal groups
therefore apply directly. Commutativity remains a separate property.

`FormalGroup.toPowerSeries` selects the unique coordinate and renames its variables
along `Fin 2 × Unit ≃ Fin 2`: `0` is `X` and `1` is `Y`.

`Xzero_eq_X` and `zeroX_eq_X` give the identity equations in `PowerSeries R`.
`add_zero` and `zero_add` extend them to any admissible substituted series.

`Point F S` is the type of topologically nilpotent elements of `S`. When `S` is a
complete Hausdorff linearly topologized `R`-algebra, evaluation of `F` defines an
`AddMonoid` structure on these points, and an `AddCommMonoid` structure if `F.IsComm`.
For power series over discrete coefficients, these are precisely the series with
nilpotent constant coefficient, and addition agrees with substitution into `F`.
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

/-- Two admissible series can be substituted into a one-dimensional formal group law. -/
theorem hasSubst_pair {τ : Type*} {x y : MvPowerSeries τ R}
    (hx : PowerSeries.HasSubst x) (hy : PowerSeries.HasSubst y) : HasSubst ![x, y] :=
  hasSubst_of_constantCoeff_nilpotent (by intro i; fin_cases i <;> assumption)

/-- Substitution into the one-dimensional law agrees with substitution into its
underlying one-coordinate multidimensional law. -/
theorem subst_toPowerSeries {τ : Type*} (F : FormalGroup R)
    (x y : MvPowerSeries τ R) (hx : PowerSeries.HasSubst x) (hy : PowerSeries.HasSubst y) :
    F.toPowerSeries.subst ![x, y] =
      (MvFormalGroup.toPowerSeries F ()).subst (uncurry ![fun _ ↦ x, fun _ ↦ y]) := by
  change (rename (Equiv.prodUnique (Fin 2) Unit) (MvFormalGroup.toPowerSeries F ())).subst
    ![x, y] = _
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) (hasSubst_pair hx hy)]
  congr 1
  funext ⟨b, ⟨⟩⟩
  fin_cases b <;> simp [subst_X (hasSubst_pair hx hy), uncurry]

/-- Associativity after substituting series with zero constant coefficients. -/
theorem assoc_subst {τ : Type*} (F : FormalGroup R) (x y z : MvPowerSeries τ R)
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) (hz : constantCoeff z = 0) :
    F.toPowerSeries.subst ![F.toPowerSeries.subst ![x, y], z] =
      F.toPowerSeries.subst ![x, F.toPowerSeries.subst ![y, z]] := by
  have hxy := PowerSeries.HasSubst.of_constantCoeff_zero hx
  have hyy := PowerSeries.HasSubst.of_constantCoeff_zero hy
  have hzy := PowerSeries.HasSubst.of_constantCoeff_zero hz
  have hc (a b : MvPowerSeries τ R) (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
      PowerSeries.HasSubst (F.toPowerSeries.subst ![a, b]) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_subst_eq_zero
      (hasSubst_pair (.of_constantCoeff_zero ha) (.of_constantCoeff_zero hb))
      (by intro i; fin_cases i <;> assumption) F.zero_constantCoeff)
  rw [subst_toPowerSeries F _ _ (hc x y hx hy) hzy,
    subst_toPowerSeries F _ _ hxy (hc y z hy hz),
    subst_toPowerSeries F x y hxy hyy, subst_toPowerSeries F y z hyy hzy]
  exact MvFormalGroup.assoc_subst F (fun _ ↦ x) (fun _ ↦ y) (fun _ ↦ z)
    (fun _ ↦ hx) (fun _ ↦ hy) (fun _ ↦ hz) ()

/-- Zero is a right identity after any admissible substitution. -/
@[simp]
theorem add_zero {τ : Type*} (F : FormalGroup R) {f : MvPowerSeries τ R}
    (hf : PowerSeries.HasSubst f) : F.toPowerSeries.subst ![f, 0] = f := by
  rw [subst_toPowerSeries F f 0 hf PowerSeries.HasSubst.zero]
  simpa only [← Pi.zero_def] using MvFormalGroup.add_zero F hf.const ()

/-- Zero is a left identity after any admissible substitution. -/
@[simp]
theorem zero_add {τ : Type*} (F : FormalGroup R) {f : MvPowerSeries τ R}
    (hf : PowerSeries.HasSubst f) : F.toPowerSeries.subst ![0, f] = f := by
  rw [subst_toPowerSeries F 0 f PowerSeries.HasSubst.zero hf]
  simpa only [← Pi.zero_def] using MvFormalGroup.zero_add F hf.const ()

/-- The one-variable series `F(X, 0)`. -/
abbrev Xzero (F : FormalGroup R) : PowerSeries R :=
  F.toPowerSeries.subst ![PowerSeries.X, 0]

/-- The one-variable series `F(0, X)`. -/
abbrev zeroX (F : FormalGroup R) : PowerSeries R :=
  F.toPowerSeries.subst ![0, PowerSeries.X]

/-- The right identity equation `F(X, 0) = X`. -/
@[simp]
theorem Xzero_eq_X (F : FormalGroup R) : F.Xzero = PowerSeries.X :=
  F.add_zero PowerSeries.HasSubst.X'

/-- The left identity equation `F(0, X) = X`. -/
@[simp]
theorem zeroX_eq_X (F : FormalGroup R) : F.zeroX = PowerSeries.X :=
  F.zero_add PowerSeries.HasSubst.X'

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

section Evaluation

variable (F : FormalGroup R)
variable {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S]
  [IsLinearTopology S S] [CompleteSpace S] [T2Space S] [IsTopologicalRing S]
  [UniformSpace R] [DiscreteUniformity R] [Algebra R S]

/-- Zero is a right identity for evaluation at topologically nilpotent elements. -/
@[simp]
theorem eval₂_add_zero {a : S} (ha : IsTopologicallyNilpotent a) :
    F.toPowerSeries.eval₂ (algebraMap R S) ![a, 0] = a := by
  have hb : HasEval (fun _ : Unit ↦ a) := ⟨fun _ ↦ ha, by simp⟩
  calc
    _ = eval₂ (algebraMap R S) (fun _ : Unit ↦ a) F.Xzero := by
      rw [eval₂_subst (a := ![PowerSeries.X, 0]) HasSubst.X_zero hb]
      congr! 2 with i
      fin_cases i <;> simp [PowerSeries.X, ← MvPolynomial.coe_zero]
    _ = a := by simp [Xzero_eq_X, PowerSeries.X]

/-- Zero is a left identity for evaluation at topologically nilpotent elements. -/
@[simp]
theorem eval₂_zero_add {a : S} (ha : IsTopologicallyNilpotent a) :
    F.toPowerSeries.eval₂ (algebraMap R S) ![0, a] = a := by
  have hb : HasEval (fun _ : Unit ↦ a) := ⟨fun _ ↦ ha, by simp⟩
  calc
    _ = eval₂ (algebraMap R S) (fun _ : Unit ↦ a) F.zeroX := by
      rw [eval₂_subst (a := ![0, PowerSeries.X]) HasSubst.zero_X hb]
      congr! 2 with i
      fin_cases i <;> simp [PowerSeries.X, ← MvPolynomial.coe_zero]
    _ = a := by simp [zeroX_eq_X, PowerSeries.X]

/-- Associativity after evaluation at topologically nilpotent elements. -/
theorem eval₂_assoc {a b c : S} (ha : IsTopologicallyNilpotent a)
    (hb : IsTopologicallyNilpotent b) (hc : IsTopologicallyNilpotent c) :
    F.toPowerSeries.eval₂ (algebraMap R S) ![F.toPowerSeries.eval₂ (algebraMap R S) ![a, b], c] =
      F.toPowerSeries.eval₂ (algebraMap R S)
        ![a, F.toPowerSeries.eval₂ (algebraMap R S) ![b, c]] := by
  have he : HasEval ![a, b, c] := ⟨fun s ↦ by fin_cases s <;> assumption, by simp⟩
  have {i j : Fin 3} : eval₂ (algebraMap R S) ![a, b, c] (F.toPowerSeries.subst ![X i, X j]) =
      F.toPowerSeries.eval₂ (algebraMap R S) ![![a, b, c] i, ![a, b, c] j] := by
    rw [eval₂_subst HasSubst.X_X he]
    congr! 2 with s
    fin_cases s <;> simp
  calc
    _ = (F.toPowerSeries.subst ![F.toPowerSeries.subst ![X (0 : Fin 3), X 1], X 2]).eval₂
          (algebraMap R S) ![a, b, c] := by
      rw [eval₂_subst (HasSubst.cons_subst_zero_left 0 1 2 F.zero_constantCoeff) he]
      congr! 2 with i
      fin_cases i <;> simp [this]
    _ = F.toPowerSeries.eval₂ (algebraMap R S)
          ![a, F.toPowerSeries.eval₂ (algebraMap R S) ![b, c]] := by
      rw [F.assoc, eval₂_subst (HasSubst.cons_subst_zero_right 0 1 2 F.zero_constantCoeff) he]
      congr! 2 with i
      fin_cases i <;> simp [this]

/-- Commutativity after evaluation at topologically nilpotent elements. -/
theorem eval₂_comm [F.IsComm] {a b : S} (ha : IsTopologicallyNilpotent a)
    (hb : IsTopologicallyNilpotent b) :
    F.toPowerSeries.eval₂ (algebraMap R S) ![a, b] =
      F.toPowerSeries.eval₂ (algebraMap R S) ![b, a] := by
  have he : HasEval ![a, b] := ⟨fun s ↦ by fin_cases s <;> assumption, by simp⟩
  nth_rw 1 [F.comm]
  rw [eval₂_subst HasSubst.X_X he]
  congr! 2 with i
  fin_cases i <;> simp

end Evaluation

section Point

variable (F : FormalGroup R) (S : Type*) [CommRing S] [TopologicalSpace S]

/-- Points of a formal group law in a topological ring. The underlying elements are
topologically nilpotent; the formal group law determines their addition. -/
@[nolint unusedArguments]
def Point (_F : FormalGroup R) := {a : S // IsTopologicallyNilpotent a}

variable {S} in
lemma hasEval_point (x y : F.Point S) : HasEval ![x.val, y.val] where
  hpow s := by fin_cases s <;> simp [x.prop, y.prop]
  tendsto_zero := by simp

instance : Zero (F.Point S) where
  zero := ⟨0, .zero⟩

@[simp]
lemma zero_apply : (0 : F.Point S).val = 0 := rfl

end Point

section PointAddition

variable (F : FormalGroup R) (S : Type*) [CommRing S] [UniformSpace S]
  [IsUniformAddGroup S] [CompleteSpace S] [T2Space S] [IsTopologicalRing S]
  [IsLinearTopology S S] [Algebra R S]

open WithPiTopology in
instance : Add (F.Point S) where
  add x y :=
    letI : UniformSpace R := ⊥
    haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
    ⟨F.toPowerSeries.aeval (F.hasEval_point x y),
      .map (continuous_aeval (F.hasEval_point x y))
        (isTopologicallyNilpotent_of_constantCoeff_zero F.zero_constantCoeff)⟩

/-- Addition of points is evaluation of the formal group law. -/
@[simp]
lemma add_eq_eval₂ [UniformSpace R] [DiscreteUniformity R] {x y : F.Point S} :
    (x + y).val = F.toPowerSeries.eval₂ (algebraMap R S) ![x.val, y.val] := by
  obtain rfl := DiscreteUniformity.eq_bot (X := R)
  let : UniformSpace R := ⊥
  have : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  exact congrFun (coe_aeval (F.hasEval_point x y)) F.toPowerSeries

instance : AddMonoid (F.Point S) where
  zero_add x := Subtype.ext <| by
    let : UniformSpace R := ⊥
    rw [add_eq_eval₂, zero_apply, F.eval₂_zero_add x.prop]
  add_zero x := Subtype.ext <| by
    let : UniformSpace R := ⊥
    rw [add_eq_eval₂, zero_apply, F.eval₂_add_zero x.prop]
  nsmul := nsmulRec
  add_assoc x y z := Subtype.ext <| by
    let : UniformSpace R := ⊥
    simp only [add_eq_eval₂]
    exact F.eval₂_assoc x.prop y.prop z.prop

instance [F.IsComm] : AddCommMonoid (F.Point S) where
  add_comm x y := Subtype.ext <| by
    let : UniformSpace R := ⊥
    simp [add_eq_eval₂, F.eval₂_comm x.prop y.prop]

end PointAddition

section PowerSeriesPoints

open WithPiTopology

variable (F : FormalGroup R) (σ : Type*)

/-- For power series over a discrete coefficient ring, the points are precisely
the series whose constant coefficients are nilpotent. -/
def pointMvPowerSeriesEquiv [TopologicalSpace R] [DiscreteTopology R] :
    F.Point (MvPowerSeries σ R) ≃ {f : MvPowerSeries σ R // PowerSeries.HasSubst f} where
  toFun f := ⟨f.val, (isTopologicallyNilpotent_iff_constantCoeff_isNilpotent f.val).mp f.prop⟩
  invFun f := ⟨f.val, (isTopologicallyNilpotent_iff_constantCoeff_isNilpotent f.val).mpr f.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Addition of power series points agrees with substitution into the formal group law. -/
lemma add_eq_subst [UniformSpace R] [DiscreteUniformity R]
    {x y : F.Point (MvPowerSeries σ R)} :
    (x + y).val = F.toPowerSeries.subst ![x.val, y.val] := by
  rw [add_eq_eval₂, subst_eq_eval₂]

end PowerSeriesPoints

end FormalGroup
