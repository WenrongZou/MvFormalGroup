/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import MvFormalGroup.ForMathlib.FormalGroup.Hom
public import MvFormalGroup.ForMathlib.FormalGroup.Inverse
public import Mathlib.Topology.Algebra.Algebra

/-!
# The group of points of a one-dimensional formal group law

Let `S` be a complete Hausdorff linearly topologized `R`-algebra. The points `F.Point S` of a
one-dimensional formal group law `F` are the topologically nilpotent elements of `S`, with
addition `x + y = F(x, y)`. This file completes the group structure and its functoriality.

## Main definitions

- `-x = i(x)`, where `i = F.inv` is the formal inverse, makes `F.Point S` an `AddGroup`, and an
  `AddCommGroup` if `F` is commutative.
- `FormalGroup.Point.map F φ : F.Point S →+ F.Point S'`, `x ↦ φ(x)`, for a continuous
  `R`-algebra homomorphism `φ : S →A[R] S'`.
- `FormalGroup.Hom.pointHom f S : F.Point S →+ G.Point S`, `x ↦ f(x)`, for a homomorphism
  `f : F → G` of formal group laws.
- `FormalGroup.Hom.pointMap f φ : F.Point S →+ G.Point S'`, `x ↦ f(φ(x))`. By
  `FormalGroup.Hom.pointMap_eq_comp`, it also equals `x ↦ φ(f(x))`.
-/

@[expose] public section

noncomputable section

open MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R]

section Evaluation

variable {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S]
  [IsLinearTopology S S] [CompleteSpace S] [T2Space S] [IsTopologicalRing S]
  [UniformSpace R] [DiscreteUniformity R] [Algebra R S]

/-- The formal inverse is a left inverse after evaluation: `F(i(a), a) = 0`. -/
theorem eval₂_inv_add (F : FormalGroup R) {a : S} (ha : IsTopologicallyNilpotent a) :
    F.toPowerSeries.eval₂ (algebraMap R S)
      ![eval₂ (algebraMap R S) (fun _ : Unit ↦ a) F.inv, a] = 0 := by
  have hb : HasEval (fun _ : Unit ↦ a) := ⟨fun _ ↦ ha, by simp⟩
  calc
    _ = eval₂ (algebraMap R S) (fun _ : Unit ↦ a)
          (F.toPowerSeries.subst ![F.inv, PowerSeries.X]) := by
      rw [eval₂_subst (FormalGroup.hasSubst_pair F.hasSubst_inv .X') hb]
      congr! 2 with i
      fin_cases i <;> simp [PowerSeries.X]
    _ = 0 := by
      rw [F.inv_left, ← MvPolynomial.coe_zero, eval₂_coe, MvPolynomial.eval₂_zero]

/-- A homomorphism commutes with the group laws after evaluation:
`f(F(a, b)) = G(f(a), f(b))`. -/
theorem Hom.eval₂_map_add {F G : FormalGroup R} (f : Hom F G) {a b : S}
    (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b) :
    eval₂ (algebraMap R S) (fun _ : Unit ↦ F.toPowerSeries.eval₂ (algebraMap R S) ![a, b])
        f.toPowerSeries =
      G.toPowerSeries.eval₂ (algebraMap R S)
        ![eval₂ (algebraMap R S) (fun _ : Unit ↦ a) f.toPowerSeries,
          eval₂ (algebraMap R S) (fun _ : Unit ↦ b) f.toPowerSeries] := by
  have he : HasEval ![a, b] := ⟨fun s ↦ by fin_cases s <;> assumption, by simp⟩
  have hx (i : Fin 2) :
      PowerSeries.HasSubst (f.toPowerSeries.subst (X i : MvPowerSeries (Fin 2) R)) :=
    .of_constantCoeff_zero
      (PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) _ f.constantCoeff_toPowerSeries)
  calc
    _ = eval₂ (algebraMap R S) ![a, b] (f.toPowerSeries.subst F.toPowerSeries) :=
      (eval₂_subst (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff).const he
        _).symm
    _ = _ := by
      rw [f.map_add, eval₂_subst (FormalGroup.hasSubst_pair (hx 0) (hx 1)) he]
      congr! 2 with i
      fin_cases i <;>
        exact (eval₂_subst (PowerSeries.HasSubst.X _).const he _).trans (by simp)

variable {S' : Type*} [CommRing S'] [UniformSpace S'] [IsUniformAddGroup S']
  [IsLinearTopology S' S'] [CompleteSpace S'] [T2Space S'] [IsTopologicalRing S'] [Algebra R S']

/-- Continuous `R`-algebra homomorphisms commute with evaluation. -/
theorem _root_.ContinuousAlgHom.map_eval₂ {σ : Type*} (φ : S →A[R] S') {a : σ → S}
    (ha : HasEval a) (f : MvPowerSeries σ R) :
    φ (eval₂ (algebraMap R S) a f) = eval₂ (algebraMap R S') (fun s ↦ φ (a s)) f := by
  have h := congrFun (comp_eval₂ (φ := algebraMap R S) continuous_of_discreteTopology ha
    (ε := ((φ : S →ₐ[R] S') : S →+* S')) φ.continuous) f
  rwa [AlgHom.comp_algebraMap] at h

end Evaluation

namespace Point

variable {S : Type*} [CommRing S] [TopologicalSpace S]

theorem hasEval {F : FormalGroup R} (x : F.Point S) : HasEval (fun _ : Unit ↦ x.val) :=
  ⟨fun _ ↦ x.prop, by simp⟩

/-- The point of `F` given by a topologically nilpotent element `a`. -/
def mk (F : FormalGroup R) {a : S} (ha : IsTopologicallyNilpotent a) : F.Point S :=
  ⟨a, ha⟩

@[simp]
theorem mk_val (F : FormalGroup R) {a : S} (ha : IsTopologicallyNilpotent a) :
    (mk F ha).val = a :=
  rfl

end Point

section PointGroup

variable {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [CompleteSpace S]
  [T2Space S] [IsTopologicalRing S] [IsLinearTopology S S] [Algebra R S]

open WithPiTopology in
/-- The value `P(x)` of a power series `P` without constant term at a point `x`, as a point of
the formal group law `G`. -/
def evalPoint (G : FormalGroup R) (P : PowerSeries R) (hP : PowerSeries.constantCoeff P = 0)
    {F : FormalGroup R} (x : F.Point S) : G.Point S :=
  letI : UniformSpace R := ⊥
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  ⟨aeval x.hasEval P,
    .map (continuous_aeval x.hasEval) (isTopologicallyNilpotent_of_constantCoeff_zero hP)⟩

@[simp]
theorem evalPoint_val [UniformSpace R] [DiscreteUniformity R] (G : FormalGroup R)
    (P : PowerSeries R) (hP : PowerSeries.constantCoeff P = 0) {F : FormalGroup R}
    (x : F.Point S) :
    (G.evalPoint P hP x).val = eval₂ (algebraMap R S) (fun _ : Unit ↦ x.val) P := by
  obtain rfl := DiscreteUniformity.eq_bot (X := R)
  let : UniformSpace R := ⊥
  have : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  exact congrFun (coe_aeval x.hasEval) P

variable (F : FormalGroup R) (S)

/-- The negative of a point `x` is `i(x)`, where `i` is the formal inverse of `F`. -/
instance : Neg (F.Point S) where
  neg x := F.evalPoint F.inv F.constantCoeff_inv x

variable {F S}

@[simp]
theorem neg_eq_eval₂ [UniformSpace R] [DiscreteUniformity R] (x : F.Point S) :
    (-x).val = eval₂ (algebraMap R S) (fun _ : Unit ↦ x.val) F.inv :=
  evalPoint_val F F.inv F.constantCoeff_inv x

variable (F S)

instance : AddGroup (F.Point S) where
  neg_add_cancel x := Subtype.ext <| by
    let : UniformSpace R := ⊥
    rw [add_eq_eval₂, neg_eq_eval₂, zero_apply, F.eval₂_inv_add x.prop]
  zsmul := zsmulRec

instance [F.IsComm] : AddCommGroup (F.Point S) where
  add_comm := add_comm

end PointGroup

section Functoriality

variable {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [CompleteSpace S]
  [T2Space S] [IsTopologicalRing S] [IsLinearTopology S S] [Algebra R S]
variable {S' : Type*} [CommRing S'] [UniformSpace S'] [IsUniformAddGroup S'] [CompleteSpace S']
  [T2Space S'] [IsTopologicalRing S'] [IsLinearTopology S' S'] [Algebra R S']
variable {S'' : Type*} [CommRing S''] [UniformSpace S''] [IsUniformAddGroup S'']
  [CompleteSpace S''] [T2Space S''] [IsTopologicalRing S''] [IsLinearTopology S'' S'']
  [Algebra R S'']

/-- A continuous `R`-algebra homomorphism `φ : S → S'` induces `F(S) →+ F(S')`, `x ↦ φ(x)`. -/
def Point.map (F : FormalGroup R) (φ : S →A[R] S') : F.Point S →+ F.Point S' :=
  AddMonoidHom.mk' (fun x ↦ Point.mk F (x.prop.map φ.continuous)) fun x y ↦ Subtype.ext <| by
    let : UniformSpace R := ⊥
    simp only [add_eq_eval₂, Point.mk_val]
    rw [φ.map_eval₂ (F.hasEval_point x y)]
    congr 1
    funext i
    fin_cases i <;> rfl

@[simp]
theorem Point.map_apply_val (F : FormalGroup R) (φ : S →A[R] S') (x : F.Point S) :
    (Point.map F φ x).val = φ x.val :=
  rfl

@[simp]
theorem Point.map_id (F : FormalGroup R) :
    Point.map F (ContinuousAlgHom.id R S) = AddMonoidHom.id _ :=
  rfl

theorem Point.map_comp (F : FormalGroup R) (ψ : S' →A[R] S'') (φ : S →A[R] S') :
    Point.map F (ψ.comp φ) = (Point.map F ψ).comp (Point.map F φ) :=
  rfl

variable {F G H : FormalGroup R}

variable (S) in
/-- A homomorphism `f : F → G` of formal group laws induces `F(S) →+ G(S)`, `x ↦ f(x)`. -/
def Hom.pointHom (f : Hom F G) : F.Point S →+ G.Point S :=
  AddMonoidHom.mk' (G.evalPoint f.toPowerSeries f.constantCoeff_toPowerSeries)
    fun x y ↦ Subtype.ext <| by
      let : UniformSpace R := ⊥
      simp only [evalPoint_val, add_eq_eval₂]
      exact f.eval₂_map_add x.prop y.prop

@[simp]
theorem Hom.pointHom_apply_val [UniformSpace R] [DiscreteUniformity R] (f : Hom F G)
    (x : F.Point S) :
    (f.pointHom S x).val = eval₂ (algebraMap R S) (fun _ : Unit ↦ x.val) f.toPowerSeries :=
  evalPoint_val G f.toPowerSeries f.constantCoeff_toPowerSeries x

@[simp]
theorem Hom.pointHom_id : (Hom.id F).pointHom S = AddMonoidHom.id _ := by
  ext x
  apply Subtype.ext
  let : UniformSpace R := ⊥
  simp [PowerSeries.X]

theorem Hom.pointHom_comp (g : Hom G H) (f : Hom F G) :
    (g.comp f).pointHom S = (g.pointHom S).comp (f.pointHom S) := by
  ext x
  apply Subtype.ext
  let : UniformSpace R := ⊥
  simp only [pointHom_apply_val, toPowerSeries_comp, AddMonoidHom.coe_comp, Function.comp_apply]
  exact eval₂_subst f.hasSubst.const x.hasEval _

/-- For a continuous `R`-algebra homomorphism `φ : S → S'`, a homomorphism `f : F → G` induces
`F(S) →+ G(S')`, `x ↦ f(φ(x))`. -/
def Hom.pointMap (f : Hom F G) (φ : S →A[R] S') : F.Point S →+ G.Point S' :=
  (f.pointHom S').comp (Point.map F φ)

/-- Naturality: `f(φ(x)) = φ(f(x))`. -/
theorem Hom.pointMap_eq_comp (f : Hom F G) (φ : S →A[R] S') :
    f.pointMap φ = (Point.map G φ).comp (f.pointHom S) := by
  ext x
  apply Subtype.ext
  let : UniformSpace R := ⊥
  simp only [pointMap, AddMonoidHom.coe_comp, Function.comp_apply, pointHom_apply_val,
    Point.map_apply_val]
  exact (φ.map_eval₂ x.hasEval _).symm

@[simp]
theorem Hom.pointMap_apply_val [UniformSpace R] [DiscreteUniformity R] (f : Hom F G)
    (φ : S →A[R] S') (x : F.Point S) :
    (f.pointMap φ x).val = eval₂ (algebraMap R S') (fun _ : Unit ↦ φ x.val) f.toPowerSeries :=
  evalPoint_val G f.toPowerSeries f.constantCoeff_toPowerSeries (Point.map F φ x)

theorem Hom.pointMap_id (f : Hom F G) :
    f.pointMap (ContinuousAlgHom.id R S) = f.pointHom S :=
  rfl

end Functoriality

end FormalGroup
