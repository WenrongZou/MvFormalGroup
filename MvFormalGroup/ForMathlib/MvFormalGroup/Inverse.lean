/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import MvFormalGroup.ForMathlib.MvFormalGroup.Basic
public import MvFormalGroup.ForMathlib.MvPowerSeries.ImplicitInfinite

/-!
# Inverses of multidimensional formal group laws

For an arbitrary coordinate index, the inverse is constructed using the formal implicit
function theorem with cofinite support. Its constant terms vanish, its coordinate family
is substitutable, and it satisfies both inverse identities. Associativity implies
`inv_subst_inv` and the right inverse identity; commutativity is not required.
-/

@[expose] public section

noncomputable section

open MvPowerSeries Finsupp Function

namespace MvFormalGroup

variable {R : Type*} [CommRing R] {σ : Type*} [DecidableEq σ]

section Inverse

/-- Identify the two blocks of variables with a disjoint sum. -/
private def sumVarsEquiv (σ : Type*) : (Fin 2 × σ) ≃ (σ ⊕ σ) where
  toFun p := if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
  invFun := Sum.elim (fun i ↦ (0, i)) (fun i ↦ (1, i))
  left_inv := by rintro ⟨b, i⟩; fin_cases b <;> simp
  right_inv := by rintro (i | i) <;> simp

variable (F : MvFormalGroup σ R)

/-- The group law with variables indexed by `σ ⊕ σ`. -/
private def toSumPowerSeries (i : σ) : MvPowerSeries (σ ⊕ σ) R :=
  rename (sumVarsEquiv σ) (F.toPowerSeries i)

private theorem constantCoeff_toSumPowerSeries (i : σ) :
    constantCoeff (F.toSumPowerSeries i) = 0 := by
  simpa only [toSumPowerSeries, constantCoeff_rename] using F.zero_constantCoeff i

private theorem hasSubst_toSumPowerSeries : HasSubst F.toSumPowerSeries := by
  have h : F.toSumPowerSeries = fun i ↦ (F.toPowerSeries i).subst (X ∘ sumVarsEquiv σ) :=
    funext fun i ↦ rename_eq_subst _ _
  rw [h]
  exact F.hasSubst.subst (HasSubst.X_comp _)

private theorem implicitJacobianLeft_toSumPowerSeries :
    Cofinite.implicitJacobianLeft F.toSumPowerSeries = 1 := by
  ext i j
  have h : coeff (single (Sum.inl j) 1) (F.toSumPowerSeries i) =
      coeff (single (0, j) 1) (F.toPowerSeries i) := by
    simpa [sumVarsEquiv, toSumPowerSeries] using
      coeff_embDomain_rename (sumVarsEquiv σ).toEmbedding (F.toPowerSeries i) (single (0, j) 1)
  change coeff (single (Sum.inl j) 1) (F.toSumPowerSeries i) = _
  rw [h, F.lin_coeff_X]
  simp [Matrix.one_apply, eq_comm]

private theorem isCofiniteInverse_one :
    Matrix.IsCofiniteInverse 1 (Cofinite.implicitJacobianLeft F.toSumPowerSeries) := by
  rw [implicitJacobianLeft_toSumPowerSeries]
  exact .one

private theorem subst_toSumPowerSeries {a b : σ → MvPowerSeries σ R} (ha : HasSubst a)
    (hb : HasSubst b) (i : σ) :
    (F.toSumPowerSeries i).subst (Sum.elim a b) = (F.toPowerSeries i).subst (uncurry ![a, b]) := by
  have hs := ha.sumElim hb
  rw [toSumPowerSeries, rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) hs]
  congr 1
  funext ⟨k, j⟩
  fin_cases k <;> simp [subst_X hs, sumVarsEquiv]

/-- The formal inverse `i(X)`, the unique substitutable solution of `F(i(X), X) = 0` with zero
constant terms. -/
@[no_expose]
def inv : σ → MvPowerSeries σ R :=
  implicitFunctionLeftCofinite F.toSumPowerSeries 1

@[simp]
theorem constantCoeff_inv (i : σ) : constantCoeff (F.inv i) = 0 :=
  constantCoeff_implicitFunctionLeftCofinite F.constantCoeff_toSumPowerSeries
    F.hasSubst_toSumPowerSeries F.isCofiniteInverse_one i

/-- The inverse satisfies the cofinite condition, so it can be substituted. -/
theorem hasSubst_inv : HasSubst F.inv :=
  hasSubst_implicitFunctionLeftCofinite F.constantCoeff_toSumPowerSeries
    F.hasSubst_toSumPowerSeries F.isCofiniteInverse_one

/-- The inverse is a left inverse: `F(i(X), X) = 0`. -/
@[simp]
theorem inv_left (i : σ) : (F.toPowerSeries i).subst (uncurry ![F.inv, X]) = 0 := by
  rw [← F.subst_toSumPowerSeries F.hasSubst_inv .X_self]
  exact subst_implicitFunctionLeftCofinite F.constantCoeff_toSumPowerSeries
    F.hasSubst_toSumPowerSeries F.isCofiniteInverse_one i

/-- Any substitutable left inverse with zero constant terms is `F.inv`. -/
theorem eq_inv (a : σ → MvPowerSeries σ R) (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0)
    (h : ∀ i, (F.toPowerSeries i).subst (uncurry ![a, X]) = 0) : a = F.inv :=
  eq_implicitFunctionLeftCofinite F.constantCoeff_toSumPowerSeries F.hasSubst_toSumPowerSeries
    F.isCofiniteInverse_one a ha ha0 fun i ↦ (F.subst_toSumPowerSeries ha .X_self i).trans (h i)

/-- The left inverse equation after any admissible substitution: `F(i(a), a) = 0`. -/
@[simp]
theorem inv_left_subst {τ : Type*} {a : σ → MvPowerSeries τ R} (ha : HasSubst a) (i : σ) :
    (F.toPowerSeries i).subst (uncurry ![fun j ↦ (F.inv j).subst a, a]) = 0 := by
  have h := congrArg (subst a) (F.inv_left i)
  rw [subst_pair_subst _ _ _ (F.hasSubst_inv.pair .X_self) ha] at h
  simpa only [subst_X ha, ← substAlgHom_apply ha, map_zero] using h

/-- Applying the inverse twice gives the identity: `i(i(X)) = X`. -/
@[simp]
theorem inv_subst_inv (i : σ) : (F.inv i).subst F.inv = X i := by
  have hj : HasSubst fun k ↦ (F.inv k).subst F.inv := F.hasSubst_inv.subst F.hasSubst_inv
  have h := F.assoc_subst hj F.hasSubst_inv .X_self i
  simp only [F.inv_left_subst F.hasSubst_inv, F.inv_left, ← Pi.zero_def] at h
  rw [F.zero_add .X_self, F.add_zero hj] at h
  exact h.symm

/-- The inverse is also a right inverse: `F(X, i(X)) = 0`. -/
@[simp]
theorem inv_right (i : σ) : (F.toPowerSeries i).subst (uncurry ![X, F.inv]) = 0 := by
  simpa only [inv_subst_inv] using F.inv_left_subst F.hasSubst_inv i

end Inverse

/-- The inverse of the additive formal group law is coordinatewise negation. -/
@[simp]
theorem inv_additive (i : σ) : (additive σ R).inv i = -X i := by
  refine (congrFun ((additive σ R).eq_inv (-X) HasSubst.X_self.neg (by simp) fun j ↦ ?_) i).symm
  change (X (0, j) + X (1, j) : MvPowerSeries (Fin 2 × σ) R).subst _ = 0
  simp [subst_add (HasSubst.X_self.neg.pair .X_self),
    subst_X (HasSubst.X_self.neg.pair .X_self)]

end MvFormalGroup
