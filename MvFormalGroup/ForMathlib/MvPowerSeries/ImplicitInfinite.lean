/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import MvFormalGroup.ForMathlib.MvPowerSeries.Substitution

/-!
# The formal implicit function theorem for infinitely many equations

Let `F(X, Y)` be a family of power series with `F(0, 0) = 0`, where the variables `X`, `Y` and
the equations are indexed by possibly infinite types `σ`, `τ`, `ι`. If every monomial occurs in
only finitely many `Fᵢ` and the Jacobian `implicitJacobian F hF : (τ →₀ R) →ₗ[R] (ι →₀ R)` is
bijective, then `F(X, α(X)) = 0` has a unique substitutable solution `α` with `α(0) = 0`.

## Main results

* `MvPowerSeries.existsUnique_implicitFunction`: the formal implicit function theorem.
* `MvPowerSeries.existsUnique_implicitFunctionLeft`: the same, solving for the first variable
  block.
* `MvPowerSeries.existsUnique_implicitFunction_of_isUnit_det`: the case of finitely many
  equations with invertible Jacobian determinant.
-/

@[expose] public section

noncomputable section

open Finsupp Function

namespace MvPowerSeries

variable {R : Type*} [CommRing R] {ι σ τ υ : Type*}

/-! ### Coefficientwise fixed points -/

section FixedPoint

variable {ι : Type*} (T : (ι → MvPowerSeries τ R) → ι → MvPowerSeries τ R)

private def iterLimit (i : ι) : MvPowerSeries τ R :=
  fun d ↦ coeff d ((T^[d.degree + 1]) 0 i)

variable
  (hT0 : ∀ a, (HasSubst a ∧ ∀ i, constantCoeff (a i) = 0) →
    HasSubst (T a) ∧ ∀ i, constantCoeff (T a i) = 0)
  (hT : ∀ (n : ℕ) a b, (HasSubst a ∧ (∀ i, constantCoeff (a i) = 0)) →
    (HasSubst b ∧ (∀ i, constantCoeff (b i) = 0)) →
    (∀ i, (n : ℕ∞) ≤ (a i - b i).order) →
    ∀ i, ((n + 1 : ℕ) : ℕ∞) ≤ (T a i - T b i).order)

include hT0 in
private theorem iterate_admissible (n : ℕ) :
    HasSubst ((T^[n]) 0) ∧ ∀ i, constantCoeff ((T^[n]) 0 i) = 0 := by
  induction n with
  | zero => simp [hasSubst_def]
  | succ n ih =>
    rw [iterate_succ_apply']
    exact hT0 _ ih

include hT0 hT in
private theorem le_order_iterate_sub (m k : ℕ) (i : ι) :
    k ≤ ((T^[m + k]) 0 i - (T^[k]) 0 i).order := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, iterate_succ_apply', iterate_succ_apply']
    have h1 := iterate_admissible T hT0 (m + k)
    have h2 := iterate_admissible T hT0 k
    exact hT k _ _ h1 h2 ih i

include hT0 hT in
private theorem le_order_iterLimit_sub (n : ℕ) (i : ι) :
    n ≤ (iterLimit T i - (T^[n]) 0 i).order := by
  refine nat_le_order fun d hd ↦ ?_
  rw [map_sub, sub_eq_zero]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hd
  exact (coeff_eq_of_lt_order_sub
    ((Nat.cast_lt.mpr (lt_add_one _)).trans_le (le_order_iterate_sub T hT0 hT m _ i))).symm

include hT0 in
private theorem iterLimit_admissible :
    HasSubst (iterLimit T) ∧ ∀ i, constantCoeff (iterLimit T i) = 0 := by
  have h0 (i : ι) : constantCoeff (iterLimit T i) = 0 := by
    simpa [iterLimit, ← coeff_zero_eq_constantCoeff_apply, coeff_apply] using
      (iterate_admissible T hT0 1).2 i
  exact ⟨⟨fun i ↦ by simp [h0 i], fun d ↦ (iterate_admissible T hT0 (d.degree + 1)).1.coeff_zero d⟩,
    h0⟩

include hT0 hT in
private theorem map_iterLimit : T (iterLimit T) = iterLimit T := by
  funext i
  ext d
  have h := hT _ _ _ (iterLimit_admissible T hT0) (iterate_admissible T hT0 _)
    (le_order_iterLimit_sub T hT0 hT (d.degree + 1)) i
  rw [← iterate_succ_apply' T] at h
  rw [coeff_eq_of_lt_order_sub ((Nat.cast_lt.mpr (by omega)).trans_le h),
    coeff_eq_of_lt_order_sub ((Nat.cast_lt.mpr (by omega)).trans_le
      (le_order_iterLimit_sub T hT0 hT (d.degree + 1 + 1) i))]

include hT0 hT in
private theorem eq_iterLimit (b : ι → MvPowerSeries τ R)
    (hb : HasSubst b ∧ ∀ i, constantCoeff (b i) = 0) (hbfix : T b = b) : b = iterLimit T := by
  have h (n : ℕ) : ∀ i, (n : ℕ∞) ≤ (b i - iterLimit T i).order := by
    induction n with
    | zero => simp
    | succ n ih =>
      intro i
      simpa only [hbfix, map_iterLimit T hT0 hT] using
        hT n b (iterLimit T) hb (iterLimit_admissible T hT0) ih i
  funext i
  ext d
  exact coeff_eq_of_lt_order_sub ((Nat.cast_lt.mpr (lt_add_one _)).trans_le (h _ i))

end FixedPoint

/-! ### Linear maps acting on families of power series -/

section LinearMap

/-- The vector of coefficients of `d` in the family `v`. -/
def coeffFinsupp (v : ι → MvPowerSeries σ R) (hv : ∀ d, {i | coeff d (v i) ≠ 0}.Finite)
    (d : σ →₀ ℕ) : ι →₀ R :=
  Finsupp.ofSupportFinite (fun i ↦ coeff d (v i)) (hv d)

@[simp]
theorem coeffFinsupp_apply (v : ι → MvPowerSeries σ R)
    (hv : ∀ d, {i | coeff d (v i) ≠ 0}.Finite) (d : σ →₀ ℕ) (i : ι) :
    coeffFinsupp v hv d i = coeff d (v i) :=
  rfl

/-- The family obtained by applying `L` to the coefficient vectors of `v`. -/
def mapCoeffFinsupp (L : (ι →₀ R) →ₗ[R] (τ →₀ R)) (v : ι → MvPowerSeries σ R)
    (hv : ∀ d, {i | coeff d (v i) ≠ 0}.Finite) : τ → MvPowerSeries σ R :=
  fun j d ↦ L (coeffFinsupp v hv d) j

theorem coeff_mapCoeffFinsupp (L : (ι →₀ R) →ₗ[R] (τ →₀ R)) (v : ι → MvPowerSeries σ R)
    (hv : ∀ d, {i | coeff d (v i) ≠ 0}.Finite) (j : τ) (d : σ →₀ ℕ) :
    coeff d (mapCoeffFinsupp L v hv j) = L (coeffFinsupp v hv d) j :=
  rfl

theorem constantCoeff_mapCoeffFinsupp (L : (ι →₀ R) →ₗ[R] (τ →₀ R))
    {v : ι → MvPowerSeries σ R} (hv : ∀ d, {i | coeff d (v i) ≠ 0}.Finite)
    (hv0 : ∀ i, constantCoeff (v i) = 0) (j : τ) :
    constantCoeff (mapCoeffFinsupp L v hv j) = 0 := by
  have h : coeffFinsupp v hv 0 = 0 := by
    ext i
    simpa using hv0 i
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mapCoeffFinsupp, h, map_zero, Finsupp.zero_apply]

theorem mapCoeffFinsupp_eq_zero (L : (ι →₀ R) →ₗ[R] (τ →₀ R)) {v : ι → MvPowerSeries σ R}
    (hv : ∀ d, {i | coeff d (v i) ≠ 0}.Finite) (h : ∀ i, v i = 0) (j : τ) :
    mapCoeffFinsupp L v hv j = 0 := by
  ext d
  have hd : coeffFinsupp v hv d = 0 := by
    ext i
    simp [h i]
  rw [coeff_mapCoeffFinsupp, hd, map_zero, Finsupp.zero_apply, coeff_zero]

theorem HasSubst.mapCoeffFinsupp (L : (ι →₀ R) →ₗ[R] (τ →₀ R)) {v : ι → MvPowerSeries σ R}
    (hv : ∀ d, {i | coeff d (v i) ≠ 0}.Finite) (hv0 : ∀ i, constantCoeff (v i) = 0) :
    HasSubst (mapCoeffFinsupp L v hv) where
  const_coeff j := by simp [constantCoeff_mapCoeffFinsupp L hv hv0 j]
  coeff_zero d := (L (coeffFinsupp v hv d)).hasFiniteSupport

/-- Substitution commutes with the coefficientwise action of a linear map. -/
theorem subst_mapCoeffFinsupp (L : (ι →₀ R) →ₗ[R] (τ →₀ R)) {v : ι → MvPowerSeries σ R}
    (hv : HasSubst v) {a : σ → MvPowerSeries υ R} (ha : HasSubst a) (j : τ) :
    (mapCoeffFinsupp L v hv.coeff_zero j).subst a =
      mapCoeffFinsupp L (fun i ↦ (v i).subst a) (hv.subst ha).coeff_zero j := by
  classical
  ext e
  let c : (σ →₀ ℕ) → R := fun d ↦ coeff e (d.prod fun s n ↦ a s ^ n)
  have h1 (d : σ →₀ ℕ) : coeff d (fun _ ↦ (1 : R) : MvPowerSeries σ R) = 1 := rfl
  have hD : (Function.support c).Finite :=
    (coeff_subst_finite ha (fun _ ↦ 1 : MvPowerSeries σ R) e).subset fun d hd ↦ by
      simpa [Function.mem_support, h1, c] using hd
  have hsub (f : MvPowerSeries σ R) :
      coeff e (f.subst a) = ∑ d ∈ hD.toFinset, c d * coeff d f := by
    rw [coeff_subst ha]
    exact (finsum_eq_sum_of_support_subset _ <| Function.support_subset_iff'.mpr <| by
      simp +contextual [c]).trans (Finset.sum_congr rfl fun d _ ↦ mul_comm _ _)
  have hW : coeffFinsupp (fun i ↦ (v i).subst a) (hv.subst ha).coeff_zero e =
      ∑ d ∈ hD.toFinset, c d • coeffFinsupp v hv.coeff_zero d := by
    ext i
    simp [hsub]
  rw [coeff_mapCoeffFinsupp, hW, hsub]
  simp [coeff_mapCoeffFinsupp]

theorem eq_zero_of_mapCoeffFinsupp_eq_zero {L : (ι →₀ R) →ₗ[R] (τ →₀ R)}
    (hL : Function.Injective L) {v : ι → MvPowerSeries σ R}
    {hv : ∀ d, {i | coeff d (v i) ≠ 0}.Finite} (h : mapCoeffFinsupp L v hv = 0) : v = 0 := by
  ext i d
  have hd : L (coeffFinsupp v hv d) = 0 :=
    Finsupp.ext fun j ↦ congrArg (coeff d) (congrFun h j)
  exact DFunLike.congr_fun ((map_eq_zero_iff L hL).mp hd) i

end LinearMap

/-! ### Jacobians -/

/-- The Jacobian of `F` in the second variable block, as a linear map: `eⱼ` is sent to the
vector of coefficients of `Yⱼ` in the `Fᵢ`. -/
def implicitJacobian (F : ι → MvPowerSeries (σ ⊕ τ) R) (hF : HasSubst F) :
    (τ →₀ R) →ₗ[R] (ι →₀ R) :=
  Finsupp.linearCombination R fun j ↦ coeffFinsupp F hF.coeff_zero (single (Sum.inr j) 1)

theorem implicitJacobian_single (F : ι → MvPowerSeries (σ ⊕ τ) R) (hF : HasSubst F) (j : τ)
    (r : R) : implicitJacobian F hF (single j r) =
      r • coeffFinsupp F hF.coeff_zero (single (Sum.inr j) 1) :=
  Finsupp.linearCombination_single ..

@[simp]
theorem implicitJacobian_single_one_apply (F : ι → MvPowerSeries (σ ⊕ τ) R) (hF : HasSubst F)
    (j : τ) (i : ι) :
    implicitJacobian F hF (single j 1) i = coeff (single (Sum.inr j) 1) (F i) := by
  simp [implicitJacobian_single]

theorem implicitJacobian_apply (F : ι → MvPowerSeries (σ ⊕ τ) R) (hF : HasSubst F)
    (v : τ →₀ R) (i : ι) :
    implicitJacobian F hF v i = v.sum fun j r ↦ coeff (single (Sum.inr j) 1) (F i) * r := by
  simp [implicitJacobian, Finsupp.linearCombination_apply, Finsupp.sum_apply, mul_comm]

/-- The Jacobian of `F` in the first variable block, as a linear map. -/
def implicitJacobianLeft (F : ι → MvPowerSeries (τ ⊕ σ) R) (hF : HasSubst F) :
    (τ →₀ R) →ₗ[R] (ι →₀ R) :=
  Finsupp.linearCombination R fun j ↦ coeffFinsupp F hF.coeff_zero (single (Sum.inl j) 1)

theorem implicitJacobianLeft_single (F : ι → MvPowerSeries (τ ⊕ σ) R) (hF : HasSubst F) (j : τ)
    (r : R) : implicitJacobianLeft F hF (single j r) =
      r • coeffFinsupp F hF.coeff_zero (single (Sum.inl j) 1) :=
  Finsupp.linearCombination_single ..

@[simp]
theorem implicitJacobianLeft_single_one_apply (F : ι → MvPowerSeries (τ ⊕ σ) R)
    (hF : HasSubst F) (j : τ) (i : ι) :
    implicitJacobianLeft F hF (single j 1) i = coeff (single (Sum.inl j) 1) (F i) := by
  simp [implicitJacobianLeft_single]

theorem HasSubst.rename_sumComm {F : ι → MvPowerSeries (τ ⊕ σ) R} (hF : HasSubst F) :
    HasSubst fun i ↦ rename (Equiv.sumComm τ σ) (F i) := by
  simpa only [rename_eq_subst] using hF.subst (HasSubst.X_comp (Equiv.sumComm τ σ))

@[simp]
theorem implicitJacobian_rename_sumComm {F : ι → MvPowerSeries (τ ⊕ σ) R} (hF : HasSubst F) :
    implicitJacobian (fun i ↦ rename (Equiv.sumComm τ σ) (F i)) hF.rename_sumComm =
      implicitJacobianLeft F hF := by
  ext j i
  simpa using
    coeff_embDomain_rename (Equiv.sumComm τ σ).toEmbedding (F i) (single (Sum.inl j) 1)

/-! ### The implicit function theorem -/

section Implicit

/-- The solution `α` of `F(X, α(X)) = 0` given by `existsUnique_implicitFunction`. -/
def implicitFunction (F : ι → MvPowerSeries (σ ⊕ τ) R) (hF : HasSubst F)
    (hJ : Function.Bijective (implicitJacobian F hF)) : τ → MvPowerSeries σ R :=
  fun i d ↦ coeff d
    (((fun a i ↦ a i - (mapCoeffFinsupp (LinearEquiv.ofBijective _ hJ).symm.toLinearMap F
      hF.coeff_zero i).subst (Sum.elim X a))^[d.degree + 1]) 0 i)

variable {F : ι → MvPowerSeries (σ ⊕ τ) R} {K : (ι →₀ R) →ₗ[R] (τ →₀ R)}

private theorem implicitStep_admissible (hF0 : ∀ i, constantCoeff (F i) = 0)
    (hF : HasSubst F) {a : τ → MvPowerSeries σ R}
    (ha : HasSubst a ∧ ∀ i, constantCoeff (a i) = 0) :
    HasSubst (fun i ↦ a i - (mapCoeffFinsupp K F hF.coeff_zero i).subst (Sum.elim X a)) ∧
      ∀ i, constantCoeff
        (a i - (mapCoeffFinsupp K F hF.coeff_zero i).subst (Sum.elim X a)) = 0 := by
  have hp := HasSubst.X.sumElim ha.1
  refine ⟨ha.1.sub ((HasSubst.mapCoeffFinsupp K hF.coeff_zero hF0).subst hp), fun i ↦ ?_⟩
  rw [map_sub, ha.2, constantCoeff_subst_eq_zero hp (by rintro (s | t) <;> simp [ha.2])
    (constantCoeff_mapCoeffFinsupp K hF.coeff_zero hF0 i), sub_zero]

private theorem implicitStep_contract (hF : HasSubst F)
    (hKJ : ∀ v, K (implicitJacobian F hF v) = v)
    (n : ℕ) {a b : τ → MvPowerSeries σ R} (ha : HasSubst a ∧ ∀ i, constantCoeff (a i) = 0)
    (hb : HasSubst b ∧ ∀ i, constantCoeff (b i) = 0)
    (h : ∀ i, n ≤ (a i - b i).order) (i : τ) :
    (n + 1) ≤ ((a i - (mapCoeffFinsupp K F hF.coeff_zero i).subst (Sum.elim X a)) -
      (b i - (mapCoeffFinsupp K F hF.coeff_zero i).subst (Sum.elim X b))).order := by
  classical
  have hpa := HasSubst.X.sumElim ha.1
  have hpb := HasSubst.X.sumElim hb.1
  have key : n + 1 ≤
      (subst (Sum.elim X a) (X (Sum.inr i) - mapCoeffFinsupp K F hF.coeff_zero i) -
        subst (Sum.elim X b) (X (Sum.inr i) - mapCoeffFinsupp K F hF.coeff_zero i)).order := by
    refine add_le_order_subst_sub hpa hpb
      (fun s ↦ one_le_order_iff_constCoeff_eq_zero.mpr (by rcases s with s | s <;> simp [ha.2]))
      (fun s ↦ one_le_order_iff_constCoeff_eq_zero.mpr (by rcases s with s | s <;> simp [hb.2]))
      (by simp [h]) ?_
    rintro (s | k) hs
    · simp at hs
    · have hk : coeffFinsupp F hF.coeff_zero (single (Sum.inr k) 1) =
          implicitJacobian F hF (single k 1) := by
        rw [implicitJacobian_single, one_smul]
      rw [map_sub, coeff_mapCoeffFinsupp, hk, hKJ, coeff_index_single_X, Finsupp.single_apply]
      simp
  simpa [subst_sub, subst_X, hpa, hpb] using key

variable (hF0 : ∀ i, constantCoeff (F i) = 0) (hF : HasSubst F)
  (hJ : Function.Bijective (implicitJacobian F hF))

include hF0 hF hJ

@[simp]
theorem constantCoeff_implicitFunction (i : τ) :
    constantCoeff (implicitFunction F hF hJ i) = 0 :=
  (iterLimit_admissible _ fun _ ha ↦ implicitStep_admissible hF0 hF ha).2 i

theorem HasSubst.implicitFunction : HasSubst (implicitFunction F hF hJ) :=
  (iterLimit_admissible _ fun _ ha ↦ implicitStep_admissible hF0 hF ha).1

@[simp]
theorem subst_implicitFunction (i : ι) :
    (F i).subst (Sum.elim X (implicitFunction F hF hJ)) = 0 := by
  have hp := HasSubst.X.sumElim <| HasSubst.implicitFunction hF0 hF hJ
  have hG (j : τ) : (mapCoeffFinsupp (LinearEquiv.ofBijective _ hJ).symm.toLinearMap F
      hF.coeff_zero j).subst (Sum.elim X (implicitFunction F hF hJ)) = 0 := by
    have h : implicitFunction F hF hJ j -
        (mapCoeffFinsupp (LinearEquiv.ofBijective _ hJ).symm.toLinearMap F
          hF.coeff_zero j).subst (Sum.elim X (implicitFunction F hF hJ)) =
        implicitFunction F hF hJ j :=
      congrFun (map_iterLimit _ (fun _ ha ↦ implicitStep_admissible hF0 hF ha)
        (fun n _ _ ha hb h ↦ implicitStep_contract hF
          (LinearEquiv.ofBijective_symm_apply_apply _) n ha hb h)) j
    exact sub_eq_self.mp h
  have h0 := eq_zero_of_mapCoeffFinsupp_eq_zero (LinearEquiv.ofBijective _ hJ).symm.injective
    (hv := (hF.subst hp).coeff_zero) (funext fun j ↦ by
      rw [← subst_mapCoeffFinsupp _ hF hp j]
      exact hG j)
  exact congrFun h0 i

theorem eq_implicitFunction (a : τ → MvPowerSeries σ R) (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (h : ∀ i, (F i).subst (Sum.elim X a) = 0) :
    a = implicitFunction F hF hJ := by
  refine eq_iterLimit _ (fun _ ha ↦ implicitStep_admissible hF0 hF ha)
    (fun n _ _ ha hb h ↦ implicitStep_contract hF
      (LinearEquiv.ofBijective_symm_apply_apply _) n ha hb h) a ⟨ha, ha0⟩
    (funext fun i ↦ ?_)
  simp [subst_mapCoeffFinsupp _ hF (HasSubst.X.sumElim ha) i, mapCoeffFinsupp_eq_zero _ _ h]

/-- **Formal implicit function theorem**: if `F(0, 0) = 0` and the Jacobian is bijective, then
`F(X, α(X)) = 0` has a unique substitutable solution `α` with `α(0) = 0`. -/
theorem existsUnique_implicitFunction :
    ∃! a : τ → MvPowerSeries σ R,
      HasSubst a ∧ (∀ i, constantCoeff (a i) = 0) ∧ ∀ i, (F i).subst (Sum.elim X a) = 0 :=
  ⟨_, ⟨HasSubst.implicitFunction hF0 hF hJ,
      constantCoeff_implicitFunction hF0 hF hJ,
      subst_implicitFunction hF0 hF hJ⟩,
    fun a h ↦ eq_implicitFunction hF0 hF hJ a h.1 h.2.1 h.2.2⟩

end Implicit

/-! ### Solving for the first variable block -/

section ImplicitLeft

private theorem subst_rename_sumComm_of_hasSubst (f : MvPowerSeries (τ ⊕ σ) R)
    {a : τ → MvPowerSeries σ R} (ha : HasSubst a) :
    (rename (Equiv.sumComm τ σ) f).subst (Sum.elim X a) = f.subst (Sum.elim a X) := by
  have hs := HasSubst.X.sumElim ha
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) hs]
  congr 1
  ext (j | j) : 1 <;> simp [subst_X hs]

theorem bijective_implicitJacobian_rename_sumComm {F : ι → MvPowerSeries (τ ⊕ σ) R}
    {hF : HasSubst F} (hJ : Function.Bijective (implicitJacobianLeft F hF)) :
    Function.Bijective
      (implicitJacobian (fun i ↦ rename (Equiv.sumComm τ σ) (F i)) hF.rename_sumComm) := by
  rwa [implicitJacobian_rename_sumComm]

/-- The solution `α` of `F(α(X), X) = 0` given by `existsUnique_implicitFunctionLeft`. -/
def implicitFunctionLeft (F : ι → MvPowerSeries (τ ⊕ σ) R) (hF : HasSubst F)
    (hJ : Function.Bijective (implicitJacobianLeft F hF)) : τ → MvPowerSeries σ R :=
  implicitFunction (fun i ↦ rename (Equiv.sumComm τ σ) (F i)) hF.rename_sumComm
    (bijective_implicitJacobian_rename_sumComm hJ)

variable {F : ι → MvPowerSeries (τ ⊕ σ) R}
  (hF0 : ∀ i, constantCoeff (F i) = 0) (hF : HasSubst F)
  (hJ : Function.Bijective (implicitJacobianLeft F hF))

include hF0 hF hJ

@[simp]
theorem constantCoeff_implicitFunctionLeft (i : τ) :
    constantCoeff (implicitFunctionLeft F hF hJ i) = 0 :=
  constantCoeff_implicitFunction (by simpa [constantCoeff_rename] using hF0) _ _ i

theorem HasSubst.implicitFunctionLeft : HasSubst (implicitFunctionLeft F hF hJ) :=
  HasSubst.implicitFunction (by simpa [constantCoeff_rename] using hF0) _ _

@[simp]
theorem subst_implicitFunctionLeft (i : ι) :
    (F i).subst (Sum.elim (implicitFunctionLeft F hF hJ) X) = 0 :=
  (subst_rename_sumComm_of_hasSubst _ (HasSubst.implicitFunctionLeft hF0 hF hJ)).symm.trans
    (subst_implicitFunction (by simpa [constantCoeff_rename] using hF0) _ _ i)

theorem eq_implicitFunctionLeft (a : τ → MvPowerSeries σ R) (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (h : ∀ i, (F i).subst (Sum.elim a X) = 0) :
    a = implicitFunctionLeft F hF hJ :=
  eq_implicitFunction (by simpa [constantCoeff_rename] using hF0) _ _ a ha ha0
    fun i ↦ (subst_rename_sumComm_of_hasSubst _ ha).trans (h i)

/-- **Formal implicit function theorem** for `F(α(X), X) = 0`. -/
theorem existsUnique_implicitFunctionLeft :
    ∃! a : τ → MvPowerSeries σ R,
      HasSubst a ∧ (∀ i, constantCoeff (a i) = 0) ∧ ∀ i, (F i).subst (Sum.elim a X) = 0 :=
  ⟨_, ⟨HasSubst.implicitFunctionLeft hF0 hF hJ,
      constantCoeff_implicitFunctionLeft hF0 hF hJ,
      subst_implicitFunctionLeft hF0 hF hJ⟩,
    fun a h ↦ eq_implicitFunctionLeft hF0 hF hJ a h.1 h.2.1 h.2.2⟩

end ImplicitLeft

/-! ### Finitely many equations -/

section Finite

variable [Fintype τ] [DecidableEq τ]

/-- The Jacobian is bijective if its determinant is a unit. -/
theorem bijective_implicitJacobian_of_isUnit_det {F : τ → MvPowerSeries (σ ⊕ τ) R}
    (hF : HasSubst F)
    (hJ : IsUnit (Matrix.of fun i j ↦ coeff (single (Sum.inr j) 1) (F i)).det) :
    Function.Bijective (implicitJacobian F hF) := by
  have h : LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
      (implicitJacobian F hF) = Matrix.of fun i j ↦ coeff (single (Sum.inr j) 1) (F i) := by
    ext i j
    simp [LinearMap.toMatrix_apply]
  rw [← h] at hJ
  exact (LinearEquiv.ofIsUnitDet hJ).bijective

/-- The left Jacobian is bijective if its determinant is a unit. -/
theorem bijective_implicitJacobianLeft_of_isUnit_det {F : τ → MvPowerSeries (τ ⊕ σ) R}
    (hF : HasSubst F)
    (hJ : IsUnit (Matrix.of fun i j ↦ coeff (single (Sum.inl j) 1) (F i)).det) :
    Function.Bijective (implicitJacobianLeft F hF) := by
  have h : LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne
      (implicitJacobianLeft F hF) = Matrix.of fun i j ↦ coeff (single (Sum.inl j) 1) (F i) := by
    ext i j
    simp [LinearMap.toMatrix_apply]
  rw [← h] at hJ
  exact (LinearEquiv.ofIsUnitDet hJ).bijective

/-- **Formal implicit function theorem** for finitely many equations with invertible Jacobian
determinant. -/
theorem existsUnique_implicitFunction_of_isUnit_det (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hF : ∀ i, constantCoeff (F i) = 0)
    (hJ : IsUnit (Matrix.of fun i j ↦ coeff (single (Sum.inr j) 1) (F i)).det) :
    ∃! a : τ → MvPowerSeries σ R,
      (∀ i, constantCoeff (a i) = 0) ∧
      (∀ i, (F i).subst (Sum.elim X a) = 0) := by
  have hF' := hasSubst_of_constantCoeff_zero hF
  have hJ' := bijective_implicitJacobian_of_isUnit_det hF' hJ
  exact ⟨_, ⟨constantCoeff_implicitFunction hF hF' hJ', subst_implicitFunction hF hF' hJ'⟩,
    fun a h ↦ eq_implicitFunction hF hF' hJ' a (hasSubst_of_constantCoeff_zero h.1) h.1 h.2⟩

/-- **Formal implicit function theorem** for `F(α(X), X) = 0`, for finitely many equations with
invertible Jacobian determinant. -/
theorem existsUnique_implicitFunctionLeft_of_isUnit_det (F : τ → MvPowerSeries (τ ⊕ σ) R)
    (hF : ∀ i, constantCoeff (F i) = 0)
    (hJ : IsUnit (Matrix.of fun i j ↦ coeff (single (Sum.inl j) 1) (F i)).det) :
    ∃! a : τ → MvPowerSeries σ R,
      (∀ i, constantCoeff (a i) = 0) ∧
      (∀ i, (F i).subst (Sum.elim a X) = 0) := by
  have hF' := hasSubst_of_constantCoeff_zero hF
  have hJ' := bijective_implicitJacobianLeft_of_isUnit_det hF' hJ
  exact ⟨_, ⟨constantCoeff_implicitFunctionLeft hF hF' hJ',
      subst_implicitFunctionLeft hF hF' hJ'⟩,
    fun a h ↦ eq_implicitFunctionLeft hF hF' hJ' a (hasSubst_of_constantCoeff_zero h.1) h.1 h.2⟩

end Finite

end MvPowerSeries
