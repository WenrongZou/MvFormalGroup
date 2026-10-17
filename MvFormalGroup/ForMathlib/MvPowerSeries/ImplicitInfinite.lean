/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Rename
public import MvFormalGroup.ForMathlib.Matrix.ColumnFinite
public import MvFormalGroup.ForMathlib.Matrix.Mul
public import MvFormalGroup.ForMathlib.MvPowerSeries.Substitution

/-!
# The formal implicit function theorem for infinitely many equations

The classical formal implicit function theorem solves `F(X, Y) = 0` for finitely many
equations and finitely many variables. Here the variables `X`
are indexed by `σ`, the equations `Fⱼ` by `ι`, and the unknowns `Y` by `τ`; all three may be
infinite, and `ι`, `τ` need not be the same type. The Jacobian `J` is then an `ι × τ` matrix.
Three extra conditions are needed.

* `HasSubst F`: every monomial occurs in only finitely many `Fⱼ`. This is the analogue of
  Hazewinkel's (9.6.3), and makes the Jacobian `J` column-finite.
* `Matrix.IsCofiniteInverse K J`: the Jacobian has a two-sided inverse `K`, a column-finite
  `τ × ι` matrix with `K J = 1` and `J K = 1`. Equivalently, `J` induces an isomorphism of free
  modules `R^(τ) ≅ R^(ι)`; so if `R` is nontrivial, `ι` and `τ` have the same cardinality. For
  infinite index sets a one-sided inverse is not enough: a shift has a one-sided inverse, and
  then existence or uniqueness fails. For a finite square system with `IsUnit J.det`, one can
  take `K = J⁻¹` (`Matrix.IsCofiniteInverse.of_isUnit_det`).
* The solution `α` itself satisfies `HasSubst α`, which is needed to substitute it.

The proof replaces `F` by `K F`, whose Jacobian is `1`, and takes the coefficientwise limit of
the iterates of `a ↦ a - (K F)(X, a)`. The matrix `K` acts on a family of power series
coefficientwise (`MvPowerSeries.finsumMulVec`, built from `Matrix.finsumMulVec`); each
coefficient is a finite sum. Agreement
below degree `n` is expressed as `n ≤ (f - g).order`, since `truncTotal` needs finitely many
variables; each step improves it by one degree (`MvPowerSeries.add_le_order_subst_sub`).

## Main results

* `MvPowerSeries.existsUnique_implicitFunction`: the implicit function theorem.
* `MvPowerSeries.existsUnique_implicitFunctionLeft`: the version solving for the first variable
  block.
* `MvPowerSeries.existsUnique_implicitFunction_of_isUnit_det`,
  `MvPowerSeries.existsUnique_implicitFunctionLeft_of_isUnit_det`: the classical theorem for
  finitely many equations, the case `K = J⁻¹`.
-/

@[expose] public section

noncomputable section

open Finsupp Function

namespace MvPowerSeries

variable {R : Type*} [CommRing R] {ι σ τ υ : Type*}

/-! ### Coefficientwise fixed points

A map `T` on substitutable families that improves agreement by one degree has a unique
substitutable fixed point with zero constant terms, obtained as the coefficientwise limit of
its iterates from zero. -/

section FixedPoint

variable {ι : Type*} (T : (ι → MvPowerSeries τ R) → ι → MvPowerSeries τ R)

/-- The coefficientwise limit of the iterates of `T` starting at zero. -/
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

/-! ### Column-finite matrices acting on families of power series -/

section CofiniteMatrix

/-- A matrix acting coefficientwise on a family of power series, `(K v)ᵢ = ∑ⱼ Kᵢⱼ vⱼ`: the
coefficient of `d` is `Matrix.finsumMulVec` applied to the coefficients of `d`. When each
monomial occurs in only finitely many `vⱼ`, every coefficient is a finite sum.

This is not `Matrix.finsumMulVec` with power series entries: a `finsum` of power series is `0`
as soon as infinitely many terms are nonzero, even if each coefficient is a finite sum. -/
def finsumMulVec (K : Matrix τ ι R) (v : ι → MvPowerSeries σ R) : τ → MvPowerSeries σ R :=
  fun i d ↦ K.finsumMulVec (fun j ↦ coeff d (v j)) i

theorem coeff_finsumMulVec (K : Matrix τ ι R) (v : ι → MvPowerSeries σ R) (i : τ)
    (d : σ →₀ ℕ) : coeff d (finsumMulVec K v i) = ∑ᶠ j, K i j * coeff d (v j) :=
  rfl

theorem constantCoeff_finsumMulVec (K : Matrix τ ι R) {v : ι → MvPowerSeries σ R}
    (hv : ∀ j, constantCoeff (v j) = 0) (i : τ) : constantCoeff (finsumMulVec K v i) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_finsumMulVec]
  simp [coeff_zero_eq_constantCoeff_apply, hv]

@[simp]
theorem finsumMulVec_zero (K : Matrix τ ι R) :
    finsumMulVec K (0 : ι → MvPowerSeries σ R) = 0 := by
  funext i
  ext d
  simp [coeff_finsumMulVec]

/-- A column-finite matrix preserves the cofinite condition. -/
theorem HasSubst.finsumMulVec {K : Matrix τ ι R} (hK : ∀ j, {i | K i j ≠ 0}.Finite)
    {v : ι → MvPowerSeries σ R} (hv : HasSubst v) (hv0 : ∀ j, constantCoeff (v j) = 0) :
    HasSubst (finsumMulVec K v) where
  const_coeff i := by simp [constantCoeff_finsumMulVec K hv0 i]
  coeff_zero d := Matrix.finite_support_finsumMulVec hK (hv.coeff_zero d)

/-- Substitution commutes with the coefficientwise action of a matrix. -/
theorem subst_finsumMulVec (K : Matrix τ ι R) {v : ι → MvPowerSeries σ R} (hv : HasSubst v)
    {a : σ → MvPowerSeries υ R} (ha : HasSubst a) (i : τ) :
    (finsumMulVec K v i).subst a = finsumMulVec K (fun j ↦ (v j).subst a) i := by
  classical
  ext e
  let c : (σ →₀ ℕ) → R := fun d ↦ coeff e (d.prod fun s n ↦ a s ^ n)
  have h1 (d : σ →₀ ℕ) : coeff d (fun _ ↦ (1 : R) : MvPowerSeries σ R) = 1 := rfl
  have hD : (Function.support c).Finite :=
    (coeff_subst_finite ha (fun _ ↦ 1 : MvPowerSeries σ R) e).subset fun d hd ↦ by
      simpa [Function.mem_support, h1, c] using hd
  let D := hD.toFinset
  let J := D.biUnion fun d ↦ (hv.coeff_zero d).toFinset
  have hvJ : ∀ d ∈ D, ∀ j ∉ J, coeff d (v j) = 0 := by simp +contextual [D, J]
  have hL : ∀ d ∈ D, coeff d (finsumMulVec K v i) = ∑ j ∈ J, K i j * coeff d (v j) :=
    fun d hd ↦ finsum_eq_sum_of_support_subset _ <|
      Function.support_subset_iff'.mpr <| by simp +contextual [hvJ d hd]
  have hR : ∀ j, coeff e ((v j).subst a) = ∑ d ∈ D, coeff d (v j) * c d := fun j ↦ by
    rw [coeff_subst ha]
    apply finsum_eq_sum_of_support_subset _ <|
      Function.support_subset_iff'.mpr (by simp +contextual [c, D])
  rw [coeff_subst ha, coeff_finsumMulVec,
    finsum_eq_sum_of_support_subset _ (s := D) (Function.support_subset_iff'.mpr _),
    finsum_eq_sum_of_support_subset _ (s := J) (Function.support_subset_iff'.mpr _)]
  · rw [Finset.sum_congr rfl fun d hd ↦ by rw [hL d hd]]
    simpa [hR, Finset.sum_mul, Finset.mul_sum, mul_assoc] using Finset.sum_comm
  · simp +contextual [hR, Finset.sum_eq_zero, D, J]
  · simp +contextual [c, D]

/-- If `J K = 1`, then the column-finite matrix `K` is injective on families satisfying the
cofinite condition. -/
theorem eq_zero_of_finsumMulVec_eq_zero [DecidableEq ι] {K : Matrix τ ι R} {J : Matrix ι τ R}
    (hK : ∀ j, {i | K i j ≠ 0}.Finite)
    (hJK : ∀ i k, ∑ᶠ j, J i j * K j k = (1 : Matrix ι ι R) i k)
    {v : ι → MvPowerSeries σ R} (hv : ∀ d, {k | coeff d (v k) ≠ 0}.Finite)
    (h : finsumMulVec K v = 0) : v = 0 := by
  classical
  ext i d
  let Ks := (hv d).toFinset
  let Js := Ks.biUnion fun k ↦ (hK k).toFinset
  have hKs : ∀ k ∉ Ks, coeff d (v k) = 0 := by simp [Ks]
  have hJs : ∀ k ∈ Ks, ∀ j ∉ Js, K j k = 0 := by simp +contextual [Ks, Js]
  have hK0 (j : τ) : ∑ k ∈ Ks, K j k * coeff d (v k) = 0 := by
    rw [← finsum_eq_sum_of_support_subset, ← coeff_finsumMulVec, h, Pi.zero_apply, coeff_zero]
    simp +contextual [Function.support_subset_iff'.mpr , hKs]
  have hi : coeff d (v i) = ∑ k ∈ Ks, (∑ j ∈ Js, J i j * K j k) * coeff d (v k) := by
    rw [Finset.sum_congr rfl fun k hk ↦ by
      rw [← finsum_eq_sum_of_support_subset _ (Function.support_subset_iff'.mpr fun j hj ↦ by
        simp [hJs k hk j hj]), hJK]]
    by_cases hiK : i ∈ Ks
    · simp +contextual [Finset.sum_eq_single i, hiK, Matrix.one_apply_ne']
    · rw [hKs i hiK, Finset.sum_eq_zero fun k hk ↦ ?_]
      simp [(ne_of_mem_of_not_mem hk hiK).symm]
  rw [hi]
  simp only [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp [← Finset.mul_sum, hK0]

end CofiniteMatrix

/-! ### Jacobians -/

/-- The matrix of coefficients of the linear terms in the `Y` variables. -/
def implicitJacobian (F : ι → MvPowerSeries (σ ⊕ τ) R) : Matrix ι τ R :=
  fun i j ↦ coeff (single (Sum.inr j) 1) (F i)

@[simp]
theorem implicitJacobian_apply (F : ι → MvPowerSeries (σ ⊕ τ) R) (i : ι) (j : τ) :
    implicitJacobian F i j = coeff (single (Sum.inr j) 1) (F i) :=
  rfl

/-- The matrix of coefficients of the linear terms in the first variable block. -/
def implicitJacobianLeft (F : ι → MvPowerSeries (τ ⊕ σ) R) : Matrix ι τ R :=
  fun i j ↦ coeff (single (Sum.inl j) 1) (F i)

@[simp]
theorem implicitJacobianLeft_apply (F : ι → MvPowerSeries (τ ⊕ σ) R) (i : ι) (j : τ) :
    implicitJacobianLeft F i j = coeff (single (Sum.inl j) 1) (F i) :=
  rfl

/-- Swapping the variable blocks turns the left Jacobian into the right Jacobian. -/
@[simp]
theorem implicitJacobian_rename_sumComm (F : ι → MvPowerSeries (τ ⊕ σ) R) :
    implicitJacobian (fun i ↦ rename (Equiv.sumComm τ σ) (F i)) = implicitJacobianLeft F := by
  ext i j
  simpa [implicitJacobian, implicitJacobianLeft] using
    coeff_embDomain_rename (Equiv.sumComm τ σ).toEmbedding _ (single (Sum.inl j) 1)

/-! ### The implicit function theorem -/

section Implicit

/- In this section, the map `T` of the fixed point section is the step `a ↦ a - (K F)(X, a)`,
that is, `T a i = a i - (finsumMulVec K F i).subst (Sum.elim X a)`. -/

/-- The implicit function, constructed coefficientwise: its coefficient of degree `d` is taken
from the `(d + 1)`st iterate of `a ↦ a - (K F)(X, a)`, starting from zero. -/
def implicitFunction (F : ι → MvPowerSeries (σ ⊕ τ) R) (K : Matrix τ ι R) :
    τ → MvPowerSeries σ R :=
  fun i d ↦ coeff d
    (((fun a i ↦ a i - (finsumMulVec K F i).subst (Sum.elim X a))^[d.degree + 1]) 0 i)

variable {F : ι → MvPowerSeries (σ ⊕ τ) R} {K : Matrix τ ι R}

private theorem implicitStep_admissible (hF0 : ∀ i, constantCoeff (F i) = 0)
    (hF : HasSubst F) (hK : ∀ j, {i | K i j ≠ 0}.Finite) {a : τ → MvPowerSeries σ R}
    (ha : HasSubst a ∧ ∀ i, constantCoeff (a i) = 0) :
    HasSubst (fun i ↦ a i - (finsumMulVec K F i).subst (Sum.elim X a)) ∧
      ∀ i, constantCoeff (a i - (finsumMulVec K F i).subst (Sum.elim X a)) = 0 := by
  have hp := HasSubst.X.sumElim ha.1
  refine ⟨ha.1.sub ((hF.finsumMulVec hK hF0).subst hp), fun i ↦ ?_⟩
  rw [map_sub, ha.2, constantCoeff_subst_eq_zero hp (by rintro (s | t) <;> simp [ha.2])
    (constantCoeff_finsumMulVec K hF0 i), sub_zero]

private theorem implicitStep_contract [DecidableEq τ]
    (hKJ : ∀ i k, ∑ᶠ j, K i j * implicitJacobian F j k = (1 : Matrix τ τ R) i k)
    (n : ℕ) {a b : τ → MvPowerSeries σ R} (ha : HasSubst a ∧ ∀ i, constantCoeff (a i) = 0)
    (hb : HasSubst b ∧ ∀ i, constantCoeff (b i) = 0)
    (h : ∀ i, n ≤ (a i - b i).order) (i : τ) :
    (n + 1) ≤ ((a i - (finsumMulVec K F i).subst (Sum.elim X a)) -
      (b i - (finsumMulVec K F i).subst (Sum.elim X b))).order := by
  classical
  have hpa := HasSubst.X.sumElim ha.1
  have hpb := HasSubst.X.sumElim hb.1
  have key : n + 1 ≤ (subst (Sum.elim X a) (X (Sum.inr i) - finsumMulVec K F i) -
    subst (Sum.elim X b) (X (Sum.inr i) - finsumMulVec K F i)).order := by
    refine add_le_order_subst_sub hpa hpb
      (fun s ↦ one_le_order_iff_constCoeff_eq_zero.mpr (by rcases s with s | s <;> simp [ha.2]))
      (fun s ↦ one_le_order_iff_constCoeff_eq_zero.mpr (by rcases s with s | s <;> simp [hb.2]))
      (by simp [h]) ?_
    rintro (s | k) hs
    · simp at hs
    · simp_rw [map_sub, coeff_finsumMulVec, ← implicitJacobian_apply, hKJ i k]
      by_cases! hik : i = k
      · simp [hik, Matrix.one_apply]
      · simp [coeff_index_single_X, hik, hik.symm]
  simpa [subst_sub, subst_X, hpa, hpb] using key

variable [DecidableEq τ] [DecidableEq ι] (hF0 : ∀ i, constantCoeff (F i) = 0) (hF : HasSubst F)
  (hK : Matrix.IsCofiniteInverse K (implicitJacobian F))
/- `Matrix.IsCofiniteInvertible J`. -/

/- Include these three assumption in the following theorems. -/
include hF0 hF hK
@[simp]
theorem constantCoeff_implicitFunction (i : τ) :
    constantCoeff (implicitFunction F K i) = 0 :=
  (iterLimit_admissible _ fun _ ha ↦ implicitStep_admissible hF0 hF hK.col_finite ha).2 i

/-- The implicit function satisfies the cofinite condition, so it can be substituted. -/
theorem HasSubst.implicitFunction : HasSubst (implicitFunction F K) :=
  (iterLimit_admissible _ fun _ ha ↦ implicitStep_admissible hF0 hF hK.col_finite ha).1

/-- The implicit function solves `F(X, α(X)) = 0`. -/
@[simp]
theorem subst_implicitFunction (i : ι) :
    (F i).subst (Sum.elim X (implicitFunction F K)) = 0 := by
  have hp := HasSubst.X.sumElim <| HasSubst.implicitFunction hF0 hF hK
  have hG (j : τ) : (finsumMulVec K F j).subst (Sum.elim X (implicitFunction F K)) = 0 := by
    have h : implicitFunction F K j -
        (finsumMulVec K F j).subst (Sum.elim X (implicitFunction F K)) = implicitFunction F K j :=
      congrFun (map_iterLimit _ (fun _ ha ↦ implicitStep_admissible hF0 hF hK.col_finite ha)
        (fun n _ _ ha hb h ↦ implicitStep_contract hK.mul_left n ha hb h)) j
    exact sub_eq_self.mp h
  have hv := hF.subst hp
  have h0 := eq_zero_of_finsumMulVec_eq_zero hK.col_finite hK.mul_right hv.coeff_zero
    (funext fun j ↦ by simp [← subst_finsumMulVec K hF hp j, hG j])
  exact congrFun h0 i

/-- Any substitutable solution with zero constant terms is the implicit function. -/
theorem eq_implicitFunction (a : τ → MvPowerSeries σ R) (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (h : ∀ i, (F i).subst (Sum.elim X a) = 0) :
    a = implicitFunction F K := by
  refine eq_iterLimit _ (fun _ ha ↦ implicitStep_admissible hF0 hF hK.col_finite ha)
    (fun n _ _ ha hb h ↦ implicitStep_contract hK.mul_left n ha hb h) a ⟨ha, ha0⟩
    (funext fun i ↦ ?_)
  have h0 : (fun j ↦ (F j).subst (Sum.elim X a)) = 0 := funext h
  simp [subst_finsumMulVec K hF (HasSubst.X.sumElim ha) i, h0, finsumMulVec_zero]

/-- **Formal implicit function theorem** for possibly infinitely many equations and variables.

Let the equations `Fⱼ` be indexed by `ι` and the unknowns `Y` by `τ`. If `F(0, 0) = 0`, every
monomial occurs in only finitely many `Fⱼ`, and the Jacobian has a two-sided inverse among
column-finite matrices, then there is a unique substitutable `α(X)`, indexed by `τ`, with
`α(0) = 0` and `F(X, α(X)) = 0`. -/
theorem existsUnique_implicitFunction :
    ∃! a : τ → MvPowerSeries σ R,
      HasSubst a ∧ (∀ i, constantCoeff (a i) = 0) ∧ ∀ i, (F i).subst (Sum.elim X a) = 0 :=
  ⟨_, ⟨HasSubst.implicitFunction hF0 hF hK,
      constantCoeff_implicitFunction hF0 hF hK,
      subst_implicitFunction hF0 hF hK⟩,
    fun a h ↦ eq_implicitFunction hF0 hF hK a h.1 h.2.1 h.2.2⟩

end Implicit

/-! ### Solving for the first variable block -/

section ImplicitLeft

private theorem hasSubst_rename_sumComm {F : ι → MvPowerSeries (τ ⊕ σ) R} (hF : HasSubst F) :
    HasSubst fun i ↦ rename (Equiv.sumComm τ σ) (F i) := by
  simpa only [rename_eq_subst] using hF.subst (HasSubst.X_comp (Equiv.sumComm τ σ))

private theorem subst_rename_sumComm_of_hasSubst (f : MvPowerSeries (τ ⊕ σ) R)
    {a : τ → MvPowerSeries σ R} (ha : HasSubst a) :
    (rename (Equiv.sumComm τ σ) f).subst (Sum.elim X a) = f.subst (Sum.elim a X) := by
  have hs := HasSubst.X.sumElim ha
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) hs]
  congr 1
  ext (j | j) : 1 <;> simp [subst_X hs]

variable [DecidableEq ι] [DecidableEq τ]

/-- The solution of `F(α(X), X) = 0`, obtained by exchanging the two variable blocks. -/
def implicitFunctionLeft (F : ι → MvPowerSeries (τ ⊕ σ) R) (K : Matrix τ ι R) :
    τ → MvPowerSeries σ R :=
  implicitFunction (fun i ↦ rename (Equiv.sumComm τ σ) (F i)) K

variable {F : ι → MvPowerSeries (τ ⊕ σ) R} {K : Matrix τ ι R}
  (hF0 : ∀ i, constantCoeff (F i) = 0) (hF : HasSubst F)
  (hK : Matrix.IsCofiniteInverse K (implicitJacobianLeft F))

include hK in
private theorem isCofiniteInverse_rename_sumComm :
    Matrix.IsCofiniteInverse K
      (implicitJacobian fun i ↦ rename (Equiv.sumComm τ σ) (F i)) := by
  rwa [implicitJacobian_rename_sumComm]

/- Include these three assumptions in the following theorems. -/
include hF0 hF hK
@[simp]
theorem constantCoeff_implicitFunctionLeft (i : τ) :
    constantCoeff (implicitFunctionLeft F K i) = 0 :=
  constantCoeff_implicitFunction (by simpa [constantCoeff_rename] using hF0)
    (hasSubst_rename_sumComm hF) (isCofiniteInverse_rename_sumComm hK) i

theorem HasSubst.implicitFunctionLeft : HasSubst (implicitFunctionLeft F K) :=
  HasSubst.implicitFunction (by simpa [constantCoeff_rename] using hF0)
    (hasSubst_rename_sumComm hF) (isCofiniteInverse_rename_sumComm hK)

/-- The left implicit function solves `F(α(X), X) = 0`. -/
@[simp]
theorem subst_implicitFunctionLeft (i : ι) :
    (F i).subst (Sum.elim (implicitFunctionLeft F K) X) = 0 :=
  (subst_rename_sumComm_of_hasSubst _ (HasSubst.implicitFunctionLeft hF0 hF hK)).symm.trans
    (subst_implicitFunction (by simpa [constantCoeff_rename] using hF0)
      (hasSubst_rename_sumComm hF) (isCofiniteInverse_rename_sumComm hK) i)

/-- Any substitutable solution of `F(a(X), X) = 0` with zero constant terms is the left
implicit function. -/
theorem eq_implicitFunctionLeft (a : τ → MvPowerSeries σ R) (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (h : ∀ i, (F i).subst (Sum.elim a X) = 0) :
    a = implicitFunctionLeft F K :=
  eq_implicitFunction (by simpa [constantCoeff_rename] using hF0)
    (hasSubst_rename_sumComm hF) (isCofiniteInverse_rename_sumComm hK) a ha ha0
    fun i ↦ (subst_rename_sumComm_of_hasSubst _ ha).trans (h i)

/-- **Formal implicit function theorem**, solving for the first variable block, for possibly
infinitely many equations and variables. -/
theorem existsUnique_implicitFunctionLeft :
    ∃! a : τ → MvPowerSeries σ R,
      HasSubst a ∧ (∀ i, constantCoeff (a i) = 0) ∧ ∀ i, (F i).subst (Sum.elim a X) = 0 :=
  ⟨_, ⟨HasSubst.implicitFunctionLeft hF0 hF hK,
      constantCoeff_implicitFunctionLeft hF0 hF hK,
      subst_implicitFunctionLeft hF0 hF hK⟩,
    fun a h ↦ eq_implicitFunctionLeft hF0 hF hK a h.1 h.2.1 h.2.2⟩

end ImplicitLeft

/-! ### Finitely many equations

For finitely many equations, `HasSubst F` and `HasSubst α` hold automatically, and if the
Jacobian `J` has invertible determinant then `J⁻¹` is a cofinite inverse
(`Matrix.IsCofiniteInverse.of_isUnit_det`). So the classical formal implicit function theorem is
the case `K = J⁻¹` of the theorem above; the variables `σ` may even be infinite. -/

section Finite

variable [Fintype τ] [DecidableEq τ]

@[simp]
theorem constantCoeff_implicitFunction_of_isUnit_det (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobian F).det) (i : τ) :
    constantCoeff (implicitFunction F (implicitJacobian F)⁻¹ i) = 0 :=
  constantCoeff_implicitFunction hF (hasSubst_of_constantCoeff_zero hF) (.of_isUnit_det hJ) i

/-- The implicit function can be substituted. -/
theorem HasSubst.implicitFunction_of_isUnit_det (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobian F).det) :
    HasSubst (MvPowerSeries.implicitFunction F (implicitJacobian F)⁻¹) :=
  .implicitFunction hF (hasSubst_of_constantCoeff_zero hF) (.of_isUnit_det hJ)

/-- The implicit function solves the original system of equations. -/
@[simp]
theorem subst_implicitFunction_of_isUnit_det (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobian F).det) (i : τ) :
    (F i).subst (Sum.elim X (implicitFunction F (implicitJacobian F)⁻¹)) = 0 :=
  subst_implicitFunction hF (hasSubst_of_constantCoeff_zero hF) (.of_isUnit_det hJ) i

/-- Any zero-constant-term solution is the implicit function. -/
theorem eq_implicitFunction_of_isUnit_det (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobian F).det)
    (a : τ → MvPowerSeries σ R) (ha0 : ∀ i, constantCoeff (a i) = 0)
    (ha : ∀ i, (F i).subst (Sum.elim X a) = 0) : a = implicitFunction F (implicitJacobian F)⁻¹ :=
  eq_implicitFunction hF (hasSubst_of_constantCoeff_zero hF) (.of_isUnit_det hJ) a
    (hasSubst_of_constantCoeff_zero ha0) ha0 ha

/-- **Formal implicit function theorem** over a commutative ring, for finitely many equations.

If `F(0, 0) = 0` and its matrix of linear `Y` coefficients has invertible determinant, there
is a unique tuple `α(X)` with `α(0) = 0` and `F(X, α(X)) = 0`. -/
theorem existsUnique_implicitFunction_of_isUnit_det (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobian F).det) :
    ∃! a : τ → MvPowerSeries σ R,
      (∀ i, constantCoeff (a i) = 0) ∧
      (∀ i, (F i).subst (Sum.elim X a) = 0) :=
  ⟨_, ⟨constantCoeff_implicitFunction_of_isUnit_det F hF hJ,
      subst_implicitFunction_of_isUnit_det F hF hJ⟩,
    fun a h ↦ eq_implicitFunction_of_isUnit_det F hF hJ a h.1 h.2⟩

@[simp]
theorem constantCoeff_implicitFunctionLeft_of_isUnit_det (F : τ → MvPowerSeries (τ ⊕ σ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobianLeft F).det) (i : τ) :
    constantCoeff (implicitFunctionLeft F (implicitJacobianLeft F)⁻¹ i) = 0 :=
  constantCoeff_implicitFunctionLeft hF (hasSubst_of_constantCoeff_zero hF) (.of_isUnit_det hJ) i

/-- The left implicit function can be substituted. -/
theorem HasSubst.implicitFunctionLeft_of_isUnit_det (F : τ → MvPowerSeries (τ ⊕ σ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobianLeft F).det) :
    HasSubst (MvPowerSeries.implicitFunctionLeft F (implicitJacobianLeft F)⁻¹) :=
  .implicitFunctionLeft hF (hasSubst_of_constantCoeff_zero hF) (.of_isUnit_det hJ)

/-- The left implicit function solves `F(α(X), X) = 0`. -/
@[simp]
theorem subst_implicitFunctionLeft_of_isUnit_det (F : τ → MvPowerSeries (τ ⊕ σ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobianLeft F).det) (i : τ) :
    (F i).subst (Sum.elim (implicitFunctionLeft F (implicitJacobianLeft F)⁻¹) X) = 0 :=
  subst_implicitFunctionLeft hF (hasSubst_of_constantCoeff_zero hF) (.of_isUnit_det hJ) i

/-- Any zero-constant-term solution of `F(a(X), X) = 0` is the left implicit function. -/
theorem eq_implicitFunctionLeft_of_isUnit_det (F : τ → MvPowerSeries (τ ⊕ σ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobianLeft F).det)
    (a : τ → MvPowerSeries σ R) (ha0 : ∀ i, constantCoeff (a i) = 0)
    (ha : ∀ i, (F i).subst (Sum.elim a X) = 0) :
    a = implicitFunctionLeft F (implicitJacobianLeft F)⁻¹ :=
  eq_implicitFunctionLeft hF (hasSubst_of_constantCoeff_zero hF) (.of_isUnit_det hJ) a
    (hasSubst_of_constantCoeff_zero ha0) ha0 ha

/-- **Formal implicit function theorem**, solving for the first variable block.
If its linear coefficient matrix has invertible determinant, there is a unique
zero-constant-term solution of `F(α(X), X) = 0`. -/
theorem existsUnique_implicitFunctionLeft_of_isUnit_det (F : τ → MvPowerSeries (τ ⊕ σ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobianLeft F).det) :
    ∃! a : τ → MvPowerSeries σ R,
      (∀ i, constantCoeff (a i) = 0) ∧
      (∀ i, (F i).subst (Sum.elim a X) = 0) :=
  ⟨_, ⟨constantCoeff_implicitFunctionLeft_of_isUnit_det F hF hJ,
      subst_implicitFunctionLeft_of_isUnit_det F hF hJ⟩,
    fun a h ↦ eq_implicitFunctionLeft_of_isUnit_det F hF hJ a h.1 h.2⟩

end Finite

end MvPowerSeries
