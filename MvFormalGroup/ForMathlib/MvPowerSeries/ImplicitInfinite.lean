/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import MvFormalGroup.ForMathlib.Matrix.ColumnFinite
public import MvFormalGroup.ForMathlib.Matrix.Mul
public import MvFormalGroup.ForMathlib.MvPowerSeries.Substitution
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# The formal implicit function theorem for infinitely many equations

The classical formal implicit function theorem (see also `Implicit.lean`) solves
`F(X, Y) = 0` for finitely many equations and finitely many variables. Here the variables `X`
are indexed by `σ`, the equations `Fⱼ` by `ι`, and the unknowns `Y` by `τ`; all three may be
infinite, and `ι`, `τ` need not be the same type. The Jacobian `J` is then an `ι × τ` matrix.
Three extra conditions are needed.

* `HasSubst F`: every monomial occurs in only finitely many `Fⱼ`. This is the analogue of
  Hazewinkel's (9.6.3), and makes the Jacobian `J` column-finite.
* `Matrix.IsCofiniteInverse K J`: the Jacobian has a two-sided inverse `K`, a column-finite
  `τ × ι` matrix with `K J = 1` and `J K = 1`. Equivalently, `J` induces an isomorphism of free
  modules `R^(τ) ≅ R^(ι)`; so if `R` is nontrivial, `ι` and `τ` have the same cardinality. For
  infinite index sets a one-sided inverse is not enough: a shift has a one-sided inverse, and
  then existence or uniqueness fails. For a finite square system, this is `IsUnit J`
  (`Matrix.IsCofiniteInverse.of_isUnit`).
* The solution `α` itself satisfies `HasSubst α`, which is needed to substitute it.

The proof replaces `F` by `K F`, whose Jacobian is `1`, and takes the coefficientwise limit of
the iterates of `a ↦ a - (K F)(X, a)`. The matrix `K` acts on a family of power series
coefficientwise (`MvPowerSeries.finsumMulVec`, built from `Matrix.finsumMulVec`); each
coefficient is a finite sum. Agreement
below degree `n` is expressed as `n ≤ (f - g).order`, since `truncTotal` needs finitely many
variables.

## Main results

* `MvPowerSeries.succ_le_order_subst_sub`: substitution improves agreement by one degree.
* `MvPowerSeries.existsUnique_implicitFunctionCofinite`: the implicit function theorem.
* `MvPowerSeries.existsUnique_implicitFunctionLeftCofinite`: the version solving for the
  first variable block.
* `MvPowerSeries.Cofinite.existsUnique_implicitFunction`,
  `MvPowerSeries.Cofinite.existsUnique_implicitFunctionLeft`: the classical theorem for finitely
  many equations, deduced from the above, with the same statements as in `Implicit.lean`.

This file does not import `Implicit.lean`. The Jacobians and the finite-index statements are
therefore stated in the namespace `MvPowerSeries.Cofinite`, so that both files can be imported
together.
-/

@[expose] public section

noncomputable section

open Finsupp Function

namespace MvPowerSeries

variable {R : Type*} [CommRing R] {ι σ τ υ : Type*}

/-- Substitution preserves substitutability; `HasSubst.comp` stated with `subst`. -/
theorem HasSubst.subst {a : σ → MvPowerSeries τ R} {b : τ → MvPowerSeries υ R}
    (ha : HasSubst a) (hb : HasSubst b) : HasSubst (fun s ↦ (a s).subst b) := by
  convert ha.comp hb
  exact (substAlgHom_apply _ _).symm

theorem HasSubst.sub {a b : σ → MvPowerSeries τ R} (ha : HasSubst a) (hb : HasSubst b) :
    HasSubst (a - b) :=
  (sub_mem ha hb : a - b ∈ hasSubstIdeal)

theorem HasSubst.neg {a : σ → MvPowerSeries τ R} (ha : HasSubst a) : HasSubst (-a) :=
  (neg_mem ha : -a ∈ hasSubstIdeal)

/-! ### Agreement below a given degree

For an arbitrary set of variables, `truncTotal` is unavailable, so agreement of `f` and `g`
in degrees below `n` is expressed as `n ≤ (f - g).order`. -/

section Order

/-- A lower bound on the order of a difference gives agreement of low-degree coefficients. -/
theorem coeff_eq_of_le_order_sub {f g : MvPowerSeries σ R} {n : ℕ}
    (h : (n : ℕ∞) ≤ (f - g).order) {d : σ →₀ ℕ} (hd : d.degree < n) :
    coeff d f = coeff d g := by
  rw [← sub_eq_zero, ← map_sub]
  exact coeff_of_lt_order ((Nat.cast_lt.mpr hd).trans_le h)

private theorem prod_toMultiset_map (d : σ →₀ ℕ) (a : σ → MvPowerSeries τ R) :
    (d.toMultiset.map a).prod = d.prod (fun i k ↦ a i ^ k) := by
  classical
  induction d using Finsupp.induction with
  | zero => simp [Finsupp.toMultiset_zero]
  | @single_add i k d hi hk ih =>
    simp [Finsupp.toMultiset_add, ih, Finsupp.prod_add_index, pow_add,
      Multiset.map_nsmul, Multiset.prod_nsmul]

private theorem constantCoeff_multiset_prod {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) {s : Multiset σ} (hs : s ≠ 0) :
    constantCoeff (s.map a).prod = 0 := by
  induction s using Multiset.induction_on with
  | empty => exact (hs rfl).elim
  | cons i t ih => simp [ha]

variable {a b : σ → MvPowerSeries τ R} {n : ℕ}

private theorem le_order_multiset_prod_sub (h : ∀ s, (n : ℕ∞) ≤ (a s - b s).order)
    (m : Multiset σ) : (n : ℕ∞) ≤ ((m.map a).prod - (m.map b).prod).order := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons s m ih =>
    have : a s * (m.map a).prod - b s * (m.map b).prod =
        a s * ((m.map a).prod - (m.map b).prod) + (a s - b s) * (m.map b).prod := by ring
    simp only [Multiset.map_cons, Multiset.prod_cons, this]
    exact (le_min ((ih.trans le_add_self).trans le_order_mul)
      (((h s).trans le_self_add).trans le_order_mul)).trans min_order_le_add

private theorem succ_le_order_multiset_prod_sub (ha : ∀ s, constantCoeff (a s) = 0)
    (hb : ∀ s, constantCoeff (b s) = 0) (h : ∀ s, (n : ℕ∞) ≤ (a s - b s).order)
    (m : Multiset σ) (hm : 2 ≤ m.card) :
    ((n + 1 : ℕ) : ℕ∞) ≤ ((m.map a).prod - (m.map b).prod).order := by
  induction m using Multiset.induction_on with
  | empty => simp at hm
  | cons s m _ =>
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm
    have : a s * (m.map a).prod - b s * (m.map b).prod =
        a s * ((m.map a).prod - (m.map b).prod) + (a s - b s) * (m.map b).prod := by ring
    simp only [Multiset.map_cons, Multiset.prod_cons, this]
    refine (le_min ?_ ?_).trans min_order_le_add
    · calc ((n + 1 : ℕ) : ℕ∞) = 1 + n := by push_cast; exact add_comm _ _
        _ ≤ _ := add_le_add (one_le_order_iff_constCoeff_eq_zero.mpr (ha s))
          (le_order_multiset_prod_sub h m)
        _ ≤ _ := le_order_mul
    · calc ((n + 1 : ℕ) : ℕ∞) = n + 1 := by push_cast; rfl
        _ ≤ _ := add_le_add (h s)
          (one_le_order_iff_constCoeff_eq_zero.mpr (constantCoeff_multiset_prod hb hm0))
        _ ≤ _ := le_order_mul

/-- Substituting two families that agree below degree `n` gives series agreeing below
degree `n + 1`, provided `f` has no linear term in a variable where the families differ.
No finiteness of the variables is needed. -/
theorem succ_le_order_subst_sub {f : MvPowerSeries σ R} (ha : HasSubst a) (hb : HasSubst b)
    (ha0 : ∀ s, constantCoeff (a s) = 0) (hb0 : ∀ s, constantCoeff (b s) = 0)
    (h : ∀ s, (n : ℕ∞) ≤ (a s - b s).order)
    (hf : ∀ s, a s ≠ b s → coeff (single s 1) f = 0) :
    ((n + 1 : ℕ) : ℕ∞) ≤ (f.subst a - f.subst b).order := by
  refine nat_le_order fun e he ↦ ?_
  rw [map_sub, sub_eq_zero, coeff_subst ha, coeff_subst hb]
  refine finsum_congr fun d ↦ ?_
  obtain hd | hd | hd : d.degree = 0 ∨ d.degree = 1 ∨ 2 ≤ d.degree := by omega
  · simp [d.degree_eq_zero_iff.mp hd]
  · obtain ⟨s, rfl⟩ := (Finsupp.sum_eq_one_iff d).mp hd
    by_cases hs : a s = b s
    · simp [hs]
    · simp [hf s hs]
  · congr 1
    rw [← prod_toMultiset_map, ← prod_toMultiset_map]
    refine coeff_eq_of_le_order_sub (succ_le_order_multiset_prod_sub ha0 hb0 h _ ?_) he
    simpa only [Finsupp.card_toMultiset, Finsupp.degree_apply, Finsupp.sum, id_eq] using hd

end Order

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
  (hT0 : ∀ a, HasSubst a → (∀ i, constantCoeff (a i) = 0) →
    HasSubst (T a) ∧ ∀ i, constantCoeff (T a i) = 0)
  (hT : ∀ (n : ℕ) a b, HasSubst a → (∀ i, constantCoeff (a i) = 0) →
    HasSubst b → (∀ i, constantCoeff (b i) = 0) →
    (∀ i, (n : ℕ∞) ≤ (a i - b i).order) →
    ∀ i, ((n + 1 : ℕ) : ℕ∞) ≤ (T a i - T b i).order)

include hT0 in
private theorem iterate_admissible (n : ℕ) :
    HasSubst ((T^[n]) 0) ∧ ∀ i, constantCoeff ((T^[n]) 0 i) = 0 := by
  induction n with
  | zero => simp [hasSubst_def]
  | succ n ih =>
    rw [iterate_succ_apply']
    exact hT0 _ ih.1 ih.2

include hT0 hT in
private theorem le_order_iterate_sub (m k : ℕ) (i : ι) :
    (k : ℕ∞) ≤ ((T^[m + k]) 0 i - (T^[k]) 0 i).order := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, iterate_succ_apply', iterate_succ_apply']
    have h1 := iterate_admissible T hT0 (m + k)
    have h2 := iterate_admissible T hT0 k
    exact hT k _ _ h1.1 h1.2 h2.1 h2.2 ih i

include hT0 hT in
private theorem le_order_iterLimit_sub (n : ℕ) (i : ι) :
    (n : ℕ∞) ≤ (iterLimit T i - (T^[n]) 0 i).order := by
  refine nat_le_order fun d hd ↦ ?_
  rw [map_sub, sub_eq_zero]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hd
  exact (coeff_eq_of_le_order_sub (le_order_iterate_sub T hT0 hT m _ i) (lt_add_one _)).symm

include hT0 in
private theorem constantCoeff_iterLimit (i : ι) : constantCoeff (iterLimit T i) = 0 := by
  simpa [iterLimit, ← coeff_zero_eq_constantCoeff_apply, coeff_apply] using
    (iterate_admissible T hT0 1).2 i

include hT0 in
private theorem hasSubst_iterLimit : HasSubst (iterLimit T) where
  const_coeff i := by simp [constantCoeff_iterLimit T hT0 i]
  coeff_zero d := (iterate_admissible T hT0 (d.degree + 1)).1.coeff_zero d

include hT0 hT in
private theorem map_iterLimit : T (iterLimit T) = iterLimit T := by
  funext i
  ext d
  have h := hT _ _ _ (hasSubst_iterLimit T hT0) (constantCoeff_iterLimit T hT0)
    (iterate_admissible T hT0 _).1 (iterate_admissible T hT0 _).2
    (le_order_iterLimit_sub T hT0 hT (d.degree + 1)) i
  rw [← iterate_succ_apply' T] at h
  rw [coeff_eq_of_le_order_sub h (by omega),
    coeff_eq_of_le_order_sub (le_order_iterLimit_sub T hT0 hT (d.degree + 1 + 1) i) (by omega)]

include hT0 hT in
private theorem eq_iterLimit (b : ι → MvPowerSeries τ R) (hb : HasSubst b)
    (hb0 : ∀ i, constantCoeff (b i) = 0) (hbfix : T b = b) : b = iterLimit T := by
  have h (n : ℕ) : ∀ i, (n : ℕ∞) ≤ (b i - iterLimit T i).order := by
    induction n with
    | zero => simp
    | succ n ih =>
      intro i
      simpa only [hbfix, map_iterLimit T hT0 hT] using hT n b (iterLimit T) hb hb0
        (hasSubst_iterLimit T hT0) (constantCoeff_iterLimit T hT0) ih i
  funext i
  ext d
  exact coeff_eq_of_le_order_sub (h _ i) (lt_add_one _)

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
theorem hasSubst_finsumMulVec {K : Matrix τ ι R} (hK : ∀ j, {i | K i j ≠ 0}.Finite)
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
    (coeff_subst_finite ha (fun _ ↦ (1 : R) : MvPowerSeries σ R) e).subset fun d hd ↦ by
      simpa [Function.mem_support, h1, c] using hd
  let D := hD.toFinset
  let J := D.biUnion fun d ↦ (hv.coeff_zero d).toFinset
  have hcD : ∀ d ∉ D, c d = 0 := fun d hd ↦ by simpa [D] using hd
  have hvJ : ∀ d ∈ D, ∀ j ∉ J, coeff d (v j) = 0 := fun d hd j hj ↦ by
    by_contra h
    exact hj (Finset.mem_biUnion.mpr ⟨d, hd, (Set.Finite.mem_toFinset _).mpr h⟩)
  have hL : ∀ d ∈ D, coeff d (finsumMulVec K v i) = ∑ j ∈ J, K i j * coeff d (v j) :=
    fun d hd ↦ finsum_eq_sum_of_support_subset _ <|
      Function.support_subset_iff'.mpr fun j hj ↦ by simp [hvJ d hd j hj]
  have hR : ∀ j, coeff e ((v j).subst a) = ∑ d ∈ D, coeff d (v j) * c d := fun j ↦ by
    rw [coeff_subst ha]
    exact finsum_eq_sum_of_support_subset _ <|
      Function.support_subset_iff'.mpr fun d hd ↦ by simp [c, hcD d hd]
  rw [coeff_subst ha, coeff_finsumMulVec,
    finsum_eq_sum_of_support_subset _ (s := D) (Function.support_subset_iff'.mpr fun d hd ↦ by
      simp [c, hcD d hd]),
    finsum_eq_sum_of_support_subset _ (s := J) (Function.support_subset_iff'.mpr fun j hj ↦ by
      rw [hR, Finset.sum_eq_zero fun d hd ↦ by rw [hvJ d hd j hj, zero_mul], mul_zero])]
  simp only [smul_eq_mul]
  rw [Finset.sum_congr rfl fun d hd ↦ by rw [hL d hd]]
  simp only [hR, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- If `J K = 1`, then the column-finite matrix `K` is injective on families satisfying the
cofinite condition. -/
theorem eq_zero_of_finsumMulVec_eq_zero [DecidableEq ι] {K : Matrix τ ι R} {J : Matrix ι τ R}
    (hK : ∀ j, {i | K i j ≠ 0}.Finite)
    (hJK : ∀ i k, ∑ᶠ j, J i j * K j k = (1 : Matrix ι ι R) i k)
    {v : ι → MvPowerSeries σ R} (hv : ∀ d, {k | coeff d (v k) ≠ 0}.Finite)
    (h : finsumMulVec K v = 0) : v = 0 := by
  classical
  funext i
  ext d
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
    · rw [Finset.sum_eq_single i (fun k _ hk ↦ by simp [Matrix.one_apply_ne' hk])
        (fun h ↦ (h hiK).elim)]
      simp
    · rw [hKs i hiK, Finset.sum_eq_zero fun k hk ↦ ?_]
      rw [Matrix.one_apply_ne (by rintro rfl; exact hiK hk), zero_mul]
  rw [hi]
  simp only [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp [← Finset.mul_sum, hK0]

end CofiniteMatrix

/-! ### Jacobians

These are the matrices `implicitJacobian` and `implicitJacobianLeft` of `Implicit.lean`. This file
does not import that one, so they are defined again here, in the namespace
`MvPowerSeries.Cofinite`. -/

namespace Cofinite

/-- The matrix of coefficients of the linear terms in the `Y` variables. -/
def implicitJacobian (F : ι → MvPowerSeries (σ ⊕ τ) R) : Matrix ι τ R :=
  fun i j ↦ coeff (single (Sum.inr j) 1) (F i)

/-- The matrix of coefficients of the linear terms in the first variable block. -/
def implicitJacobianLeft (F : ι → MvPowerSeries (τ ⊕ σ) R) : Matrix ι τ R :=
  fun i j ↦ coeff (single (Sum.inl j) 1) (F i)

/-- Swapping the variable blocks turns the left Jacobian into the right Jacobian. -/
@[simp]
theorem implicitJacobian_rename_sumComm (F : ι → MvPowerSeries (τ ⊕ σ) R) :
    implicitJacobian (fun i ↦ rename (Equiv.sumComm τ σ) (F i)) = implicitJacobianLeft F := by
  ext i j
  simpa [implicitJacobian, implicitJacobianLeft] using
    coeff_embDomain_rename (Equiv.sumComm τ σ).toEmbedding (F i) (single (Sum.inl j) 1)

end Cofinite

/-! ### The implicit function theorem -/

section Implicit

variable [DecidableEq ι] [DecidableEq τ]

/-- The `n`th successive approximation, iterating `a ↦ a - (K F)(X, a)` from zero. -/
def implicitApproxCofinite (F : ι → MvPowerSeries (σ ⊕ τ) R) (K : Matrix τ ι R) (n : ℕ) :
    τ → MvPowerSeries σ R :=
  ((fun a i ↦ a i - (finsumMulVec K F i).subst (Sum.elim X a))^[n]) 0

/-- The implicit function, constructed coefficientwise: its coefficient of degree `d` is
taken from the `(d + 1)`st successive approximation. -/
def implicitFunctionCofinite (F : ι → MvPowerSeries (σ ⊕ τ) R) (K : Matrix τ ι R) :
    τ → MvPowerSeries σ R :=
  fun i d ↦ coeff d (implicitApproxCofinite F K (d.degree + 1) i)

variable {F : ι → MvPowerSeries (σ ⊕ τ) R} {K : Matrix τ ι R}

omit [DecidableEq ι] [DecidableEq τ] in
private theorem implicitStep_admissible (hF0 : ∀ i, constantCoeff (F i) = 0)
    (hF : HasSubst F) (hK : ∀ j, {i | K i j ≠ 0}.Finite) {a : τ → MvPowerSeries σ R}
    (ha : HasSubst a) (ha0 : ∀ i, constantCoeff (a i) = 0) :
    HasSubst (fun i ↦ a i - (finsumMulVec K F i).subst (Sum.elim X a)) ∧
      ∀ i, constantCoeff (a i - (finsumMulVec K F i).subst (Sum.elim X a)) = 0 := by
  have hp := HasSubst.X.sumElim ha
  refine ⟨ha.sub ((hasSubst_finsumMulVec hK hF hF0).subst hp), fun i ↦ ?_⟩
  rw [map_sub, ha0, constantCoeff_subst_eq_zero hp (by rintro (s | t) <;> simp [ha0])
    (constantCoeff_finsumMulVec K hF0 i), sub_zero]

omit [DecidableEq ι] in
private theorem implicitStep_contract
    (hKJ : ∀ i k, ∑ᶠ j, K i j * Cofinite.implicitJacobian F j k = (1 : Matrix τ τ R) i k)
    (n : ℕ) {a b : τ → MvPowerSeries σ R} (ha : HasSubst a) (ha0 : ∀ i, constantCoeff (a i) = 0)
    (hb : HasSubst b) (hb0 : ∀ i, constantCoeff (b i) = 0)
    (h : ∀ i, (n : ℕ∞) ≤ (a i - b i).order) (i : τ) :
    ((n + 1 : ℕ) : ℕ∞) ≤ ((a i - (finsumMulVec K F i).subst (Sum.elim X a)) -
      (b i - (finsumMulVec K F i).subst (Sum.elim X b))).order := by
  classical
  have hpa := HasSubst.X.sumElim ha
  have hpb := HasSubst.X.sumElim hb
  have key := succ_le_order_subst_sub (n := n) (f := X (Sum.inr i) - finsumMulVec K F i) hpa hpb
    (by rintro (s | k) <;> simp [ha0]) (by rintro (s | k) <;> simp [hb0])
    (by rintro (s | k) <;> simp [h]) (by
      rintro (s | k) hs
      · simp at hs
      · have hk : ∑ᶠ j, K i j * coeff (single (Sum.inr k) 1) (F j) = (1 : Matrix τ τ R) i k :=
          hKJ i k
        rw [map_sub, coeff_finsumMulVec, hk, coeff_index_single_X]
        by_cases hik : i = k
        · subst hik
          simp
        · simp [hik, Ne.symm hik])
  simpa [subst_sub hpa, subst_sub hpb, subst_X hpa, subst_X hpb] using key

variable (hF0 : ∀ i, constantCoeff (F i) = 0) (hF : HasSubst F)
  (hK : Matrix.IsCofiniteInverse K (Cofinite.implicitJacobian F))

include hF0 hF hK in
@[simp]
theorem constantCoeff_implicitFunctionCofinite (i : τ) :
    constantCoeff (implicitFunctionCofinite F K i) = 0 :=
  constantCoeff_iterLimit _ (fun _ ha ha0 ↦ implicitStep_admissible hF0 hF hK.col_finite ha ha0) i

include hF0 hF hK in
/-- The implicit function satisfies the cofinite condition, so it can be substituted. -/
theorem hasSubst_implicitFunctionCofinite : HasSubst (implicitFunctionCofinite F K) :=
  hasSubst_iterLimit _ (fun _ ha ha0 ↦ implicitStep_admissible hF0 hF hK.col_finite ha ha0)

include hF0 hF hK in
/-- The implicit function solves `F(X, α(X)) = 0`. -/
@[simp]
theorem subst_implicitFunctionCofinite (i : ι) :
    (F i).subst (Sum.elim X (implicitFunctionCofinite F K)) = 0 := by
  have hp := HasSubst.X.sumElim <| hasSubst_implicitFunctionCofinite hF0 hF hK
  have hG (j : τ) : (finsumMulVec K F j).subst (Sum.elim X (implicitFunctionCofinite F K)) = 0 := by
    have h : implicitFunctionCofinite F K j -
        (finsumMulVec K F j).subst (Sum.elim X (implicitFunctionCofinite F K)) =
        implicitFunctionCofinite F K j :=
      congrFun (map_iterLimit _ (fun _ ha ha0 ↦ implicitStep_admissible hF0 hF hK.col_finite ha ha0)
        (fun n _ _ ha ha0 hb hb0 h ↦ implicitStep_contract hK.mul_left n ha ha0 hb hb0 h)) j
    exact sub_eq_self.mp h
  have hv := hF.subst hp
  have h0 := eq_zero_of_finsumMulVec_eq_zero hK.col_finite hK.mul_right hv.coeff_zero
    (funext fun j ↦ by simp [← subst_finsumMulVec K hF hp j, hG j])
  exact congrFun h0 i

include hF0 hF hK in
/-- Any substitutable solution with zero constant terms is the implicit function. -/
theorem eq_implicitFunctionCofinite (a : τ → MvPowerSeries σ R) (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (h : ∀ i, (F i).subst (Sum.elim X a) = 0) :
    a = implicitFunctionCofinite F K := by
  have hp := HasSubst.X.sumElim ha
  refine eq_iterLimit _ (fun _ ha ha0 ↦ implicitStep_admissible hF0 hF hK.col_finite ha ha0)
    (fun n _ _ ha ha0 hb hb0 h ↦ implicitStep_contract hK.mul_left n ha ha0 hb hb0 h) a ha ha0
    (funext fun i ↦ ?_)
  have h0 : (fun j ↦ (F j).subst (Sum.elim X a)) = 0 := funext h
  simp only [subst_finsumMulVec K hF hp i, h0, finsumMulVec_zero, Pi.zero_apply, sub_zero]

include hF0 hF hK in
/-- **Formal implicit function theorem** for possibly infinitely many equations and variables.

Let the equations `Fⱼ` be indexed by `ι` and the unknowns `Y` by `τ`. If `F(0, 0) = 0`, every
monomial occurs in only finitely many `Fⱼ`, and the Jacobian has a two-sided inverse among
column-finite matrices, then there is a unique substitutable `α(X)`, indexed by `τ`, with
`α(0) = 0` and `F(X, α(X)) = 0`. -/
theorem existsUnique_implicitFunctionCofinite :
    ∃! a : τ → MvPowerSeries σ R,
      HasSubst a ∧ (∀ i, constantCoeff (a i) = 0) ∧ ∀ i, (F i).subst (Sum.elim X a) = 0 :=
  ⟨_, ⟨hasSubst_implicitFunctionCofinite hF0 hF hK,
      constantCoeff_implicitFunctionCofinite hF0 hF hK,
      subst_implicitFunctionCofinite hF0 hF hK⟩,
    fun a h ↦ eq_implicitFunctionCofinite hF0 hF hK a h.1 h.2.1 h.2.2⟩

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
def implicitFunctionLeftCofinite (F : ι → MvPowerSeries (τ ⊕ σ) R) (K : Matrix τ ι R) :
    τ → MvPowerSeries σ R :=
  implicitFunctionCofinite (fun i ↦ rename (Equiv.sumComm τ σ) (F i)) K

variable {F : ι → MvPowerSeries (τ ⊕ σ) R} {K : Matrix τ ι R}
  (hF0 : ∀ i, constantCoeff (F i) = 0) (hF : HasSubst F)
  (hK : Matrix.IsCofiniteInverse K (Cofinite.implicitJacobianLeft F))

include hK in
private theorem isCofiniteInverse_rename_sumComm :
    Matrix.IsCofiniteInverse K
      (Cofinite.implicitJacobian fun i ↦ rename (Equiv.sumComm τ σ) (F i)) := by
  rwa [Cofinite.implicitJacobian_rename_sumComm]

include hF0 hF hK in
@[simp]
theorem constantCoeff_implicitFunctionLeftCofinite (i : τ) :
    constantCoeff (implicitFunctionLeftCofinite F K i) = 0 :=
  constantCoeff_implicitFunctionCofinite (by simpa [constantCoeff_rename] using hF0)
    (hasSubst_rename_sumComm hF) (isCofiniteInverse_rename_sumComm hK) i

include hF0 hF hK in
theorem hasSubst_implicitFunctionLeftCofinite : HasSubst (implicitFunctionLeftCofinite F K) :=
  hasSubst_implicitFunctionCofinite (by simpa [constantCoeff_rename] using hF0)
    (hasSubst_rename_sumComm hF) (isCofiniteInverse_rename_sumComm hK)

include hF0 hF hK in
/-- The left implicit function solves `F(α(X), X) = 0`. -/
@[simp]
theorem subst_implicitFunctionLeftCofinite (i : ι) :
    (F i).subst (Sum.elim (implicitFunctionLeftCofinite F K) X) = 0 :=
  (subst_rename_sumComm_of_hasSubst _ (hasSubst_implicitFunctionLeftCofinite hF0 hF hK)).symm.trans
    (subst_implicitFunctionCofinite (by simpa [constantCoeff_rename] using hF0)
      (hasSubst_rename_sumComm hF) (isCofiniteInverse_rename_sumComm hK) i)

include hF0 hF hK in
/-- Any substitutable solution of `F(a(X), X) = 0` with zero constant terms is the left
implicit function. -/
theorem eq_implicitFunctionLeftCofinite (a : τ → MvPowerSeries σ R) (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (h : ∀ i, (F i).subst (Sum.elim a X) = 0) :
    a = implicitFunctionLeftCofinite F K :=
  eq_implicitFunctionCofinite (by simpa [constantCoeff_rename] using hF0)
    (hasSubst_rename_sumComm hF) (isCofiniteInverse_rename_sumComm hK) a ha ha0
    fun i ↦ (subst_rename_sumComm_of_hasSubst _ ha).trans (h i)

include hF0 hF hK in
/-- **Formal implicit function theorem**, solving for the first variable block, for possibly
infinitely many equations and variables. -/
theorem existsUnique_implicitFunctionLeftCofinite :
    ∃! a : τ → MvPowerSeries σ R,
      HasSubst a ∧ (∀ i, constantCoeff (a i) = 0) ∧ ∀ i, (F i).subst (Sum.elim a X) = 0 :=
  ⟨_, ⟨hasSubst_implicitFunctionLeftCofinite hF0 hF hK,
      constantCoeff_implicitFunctionLeftCofinite hF0 hF hK,
      subst_implicitFunctionLeftCofinite hF0 hF hK⟩,
    fun a h ↦ eq_implicitFunctionLeftCofinite hF0 hF hK a h.1 h.2.1 h.2.2⟩

end ImplicitLeft

/-! ### Finitely many equations

For finitely many equations, `HasSubst F` and `HasSubst α` hold automatically, and the inverse of
an invertible Jacobian is a cofinite inverse (`Matrix.IsCofiniteInverse.of_isUnit`). So the theorem
above specializes to the classical formal implicit function theorem. The statements below are
those of `Implicit.lean`, in the namespace `MvPowerSeries.Cofinite`; the variables `σ` may even
be infinite. -/

namespace Cofinite

section Finite

variable [Fintype τ] [DecidableEq τ]

/-- The formal solution `α(X)` of `F(X, α(X)) = 0` for finitely many equations with invertible
Jacobian, obtained from `implicitFunctionCofinite` with `K = J⁻¹`. -/
def implicitFunction (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (_hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobian F)) :
    τ → MvPowerSeries σ R :=
  implicitFunctionCofinite F (↑hJ.unit⁻¹ : Matrix τ τ R)

@[simp]
theorem constantCoeff_implicitFunction (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobian F)) (i : τ) :
    constantCoeff (implicitFunction F hF hJ i) = 0 :=
  constantCoeff_implicitFunctionCofinite hF (hasSubst_of_constantCoeff_zero hF) (.of_isUnit hJ) i

/-- Substitution of the implicit function is defined. -/
theorem hasSubst_implicitFunction (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobian F)) :
    HasSubst (Sum.elim X (implicitFunction F hF hJ)) :=
  HasSubst.X.sumElim
    (hasSubst_implicitFunctionCofinite hF (hasSubst_of_constantCoeff_zero hF) (.of_isUnit hJ))

/-- The implicit function solves the original system of equations. -/
@[simp]
theorem subst_implicitFunction (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobian F)) (i : τ) :
    (F i).subst (Sum.elim X (implicitFunction F hF hJ)) = 0 :=
  subst_implicitFunctionCofinite hF (hasSubst_of_constantCoeff_zero hF) (.of_isUnit hJ) i

/-- Any zero-constant-term solution is the implicit function. -/
theorem eq_implicitFunction (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobian F))
    (a : τ → MvPowerSeries σ R) (ha0 : ∀ i, constantCoeff (a i) = 0)
    (ha : ∀ i, (F i).subst (Sum.elim X a) = 0) : a = implicitFunction F hF hJ :=
  eq_implicitFunctionCofinite hF (hasSubst_of_constantCoeff_zero hF) (.of_isUnit hJ) a
    (hasSubst_of_constantCoeff_zero ha0) ha0 ha

/-- **Formal implicit function theorem** over a commutative ring, for finitely many equations.

If `F(0, 0) = 0` and its matrix of linear `Y` coefficients is invertible, there
is a unique tuple `α(X)` with `α(0) = 0` and `F(X, α(X)) = 0`. -/
theorem existsUnique_implicitFunction (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobian F)) :
    ∃! a : τ → MvPowerSeries σ R,
      (∀ i, constantCoeff (a i) = 0) ∧
      (∀ i, (F i).subst (Sum.elim X a) = 0) :=
  ⟨_, ⟨constantCoeff_implicitFunction F hF hJ, subst_implicitFunction F hF hJ⟩,
    fun a h ↦ eq_implicitFunction F hF hJ a h.1 h.2⟩

/-- A determinant formulation of the formal implicit function theorem. -/
theorem existsUnique_implicitFunction_of_isUnit_det (F : τ → MvPowerSeries (σ ⊕ τ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobian F).det) :
    ∃! a : τ → MvPowerSeries σ R,
      (∀ i, constantCoeff (a i) = 0) ∧
      (∀ i, (F i).subst (Sum.elim X a) = 0) :=
  existsUnique_implicitFunction F hF ((Matrix.isUnit_iff_isUnit_det _).mpr hJ)

/-- The solution of `F(α(X), X) = 0` for finitely many equations with invertible Jacobian in
the first variable block. -/
def implicitFunctionLeft (F : τ → MvPowerSeries (τ ⊕ σ) R)
    (_hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobianLeft F)) :
    τ → MvPowerSeries σ R :=
  implicitFunctionLeftCofinite F (↑hJ.unit⁻¹ : Matrix τ τ R)

@[simp]
theorem constantCoeff_implicitFunctionLeft (F : τ → MvPowerSeries (τ ⊕ σ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobianLeft F)) (i : τ) :
    constantCoeff (implicitFunctionLeft F hF hJ i) = 0 :=
  constantCoeff_implicitFunctionLeftCofinite hF (hasSubst_of_constantCoeff_zero hF)
    (.of_isUnit hJ) i

/-- Substitution of the left implicit function is defined. -/
theorem hasSubst_implicitFunctionLeft (F : τ → MvPowerSeries (τ ⊕ σ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobianLeft F)) :
    HasSubst (Sum.elim (implicitFunctionLeft F hF hJ) X) :=
  (hasSubst_implicitFunctionLeftCofinite hF (hasSubst_of_constantCoeff_zero hF)
    (.of_isUnit hJ)).sumElim HasSubst.X

/-- The left implicit function solves `F(α(X), X) = 0`. -/
@[simp]
theorem subst_implicitFunctionLeft (F : τ → MvPowerSeries (τ ⊕ σ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobianLeft F)) (i : τ) :
    (F i).subst (Sum.elim (implicitFunctionLeft F hF hJ) X) = 0 :=
  subst_implicitFunctionLeftCofinite hF (hasSubst_of_constantCoeff_zero hF) (.of_isUnit hJ) i

/-- Any zero-constant-term solution of `F(a(X), X) = 0` is the left implicit function. -/
theorem eq_implicitFunctionLeft (F : τ → MvPowerSeries (τ ⊕ σ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobianLeft F))
    (a : τ → MvPowerSeries σ R) (ha0 : ∀ i, constantCoeff (a i) = 0)
    (ha : ∀ i, (F i).subst (Sum.elim a X) = 0) : a = implicitFunctionLeft F hF hJ :=
  eq_implicitFunctionLeftCofinite hF (hasSubst_of_constantCoeff_zero hF) (.of_isUnit hJ) a
    (hasSubst_of_constantCoeff_zero ha0) ha0 ha

/-- **Formal implicit function theorem**, solving for the first variable block.
Invertibility of its linear coefficient matrix gives a unique zero-constant-term
solution of `F(α(X), X) = 0`. -/
theorem existsUnique_implicitFunctionLeft (F : τ → MvPowerSeries (τ ⊕ σ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobianLeft F)) :
    ∃! a : τ → MvPowerSeries σ R,
      (∀ i, constantCoeff (a i) = 0) ∧
      (∀ i, (F i).subst (Sum.elim a X) = 0) :=
  ⟨_, ⟨constantCoeff_implicitFunctionLeft F hF hJ, subst_implicitFunctionLeft F hF hJ⟩,
    fun a h ↦ eq_implicitFunctionLeft F hF hJ a h.1 h.2⟩

/-- A determinant formulation of the implicit function theorem for the first variable block. -/
theorem existsUnique_implicitFunctionLeft_of_isUnit_det (F : τ → MvPowerSeries (τ ⊕ σ) R)
    (hF : ∀ i, constantCoeff (F i) = 0) (hJ : IsUnit (implicitJacobianLeft F).det) :
    ∃! a : τ → MvPowerSeries σ R,
      (∀ i, constantCoeff (a i) = 0) ∧
      (∀ i, (F i).subst (Sum.elim a X) = 0) :=
  existsUnique_implicitFunctionLeft F hF ((Matrix.isUnit_iff_isUnit_det _).mpr hJ)

end Finite

end Cofinite

end MvPowerSeries
