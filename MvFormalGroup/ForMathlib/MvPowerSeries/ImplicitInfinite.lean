/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import MvFormalGroup.ForMathlib.MvPowerSeries.Implicit

/-!
# The formal implicit function theorem for infinitely many equations

`MvPowerSeries.existsUnique_implicitFunction` solves `F(X, Y) = 0` for finitely many
equations and finitely many variables. Here both index sets `σ` (the variables `X`) and `τ`
(the equations, and the unknowns `Y`) may be infinite. Three extra conditions are needed.

* `HasSubst F`: every monomial occurs in only finitely many `Fᵢ`. This is the analogue of
  Hazewinkel's (9.6.3), and makes the Jacobian `J` column-finite.
* `IsCofiniteInverse K J`: the Jacobian has a two-sided inverse `K` among column-finite
  matrices. For infinite `τ`, a one-sided inverse is not enough: a shift has a one-sided
  inverse, and then existence or uniqueness fails. For finite `τ`, this is `IsUnit J`
  (`IsCofiniteInverse.of_isUnit`).
* The solution `α` itself satisfies `HasSubst α`, which is needed to substitute it.

The proof replaces `F` by `K F`, whose Jacobian is `1`, and takes the coefficientwise limit of
the iterates of `a ↦ a - (K F)(X, a)`. The matrix `K` acts on a family of power series
coefficientwise (`MvPowerSeries.finsumMulVec`); each coefficient is a finite sum. Agreement
below degree `n` is expressed as `n ≤ (f - g).order`, since `truncTotal` needs finitely many
variables.

## Main results

* `MvPowerSeries.succ_le_order_subst_sub`: substitution improves agreement by one degree.
* `MvPowerSeries.existsUnique_implicitFunctionCofinite`: the implicit function theorem.
* `MvPowerSeries.existsUnique_implicitFunctionLeftCofinite`: the version solving for the
  first variable block.
* `MvPowerSeries.implicitFunctionCofinite_eq_implicitFunction`: for finitely many equations and
  variables, the solution agrees with `MvPowerSeries.implicitFunction`.
-/

@[expose] public section

noncomputable section

open Finsupp Function

namespace MvPowerSeries

variable {R : Type*} [CommRing R] {ι σ τ υ : Type*}

/-- Substitution preserves substitutability; `HasSubst.comp` stated with `subst`. -/
theorem HasSubst.subst {a : σ → MvPowerSeries τ R} {b : τ → MvPowerSeries υ R}
    (ha : HasSubst a) (hb : HasSubst b) : HasSubst (fun s ↦ (a s).subst b) := by
  simpa only [coe_substAlgHom] using ha.comp hb

/-- `HasSubst.X`, stated for the family `X` itself. -/
theorem HasSubst.X_self : HasSubst (X : σ → MvPowerSeries σ R) := HasSubst.X

/-- `HasSubst.zero`, stated for the family `0` itself. -/
theorem HasSubst.zero' : HasSubst (0 : σ → MvPowerSeries τ R) := HasSubst.zero

theorem HasSubst.sub {a b : σ → MvPowerSeries τ R} (ha : HasSubst a) (hb : HasSubst b) :
    HasSubst (a - b) := by
  have : a - b ∈ (hasSubstIdeal : Ideal (σ → MvPowerSeries τ R)) := sub_mem ha hb
  exact this

theorem HasSubst.neg {a : σ → MvPowerSeries τ R} (ha : HasSubst a) : HasSubst (-a) := by
  have : -a ∈ (hasSubstIdeal : Ideal (σ → MvPowerSeries τ R)) := neg_mem ha
  exact this

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
  | zero => exact ⟨HasSubst.zero, fun _ ↦ by simp⟩
  | succ n ih => rw [iterate_succ_apply']; exact hT0 _ ih.1 ih.2

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

/-- Two substitutable families on disjoint index sets combine to a substitutable family. -/
theorem HasSubst.sumElim {a : σ → MvPowerSeries υ R} {b : τ → MvPowerSeries υ R}
    (ha : HasSubst a) (hb : HasSubst b) : HasSubst (Sum.elim a b) where
  const_coeff := by
    rintro (s | t)
    exacts [ha.const_coeff s, hb.const_coeff t]
  coeff_zero d := by
    refine (((ha.coeff_zero d).image Sum.inl).union ((hb.coeff_zero d).image Sum.inr)).subset ?_
    rintro (s | t) h
    · exact Or.inl ⟨s, h, rfl⟩
    · exact Or.inr ⟨t, h, rfl⟩

/-! ### Column-finite matrices acting on families of power series -/

section CofiniteMatrix

/-- A matrix acting coefficientwise on a family of power series, `(K v)ᵢ = ∑ⱼ Kᵢⱼ vⱼ`.
When each monomial occurs in only finitely many `vⱼ`, every coefficient is a finite sum. -/
def finsumMulVec (K : Matrix τ τ R) (v : τ → MvPowerSeries σ R) : τ → MvPowerSeries σ R :=
  fun i d ↦ ∑ᶠ j, K i j * coeff d (v j)

theorem coeff_finsumMulVec (K : Matrix τ τ R) (v : τ → MvPowerSeries σ R) (i : τ)
    (d : σ →₀ ℕ) : coeff d (finsumMulVec K v i) = ∑ᶠ j, K i j * coeff d (v j) :=
  rfl

theorem constantCoeff_finsumMulVec (K : Matrix τ τ R) {v : τ → MvPowerSeries σ R}
    (hv : ∀ j, constantCoeff (v j) = 0) (i : τ) : constantCoeff (finsumMulVec K v i) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_finsumMulVec]
  simp [coeff_zero_eq_constantCoeff_apply, hv]

@[simp]
theorem finsumMulVec_zero (K : Matrix τ τ R) :
    finsumMulVec K (0 : τ → MvPowerSeries σ R) = 0 := by
  funext i
  ext d
  simp [coeff_finsumMulVec]

/-- A column-finite matrix preserves the cofinite condition. -/
theorem hasSubst_finsumMulVec {K : Matrix τ τ R} (hK : ∀ j, {i | K i j ≠ 0}.Finite)
    {v : τ → MvPowerSeries σ R} (hv : HasSubst v) (hv0 : ∀ j, constantCoeff (v j) = 0) :
    HasSubst (finsumMulVec K v) where
  const_coeff i := by simp [constantCoeff_finsumMulVec K hv0 i]
  coeff_zero d := by
    refine ((hv.coeff_zero d).biUnion fun j _ ↦ hK j).subset fun i hi ↦ ?_
    obtain ⟨j, hj⟩ : ∃ j, K i j * coeff d (v j) ≠ 0 := by
      by_contra! h
      exact hi (finsum_eq_zero_of_forall_eq_zero h)
    exact Set.mem_biUnion (right_ne_zero_of_mul hj) (left_ne_zero_of_mul hj)

/-- Substitution commutes with the coefficientwise action of a matrix. -/
theorem subst_finsumMulVec (K : Matrix τ τ R) {v : τ → MvPowerSeries σ R} (hv : HasSubst v)
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
theorem eq_zero_of_finsumMulVec_eq_zero [DecidableEq τ] {K J : Matrix τ τ R}
    (hK : ∀ j, {i | K i j ≠ 0}.Finite)
    (hJK : ∀ i k, ∑ᶠ j, J i j * K j k = (1 : Matrix τ τ R) i k)
    {v : τ → MvPowerSeries σ R} (hv : ∀ d, {k | coeff d (v k) ≠ 0}.Finite)
    (h : finsumMulVec K v = 0) : v = 0 := by
  funext i
  ext d
  let Ks := (hv d).toFinset
  let Js := Ks.biUnion fun k ↦ (hK k).toFinset
  have hKs : ∀ k ∉ Ks, coeff d (v k) = 0 := fun k hk ↦ by simpa [Ks] using hk
  have hJs : ∀ k ∈ Ks, ∀ j ∉ Js, K j k = 0 := fun k hk j hj ↦ by
    by_contra hne
    exact hj (Finset.mem_biUnion.mpr ⟨k, hk, (Set.Finite.mem_toFinset _).mpr hne⟩)
  have hK0 : ∀ j, ∑ k ∈ Ks, K j k * coeff d (v k) = 0 := fun j ↦ by
    have := congrArg (coeff d) (congrFun h j)
    rwa [coeff_finsumMulVec, finsum_eq_sum_of_support_subset _ (s := Ks)
      (Function.support_subset_iff'.mpr fun k hk ↦ by simp [hKs k hk])] at this
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

/-- `K` is a two-sided inverse of `J` among column-finite matrices. Products are taken with
`finsum`; each is a finite sum as soon as the right-hand factor is column-finite. -/
structure IsCofiniteInverse [DecidableEq τ] (K J : Matrix τ τ R) : Prop where
  /-- Every column of `K` has finitely many nonzero entries. -/
  col_finite j : {i | K i j ≠ 0}.Finite
  /-- `K J = 1`. -/
  mul_left i k : ∑ᶠ j, K i j * J j k = (1 : Matrix τ τ R) i k
  /-- `J K = 1`. -/
  mul_right i k : ∑ᶠ j, J i j * K j k = (1 : Matrix τ τ R) i k

theorem IsCofiniteInverse.one [DecidableEq τ] : IsCofiniteInverse (1 : Matrix τ τ R) 1 where
  col_finite j := (Set.finite_singleton j).subset fun i hi ↦ by
    by_contra h
    exact hi (Matrix.one_apply_ne h)
  mul_left i k := by
    rw [finsum_eq_single _ i fun j hj ↦ by simp [Matrix.one_apply_ne' hj]]
    simp
  mul_right i k := by
    rw [finsum_eq_single _ i fun j hj ↦ by simp [Matrix.one_apply_ne' hj]]
    simp

/-- For finitely many equations, the inverse of an invertible matrix is a cofinite inverse. -/
theorem IsCofiniteInverse.of_isUnit [Fintype τ] [DecidableEq τ] {J : Matrix τ τ R}
    (hJ : IsUnit J) : IsCofiniteInverse (↑hJ.unit⁻¹ : Matrix τ τ R) J where
  col_finite _ := Set.toFinite _
  mul_left i k := by
    have : (↑hJ.unit⁻¹ : Matrix τ τ R) * J = 1 := by
      simpa only [hJ.unit_spec] using hJ.unit.inv_mul
    rw [finsum_eq_sum_of_fintype, ← Matrix.mul_apply, this]
  mul_right i k := by
    have : J * (↑hJ.unit⁻¹ : Matrix τ τ R) = 1 := by
      simpa only [hJ.unit_spec] using hJ.unit.mul_inv
    rw [finsum_eq_sum_of_fintype, ← Matrix.mul_apply, this]

end CofiniteMatrix

/-! ### The implicit function theorem -/

section Implicit

variable [DecidableEq τ]

/-- The `n`th successive approximation, iterating `a ↦ a - (K F)(X, a)` from zero. -/
def implicitApproxCofinite (F : τ → MvPowerSeries (σ ⊕ τ) R) (K : Matrix τ τ R) (n : ℕ) :
    τ → MvPowerSeries σ R :=
  ((fun a i ↦ a i - (finsumMulVec K F i).subst (Sum.elim X a))^[n]) 0

/-- The implicit function, constructed coefficientwise: its coefficient of degree `d` is
taken from the `(d + 1)`st successive approximation. -/
def implicitFunctionCofinite (F : τ → MvPowerSeries (σ ⊕ τ) R) (K : Matrix τ τ R) :
    τ → MvPowerSeries σ R :=
  fun i d ↦ coeff d (implicitApproxCofinite F K (d.degree + 1) i)

variable {F : τ → MvPowerSeries (σ ⊕ τ) R} {K : Matrix τ τ R}

omit [DecidableEq τ] in
private theorem implicitStep_admissible (hF0 : ∀ i, constantCoeff (F i) = 0)
    (hF : HasSubst F) (hK : ∀ j, {i | K i j ≠ 0}.Finite) {a : τ → MvPowerSeries σ R}
    (ha : HasSubst a) (ha0 : ∀ i, constantCoeff (a i) = 0) :
    HasSubst (fun i ↦ a i - (finsumMulVec K F i).subst (Sum.elim X a)) ∧
      ∀ i, constantCoeff (a i - (finsumMulVec K F i).subst (Sum.elim X a)) = 0 := by
  have hp := HasSubst.X_self.sumElim ha
  refine ⟨ha.sub ((hasSubst_finsumMulVec hK hF hF0).subst hp), fun i ↦ ?_⟩
  rw [map_sub, ha0, constantCoeff_subst_eq_zero hp (by rintro (s | t) <;> simp [ha0])
    (constantCoeff_finsumMulVec K hF0 i), sub_zero]

private theorem implicitStep_contract
    (hKJ : ∀ i k, ∑ᶠ j, K i j * implicitJacobian F j k = (1 : Matrix τ τ R) i k)
    (n : ℕ) {a b : τ → MvPowerSeries σ R} (ha : HasSubst a) (ha0 : ∀ i, constantCoeff (a i) = 0)
    (hb : HasSubst b) (hb0 : ∀ i, constantCoeff (b i) = 0)
    (h : ∀ i, (n : ℕ∞) ≤ (a i - b i).order) (i : τ) :
    ((n + 1 : ℕ) : ℕ∞) ≤ ((a i - (finsumMulVec K F i).subst (Sum.elim X a)) -
      (b i - (finsumMulVec K F i).subst (Sum.elim X b))).order := by
  classical
  have hpa := HasSubst.X_self.sumElim ha
  have hpb := HasSubst.X_self.sumElim hb
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
  (hK : IsCofiniteInverse K (implicitJacobian F))

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
theorem subst_implicitFunctionCofinite (i : τ) :
    (F i).subst (Sum.elim X (implicitFunctionCofinite F K)) = 0 := by
  have hα := hasSubst_implicitFunctionCofinite hF0 hF hK
  have hp := HasSubst.X_self.sumElim hα
  have hG (j : τ) : (finsumMulVec K F j).subst (Sum.elim X (implicitFunctionCofinite F K)) = 0 := by
    have h : implicitFunctionCofinite F K j -
        (finsumMulVec K F j).subst (Sum.elim X (implicitFunctionCofinite F K)) =
        implicitFunctionCofinite F K j :=
      congrFun (map_iterLimit _ (fun _ ha ha0 ↦ implicitStep_admissible hF0 hF hK.col_finite ha ha0)
        (fun n _ _ ha ha0 hb hb0 h ↦ implicitStep_contract hK.mul_left n ha ha0 hb hb0 h)) j
    exact sub_eq_self.mp h
  have hv := hF.subst hp
  have h0 := eq_zero_of_finsumMulVec_eq_zero hK.col_finite hK.mul_right hv.coeff_zero
    (funext fun j ↦ by rw [← subst_finsumMulVec K hF hp j, hG j]; rfl)
  exact congrFun h0 i

include hF0 hF hK in
/-- Any substitutable solution with zero constant terms is the implicit function. -/
theorem eq_implicitFunctionCofinite (a : τ → MvPowerSeries σ R) (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (h : ∀ i, (F i).subst (Sum.elim X a) = 0) :
    a = implicitFunctionCofinite F K := by
  have hp := HasSubst.X_self.sumElim ha
  refine eq_iterLimit _ (fun _ ha ha0 ↦ implicitStep_admissible hF0 hF hK.col_finite ha ha0)
    (fun n _ _ ha ha0 hb hb0 h ↦ implicitStep_contract hK.mul_left n ha ha0 hb hb0 h) a ha ha0
    (funext fun i ↦ ?_)
  have h0 : (fun j ↦ (F j).subst (Sum.elim X a)) = 0 := funext h
  simp only [subst_finsumMulVec K hF hp i, h0, finsumMulVec_zero, Pi.zero_apply, sub_zero]

include hF0 hF hK in
/-- **Formal implicit function theorem** for possibly infinitely many equations and variables.

If `F(0, 0) = 0`, every monomial occurs in only finitely many `Fᵢ`, and the Jacobian has a
two-sided inverse among column-finite matrices, then there is a unique substitutable `α(X)`
with `α(0) = 0` and `F(X, α(X)) = 0`. -/
theorem existsUnique_implicitFunctionCofinite :
    ∃! a : τ → MvPowerSeries σ R,
      HasSubst a ∧ (∀ i, constantCoeff (a i) = 0) ∧ ∀ i, (F i).subst (Sum.elim X a) = 0 :=
  ⟨_, ⟨hasSubst_implicitFunctionCofinite hF0 hF hK,
      constantCoeff_implicitFunctionCofinite hF0 hF hK,
      subst_implicitFunctionCofinite hF0 hF hK⟩,
    fun a h ↦ eq_implicitFunctionCofinite hF0 hF hK a h.1 h.2.1 h.2.2⟩

omit [DecidableEq τ] in
/-- For finitely many equations and variables, the solution agrees with `implicitFunction`. -/
theorem implicitFunctionCofinite_eq_implicitFunction [Finite σ] [Fintype τ] [DecidableEq τ]
    (hJ : IsUnit (implicitJacobian F)) :
    implicitFunctionCofinite F (↑hJ.unit⁻¹ : Matrix τ τ R) = implicitFunction F hF0 hJ := by
  have hF := hasSubst_of_constantCoeff_zero hF0
  have hK := IsCofiniteInverse.of_isUnit hJ
  exact eq_implicitFunction F hF0 hJ _ (constantCoeff_implicitFunctionCofinite hF0 hF hK)
    (subst_implicitFunctionCofinite hF0 hF hK)

end Implicit

/-! ### Solving for the first variable block -/

section ImplicitLeft

private theorem hasSubst_rename_sumComm {F : τ → MvPowerSeries (τ ⊕ σ) R} (hF : HasSubst F) :
    HasSubst fun i ↦ rename (Equiv.sumComm τ σ) (F i) := by
  simpa only [rename_eq_subst] using hF.subst (HasSubst.X_comp (Equiv.sumComm τ σ))

private theorem subst_rename_sumComm_of_hasSubst (f : MvPowerSeries (τ ⊕ σ) R)
    {a : τ → MvPowerSeries σ R} (ha : HasSubst a) :
    (rename (Equiv.sumComm τ σ) f).subst (Sum.elim X a) = f.subst (Sum.elim a X) := by
  have hs := HasSubst.X_self.sumElim ha
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) hs]
  congr 1
  ext (j | j) : 1 <;> simp [subst_X hs]

variable [DecidableEq τ]

/-- The solution of `F(α(X), X) = 0`, obtained by exchanging the two variable blocks. -/
def implicitFunctionLeftCofinite (F : τ → MvPowerSeries (τ ⊕ σ) R) (K : Matrix τ τ R) :
    τ → MvPowerSeries σ R :=
  implicitFunctionCofinite (fun i ↦ rename (Equiv.sumComm τ σ) (F i)) K

variable {F : τ → MvPowerSeries (τ ⊕ σ) R} {K : Matrix τ τ R}
  (hF0 : ∀ i, constantCoeff (F i) = 0) (hF : HasSubst F)
  (hK : IsCofiniteInverse K (implicitJacobianLeft F))

include hK in
private theorem isCofiniteInverse_rename_sumComm :
    IsCofiniteInverse K (implicitJacobian fun i ↦ rename (Equiv.sumComm τ σ) (F i)) := by
  rwa [implicitJacobian_rename_sumComm]

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
theorem subst_implicitFunctionLeftCofinite (i : τ) :
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

end MvPowerSeries
