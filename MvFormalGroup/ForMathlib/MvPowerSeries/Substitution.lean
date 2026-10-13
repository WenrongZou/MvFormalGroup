/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Basic.Finite.Sum

/-!
# Substitutable families and total-degree estimates

The family operations (`HasSubst.comp_injective`, `HasSubst.uncurry`, `HasSubst.pair`, and
`HasSubst.sumElim`) apply to arbitrary variable sets. The total-degree estimates below use
`truncTotal` and are used in the finite-variable formal implicit function theorem.
-/

@[expose] public section

noncomputable section

open Finsupp Function

namespace MvPowerSeries

variable {R : Type*} [CommRing R] {ι σ τ υ : Type*}

/-- Reindexing a substitutable family along an injective map keeps it substitutable. -/
theorem HasSubst.comp_injective {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
    {f : ι → σ} (hf : Injective f) : HasSubst (a ∘ f) where
  const_coeff i := ha.const_coeff (f i)
  coeff_zero d := (ha.coeff_zero d).preimage hf.injOn

/-- Stacking finitely many substitutable families gives a substitutable family. -/
theorem HasSubst.uncurry [Finite ι] {a : ι → σ → MvPowerSeries τ R}
    (ha : ∀ k, HasSubst (a k)) : HasSubst (Function.uncurry a) where
  const_coeff p := (ha p.1).const_coeff p.2
  coeff_zero d := by
    refine (Set.finite_iUnion fun k ↦ ((ha k).coeff_zero d).image (Prod.mk k)).subset ?_
    rintro ⟨k, s⟩ h
    exact Set.mem_iUnion.mpr ⟨k, s, h, rfl⟩

/-- A pair of substitutable families is substitutable. -/
theorem HasSubst.pair {x y : σ → MvPowerSeries τ R} (hx : HasSubst x) (hy : HasSubst y) :
    HasSubst (Function.uncurry ![x, y]) :=
  HasSubst.uncurry fun b ↦ by fin_cases b <;> assumption

/-- One block of variables is substitutable. -/
theorem HasSubst.curry_X (b : ι) : HasSubst (Function.curry (X (R := R) (σ := ι × σ)) b) :=
  HasSubst.X.comp_injective (Prod.mk_right_injective b)

/-- Two substitutable families on disjoint index sets combine to a substitutable family. -/
theorem HasSubst.sumElim {a : σ → MvPowerSeries υ R} {b : τ → MvPowerSeries υ R}
    (ha : HasSubst a) (hb : HasSubst b) : HasSubst (Sum.elim a b) where
  const_coeff := by
    rintro (s | t)
    exacts [ha.const_coeff s, hb.const_coeff t]
  coeff_zero d := by
    refine (((ha.coeff_zero d).image Sum.inl).union ((hb.coeff_zero d).image Sum.inr)).subset ?_
    rintro (s | t) h <;> simpa

/-- Substitution into a pair of families commutes with a further admissible substitution. -/
theorem subst_pair_subst (f : MvPowerSeries (Fin 2 × σ) R)
    (x y : σ → MvPowerSeries τ R) {a : τ → MvPowerSeries υ R}
    (hxy : HasSubst (uncurry ![x, y])) (ha : HasSubst a) :
    (f.subst (uncurry ![x, y])).subst a =
      f.subst (uncurry ![fun i ↦ (x i).subst a, fun i ↦ (y i).subst a]) := by
  rw [subst_comp_subst_apply hxy ha]
  congr 1
  funext ⟨b, i⟩
  fin_cases b <;> rfl

variable [Finite τ]

/-- Equality of total truncations is equality of all coefficients below the cutoff. -/
theorem truncTotal_eq_iff {n : ℕ} {f g : MvPowerSeries τ R} :
    f.truncTotal n = g.truncTotal n ↔ ∀ d, d.degree < n → coeff d f = coeff d g := by
  constructor
  · intro h d hd
    simpa only [coeff_truncTotal _ hd] using congrArg (fun p : MvPolynomial τ R ↦ p.coeff d) h
  · intro h
    ext d
    by_cases hd : d.degree < n
    · simpa only [coeff_truncTotal _ hd] using h d hd
    · simp only [coeff_truncTotal_eq_zero _ (Nat.le_of_not_gt hd)]

private theorem truncTotal_eq_iff_order {n : ℕ} {f g : MvPowerSeries τ R} :
    f.truncTotal n = g.truncTotal n ↔ (n : ℕ∞) ≤ (f - g).order := by
  rw [truncTotal_eq_iff]
  constructor
  · intro h
    exact nat_le_order (fun d hd ↦ by simp [h d hd])
  · intro h d hd
    have hz := coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)
    simpa [sub_eq_zero] using hz

private theorem truncTotal_mul_congr {n : ℕ} {f g f' g' : MvPowerSeries τ R}
    (h : f.truncTotal n = g.truncTotal n) (h' : f'.truncTotal n = g'.truncTotal n) :
    (f * f').truncTotal n = (g * g').truncTotal n := by
  apply truncTotal_eq_iff.mpr
  intro d hd
  rw [← coeff_truncTotal_mul_truncTotal_eq_coeff_mul _ _ hd,
    ← coeff_truncTotal_mul_truncTotal_eq_coeff_mul _ _ hd, h, h']

private theorem truncTotal_mul_right_succ {n : ℕ} {f g : MvPowerSeries τ R}
    (h : f.truncTotal n = g.truncTotal n) (a : MvPowerSeries τ R)
    (ha : constantCoeff a = 0) : (f * a).truncTotal (n + 1) = (g * a).truncTotal (n + 1) := by
  apply truncTotal_eq_iff_order.mpr
  rw [← sub_mul, Nat.cast_add, Nat.cast_one]
  exact (add_le_add (truncTotal_eq_iff_order.mp h)
    (one_le_order_iff_constCoeff_eq_zero.mpr ha)).trans le_order_mul

private theorem truncTotal_prod_congr {n : ℕ} {a b : σ → MvPowerSeries τ R}
    (h : ∀ i, (a i).truncTotal n = (b i).truncTotal n) (s : Multiset σ) :
    (s.map a).prod.truncTotal n = (s.map b).prod.truncTotal n := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons i s ih => simpa using truncTotal_mul_congr (h i) ih

omit [Finite τ] in
private theorem constantCoeff_prod {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) {s : Multiset σ} (hs : s ≠ 0) :
    constantCoeff (s.map a).prod = 0 := by
  induction s using Multiset.induction_on with
  | empty => exact (hs rfl).elim
  | cons i t ih => simp [ha]

private theorem truncTotal_prod_succ {n : ℕ} {a b : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0)
    (h : ∀ i, (a i).truncTotal n = (b i).truncTotal n) (s : Multiset σ) (hs : 2 ≤ s.card) :
    (s.map a).prod.truncTotal (n + 1) = (s.map b).prod.truncTotal (n + 1) := by
  induction s using Multiset.induction_on with
  | empty => simp at hs
  | cons i t ih =>
    have ht : t ≠ 0 := by rintro rfl; simp at hs
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (truncTotal_mul_right_succ (h i) _ (constantCoeff_prod ha ht)).trans
      (by simpa [mul_comm] using
        truncTotal_mul_right_succ (truncTotal_prod_congr h t) (b i) (hb i))

omit [Finite τ] in
private theorem prod_toMultiset_map (d : σ →₀ ℕ) (a : σ → MvPowerSeries τ R) :
    (d.toMultiset.map a).prod = d.prod (fun i k ↦ a i ^ k) := by
  classical
  induction d using Finsupp.induction with
  | zero => simp [Finsupp.toMultiset_zero]
  | @single_add i k d hi hk ih =>
    simp [Finsupp.toMultiset_add, ih, Finsupp.prod_add_index, pow_add,
      Multiset.map_nsmul, Multiset.prod_nsmul]

/-- Substitution into a series with no constant or linear terms improves agreement
by one total degree. -/
theorem truncTotal_subst_succ [Finite σ] {n : ℕ} (f : MvPowerSeries σ R)
    (hf : ∀ d, d.degree < 2 → coeff d f = 0) {a b : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0)
    (h : ∀ i, (a i).truncTotal n = (b i).truncTotal n) :
    (f.subst a).truncTotal (n + 1) = (f.subst b).truncTotal (n + 1) := by
  apply truncTotal_eq_iff.mpr
  intro d hd
  rw [coeff_subst (hasSubst_of_constantCoeff_zero ha),
    coeff_subst (hasSubst_of_constantCoeff_zero hb)]
  apply finsum_congr
  intro e
  by_cases he : e.degree < 2
  · simp [hf e he]
  · congr 1
    rw [← prod_toMultiset_map, ← prod_toMultiset_map]
    apply truncTotal_eq_iff.mp (truncTotal_prod_succ ha hb h _ _) d hd
    simpa only [Finsupp.card_toMultiset, Finsupp.degree_apply, Finsupp.sum, id_eq]
      using (Nat.le_of_not_gt he)

/-- If the linear coefficients in the second block vanish, substitution with a
fixed first block improves agreement by one total degree. -/
theorem truncTotal_subst_sum_succ {ι : Type*} [Finite σ] [Finite ι] {n : ℕ}
    (f : MvPowerSeries (σ ⊕ ι) R)
    (hf : ∀ i, coeff (single (Sum.inr i) 1) f = 0)
    {x : σ → MvPowerSeries τ R} {a b : ι → MvPowerSeries τ R}
    (hx : ∀ i, constantCoeff (x i) = 0)
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0)
    (h : ∀ i, (a i).truncTotal n = (b i).truncTotal n) :
    (f.subst (Sum.elim x a)).truncTotal (n + 1) =
      (f.subst (Sum.elim x b)).truncTotal (n + 1) := by
  have hxa : ∀ i, constantCoeff (Sum.elim x a i) = 0 := by
    rintro (i | i) <;> simp [hx, ha]
  have hxb : ∀ i, constantCoeff (Sum.elim x b i) = 0 := by
    rintro (i | i) <;> simp [hx, hb]
  have hab : ∀ i, (Sum.elim x a i).truncTotal n = (Sum.elim x b i).truncTotal n := by
    rintro (i | i)
    · rfl
    · exact h i
  apply truncTotal_eq_iff.mpr
  intro d hd
  rw [coeff_subst (hasSubst_of_constantCoeff_zero hxa),
    coeff_subst (hasSubst_of_constantCoeff_zero hxb)]
  apply finsum_congr
  intro e
  by_cases he : e.degree < 2
  · rcases show e.degree = 0 ∨ e.degree = 1 by omega with hz | ho
    · have : e = 0 := e.degree_eq_zero_iff.mp hz
      simp [this]
    · obtain ⟨i, rfl⟩ := (Finsupp.sum_eq_one_iff e).mp ho
      rcases i with i | i
      · simp
      · simp [hf]
  · congr 1
    rw [← prod_toMultiset_map, ← prod_toMultiset_map]
    apply truncTotal_eq_iff.mp (truncTotal_prod_succ hxa hxb hab _ _) d hd
    simpa only [Finsupp.card_toMultiset, Finsupp.degree_apply, Finsupp.sum, id_eq]
      using (Nat.le_of_not_gt he)

end MvPowerSeries
