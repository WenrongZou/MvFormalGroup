/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Order

/-!
# Order of differences of products

Estimates on the (weighted) order of `∏ i ∈ s, a i - ∏ i ∈ s, b i` in terms of the orders of
`a i - b i`, `a i` and `b i`, and agreement of coefficients below the order of a difference.
They are used to show that substitution improves agreement of families of power series.

## Main results

* `MvPowerSeries.coeff_eq_of_lt_order_sub`: `f` and `g` agree below the order of `f - g`.
* `MvPowerSeries.le_order_prod_sub_prod`: a lower bound on the order of a difference of
  products.
* `MvPowerSeries.add_nsmul_le_order_prod_sub_prod`: the sharper bound when all factors have
  order at least `k`.
-/

@[expose] public section

namespace MvPowerSeries

open ENat Finsupp

variable {σ : Type*}

section WeightedOrder

variable (w : σ → ℕ) {R : Type*} [Ring R] {f g : MvPowerSeries σ R}

/-- If `f - g` has weighted order larger than the weight of `d`, then `f` and `g` have the same
coefficient at `d`. -/
theorem coeff_eq_of_lt_weightedOrder_sub {d : σ →₀ ℕ}
    (h : weight w d < (f - g).weightedOrder w) : coeff d f = coeff d g := by
  rw [← sub_eq_zero, ← map_sub]
  exact coeff_eq_zero_of_lt_weightedOrder w h

/-- If `a i - b i` has weighted order at least `n` for all `i ∈ s`, then so does
`∏ i ∈ s, a i - ∏ i ∈ s, b i`. -/
theorem le_weightedOrder_prod_sub_prod {R ι : Type*} [CommRing R] {n : ℕ∞}
    {a b : ι → MvPowerSeries σ R} {s : Finset ι}
    (h : ∀ i ∈ s, n ≤ (a i - b i).weightedOrder w) :
    n ≤ (∏ i ∈ s, a i - ∏ i ∈ s, b i).weightedOrder w := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    simp only [Finset.mem_cons, forall_eq_or_imp] at h
    have : a i * ∏ j ∈ s, a j - b i * ∏ j ∈ s, b j =
        a i * (∏ j ∈ s, a j - ∏ j ∈ s, b j) + (a i - b i) * ∏ j ∈ s, b j := by
      rw [mul_sub, sub_mul, sub_add_sub_cancel]
    rw [Finset.prod_cons, Finset.prod_cons, this]
    exact (le_min ((ih h.2).trans (le_add_self.trans (le_weightedOrder_mul w)))
      (h.1.trans (le_self_add.trans (le_weightedOrder_mul w)))).trans (min_weightedOrder_le_add w)

/-- If `a i - b i` has weighted order at least `n`, and `a i`, `b i` have weighted order at
least `k`, for all `i ∈ s`, then `∏ i ∈ s, a i - ∏ i ∈ s, b i` has weighted order at least
`n + (#s - 1) • k`. -/
theorem add_nsmul_le_weightedOrder_prod_sub_prod {R ι : Type*} [CommRing R] {n k : ℕ∞}
    {a b : ι → MvPowerSeries σ R} {s : Finset ι}
    (ha : ∀ i ∈ s, k ≤ (a i).weightedOrder w) (hb : ∀ i ∈ s, k ≤ (b i).weightedOrder w)
    (h : ∀ i ∈ s, n ≤ (a i - b i).weightedOrder w) :
    n + (s.card - 1) • k ≤ (∏ i ∈ s, a i - ∏ i ∈ s, b i).weightedOrder w := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    simp only [Finset.mem_cons, forall_eq_or_imp] at ha hb h
    have : a i * ∏ j ∈ s, a j - b i * ∏ j ∈ s, b j =
        a i * (∏ j ∈ s, a j - ∏ j ∈ s, b j) + (a i - b i) * ∏ j ∈ s, b j := by
      rw [mul_sub, sub_mul, sub_add_sub_cancel]
    rw [Finset.prod_cons, Finset.prod_cons, this, Finset.card_cons, Nat.add_sub_cancel]
    refine (le_min ?_ ?_).trans (min_weightedOrder_le_add w)
    · rcases s.eq_empty_or_nonempty with rfl | hs
      · simp
      calc
        _ = k + (n + (s.card - 1) • k) := by
          rw [add_left_comm, ← succ_nsmul', Nat.sub_add_cancel hs.card_pos]
        _ ≤ _ := (add_le_add ha.1 (ih ha.2 hb.2 h.2)).trans (le_weightedOrder_mul w)
    · exact (add_le_add h.1 ((s.card_nsmul_le_sum _ k hb.2).trans
        (le_weightedOrder_prod w b s))).trans (le_weightedOrder_mul w)

end WeightedOrder

section Order

variable {R : Type*} [Ring R] {f g : MvPowerSeries σ R}

/-- If `f - g` has order larger than the degree of `d`, then `f` and `g` have the same
coefficient at `d`. -/
theorem coeff_eq_of_lt_order_sub {d : σ →₀ ℕ} (h : degree d < (f - g).order) :
    coeff d f = coeff d g := by
  rw [degree_eq_weight_one] at h
  exact coeff_eq_of_lt_weightedOrder_sub _ h

/-- If `a i - b i` has order at least `n` for all `i ∈ s`, then so does
`∏ i ∈ s, a i - ∏ i ∈ s, b i`. -/
theorem le_order_prod_sub_prod {R ι : Type*} [CommRing R] {n : ℕ∞}
    {a b : ι → MvPowerSeries σ R} {s : Finset ι} (h : ∀ i ∈ s, n ≤ (a i - b i).order) :
    n ≤ (∏ i ∈ s, a i - ∏ i ∈ s, b i).order :=
  le_weightedOrder_prod_sub_prod _ h

/-- If `a i - b i` has order at least `n`, and `a i`, `b i` have order at least `k`, for all
`i ∈ s`, then `∏ i ∈ s, a i - ∏ i ∈ s, b i` has order at least `n + (#s - 1) • k`. -/
theorem add_nsmul_le_order_prod_sub_prod {R ι : Type*} [CommRing R] {n k : ℕ∞}
    {a b : ι → MvPowerSeries σ R} {s : Finset ι}
    (ha : ∀ i ∈ s, k ≤ (a i).order) (hb : ∀ i ∈ s, k ≤ (b i).order)
    (h : ∀ i ∈ s, n ≤ (a i - b i).order) :
    n + (s.card - 1) • k ≤ (∏ i ∈ s, a i - ∏ i ∈ s, b i).order :=
  add_nsmul_le_weightedOrder_prod_sub_prod _ ha hb h

end Order

end MvPowerSeries
