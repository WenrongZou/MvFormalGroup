/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import MvFormalGroup.ForMathlib.MvPowerSeries.Substitution
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# The chain rule for multivariate power series

For `a : σ → MvPowerSeries τ R` with zero constant coefficients and `f : MvPowerSeries σ R`,
`MvPowerSeries.pderiv_subst` states the chain rule
`∂ᵢ (f (a)) = ∑ s, (∂ₛ f) (a) * ∂ᵢ (a s)`. `PowerSeries.pderiv_subst` is the special case of a
one-variable power series `f`: `∂ᵢ (f (a)) = f' (a) * ∂ᵢ a`.

The proof first treats polynomials, by induction, and then reduces to them: below a given total
degree, the coefficients of `f.subst a` only depend on a truncation of `f`.
-/

@[expose] public section

noncomputable section

open Finsupp

namespace MvPowerSeries

variable {R : Type*} [CommRing R] {σ τ : Type*}

/-- The chain rule for polynomials. -/
private theorem pderiv_subst_coe [Fintype σ] {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (p : MvPolynomial σ R) (i : τ) :
    pderiv i ((p : MvPowerSeries σ R).subst a) =
      ∑ s, (pderiv s (p : MvPowerSeries σ R)).subst a * pderiv i (a s) := by
  classical
  simp only [← substAlgHom_apply ha]
  induction p using MvPolynomial.induction_on with
  | C r =>
    simp only [MvPolynomial.coe_C, pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
    simp [substAlgHom_apply]
  | add p q hp hq =>
    simp only [MvPolynomial.coe_add, map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, Derivation.leibniz, smul_eq_mul,
      map_add, substAlgHom_X, hp, pderiv_X, Pi.single_apply, add_mul, Finset.sum_add_distrib]
    simp [Finset.mul_sum, mul_assoc]

/-- Coefficients of `f.subst a` below total degree `n` only depend on `f.truncTotal n`. -/
private theorem coeff_subst_truncTotal [Finite σ] [Finite τ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) {n : ℕ} {e : τ →₀ ℕ}
    (he : e.degree < n) :
    coeff e (f.subst a) = coeff e ((f.truncTotal n : MvPowerSeries σ R).subst a) := by
  rw [← coeff_truncTotal _ he, truncTotal_subst_eq_truncTotal_truncTotal_subst ha,
    coeff_truncTotal _ he]

/-- **Chain rule** for substitution of multivariate power series with zero constant
coefficients. -/
theorem pderiv_subst [Fintype σ] [Finite τ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) (i : τ) :
    pderiv i (f.subst a) = ∑ s, (pderiv s f).subst a * pderiv i (a s) := by
  classical
  ext d
  set p : MvPowerSeries σ R := ↑(f.truncTotal (d.degree + 2))
  have hp (e : σ →₀ ℕ) (he : e.degree < d.degree + 2) : coeff e p = coeff e f := by
    simp [p, coeff_truncTotal _ he]
  calc coeff d (pderiv i (f.subst a))
      = coeff d (pderiv i (p.subst a)) := by
        rw [coeff_pderiv, coeff_pderiv, coeff_subst_truncTotal ha f (n := d.degree + 2)
          (by simp [map_add])]
    _ = coeff d (∑ s, (pderiv s p).subst a * pderiv i (a s)) := by
        rw [pderiv_subst_coe (hasSubst_of_constantCoeff_zero ha)]
    _ = coeff d (∑ s, (pderiv s f).subst a * pderiv i (a s)) := by
        simp only [map_sum]
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        rw [coeff_mul, coeff_mul]
        refine Finset.sum_congr rfl fun x hx ↦ ?_
        have hx : x.1.degree < d.degree + 1 := by
          have := congrArg Finsupp.degree (Finset.mem_antidiagonal.mp hx)
          rw [map_add] at this
          omega
        rw [coeff_subst_truncTotal ha _ hx, coeff_subst_truncTotal ha (pderiv s f) hx]
        congr 4
        refine truncTotal_eq_iff.mpr fun e he ↦ ?_
        rw [coeff_pderiv, coeff_pderiv, hp _ (by simp [map_add]; omega)]

open scoped PowerSeries in
/-- **Chain rule** for substituting a multivariate power series without constant term into a
one-variable power series: `∂ᵢ (f (a)) = f' (a) * ∂ᵢ a`. -/
theorem _root_.PowerSeries.pderiv_subst [Finite τ] {a : MvPowerSeries τ R}
    (ha : constantCoeff a = 0) (f : PowerSeries R) (i : τ) :
    pderiv i (f.subst a) = (d⁄dX f).subst a * pderiv i a := by
  rw [PowerSeries.subst, MvPowerSeries.pderiv_subst (fun _ ↦ ha), Fintype.sum_unique]
  rfl

end MvPowerSeries
