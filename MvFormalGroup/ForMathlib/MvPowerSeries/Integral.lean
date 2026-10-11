/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Module.Rat

/-!
# Formal integration of multivariate power series

For a `ℚ`-algebra `R`, this file defines `MvPowerSeries.integral i`, the formal integral of a
multivariate power series with respect to the variable `X i`, sending the monomial `X ^ n` to
`X ^ (n + single i 1) / (n i + 1)`. Integration divides by the exponents, which is why `R` is
assumed to be a `ℚ`-algebra, as for `PowerSeries.exp` and `PowerSeries.log`.

See also `PowerSeries.integral` for the univariate setting.

## Main definitions

- `MvPowerSeries.integral i`: the formal integral with respect to `X i`, as an `R`-linear map.

## Main results

- `MvPowerSeries.coeff_integral`: `coeff n (integral i f) = (n i)⁻¹ • coeff (n - single i 1) f`.
- `MvPowerSeries.pderiv_integral`: `pderiv i (integral i f) = f`.
- `MvPowerSeries.coeff_integral_pderiv`: integrating `pderiv i f` recovers the monomials of `f`
  that involve `X i`.
- `MvPowerSeries.eq_integral_of_pderiv_eq`: `integral i f` is the unique antiderivative of `f`
  with respect to `X i` with no monomials independent of `X i`.
- `MvPowerSeries.pderiv_integral_of_ne`, `MvPowerSeries.integral_comm`: integrals commute with
  partial derivatives in other variables and with each other.
-/

@[expose] public section

noncomputable section

open Finsupp

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R] [Algebra ℚ R]

/-- The formal integral of a multivariate power series with respect to the variable `X i`.
It sends `X ^ n` to `X ^ (n + single i 1) / (n i + 1)`, so its coefficient at `n` is
`(n i)⁻¹ • coeff (n - single i 1) f`, which vanishes when `n i = 0`. -/
def integral (i : σ) : MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R where
  toFun f n := (n i : ℚ)⁻¹ • coeff (n - single i 1) f
  map_add' f g := by
    ext n
    change (n i : ℚ)⁻¹ • coeff _ (f + g) = (n i : ℚ)⁻¹ • coeff _ f + (n i : ℚ)⁻¹ • coeff _ g
    rw [map_add, smul_add]
  map_smul' r f := by
    ext n
    change (n i : ℚ)⁻¹ • coeff _ (r • f) = r • ((n i : ℚ)⁻¹ • coeff _ f)
    rw [map_smul, smul_comm]

variable {i : σ}

theorem coeff_integral (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    coeff n (integral i f) = (n i : ℚ)⁻¹ • coeff (n - single i 1) f :=
  rfl

theorem coeff_integral_of_eq_zero (f : MvPowerSeries σ R) {n : σ →₀ ℕ} (hn : n i = 0) :
    coeff n (integral i f) = 0 := by
  rw [coeff_integral, hn, Nat.cast_zero, inv_zero, zero_smul]

@[simp]
theorem coeff_add_single_integral (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    coeff (n + single i 1) (integral i f) = ((n i : ℚ) + 1)⁻¹ • coeff n f := by
  rw [coeff_integral, add_tsub_cancel_right, Finsupp.add_apply, single_eq_same, Nat.cast_add,
    Nat.cast_one]

@[simp]
theorem constantCoeff_integral (f : MvPowerSeries σ R) : constantCoeff (integral i f) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_integral_of_eq_zero f (zero_apply ..)]

/-- In a `ℚ`-algebra, multiplying by `k + 1` cancels the scalar `(k + 1)⁻¹`. -/
private theorem inv_smul_mul_cast_add_one {A : Type*} [CommRing A] [Algebra ℚ A] (k : ℕ) (a : A) :
    ((k : ℚ) + 1)⁻¹ • a * ((k : A) + 1) = a := by
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hR : ((k : A) + 1) = algebraMap ℚ A ((k : ℚ) + 1) := by simp
  rw [hR, ← Algebra.commutes, ← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hk, one_smul]

private theorem inv_smul_mul_cast_add_one' {A : Type*} [CommRing A] [Algebra ℚ A] (k : ℕ)
    (a : A) : ((k : ℚ) + 1)⁻¹ • (a * ((k : A) + 1)) = a := by
  rw [← smul_mul_assoc, inv_smul_mul_cast_add_one]

/-- The fundamental theorem of calculus: `integral i` is a right inverse of `pderiv i`. -/
@[simp]
theorem pderiv_integral (f : MvPowerSeries σ R) : pderiv i (integral i f) = f := by
  ext n
  rw [coeff_pderiv, coeff_add_single_integral, inv_smul_mul_cast_add_one]

/-- Integrating `pderiv i f` recovers the monomials of `f` which involve `X i`. -/
theorem coeff_integral_pderiv (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    coeff n (integral i (pderiv i f)) = if n i = 0 then 0 else coeff n f := by
  split_ifs with hn
  · exact coeff_integral_of_eq_zero _ hn
  have hle : single i 1 ≤ n := single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hn)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + single i 1 :=
    ⟨n - single i 1, (tsub_add_cancel_of_le hle).symm⟩
  rw [coeff_add_single_integral, coeff_pderiv, inv_smul_mul_cast_add_one']

/-- `integral i f` is the unique power series whose partial derivative with respect to `X i` is
`f` and which has no monomials independent of `X i`. -/
theorem eq_integral_of_pderiv_eq {f g : MvPowerSeries σ R} (hg : pderiv i g = f)
    (h0 : ∀ n : σ →₀ ℕ, n i = 0 → coeff n g = 0) : g = integral i f := by
  ext n
  rw [← hg, coeff_integral_pderiv]
  split_ifs with hn
  · exact h0 n hn
  · rfl

theorem integral_X_pow (k : ℕ) :
    integral i (X i ^ k : MvPowerSeries σ R) = ((k : ℚ) + 1)⁻¹ • X i ^ (k + 1) := by
  classical
  refine (eq_integral_of_pderiv_eq ?_ fun n hn ↦ ?_).symm
  · rw [map_rat_smul, pderiv_pow, pderiv_X_self, mul_one, Nat.add_sub_cancel, Nat.cast_succ,
      mul_comm, inv_smul_mul_cast_add_one']
  · rw [map_rat_smul, coeff_X_pow, ite_eq_right_iff.mpr, smul_zero]
    rintro rfl
    simp at hn

@[simp]
theorem integral_one : integral i (1 : MvPowerSeries σ R) = X i := by
  simpa using integral_X_pow (R := R) (i := i) 0

@[simp]
theorem integral_C (r : R) : integral i (C r : MvPowerSeries σ R) = r • X i := by
  rw [← mul_one (C r), ← smul_eq_C_mul, map_smul, integral_one]

/-- Factors independent of `X i` can be pulled out of `integral i`. -/
theorem integral_mul_of_pderiv_eq_zero {g : MvPowerSeries σ R} (hg : pderiv i g = 0)
    (f : MvPowerSeries σ R) : integral i (g * f) = g * integral i f := by
  classical
  refine (eq_integral_of_pderiv_eq ?_ fun n hn ↦ ?_).symm
  · rw [Derivation.leibniz, hg, smul_zero, add_zero, pderiv_integral, smul_eq_mul]
  · rw [coeff_mul]
    refine Finset.sum_eq_zero fun p hp ↦ ?_
    have h := congr($(Finset.mem_antidiagonal.mp hp) i)
    rw [Finsupp.add_apply, hn] at h
    rw [coeff_integral_of_eq_zero _ (by omega), mul_zero]

theorem integral_X_of_ne {j : σ} (h : j ≠ i) :
    integral i (X j : MvPowerSeries σ R) = X j * X i := by
  simpa using integral_mul_of_pderiv_eq_zero (pderiv_X_of_ne (R := R) h) 1

/-- Integration with respect to `X i` commutes with differentiation with respect to `X j`
for `j ≠ i`. -/
theorem pderiv_integral_of_ne {j : σ} (h : j ≠ i) (f : MvPowerSeries σ R) :
    pderiv j (integral i f) = integral i (pderiv j f) := by
  classical
  ext n
  have h₁ : (n + single j 1 : σ →₀ ℕ) i = n i := by simp [h]
  have h₂ : (n - single i 1 : σ →₀ ℕ) j = n j := by simp [h.symm]
  have h₃ : n + single j 1 - single i 1 = n - single i 1 + single j 1 := by
    ext k
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    grind
  rw [coeff_pderiv, coeff_integral, coeff_integral, coeff_pderiv, h₁, h₂, h₃, smul_mul_assoc]

theorem integral_comm (i j : σ) (f : MvPowerSeries σ R) :
    integral i (integral j f) = integral j (integral i f) := by
  obtain rfl | h := eq_or_ne i j
  · rfl
  classical
  ext n
  have h₁ : (n - single i 1 : σ →₀ ℕ) j = n j := by simp [h]
  have h₂ : (n - single j 1 : σ →₀ ℕ) i = n i := by simp [h.symm]
  rw [coeff_integral, coeff_integral, coeff_integral, coeff_integral, h₁, h₂, smul_smul,
    smul_smul, tsub_right_comm, mul_comm]

theorem map_integral {S : Type*} [CommRing S] [Algebra ℚ S] (φ : R →+* S)
    (f : MvPowerSeries σ R) : map φ (integral i f) = integral i (map φ f) := by
  ext n
  rw [coeff_map, coeff_integral, coeff_integral, coeff_map, map_rat_smul]

end MvPowerSeries
