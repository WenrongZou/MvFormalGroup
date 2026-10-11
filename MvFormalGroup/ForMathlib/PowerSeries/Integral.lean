/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import MvFormalGroup.ForMathlib.MvPowerSeries.Integral
public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Formal integration of power series

For a `ℚ`-algebra `R`, this file defines `PowerSeries.integral`, the formal integral of a power
series, sending `X ^ n` to `X ^ (n + 1) / (n + 1)`. It is a special case of
`MvPowerSeries.integral`.

## Main definitions

- `PowerSeries.integral`: the formal integral, as an `R`-linear map.

## Main results

- `PowerSeries.coeff_integral`: `coeff n (integral f) = n⁻¹ • coeff (n - 1) f`.
- `PowerSeries.derivative_integral`, `PowerSeries.integral_derivative`: the fundamental theorem
  of calculus.
- `PowerSeries.eq_integral_of_derivative_eq`: `integral f` is the unique antiderivative of `f`
  with zero constant coefficient.
-/

@[expose] public section

noncomputable section

namespace PowerSeries

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The formal integral of a power series, sending `X ^ n` to `X ^ (n + 1) / (n + 1)`.
Its constant coefficient is zero. -/
def integral : R⟦X⟧ →ₗ[R] R⟦X⟧ :=
  MvPowerSeries.integral ()

theorem coeff_integral (f : R⟦X⟧) (n : ℕ) :
    coeff n (integral f) = (n : ℚ)⁻¹ • coeff (n - 1) f := by
  simp [coeff, integral, MvPowerSeries.coeff_integral, Finsupp.single_tsub]

@[simp]
theorem coeff_succ_integral (f : R⟦X⟧) (n : ℕ) :
    coeff (n + 1) (integral f) = ((n : ℚ) + 1)⁻¹ • coeff n f := by
  rw [coeff_integral, Nat.add_sub_cancel, Nat.cast_succ]

@[simp]
theorem constantCoeff_integral (f : R⟦X⟧) : constantCoeff (integral f) = 0 :=
  MvPowerSeries.constantCoeff_integral f

/-- The fundamental theorem of calculus: `integral` is a right inverse of `d⁄dX`. -/
@[simp]
theorem derivative_integral (f : R⟦X⟧) : d⁄dX (integral f) = f :=
  MvPowerSeries.pderiv_integral f

/-- The fundamental theorem of calculus: integrating `d⁄dX f` recovers `f` up to its constant
coefficient. -/
theorem integral_derivative (f : R⟦X⟧) : integral (d⁄dX f) = f - C (constantCoeff f) := by
  ext n
  rcases n with _ | n
  · simp
  · rw [map_sub, coeff_succ_C, sub_zero]
    exact (MvPowerSeries.coeff_integral_pderiv f _).trans (by simp [coeff])

/-- `integral f` is the unique antiderivative of `f` with zero constant coefficient. -/
theorem eq_integral_of_derivative_eq {f g : R⟦X⟧} (hg : d⁄dX g = f)
    (h0 : constantCoeff g = 0) : g = integral f := by
  rw [← hg, integral_derivative, h0, map_zero, sub_zero]

theorem integral_X_pow (k : ℕ) : integral (X ^ k : R⟦X⟧) = ((k : ℚ) + 1)⁻¹ • X ^ (k + 1) :=
  MvPowerSeries.integral_X_pow k

@[simp]
theorem integral_one : integral (1 : R⟦X⟧) = X :=
  MvPowerSeries.integral_one

@[simp]
theorem integral_C (r : R) : integral (C r) = r • X :=
  MvPowerSeries.integral_C r

theorem map_integral {S : Type*} [CommRing S] [Algebra ℚ S] (φ : R →+* S) (f : R⟦X⟧) :
    map φ (integral f) = integral (map φ f) :=
  MvPowerSeries.map_integral φ f

end PowerSeries
