/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import MvFormalGroup.ForMathlib.FormalGroup.Hom
public import MvFormalGroup.ForMathlib.FormalGroup.InvariantDifferential
public import MvFormalGroup.ForMathlib.MvFormalGroup.Iso
public import MvFormalGroup.ForMathlib.MvPowerSeries.Integral
public import MvFormalGroup.ForMathlib.PowerSeries.Integral

/-!
# The formal logarithm of a one-dimensional formal group law

We follow Silverman, *The Arithmetic of Elliptic Curves*, §IV.5. Let `R` be a `ℚ`-algebra and let
`F` be a one-dimensional formal group law over `R`. Write the normalized invariant differential as
`ω(T) = (1 + c₁ T + c₂ T² + ⋯) dT`. The *formal logarithm* of `F` is
`log_F(T) = ∫ ω(T) = T + (c₁ / 2) T² + (c₂ / 3) T³ + ⋯`.
The *formal exponential* `exp_F(T)` is the unique power series with
`log_F ∘ exp_F = exp_F ∘ log_F = T`.

Silverman works over a torsion-free ring `R` and places `log_F` in `K⟦T⟧` with `K = R ⊗ ℚ`. Here
`R` itself is a `ℚ`-algebra, which amounts to working over `K`.

## Main definitions

- `FormalGroup.log F`: the formal logarithm `log_F = ∫ ω`.
- `FormalGroup.exp F`: the formal exponential, the compositional inverse of `log_F`.
- `FormalGroup.logHom F : Hom F (additive R)` and `FormalGroup.expHom F : Hom (additive R) F`.
- `FormalGroup.logIso F`: `log_F` is an isomorphism from `F` to the additive formal group.

## Main results

- `FormalGroup.coeff_succ_log`: the coefficients of `log_F` are `cₙ / (n + 1)`.
- `FormalGroup.derivative_log`: `d⁄dT log_F = ω`.
- `FormalGroup.log_subst_toPowerSeries`: `log_F(F(X, Y)) = log_F(X) + log_F(Y)`.
- `FormalGroup.log_subst_exp`, `FormalGroup.exp_subst_log`, `FormalGroup.eq_exp_of_log_subst_eq_X`,
  `FormalGroup.eq_exp_of_subst_log_eq_X`: `exp_F` is the unique compositional inverse of `log_F`.
- `FormalGroup.toPowerSeries_eq_exp_subst`: `F(X, Y) = exp_F(log_F(X) + log_F(Y))`.
- `FormalGroup.isComm`: every one-dimensional formal group law over a `ℚ`-algebra is commutative.
- `FormalGroup.Hom.eq_smul_log`: every homomorphism `f : F → Ĝₐ` equals `f'(0) • log_F`.

## Implementation notes

The additivity of `log_F` uses only the right invariance `ω(F(T, S)) F_X(T, S) = ω(T)`. The
series `H = log_F(F(X, Y)) - log_F(X) - log_F(Y)` satisfies `∂H/∂X = 0` and `H(0, Y) = 0`, and
over a `ℚ`-algebra this forces `H = 0`. Commutativity of `F` is not assumed; it follows from
`F(X, Y) = exp_F(log_F(X) + log_F(Y))`.
-/

@[expose] public section

noncomputable section

open MvPowerSeries
open scoped PowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R]

/-- A one-dimensional formal group law with `F(Y, X) = F(X, Y)` is commutative. -/
theorem isComm_of_subst_swap {F : FormalGroup R}
    (h : F.toPowerSeries.subst ![X 1, X 0] = F.toPowerSeries) : F.IsComm := by
  refine ⟨fun _ ↦ ?_⟩
  set b : Fin 2 → MvPowerSeries (Fin 2 × Unit) R := fun i ↦ X (i, ())
  have hb : HasSubst b := hasSubst_of_constantCoeff_zero fun _ ↦ constantCoeff_X _
  have hswap : HasSubst (![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) R) := HasSubst.X_X
  have hc := hswap.comp hb
  simp only [substAlgHom_apply] at hc
  calc MvFormalGroup.toPowerSeries F ()
      = F.toPowerSeries.subst b := by
        rw [subst_toPowerSeries_eq F hb]
        exact (congrFun subst_self _).symm
    _ = (F.toPowerSeries.subst ![X 1, X 0]).subst b := by rw [h]
    _ = (MvFormalGroup.toPowerSeries F ()).subst
          (fun p : Fin 2 × Unit ↦ (![X 1, X 0] p.1 : MvPowerSeries (Fin 2) R).subst b) := by
        rw [subst_comp_subst_apply hswap hb, subst_toPowerSeries_eq F hc]
    _ = _ := by
        congr 1
        funext p
        obtain ⟨i, ⟨⟩⟩ := p
        fin_cases i <;> exact subst_X hb _

/-- `(f(a))(c) = f(a(c))` for a one-variable power series `f`. -/
private theorem subst_subst {τ υ : Type*} {a : MvPowerSeries τ R} (ha : PowerSeries.HasSubst a)
    {c : τ → MvPowerSeries υ R} (hc : HasSubst c) (f : PowerSeries R) :
    (f.subst a).subst c = f.subst (a.subst c) :=
  subst_comp_subst_apply ha.const hc f

/-- `Ĝₐ(x, y) = x + y`. -/
private theorem additive_subst {τ : Type*} {x y : MvPowerSeries τ R}
    (hx : PowerSeries.HasSubst x) (hy : PowerSeries.HasSubst y) :
    (additive R).toPowerSeries.subst ![x, y] = x + y := by
  have h := FormalGroup.hasSubst_pair hx hy
  rw [additive_toPowerSeries, subst_add h, subst_X h, subst_X h]
  rfl

private theorem hasSubst_subst_X {f : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0)
    (i : Fin 2) : PowerSeries.HasSubst (f.subst (X i : MvPowerSeries (Fin 2) R)) :=
  .of_constantCoeff_zero (PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) f hf)

variable [Algebra ℚ R] (F : FormalGroup R)

/-! ### The formal logarithm -/

/-- The *formal logarithm* `log_F(T) = ∫ ω(T)`, where `ω` is the normalized invariant
differential of `F`. -/
def log : PowerSeries R :=
  PowerSeries.integral F.invariantDifferential

@[simp]
theorem constantCoeff_log : PowerSeries.constantCoeff F.log = 0 :=
  PowerSeries.constantCoeff_integral _

/-- If `ω = (1 + c₁ T + c₂ T² + ⋯) dT`, then `log_F(T) = T + (c₁ / 2) T² + (c₂ / 3) T³ + ⋯`. -/
theorem coeff_succ_log (n : ℕ) :
    PowerSeries.coeff (n + 1) F.log =
      ((n : ℚ) + 1)⁻¹ • PowerSeries.coeff n F.invariantDifferential :=
  PowerSeries.coeff_succ_integral _ _

@[simp]
theorem coeff_one_log : PowerSeries.coeff 1 F.log = 1 := by
  simpa using F.coeff_succ_log 0

/-- The derivative of the formal logarithm is the normalized invariant differential. -/
@[simp]
theorem derivative_log : d⁄dX F.log = F.invariantDifferential :=
  PowerSeries.derivative_integral _

theorem hasSubst_log : PowerSeries.HasSubst F.log :=
  .of_constantCoeff_zero' F.constantCoeff_log

variable {F} in
/-- `log_F` is the unique power series without constant term whose derivative is `ω`. -/
theorem eq_log_of_derivative_eq {f : PowerSeries R} (hf : d⁄dX f = F.invariantDifferential)
    (h0 : PowerSeries.constantCoeff f = 0) : f = F.log :=
  PowerSeries.eq_integral_of_derivative_eq hf h0

/-- **The formal logarithm is additive**: `log_F(F(X, Y)) = log_F(X) + log_F(Y)`.
Commutativity of `F` is not needed. -/
theorem log_subst_toPowerSeries :
    F.log.subst F.toPowerSeries =
      F.log.subst (X 0 : MvPowerSeries (Fin 2) R) +
        F.log.subst (X 1 : MvPowerSeries (Fin 2) R) := by
  set H := F.log.subst F.toPowerSeries - F.log.subst (X 0 : MvPowerSeries (Fin 2) R) -
    F.log.subst (X 1 : MvPowerSeries (Fin 2) R) with hH
  -- `∂H/∂X = ω(F(X, Y)) F_X(X, Y) - ω(X) = 0` by invariance of `ω`
  have hd : pderiv 0 H = 0 := by
    rw [hH, map_sub, map_sub, PowerSeries.pderiv_subst F.zero_constantCoeff,
      PowerSeries.pderiv_subst (constantCoeff_X 0), PowerSeries.pderiv_subst (constantCoeff_X 1),
      derivative_log, F.isInvariantDifferential_invariantDifferential, pderiv_X_self,
      pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0), mul_one, mul_zero, sub_self, sub_zero]
  -- `H(0, Y) = log_F(F(0, Y)) - log_F(0) - log_F(Y) = 0`
  have hc : HasSubst (![0, X 1] : Fin 2 → MvPowerSeries (Fin 2) R) :=
    FormalGroup.hasSubst_pair .zero (.X 1)
  have hH0 : H.subst (![0, X 1] : Fin 2 → MvPowerSeries (Fin 2) R) = 0 := by
    rw [hH, subst_sub hc, subst_sub hc,
      subst_subst (.of_constantCoeff_zero F.zero_constantCoeff) hc,
      subst_subst (PowerSeries.HasSubst.X (0 : Fin 2)) hc,
      subst_subst (PowerSeries.HasSubst.X (1 : Fin 2)) hc, subst_X hc, subst_X hc,
      F.zero_add (PowerSeries.HasSubst.X (1 : Fin 2))]
    simp
  -- hence the monomials of `H` without `X` vanish
  have h0 (n : Fin 2 →₀ ℕ) (hn : n 0 = 0) : coeff n H = 0 := by
    have h := congrArg (coeff n) hH0
    rw [show H.subst (![0, X 1] : Fin 2 → MvPowerSeries (Fin 2) R) = rescale ![0, 1] H by
        rw [rescale_eq_subst]
        congr 1
        funext i
        fin_cases i <;> simp,
      coeff_rescale, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two, hn, map_zero] at h
    simpa using h
  have h := eq_integral_of_pderiv_eq hd h0
  rwa [map_zero, hH, sub_sub, sub_eq_zero] at h

/-! ### The formal exponential -/

/-- The *formal exponential* `exp_F`, the compositional inverse of `log_F`. It exists and is
unique because `log_F(T) = T + O(T²)` (Silverman, Lemma IV.2.4). -/
def exp : PowerSeries R :=
  F.log.substInvOfIsUnit (by simp)

/-- `log_F(exp_F(T)) = T`. -/
@[simp]
theorem log_subst_exp : F.log.subst F.exp = PowerSeries.X :=
  PowerSeries.subst_substInvOfIsUnit_right _ F.constantCoeff_log _

/-- `exp_F(log_F(T)) = T`. -/
@[simp]
theorem exp_subst_log : F.exp.subst F.log = PowerSeries.X :=
  PowerSeries.subst_substInvOfIsUnit_left _ F.constantCoeff_log _

@[simp]
theorem constantCoeff_exp : PowerSeries.constantCoeff F.exp = 0 :=
  PowerSeries.constantCoeff_substInvOfIsUnit _ _

@[simp]
theorem coeff_one_exp : PowerSeries.coeff 1 F.exp = 1 := by
  simp [exp]

theorem hasSubst_exp : PowerSeries.HasSubst F.exp :=
  .of_constantCoeff_zero' F.constantCoeff_exp

variable {F} in
/-- A power series `g` without constant term with `log_F(g(T)) = T` is `exp_F`. -/
theorem eq_exp_of_log_subst_eq_X {g : PowerSeries R} (hg : PowerSeries.HasSubst g)
    (h : F.log.subst g = PowerSeries.X) : g = F.exp :=
  PowerSeries.eq_substInvOfIsUnit_of_subst_eq_X _ F.constantCoeff_log _ hg h

variable {F} in
/-- A power series `g` with `g(log_F(T)) = T` is `exp_F`. -/
theorem eq_exp_of_subst_log_eq_X {g : PowerSeries R} (h : g.subst F.log = PowerSeries.X) :
    g = F.exp := by
  rw [← PowerSeries.X_subst g, ← F.log_subst_exp,
    ← PowerSeries.subst_comp_subst_apply F.hasSubst_log F.hasSubst_exp, h,
    PowerSeries.subst_X F.hasSubst_exp]

/-- **The formal group law in terms of its logarithm**: `F(X, Y) = exp_F(log_F(X) + log_F(Y))`. -/
theorem toPowerSeries_eq_exp_subst :
    F.toPowerSeries = F.exp.subst
      (F.log.subst (X 0 : MvPowerSeries (Fin 2) R) +
        F.log.subst (X 1 : MvPowerSeries (Fin 2) R)) := by
  have hG : PowerSeries.HasSubst F.toPowerSeries := .of_constantCoeff_zero F.zero_constantCoeff
  rw [← log_subst_toPowerSeries, ← PowerSeries.subst_comp_subst_apply F.hasSubst_log hG,
    exp_subst_log, PowerSeries.subst_X hG]

private theorem hasSubst_log_add_log :
    PowerSeries.HasSubst
      (F.log.subst (X 0 : MvPowerSeries (Fin 2) R) + F.log.subst (X 1 : MvPowerSeries (Fin 2) R)) :=
  .of_constantCoeff_zero <| by
    rw [map_add, PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X 0) _ F.constantCoeff_log,
      PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X 1) _ F.constantCoeff_log,
      _root_.add_zero]

/-- `exp_F(log_F(x) + log_F(y))` for admissible `x` and `y`. -/
private theorem exp_log_add_log_subst {τ : Type*} {x y : MvPowerSeries τ R}
    (hx : PowerSeries.HasSubst x) (hy : PowerSeries.HasSubst y) :
    F.toPowerSeries.subst ![x, y] = F.exp.subst (F.log.subst x + F.log.subst y) := by
  have hc := FormalGroup.hasSubst_pair hx hy
  rw [F.toPowerSeries_eq_exp_subst, subst_subst F.hasSubst_log_add_log hc, subst_add hc,
    subst_subst (PowerSeries.HasSubst.X (0 : Fin 2)) hc,
    subst_subst (PowerSeries.HasSubst.X (1 : Fin 2)) hc, subst_X hc, subst_X hc]
  rfl

/-- Every one-dimensional formal group law over a `ℚ`-algebra is commutative. -/
instance isComm : F.IsComm :=
  isComm_of_subst_swap <| by
    rw [F.exp_log_add_log_subst (.X 1) (.X 0), add_comm, ← F.toPowerSeries_eq_exp_subst]

/-! ### The logarithm as an isomorphism with the additive formal group -/

/-- The formal logarithm as a homomorphism `F → Ĝₐ`. -/
def logHom : Hom F (additive R) :=
  Hom.mk' F.log F.constantCoeff_log <| by
    rw [additive_subst (hasSubst_subst_X F.constantCoeff_log 0)
      (hasSubst_subst_X F.constantCoeff_log 1)]
    exact F.log_subst_toPowerSeries

@[simp]
theorem toPowerSeries_logHom : F.logHom.toPowerSeries = F.log :=
  rfl

/-- The formal exponential as a homomorphism `Ĝₐ → F`. -/
def expHom : Hom (additive R) F :=
  Hom.mk' F.exp F.constantCoeff_exp <| by
    have he := hasSubst_subst_X F.constantCoeff_exp
    have hc := FormalGroup.hasSubst_pair (he 0) (he 1)
    have hlog (i : Fin 2) :
        F.log.subst (F.exp.subst (X i : MvPowerSeries (Fin 2) R)) = X i := by
      rw [← PowerSeries.subst_comp_subst_apply F.hasSubst_exp (.X i), log_subst_exp,
        PowerSeries.subst_X (.X i)]
    rw [additive_toPowerSeries, F.exp_log_add_log_subst (he 0) (he 1), hlog, hlog]

@[simp]
theorem toPowerSeries_expHom : F.expHom.toPowerSeries = F.exp :=
  rfl

/-- **Silverman, Proposition IV.5.2**: the formal logarithm is an isomorphism from `F` to the
additive formal group, with inverse the formal exponential. -/
def logIso : MvFormalGroup.Iso F (additive R) where
  toHom := F.logHom
  invHom := F.expHom
  hom_inv_id := Hom.ext F.log_subst_exp
  inv_hom_id := Hom.ext F.exp_subst_log

variable {F} in
/-- Every homomorphism `f : F → Ĝₐ` equals `f'(0) • log_F`. In particular, `log_F` is the unique
homomorphism `F → Ĝₐ` with `f'(0) = 1`. -/
theorem Hom.eq_smul_log (f : Hom F (additive R)) :
    f.toPowerSeries = PowerSeries.coeff 1 f.toPowerSeries • F.log := by
  set g := f.toPowerSeries
  have hg := hasSubst_subst_X f.constantCoeff_toPowerSeries
  -- differentiating `g(F(X, Y)) = g(X) + g(Y)` in `X` shows that `g'(T) dT` is invariant
  have h := congrArg (pderiv 0) f.map_add
  rw [additive_subst (hg 0) (hg 1), _root_.map_add, PowerSeries.pderiv_subst F.zero_constantCoeff,
    PowerSeries.pderiv_subst (constantCoeff_X 0), PowerSeries.pderiv_subst (constantCoeff_X 1),
    pderiv_X_self, pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0), mul_one, mul_zero,
    _root_.add_zero] at h
  have hinv : F.IsInvariantDifferential (d⁄dX g) := h
  have hc : PowerSeries.constantCoeff (d⁄dX g) = PowerSeries.coeff 1 g := by
    simpa using PowerSeries.coeff_derivative g 0
  calc g = PowerSeries.integral (d⁄dX g) :=
        PowerSeries.eq_integral_of_derivative_eq rfl f.constantCoeff_toPowerSeries
    _ = _ := by rw [hinv.eq_smul, hc, map_smul]; rfl

/-! ### The additive formal group -/

@[simp]
theorem log_additive : (additive R).log = PowerSeries.X := by
  simp [log, PowerSeries.integral_one]

@[simp]
theorem exp_additive : (additive R).exp = PowerSeries.X :=
  (eq_exp_of_subst_log_eq_X (by rw [log_additive, PowerSeries.X_subst])).symm

end FormalGroup
