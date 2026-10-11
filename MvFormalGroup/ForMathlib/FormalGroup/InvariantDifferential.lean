/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import MvFormalGroup.ForMathlib.FormalGroup.Basic
public import MvFormalGroup.ForMathlib.MvPowerSeries.Derivative
public import MvFormalGroup.ForMathlib.PowerSeries.Differential
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Invariant differentials of one-dimensional formal group laws

We follow Silverman, *The Arithmetic of Elliptic Curves*, §IV.4. Over a ring `R`, a differential
form is an expression `P(T) dT` with `P ∈ R⟦T⟧`, and we identify it with the power series `P`.
For a formal group law `F(X, Y)`, the form `ω(T) = P(T) dT` is a *right-invariant differential*
if it is preserved by the right translation `T ↦ F(T, S)`, with `S` held fixed, that is, if
`P(F(T, S)) F_X(T, S) = P(T)`,
where `F_X` is the partial derivative of `F` with respect to its first variable. An invariant
differential is *normalized* if `P(0) = 1`.

Throughout this file, "invariant" means right-invariant; no commutativity of `F` is assumed.
The equation compares the `dT` coefficients of the pullbacks along `F(T, S)` and `T`.
It is a relative differential identity with `dS = 0`, not an equality of the full two-variable
forms: the full pullback `P(F) dF` also has the term `P(F) F_Y dS`.
`PowerSeries.pullbackDifferentialCoeff` provides the corresponding coefficient operation,
while `PowerSeries.pullbackDifferential` handles one-variable coordinate changes.

Differentiating associativity `F(F(U, T), S) = F(U, F(T, S))` with respect to `U` and then
setting `U = 0` gives `F_X(T, S) F_X(0, T) = F_X(0, F(T, S))`. Hence `ω(T) = F_X(0, T)⁻¹ dT` is
invariant. Setting `T = 0` in the invariance equation shows that every invariant differential `P`
equals `P(0) ω`.

## Main definitions

- `FormalGroup.IsInvariantDifferential F P`: `P(T) dT` is an invariant differential on `F`.
- `FormalGroup.invariantDifferentials F`: the `R`-submodule of invariant differentials on `F`.
- `FormalGroup.invariantDifferential F`: the normalized invariant differential
  `F_X(0, T)⁻¹ dT`.

## Main results

- `FormalGroup.isInvariantDifferential_invariantDifferential` and
  `FormalGroup.constantCoeff_invariantDifferential`: `F.invariantDifferential` is a normalized
  invariant differential.
- `FormalGroup.IsInvariantDifferential.eq_smul`: every invariant differential `P` equals
  `P(0) • F.invariantDifferential`.
- `FormalGroup.invariantDifferentials_eq_span`: the invariant differentials are exactly the
  `R`-multiples of `F.invariantDifferential`.
- `FormalGroup.invariantDifferentialsEquiv`: the `R`-linear equivalence from invariant
  differentials to `R`, given by `P ↦ P(0)`, with inverse `a ↦ a • F.invariantDifferential`.
- `FormalGroup.existsUnique_invariantDifferential`: there is a unique normalized invariant
  differential (Silverman, Proposition IV.4.2).
- `FormalGroup.invariantDifferential_additive`: the additive formal group has `ω = dT`.

## Implementation notes

The proof of invariance differentiates associativity, using the multivariate chain rule
`MvPowerSeries.pderiv_subst`.
-/

@[expose] public section

noncomputable section

open MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R]

/-- `P(T) dT` is a *right-invariant differential* on `F` if
`P(F(T, S)) F_X(T, S) = P(T)`. Here `T ↦ F(T, S)` is right translation, and `S` is
held fixed when differentiating. No commutativity of the formal group is assumed. -/
def IsInvariantDifferential (F : FormalGroup R) (P : PowerSeries R) : Prop :=
  P.subst F.toPowerSeries * pderiv 0 F.toPowerSeries = P.subst (X 0)

/-- Right invariance is equality of the `dT` components of the pullbacks along
`F(T, S)` and the first projection. It does not assert equality of the `dS` components. -/
theorem isInvariantDifferential_iff_pullbackDifferentialCoeff (F : FormalGroup R)
    (P : PowerSeries R) :
    F.IsInvariantDifferential P ↔
      PowerSeries.pullbackDifferentialCoeff F.toPowerSeries 0 P =
        PowerSeries.pullbackDifferentialCoeff (X 0 : MvPowerSeries (Fin 2) R) 0 P := by
  rw [PowerSeries.pullbackDifferentialCoeff_X_self]
  rfl

private theorem hasSubst_toPowerSeries (F : FormalGroup R) :
    PowerSeries.HasSubst F.toPowerSeries :=
  .of_constantCoeff_zero F.zero_constantCoeff

private theorem subst_zero' {σ τ : Type*} {b : σ → MvPowerSeries τ R} (hb : HasSubst b) :
    (0 : MvPowerSeries σ R).subst b = 0 := by
  rw [← substAlgHom_apply hb, map_zero]

/-- The invariant differentials on `F` form an `R`-submodule of `R⟦X⟧`. -/
def invariantDifferentials (F : FormalGroup R) : Submodule R (PowerSeries R) where
  carrier := {P | F.IsInvariantDifferential P}
  add_mem' {P Q} (hP : F.IsInvariantDifferential P) (hQ : F.IsInvariantDifferential Q) := by
    change F.IsInvariantDifferential (P + Q)
    rw [IsInvariantDifferential, PowerSeries.subst_add F.hasSubst_toPowerSeries,
      PowerSeries.subst_add (.X 0), add_mul, hP, hQ]
  zero_mem' := by
    change F.IsInvariantDifferential 0
    rw [IsInvariantDifferential, PowerSeries.subst, PowerSeries.subst,
      subst_zero' F.hasSubst_toPowerSeries.const, subst_zero' (PowerSeries.HasSubst.X 0).const,
      zero_mul]
  smul_mem' r P (hP : F.IsInvariantDifferential P) := by
    change F.IsInvariantDifferential (r • P)
    rw [IsInvariantDifferential, PowerSeries.subst_smul F.hasSubst_toPowerSeries,
      PowerSeries.subst_smul (.X 0), smul_mul_assoc, hP]

@[simp]
theorem mem_invariantDifferentials {F : FormalGroup R} {P : PowerSeries R} :
    P ∈ F.invariantDifferentials ↔ F.IsInvariantDifferential P :=
  Iff.rfl

/-- The normalized invariant differential `ω(T) = F_X(0, T)⁻¹ dT` of `F`. -/
def invariantDifferential (F : FormalGroup R) : PowerSeries R :=
  PowerSeries.invOfUnit ((pderiv 0 F.toPowerSeries).subst ![0, PowerSeries.X]) 1

private theorem constantCoeff_subst_of_forall_eq_zero {σ τ : Type*} [Finite σ]
    {a : σ → MvPowerSeries τ R} (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (f.subst a) = constantCoeff f := by
  have hs := hasSubst_of_constantCoeff_zero ha
  have h := constantCoeff_subst_eq_zero hs ha (f := f - C (constantCoeff f)) (by simp)
  rwa [subst_sub hs, subst_C, map_sub, sub_eq_zero, constantCoeff_C] at h

private theorem constantCoeff_pderiv_zero (F : FormalGroup R) :
    constantCoeff (pderiv 0 F.toPowerSeries) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, _root_.zero_add, F.lin_coeff_X]
  simp

/-- `F_X(0, T) * ω(T) = 1`. -/
theorem mul_invariantDifferential (F : FormalGroup R) :
    (pderiv 0 F.toPowerSeries).subst ![0, PowerSeries.X] * F.invariantDifferential = 1 := by
  refine PowerSeries.mul_invOfUnit _ _ ?_
  change constantCoeff ((pderiv 0 F.toPowerSeries).subst ![0, PowerSeries.X]) = _
  rw [constantCoeff_subst_of_forall_eq_zero, constantCoeff_pderiv_zero, Units.val_one]
  intro s
  fin_cases s
  · simp
  · exact constantCoeff_X _

/-- `F.invariantDifferential` is normalized. -/
@[simp]
theorem constantCoeff_invariantDifferential (F : FormalGroup R) :
    PowerSeries.constantCoeff F.invariantDifferential = 1 := by
  simp [invariantDifferential, PowerSeries.constantCoeff_invOfUnit]

private theorem constantCoeff_subst_toPowerSeries (F : FormalGroup R) {τ : Type*}
    {x y : MvPowerSeries τ R} (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    constantCoeff (F.toPowerSeries.subst ![x, y]) = 0 :=
  constantCoeff_subst_eq_zero
    (FormalGroup.hasSubst_pair (.of_constantCoeff_zero hx) (.of_constantCoeff_zero hy))
    (by intro i; fin_cases i <;> assumption) F.zero_constantCoeff

private theorem subst_pair_subst {τ υ : Type*} (f : MvPowerSeries (Fin 2) R)
    {x y : MvPowerSeries τ R} (hx : constantCoeff x = 0) (hy : constantCoeff y = 0)
    {b : τ → MvPowerSeries υ R} (hb : HasSubst b) :
    (f.subst ![x, y]).subst b = f.subst ![x.subst b, y.subst b] := by
  rw [subst_comp_subst_apply
    (FormalGroup.hasSubst_pair (.of_constantCoeff_zero hx) (.of_constantCoeff_zero hy)) hb]
  congr 1
  funext s
  fin_cases s <;> rfl

private theorem subst_X_X (f : MvPowerSeries (Fin 2) R) : f.subst ![X 0, X 1] = f := by
  rw [show (![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 2) R) = X by
    funext s; fin_cases s <;> rfl, subst_self]
  rfl

/-- The chain rule for `F(x, y)`. -/
private theorem pderiv_subst_toPowerSeries (F : FormalGroup R) {τ : Type*} [Finite τ]
    {x y : MvPowerSeries τ R} (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) (i : τ) :
    pderiv i (F.toPowerSeries.subst ![x, y]) =
      (pderiv 0 F.toPowerSeries).subst ![x, y] * pderiv i x +
        (pderiv 1 F.toPowerSeries).subst ![x, y] * pderiv i y := by
  rw [pderiv_subst (by intro s; fin_cases s <;> assumption), Fin.sum_univ_two]
  rfl

/-- Differentiating associativity: `F_X(T, S) F_X(0, T) = F_X(0, F(T, S))`. -/
private theorem pderiv_mul_subst_zero_X (F : FormalGroup R) :
    pderiv 0 F.toPowerSeries * (pderiv 0 F.toPowerSeries).subst ![0, X 0] =
      (pderiv 0 F.toPowerSeries).subst ![0, F.toPowerSeries] := by
  have hX (i : Fin 3) : constantCoeff (X i : MvPowerSeries (Fin 3) R) = 0 := constantCoeff_X i
  have hA := F.constantCoeff_subst_toPowerSeries (hX 0) (hX 1)
  have hB := F.constantCoeff_subst_toPowerSeries (hX 1) (hX 2)
  -- differentiate `F(F(U, T), S) = F(U, F(T, S))` with respect to `U`
  have h := congrArg (pderiv 0) (F.assoc_subst _ _ _ (hX 0) (hX 1) (hX 2))
  rw [F.pderiv_subst_toPowerSeries hA (hX 2), F.pderiv_subst_toPowerSeries (hX 0) (hX 1),
    F.pderiv_subst_toPowerSeries (hX 0) hB, F.pderiv_subst_toPowerSeries (hX 1) (hX 2)] at h
  simp only [pderiv_X_self, pderiv_X_of_ne (show (1 : Fin 3) ≠ 0 by decide),
    pderiv_X_of_ne (show (2 : Fin 3) ≠ 0 by decide), mul_one, mul_zero, _root_.add_zero] at h
  -- set `U = 0`
  have hb : HasSubst (![0, X 0, X 1] : Fin 3 → MvPowerSeries (Fin 2) R) :=
    hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp)
  have h' := congrArg (subst (![0, X 0, X 1] : Fin 3 → MvPowerSeries (Fin 2) R)) h
  rw [subst_mul hb, subst_pair_subst _ hA (hX 2) hb, subst_pair_subst _ (hX 0) (hX 1) hb,
    subst_pair_subst _ (hX 0) hB hb, subst_pair_subst _ (hX 0) (hX 1) hb,
    subst_pair_subst _ (hX 1) (hX 2) hb] at h'
  simp only [subst_X hb] at h'
  simpa [F.zero_add (PowerSeries.HasSubst.X (0 : Fin 2) (S := R)), subst_X_X, mul_comm] using h'

private theorem subst_subst_zero_X {τ : Type*} (f : MvPowerSeries (Fin 2) R)
    {a : MvPowerSeries τ R} (ha : constantCoeff a = 0) :
    PowerSeries.subst a (f.subst ![0, PowerSeries.X] : PowerSeries R) = f.subst ![0, a] := by
  rw [PowerSeries.subst, subst_pair_subst (y := PowerSeries.X) _ (map_zero _) (constantCoeff_X ())
    (PowerSeries.HasSubst.of_constantCoeff_zero ha).const,
    subst_zero' (PowerSeries.HasSubst.of_constantCoeff_zero ha).const]
  congr
  exact PowerSeries.subst_X (.of_constantCoeff_zero ha)

/-- **Existence** of the normalized invariant differential (Silverman, Proposition IV.4.2):
`ω(T) = F_X(0, T)⁻¹ dT` is invariant. -/
theorem isInvariantDifferential_invariantDifferential (F : FormalGroup R) :
    F.IsInvariantDifferential F.invariantDifferential := by
  set g : PowerSeries R := (pderiv 0 F.toPowerSeries).subst ![0, PowerSeries.X]
  have hF := F.hasSubst_toPowerSeries
  have hX : PowerSeries.HasSubst (X 0 : MvPowerSeries (Fin 2) R) := .X 0
  have hg : g * F.invariantDifferential = 1 := F.mul_invariantDifferential
  -- `F_X(T, S) g(T) = g(F(T, S))`
  have key : pderiv 0 F.toPowerSeries * g.subst (X 0 : MvPowerSeries (Fin 2) R) =
      g.subst F.toPowerSeries := by
    rw [subst_subst_zero_X _ (constantCoeff_X 0), subst_subst_zero_X _ F.zero_constantCoeff]
    exact F.pderiv_mul_subst_zero_X
  simp only [IsInvariantDifferential, ← PowerSeries.coe_substAlgHom hF,
    ← PowerSeries.coe_substAlgHom hX] at key ⊢
  calc PowerSeries.substAlgHom hF F.invariantDifferential * pderiv 0 F.toPowerSeries
      = PowerSeries.substAlgHom hF F.invariantDifferential * pderiv 0 F.toPowerSeries *
          PowerSeries.substAlgHom hX (g * F.invariantDifferential) := by
        rw [hg, map_one, mul_one]
    _ = PowerSeries.substAlgHom hF (F.invariantDifferential * g) *
          PowerSeries.substAlgHom hX F.invariantDifferential := by
        rw [map_mul, map_mul, ← key]
        ring
    _ = PowerSeries.substAlgHom hX F.invariantDifferential := by
        rw [mul_comm F.invariantDifferential, hg, map_one, one_mul]

/-- **Uniqueness** (Silverman, Proposition IV.4.2): every invariant differential `P` on `F` equals
`P(0) • ω`, where `ω` is the normalized invariant differential. This follows by setting `T = 0` in
`P(F(T, S)) F_X(T, S) = P(T)`. -/
theorem IsInvariantDifferential.eq_smul {F : FormalGroup R} {P : PowerSeries R}
    (hP : F.IsInvariantDifferential P) :
    P = PowerSeries.constantCoeff P • F.invariantDifferential := by
  set g : PowerSeries R := (pderiv 0 F.toPowerSeries).subst ![0, PowerSeries.X]
  have hc : HasSubst (![0, PowerSeries.X] : Fin 2 → PowerSeries R) :=
    FormalGroup.hasSubst_pair .zero .X'
  -- setting `T = 0` gives `P(S) g(S) = P(0)`
  have h := congrArg (subst (![0, PowerSeries.X] : Fin 2 → PowerSeries R)) hP
  rw [subst_mul hc, PowerSeries.subst, PowerSeries.subst,
    subst_comp_subst_apply F.hasSubst_toPowerSeries.const hc,
    subst_comp_subst_apply (PowerSeries.HasSubst.X 0).const hc, subst_X hc] at h
  change P.subst F.zeroX * g = P.subst (0 : PowerSeries R) at h
  rw [F.zeroX_eq_X, PowerSeries.subst_zero_eq_C_constantCoeff,
    show P.subst (PowerSeries.X : PowerSeries R) = P from congrFun subst_self P] at h
  calc P = P * g * F.invariantDifferential := by
        rw [mul_assoc, F.mul_invariantDifferential, mul_one]
    _ = _ := by rw [h, smul_eq_C_mul]; simp

/-- Every invariant differential on `F` is of the form `a ω` with `a ∈ R`, where `ω` is the
normalized invariant differential. -/
theorem isInvariantDifferential_iff {F : FormalGroup R} {P : PowerSeries R} :
    F.IsInvariantDifferential P ↔ ∃ a : R, P = a • F.invariantDifferential :=
  ⟨fun h ↦ ⟨_, h.eq_smul⟩, fun ⟨a, h⟩ ↦
    h ▸ F.invariantDifferentials.smul_mem a F.isInvariantDifferential_invariantDifferential⟩

/-- The invariant differentials on `F` are the `R`-multiples of the normalized one. -/
theorem invariantDifferentials_eq_span (F : FormalGroup R) :
    F.invariantDifferentials = R ∙ F.invariantDifferential := by
  ext P
  simp [Submodule.mem_span_singleton, isInvariantDifferential_iff, eq_comm]

/-- Evaluation at the origin identifies the `R`-module of right-invariant differentials
with `R`. Its inverse sends `a` to `a • F.invariantDifferential`; thus this module is free of
rank one with the normalized invariant differential as its distinguished generator. -/
def invariantDifferentialsEquiv (F : FormalGroup R) : F.invariantDifferentials ≃ₗ[R] R where
  toFun P := PowerSeries.constantCoeff P.val
  invFun a := ⟨a • F.invariantDifferential,
    F.invariantDifferentials.smul_mem a F.isInvariantDifferential_invariantDifferential⟩
  left_inv P := Subtype.ext (IsInvariantDifferential.eq_smul P.property).symm
  right_inv a := by simp [PowerSeries.constantCoeff_smul]
  map_add' P Q := map_add PowerSeries.constantCoeff P.val Q.val
  map_smul' a P := by simp

@[simp]
theorem invariantDifferentialsEquiv_apply (F : FormalGroup R) (P : F.invariantDifferentials) :
    F.invariantDifferentialsEquiv P = PowerSeries.constantCoeff (P : PowerSeries R) := rfl

@[simp]
theorem invariantDifferentialsEquiv_symm_apply (F : FormalGroup R) (a : R) :
    (F.invariantDifferentialsEquiv.symm a : PowerSeries R) = a • F.invariantDifferential := rfl

/-- The distinguished normalized differential corresponds to `1 ∈ R`. -/
@[simp]
theorem invariantDifferentialsEquiv_symm_one (F : FormalGroup R) :
    (F.invariantDifferentialsEquiv.symm 1 : PowerSeries R) = F.invariantDifferential := by
  simp

/-- A normalized invariant differential is `F.invariantDifferential`. -/
theorem IsInvariantDifferential.eq_invariantDifferential {F : FormalGroup R} {P : PowerSeries R}
    (hP : F.IsInvariantDifferential P) (h0 : PowerSeries.constantCoeff P = 1) :
    P = F.invariantDifferential := by
  rw [hP.eq_smul, h0, one_smul]

/-- **Silverman, Proposition IV.4.2**: a formal group has a unique normalized invariant
differential. -/
theorem existsUnique_invariantDifferential (F : FormalGroup R) :
    ∃! P : PowerSeries R, F.IsInvariantDifferential P ∧ PowerSeries.constantCoeff P = 1 :=
  ⟨_, ⟨F.isInvariantDifferential_invariantDifferential, F.constantCoeff_invariantDifferential⟩,
    fun _ h ↦ h.1.eq_invariantDifferential h.2⟩

/-- The normalized invariant differential of the additive formal group is `dT`. -/
@[simp]
theorem invariantDifferential_additive : (additive R).invariantDifferential = 1 := by
  have hc : HasSubst (![0, PowerSeries.X] : Fin 2 → PowerSeries R) :=
    FormalGroup.hasSubst_pair .zero .X'
  have h := (additive R).mul_invariantDifferential
  rwa [additive_toPowerSeries, map_add, pderiv_X_self, pderiv_X_of_ne (by decide),
    _root_.add_zero, ← substAlgHom_apply hc, map_one, one_mul] at h

end FormalGroup
