/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Multidimensional formal group laws

A formal group law with finite coordinate index `σ` is a `σ`-indexed family of
power series in two blocks of variables, with linear part `X + Y`, satisfying
associativity. Variables are indexed by `Fin 2 × σ`: `(0, i)` denotes `Xᵢ` and
`(1, i)` denotes `Yᵢ`. Associativity uses three blocks, indexed by `Fin 3 × σ`.
Taking `σ = Fin n` recovers dimension `n`; taking `σ = Fin m × Fin m` allows
matrix coordinates. Only finiteness, rather than an enumeration, is required.

The coefficient axioms express `Fᵢ(X, Y) = Xᵢ + Yᵢ mod (degree 2)`; in
particular, all off-diagonal linear coefficients vanish. Commutativity is a
separate property, `MvFormalGroup.IsComm`, as in the one-dimensional API.
Neither an identity nor an inverse is imposed as an additional axiom.
-/

@[expose] public section

noncomputable section

open MvPowerSeries Finsupp Function

namespace MvFormalGroup

variable {R : Type*} [CommRing R] {σ τ : Type*}

/-- Apply a variable substitution to each coordinate of a family.
Used by the alternative vector-equality definition `MvFormalGroup'`. -/
def comp (f : σ → MvPowerSeries (Fin 2 × σ) R)
    (v : Fin 2 × σ → MvPowerSeries τ R) : σ → MvPowerSeries τ R :=
  fun i ↦ (f i).subst v

lemma hasSubst_pair [Finite σ] {x y : σ → MvPowerSeries τ R}
    (hx : ∀ i, constantCoeff (x i) = 0) (hy : ∀ i, constantCoeff (y i) = 0) :
    HasSubst (Function.uncurry ![x, y]) := by
  apply hasSubst_of_constantCoeff_zero
  rintro ⟨b, i⟩
  fin_cases b <;> simp [Function.uncurry, hx, hy]

@[simp]
lemma constantCoeff_curry_X {k : ℕ} (b : Fin k) (i : σ) :
    constantCoeff (Function.curry (X (R := R)) b i) = 0 := constantCoeff_X _

lemma constantCoeff_subst_pair [Finite σ] {f : σ → MvPowerSeries (Fin 2 × σ) R}
    {x y : σ → MvPowerSeries τ R}
    (hf : ∀ i, constantCoeff (f i) = 0)
    (hx : ∀ i, constantCoeff (x i) = 0) (hy : ∀ i, constantCoeff (y i) = 0)
    (i : σ) : constantCoeff ((f i).subst (uncurry ![x, y])) = 0 := by
  apply constantCoeff_subst_eq_zero (hasSubst_pair hx hy) _ (hf i)
  rintro ⟨b, j⟩
  fin_cases b <;> simp [Function.uncurry, hx, hy]

end MvFormalGroup

/-- A formal group law over a commutative ring `R` with finite coordinate index `σ`.
The two linear coefficient axioms give the identity matrix in each block. -/
@[ext]
structure MvFormalGroup (σ : Type*) [Finite σ] (R : Type*) [CommRing R]
    [DecidableEq σ] where
  /-- The coordinate power series `Fᵢ(X, Y)`. -/
  toPowerSeries : σ → MvPowerSeries (Fin 2 × σ) R
  /-- Every coordinate has zero constant term. -/
  zero_constantCoeff : ∀ i, constantCoeff (toPowerSeries i) = 0
  /-- The coefficient of `Xⱼ` in `Fᵢ` is the Kronecker delta. -/
  lin_coeff_X i j : coeff (single (0, j) 1) (toPowerSeries i) = if j = i then 1 else 0
  /-- The coefficient of `Yⱼ` in `Fᵢ` is the Kronecker delta. -/
  lin_coeff_Y i j : coeff (single (1, j) 1) (toPowerSeries i) = if j = i then 1 else 0
  /-- `F(F(X, Y), Z) = F(X, F(Y, Z))`, coordinate by coordinate. -/
  assoc i :
    let V : Fin 3 → σ → MvPowerSeries (Fin 3 × σ) R := curry X
    (toPowerSeries i).subst (uncurry
      ![fun j ↦ (toPowerSeries j).subst (uncurry ![V 0, V 1]), V 2]) =
    (toPowerSeries i).subst (uncurry
      ![V 0, fun j ↦ (toPowerSeries j).subst (uncurry ![V 1, V 2])])

/-- The original formulation, retained for comparison with `MvFormalGroup`.
It takes the coefficient ring first and states associativity as a vector equality
using `MvFormalGroup.comp`. -/
@[ext]
structure MvFormalGroup' (R : Type*) [CommRing R] (σ : Type*) [Finite σ]
    [DecidableEq σ] where
  /-- The coordinate power series `Fᵢ(X, Y)`. -/
  toPowerSeries : σ → MvPowerSeries (Fin 2 × σ) R
  /-- Every coordinate has zero constant term. -/
  zero_constantCoeff : ∀ i, constantCoeff (toPowerSeries i) = 0
  /-- The coefficient of `Xⱼ` in `Fᵢ` is the Kronecker delta. -/
  lin_coeff_X : ∀ i j, coeff (single (0, j) 1) (toPowerSeries i) = if j = i then 1 else 0
  /-- The coefficient of `Yⱼ` in `Fᵢ` is the Kronecker delta. -/
  lin_coeff_Y : ∀ i j, coeff (single (1, j) 1) (toPowerSeries i) = if j = i then 1 else 0
  /-- `F(F(X, Y), Z) = F(X, F(Y, Z))` as an equality of coordinate families. -/
  assoc :
    let V : Fin 3 → σ → MvPowerSeries (Fin 3 × σ) R := Function.curry X
    MvFormalGroup.comp toPowerSeries (Function.uncurry
      ![MvFormalGroup.comp toPowerSeries (Function.uncurry ![V 0, V 1]), V 2]) =
    MvFormalGroup.comp toPowerSeries (Function.uncurry
      ![V 0, MvFormalGroup.comp toPowerSeries (Function.uncurry ![V 1, V 2])])

namespace MvFormalGroup

variable {R : Type*} [CommRing R] {σ : Type*} [Finite σ] [DecidableEq σ]

/-- Commutativity is optional: `F(X, Y) = F(Y, X)`. -/
class IsComm (F : MvFormalGroup σ R) : Prop where
  comm i :
    let V : Fin 2 → σ → MvPowerSeries (Fin 2 × σ) R := curry X
    F.toPowerSeries i = (F.toPowerSeries i).subst (uncurry ![V 1, V 0])

/-- The coefficient axioms give exactly the prescribed truncation modulo degree two. -/
theorem truncTotal_two (F : MvFormalGroup σ R) (i : σ) :
    (F.toPowerSeries i).truncTotal 2 = MvPolynomial.X (0, i) + MvPolynomial.X (1, i) := by
  classical
  ext d
  by_cases hd : d.degree < 2
  · rw [coeff_truncTotal _ hd]
    rcases show d.degree = 0 ∨ d.degree = 1 by omega with hzero | hone
    · have : d = 0 := d.degree_eq_zero_iff.mp hzero
      simp [this, F.zero_constantCoeff, MvPolynomial.coeff_X]
    · obtain ⟨⟨b, j⟩, rfl⟩ := (Finsupp.sum_eq_one_iff d).mp hone
      fin_cases b <;>
        simp [F.lin_coeff_X, F.lin_coeff_Y, MvPolynomial.coeff_X,
          Finsupp.single_left_inj, eq_comm]
  · rw [coeff_truncTotal_eq_zero _ (by omega)]
    have hx : d ≠ single (0, i) 1 := by rintro rfl; simp at hd
    have hy : d ≠ single (1, i) 1 := by rintro rfl; simp at hd
    simp [MvPolynomial.coeff_X, Ne.symm hx, Ne.symm hy]

/-- The additive formal group with coordinates indexed by `σ`. -/
def additive (σ : Type*) [Finite σ] (R : Type*) [CommRing R] [DecidableEq σ] :
    MvFormalGroup σ R where
  toPowerSeries i := X (0, i) + X (1, i)
  zero_constantCoeff _ := by simp
  lin_coeff_X i j := by simp [coeff_index_single_X]
  lin_coeff_Y i j := by simp [coeff_index_single_X]
  assoc i := by
    have hvars (b c : Fin 3) := hasSubst_pair
      (constantCoeff_curry_X (R := R) (σ := σ) b) (constantCoeff_curry_X c)
    have hcomp (b c : Fin 3) := constantCoeff_subst_pair
      (f := fun i : σ ↦ X (0, i) + X (1, i)) (by intro i; simp)
      (constantCoeff_curry_X (R := R) b) (constantCoeff_curry_X c)
    simp only [subst_add (hasSubst_pair (hcomp 0 1) (constantCoeff_curry_X 2)),
      subst_X (hasSubst_pair (hcomp 0 1) (constantCoeff_curry_X 2)),
      subst_add (hasSubst_pair (constantCoeff_curry_X 0) (hcomp 1 2)),
      subst_X (hasSubst_pair (constantCoeff_curry_X 0) (hcomp 1 2))]
    simp [subst_add (hvars _ _), subst_X (hvars _ _), Function.curry,
      Function.uncurry, add_assoc]

instance : (additive σ R).IsComm where
  comm i := by
    have h := hasSubst_pair (constantCoeff_curry_X (R := R) (σ := σ) (1 : Fin 2))
      (constantCoeff_curry_X 0)
    simp [additive, subst_add h, subst_X h, add_comm]

end MvFormalGroup
