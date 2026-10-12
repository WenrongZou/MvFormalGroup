/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import MvFormalGroup.ForMathlib.MvPowerSeries.Substitution

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

lemma hasSubst_pair [Finite σ] {x y : σ → MvPowerSeries τ R}
    (hx : ∀ i, constantCoeff (x i) = 0) (hy : ∀ i, constantCoeff (y i) = 0) :
    HasSubst (Function.uncurry ![x, y]) :=
  hasSubst_of_constantCoeff_zero fun ⟨b, i⟩ => by fin_cases b <;> simp [hx, hy]

@[simp]
lemma constantCoeff_curry_X (i : τ) (j : σ) :
    constantCoeff (Function.curry (X (R := R)) i j) = 0 := constantCoeff_X _

lemma constantCoeff_subst_pair [Finite σ] {f : σ → MvPowerSeries (Fin 2 × σ) R}
    {x y : σ → MvPowerSeries τ R} (hf : ∀ i, constantCoeff (f i) = 0)
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

section AlternativeDefn

variable {R : Type*} [CommRing R] {σ τ : Type*}

/-- Apply a variable substitution to each coordinate of a family.
Used by the alternative vector-equality definition `MvFormalGroup'`. -/
def MvFormalGroup.comp (f : σ → MvPowerSeries (Fin 2 × σ) R)
    (v : Fin 2 × σ → MvPowerSeries τ R) : σ → MvPowerSeries τ R :=
  fun i ↦ (f i).subst v

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

end AlternativeDefn

namespace MvFormalGroup

variable {R : Type*} [CommRing R] {σ : Type*} [Finite σ] [DecidableEq σ]

/-- Commutativity is optional: `F(X, Y) = F(Y, X)`. -/
class IsComm (F : MvFormalGroup σ R) : Prop where
  comm i :
    F.toPowerSeries i = (F.toPowerSeries i).subst (uncurry ![curry X (1 : Fin 2), curry X 0])

/-- The coefficient axioms give exactly the prescribed truncation modulo degree two. -/
theorem truncTotal_two (F : MvFormalGroup σ R) (i : σ) :
    (F.toPowerSeries i).truncTotal 2 = MvPolynomial.X (0, i) + MvPolynomial.X (1, i) := by
  ext d
  by_cases hd : d.degree < 2
  · rw [coeff_truncTotal _ hd]
    obtain hzero | hone : d.degree = 0 ∨ d.degree = 1 := by omega
    · simp [d.degree_eq_zero_iff.mp hzero, F.zero_constantCoeff, MvPolynomial.coeff_X]
    · obtain ⟨⟨b, j⟩, rfl⟩ := (Finsupp.sum_eq_one_iff d).mp hone
      fin_cases b <;>
        simp [F.lin_coeff_X, F.lin_coeff_Y, MvPolynomial.coeff_X, Finsupp.single_left_inj, eq_comm]
  · rw [coeff_truncTotal_eq_zero _ (not_lt.mp hd)]
    have hx : d ≠ single (0, i) 1 := by
      intro rfl
      simp at hd
    have hy : d ≠ single (1, i) 1 := by
      intro rfl
      simp at hd
    simp [MvPolynomial.coeff_X, Ne.symm hx, Ne.symm hy]

omit [Finite σ] [DecidableEq σ] in
private theorem subst_pair_subst {τ υ : Type*} (f : MvPowerSeries (Fin 2 × σ) R)
    (x y : σ → MvPowerSeries τ R) {a : τ → MvPowerSeries υ R}
    (hxy : HasSubst (uncurry ![x, y])) (ha : HasSubst a) :
    (f.subst (uncurry ![x, y])).subst a =
      f.subst (uncurry ![fun i ↦ (x i).subst a, fun i ↦ (y i).subst a]) := by
  rw [subst_comp_subst_apply hxy ha]
  congr 1
  funext ⟨b, i⟩
  fin_cases b <;> rfl

/-- Associativity after substituting three families with zero constant coefficients. -/
theorem assoc_subst (F : MvFormalGroup σ R) {τ : Type*} (x y z : σ → MvPowerSeries τ R)
    (hx : ∀ i, constantCoeff (x i) = 0) (hy : ∀ i, constantCoeff (y i) = 0)
    (hz : ∀ i, constantCoeff (z i) = 0) (i : σ) :
    (F.toPowerSeries i).subst (uncurry ![fun j ↦ (F.toPowerSeries j).subst (uncurry ![x, y]), z]) =
      (F.toPowerSeries i).subst
        (uncurry ![x, fun j ↦ (F.toPowerSeries j).subst (uncurry ![y, z])]) := by
  let a : Fin 3 × σ → MvPowerSeries τ R := uncurry ![x, y, z]
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero (by
    rintro ⟨b, j⟩; fin_cases b <;> simp [a, hx, hy, hz])
  have hv (b : Fin 3) := constantCoeff_curry_X (R := R) (σ := σ) b
  have hc (b c : Fin 3) := constantCoeff_subst_pair F.zero_constantCoeff (hv b) (hv c)
  have h := congrArg (subst a) (F.assoc i)
  rw [subst_pair_subst _ _ _ (hasSubst_pair (hc 0 1) (hv 2)) ha,
    subst_pair_subst _ _ _ (hasSubst_pair (hv 0) (hc 1 2)) ha] at h
  simpa [subst_pair_subst, subst_X ha, a, hasSubst_pair, ha] using h

/-- The family of series `F(X, 0)`. -/
abbrev Xzero (F : MvFormalGroup σ R) : σ → MvPowerSeries σ R :=
  fun i ↦ (F.toPowerSeries i).subst (uncurry ![X, 0])

/-- The family of series `F(0, X)`. -/
abbrev zeroX (F : MvFormalGroup σ R) : σ → MvPowerSeries σ R :=
  fun i ↦ (F.toPowerSeries i).subst (uncurry ![0, X])

@[simp]
theorem constantCoeff_Xzero (F : MvFormalGroup σ R) (i : σ) :
    constantCoeff (F.Xzero i) = 0 :=
  constantCoeff_subst_pair F.zero_constantCoeff constantCoeff_X (by simp) i

@[simp]
theorem constantCoeff_zeroX (F : MvFormalGroup σ R) (i : σ) :
    constantCoeff (F.zeroX i) = 0 :=
  constantCoeff_subst_pair F.zero_constantCoeff (by simp) constantCoeff_X i

@[simp]
theorem Xzero_subst_Xzero (F : MvFormalGroup σ R) (i : σ) :
    (F.Xzero i).subst F.Xzero = F.Xzero i := by
  have hX0 : HasSubst (uncurry ![X, (0 : σ → MvPowerSeries σ R)]) :=
    hasSubst_pair (fun j ↦ constantCoeff_X j) (by simp)
  have hs := hasSubst_of_constantCoeff_zero (constantCoeff_Xzero F)
  rw [Xzero, subst_pair_subst _ _ _ hX0 hs]
  have h00 : uncurry ![(0 : σ → MvPowerSeries σ R), 0] = 0 := by
    funext ⟨b, j⟩; fin_cases b <;> rfl
  simpa only [h00, subst_zero_of_constantCoeff_zero (F.zero_constantCoeff _),
    Pi.zero_apply, ← substAlgHom_apply hs, map_zero, substAlgHom_X,
    Xzero, zeroX, ← Pi.zero_def] using
    F.assoc_subst X 0 0 (fun j ↦ constantCoeff_X j) (by simp) (by simp) i

@[simp]
theorem zeroX_subst_zeroX (F : MvFormalGroup σ R) (i : σ) :
    (F.zeroX i).subst F.zeroX = F.zeroX i := by
  have h0X : HasSubst (uncurry ![(0 : σ → MvPowerSeries σ R), X]) :=
    hasSubst_pair (by simp) (fun j ↦ constantCoeff_X j)
  have hs := hasSubst_of_constantCoeff_zero (constantCoeff_zeroX F)
  rw [zeroX, subst_pair_subst _ _ _ h0X hs]
  have h00 : uncurry ![(0 : σ → MvPowerSeries σ R), 0] = 0 := by
    funext ⟨b, j⟩; fin_cases b <;> rfl
  simpa only [h00, subst_zero_of_constantCoeff_zero (F.zero_constantCoeff _),
    Pi.zero_apply, ← substAlgHom_apply hs, map_zero, substAlgHom_X,
    Xzero, zeroX, ← Pi.zero_def] using
    (F.assoc_subst 0 0 X (by simp) (by simp) (fun j ↦ constantCoeff_X j) i).symm

omit [DecidableEq σ] in
private theorem eq_X_of_idempotent (f : σ → MvPowerSeries σ R)
    (h0 : ∀ i, constantCoeff (f i) = 0)
    (hlin : ∀ i, (f i).truncTotal 2 = (X i).truncTotal 2)
    (hf : ∀ i, (f i).subst f = f i) : ∀ i, f i = X i := by
  have hs := hasSubst_of_constantCoeff_zero h0
  have heq (n : ℕ) (i : σ) : (f i).truncTotal n = (X i : MvPowerSeries σ R).truncTotal n := by
    induction n generalizing i with
    | zero => ext d; simp only [coeff_truncTotal_eq_zero _ (Nat.zero_le _)]
    | succ n ih =>
      have h := truncTotal_subst_succ (f i - X i) (fun d hd ↦ by
        rw [map_sub, sub_eq_zero]; exact truncTotal_eq_iff.mp (hlin i) d hd)
        h0 (fun j ↦ constantCoeff_X j) ih
      simp only [subst_sub hs, hf, subst_X hs, sub_self, subst_self, id_eq,
        map_zero, map_sub] at h
      exact sub_eq_zero.mp h.symm
  intro i
  ext d
  exact truncTotal_eq_iff.mp (heq (d.degree + 1) i) d (Nat.lt_succ_self _)

/-- Zero is a right identity for the formal group law: `F(X, 0) = X`. -/
@[simp]
theorem Xzero_eq_X (F : MvFormalGroup σ R) (i : σ) : F.Xzero i = X i := by
  apply eq_X_of_idempotent F.Xzero (constantCoeff_Xzero F) ?_ (Xzero_subst_Xzero F) i
  intro j
  have hp : ∀ p, constantCoeff (uncurry ![X, 0] p : MvPowerSeries σ R) = 0 := by
    rintro ⟨b, k⟩; fin_cases b <;> simp [uncurry]
  rw [Xzero, truncTotal_subst_eq_truncTotal_truncTotal_subst hp, F.truncTotal_two]
  simp [subst_add (hasSubst_of_constantCoeff_zero hp),
    subst_X (hasSubst_of_constantCoeff_zero hp), uncurry]

/-- Zero is a left identity for the formal group law: `F(0, X) = X`. -/
@[simp]
theorem zeroX_eq_X (F : MvFormalGroup σ R) (i : σ) : F.zeroX i = X i := by
  apply eq_X_of_idempotent F.zeroX (constantCoeff_zeroX F) ?_ (zeroX_subst_zeroX F) i
  intro j
  have hp : ∀ p, constantCoeff (uncurry ![0, X] p : MvPowerSeries σ R) = 0 := by
    rintro ⟨b, k⟩; fin_cases b <;> simp [uncurry]
  rw [zeroX, truncTotal_subst_eq_truncTotal_truncTotal_subst hp, F.truncTotal_two]
  simp [subst_add (hasSubst_of_constantCoeff_zero hp),
    subst_X (hasSubst_of_constantCoeff_zero hp), uncurry]

/-- Zero is a right identity after any admissible substitution. -/
@[simp]
theorem add_zero (F : MvFormalGroup σ R) {τ : Type*} {a : σ → MvPowerSeries τ R}
    (ha : HasSubst a) (i : σ) : (F.toPowerSeries i).subst (uncurry ![a, 0]) = a i := by
  have h := congrArg (subst a) (F.Xzero_eq_X i)
  rw [Xzero, subst_pair_subst _ _ _ (hasSubst_pair (fun j ↦ constantCoeff_X j) (by simp)) ha]
    at h
  simpa only [Pi.zero_apply, ← substAlgHom_apply ha, map_zero, substAlgHom_X, ← Pi.zero_def] using h

/-- Zero is a left identity after any admissible substitution. -/
@[simp]
theorem zero_add (F : MvFormalGroup σ R) {τ : Type*} {a : σ → MvPowerSeries τ R}
    (ha : HasSubst a) (i : σ) : (F.toPowerSeries i).subst (uncurry ![0, a]) = a i := by
  have h := congrArg (subst a) (F.zeroX_eq_X i)
  rw [zeroX, subst_pair_subst _ _ _ (hasSubst_pair (by simp) (fun j ↦ constantCoeff_X j)) ha]
    at h
  simpa only [Pi.zero_apply, ← substAlgHom_apply ha, map_zero, substAlgHom_X, ← Pi.zero_def] using h

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
