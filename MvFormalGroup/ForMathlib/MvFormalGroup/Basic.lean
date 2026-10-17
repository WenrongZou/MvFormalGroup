/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import MvFormalGroup.ForMathlib.MvPowerSeries.Substitution
public import MvFormalGroup.ForMathlib.MvPowerSeries.ImplicitInfinite

/-!
# Multidimensional formal group laws

A formal group law over `R` has an arbitrary coordinate index `σ`, which may be infinite.
Variables are indexed by `Fin 2 × σ`: `(0, i)` denotes `Xᵢ` and `(1, i)` denotes `Yᵢ`.
The linear part is `X + Y`, and the law is associative. In addition, each monomial
occurs in only finitely many coordinate series (`coeff_zero`). Together with zero
constant terms, this gives `MvPowerSeries.HasSubst`, making composition well-defined.
For finite `σ`, the extra condition is automatic.

The identity equations are deduced using order estimates valid for arbitrary variables.
Commutativity is a separate property `MvFormalGroup.IsComm`; inverses are constructed in
`MvFormalGroup.Inverse`. Finite-index convenience lemmas and the `truncTotal` API
retain their `[Finite σ]` hypotheses.
-/

@[expose] public section

noncomputable section

open MvPowerSeries Finsupp Function

namespace MvFormalGroup

variable {R : Type*} [CommRing R] {σ τ : Type*}

/-- For finite coordinate families, zero constant terms suffice for paired substitution.
For arbitrary indices, use `MvPowerSeries.HasSubst.pair`. -/
lemma hasSubst_pair [Finite σ] {x y : σ → MvPowerSeries τ R}
    (hx : ∀ i, constantCoeff (x i) = 0) (hy : ∀ i, constantCoeff (y i) = 0) :
    HasSubst (Function.uncurry ![x, y]) :=
  /- Here `![x, y] : Fin 2 → σ → MvPowerSeries τ R`. -/
  hasSubst_of_constantCoeff_zero fun ⟨b, i⟩ => by fin_cases b <;> simp [hx, hy]

lemma constantCoeff_subst_pair [Finite σ] {f : σ → MvPowerSeries (Fin 2 × σ) R}
    {x y : σ → MvPowerSeries τ R} (hf : ∀ i, constantCoeff (f i) = 0)
    (hx : ∀ i, constantCoeff (x i) = 0) (hy : ∀ i, constantCoeff (y i) = 0)
    (i : σ) : constantCoeff ((f i).subst (uncurry ![x, y])) = 0 := by
  apply constantCoeff_subst_eq_zero (hasSubst_pair hx hy) _ (hf i)
  intro ⟨b, j⟩
  fin_cases b <;> simp [Function.uncurry, hx, hy]

end MvFormalGroup

/-- A formal group law over a commutative ring `R` with (possibly infinite) coordinate
index `σ`. -/
@[ext]
structure MvFormalGroup (σ : Type*) (R : Type*) [CommRing R] [DecidableEq σ] where
  /-- The coordinate power series `F(i)(X, Y)`. -/
  toPowerSeries : σ → MvPowerSeries (Fin 2 × σ) R
  /-- Every coordinate has zero constant term. -/
  zero_constantCoeff : ∀ i, constantCoeff (toPowerSeries i) = 0
  /-- The coefficient of `Xⱼ` in `F(i)` is the Kronecker delta. -/
  lin_coeff_X i j : coeff (single (0, j) 1) (toPowerSeries i) = if j = i then 1 else 0
  /-- The coefficient of `Yⱼ` in `F(i)` is the Kronecker delta. -/
  lin_coeff_Y i j : coeff (single (1, j) 1) (toPowerSeries i) = if j = i then 1 else 0
  /-- (9.6.3): every monomial `XᵐYⁿ` occurs in only finitely many `F(i)`. -/
  coeff_zero d : {i | coeff d (toPowerSeries i) ≠ 0}.Finite
  /-- (9.6.4): `F(F(X, Y), Z) = F(X, F(Y, Z))`, coordinate by coordinate. -/
  assoc i :
    let V : Fin 3 → σ → MvPowerSeries (Fin 3 × σ) R := curry X
    (toPowerSeries i).subst (uncurry
      ![fun j ↦ (toPowerSeries j).subst (uncurry ![V 0, V 1]), V 2]) =
    (toPowerSeries i).subst (uncurry
      ![V 0, fun j ↦ (toPowerSeries j).subst (uncurry ![V 1, V 2])])

namespace MvFormalGroup

variable {R : Type*} [CommRing R] {σ : Type*} [DecidableEq σ]

/-- (9.6.5) Commutativity is optional: `F(X, Y) = F(Y, X)`. -/
class IsComm (F : MvFormalGroup σ R) : Prop where
  comm i :
    F.toPowerSeries i = (F.toPowerSeries i).subst (uncurry ![curry X 1, curry X 0])

section Basic

variable (F : MvFormalGroup σ R)

/-- (9.6.2): `F(i)(X, Y) ≡ Xᵢ + Yᵢ` modulo terms of total degree at least two. -/
theorem coeff_eq_of_degree_lt_two (i : σ) {d : Fin 2 × σ →₀ ℕ} (hd : d.degree < 2) :
    coeff d (F.toPowerSeries i) = coeff d (X (0, i) + X (1, i)) := by
  rcases show d.degree = 0 ∨ d.degree = 1 by omega with hzero | hone
  · have : d = 0 := d.degree_eq_zero_iff.mp hzero
    simp [this, F.zero_constantCoeff]
  · obtain ⟨⟨b, j⟩, rfl⟩ := (Finsupp.sum_eq_one_iff d).mp hone
    fin_cases b <;>
      simp [F.lin_coeff_X, F.lin_coeff_Y, coeff_X, Finsupp.single_left_inj, eq_comm]

/-- Zero constant terms and (9.6.3) say exactly that the coordinates can be substituted. -/
theorem hasSubst : HasSubst F.toPowerSeries where
  const_coeff i := by simp [F.zero_constantCoeff]
  coeff_zero := F.coeff_zero

/-- `F(x, y)` is substitutable whenever `x` and `y` are. -/
theorem hasSubst_subst_pair {τ : Type*} {x y : σ → MvPowerSeries τ R}
    (hx : HasSubst x) (hy : HasSubst y) :
    HasSubst fun j ↦ (F.toPowerSeries j).subst (uncurry ![x, y]) :=
  F.hasSubst.subst (hx.pair hy)

/-- The substitution on the left-hand side of (9.6.4) is legitimate. -/
theorem hasSubst_assoc_left :
    let V : Fin 3 → σ → MvPowerSeries (Fin 3 × σ) R := curry X
    HasSubst (uncurry ![fun j ↦ (F.toPowerSeries j).subst (uncurry ![V 0, V 1]), V 2]) :=
  (F.hasSubst_subst_pair (.curry_X 0) (.curry_X 1)).pair (.curry_X 2)

/-- The substitution on the right-hand side of (9.6.4) is legitimate. -/
theorem hasSubst_assoc_right :
    let V : Fin 3 → σ → MvPowerSeries (Fin 3 × σ) R := curry X
    HasSubst (uncurry ![V 0, fun j ↦ (F.toPowerSeries j).subst (uncurry ![V 1, V 2])]) :=
  (HasSubst.curry_X 0).pair (F.hasSubst_subst_pair (.curry_X 1) (.curry_X 2))

/-- Associativity after substituting three substitutable families. -/
theorem assoc_subst {τ : Type*} {x y z : σ → MvPowerSeries τ R}
    (hx : HasSubst x) (hy : HasSubst y) (hz : HasSubst z) (i : σ) :
    (F.toPowerSeries i).subst
        (uncurry ![fun j ↦ (F.toPowerSeries j).subst (uncurry ![x, y]), z]) =
      (F.toPowerSeries i).subst
        (uncurry ![x, fun j ↦ (F.toPowerSeries j).subst (uncurry ![y, z])]) := by
  let a : Fin 3 × σ → MvPowerSeries τ R := uncurry ![x, y, z]
  have ha : HasSubst a := HasSubst.uncurry fun b ↦ by fin_cases b <;> assumption
  have hv (b : Fin 3) := HasSubst.curry_X (R := R) (σ := σ) b
  have hX (b : Fin 3) : (fun j ↦ (curry X b j : MvPowerSeries (Fin 3 × σ) R).subst a) =
      ![x, y, z] b := by
    funext j
    simp [subst_X ha, a]
  have hF (b c : Fin 3) : (fun j ↦ ((F.toPowerSeries j).subst
      (uncurry ![curry X b, curry X c] : Fin 2 × σ → MvPowerSeries (Fin 3 × σ) R)).subst a) =
      fun j ↦ (F.toPowerSeries j).subst (uncurry ![![x, y, z] b, ![x, y, z] c]) := by
    funext j
    rw [subst_pair_subst _ _ _ ((hv b).pair (hv c)) ha, hX, hX]
  have h := congrArg (subst a) (F.assoc i)
  rw [subst_pair_subst _ _ _ F.hasSubst_assoc_left ha,
    subst_pair_subst _ _ _ F.hasSubst_assoc_right ha, hF, hF, hX, hX] at h
  simpa using h

/-! ### The identity -/

/-- `F(x, y) ≡ x + y` modulo terms of total degree at least two. -/
theorem two_le_order_subst_sub {τ : Type*} {x y : σ → MvPowerSeries τ R}
    (hx : HasSubst x) (hy : HasSubst y) (hx0 : ∀ i, constantCoeff (x i) = 0)
    (hy0 : ∀ i, constantCoeff (y i) = 0) (i : σ) :
    (2 : ℕ∞) ≤ ((F.toPowerSeries i).subst (uncurry ![x, y]) - (x i + y i)).order := by
  have hp := hx.pair hy
  have hp0 : ∀ s, constantCoeff (uncurry ![x, y] s) = 0 := by
    intro ⟨b, j⟩
    fin_cases b <;> simp [hx0, hy0]
  have h := succ_le_order_subst_sub (n := 1) (b := 0)
    (f := F.toPowerSeries i - (X (0, i) + X (1, i))) hp HasSubst.zero hp0 (fun _ ↦ by simp)
    (fun s ↦ by simpa using one_le_order_iff_constCoeff_eq_zero.mpr (hp0 s))
    (fun s _ ↦ by
      rw [map_sub, F.coeff_eq_of_degree_lt_two i (d := single s 1) (by simp), sub_self])
  rw [subst_zero_of_constantCoeff_zero (by simp [F.zero_constantCoeff]), sub_zero,
    subst_sub hp, subst_add hp, subst_X hp, subst_X hp] at h
  simpa [one_add_one_eq_two] using h

/-- The family of series `F(X, 0)`. -/
abbrev Xzero : σ → MvPowerSeries σ R := fun i ↦ (F.toPowerSeries i).subst (uncurry ![X, 0])

/-- The family of series `F(0, X)`. -/
abbrev zeroX : σ → MvPowerSeries σ R := fun i ↦ (F.toPowerSeries i).subst (uncurry ![0, X])

@[simp]
theorem constantCoeff_Xzero (i : σ) : constantCoeff (F.Xzero i) = 0 :=
  constantCoeff_subst_eq_zero (HasSubst.X.pair .zero)
    (by rintro ⟨b, j⟩; fin_cases b <;> simp) (F.zero_constantCoeff i)

@[simp]
theorem constantCoeff_zeroX (i : σ) : constantCoeff (F.zeroX i) = 0 :=
  constantCoeff_subst_eq_zero (HasSubst.zero.pair .X)
    (by rintro ⟨b, j⟩; fin_cases b <;> simp) (F.zero_constantCoeff i)

@[simp]
theorem Xzero_subst_Xzero (i : σ) : (F.Xzero i).subst F.Xzero = F.Xzero i := by
  have hs : HasSubst F.Xzero := F.hasSubst_subst_pair .X .zero
  rw [Xzero, subst_pair_subst _ X 0 (HasSubst.X.pair .zero) hs]
  have h00 : uncurry ![(0 : σ → MvPowerSeries σ R), 0] = 0 := by
    funext ⟨b, j⟩; fin_cases b <;> rfl
  simpa only [h00, subst_zero_of_constantCoeff_zero (F.zero_constantCoeff _),
    Pi.zero_apply, ← substAlgHom_apply hs, map_zero, substAlgHom_X,
    Xzero, ← Pi.zero_def] using F.assoc_subst (x := X) (y := 0) (z := 0) .X .zero .zero i

@[simp]
theorem zeroX_subst_zeroX (i : σ) : (F.zeroX i).subst F.zeroX = F.zeroX i := by
  have hs : HasSubst F.zeroX := F.hasSubst_subst_pair .zero .X
  rw [zeroX, subst_pair_subst _ 0 X (HasSubst.zero.pair .X) hs]
  have h00 : uncurry ![(0 : σ → MvPowerSeries σ R), 0] = 0 := by
    funext ⟨b, j⟩; fin_cases b <;> rfl
  simpa only [h00, subst_zero_of_constantCoeff_zero (F.zero_constantCoeff _),
    Pi.zero_apply, ← substAlgHom_apply hs, map_zero, substAlgHom_X,
    zeroX, ← Pi.zero_def] using (F.assoc_subst (x := 0) (y := 0) (z := X) .zero .zero .X i).symm

omit [DecidableEq σ] in
/-- An idempotent family congruent to `X` modulo degree two is `X`. -/
private theorem eq_X_of_idempotent (g : σ → MvPowerSeries σ R) (hg : HasSubst g)
    (hg0 : ∀ i, constantCoeff (g i) = 0) (hlin : ∀ i, (2 : ℕ∞) ≤ (g i - X i).order)
    (hgg : ∀ i, (g i).subst g = g i) : g = X := by
  have h (n : ℕ) : ∀ i, (n : ℕ∞) ≤ (g i - X i).order := by
    induction n with
    | zero => simp
    | succ n ih =>
      intro i
      have hf : ∀ s, g s ≠ X s → coeff (single s 1) (g i - X i) = 0 := fun s _ ↦ by
        have hs : (((single s 1 : σ →₀ ℕ).degree : ℕ) : ℕ∞) < 2 := by simp
        exact coeff_of_lt_order (hs.trans_le (hlin i))
      have := succ_le_order_subst_sub (b := X) hg HasSubst.X hg0 (fun s ↦ constantCoeff_X s) ih hf
      rwa [subst_sub hg, hgg, subst_X hg, sub_self, subst_self, id_eq, zero_sub,
        order_neg] at this
  funext i
  ext d
  exact coeff_eq_of_le_order_sub (h _ i) (lt_add_one _)

/-- Zero is a right identity: `F(X, 0) = X`. -/
@[simp]
theorem Xzero_eq_X (i : σ) : F.Xzero i = X i := by
  refine congrFun (eq_X_of_idempotent F.Xzero (F.hasSubst_subst_pair .X .zero)
    (fun j ↦ ?_) (fun j ↦ ?_) F.Xzero_subst_Xzero) i
  · exact F.constantCoeff_Xzero j
  · simpa using F.two_le_order_subst_sub (x := X) (y := 0) .X .zero
      (fun k ↦ constantCoeff_X k) (by simp) j

/-- Zero is a left identity: `F(0, X) = X`. -/
@[simp]
theorem zeroX_eq_X (i : σ) : F.zeroX i = X i := by
  refine congrFun (eq_X_of_idempotent F.zeroX (F.hasSubst_subst_pair .zero .X)
    (fun j ↦ ?_) (fun j ↦ ?_) F.zeroX_subst_zeroX) i
  · exact F.constantCoeff_zeroX j
  · simpa using F.two_le_order_subst_sub (x := 0) (y := X) .zero .X
      (by simp) (fun k ↦ constantCoeff_X k) j

/-- Zero is a right identity after any admissible substitution. -/
@[simp]
theorem add_zero {τ : Type*} {a : σ → MvPowerSeries τ R} (ha : HasSubst a) (i : σ) :
    (F.toPowerSeries i).subst (uncurry ![a, 0]) = a i := by
  have h := congrArg (subst a) (F.Xzero_eq_X i)
  rw [Xzero, subst_pair_subst _ X 0 (HasSubst.X.pair .zero) ha] at h
  simpa only [Pi.zero_apply, ← substAlgHom_apply ha, map_zero, substAlgHom_X,
    ← Pi.zero_def] using h

/-- Zero is a left identity after any admissible substitution. -/
@[simp]
theorem zero_add {τ : Type*} {a : σ → MvPowerSeries τ R} (ha : HasSubst a) (i : σ) :
    (F.toPowerSeries i).subst (uncurry ![0, a]) = a i := by
  have h := congrArg (subst a) (F.zeroX_eq_X i)
  rw [zeroX, subst_pair_subst _ 0 X (HasSubst.zero.pair .X) ha] at h
  simpa only [Pi.zero_apply, ← substAlgHom_apply ha, map_zero, substAlgHom_X,
    ← Pi.zero_def] using h

end Basic

omit [DecidableEq σ] in
/-- Substituting `(x, y)` into `Xᵢ + Yᵢ` gives `xᵢ + yᵢ`. -/
private theorem subst_X_add_X {τ : Type*} {x y : σ → MvPowerSeries τ R}
    (hx : HasSubst x) (hy : HasSubst y) (i : σ) :
    (X (0, i) + X (1, i) : MvPowerSeries (Fin 2 × σ) R).subst (uncurry ![x, y]) = x i + y i := by
  simp [subst_add (hx.pair hy), subst_X (hx.pair hy)]

/-- The additive formal group law `F(i)(X, Y) = Xᵢ + Yᵢ`. -/
def additive (σ : Type*) (R : Type*) [CommRing R] [DecidableEq σ] : MvFormalGroup σ R where
  toPowerSeries i := X (0, i) + X (1, i)
  zero_constantCoeff _ := by simp
  lin_coeff_X i j := by simp [coeff_index_single_X]
  lin_coeff_Y i j := by simp [coeff_index_single_X]
  coeff_zero d := ((HasSubst.curry_X (R := R) (σ := σ) 0).add (.curry_X 1)).coeff_zero d
  assoc i := by
    have hv (b : Fin 3) := HasSubst.curry_X (R := R) (σ := σ) b
    simp only [subst_X_add_X (hv _) (hv _)]
    rw [subst_X_add_X (x := fun j ↦ curry X 0 j + curry X 1 j) ((hv 0).add (hv 1)) (hv 2),
      subst_X_add_X (y := fun j ↦ curry X 1 j + curry X 2 j) (hv 0) ((hv 1).add (hv 2)),
      add_assoc]

instance : (additive σ R).IsComm where
  comm i := by
    change X (0, i) + X (1, i) = (X (0, i) + X (1, i) : MvPowerSeries (Fin 2 × σ) R).subst _
    rw [subst_X_add_X (.curry_X 1) (.curry_X 0)]
    simp [add_comm]

section Finite

variable [Finite σ]

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

end Finite

end MvFormalGroup

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
