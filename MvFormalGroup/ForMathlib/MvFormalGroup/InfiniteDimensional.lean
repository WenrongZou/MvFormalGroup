/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import MvFormalGroup.ForMathlib.MvFormalGroup.Inverse
public import MvFormalGroup.ForMathlib.MvPowerSeries.ImplicitInfinite

/-!
# Infinite-dimensional formal group laws

Following Hazewinkel, *Formal Groups and Applications*, (9.6.1), a formal group law with
(possibly infinite) index set `I` over `R` is a family `F(i)(X, Y) ∈ R⟦Xᵢ, Yᵢ; i ∈ I⟧`
such that

* (9.6.2) `F(i)(X, Y) ≡ Xᵢ + Yᵢ mod (degree 2)`;
* (9.6.3) for every monomial `XᵐYⁿ`, only finitely many `F(i)` have a nonzero coefficient
  at `XᵐYⁿ`;
* (9.6.4) `F(i)(F(X, Y), Z) = F(i)(X, F(Y, Z))`.

The formal group law is commutative if moreover (9.6.5) `F(i)(X, Y) = F(i)(Y, X)`.

As in `MvFormalGroup`, variables are indexed by `Fin 2 × I` (resp. `Fin 3 × I`), and
(9.6.2) is encoded by coefficient axioms. A monomial `XᵐYⁿ` is a finitely supported
`d : Fin 2 × I →₀ ℕ`.

Condition (9.6.3), together with the vanishing of constant terms, is exactly
`MvPowerSeries.HasSubst F.toPowerSeries`. This is what makes the substitutions in (9.6.4)
legitimate (`InfDimFormalGroup.hasSubst_assoc_left`, `InfDimFormalGroup.hasSubst_assoc_right`):
for finite `I` this is automatic, which is why `MvFormalGroup` does not need it.

The finite-dimensional proof of the identity uses `truncTotal`, which needs finitely many
variables. Here agreement below degree `n` is instead expressed as `n ≤ (f - g).order`, and the
key estimate is `MvPowerSeries.succ_le_order_subst_sub`. The inverse comes from the formal
implicit function theorem for infinitely many equations,
`MvPowerSeries.existsUnique_implicitFunctionLeftCofinite`.

## Main declarations

* `InfDimFormalGroup I R`: formal group laws with coordinate index `I`.
* `InfDimFormalGroup.IsComm`: commutativity (9.6.5).
* `InfDimFormalGroup.assoc_subst`: associativity after substituting arbitrary
  substitutable families.
* `InfDimFormalGroup.Xzero_eq_X`, `InfDimFormalGroup.zeroX_eq_X`: `F(X, 0) = X = F(0, X)`.
* `InfDimFormalGroup.inv`: the formal inverse, with `inv_left`, `inv_right`, `eq_inv`
  (uniqueness) and `hasSubst_inv` (it satisfies (9.6.3)).
* `InfDimFormalGroup.additive`: the additive formal group law `Xᵢ + Yᵢ`.
* `InfDimFormalGroup.equivMvFormalGroup`: for finite `I`, this is the same as `MvFormalGroup`;
  the inverses agree (`inv_equivMvFormalGroup`).
-/

@[expose] public section

noncomputable section

open MvPowerSeries Finsupp Function

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


end MvPowerSeries

/-- A formal group law over a commutative ring `R` with (possibly infinite) coordinate
index `I`, following Hazewinkel (9.6.1). Compared with `MvFormalGroup`, the extra axiom
`coeff_finite` is (9.6.3); it ensures that the substitutions in `assoc` are legitimate. -/
@[ext]
structure InfDimFormalGroup (I : Type*) (R : Type*) [CommRing R] [DecidableEq I] where
  /-- The coordinate power series `F(i)(X, Y)`. -/
  toPowerSeries : I → MvPowerSeries (Fin 2 × I) R
  /-- Every coordinate has zero constant term. -/
  zero_constantCoeff : ∀ i, constantCoeff (toPowerSeries i) = 0
  /-- The coefficient of `Xⱼ` in `F(i)` is the Kronecker delta. -/
  lin_coeff_X i j : coeff (single (0, j) 1) (toPowerSeries i) = if j = i then 1 else 0
  /-- The coefficient of `Yⱼ` in `F(i)` is the Kronecker delta. -/
  lin_coeff_Y i j : coeff (single (1, j) 1) (toPowerSeries i) = if j = i then 1 else 0
  /-- (9.6.3): every monomial `XᵐYⁿ` occurs in only finitely many `F(i)`. -/
  coeff_finite d : {i | coeff d (toPowerSeries i) ≠ 0}.Finite
  /-- (9.6.4): `F(F(X, Y), Z) = F(X, F(Y, Z))`, coordinate by coordinate. -/
  assoc i :
    let V : Fin 3 → I → MvPowerSeries (Fin 3 × I) R := curry X
    (toPowerSeries i).subst (uncurry
      ![fun j ↦ (toPowerSeries j).subst (uncurry ![V 0, V 1]), V 2]) =
    (toPowerSeries i).subst (uncurry
      ![V 0, fun j ↦ (toPowerSeries j).subst (uncurry ![V 1, V 2])])

namespace InfDimFormalGroup

variable {R : Type*} [CommRing R] {I : Type*} [DecidableEq I]

/-- (9.6.5) Commutativity is optional: `F(X, Y) = F(Y, X)`. -/
class IsComm (F : InfDimFormalGroup I R) : Prop where
  comm i :
    F.toPowerSeries i = (F.toPowerSeries i).subst (uncurry ![curry X (1 : Fin 2), curry X 0])

section Basic

variable (F : InfDimFormalGroup I R)

/-- (9.6.2): `F(i)(X, Y) ≡ Xᵢ + Yᵢ` modulo terms of total degree at least two. -/
theorem coeff_eq_of_degree_lt_two (i : I) {d : Fin 2 × I →₀ ℕ} (hd : d.degree < 2) :
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
  coeff_zero := F.coeff_finite

/-- `F(x, y)` is substitutable whenever `x` and `y` are. -/
theorem hasSubst_subst_pair {τ : Type*} {x y : I → MvPowerSeries τ R}
    (hx : HasSubst x) (hy : HasSubst y) :
    HasSubst fun j ↦ (F.toPowerSeries j).subst (uncurry ![x, y]) :=
  F.hasSubst.subst (hx.pair hy)

/-- The substitution on the left-hand side of (9.6.4) is legitimate. -/
theorem hasSubst_assoc_left :
    let V : Fin 3 → I → MvPowerSeries (Fin 3 × I) R := curry X
    HasSubst (uncurry ![fun j ↦ (F.toPowerSeries j).subst (uncurry ![V 0, V 1]), V 2]) :=
  (F.hasSubst_subst_pair (.curry_X 0) (.curry_X 1)).pair (.curry_X 2)

/-- The substitution on the right-hand side of (9.6.4) is legitimate. -/
theorem hasSubst_assoc_right :
    let V : Fin 3 → I → MvPowerSeries (Fin 3 × I) R := curry X
    HasSubst (uncurry ![V 0, fun j ↦ (F.toPowerSeries j).subst (uncurry ![V 1, V 2])]) :=
  (HasSubst.curry_X 0).pair (F.hasSubst_subst_pair (.curry_X 1) (.curry_X 2))

omit [DecidableEq I] in
private theorem subst_pair_subst {τ υ : Type*} (f : MvPowerSeries (Fin 2 × I) R)
    (x y : I → MvPowerSeries τ R) {a : τ → MvPowerSeries υ R}
    (hxy : HasSubst (uncurry ![x, y])) (ha : HasSubst a) :
    (f.subst (uncurry ![x, y])).subst a =
      f.subst (uncurry ![fun i ↦ (x i).subst a, fun i ↦ (y i).subst a]) := by
  rw [subst_comp_subst_apply hxy ha]
  congr 1
  funext ⟨b, i⟩
  fin_cases b <;> rfl

/-- Associativity after substituting three substitutable families. -/
theorem assoc_subst {τ : Type*} {x y z : I → MvPowerSeries τ R}
    (hx : HasSubst x) (hy : HasSubst y) (hz : HasSubst z) (i : I) :
    (F.toPowerSeries i).subst
        (uncurry ![fun j ↦ (F.toPowerSeries j).subst (uncurry ![x, y]), z]) =
      (F.toPowerSeries i).subst
        (uncurry ![x, fun j ↦ (F.toPowerSeries j).subst (uncurry ![y, z])]) := by
  let a : Fin 3 × I → MvPowerSeries τ R := uncurry ![x, y, z]
  have ha : HasSubst a := HasSubst.uncurry fun b ↦ by fin_cases b <;> assumption
  have hv (b : Fin 3) := HasSubst.curry_X (R := R) (σ := I) b
  have hX (b : Fin 3) : (fun j ↦ (curry X b j : MvPowerSeries (Fin 3 × I) R).subst a) =
      ![x, y, z] b := by
    funext j
    simp [subst_X ha, a]
  have hF (b c : Fin 3) : (fun j ↦ ((F.toPowerSeries j).subst
      (uncurry ![curry X b, curry X c] : Fin 2 × I → MvPowerSeries (Fin 3 × I) R)).subst a) =
      fun j ↦ (F.toPowerSeries j).subst (uncurry ![![x, y, z] b, ![x, y, z] c]) := by
    funext j
    rw [subst_pair_subst _ _ _ ((hv b).pair (hv c)) ha, hX, hX]
  have h := congrArg (subst a) (F.assoc i)
  rw [subst_pair_subst _ _ _ F.hasSubst_assoc_left ha,
    subst_pair_subst _ _ _ F.hasSubst_assoc_right ha, hF, hF, hX, hX] at h
  simpa using h

/-! ### The identity -/

/-- `F(x, y) ≡ x + y` modulo terms of total degree at least two. -/
theorem two_le_order_subst_sub {τ : Type*} {x y : I → MvPowerSeries τ R}
    (hx : HasSubst x) (hy : HasSubst y) (hx0 : ∀ i, constantCoeff (x i) = 0)
    (hy0 : ∀ i, constantCoeff (y i) = 0) (i : I) :
    (2 : ℕ∞) ≤ ((F.toPowerSeries i).subst (uncurry ![x, y]) - (x i + y i)).order := by
  have hp := hx.pair hy
  have hp0 : ∀ s, constantCoeff (uncurry ![x, y] s) = 0 := by
    rintro ⟨b, j⟩; fin_cases b <;> simp [hx0, hy0]
  have h := succ_le_order_subst_sub (n := 1)
    (f := F.toPowerSeries i - (X (0, i) + X (1, i))) hp HasSubst.zero' hp0 (fun _ ↦ by simp)
    (fun s ↦ by simpa using one_le_order_iff_constCoeff_eq_zero.mpr (hp0 s))
    (fun s _ ↦ by
      rw [map_sub, F.coeff_eq_of_degree_lt_two i (d := single s 1) (by simp), sub_self])
  rw [subst_zero_of_constantCoeff_zero (by simp [F.zero_constantCoeff]), sub_zero,
    subst_sub hp, subst_add hp, subst_X hp, subst_X hp] at h
  simpa using h

/-- The family of series `F(X, 0)`. -/
abbrev Xzero : I → MvPowerSeries I R := fun i ↦ (F.toPowerSeries i).subst (uncurry ![X, 0])

/-- The family of series `F(0, X)`. -/
abbrev zeroX : I → MvPowerSeries I R := fun i ↦ (F.toPowerSeries i).subst (uncurry ![0, X])

theorem Xzero_subst_Xzero (i : I) : (F.Xzero i).subst F.Xzero = F.Xzero i := by
  have hs : HasSubst F.Xzero := F.hasSubst_subst_pair .X_self .zero'
  rw [Xzero, subst_pair_subst _ _ _ (HasSubst.X_self.pair .zero') hs]
  have h00 : uncurry ![(0 : I → MvPowerSeries I R), 0] = 0 := by
    funext ⟨b, j⟩; fin_cases b <;> rfl
  simpa only [h00, subst_zero_of_constantCoeff_zero (F.zero_constantCoeff _),
    Pi.zero_apply, ← substAlgHom_apply hs, map_zero, substAlgHom_X,
    Xzero, ← Pi.zero_def] using F.assoc_subst .X_self .zero' .zero' i

theorem zeroX_subst_zeroX (i : I) : (F.zeroX i).subst F.zeroX = F.zeroX i := by
  have hs : HasSubst F.zeroX := F.hasSubst_subst_pair .zero' .X_self
  rw [zeroX, subst_pair_subst _ _ _ (HasSubst.zero'.pair .X_self) hs]
  have h00 : uncurry ![(0 : I → MvPowerSeries I R), 0] = 0 := by
    funext ⟨b, j⟩; fin_cases b <;> rfl
  simpa only [h00, subst_zero_of_constantCoeff_zero (F.zero_constantCoeff _),
    Pi.zero_apply, ← substAlgHom_apply hs, map_zero, substAlgHom_X,
    zeroX, ← Pi.zero_def] using (F.assoc_subst .zero' .zero' .X_self i).symm

omit [DecidableEq I] in
/-- An idempotent family congruent to `X` modulo degree two is `X`. -/
private theorem eq_X_of_idempotent (g : I → MvPowerSeries I R) (hg : HasSubst g)
    (hg0 : ∀ i, constantCoeff (g i) = 0) (hlin : ∀ i, (2 : ℕ∞) ≤ (g i - X i).order)
    (hgg : ∀ i, (g i).subst g = g i) : g = X := by
  have h (n : ℕ) : ∀ i, (n : ℕ∞) ≤ (g i - X i).order := by
    induction n with
    | zero => simp
    | succ n ih =>
      intro i
      have hf : ∀ s, g s ≠ X s → coeff (single s 1) (g i - X i) = 0 := fun s _ ↦ by
        have hs : (((single s 1 : I →₀ ℕ).degree : ℕ) : ℕ∞) < 2 := by simp
        exact coeff_of_lt_order (hs.trans_le (hlin i))
      have := succ_le_order_subst_sub hg HasSubst.X_self hg0 (fun s ↦ constantCoeff_X s) ih hf
      rwa [subst_sub hg, hgg, subst_X hg, sub_self, subst_self, id_eq, zero_sub,
        order_neg] at this
  funext i
  ext d
  exact coeff_eq_of_le_order_sub (h _ i) (lt_add_one _)

/-- Zero is a right identity: `F(X, 0) = X`. -/
@[simp]
theorem Xzero_eq_X (i : I) : F.Xzero i = X i := by
  refine congrFun (eq_X_of_idempotent F.Xzero (F.hasSubst_subst_pair .X_self .zero')
    (fun j ↦ ?_) (fun j ↦ ?_) F.Xzero_subst_Xzero) i
  · exact constantCoeff_subst_eq_zero (HasSubst.X_self.pair .zero')
      (by rintro ⟨b, k⟩; fin_cases b <;> simp) (F.zero_constantCoeff j)
  · simpa using F.two_le_order_subst_sub .X_self .zero' (fun k ↦ constantCoeff_X k) (by simp) j

/-- Zero is a left identity: `F(0, X) = X`. -/
@[simp]
theorem zeroX_eq_X (i : I) : F.zeroX i = X i := by
  refine congrFun (eq_X_of_idempotent F.zeroX (F.hasSubst_subst_pair .zero' .X_self)
    (fun j ↦ ?_) (fun j ↦ ?_) F.zeroX_subst_zeroX) i
  · exact constantCoeff_subst_eq_zero (HasSubst.zero'.pair .X_self)
      (by rintro ⟨b, k⟩; fin_cases b <;> simp) (F.zero_constantCoeff j)
  · simpa using F.two_le_order_subst_sub .zero' .X_self (by simp) (fun k ↦ constantCoeff_X k) j

/-- Zero is a right identity after any admissible substitution. -/
@[simp]
theorem add_zero {τ : Type*} {a : I → MvPowerSeries τ R} (ha : HasSubst a) (i : I) :
    (F.toPowerSeries i).subst (uncurry ![a, 0]) = a i := by
  have h := congrArg (subst a) (F.Xzero_eq_X i)
  rw [Xzero, subst_pair_subst _ _ _ (HasSubst.X_self.pair .zero') ha] at h
  simpa only [Pi.zero_apply, ← substAlgHom_apply ha, map_zero, substAlgHom_X,
    ← Pi.zero_def] using h

/-- Zero is a left identity after any admissible substitution. -/
@[simp]
theorem zero_add {τ : Type*} {a : I → MvPowerSeries τ R} (ha : HasSubst a) (i : I) :
    (F.toPowerSeries i).subst (uncurry ![0, a]) = a i := by
  have h := congrArg (subst a) (F.zeroX_eq_X i)
  rw [zeroX, subst_pair_subst _ _ _ (HasSubst.zero'.pair .X_self) ha] at h
  simpa only [Pi.zero_apply, ← substAlgHom_apply ha, map_zero, substAlgHom_X,
    ← Pi.zero_def] using h

end Basic

/-! ### The inverse

The inverse is the solution `α` of `F(α(X), X) = 0` given by the formal implicit function
theorem for infinitely many equations, `MvPowerSeries.existsUnique_implicitFunctionLeftCofinite`.
Its hypotheses hold: (9.6.3) is `HasSubst F`, and the Jacobian in the first variable block is
the identity matrix. -/

section Inverse

/-- Identify the two blocks of variables with a disjoint sum. -/
private def sumVarsEquiv (I : Type*) : (Fin 2 × I) ≃ (I ⊕ I) where
  toFun p := if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
  invFun := Sum.elim (fun i ↦ (0, i)) (fun i ↦ (1, i))
  left_inv := by rintro ⟨b, i⟩; fin_cases b <;> simp
  right_inv := by rintro (i | i) <;> simp

variable (F : InfDimFormalGroup I R)

/-- The group law with variables indexed by `I ⊕ I`. -/
private def toSumPowerSeries (i : I) : MvPowerSeries (I ⊕ I) R :=
  rename (sumVarsEquiv I) (F.toPowerSeries i)

private theorem constantCoeff_toSumPowerSeries (i : I) :
    constantCoeff (F.toSumPowerSeries i) = 0 := by
  simpa only [toSumPowerSeries, constantCoeff_rename] using F.zero_constantCoeff i

private theorem hasSubst_toSumPowerSeries : HasSubst F.toSumPowerSeries := by
  have h : F.toSumPowerSeries = fun i ↦ (F.toPowerSeries i).subst (X ∘ sumVarsEquiv I) :=
    funext fun i ↦ rename_eq_subst _ _
  rw [h]
  exact F.hasSubst.subst (HasSubst.X_comp _)

private theorem implicitJacobianLeft_toSumPowerSeries :
    implicitJacobianLeft F.toSumPowerSeries = 1 := by
  ext i j
  have h : coeff (single (Sum.inl j) 1) (F.toSumPowerSeries i) =
      coeff (single (0, j) 1) (F.toPowerSeries i) := by
    simpa [sumVarsEquiv, toSumPowerSeries] using
      coeff_embDomain_rename (sumVarsEquiv I).toEmbedding (F.toPowerSeries i) (single (0, j) 1)
  change coeff (single (Sum.inl j) 1) (F.toSumPowerSeries i) = _
  rw [h, F.lin_coeff_X]
  simp [Matrix.one_apply, eq_comm]

private theorem isCofiniteInverse_one :
    IsCofiniteInverse 1 (implicitJacobianLeft F.toSumPowerSeries) := by
  rw [implicitJacobianLeft_toSumPowerSeries]
  exact .one

private theorem subst_toSumPowerSeries {a b : I → MvPowerSeries I R} (ha : HasSubst a)
    (hb : HasSubst b) (i : I) :
    (F.toSumPowerSeries i).subst (Sum.elim a b) = (F.toPowerSeries i).subst (uncurry ![a, b]) := by
  have hs := ha.sumElim hb
  rw [toSumPowerSeries, rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) hs]
  congr 1
  funext ⟨k, j⟩
  fin_cases k <;> simp [subst_X hs, sumVarsEquiv]

/-- The formal inverse `i(X)`, the unique substitutable solution of `F(i(X), X) = 0` with zero
constant terms. -/
@[no_expose]
def inv : I → MvPowerSeries I R :=
  implicitFunctionLeftCofinite F.toSumPowerSeries 1

@[simp]
theorem constantCoeff_inv (i : I) : constantCoeff (F.inv i) = 0 :=
  constantCoeff_implicitFunctionLeftCofinite F.constantCoeff_toSumPowerSeries
    F.hasSubst_toSumPowerSeries F.isCofiniteInverse_one i

/-- The inverse satisfies the cofinite condition, so it can be substituted. -/
theorem hasSubst_inv : HasSubst F.inv :=
  hasSubst_implicitFunctionLeftCofinite F.constantCoeff_toSumPowerSeries
    F.hasSubst_toSumPowerSeries F.isCofiniteInverse_one

/-- The inverse is a left inverse: `F(i(X), X) = 0`. -/
@[simp]
theorem inv_left (i : I) : (F.toPowerSeries i).subst (uncurry ![F.inv, X]) = 0 := by
  rw [← F.subst_toSumPowerSeries F.hasSubst_inv .X_self]
  exact subst_implicitFunctionLeftCofinite F.constantCoeff_toSumPowerSeries
    F.hasSubst_toSumPowerSeries F.isCofiniteInverse_one i

/-- Any substitutable left inverse with zero constant terms is `F.inv`. -/
theorem eq_inv (a : I → MvPowerSeries I R) (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0)
    (h : ∀ i, (F.toPowerSeries i).subst (uncurry ![a, X]) = 0) : a = F.inv :=
  eq_implicitFunctionLeftCofinite F.constantCoeff_toSumPowerSeries F.hasSubst_toSumPowerSeries
    F.isCofiniteInverse_one a ha ha0 fun i ↦ (F.subst_toSumPowerSeries ha .X_self i).trans (h i)

/-- The left inverse equation after any admissible substitution: `F(i(a), a) = 0`. -/
@[simp]
theorem inv_left_subst {τ : Type*} {a : I → MvPowerSeries τ R} (ha : HasSubst a) (i : I) :
    (F.toPowerSeries i).subst (uncurry ![fun j ↦ (F.inv j).subst a, a]) = 0 := by
  have h := congrArg (subst a) (F.inv_left i)
  rw [subst_pair_subst _ _ _ (F.hasSubst_inv.pair .X_self) ha] at h
  simpa only [subst_X ha, ← substAlgHom_apply ha, map_zero] using h

/-- Applying the inverse twice gives the identity: `i(i(X)) = X`. -/
@[simp]
theorem inv_subst_inv (i : I) : (F.inv i).subst F.inv = X i := by
  have hj : HasSubst fun k ↦ (F.inv k).subst F.inv := F.hasSubst_inv.subst F.hasSubst_inv
  have h := F.assoc_subst hj F.hasSubst_inv .X_self i
  simp only [F.inv_left_subst F.hasSubst_inv, F.inv_left, ← Pi.zero_def] at h
  rw [F.zero_add .X_self, F.add_zero hj] at h
  exact h.symm

/-- The inverse is also a right inverse: `F(X, i(X)) = 0`. -/
@[simp]
theorem inv_right (i : I) : (F.toPowerSeries i).subst (uncurry ![X, F.inv]) = 0 := by
  simpa only [inv_subst_inv] using F.inv_left_subst F.hasSubst_inv i

end Inverse

omit [DecidableEq I] in
/-- Substituting `(x, y)` into `Xᵢ + Yᵢ` gives `xᵢ + yᵢ`. -/
private theorem subst_X_add_X {τ : Type*} {x y : I → MvPowerSeries τ R}
    (hx : HasSubst x) (hy : HasSubst y) (i : I) :
    (X (0, i) + X (1, i) : MvPowerSeries (Fin 2 × I) R).subst (uncurry ![x, y]) = x i + y i := by
  simp [subst_add (hx.pair hy), subst_X (hx.pair hy)]

/-- The additive formal group law `F(i)(X, Y) = Xᵢ + Yᵢ`. -/
def additive (I : Type*) (R : Type*) [CommRing R] [DecidableEq I] : InfDimFormalGroup I R where
  toPowerSeries i := X (0, i) + X (1, i)
  zero_constantCoeff _ := by simp
  lin_coeff_X i j := by simp [coeff_index_single_X]
  lin_coeff_Y i j := by simp [coeff_index_single_X]
  coeff_finite d := ((HasSubst.curry_X (R := R) (σ := I) 0).add (.curry_X 1)).coeff_zero d
  assoc i := by
    have hv (b : Fin 3) := HasSubst.curry_X (R := R) (σ := I) b
    simp only [subst_X_add_X (hv _) (hv _)]
    rw [subst_X_add_X (x := fun j ↦ curry X 0 j + curry X 1 j) ((hv 0).add (hv 1)) (hv 2),
      subst_X_add_X (y := fun j ↦ curry X 1 j + curry X 2 j) (hv 0) ((hv 1).add (hv 2)),
      add_assoc]

instance : (additive I R).IsComm where
  comm i := by
    change X (0, i) + X (1, i) = (X (0, i) + X (1, i) : MvPowerSeries (Fin 2 × I) R).subst _
    rw [subst_X_add_X (.curry_X 1) (.curry_X 0)]
    simp [add_comm]

/-- The inverse of the additive formal group law is coordinatewise negation. -/
@[simp]
theorem inv_additive (i : I) : (additive I R).inv i = -X i := by
  refine (congrFun ((additive I R).eq_inv (-X) HasSubst.X_self.neg (by simp) fun j ↦ ?_) i).symm
  change (X (0, j) + X (1, j) : MvPowerSeries (Fin 2 × I) R).subst _ = 0
  rw [subst_X_add_X HasSubst.X_self.neg .X_self]
  simp

section Finite

variable {σ : Type*} [Finite σ] [DecidableEq σ]

/-- For a finite index set, condition (9.6.3) is automatic, so formal group laws in the
sense of (9.6.1) are exactly `MvFormalGroup σ R`. -/
def equivMvFormalGroup : InfDimFormalGroup σ R ≃ MvFormalGroup σ R where
  toFun F := ⟨F.toPowerSeries, F.zero_constantCoeff, F.lin_coeff_X, F.lin_coeff_Y, F.assoc⟩
  invFun F := ⟨F.toPowerSeries, F.zero_constantCoeff, F.lin_coeff_X, F.lin_coeff_Y,
    fun _ ↦ Set.toFinite _, F.assoc⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem toPowerSeries_equivMvFormalGroup (F : InfDimFormalGroup σ R) :
    (equivMvFormalGroup F).toPowerSeries = F.toPowerSeries := rfl

@[simp]
theorem toPowerSeries_equivMvFormalGroup_symm (F : MvFormalGroup σ R) :
    (equivMvFormalGroup.symm F).toPowerSeries = F.toPowerSeries := rfl

/-- The comparison preserves commutativity. -/
theorem isComm_equivMvFormalGroup_iff (F : InfDimFormalGroup σ R) :
    (equivMvFormalGroup F).IsComm ↔ F.IsComm :=
  ⟨fun h ↦ ⟨h.comm⟩, fun h ↦ ⟨h.comm⟩⟩

/-- For a finite index set, the inverse agrees with `MvFormalGroup.inv`. -/
@[simp]
theorem inv_equivMvFormalGroup (F : InfDimFormalGroup σ R) :
    (equivMvFormalGroup F).inv = F.inv :=
  (MvFormalGroup.eq_inv _ F.inv F.constantCoeff_inv F.inv_left).symm

/-- The comparison sends the additive formal group law to the additive formal group law. -/
@[simp]
theorem equivMvFormalGroup_additive :
    equivMvFormalGroup (additive σ R) = MvFormalGroup.additive σ R := rfl

end Finite

end InfDimFormalGroup
