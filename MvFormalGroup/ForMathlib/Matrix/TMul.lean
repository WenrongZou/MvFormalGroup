module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! ToAdd. -/

@[expose] public section

variable {α} [TopologicalSpace α] [AddCommMonoid α] [Mul α] {l m n : Type*}

/-- The matrix product `(M N)ᵢₖ = ∑' j, Mᵢⱼ Nⱼₖ` for arbitrary index types, with the sum
taken as a `tsum`. For a finite middle index it agrees with `M * N` (`Matrix.tmul_eq_mul`). -/
noncomputable def Matrix.tmul (M : Matrix l m α) (N : Matrix m n α) : Matrix l n α :=
  Matrix.of fun i k => ∑' j, M i j * N j k

@[inherit_doc]
scoped[Matrix] infixl:70 " *ₜ " => Matrix.tmul

open Matrix

theorem Matrix.tmul_eq_mul [Fintype m] (M : Matrix l m α) (N : Matrix m n α) :
    M *ₜ N = M * N := by
  ext i k
  simp [Matrix.tmul, Matrix.mul_apply, tsum_fintype]
