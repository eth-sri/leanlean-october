module

public import GS.Core

public import Mathlib.Analysis.RCLike.Basic

public import Mathlib.Analysis.Matrix.Normed

public import Mathlib.Analysis.Matrix.PosDef

public import Mathlib.Analysis.CStarAlgebra.Matrix

public import Mathlib.Topology.Algebra.Star.Unitary

public import Mathlib.Analysis.Calculus.ContDiff.Operations

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public import Mathlib.LinearAlgebra.UnitaryGroup

public import Mathlib.Topology.Instances.Matrix

public import Mathlib.Analysis.Normed.Module.FiniteDimension

public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

@[expose] public section

/-! Common real and complex matrix algebra and calculus, in the entrywise matrix topology. -/
noncomputable section
open Matrix ContinuousLinearMap
open scoped BigOperators ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace GS.Shared

abbrev M (𝕜 : Type*) (n : ℕ) := Matrix (Fin n) (Fin n) 𝕜

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

section Unitary
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def Unitary (A : Matrix ι ι 𝕜) : Prop := Aᴴ * A = 1 ∧ A * Aᴴ = 1

theorem Unitary.one : Unitary (1 : Matrix ι ι 𝕜) := one_mem (unitary _)

theorem Unitary.conjTranspose {A : Matrix ι ι 𝕜} (h : Unitary A) : Unitary Aᴴ :=
  _root_.Unitary.star_mem h

theorem Unitary.of_conjTranspose_mul {A : Matrix ι ι 𝕜} (h : Aᴴ * A = 1) : Unitary A :=
  ⟨h, mul_eq_one_comm.mp h⟩

theorem Unitary.mul {A B : Matrix ι ι 𝕜} (hA : Unitary A) (hB : Unitary B) : Unitary (A * B) :=
  (unitary _).mul_mem hA hB

theorem Unitary.isUnit {A : Matrix ι ι 𝕜} (hA : Unitary A) : IsUnit A :=
  IsUnit.of_mul_eq_one _ hA.2

theorem Unitary.adjoint_mul_cancel {A : Matrix ι ι 𝕜} (h : Unitary A) (X : Matrix ι ι 𝕜) :
    Aᴴ * (A * X) = X := by rw [← Matrix.mul_assoc, h.1, Matrix.one_mul]

theorem Unitary.mul_adjoint_cancel {A : Matrix ι ι 𝕜} (h : Unitary A) (X : Matrix ι ι 𝕜) :
    A * (Aᴴ * X) = X := by rw [← Matrix.mul_assoc, h.2, Matrix.one_mul]

end Unitary

def CSupported {ι : Type*} (block : ι → ℕ) (A : Matrix ι ι 𝕜) : Prop :=
  ∀ i j, block i ≠ block j → A i j = 0

namespace CSupported
variable {block : Fin n → ℕ} {A B : M 𝕜 n}

theorem zero : CSupported block (0 : M 𝕜 n) := fun _ _ _ => rfl

theorem one : CSupported block (1 : M 𝕜 n) := fun i j h => Matrix.one_apply_ne (ne_of_apply_ne block h)

theorem add (hA : CSupported block A) (hB : CSupported block B) : CSupported block (A+B) :=
  fun i j h => by simp [hA i j h, hB i j h]

theorem real_smul (r : ℝ) (hA : CSupported block A) : CSupported block (r • A) :=
  fun i j h => by aesop

theorem conjTranspose (hA : CSupported block A) : CSupported block Aᴴ :=
  fun i j h => by aesop

theorem mul (hA : CSupported block A) (hB : CSupported block B) : CSupported block (A * B) := by
  intro i j h
  simp only [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : block i = block k
  · aesop
  · aesop

end CSupported

theorem Unitary.column_norm_sq {A : M 𝕜 n} (hA : Unitary A) (j : Fin n) :
    ∑ k, ‖A k j‖ ^ 2 = 1 := by
  simpa [Matrix.mul_apply, RCLike.star_def, RCLike.conj_mul] using
    congrArg (fun X : M 𝕜 n => RCLike.re (X j j)) hA.1

theorem compact_unitary_of_closed {S : Set (M 𝕜 n)} (hS : IsClosed S)
    (h : ∀ A ∈ S, Unitary A) : IsCompact S := by
  have hbox : IsCompact {A : M 𝕜 n | ∀ i j, A i j ∈ Metric.closedBall (0 : 𝕜) 1} :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_closedBall (0 : 𝕜) 1
  exact hbox.of_isClosed_subset hS fun A hA i j => by
    simpa [Metric.mem_closedBall, dist_zero_right] using entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.mpr (h A hA).1) i j

def IsSkewHermitian (A : M 𝕜 n) : Prop := Aᴴ = -A

theorem skewHermitian_add {A B : M 𝕜 n} (hA : IsSkewHermitian A) (hB : IsSkewHermitian B) :
    IsSkewHermitian (A + B) := by
  change (A+B)ᴴ = _
  rw [Matrix.conjTranspose_add, hA, hB, neg_add]

theorem skewHermitian_real_smul {A : M 𝕜 n} (r : ℝ) (hA : IsSkewHermitian A) :
    IsSkewHermitian (r • A) := by
  change (r • A)ᴴ = _
  rw [Matrix.conjTranspose_smul, star_trivial, hA, smul_neg]

theorem IsSkewHermitian.conjugate {A : M 𝕜 n} (hA : IsSkewHermitian A) (P : M 𝕜 n) :
    IsSkewHermitian (P * A * Pᴴ) := by
  change Aᴴ = -A at hA
  change (P * A * Pᴴ)ᴴ = _
  simp_all [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

def product2 (L P R : M 𝕜 n) := L * P * R

def mulCLM : M 𝕜 n →L[ℝ] M 𝕜 n →L[ℝ] M 𝕜 n :=
  (LinearMap.mul ℝ (M 𝕜 n)).toContinuousBilinearMap

def adjCLM : M 𝕜 n →L[ℝ] M 𝕜 n :=
  (Matrix.conjTransposeLinearEquiv (Fin n) (Fin n) ℝ 𝕜).toLinearMap.toContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[fun_prop] theorem smooth_mul_at {A B : E → M 𝕜 n} {x : E} (hA : ContDiffAt ℝ ⊤ A x) (hB : ContDiffAt ℝ ⊤ B x) :
    ContDiffAt ℝ ⊤ (fun y => A y * B y) x :=
  ((mulCLM (𝕜 := 𝕜) (n := n)).isBoundedBilinearMap.contDiff.contDiffAt).comp x (hA.prodMk hB)

@[fun_prop] theorem smooth_matrix_product {A B : E → M 𝕜 n}
    (hA : ContDiff ℝ ⊤ A) (hB : ContDiff ℝ ⊤ B) : ContDiff ℝ ⊤ (fun x => A x * B x) :=
  contDiff_iff_contDiffAt.mpr fun _ => smooth_mul_at hA.contDiffAt hB.contDiffAt

@[fun_prop] theorem smooth_conjTranspose {A : E → M 𝕜 n} (hA : ContDiff ℝ ⊤ A) :
    ContDiff ℝ ⊤ (fun y => (A y)ᴴ) := (adjCLM (𝕜 := 𝕜) (n := n)).contDiff.comp hA

end GS.Shared
