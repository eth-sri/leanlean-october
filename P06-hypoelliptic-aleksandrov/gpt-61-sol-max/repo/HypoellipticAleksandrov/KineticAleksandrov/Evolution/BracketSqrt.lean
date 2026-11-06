module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import PDEFoundation.Ambient.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Smooth positive square root of a smooth positive-definite matrix field

This module proves the standard fact used in the Hörmander bracket check
Proposition 2.1: if `B : E → Mat d` is smooth (entrywise) with every `B p`
positive definite, then `p ↦ CFC.sqrt (B p)` is smooth (entrywise).

The proof is the inverse function theorem for the squaring map `A ↦ A * A` at the
positive-definite matrix `β₀ = √(B p₀)`.  Its derivative `X ↦ β₀ X + X β₀` is injective
(trace argument), hence a continuous linear equivalence in finite dimension.  The local
inverse agrees with `CFC.sqrt ∘ B` near `p₀` because `CFC.sqrt` is continuous on
positive-semidefinite matrices.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution

variable {d : ℕ}

/-- The Sylvester map `X ↦ β X + X β`, the derivative of squaring at `β`. -/
def sylvester (β : PDE.Mat d) : PDE.Mat d →ₗ[ℝ] PDE.Mat d :=
  LinearMap.mulLeft ℝ β + LinearMap.mulRight ℝ β

theorem sylvester_apply (β X : PDE.Mat d) : sylvester β X = β * X + X * β := rfl

/-- The Sylvester map of a positive-definite matrix is injective. -/
theorem sylvester_injective {β : PDE.Mat d} (hβ : β.PosDef) :
    Function.Injective (sylvester β) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro X hX
  rw [sylvester_apply] at hX
  have h1  := hβ.posSemidef.conjTranspose_mul_mul_same X

  have htr : (Xᴴ * β * X).trace + (X * β * Xᴴ).trace = 0 := by
    have : (Xᴴ * (β * X + X * β)).trace = 0 := by rw [hX]; simp
    rw [mul_add, Matrix.trace_add] at this
    rw [Matrix.trace_mul_cycle X β Xᴴ]
    rw [← Matrix.mul_assoc Xᴴ β X] at this
    rw [← Matrix.mul_assoc Xᴴ X β] at this
    exact this



  ext i j
  have := congrFun ((show ∀ y : Fin d → ℝ, X.mulVec y = 0 by
      intro y
      by_contra hy
      have hpos := hβ.dotProduct_mulVec_pos hy
      have h3 : star (X.mulVec y) ⬝ᵥ β.mulVec (X.mulVec y) = 0 := by
        have : star y ⬝ᵥ (Xᴴ * β * X).mulVec y = 0 := by rw [((h1.trace_eq_zero_iff).1 (le_antisymm (by linarith [(hβ.posSemidef.mul_mul_conjTranspose_same X).trace_nonneg]) h1.trace_nonneg))]; simp
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
          Matrix.vecMul_conjTranspose] at this
        exact this
      linarith) (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

/-- The positive square root of a positive-definite matrix is positive definite. -/
theorem posDef_sqrt {B : PDE.Mat d} (hB : B.PosDef) : (CFC.sqrt B).PosDef := by

  rw [(Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg B)).posDef_iff_mulVec_injective]
  intro x y hxy
  apply hB.mulVec_injective

  simpa only [Matrix.mulVec_mulVec, CFC.sqrt_mul_sqrt_self B hB.posSemidef.nonneg] using (congrArg (fun z => (CFC.sqrt B).mulVec z) hxy)

variable {β : PDE.Mat d} (hβ : β.PosDef)

/-- The derivative of squaring at a positive-definite matrix, as a continuous linear
equivalence (finite-dimensional, from injectivity). -/
def sylvesterEquiv  : PDE.Mat d ≃L[ℝ] PDE.Mat d :=
  (LinearEquiv.ofInjectiveEndo (sylvester β) (sylvester_injective hβ)).toContinuousLinearEquiv

theorem sylvesterEquiv_apply  (X : PDE.Mat d) :
    sylvesterEquiv hβ X = β * X + X * β := rfl

theorem hasFDerivAt_matrix_sq  :
    HasFDerivAt (fun A : PDE.Mat d => A * A)
      ((sylvesterEquiv hβ ) : PDE.Mat d →L[ℝ] PDE.Mat d) β := by

  refine ((hasFDerivAt_id (𝕜 := ℝ) β).mul' (hasFDerivAt_id  β)).congr_fderiv ?_
  ext X : 1
  simp [sylvesterEquiv_apply]

open Filter Topology in
/-- Smoothness of `p ↦ √(B p)` at a point, for a smooth positive-definite field `B`,
in the (`L²`-operator) normed structure on matrices. -/
theorem contDiffAt_sqrt_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E → PDE.Mat d) (hB : ContDiff ℝ PDE.smoothOrder B) (hpd : ∀ p, (B p).PosDef) (p₀ : E) :
    ContDiffAt ℝ PDE.smoothOrder (fun p => CFC.sqrt (B p)) p₀ := by
  set β₀ := CFC.sqrt (B p₀) with hβ₀
  have hβpd  := posDef_sqrt (hpd p₀)
  have hsq : β₀ * β₀ = B p₀ := CFC.sqrt_mul_sqrt_self _ (hpd p₀).posSemidef.nonneg
  have hf : ContDiffAt ℝ PDE.smoothOrder (fun A : PDE.Mat d => A * A) β₀ :=
    (contDiff_id.mul contDiff_id).contDiffAt
  have hf' := hasFDerivAt_matrix_sq hβpd

  set g := hf.localInverse hf' (by simp) with hg
  have hg_cd  := hf.to_localInverse hf' (by simp)
  rw [hsq] at hg_cd
  have hcomp  :=
    hg_cd.comp p₀ hB.contDiffAt
  refine hcomp.congr_of_eventuallyEq ?_



  filter_upwards [((show ContinuousAt (fun p => CFC.sqrt (B p)) p₀ by
      have h1 : ContinuousOn (fun p => CFC.sqrt (B p)) Set.univ :=
        (CFC.continuousOn_sqrt (A := PDE.Mat d)).comp hB.continuous.continuousOn
          (fun p _ => (hpd p).posSemidef.nonneg)
      exact h1.continuousAt Filter.univ_mem).eventually ((hf.hasStrictFDerivAt' hf' (by simp)).eventually_left_inverse))] with p hp

  exact (show g (B p) = CFC.sqrt (B p) by
      have h3 := hp
      change g (CFC.sqrt (B p) * CFC.sqrt (B p)) = CFC.sqrt (B p) at h3
      rwa [CFC.sqrt_mul_sqrt_self _ (hpd p).posSemidef.nonneg] at h3).symm

/-- Entrywise smoothness is smoothness for the `L²`-operator normed structure. -/
def matrixCLE (d : ℕ) : (Fin d → Fin d → ℝ) ≃L[ℝ] PDE.Mat d :=
  (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv

variable {E : Type*}

theorem contDiff_matrix_iff  [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E → PDE.Mat d) :
    ContDiff ℝ PDE.smoothOrder B ↔ ∀ i j, ContDiff ℝ PDE.smoothOrder (fun p => B p i j) := by
  constructor
  · intro h i j


    exact contDiff_pi.1 (contDiff_pi.1 ((matrixCLE d).symm.contDiff.comp h) i) j
  · intro h

    exact (matrixCLE d).contDiff.comp (contDiff_pi.2 fun i => contDiff_pi.2 fun j => h i j)

/-- **Smooth positive square root.**  If `B : E → Mat d` is entrywise smooth and every
`B p` is positive definite, then every entry of `p ↦ CFC.sqrt (B p)` is smooth. -/
theorem contDiff_sqrt_entry  [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E → PDE.Mat d) (hB : ∀ i j, ContDiff ℝ PDE.smoothOrder (fun p => B p i j))
    (hpd : ∀ p, (B p).PosDef) (i j : Fin d) :
    ContDiff ℝ PDE.smoothOrder (fun p => CFC.sqrt (B p) i j) := ((contDiff_matrix_iff fun p => CFC.sqrt (B p)).mp
  (contDiff_iff_contDiffAt.mpr (contDiffAt_sqrt_comp B ((contDiff_matrix_iff B).mpr hB) hpd)) i j)

/-- A matrix with `lam • 1 ≤ A` for `0 < lam` is positive definite. -/
theorem posDef_of_smul_one_le {lam : ℝ} (hlam : 0 < lam) {A : PDE.Mat d}
    (h : lam • (1 : PDE.Mat d) ≤ A) : A.PosDef := by


  have := (Matrix.PosDef.one.smul hlam).add_posSemidef (Matrix.le_iff.1 h)
  simpa using this

end HypoellipticAleksandrov.KineticAleksandrov.Evolution
