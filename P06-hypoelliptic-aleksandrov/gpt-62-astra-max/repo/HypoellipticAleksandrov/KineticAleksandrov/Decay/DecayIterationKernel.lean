module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernelsVariation
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
import Mathlib.Tactic.Linarith

/-! # Natural block iteration of the Fourier composition bound -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

variable {d : ℕ} (K : MovingFiberKernel (wholeSpace d) stationary)
    (hcomp : K.HasComposition MeasurableSet.univ)
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) stationary MeasurableSet.univ K)
    (ξ : PDE.Vec d) {T c : ℝ} (hT : 0 < T) (hc : 0 ≤ c)
    (hstep : ∀ (s : ℝ) (v : PDE.Vec d),
      totalVariationNorm (fourierKernel K s (s + T) (le_add_of_nonneg_right hT.le) ξ v) ≤
        ENNReal.ofReal c)
    (k : ℕ) (σ τ : ℝ) (hστ : σ ≤ τ)

/-- A characterized Fourier measure at a whole-space query is the canonical Fourier kernel. -/
theorem iteration_projection_eq
    (v ξ : PDE.Vec d) (q : EvolutionQuery (wholeSpace d) stationary)
    (hq : q.1 = (σ, τ, v, 0)) (ν : ComplexMeasure (PDE.Vec d))
    (hν : IsFourierProjection K q ξ ν) : ν = fourierKernel K σ τ hστ ξ v := by
  have he : q = wholeSpaceQuery σ τ hστ v 0 := Subtype.ext hq
  subst q
  apply VectorMeasure.ext
  intro E hE
  exact (hν E hE).trans ((fourierKernel_spec K σ τ hστ ξ v E hE).symm)

include hcomp hcov hc hstep in
/-- Each full block contributes its contraction; the leftover interval contributes at most one. -/
theorem fourier_natural_block_iteration
    (hk : (k : ℝ) * T ≤ τ - σ) (v : PDE.Vec d) :
    totalVariationNorm (fourierKernel K σ τ hστ ξ v) ≤ ENNReal.ofReal c ^ k := by
  induction k generalizing σ τ v with
  | zero => exact fourierKernel_totalVariation_le_one K σ τ hστ ξ v
  | succ k ih =>
    let r := σ + T
    have hσr : σ ≤ r := le_add_of_nonneg_right hT.le
    have hrτ : r ≤ τ := by
      have hn : 0 ≤ k := Nat.cast_nonneg k
      rw [Nat.cast_succ] at hk
      nlinarith only [hk, hT, hn]
    have hremain : k * T ≤ τ - r := by
      rw [Nat.cast_succ] at hk
      linarith
    calc
      _ ≤ totalVariationNorm (fourierKernel K σ r hσr ξ v) *
          ⨆ w : PDE.Vec d, totalVariationNorm (fourierKernel K r τ hrτ ξ w) :=
        fourierKernel_totalVariation_composition K hcomp hcov σ r τ hσr hrτ ξ v
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal c ^ k := mul_le_mul' (hstep σ v) (iSup_le fun w => ih r τ hrτ hremain w)
      _ = ENNReal.ofReal c ^ (k + 1) := by rw [pow_succ, mul_comm]

end HypoellipticAleksandrov.KineticAleksandrov.Decay
