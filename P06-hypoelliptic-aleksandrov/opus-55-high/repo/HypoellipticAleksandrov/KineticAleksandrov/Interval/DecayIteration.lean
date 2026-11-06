module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.FourierKernelsVariation
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
import Mathlib.Tactic.Linarith

/-! # Natural block iteration of the Fourier composition bound -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

/-- Each full block contributes its contraction; the leftover interval contributes at most one. -/
theorem interval_natural_block_iteration {a b : ℝ}
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a b) stationary)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a b))
    (hcomp : K.HasComposition hJ)
    (hcov : IsTranslationCovariantEvolution (PDE.oneDimensionalAxisBox a b) stationary hJ K)
    (ξ : PDE.Vec 1) {T c : ℝ} (hT : 0 < T) (_hc : 0 ≤ c)
    (hstep : ∀ (s : ℝ) (v : PDE.oneDimensionalAxisBox a b),
      totalVariationNorm (intervalFourierKernel K s (s + T) (le_add_of_nonneg_right hT.le) ξ v) ≤
        ENNReal.ofReal c) (k : ℕ) (σ τ : ℝ) (hστ : σ ≤ τ)
    (hk : (k : ℝ) * T ≤ τ - σ) (v : PDE.oneDimensionalAxisBox a b) :
    totalVariationNorm (intervalFourierKernel K σ τ hστ ξ v) ≤ ENNReal.ofReal c ^ k := by
  induction k generalizing σ τ v with
  | zero => simpa using intervalFourierKernel_totalVariation_le_one K σ τ hστ ξ v
  | succ k ih =>
    let r := σ + T
    have hσr : σ ≤ r := le_add_of_nonneg_right hT.le
    have hrτ : r ≤ τ := by
      have hn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      rw [Nat.cast_succ] at hk
      nlinarith only [hk, hT, hn]
    have hremain : (k : ℝ) * T ≤ τ - r := by
      grind
    have htail : (⨆ w : PDE.oneDimensionalAxisBox a b,
        totalVariationNorm (intervalFourierKernel K r τ hrτ ξ w)) ≤
        ENNReal.ofReal c ^ k :=
      iSup_le fun w => ih r τ hrτ hremain w
    calc
      _ ≤ totalVariationNorm _ *
          ⨆ w : PDE.oneDimensionalAxisBox a b,
            totalVariationNorm _ :=
        intervalFourierKernel_totalVariation_composition K hJ hcomp hcov σ r τ hσr hrτ ξ v
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal c ^ k := mul_le_mul' (hstep σ v) htail
      _ = ENNReal.ofReal c ^ (k + 1) := by ring

end HypoellipticAleksandrov.KineticAleksandrov.Interval
