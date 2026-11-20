module

public import PDEFoundation.Sobolev.OneDimensional.PrimitiveWeakIdentity
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativePrimitiveIntegrable
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Tactic

/-! # The actual distributional derivative of a weighted measure primitive -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The primitive based at zero has exactly the weighted measure as its distributional
derivative. -/
theorem bellmanMeasurePrimitive_weak (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (g : ℝ → ℝ) (hg : Continuous g) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ) :
    (∫ x, bellmanMeasurePrimitive μ g 0 x * deriv φ x) = -∫ x, g x * φ x ∂μ := 
  PDE.intervalIntegral_weak_identity μ hg.locallyIntegrable
    (bellmanMeasurePrimitive_locallyIntegrable μ g hg) (hφ.of_le (by simp)) hcφ

end HypoellipticAleksandrov.KineticAleksandrov
