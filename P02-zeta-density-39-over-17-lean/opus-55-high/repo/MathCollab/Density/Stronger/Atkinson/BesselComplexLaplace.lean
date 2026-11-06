module
/-
Copyright (c) 2026 S. McColm. Selected literal Y0 Mellin proofs adapted
from DFIComplexLaplace.lean, exact revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
MIT-0. See third_party/twelfth/Y0_MELLIN_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies
retain Apache-2.0 attribution. No Estermann/Voronoi identity is assumed.
-/
public import MathCollab.Density.Stronger.Atkinson.BesselK0Mellin
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import WeylPort.Analytic.ComplexLaplace
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Complex Gamma--Laplace integral for the DFI Neumann kernel

The oscillatory part of Schläfli's representation is handled by Abel
regularization.  This module proves the complex-damping Gamma integral on
the full right half-plane.  The proof differentiates under the integral and
uses analytic continuation from positive real damping parameters.
-/

open Complex Set MeasureTheory Filter
open scoped Topology

noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

export RiemannZeta.GuthMaynard (integrableOn_cpow_mul_cexp_neg_complex_mul_Ioi dfiComplexLaplace_ofReal analyticOnNhd_dfiComplexLaplace dfiComplexLaplace)

section
variable {s a : ℂ} (hs : 0 < s.re) (ha : 0 < a.re)
include s a hs ha
theorem hasDerivAt_dfiComplexLaplace :
    HasDerivAt (dfiComplexLaplace s)
      (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * (-x) * cexp (-(a * x))) a := by
  pm_51
  have hFInt : Integrable (F a) (volume.restrict (Set.Ioi 0)) := by
    simpa only [F] using! integrableOn_cpow_mul_cexp_neg_complex_mul_Ioi hs ha
  pm_50
  have hDiff : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
      ∀ b ∈ Metric.ball a r, HasDerivAt (F · x) (F' b x) b := by
    filter_upwards with x
    intro b _
    simpa [F, F', Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using!
      ((Complex.hasDerivAt_exp (-(b * x))).comp b
        (((hasDerivAt_id b).mul_const (x : ℂ)).neg) |>.const_mul
          ((x : ℂ) ^ (s - 1)))
  pm_52
  aesop

theorem dfiComplexLaplace_eq :
    dfiComplexLaplace s a = a ^ (-s) * Gamma s := by
  pm_54
  have hGDiff : DifferentiableOn ℂ G U := by
    intro b hb
    have hbpos : 0 < b.re := by simpa only [U] using! hb
    pm_771
  pm_53
  have hFreq : ∃ᶠ b : ℂ in 𝓝[≠] (1 : ℂ), F b = G b := by
    pm_55
    · rw [tendsto_nhdsWithin_iff] at hxs ⊢
      constructor
      · simpa using! Complex.continuous_ofReal.continuousAt.tendsto.comp hxs.1
      · simpa using hxs.2
    pm_8303
  pm_56
end

end MathCollab.Density.Stronger.Atkinson
