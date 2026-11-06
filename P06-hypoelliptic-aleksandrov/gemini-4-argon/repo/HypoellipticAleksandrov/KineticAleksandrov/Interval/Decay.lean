module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.DecayFrequency
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.DecayMass
import HypoellipticAleksandrov.KineticAleksandrov.Interval.BlockScaling
import HypoellipticAleksandrov.KineticAleksandrov.Interval.DecayBlocks

/-! # Combined kinetic Fourier decay on bounded intervals

Frequency decay on the first half and killing decay on the second half give the
source rate `1 + |ξ|^(2/3)`. Constants are chosen before the interval position,
coefficients, query times, starting velocity, and frequency.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

/- Real bounds for the two factors imply a real product bound for composition. -/
theorem interval_composition_real_bound {a c F G }
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (hcomp : K.HasComposition hJ)
    (hcov : IsTranslationCovariantEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ K)
    (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ) (ξ : PDE.Vec 1)
    (v ) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hhead : TV (intervalFourierKernel K σ r hσr ξ v) ≤ F)
    (htail : ∀ w : PDE.oneDimensionalAxisBox a c,
      TV (intervalFourierKernel K r τ hrτ ξ w) ≤ G) :
    TV (intervalFourierKernel K σ τ (hσr.trans hrτ) ξ v) ≤ F * G := by
  have hfinite : ∀ s t hst w,
      totalVariationNorm (intervalFourierKernel K s t hst ξ w) ≠ ⊤ :=
    fun s t hst w => ne_of_lt
      ((intervalFourierKernel_totalVariation_le_one K s t hst ξ w).trans_lt
        ENNReal.one_lt_top)
  have hhead' : totalVariationNorm (intervalFourierKernel K σ r hσr ξ v) ≤
      ENNReal.ofReal F := by
    rw [← ENNReal.ofReal_toReal (hfinite σ r hσr v)]
    exact ENNReal.ofReal_le_ofReal hhead
  have htail' : (⨆ w : PDE.oneDimensionalAxisBox a c,
      totalVariationNorm (intervalFourierKernel K r τ hrτ ξ w)) ≤ ENNReal.ofReal G := by
    apply iSup_le
    intro w
    rw [← ENNReal.ofReal_toReal (hfinite r τ hrτ w)]
    exact ENNReal.ofReal_le_ofReal (htail w)
  have h := (intervalFourierKernel_totalVariation_composition K hJ hcomp hcov
    σ r τ hσr hrτ ξ v).trans (mul_le_mul' hhead' htail')
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hF,
    ENNReal.toReal_ofReal hG] using ht

/- The case-I decay estimate, conditional only on Hörmander's theorem and Lieberman's Theorem 5.14.
-/
end HypoellipticAleksandrov.KineticAleksandrov.Interval
