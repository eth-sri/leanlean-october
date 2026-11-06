module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaMorseRemainder
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Smooth zero-extension of the actual transformed source weight

The original cutoff has compact support strictly inside the source interval.
Its image under the actual smooth coordinate is compact inside the Morse
image. This proves smooth extension by zero, including at the moving boundary.
-/

noncomputable section

open Set Expdb Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

def modelPhaseMorseWeight (χ F : ℝ → ℝ) (v : ℝ) : ℝ → ℝ :=
  (modelPhaseMorseRange F v).indicator (modelPhaseMorseAmplitude χ F v)

section
variable {χ F : ℝ → ℝ}
include χ F
theorem modelPhaseMorseWeight_eq {v z : ℝ}
    (hz : z ∈ modelPhaseMorseRange F v) :
    modelPhaseMorseWeight χ F v z = modelPhaseMorseAmplitude χ F v z :=
  Set.indicator_of_mem hz _

theorem modelPhaseMorseWeight_zero_of_not_mem {v z : ℝ}
    (hz : z ∉ modelPhaseMorseRange F v) :
    modelPhaseMorseWeight χ F v z = 0 :=
  Set.indicator_of_notMem hz _

theorem modelPhaseMorseWeight_support_subset {v : ℝ} :
    Function.support (modelPhaseMorseWeight χ F v) ⊆
      modelPhaseMorseCoordinate F v '' tsupport χ := by
  intro z hz
  have hr : z ∈ modelPhaseMorseRange F v := by
    by_contra hn
    exact hz (modelPhaseMorseWeight_zero_of_not_mem hn)
  refine ⟨modelPhaseMorseInverse F v z,?_,modelPhaseMorseCoordinate_inverse hr⟩
  apply subset_tsupport χ
  intro hc
  apply hz
  rw [modelPhaseMorseWeight_eq hr,modelPhaseMorseAmplitude,hc,zero_mul]

theorem isCompact_modelPhaseMorseCoordinate_image_tsupport {σ δ v : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    IsCompact (modelPhaseMorseCoordinate F v '' tsupport χ) := by
  have hc : IsCompact (tsupport χ) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport χ) (hs.trans Ioo_subset_Icc_self)
  exact hc.image_of_continuousOn
    ((modelPhaseMorseCoordinate_contDiffOn hσ hδ hF hv).continuousOn.mono hs)

theorem modelPhaseMorseWeight_tsupport_subset {σ δ v : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    tsupport (modelPhaseMorseWeight χ F v) ⊆
      modelPhaseMorseCoordinate F v '' tsupport χ :=
  closure_minimal modelPhaseMorseWeight_support_subset
    (isCompact_modelPhaseMorseCoordinate_image_tsupport hs hσ hδ hF hv).isClosed

theorem modelPhaseMorseWeight_tsupport_subset_range {σ δ v : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    tsupport (modelPhaseMorseWeight χ F v) ⊆ modelPhaseMorseRange F v :=
  (modelPhaseMorseWeight_tsupport_subset hs hσ hδ hF hv).trans (image_mono hs)

theorem modelPhaseMorseWeight_contDiff {σ δ v : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    ContDiff ℝ ∞ (modelPhaseMorseWeight χ F v) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ modelPhaseMorseRange F v
  · apply (modelPhaseMorseAmplitude_contDiffAt hχ hσ hδ hF hv hz).congr_of_eventuallyEq
    pm_5907 u hu modelPhaseMorseWeight_eq
  · have hn : z ∉ tsupport (modelPhaseMorseWeight χ F v) :=
      fun h => hz (modelPhaseMorseWeight_tsupport_subset_range hs hσ hδ hF hv h)
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hn)
end

end TaoTrudgianYang2025
