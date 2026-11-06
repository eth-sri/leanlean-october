module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaMorseMonotonicity
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# The actual smooth inverse of the quadratic coordinate

The inverse is restricted to the coordinate image of (1,2).
Its identities, smoothness and critical Jacobian are proved from the
original model phase and the positive coordinate derivative.
-/

noncomputable section

open Set Expdb Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

def modelPhaseMorseRange (F : ℝ → ℝ) (v : ℝ) : Set ℝ :=
  modelPhaseMorseCoordinate F v '' Ioo (1 : ℝ) 2

def modelPhaseMorseInverse (F : ℝ → ℝ) (v : ℝ) : ℝ → ℝ :=
  Function.invFunOn (modelPhaseMorseCoordinate F v) (Ioo (1 : ℝ) 2)

section
variable {F : ℝ → ℝ}
include F
theorem modelPhaseMorseInverse_mem {v z : ℝ}
    (hz : z ∈ modelPhaseMorseRange F v) :
    modelPhaseMorseInverse F v z ∈ Ioo (1 : ℝ) 2 :=
  Function.invFunOn_mem hz

theorem modelPhaseMorseCoordinate_inverse {v z : ℝ}
    (hz : z ∈ modelPhaseMorseRange F v) :
    modelPhaseMorseCoordinate F v (modelPhaseMorseInverse F v z) = z :=
  Function.invFunOn_eq hz

theorem modelPhaseMorseInverse_coordinate {σ δ v u : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseMorseInverse F v (modelPhaseMorseCoordinate F v u) = u :=
  (modelPhaseMorseCoordinate_strictMonoOn hσ hδ hF hv).injOn.leftInvOn_invFunOn hu

theorem zero_mem_modelPhaseMorseRange {v : ℝ}
    (hv : v ∈ modelPhaseSlopeRange F) :
    0 ∈ modelPhaseMorseRange F v :=
  ⟨modelPhaseInverseSlope F v,modelPhaseInverseSlope_mem hv,
    modelPhaseMorseCoordinate_at_inverse F v⟩

theorem modelPhaseMorseInverse_zero {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    modelPhaseMorseInverse F v 0 = modelPhaseInverseSlope F v := by
  simpa only [modelPhaseMorseCoordinate_at_inverse] using
    modelPhaseMorseInverse_coordinate hσ hδ hF hv (modelPhaseInverseSlope_mem hv)

theorem modelPhaseMorseInverse_hasStrictDerivAt {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) :
    HasStrictDerivAt (modelPhaseMorseInverse F v)
      (deriv (modelPhaseMorseCoordinate F v) (modelPhaseMorseInverse F v z))⁻¹ z := by
  pm_8308
  rw [modelPhaseMorseInverse_coordinate hσ hδ hF hv hu]
  have hd := (modelPhaseMorseCoordinate_contDiffAt hσ hδ hF hv hu).hasStrictDerivAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  apply hd.to_local_left_inverse (modelPhaseMorseCoordinate_deriv_pos hσ hδ hF hv hu).ne'
  pm_5348 modelPhaseMorseInverse_coordinate

theorem modelPhaseMorseRange_isOpen {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    IsOpen (modelPhaseMorseRange F v) := by
  pm_8039
  have hd := (modelPhaseMorseCoordinate_contDiffAt hσ hδ hF hv hu).hasStrictDerivAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hi := Filter.image_mem_map (m := modelPhaseMorseCoordinate F v) (isOpen_Ioo.mem_nhds hu)
  rwa [hd.map_nhds_eq (modelPhaseMorseCoordinate_deriv_pos hσ hδ hF hv hu).ne'] at hi

theorem modelPhaseMorseInverse_contDiffAt {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) :
    ContDiffAt ℝ ∞ (modelPhaseMorseInverse F v) z := by
  pm_8308
  have hc := modelPhaseMorseCoordinate_contDiffAt hσ hδ hF hv hu
  have hd := hc.hasStrictDerivAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have he := hd.hasStrictFDerivAt_equiv (modelPhaseMorseCoordinate_deriv_pos hσ hδ hF hv hu).ne'
  have hg : ∀ᶠ x in 𝓝 u,
      modelPhaseMorseInverse F v (modelPhaseMorseCoordinate F v x) = x := by
    pm_5348 modelPhaseMorseInverse_coordinate
  pm_881

theorem modelPhaseMorseInverse_hasDerivAt_zero {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    HasDerivAt (modelPhaseMorseInverse F v) (modelPhaseStationaryAmplitude F v) 0 := by
  have h := (modelPhaseMorseInverse_hasStrictDerivAt hσ hδ hF hv
    (zero_mem_modelPhaseMorseRange hv)).hasDerivAt
  rwa [modelPhaseMorseInverse_zero hσ hδ hF hv,
    modelPhaseMorseCoordinate_reciprocal_derivative_amplitude hF hv] at h

theorem modelPhaseMorseInverse_quadratic {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) :
    F (modelPhaseMorseInverse F v z)-v*modelPhaseMorseInverse F v z =
      -modelPhaseLegendreDual F v-z^2/2 := by
  simpa only [modelPhaseMorseCoordinate_inverse hz] using
    modelPhaseMorseCoordinate_normalForm hσ hδ hF hv (modelPhaseMorseInverse_mem hz)
end

end TaoTrudgianYang2025
