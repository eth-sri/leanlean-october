module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaSecondDerivative
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Inverting the derivative of an actual approximate model phase

All inverse identities are restricted to the derivative image of (1,2).
No global derivative at the endpoints, nor any dual exponential-sum estimate,
is assumed. The small-error model hypothesis supplies strict negative curvature.
-/

noncomputable section

open Set Expdb Filter
open scoped Topology ContDiff

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

def modelPhaseSlopeRange (F : ℝ → ℝ) : Set ℝ :=
  deriv F '' Ioo (1 : ℝ) 2

def modelPhaseInverseSlope (F : ℝ → ℝ) : ℝ → ℝ :=
  Function.invFunOn (deriv F) (Ioo (1 : ℝ) 2)

section
variable {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ} (hF : IsApproximateModelPhaseFunction F σ P δ) {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2)
include σ δ P F hF u hu
theorem approximateModelPhase_contDiffAt :
    ContDiffAt ℝ ∞ F u :=
  hF.1.contDiffAt (Icc_mem_nhds hu.1 hu.2)

theorem approximateModelPhase_deriv_contDiffAt :
    ContDiffAt ℝ ∞ (deriv F) u := by
  exact (approximateModelPhase_contDiffAt hF hu).derivWithin (by simp)
end

theorem approximateModelPhase_deriv_strictAntiOn {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) :
    StrictAntiOn (deriv F) (Ioo (1 : ℝ) 2) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 1 2)
  · exact fun u hu =>
      (approximateModelPhase_deriv_contDiffAt hF hu).continuousAt.continuousWithinAt
  · intro u hu
    pm_5928 hui u
    pm_7386 hui

section
variable {F : ℝ → ℝ} {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F)
include F v hv
theorem modelPhaseInverseSlope_mem :
    modelPhaseInverseSlope F v ∈ Ioo (1 : ℝ) 2 :=
  Function.invFunOn_mem hv

theorem deriv_modelPhaseInverseSlope_apply :
    deriv F (modelPhaseInverseSlope F v) = v :=
  Function.invFunOn_eq hv
end

section
variable {σ δ : ℝ} {F : ℝ → ℝ} (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1) (hF : IsApproximateModelPhaseFunction F σ 1 δ)
include σ δ F hσ hδ hF
theorem modelPhaseInverseSlope_deriv
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseInverseSlope F (deriv F u) = u :=
  (approximateModelPhase_deriv_strictAntiOn hσ hδ hF).injOn.leftInvOn_invFunOn hu

theorem approximateModelPhase_secondDeriv_ne_zero
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    deriv (deriv F) u ≠ 0 := by
  pm_7386 hu

theorem modelPhaseInverseSlope_hasStrictDerivAt
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    HasStrictDerivAt (modelPhaseInverseSlope F)
      (deriv (deriv F) (modelPhaseInverseSlope F v))⁻¹ v := by
  rcases hv with ⟨u, hu, rfl⟩
  rw [modelPhaseInverseSlope_deriv hσ hδ hF hu]
  have hd := (approximateModelPhase_deriv_contDiffAt hF hu).hasStrictDerivAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  apply hd.to_local_left_inverse (approximateModelPhase_secondDeriv_ne_zero hσ hδ hF hu)
  filter_upwards [isOpen_Ioo.mem_nhds hu] with x hx
  exact modelPhaseInverseSlope_deriv hσ hδ hF hx

theorem modelPhaseSlopeRange_isOpen :
    IsOpen (modelPhaseSlopeRange F) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro v ⟨u, hu, rfl⟩
  have hd := (approximateModelPhase_deriv_contDiffAt hF hu).hasStrictDerivAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hi := Filter.image_mem_map (m := deriv F) (isOpen_Ioo.mem_nhds hu)
  rwa [hd.map_nhds_eq (approximateModelPhase_secondDeriv_ne_zero hσ hδ hF hu)] at hi

theorem modelPhaseInverseSlope_contDiffAt
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    ContDiffAt ℝ ∞ (modelPhaseInverseSlope F) v := by
  rcases hv with ⟨u, hu, rfl⟩
  have hc := approximateModelPhase_deriv_contDiffAt hF hu
  have hd := hc.hasStrictDerivAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have he := hd.hasStrictFDerivAt_equiv
    (approximateModelPhase_secondDeriv_ne_zero hσ hδ hF hu)
  have hg : ∀ᶠ x in 𝓝 u, modelPhaseInverseSlope F (deriv F x) = x := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with x hx
    exact modelPhaseInverseSlope_deriv hσ hδ hF hx
  pm_881
end

end TaoTrudgianYang2025
