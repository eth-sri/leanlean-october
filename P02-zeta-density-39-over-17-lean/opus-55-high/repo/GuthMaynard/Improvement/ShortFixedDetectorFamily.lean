module
public import GuthMaynard.Improvement.ShortDetectorBlockExpansion
public import GuthMaynard.Improvement.ShortDetectorFamilyScales
public import MathCollab.Density.FixedDetectorCover
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Filter MathCollab.Density
open scoped Topology
noncomputable section
namespace GuthMaynard.Improvement

/-- This finite set depends on T alone, before any zero is selected. -/
def fixedShortDetectorIndices (T : ℝ) : Finset (ℕ × ℕ) :=
  (Finset.range (shortDetectorDyadicCount T)).product (Finset.range (detectorTaylorCutoff T+1))

section
variable {T : ℝ}
include T
theorem fixedShortDetectorIndices_card_le
    (hlog : 0 ≤ Real.log T)
    (hD : (shortDetectorDyadicCount T : ℝ) ≤ 5*Real.log T)
    (hJ : (detectorTaylorCutoff T+1 : ℝ) ≤ 12*Real.log T) :
    ((fixedShortDetectorIndices T).card : ℝ) ≤ 60*(Real.log T)^2 := by pm_4319 shortDetectorDyadicCount fixedShortDetectorIndices

/-- Quantitative tail control at the actual family cutoff. -/
theorem norm_fixedShortDetector_tail_le {N : ℕ} {ρ : ℂ}
    (hT : 1 ≤ T) (hN : 0 < N) (hN' : (N : ℝ) ≤ T^2)
    (hβ : 0 ≤ ρ.re) (hβ' : ρ.re ≤ 1) :
    ‖∑' j : ℕ, (detectorTaylorWeight ρ.re (j+(detectorTaylorCutoff T+1)) : ℂ)*
      shortDetectorTaylorPolynomial T N (j+(detectorTaylorCutoff T+1)) ρ.im‖ ≤ 3*T^(-1 : ℝ) := by pm_4320 norm_shortDetectorTaylor_tail_le hTpos

/-- The fixed family has the full block height, up to an absolute constant. -/
theorem exists_fixedShortDetector_component {N : ℕ} {ρ : ℂ}
    (hT : 1 ≤ T) (hN : 0 < N) (hN' : (N : ℝ) ≤ T^2)
    (hβ : 0 ≤ ρ.re) (hβ' : ρ.re ≤ 1)
    (hsmall : 3*T^(-1 : ℝ) ≤ 1/(6*(shortDetectorDyadicCount T : ℝ)))
    (hblock : 1/(3*(shortDetectorDyadicCount T : ℝ)) ≤ ‖shortDetectorBlock ρ T N‖) :
    ∃ j ∈ Finset.range (detectorTaylorCutoff T+1),
      (N : ℝ)^ρ.re/(12*(shortDetectorDyadicCount T : ℝ)) ≤ ‖shortDetectorTaylorPolynomial T N j ρ.im‖ := by pf_40 shortDetectorDyadicCount shortDetectorTaylorPolynomial norm_shortDetectorTaylor_tsum_ge norm_fixedShortDetector_tail_le hasSum_shortDetectorTaylorPolynomial 6 shortDetectorBlock 3 12
end

/-- Actual short finite detection gives a member of a fixed coefficient family.
The family and its logarithmic size are chosen before beta or gamma. -/
theorem shortFiniteDetector_fixed_family_eventually :
    ∀ᶠ T : ℝ in atTop,
      ((fixedShortDetectorIndices T).card : ℝ) ≤ 60*(Real.log T)^2 ∧
      ∀ (σ : ℝ) (ρ : ℂ), 0 ≤ σ → σ ≤ ρ.re → ρ.re ≤ 1 →
        1/3 ≤ ‖shortFiniteDetector ρ T‖ →
        ∃ p ∈ fixedShortDetectorIndices T,
          T^((100:ℝ)⁻¹) < ((2^p.1 : ℕ) : ℝ) ∧
          ((2^p.1 : ℕ) : ℝ) < T^(1/2:ℝ)*(Real.log T)^2 ∧
          ((2^p.1 : ℕ) : ℝ)^σ/(60*Real.log T) ≤
            ‖shortDetectorTaylorPolynomial T (2^p.1) p.2 ρ.im‖ := by
  filter_upwards [short_detector_family_scales_eventually] with T hsc
  pm_6746
  refine ⟨fixedShortDetectorIndices_card_le (by linarith) hD hJ, ?_⟩
  intro σ ρ hσ hσβ hβ' hlarge
  obtain ⟨r, hr, hblock⟩ := exists_short_detector_dyadic_block (by linarith : 1 ≤ T)
    (by norm_num : (0 : ℝ) < 1/3) hlarge
  let N : ℕ := 2^r
  pm_64 hN N
  pm_7669 shortDetectorDyadicCount
  have hb : 1/(3*(shortDetectorDyadicCount T : ℝ)) ≤ ‖shortDetectorBlock ρ T N‖ := by
    convert hblock using 1; ring
  pm_4322 shortDetectorBlock shortDetectorBlock_scale_bounds
  obtain ⟨j, hj, hdetect⟩ := exists_fixedShortDetector_component (by linarith : 1 ≤ T) hN hN'
    (hσ.trans hσβ) hβ' hsmall hb
  pm_4321
  have hden : 12*(shortDetectorDyadicCount T : ℝ) ≤ 60*Real.log T := by linarith
  change (N : ℝ)^σ/(60*Real.log T) ≤ _
  pm_1054

end GuthMaynard.Improvement
