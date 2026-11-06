module
public import GuthMaynard.Improvement.ShortDetectorNormalization
public import MathCollab.Density.DetectorPoweredHeight
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Real Complex Filter MathCollab.Density
open scoped Topology
noncomputable section
namespace GuthMaynard.Improvement

def shortDetectorHeightConstant : ℝ := 2^100*100*60^100

/-- Explicit height after powering and splitting; all losses are absolute or
logarithmic, and no dependence on beta or the zero enters the coefficients. -/
theorem exists_shortPoweredDetector_height {T σ t : ℝ} {N j k : ℕ}
    (hlog : 1 ≤ Real.log T) (hN : 0 < N) (_hσ : 0 ≤ σ) (hσ' : σ ≤ 1)
    (hk : 0 < k) (hk' : k ≤ 100)
    (hD : (N : ℝ)^σ/(60*Real.log T) ≤ ‖shortDetectorTaylorPolynomial T N j t‖) :
    ∃ ℓ ∈ Finset.range k,
      (((2^ℓ*N^k : ℕ) : ℝ)^σ)/(shortDetectorHeightConstant*(Real.log T)^100) ≤
        ‖detectingPolynomial (2^ℓ*N^k) (shortPoweredDetectorCoefficient T N j k) t‖ := by
  obtain ⟨ℓ, hℓ, hh⟩ := exists_shortPoweredDetector_piece hN hk T t j
  pm_4314
  have hkfour : (k : ℝ) ≤ 100 := by exact_mod_cast hk'
  have hℓthree : ℓ ≤ 100 := by have := Finset.mem_range.mp hℓ; omega
  have htwo : (2 : ℝ)^ℓ ≤ 2^100 := by
    pm_662 hh hℓthree
    norm_num at hh ⊢
    exact hh
  have hscale : (((2^ℓ*N^k : ℕ) : ℝ)^σ) ≤ 2^100*((N : ℝ)^σ)^k := by
    pm_4313
  have hden : (k : ℝ)*(60*Real.log T)^k ≤ 100*60^100*(Real.log T)^100 := by
    have hp := pow_le_pow_right₀ (show (1 : ℝ) ≤ 60*Real.log T by linarith) hk'
    pm_7001
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (N : ℝ)^σ/(60*Real.log T)) hD k
  calc
    _ ≤ (2^100*((N : ℝ)^σ)^k)/(shortDetectorHeightConstant*(Real.log T)^100) :=
      div_le_div_of_nonneg_right hscale (by unfold shortDetectorHeightConstant; positivity)
    _ = ((N : ℝ)^σ)^k/(100*60^100*(Real.log T)^100) := by unfold shortDetectorHeightConstant; ring
    _ ≤ ((N : ℝ)^σ)^k/((k : ℝ)*(60*Real.log T)^k) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = ((N : ℝ)^σ/(60*Real.log T))^k/(k : ℝ) := by rw [div_pow]; ring
    _ ≤ ‖shortDetectorTaylorPolynomial T N j t‖^k/(k : ℝ) :=
      div_le_div_of_nonneg_right hpow hkpos.le
    _ ≤ _ := hh

section
variable {η : ℝ} (hη : 0 < η)
include η hη
/-- The fixed logarithmic loss costs any positive power of T. -/
theorem shortDetectorHeightConstant_eventually :
    ∀ᶠ T : ℝ in atTop, shortDetectorHeightConstant*(Real.log T)^100 ≤ T^η := by pf_154 100 shortDetectorHeightConstant

/-- Normalizing by T^eta and absorbing the actual logarithmic loss gives
precisely L^sigma*T^(-2eta), as required by the epsilon budget. -/
theorem exists_shortNormalizedPowered_height :
    ∀ᶠ T : ℝ in atTop, ∀ (σ t : ℝ) (N j k : ℕ),
      0 < N → 0 ≤ σ → σ ≤ 1 → 0 < k → k ≤ 100 →
      (N : ℝ)^σ/(60*Real.log T) ≤ ‖shortDetectorTaylorPolynomial T N j t‖ →
      ∃ ℓ ∈ Finset.range k,
        (((2^ℓ*N^k : ℕ) : ℝ)^σ)*T^(-2*η) ≤
          ‖detectingPolynomial (2^ℓ*N^k) (shortNormalizedPoweredCoefficient η T N j k) t‖ := by pf_98 shortDetectorHeightConstant_eventually exists_shortPoweredDetector_height shortDetectorHeightConstant 100 detectingPolynomial_shortNormalizedPowered
end

end GuthMaynard.Improvement
