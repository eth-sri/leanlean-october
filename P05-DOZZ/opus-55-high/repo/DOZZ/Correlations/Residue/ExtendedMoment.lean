/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.ExtendedTail
public import DOZZ.Correlations.Residue.CompetitorLimit
public import DOZZ.Complex.Basic

/-! Almost-sure finiteness and real/extended moment conversion for the residue masses. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
section
variable (Y : Ω → ℝ≥0∞)
section
variable (hY : AEMeasurable Y P)
include hY

/-- A finite positive moment excludes infinite mass and gives real-power integrability. -/
theorem residue_real_moment_of_extended_bound
    (r : ℝ) (hr : 0 < r)
    (hfinite : (∫⁻ ω, ENNReal.rpow (Y ω) r ∂P) ≠ ⊤) :
    (∀ᵐ ω ∂P, Y ω ≠ ⊤) ∧ Integrable (fun ω => (Y ω).toReal ^ r) P ∧
      (∫ ω, (Y ω).toReal ^ r ∂P) = (∫⁻ ω, ENNReal.rpow (Y ω) r ∂P).toReal := by
  have hpow := hY.pow_const r
  have hf := ae_lt_top' hpow hfinite
  have hmass := hf.mono fun ω hω =>
    (ENNReal.rpow_eq_top_iff_of_pos hr).not.mp hω.ne
  refine ⟨hmass, ?_, ?_⟩
  · have hh := integrable_toReal_of_lintegral_ne_top hpow hfinite
    simpa only [ENNReal.rpow_eq_pow, ENNReal.toReal_rpow] using hh
  · simpa only [ENNReal.rpow_eq_pow, ENNReal.toReal_rpow] using integral_toReal hpow hf

/-- Finite masses permit conversion between their literal extended moment and real moment. -/
theorem residue_integral_toReal_rpow
    (hfinite : ∀ᵐ ω ∂P, Y ω ≠ ⊤)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫ ω, (Y ω).toReal ^ q ∂P) = (∫⁻ ω, ENNReal.rpow (Y ω) q ∂P).toReal := by
  simpa only [ENNReal.rpow_eq_pow, ENNReal.toReal_rpow] using integral_toReal (hY.pow_const q) (hfinite.mono fun ω hω => ENNReal.rpow_lt_top_of_nonneg hq hω)

end

end

/-- Tail-derived integrability inside the convergent moment strip. -/
theorem residue_real_power_integrable_of_extended_tail
    [IsProbabilityMeasure P]
    (Y : Ω → ℝ≥0∞) (hY : AEMeasurable Y P)
    (c β η C q : ℝ) (hβ : 0 < β) (hη : 0 < η) (hC : 0 ≤ C)
    (hq : 0 < q) (hqβ : q < β)
    (htail : ∀ t : ℝ, 1 ≤ t →
      |(P {ω | ENNReal.ofReal t < Y ω}).toReal - c * t ^ (-β)| ≤ C * t ^ (-β - η)) :
    Integrable (fun ω => (Y ω).toReal ^ q) P := by
  apply (realMoment_tail_error P (fun ω => (Y ω).toReal)
    (ENNReal.measurable_toReal.comp_aemeasurable hY) (ae_of_all _ fun _ => ENNReal.toReal_nonneg)
    c β η C q hq hqβ hη hC ?_).1
  intro t ht
  rw [residue_realUpperTail_toReal P Y hY (residue_ae_finite_of_tail P Y c β η C hβ hη htail) t (by positivity)]
  simp_all

end

end DOZZ.Proofs
