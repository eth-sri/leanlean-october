module
/- Adapted from audited Density.DetectorDyadic; actual short coefficient support. -/
public import MathCollab.Density.DetectorDyadic
public import GuthMaynard.Improvement.ShortFiniteDetector
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Filter MathCollab.Density
open scoped Topology
noncomputable section
namespace GuthMaynard.Improvement

def shortDetectorBlock (ρ : ℂ) (T : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2*N), shortDetectorCoefficient T n*(n : ℂ)^(-ρ)

/-- The full finite list is fixed at T, before a zero is considered. -/
def shortDetectorDyadicCount (T : ℝ) : ℕ := Nat.log 2 (shortDetectorCutoff T)+1

theorem shortFiniteDetector_eq_dyadic_sum {T : ℝ} (hT : 1 ≤ T) (ρ : ℂ) :
    shortFiniteDetector ρ T =
      ∑ r ∈ Finset.range (shortDetectorDyadicCount T), shortDetectorBlock ρ T (2^r) := by
  let K := shortDetectorCutoff T
  let L := shortDetectorDyadicCount T
  pm_686 shortDetectorCoefficient
  have hX : 1 ≤ ⌊2*T^((100:ℝ)⁻¹)⌋₊ := Nat.le_floor (by
    have hp := Real.one_le_rpow hT (by positivity : (0:ℝ) ≤ (100:ℝ)⁻¹)
    linarith)
  pm_4263 shortDetectorCutoff shortDetectorCoefficient
  have hi : ∑ n ∈ Finset.Ioc 1 (2^L), f n = ∑ n ∈ Finset.range (2^L+1), f n := by
    apply Finset.sum_subset
    grind
    · intro n hn hn'
      have hnlow : n ≤ 1 := by
        have hnr := Finset.mem_range.mp hn
        have hni : ¬ (1 < n ∧ n ≤ 2^L) := by grind
        omega
      have hz : ¬ ⌊2*T^((100:ℝ)⁻¹)⌋₊ < n := by omega
      simp [f, shortDetectorCoefficient, hz]
  pm_1052

/-- Quantitative extraction from the fixed dyadic list, without moving t. -/
theorem exists_short_detector_dyadic_block {T A : ℝ} {ρ : ℂ}
    (hT : 1 ≤ T) (hA : 0 < A) (hlarge : A ≤ ‖shortFiniteDetector ρ T‖) :
    ∃ r ∈ Finset.range (shortDetectorDyadicCount T),
      A/(shortDetectorDyadicCount T : ℝ) ≤ ‖shortDetectorBlock ρ T (2^r)‖ := by pm_4264 shortDetectorDyadicCount shortDetectorBlock shortFiniteDetector_eq_dyadic_sum

/-- A nonzero block meets the true retained support, giving the packet's
strict lower block scale and its original logarithmic upper scale. -/
theorem shortDetectorBlock_scale_bounds {T : ℝ} {N : ℕ} {ρ : ℂ}
    (hT : 0 < T) (hblock : shortDetectorBlock ρ T N ≠ 0) :
    T^((100:ℝ)⁻¹) < (N : ℝ) ∧ (N : ℝ) < T^(1/2:ℝ)*(Real.log T)^2 := by pm_4265 shortDetectorCoefficient shortDetectorCoefficient_real_support

end GuthMaynard.Improvement
