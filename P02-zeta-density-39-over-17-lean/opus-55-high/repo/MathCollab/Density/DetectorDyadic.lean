module
public import MathCollab.Density.DetectorTaylorFamily
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

def detectorBlock (ρ : ℂ) (T : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2*N), firstDetectorCoefficient T n*(n : ℂ)^(-ρ)

/-- The full finite list is fixed at T, before a zero is considered. -/
def detectorDyadicCount (T : ℝ) : ℕ := Nat.log 2 (firstDetectorCutoff T)+1

theorem sum_dyadic_Ioc (f : ℕ → ℂ) (L : ℕ) :
    (∑ r ∈ Finset.range L, ∑ n ∈ Finset.Ioc (2^r) (2*2^r), f n) =
      ∑ n ∈ Finset.Ioc 1 (2^L), f n := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    have he : 2^(L+1) = 2*2^L := by ring
    rw [he]
    exact Finset.sum_Ioc_consecutive f (by exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))) (by omega)

theorem finiteDetector_eq_dyadic_sum {T : ℝ} (hT : 1 ≤ T) (ρ : ℂ) :
    finiteDetector ρ T =
      ∑ r ∈ Finset.range (detectorDyadicCount T), detectorBlock ρ T (2^r) := by
  let K := firstDetectorCutoff T
  let L := detectorDyadicCount T
  pm_686 firstDetectorCoefficient
  have hX : 1 ≤ ⌊firstDetectorX T⌋₊ := Nat.le_floor (by simpa using firstDetectorX_one_le hT)
  pm_4263 firstDetectorCutoff firstDetectorCoefficient
  have hi : ∑ n ∈ Finset.Ioc 1 (2^L), f n = ∑ n ∈ Finset.range (2^L+1), f n := by
    apply Finset.sum_subset
    grind
    · intro n hn hn'
      have hnlow : n ≤ 1 := by
        have hnr := Finset.mem_range.mp hn
        have hni : ¬ (1 < n ∧ n ≤ 2^L) := by simpa using hn'
        omega
      have hz : ¬ ⌊firstDetectorX T⌋₊ < n := by omega
      simp [f, firstDetectorCoefficient, hz]
  pm_1052

/-- Quantitative extraction from the fixed dyadic list, without moving t. -/
theorem exists_detector_dyadic_block {T A : ℝ} {ρ : ℂ}
    (hT : 1 ≤ T) (hA : 0 < A) (hlarge : A ≤ ‖finiteDetector ρ T‖) :
    ∃ r ∈ Finset.range (detectorDyadicCount T),
      A/(detectorDyadicCount T : ℝ) ≤ ‖detectorBlock ρ T (2^r)‖ := by pm_4264 detectorDyadicCount detectorBlock finiteDetector_eq_dyadic_sum

/-- A nonzero block meets the true retained support, giving the packet's
strict lower block scale and its original logarithmic upper scale. -/
theorem detectorBlock_scale_bounds {T : ℝ} {N : ℕ} {ρ : ℂ}
    (hT : 0 < T) (hblock : detectorBlock ρ T N ≠ 0) :
    firstDetectorX T/2 < (N : ℝ) ∧ (N : ℝ) < T*(Real.log T)^2 := by pm_4265 firstDetectorCoefficient firstDetectorCoefficient_real_support

end MathCollab.Density
