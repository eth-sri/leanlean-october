module

public import Mathlib
public import PottsDiscontinuity.Frozen.Defs.IsPottsInfiniteVolumeLimit
public import PottsDiscontinuity.Frozen.Defs.IsTranslationErgodic
public import PottsDiscontinuity.Frozen.Defs.DiagonalSite
public import PottsDiscontinuity.Frozen.Defs.PottsCriticalBeta
public import PottsDiscontinuity.PottsThm.PottsTheorem11
public import PottsDiscontinuity.RCMProof.Item3

/-! # Proof of Theorem 1.1 (`potts_theorem_1_1`) -/

@[expose] public section

namespace PottsDiscontinuity.Provider

open MeasureTheory Filter Topology Real
open scoped ENNReal

/-- Theorem 1.1, in the form used to close the statement `potts_theorem_1_1`. -/
theorem potts_theorem_1_1 {q : ℕ} (hq : 4 < q := by assumption) :
    ∃ μ : Fin (q + 1) → Measure (ℤ × ℤ → Set.Icc 1 q),
      (∀ i, IsPottsInfiniteVolumeLimit q (pottsCriticalBeta q) i (μ i)) ∧
      ((∀ i j, i ≠ j → μ i ≠ μ j) ∧ (∀ i, IsTranslationErgodic (μ i)) ∧
        μ 0 ≠ (q : ℝ≥0∞)⁻¹ • ∑ i : Fin q, μ i.succ) ∧
      (∀ i : Fin q, (1 : ℝ) / q < (μ i.succ).real {σ | ((σ (0, 0) : ℕ)) = (i.succ : ℕ)}) ∧
      (∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
        ∃ S : ℝ,
          Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
              (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
          Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
              Real.log ((μ 0).real {σ | σ (0, 0) = σ (diagonalSite n)} - 1 / q))
            atTop (𝓝 (lam + 2 * S)) ∧
          0 < lam + 2 * S) := by
  refine PottsThm.potts_theorem_1_1_of_rc_rate q hq fun lam hlam hcosh φ₀ hφ₀ => ?_
  have hq' : (4 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  obtain ⟨S, hS, hrate⟩ := RCMProof.rcItem3ForEveryFreeLimit_proved (q : ℝ) hq' φ₀ hφ₀ lam hlam hcosh
  obtain ⟨S₀, _, hS₀, _, hpos, _⟩ := identity44 lam hlam
  exact ⟨S, hS, hrate, tendsto_nhds_unique hS hS₀ ▸ hpos⟩

end PottsDiscontinuity.Provider
