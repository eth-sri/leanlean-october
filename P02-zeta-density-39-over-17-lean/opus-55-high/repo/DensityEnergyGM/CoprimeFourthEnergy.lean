module
public import SmallGcdCubicEnergy
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset
namespace Montgomery.RationalMoment

section
variable {T t₀ M : ℝ} (hT : 1 < T) (hM : 0 < M)
include T t₀ M hT hM
/-- Distinct reduced fractions retain the actual fourth energy in the
sampling estimate. No lower bound on the ordinate cardinality is required. -/
theorem coprime_dyadic_fourth_energy
    (Q : Finset (ℕ × ℕ))
    (hQ : ∀ q ∈ Q, 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2 ∧
      M < q.1 ∧ (q.1:ℝ) ≤ 2*M ∧ M < q.2 ∧ (q.2:ℝ) ≤ 2*M)
    (W : Finset ℝ) (hW : ∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T))
    :
    (∑ q ∈ Q, ‖∑ t ∈ W, phase (pairRatio q) t‖^4) ≤
      1024*(16*Real.pi*M^2+12*Real.pi*T)*(discreteAdditiveEnergy W:ℝ) := by
  pm_2758
  have hh := sampled_character_fourth hT hδ W hW x hx hs
  pm_2759
  rw [Finset.sum_coe_sort Q (fun q => ‖∑ t ∈ W, phase (pairRatio q) t‖^4)] at hh
  pm_795


/-- The reduced fourth moment at every short real scale, including small
scales and the exact tolerance-one energy. -/
theorem coprime_short_fourth_energy
    (hMT : M ^ 2 ≤ T) (Q : Finset (ℕ × ℕ))
    (hQ : ∀ q ∈ Q, 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2 ∧
      M < q.1 ∧ (q.1 : ℝ) ≤ 2 * M ∧ M < q.2 ∧ (q.2 : ℝ) ≤ 2 * M)
    (W : Finset ℝ) (hW : ∀ t ∈ W, t ∈ Set.Icc t₀ (t₀ + T)) :
    (∑ q ∈ Q, ‖∑ t ∈ W, phase (pairRatio q) t‖ ^ 4) ≤
      (28672 * Real.pi) * T * (discreteAdditiveEnergy W : ℝ) := by
  have h := coprime_dyadic_fourth_energy hT hM Q hQ W hW
  pm_5014 he discreteAdditiveEnergy W
  have hscale : 16 * Real.pi * M ^ 2 + 12 * Real.pi * T ≤ 28 * Real.pi * T := by
    nlinarith [Real.pi_pos]
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_right hscale he])
end

end Montgomery.RationalMoment
