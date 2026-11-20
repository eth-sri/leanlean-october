module

public import Glennie.Compact.ObservationData
/- Deterministic robustness of the six raw scalar readouts. -/
@[expose] public section

namespace Glennie.Compact.ReadoutRobustnessR01
open Glennie Glennie.Compact.Affine20
open scoped BigOperators
open Glennie.SubmissionR03 (phiOf score score_eq_two_phi)
open Glennie.Compact.OperationalPhi
noncomputable section
set_option autoImplicit false

export Glennie.SubmissionR03 (Readouts weightedScore rawPlus rawMinus exactReadouts ErrorsAtMost noisyPhi)

theorem weightedScore_exact (T : Triple) :
    weightedScore (exactReadouts T) = score T := by
  simp only [weightedScore, exactReadouts, score, delta, contrast,
    inner_sub_right, rawPlus, rawMinus]
  ring

theorem weightedScore_eq_two_phi (T : Triple) :
    weightedScore (exactReadouts T) = 2 * phiOf T := by
  rw [weightedScore_exact, score_eq_two_phi]

/-- Deterministic coefficient bound; independence and positivity are unnecessary. -/
theorem weightedScore_error (noisy exact : Readouts) (ε : ℝ)
    (h : ErrorsAtMost noisy exact ε) :
    |weightedScore noisy - weightedScore exact| ≤ 12 * ε := by
  simp only [ErrorsAtMost, abs_le] at h
  simp only [weightedScore, abs_le]
  grind

theorem phi_error (T : Triple) (noisy : Readouts) (ε : ℝ)
    (h : ErrorsAtMost noisy (exactReadouts T) ε) :
    |noisyPhi noisy - phiOf T| ≤ 6 * ε := by
  have hb := weightedScore_error noisy (exactReadouts T) ε h
  rw [weightedScore_eq_two_phi] at hb
  rcases abs_le.mp hb with ⟨hl, hu⟩
  apply abs_le.mpr
  dsimp [noisyPhi]
  constructor <;> linarith

theorem scalar_sign_certificate {observed actual ε : ℝ}
    (h : |observed - actual| ≤ ε) (hm : ε < |observed|) :
    (observed < 0 ∧ actual < 0) ∨ (0 < observed ∧ 0 < actual) := by
  have hε := (abs_nonneg _).trans h
  rcases abs_le.mp h with ⟨hl, hu⟩
  rcases le_total 0 observed with ho | ho
  · rw [abs_of_nonneg ho] at hm
    right; constructor <;> linarith
  · rw [abs_of_nonpos ho] at hm
    left; constructor <;> linarith

/-- A posteriori strict sign certificate for the actual ordered triple. -/
theorem _root_.Glennie.SubmissionR03.signed_readout_margin
    (T : Triple) (noisy : Readouts) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ErrorsAtMost noisy (exactReadouts T) ε)
    (hm : 12 * ε < |weightedScore noisy|) :
    (weightedScore noisy < 0 ∧ phiOf T < 0) ∨
    (0 < weightedScore noisy ∧ 0 < phiOf T) := by
  have hb := weightedScore_error noisy (exactReadouts T) ε h
  rw [weightedScore_eq_two_phi] at hb
  simpa [mul_neg_iff, show ¬ (2 : ℝ) < 0 by norm_num] using scalar_sign_certificate hb hm

end
end Glennie.Compact.ReadoutRobustnessR01
