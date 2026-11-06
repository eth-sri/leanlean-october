module

public import Glennie.Compact.LocalContrast

/- Deterministic robustness of the six raw scalar readouts. -/
@[expose] public section
namespace Glennie.Compact.ReadoutRobustnessR01
open Glennie Glennie.Compact.Affine20 Glennie.Compact.Sections
open Glennie.Compact.OperationalPhi
section
export Glennie.SubmissionR03
  (Readouts weightedScore rawPlus rawMinus exactReadouts ErrorsAtMost noisyPhi)

theorem weightedScore_eq_two_phi (T : Triple) :
    weightedScore (exactReadouts T) = 2 * phiOf T := by
  rw [← LocalContrast.score_eq_two_phi]
  simp [weightedScore, exactReadouts, LocalContrast.score, delta, contrast,
    inner_sub_right, rawPlus, rawMinus,
    Glennie.SubmissionR03.f0, Glennie.SubmissionR03.f1, Glennie.SubmissionR03.f2]
  ring

/-- Deterministic coefficient bound; independence and positivity are unnecessary. -/
theorem weightedScore_error (noisy exact : Readouts) (ε : ℝ)
    (h : ErrorsAtMost noisy exact ε) :
    |weightedScore noisy - weightedScore exact| ≤ 12 * ε := by
  simp only [ErrorsAtMost, abs_le] at h
  rw [abs_le]
  constructor <;> dsimp [weightedScore] <;> linarith



variable (T : Triple) (noisy : Readouts) (ε : ℝ)
    (h : ErrorsAtMost noisy (exactReadouts T) ε)

include T noisy ε h in
theorem phi_error  :
    |noisyPhi noisy - phiOf T| ≤ 6 * ε := by
  have hb := weightedScore_error noisy (exactReadouts T) ε h
  rw [weightedScore_eq_two_phi] at hb
  rcases abs_le.mp hb with ⟨hl, hu⟩
  apply abs_le.mpr
  dsimp [noisyPhi]
  constructor <;> linarith


end
end Glennie.Compact.ReadoutRobustnessR01
