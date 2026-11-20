module

public import Glennie.Compact.LocalContrast

/- Deterministic robustness of the six raw scalar readouts. -/
@[expose] public section
namespace Glennie.Compact.ReadoutRobustnessR01
open Glennie Glennie.Compact.Affine20 Glennie.Compact.Sections
open Glennie.Compact.OperationalPhi
noncomputable section
set_option autoImplicit false

export _root_.Glennie.SubmissionR03 (Readouts weightedScore rawPlus rawMinus exactReadouts ErrorsAtMost)

theorem weightedScore_exact (T : Triple) :
    weightedScore (exactReadouts T) = LocalContrast.score T := by
  grind [weightedScore, exactReadouts, LocalContrast.score, delta, contrast, inner_sub_right, rawPlus, rawMinus]

theorem weightedScore_eq_two_phi (T : Triple) :
    weightedScore (exactReadouts T) = 2 * phiOf T := by
  rw [weightedScore_exact, LocalContrast.score_eq_two_phi]

/-- Deterministic coefficient bound; independence and positivity are unnecessary. -/
theorem weightedScore_error (noisy exact : Readouts) (ε : ℝ)
    (h : ErrorsAtMost noisy exact ε) :
    |weightedScore noisy - weightedScore exact| ≤ 12 * ε := by
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩
  grind [weightedScore]

def noisyPhi (noisy : Readouts) : ℝ := weightedScore noisy / 2

theorem phi_error (T : Triple) (noisy : Readouts) (ε : ℝ)
    (h : ErrorsAtMost noisy (exactReadouts T) ε) :
    |noisyPhi noisy - phiOf T| ≤ 6 * ε := by
  have hb := weightedScore_error noisy (exactReadouts T) ε h
  grind [weightedScore_eq_two_phi, noisyPhi]

/-- A posteriori strict sign certificate for the actual ordered triple. -/
theorem sign_certificate (T : Triple) (noisy : Readouts) (ε : ℝ)
    (hε : 0 ≤ ε) (h : ErrorsAtMost noisy (exactReadouts T) ε)
    (hm : 12 * ε < |weightedScore noisy|) :
    (weightedScore noisy < 0 ∧ phiOf T < 0) ∨
    (0 < weightedScore noisy ∧ 0 < phiOf T) := by
  have he := weightedScore_error noisy _ ε h
  grind [weightedScore_eq_two_phi]

end
end Glennie.Compact.ReadoutRobustnessR01
