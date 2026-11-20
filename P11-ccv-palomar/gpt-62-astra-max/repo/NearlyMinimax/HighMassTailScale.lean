module

public import NearlyMinimax.HighHistoryMassConcentration
public import NearlyMinimax.LowerSaddle

@[expose] public section

/-! The actual history mass coefficient and the paper's rounded lower saddle.
These are numerical identities and eventual guards; the probability tail is
proved independently for the actual constructed prior. -/
noncomputable section
open Filter
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable (d : ℕ) (m θ C : ℝ) (k : ℕ) (cm a b : ℝ)

/-- The actual fixed geometric mass-MGF constant. -/
def highHistoryMassMomentConstant : ℝ :=
  2^(2*d) * (b-a)^2 / 8

theorem highHistoryMassParameter_eq_hpower (hk : 0 < k) :
    highHistoryMassParameter d k a b = highHistoryMassMomentConstant d a b * ((k : ℝ)⁻¹)^d := by
  rw [highHistoryMassParameter_eq d k a b hk]
  unfold highHistoryMassMomentConstant
  ring

theorem highHistoryMassParameter_lowerSaddle (x : ℝ) :
    highHistoryMassParameter d (lowerSaddleGrid d m θ C x) a b =
      highHistoryMassMomentConstant d a b * (lowerSaddleH d m θ C x)^(d : ℝ) := by
  rw [highHistoryMassParameter_eq_hpower d _ a b
    (by exact_mod_cast lowerSaddleGrid_positive ..)]
  simp [lowerSaddleH]

/-- Actual rounded saddle parameters satisfy the true mass-tail epsilon guard eventually. -/
theorem eventually_highHistoryMass_saddle_guard {d : ℕ} (hd : 0 < d)
    {m θ cm : ℝ} (hm : 0 < m) (hθ : 0 < θ) (hcm : 0 < cm) (C a b : ℝ) (hab : a < b) :
    ∀ᶠ x in atTop, 2 ≤ lowerSaddleGrid d m θ C x ∧
      8 * highHistoryMassParameter d (lowerSaddleGrid d m θ C x) a b * x ≤ cm / lowerSaddleM m x := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  filter_upwards [eventually_lowerSaddle_grid_and_mass hdR hm hθ hcm ((by unfold highHistoryMassMomentConstant; positivity : 0 < highHistoryMassMomentConstant d a b)) C 2] with x hx
  refine ⟨hx.1, ?_⟩
  rw [highHistoryMassParameter_lowerSaddle]
  unfold lowerSaddleMu at hx
  bound

/-- The genuine tilted-tail numerical expression equals the source saddle tail envelope. -/
theorem highHistoryMass_saddle_tail_eq (x : ℝ) :
    2 * Real.exp (-(cm / (lowerSaddleM m x))^2 /
      (8 * highHistoryMassParameter d (lowerSaddleGrid d m θ C x) a b)) =
      lowerSaddleExceptionalTail d m θ C (cm^2 / (8 * highHistoryMassMomentConstant d a b)) x := by
  rw [highHistoryMassParameter_lowerSaddle]
  simp [lowerSaddleExceptionalTail] <;> ring

end NearlyMinimax
