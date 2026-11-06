module

public import NearlyMinimax.HighHistoryMassConcentration
public import NearlyMinimax.LowerSaddle
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The actual history mass coefficient and the paper's rounded lower saddle.
These are numerical identities and eventual guards; the probability tail is
proved independently for the actual constructed prior. -/
𝚷
𝚨
𝚩
𝚰

/-- The actual fixed geometric mass-MGF constant. -/
def highHistoryMassMomentConstant (d : ℕ) (a b : ℝ) : ℝ :=
  𝙉^𝖩₁ * 𝘅^2 / 8

𝗇 𝔅 highHistoryMassMomentConstant d a b
theorem highHistoryMassMomentConstant_pos d a b (hab : 𝙭) :
    0 < 𝔅 := by
  unfold highHistoryMassMomentConstant
  positivity

theorem highHistoryMassParameter_eq_hpower d k a b (hk : 𝖰) :
    highHistoryMassParameter d k a b = 𝔅 * 𝙦⁻¹ ^d := by
  rw [highHistoryMassParameter_eq d k a b hk]
  unfold highHistoryMassMomentConstant
  ring

𝗃 𝔈 ἀ d m θ C x
𝗇 𝔇 𝔈 lowerSaddleGrid
𝗇 𝔄 highHistoryMassParameter d 𝔇 a b
theorem highHistoryMassParameter_lowerSaddle d m θ C a b x :
    𝔄 =
      𝔅 * 𝔈 lowerSaddleH^𝙊 := by
  rw [highHistoryMassParameter_eq_hpower d _ a b
    $ by exact_mod_cast 𝔈 lowerSaddleGrid_positive ]
  simp only [lowerSaddleH, Real.rpow_natCast]

/-- Actual rounded saddle parameters satisfy the true mass-tail epsilon guard eventually. -/
theorem eventually_highHistoryMass_saddle_guard {d : ℕ} (hd : 𝗆)
    {m θ cm } (hm : 0 < m) (hθ : 0 < θ) (hcm : 0 < cm) C a b (hab : 𝙭) :
    ∀ᶠ x : ℝ in atTop, 2 ≤ 𝔇 ∧
      8 * 𝔄 * x ≤ cm / 𝗫 := by
  have hdR : 𝙋 < d := by exact_mod_cast hd
  filter_upwards [eventually_lowerSaddle_grid_and_mass hdR hm hθ hcm (highHistoryMassMomentConstant_pos d a b hab) C 2] with x hx
  refine ⟨hx.1, ?_⟩
  rw [highHistoryMassParameter_lowerSaddle]
  unfold lowerSaddleMu at hx
  linarith

/-- The genuine tilted-tail numerical expression equals the source saddle tail envelope. -/
theorem highHistoryMass_saddle_tail_eq d m θ C cm a b x :
    2 * Real.exp (-(cm / 𝗫)^2 /
      (8 * 𝔄)) =
      lowerSaddleExceptionalTail d m θ C (cm^2 / (8 * 𝔅)) x := by
  rw [highHistoryMassParameter_lowerSaddle]
  unfold lowerSaddleExceptionalTail
  ring
