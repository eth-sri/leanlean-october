module

public import proofs.RAFCriticalWindowQuantitative.SourceContract

@[expose] public section

namespace RAFCriticalWindowQuantitative

def rationalIntervalError (source profile : ℚ × ℚ) : ℚ :=
  max (source.2-profile.1) (profile.2-source.1)

theorem interval_comparison_error {P S : ℝ} {source profile : ℚ × ℚ} {ε : ℚ}
    (hP : (source.1 : ℝ) ≤ P ∧ P ≤ source.2)
    (hS : (profile.1 : ℝ) ≤ S ∧ S ≤ profile.2 ∧ profile.2 - profile.1 < ε) :
    |P - S| ≤ (rationalIntervalError source profile : ℝ) := by
  rw [rationalIntervalError, Rat.cast_max, Rat.cast_sub, Rat.cast_sub]
  exact abs_le.mpr ⟨by linarith [le_max_right (source.2 - profile.1 : ℝ) (profile.2 - source.1), hP.1, hS.2.1],
    by linarith [le_max_left (source.2 - profile.1 : ℝ) (profile.2 - source.1), hP.2, hS.1]⟩

end RAFCriticalWindowQuantitative
