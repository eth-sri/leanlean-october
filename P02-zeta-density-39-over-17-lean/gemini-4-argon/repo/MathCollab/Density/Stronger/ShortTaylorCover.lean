module
public import MathCollab.Density.Stronger.ShortFixedFamily

@[expose] public section

open Complex Set Filter
open scoped BigOperators Topology ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Original smooth scale, half choice, and Taylor index: all chosen from a
finite set before the zero. -/
def smoothTaylorIndices (σ T : ℝ) : Finset (ℤ × ℕ × ℕ) :=
  (smoothScaleIndices (detectorY σ T*(Real.log T)^2)).product
    ((Finset.range 2).product (Finset.range (detectorTaylorCutoff T+1)))


theorem smoothTaylorIndices_card_le_log {σ T : ℝ}
    (hD : ((smoothScaleIndices (detectorY σ T*(Real.log T)^2)).card : ℝ) ≤ 6*Real.log T)
    (hlog : 1 ≤ Real.log T) :
    ((smoothTaylorIndices σ T).card : ℝ) ≤ 144*(Real.log T)^2 := by
  have hJ := detectorTaylorCutoff_le_log hlog
  have h0 : 0 ≤ Real.log T := by linarith
  calc
    _ = ((smoothScaleIndices (detectorY σ T*(Real.log T)^2)).card : ℝ)*
        (2*(detectorTaylorCutoff T+1 : ℕ)) := by simp [smoothTaylorIndices]
    _ ≤ (6*Real.log T)*(2*(12*Real.log T)) := by push_cast; gcongr
    _ = _ := by ring




