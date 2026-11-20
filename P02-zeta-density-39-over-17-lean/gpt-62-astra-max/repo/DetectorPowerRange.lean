module
public import TwoPowerTailTransfer
public import RightSolidPolynomialCounts

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter MathCollab.Density.Stronger MathCollab.Density
namespace Montgomery.RationalMoment.RightDetector

/-- Whole-interval lower bound, including every closed join, for the exact detector exponent. -/
theorem rightSolid_detector_exponent_lower {σ : ℝ}
    (hl : 7/9 ≤ σ) (_hr : σ ≤ 4/5) :
    (881/6659:ℝ) ≤ (3*rightSolidLengthExponent σ/4)*(σ-1/2) := by
  unfold rightSolidLengthExponent
  split_ifs with h₁ h₂ h₃ h₄
  · have hd : 0 < 4*(11*σ-7) := by linarith
    have he : (3*(1/(11*σ-7))/4)*(σ-1/2) =
        (3*(σ-1/2))/(4*(11*σ-7)) := by field_simp
    rw [he]
    apply (le_div_iff₀ hd).mpr
    nlinarith
  · have hd : 0 < 4*(14610*σ-3849) := by linarith
    have he : (3*(4744/(14610*σ-3849))/4)*(σ-1/2) =
        (3*4744*(σ-1/2))/(4*(14610*σ-3849)) := by field_simp
    rw [he]
    apply (le_div_iff₀ hd).mpr
    nlinarith
  · have hd : 0 < 4*(19062*σ-5079) := by linarith
    have he : (3*(6154/(19062*σ-5079))/4)*(σ-1/2) =
        (3*6154*(σ-1/2))/(4*(19062*σ-5079)) := by field_simp
    rw [he]
    apply (le_div_iff₀ hd).mpr
    nlinarith
  · have hd : 0 < 4*(11808*σ-3195) := by linarith
    have he : (3*(3782/(11808*σ-3195))/4)*(σ-1/2) =
        (3*3782*(σ-1/2))/(4*(11808*σ-3195)) := by field_simp
    rw [he]
    apply (le_div_iff₀ hd).mpr
    nlinarith
  · have hd : 0 < 4*(6846*σ-1893) := by linarith
    have he : (3*(2168/(6846*σ-1893))/4)*(σ-1/2) =
        (3*2168*(σ-1/2))/(4*(6846*σ-1893)) := by field_simp
    rw [he]
    apply (le_div_iff₀ hd).mpr
    nlinarith


end Montgomery.RationalMoment.RightDetector
