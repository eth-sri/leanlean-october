module
/- A weak actual mollified fourth moment from the ordinary fourth moment.
The fixed power loss 1/25 is intentional; this does not assert
ShortMobiusFourthMoment. -/
public import GuthMaynard.Improvement.ShortDetectorLocalMass
public import MathCollab.Density.Stronger.Fourth.FourthMoment
public import HalfLossShortMoment
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set MathCollab.Density MathCollab.Density.Stronger
open scoped Interval
namespace GuthMaynard.Improvement

theorem shortTwistedNorm_fourth_le {H : ℝ} (hH : 0 ≤ H) (t : ℝ) :
    (shortTwistedNorm H t)^4 ≤
      16*H^((1:ℝ)/25)*(zetaMomentCriticalNorm t)^4 := by
  have hm := (norm_zetaMollifier_le_cutoff (2*H^((1:ℝ)/100))
    (s := (1/2:ℂ)+(t:ℂ)*Complex.I) (by norm_num)).trans
    (Nat.floor_le (by positivity))
  have hp : shortTwistedNorm H t ≤ zetaMomentCriticalNorm t*(2*H^((1:ℝ)/100)) := by
    pm_7
  pm_6013
  have he : (H^((1:ℝ)/100))^4 = H^((1:ℝ)/25) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hH]; norm_num
  simp only [mul_pow,he] at hh
  grind

/-- Constants precede height; the norm and integration interval are literal. -/
theorem weak_short_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ C H0 : ℝ, 0 < C ∧ 2 ≤ H0 ∧ ∀ H : ℝ, H0 ≤ H →
      (∫ t in Icc (H/2) (3*H), (shortTwistedNorm H t)^4) ≤
        C*H^(1+(1:ℝ)/25+ε) := by pf_20 48 16 25 shortTwistedNorm_fourth_le

end GuthMaynard.Improvement
