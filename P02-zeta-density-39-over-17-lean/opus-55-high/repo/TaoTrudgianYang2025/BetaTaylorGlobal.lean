module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaTaylorJets
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Global smooth Taylor averages and quantitative remainder identities

These lemmas apply to the actual smooth zero-extended Morse weight.
The supplied derivative bounds concern the original function, not its remainder.
-/

noncomputable section

open Set
open scoped ContDiff

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

section
variable {f : ℝ → ℝ}
include f
theorem segmentTaylorAverage_hasDerivAt_global (hf : ContDiff ℝ ∞ f) (a x : ℝ) (k : ℕ) :
    HasDerivAt (segmentTaylorAverage f a k) (segmentTaylorAverage f a (k+1) x) x := by
  pm_5282 segmentTaylorAverage_hasDerivAt

theorem segmentTaylorAverage_contDiff_global (hf : ContDiff ℝ ∞ f) (a : ℝ) (k : ℕ) :
    ContDiff ℝ ∞ (segmentTaylorAverage f a k) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have ha : a ∈ Ioo (min a x-1) (max a x+1) :=
    ⟨by grind,by grind⟩
  have hx : x ∈ Ioo (min a x-1) (max a x+1) :=
    ⟨by grind,by grind⟩
  exact (segmentTaylorAverage_contDiffOn (fun _ _ => hf.contDiffAt) ha k).contDiffAt
    (isOpen_Ioo.mem_nhds hx)

theorem abs_segmentTaylorAverage_le_global {M : ℝ} (a x : ℝ) (k : ℕ)
    (hb : ∀ u : ℝ, |iteratedDeriv k f u| ≤ M) :
    |segmentTaylorAverage f a k x| ≤ M := by
  apply abs_segmentTaylorAverage_le (l := min a x-1) (r := max a x+1) ?_ ?_ k
    (fun u _ => hb u)
  grind
  grind

theorem segmentTaylorAverage_second_global (hf : ContDiff ℝ ∞ f) (a x : ℝ) :
    (x-a)^2*segmentTaylorAverage (deriv (deriv f)) a 0 x =
      f x-f a-(x-a)*deriv f a := by
  pm_5282 segmentTaylorAverage_second
end

end TaoTrudgianYang2025
