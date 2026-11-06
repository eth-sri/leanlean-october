module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaAmplitudeVariation
public import TaoTrudgianYang2025.BetaDualScales
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Literal stationary main terms and canonical prefix sums

The phase includes the negative-curvature factor e(-1/8). Main terms
use the actual physical second derivative. Exact prefix identities
retain the original natural-number summation endpoints.
-/

noncomputable section

open Set Expdb
open scoped FourierTransform BigOperators

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

def modelPhaseStationaryCharacter (F : ℝ → ℝ) (T N r : ℝ) : ℂ :=
  𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)-1/8)

def modelPhaseStationaryMainTerm (F : ℝ → ℝ) (T N r : ℝ) : ℂ :=
  (modelPhasePhysicalAmplitude F T N r : ℂ)*modelPhaseStationaryCharacter F T N r

def exponentialSumAtPrefixMax (F : ℝ → ℝ) (T N : ℝ) (a L : ℕ) : ℝ :=
  (Finset.range (L+1)).sup' (by simp) (fun j => ‖exponentialSumAt F T N a (a+j)‖)

section
variable (F : ℝ → ℝ) (T N : ℝ)
include F T N
theorem exponentialSumAt_eq_range (a L : ℕ) :
    exponentialSumAt F T N a (a+L) =
      ∑ i ∈ Finset.range (L+1), (𝐞 (T*F (((a : ℝ)+i)/N)) : ℂ) := by
  pm_7101 exponentialSumAt
  aesop

theorem norm_exponentialSumAt_le_prefixMax
    (a L j : ℕ) (hj : j ≤ L) :
    ‖exponentialSumAt F T N a (a+j)‖ ≤ exponentialSumAtPrefixMax F T N a L := by
  exact Finset.le_sup' (fun k => ‖exponentialSumAt F T N a (a+k)‖)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

theorem exponentialSumAtPrefixMax_nonneg (a L : ℕ) :
    0 ≤ exponentialSumAtPrefixMax F T N a L :=
  (norm_nonneg _).trans (norm_exponentialSumAt_le_prefixMax F T N a L 0 (Nat.zero_le L))
end

theorem exponentialSumAtPrefixMax_le {F : ℝ → ℝ} {T N B : ℝ} {a L : ℕ}
    (h : ∀ j ≤ L, ‖exponentialSumAt F T N a (a+j)‖ ≤ B) :
    exponentialSumAtPrefixMax F T N a L ≤ B := by
  apply Finset.sup'_le
  intro j hj
  grind

end TaoTrudgianYang2025
