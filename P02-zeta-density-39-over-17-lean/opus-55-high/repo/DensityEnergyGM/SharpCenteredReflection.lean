module
public import DensityEnergyGM.SharpReflectionSecond
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
namespace Montgomery.RationalMoment

def sharpLocalReflectionBudget (T L H R E : ℝ) : ℝ :=
  (H/L)^2*E^(1/2:ℝ)+R*E^(1/4:ℝ)*
    ((H/L)^(9/5:ℝ)+T^(1/4:ℝ)*(H/L)^(6/5:ℝ))

theorem reflection_local_energy_sharp {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ,0<C ∧ ∀ T t₀ L H : ℝ,2≤T → Real.sqrt T≤L → 0<H → H≤2*T →
      ∀ W : Finset ℝ,(∀ t∈W,t∈Set.Icc t₀ (t₀+T)) →
        (∀ t∈W,∀ u∈W,t≠u → 1≤|t-u|) →
        MathCollab.Density.localReflectionEnergy L H W ≤
          C*T^η*sharpLocalReflectionBudget T L H W.card (discreteAdditiveEnergy W) := by
  obtain ⟨C,hC,hBound⟩ := reflection_complete_pair_energy_sharp hη
  pm_508 hSep
  pm_4107
  let S := sharpLocalReflectionBudget T L H W.card (discreteAdditiveEnergy W)
  have hS : 0≤S := by dsimp [S,sharpLocalReflectionBudget]; positivity
  open MathCollab.Density in
  have hBlock (M : ℕ) (hM : M∈reflectionBlocks L H) :
      (∑' j : ℤ,completePairEnergy M (localSet W H j)) ≤ 12*(C*T^η*S) := by
    pm_4108
    have h := hBound T t₀ hT M hM0 hMT W hW hSep
    pm_497
    have hPow (q : ℝ) (hq : 0≤q) (hq2 : q≤2) : (M:ℝ)^q≤4*X^q := by
      calc
        _ ≤ (2*X)^q := Real.rpow_le_rpow (Nat.cast_nonneg M) hMU hq
        _ = (2:ℝ)^q*X^q := Real.mul_rpow (by norm_num) hX.le
        _ ≤ 4*X^q := by
          pm_290 hh hq2
    have hMono : (M:ℝ)^2*(discreteAdditiveEnergy W:ℝ)^(1/2:ℝ)+
        (W.card:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/4:ℝ)*
          ((M:ℝ)^(9/5:ℝ)+T^(1/4:ℝ)*(M:ℝ)^(6/5:ℝ)) ≤ 4*S := by
      calc
        _ ≤ (4*X^2)*(discreteAdditiveEnergy W:ℝ)^(1/2:ℝ)+
            (W.card:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/4:ℝ)*
              ((4*X^(9/5:ℝ))+T^(1/4:ℝ)*(4*X^(6/5:ℝ))) := by
          gcongr
          · exact hPow _ (by norm_num) (by norm_num)
          · exact hPow _ (by norm_num) (by norm_num)
        _ = _ := by dsimp [S,sharpLocalReflectionBudget,X]; ring
    exact (reflection_local_pair_le_three hH M W).trans
      ((mul_le_mul_of_nonneg_left
        (h.trans (mul_le_mul_of_nonneg_left hMono (by positivity)))
        (by norm_num : (0:ℝ)≤3)).trans_eq (by ring))
  pm_163

end Montgomery.RationalMoment
