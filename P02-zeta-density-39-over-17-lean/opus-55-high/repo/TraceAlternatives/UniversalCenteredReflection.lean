module
public import TraceAlternatives.UniversalReflectionSecond
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
namespace Montgomery.RationalMoment

def universalLocalReflectionBudget (T L H R E : ℝ) : ℝ :=
  universalShortProfile T (H/L) R E

theorem reflection_local_energy_universal {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ,0<C ∧ ∀ T t₀ L H : ℝ,2≤T → Real.sqrt T≤L → 0<H → H≤2*T →
      ∀ W : Finset ℝ,(∀ t∈W,t∈Set.Icc t₀ (t₀+T)) →
        (∀ t∈W,∀ u∈W,t≠u → 1≤|t-u|) →
        MathCollab.Density.localReflectionEnergy L H W ≤
          C*T^η*universalLocalReflectionBudget T L H W.card (discreteAdditiveEnergy W) := by
  obtain ⟨C,hC,hBound⟩ := reflection_complete_pair_energy_universal hη
  refine ⟨240*C,by positivity,?_⟩
  intro T t₀ L H hT hL hH hHT W hW _hSep
  pm_4107
  let S := universalLocalReflectionBudget T L H W.card (discreteAdditiveEnergy W)
  have hS : 0≤S := by dsimp [S,universalLocalReflectionBudget,universalShortProfile,universalShortSublinearProfile]; positivity
  open MathCollab.Density in
  have hBlock (M : ℕ) (hM : M∈reflectionBlocks L H) :
      (∑' j : ℤ,completePairEnergy M (localSet W H j)) ≤ 24*(C*T^η*S) := by
    pm_4108
    pm_528 h hBound T t₀ hT M hM0 hMT W hW
    have hMono : universalShortProfile T M W.card (discreteAdditiveEnergy W) ≤ 8*S := by
      pm_5407 M hMU
      have hs := universalShortProfile_scale (by norm_num : (1:ℝ)≤2) hTp.le hX.le
        (Nat.cast_nonneg W.card) (Nat.cast_nonneg (discreteAdditiveEnergy W))
      pm_7201
    have hGrouped : completePairEnergy M W ≤ C*T^η*
        universalShortProfile T M W.card (discreteAdditiveEnergy W) := h
    pm_2726
  open MathCollab.Density in
  calc
    localReflectionEnergy L H W ≤ ∑ _M∈reflectionBlocks L H,24*(C*T^η*S) := sum_le_sum hBlock
    _ = ((reflectionBlocks L H).card:ℝ)*(24*(C*T^η*S)) := by simp
    _ ≤ 10*(24*(C*T^η*S)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast reflectionBlocks_card_le hLp hH
    _ = _ := by ring

end Montgomery.RationalMoment
