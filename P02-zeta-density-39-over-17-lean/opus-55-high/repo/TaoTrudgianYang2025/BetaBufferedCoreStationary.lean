module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaBufferedCore
public import TaoTrudgianYang2025.BetaBufferedStationary
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Stationary-frequency selection inside the actual physical core

The selected set is derived from the actual slope image. Its size is
controlled by T/N, independently of the much larger far-tail radius.
-/

noncomputable section

open Set Expdb
open scoped BigOperators

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

theorem modelPhaseCore_card_le
    {σ δ T N : ℝ} (hσ : 0 ≤ σ) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hT : 0 ≤ T) (hN : 0 < N) :
    ((Finset.Icc (modelPhaseCoreLower σ δ T N) (modelPhaseCoreUpper δ T N)).card : ℝ) ≤
      3*(T/N)+3 := by
  have hAB := modelPhaseCoreLower_le_upper hσ hδ hT hN
  have hc := Int.card_Icc_of_le _ _ (show
    modelPhaseCoreLower σ δ T N ≤ modelPhaseCoreUpper δ T N+1 by omega)
  have he : ((Finset.Icc (modelPhaseCoreLower σ δ T N)
      (modelPhaseCoreUpper δ T N)).card : ℝ) =
        (modelPhaseCoreUpper δ T N : ℝ)+1-(modelPhaseCoreLower σ δ T N : ℝ) := by
    exact_mod_cast hc
  rw [he]
  pm_1616 ha Int.lt_floor_add_one
  have hb := Int.ceil_lt_add_one ((T/N)*(1+δ))
  pm_534 hs
  have hTN : 0 ≤ T/N := div_nonneg hT hN.le
  pm_1615 hlo hTN
  have hhi : (T/N)*(1+δ) ≤ 2*(T/N) := by
    have h := mul_le_mul_of_nonneg_left (show 1+δ ≤ (2 : ℝ) by linarith) hTN
    nlinarith
  unfold modelPhaseCoreLower modelPhaseCoreUpper
  linarith

end TaoTrudgianYang2025
