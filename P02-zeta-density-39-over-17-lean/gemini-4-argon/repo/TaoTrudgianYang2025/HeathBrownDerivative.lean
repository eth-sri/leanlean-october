module
public import TaoTrudgianYang2025.HeathBrownBetaDeduction
public import GafniTao.WooleyNative

@[expose] public section

/-!
# Heath--Brown's source beta bound from native Vinogradov mean values

The kth-derivative input is supplied by the proved Wooley/Heath--Brown
dependency, not a theorem parameter. The public beta theorem displays
the exact formula in the Tao--Trudgian--Yang source.
-/

noncomputable section

open Expdb
open scoped NNReal

namespace TaoTrudgianYang2025

theorem isExponentSumBoundNonAsymptotic_heathBrown
    {k : ℕ} (hk : 3 ≤ k) {α : ℝ≥0} (hα : 0 < (α : ℝ)) :
    IsExponentSumBoundNonAsymptotic α (heathBrownBetaBound k α) :=
  isExponentSumBoundNonAsymptotic_heathBrown_of_derivative
    GafniTao.heathBrownKthDerivativeTheorem_native hk hα

