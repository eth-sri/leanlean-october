module
public import GafniTao.HeathBrownLemmaOneCompact
public import GafniTao.HeathBrownInteriorShift
import WeylPort.Analytic.RealLaplace

public section

/-!
# Monotonicity of the source-scale majorant

The endpoint repair replaces `N` by `N-2`.  All three critical monomials
are nondecreasing in the length because their `N` exponents are nonnegative.
-/

namespace GafniTao


section
variable {M N k : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N)
include M N k hM hMN
theorem heathBrownThreeTerm_mono (hk : 2 ≤ k)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    heathBrownThreeTerm M k lambda ≤
      heathBrownThreeTerm N k lambda := by
  let r := heathBrownCriticalReciprocal k
  have hr0 : 0 ≤ r :=
    (heathBrownCriticalReciprocal_pos hk).le
  have hrHalf : r ≤ 1 / 2 :=
    heathBrownCriticalReciprocal_le_half hk
  pm_96 hM0 M
  pm_106 hMNReal M N hMN
  pm_7905 hFirstExp r
  pm_8549 hLastExp
  have hfirst :
      (M : ℝ) ^ (1 - r) ≤ (N : ℝ) ^ (1 - r) :=
    Real.rpow_le_rpow hM0 hMNReal hFirstExp
  have hmiddle :
      (M : ℝ) * lambda ^ r ≤ (N : ℝ) * lambda ^ r :=
    mul_le_mul_of_nonneg_right hMNReal (by positivity)
  have hlast :
      (M : ℝ) ^ (1 - 2 * r) *
          lambda ^ (-2 * r / (k : ℝ)) ≤
        (N : ℝ) ^ (1 - 2 * r) *
          lambda ^ (-2 * r / (k : ℝ)) := by
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hM0 hMNReal hLastExp) (by positivity)
  unfold heathBrownThreeTerm
  dsimp only
  linarith

theorem heathBrown_sourceScale_main_mono (hk : 3 ≤ k)
    {A lambda epsilon C : ℝ}
    (hlambda : 0 < lambda) (hepsilon : 0 < epsilon)
    (hconstant : 0 ≤ heathBrownLemmaOneSourceConstant k A C epsilon) :
    heathBrownLemmaOneSourceConstant k A C epsilon *
        (M : ℝ) ^ epsilon * heathBrownThreeTerm M k lambda ≤
      heathBrownLemmaOneSourceConstant k A C epsilon *
        (N : ℝ) ^ epsilon * heathBrownThreeTerm N k lambda := by
  pm_96 hM0 M
  pm_106 hMNReal M N hMN
  have hpow := Real.rpow_le_rpow hM0 hMNReal hepsilon.le
  have hthree := heathBrownThreeTerm_mono hM hMN
    (by omega : 2 ≤ k) hlambda
  have hthreeM0 : 0 ≤ heathBrownThreeTerm M k lambda :=
    (heathBrownThreeTerm_pos (k := k) hM hlambda).le
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left
      (mul_le_mul hpow hthree hthreeM0 (by positivity)) hconstant)
end



end GafniTao
