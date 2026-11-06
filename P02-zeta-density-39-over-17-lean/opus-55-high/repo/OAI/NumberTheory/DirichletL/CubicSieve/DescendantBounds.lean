module
public import OAI.NumberTheory.DirichletL.CubicSieve.CommonFactorBound
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

namespace SevenEighths.CubicSieve
noncomputable section

lemma descendant_unit_scale_le (M N D E : ℝ) (hM : 0 ≤ M) (hN : 0 < N)
    (hD : 1 ≤ D) (hE : 1 ≤ E) (hDN : D ≤ N) :
    (M/E)*(2/(N/D)) ≤ 2*M := by
  pm_72 hD0 D hE0 E
  pm_5443 hY N D hD0 hDN
  have hr : 2/(N/D) ≤ 2 := div_le_self (by norm_num) hY
  calc
    _ ≤ M*2 := mul_le_mul (div_le_self hM hE) hr (by positivity) hM
    _ = _ := mul_comm _ _

end
end SevenEighths.CubicSieve

end OAI
