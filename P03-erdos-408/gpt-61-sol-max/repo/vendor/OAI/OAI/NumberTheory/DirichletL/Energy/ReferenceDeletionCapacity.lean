module

public import OAI.NumberTheory.DirichletL.Energy.ReferenceDeletionBudget
public import OAI.NumberTheory.DirichletL.Energy.ReferenceState
public import OAI.NumberTheory.DirichletL.Energy.Bands

@[expose] public section

namespace OAI


open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentEnergyReferenceDeletionCapacity
open HeckeFamily CenteredMomentEnergyReferenceDeletionBudget
open CenteredMomentEnergyReferenceState CenteredMomentEnergyBands CenteredMomentLiveCapacity



lemma deleted_short_length (Z M:ℝ)(hZ:1<Z)(hM:0≤M)
    (D:Finset (Ideal HeckeFamily.O))(hD:∀I∈D,Prime I):
    length Z (comparisonFirst Z M/((∏I∈D,I).absNorm:ℝ))≤M/4:=by
  have hn:=product_norm_ge_one D hD
  have hY:1≤comparisonFirst Z M:=Real.one_le_rpow hZ.le (by linarith)
  have hdiv:comparisonFirst Z M/((∏I∈D,I).absNorm:ℝ)≤comparisonFirst Z M:=
    div_le_self (zero_le_one.trans hY) hn
  have hm:max 1 (comparisonFirst Z M/((∏I∈D,I).absNorm:ℝ))≤comparisonFirst Z M:=max_le hY hdiv
  have he:=Real.logb_le_logb_of_le hZ
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 _)) hm
  simpa only [length,comparisonFirst,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using he

end SevenEighths.CenteredMomentEnergyReferenceDeletionCapacity



end OAI
