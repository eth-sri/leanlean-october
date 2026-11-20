module
public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalIdealFamily
public import OAI.NumberTheory.DirichletL.Descent.FirstEnergy

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory JointLogSeparation FourierBridge ActualEisensteinCubic FirstPassCubeLabels
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [OAI.PrincipalIdealFamily.Maximal p]
  (hcop : OAI.PrincipalIdealFamily.PairwiseCoprime p)
  (hg : OAI.PrincipalIdealFamily.Avoids p ConcretePrimeRowBridge.goodLambda)

theorem firstOuterPhase_norm (h : Fin 9 → ℝ) (a : Fin 7 → ℝ) :
    ‖firstOuterPhase h a‖ = 1 := by
  simp [firstOuterPhase,norm_prod,logPhase_norm]

end
end SevenEighths.InverseMoment

end OAI
