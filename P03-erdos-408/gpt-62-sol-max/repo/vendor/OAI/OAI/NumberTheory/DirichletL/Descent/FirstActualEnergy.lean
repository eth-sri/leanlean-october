module

public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalFamily
public import OAI.NumberTheory.DirichletL.Descent.FirstModeColumns
public import OAI.NumberTheory.DirichletL.Descent.FirstPass

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped Classical
open MeasureTheory JointLogSeparation FourierBridge ActualEisensteinCubic FirstPassCubeLabels
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [OAI.PrincipalFamily.Maximal p]
  (hcop : OAI.PrincipalFamily.Coprime p)
  (hg : OAI.PrincipalFamily.Avoids p ConcretePrimeRowBridge.goodLambda)

theorem firstOuterPhase_norm (h : Fin 9 → ℝ) (a : Fin 7 → ℝ) :
    ‖firstOuterPhase h a‖ = 1 := by
  simp [firstOuterPhase,norm_prod,logPhase_norm]

end
end SevenEighths.InverseMoment

end OAI
