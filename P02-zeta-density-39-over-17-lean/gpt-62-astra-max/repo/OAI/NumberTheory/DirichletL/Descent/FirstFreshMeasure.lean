module
public import OAI.NumberTheory.DirichletL.Descent.FirstNominal
public import OAI.NumberTheory.DirichletL.Descent.ProfileIntegral

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory JointLogSeparation
noncomputable section

def firstRelativeLog (q s : Fin 9 → ℝ) (i : Fin 9) : ℝ := Real.log (q i/s i)

end
end SevenEighths.InverseMoment

end OAI
