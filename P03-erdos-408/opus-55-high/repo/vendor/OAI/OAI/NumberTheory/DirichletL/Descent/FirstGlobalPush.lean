module

public import OAI.NumberTheory.DirichletL.Descent.FirstActualSecondEnergy

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.InverseMoment
open SecondPassArithmetic
variable {ι κ:Type*} [DecidableEq ι] [DecidableEq κ]

def firstGlobalRetainedSource (p:ι→ActualEisensteinCubic.O) (outer:Finset κ)
    (labels:κ→Finset (Ideal ActualEisensteinCubic.O)) (cube:κ→CubeCoordinates ι) (Y:ℝ):
    Finset (Σ _ : κ,Ideal ActualEisensteinCubic.O×ActualEisensteinCubic.O):=
  outer.sigma (fun k=>firstRetainedSource p (labels k) (cube k) Y)

end SevenEighths.InverseMoment

end

end OAI
