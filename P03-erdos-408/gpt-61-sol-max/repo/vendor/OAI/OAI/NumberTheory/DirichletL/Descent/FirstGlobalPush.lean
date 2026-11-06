module

public import OAI.NumberTheory.DirichletL.Descent.FirstActualSecondEnergy

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion

variable {ι κ:Type*} [DecidableEq ι] [DecidableEq κ]

def firstGlobalRetainedSource (p:ι→ActualEisensteinCubic.O) (outer:Finset κ)
    (labels:κ→Finset (Ideal ActualEisensteinCubic.O)) (cube:κ→CubeCoordinates ι) (Y:ℝ):=
  outer.sigma (fun k=>firstRetainedSource p (labels k) (cube k) Y)

end SevenEighths.InverseMoment

end

end OAI
