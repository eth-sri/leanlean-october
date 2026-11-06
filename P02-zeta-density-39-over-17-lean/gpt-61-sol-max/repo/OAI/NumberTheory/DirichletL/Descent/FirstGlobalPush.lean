module
public import OAI.NumberTheory.DirichletL.Descent.FirstActualSecondEnergy

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic SecondPassArithmetic
open scoped EisensteinEis
variable {ι κ:Type*} [DecidableEq ι] [DecidableEq κ]

def firstGlobalRetainedSource (p:ι→Eis) (outer:Finset κ)
    (labels:κ→Finset (Ideal Eis)) (cube:κ→CubeCoordinates ι) (Y:ℝ):
    Finset (Σ _ : κ,Ideal Eis×Eis):=
  outer.sigma (fun k=>firstRetainedSource p (labels k) (cube k) Y)






