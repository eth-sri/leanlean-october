module

public import OAI.NumberTheory.DirichletL.Inversion.PrincipalEnergy
public import OAI.NumberTheory.DirichletL.Descent.ChildCutoff

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InversePrincipalEnergy



lemma zero_mem_childFrequencyBall  a  (ha : a ≠ 0)  R  (hR : 0 ≤ R) :
    (0 : ActualEisensteinCubic.O) ∈ childFrequencyBall a R := by
  apply (mem_childFrequencyBall a ha R 0).mpr
  simpa using hR


end SevenEighths.InverseMoment

end OAI
