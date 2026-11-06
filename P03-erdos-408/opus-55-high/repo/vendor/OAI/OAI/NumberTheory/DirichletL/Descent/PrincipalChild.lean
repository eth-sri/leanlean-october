module

public import OAI.NumberTheory.DirichletL.Inversion.PrincipalEnergy
public import OAI.NumberTheory.DirichletL.Descent.ChildCutoff

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped Classical
noncomputable section

lemma zero_mem_childFrequencyBall (a : ActualEisensteinCubic.O) (ha : a ≠ 0) (R : ℝ) (hR : 0 ≤ R) :
    (0 : ActualEisensteinCubic.O) ∈ childFrequencyBall a R := by
  apply (mem_childFrequencyBall a ha R 0).mpr
  simp_all

end
end SevenEighths.InverseMoment

end OAI
