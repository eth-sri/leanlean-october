module
public import OAI.NumberTheory.DirichletL.Inversion.PrincipalEnergy
public import OAI.NumberTheory.DirichletL.Descent.ChildCutoff

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InversePrincipalEnergy
noncomputable section

lemma zero_mem_childFrequencyBall (a : Eis) (ha : a ≠ 0) (R : ℝ) (hR : 0 ≤ R) :
    (0 : Eis) ∈ childFrequencyBall a R := by
  apply (mem_childFrequencyBall a ha R 0).mpr
  simpa using hR
