module

public import OAI.NumberTheory.DirichletL.Descent.SecondPhysicalEnergy
public import OAI.NumberTheory.DirichletL.Descent.SecondNormalizedEnergy
public import OAI.NumberTheory.DirichletL.Descent.SecondBalancedSource

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap InverseInitialClippedColumns
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondPhysicalRecursiveUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

end
end SevenEighths.InverseMoment

end OAI
