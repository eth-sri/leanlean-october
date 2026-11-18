module

public import OAI.NumberTheory.DirichletL.Descent.SecondAllIntegral
public import OAI.NumberTheory.DirichletL.Descent.SecondBalancedPhysical
public import OAI.NumberTheory.DirichletL.Descent.SecondBalancedSource

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondPhysicalEnergyUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

end
end SevenEighths.InverseMoment

end OAI
