module

public import OAI.NumberTheory.DirichletL.Descent.SecondOriginalBound
public import OAI.NumberTheory.DirichletL.Descent.SecondSectorAssembly

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped Classical
noncomputable section
local instance inverseSecondAllModesUnits : Fintype ActualEisensteinCubic.Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

end
end SevenEighths.InverseMoment

end OAI
