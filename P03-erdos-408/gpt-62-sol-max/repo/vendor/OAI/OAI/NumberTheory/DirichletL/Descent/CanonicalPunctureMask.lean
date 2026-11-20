module

public import OAI.NumberTheory.DirichletL.Descent.ActualChildStatePuncture
public import OAI.NumberTheory.DirichletL.Inversion.InitialClippedColumns

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge CanonicalQuadraticSieve
open InverseInitialClippedColumns
local notation "Eis" => ActualEisensteinCubic.O

section General
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,goodLambda∉Ideal.span {p i})

end General

end SevenEighths.InverseMoment
end

end OAI
