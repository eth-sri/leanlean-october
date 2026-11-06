module

public import OAI.NumberTheory.DirichletL.Descent.CanonicalLongParent

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical
namespace SevenEighths.InverseMoment
open SecondPassArithmetic
open InverseMomentFirstOriginalProfile CompletedHeight

def actualLongSourceKeys {ι σ:Type}[DecidableEq ι][DecidableEq σ]
    (p:ι→ActualEisensteinCubic.O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal ActualEisensteinCubic.O))(Ψ:ActualEisensteinCubic.O→*ℂ)(m mCoef:ActualEisensteinCubic.O)
    (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)(om:ℝ→ℂ)
    (Z M r ell V H₀ ξ Lcap eta tau:ℝ) :=
  let mark:=fun v U=>primeMark slots lists weights (v.support∪U)
  let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal ActualEisensteinCubic.O)(D:Finset ι)=>
    firstDyadicRadius p q C D Z M r ell V eta tau
  let W:=fun y=>normTwistedSource om ξ (y/Z^r)
  let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels)
    (fun x=>x.1) (Z^(2*Lcap+15*eta+tau))
  liveJointKeys p source pool (sourceSummand p hp hcop hg
    (actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) cutoff Ψ m mark W rowMajorant (Z^M))

end SevenEighths.InverseMoment

end

end OAI
