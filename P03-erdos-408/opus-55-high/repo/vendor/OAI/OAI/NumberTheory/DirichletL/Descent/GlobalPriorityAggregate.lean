module

public import OAI.NumberTheory.DirichletL.Descent.GlobalPriorityRays
public import OAI.NumberTheory.DirichletL.Descent.GlobalPriorityPhysical

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap

namespace SevenEighths.InverseMoment
open SecondPassArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
def globalPriorityRetainedAggregate
    (p:ι→ActualEisensteinCubic.O)[∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hp:∀i,p i≠0)(hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    {Jo:ℕ}(extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))(w:InverseFirstPriorityParents.Source ι Jo→ℂ)
    (negative:Bool)(Ψ:ActualEisensteinCubic.O→*ℂ)(m:ActualEisensteinCubic.O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (V:𝓢(ℝ,ℂ))(X Y:ℝ)(R:Finset ι→Finset ι→ℝ):ℝ:=
  (32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
    ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z*
      ∑x∈unifiedSource p pool (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative J lists) (fun _=>R),
        globalPriorityWeight p hg negative Ψ m ray core w J a x*
        wholeRow p hp hcop hg extra pool negative (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
          m slots J lists a V X Y z x‖

end SevenEighths.InverseMoment

end

end OAI
