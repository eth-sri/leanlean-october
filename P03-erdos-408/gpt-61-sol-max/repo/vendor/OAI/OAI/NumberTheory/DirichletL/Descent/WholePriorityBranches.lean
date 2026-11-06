module

public import OAI.NumberTheory.DirichletL.Descent.WholePriorityCollapse

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
open InverseMomentWholePriorityPhysical InversePrioritySecondSource InverseSecondPrincipalCaller

variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→ActualEisensteinCubic.O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def priorityZeroParent (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (negative:Bool) (Ψ:ActualEisensteinCubic.O→*ℂ) (m:ActualEisensteinCubic.O) (slots assigned:Finset σ)
    (lists:σ→Finset ι) (a:σ→ι→ℂ) (V:𝓢(ℝ,ℂ)) (X Y:ℝ)
    (R:Finset ι→Finset ι→ℝ) (y:SecondParentSource ι Jo):=
  truncatedSecondZero p hg pool Ψ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y)
    (InversePrincipalEnergy.markedRadial p (slots\assigned)
      (residualLists p negative (fun i=>lists i\extra y.cube) y) a ∅ V X)
    rowMajorant Y (secondVariableCutoff p y R)

def priorityTailParent (hp:∀i,p i≠0) (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (negative:Bool) (Ψ:ActualEisensteinCubic.O→*ℂ) (m:ActualEisensteinCubic.O) (slots assigned:Finset σ)
    (lists:σ→Finset ι) (a:σ→ι→ℂ) (V:𝓢(ℝ,ℂ)) (X Y:ℝ)
    (R:Finset ι→Finset ι→ℝ) (y:SecondParentSource ι Jo):=
  secondSourceTail p hp hg hinj pool Ψ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y)
    (InversePrincipalEnergy.markedRadial p (slots\assigned)
      (residualLists p negative (fun i=>lists i\extra y.cube) y) a ∅ V X)
    rowMajorant Y (secondVariableCutoff p y R)

end SevenEighths.InverseMoment

end

end OAI
