module

public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalFamily
public import OAI.NumberTheory.DirichletL.Descent.SecondCellPhysical
public import OAI.NumberTheory.DirichletL.Descent.SecondCellParameters
public import OAI.NumberTheory.DirichletL.Descent.PrioritySourceBudget
public import OAI.NumberTheory.DirichletL.Inversion.WholePriorityRetainedSource
public import OAI.NumberTheory.DirichletL.Inversion.SecondPrincipalCaller
public import OAI.NumberTheory.DirichletL.Descent.FirstRetainedFamily
public import OAI.NumberTheory.DirichletL.Descent.FirstWholeCubePriority
public import OAI.NumberTheory.DirichletL.Descent.FirstWholeMarkedColumns
public import OAI.NumberTheory.DirichletL.Inversion.WholePriorityRapidTail

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseInitialArithmetic
open InverseFirstPriorityParents InverseMomentWholePriorityParents InverseWholePriorityValidSource
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
open InverseMomentWholePriorityPhysical InversePrioritySecondSource InverseSecondPrincipalCaller
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→Eis) [OAI.PrincipalFamily.Maximal p]
  (hg:OAI.PrincipalFamily.Avoids p ConcretePrimeRowBridge.goodLambda)

def priorityZeroParent (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis) (slots assigned:Finset σ)
    (lists:σ→Finset ι) (a:σ→ι→ℂ) (V:𝓢(ℝ,ℂ)) (X Y:ℝ)
    (R:Finset ι→Finset ι→ℝ) (y:SecondParentSource ι Jo):ℂ:=
  truncatedSecondZero p hg pool Ψ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y)
    (InversePrincipalEnergy.markedRadial p (slots\assigned)
      (residualLists p negative (fun i=>lists i\extra y.cube) y) a ∅ V X)
    rowMajorant Y (secondVariableCutoff p y R)

def priorityTailParent (hp:∀i,p i≠0) (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis) (slots assigned:Finset σ)
    (lists:σ→Finset ι) (a:σ→ι→ℂ) (V:𝓢(ℝ,ℂ)) (X Y:ℝ)
    (R:Finset ι→Finset ι→ℝ) (y:SecondParentSource ι Jo):ℂ:=
  secondSourceTail p hp hg hinj pool Ψ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y)
    (InversePrincipalEnergy.markedRadial p (slots\assigned)
      (residualLists p negative (fun i=>lists i\extra y.cube) y) a ∅ V X)
    rowMajorant Y (secondVariableCutoff p y R)

end SevenEighths.InverseMoment

end

end OAI
