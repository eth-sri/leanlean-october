module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Descent.WholeRetainedSource

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseWholePriorityValidSource
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents InversePrioritySecondSource
open InverseMomentWholePriorityParents InverseMomentWholePriorityPhysical
open RayFourExpansion InversePrincipalEnergy InverseSecondPrincipalCaller

variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ}

variable (p : ι→ActualEisensteinCubic.O) [∀ i,(Ideal.span {p i}).IsMaximal]

variable (hp : ∀ i,p i≠0) (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem priorityOuter_zero  b   negative   Ψ   m 
     selector   r   core 
     D  (hD : selector D=0) : priorityOuter p hg b negative Ψ m selector r core D=0 := by
  simp_all [priorityOuter]

def wholePriorityPoisson (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (b : CubeCoordinates ι) (C E extra : Finset ι) (negative : Bool)
    (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : ℝ→ℂ) (X t Y : ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex) (D : Finset ι)  :=
  firstFreshSecondPoisson p hp hg hinj pool D b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
    (if negative then r.1 else r.2) Ψ m
    (fun U=>primeMark (slots\J)
      (fun i=>lists i\((extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)) a U)
    om X (∏ i∈C,p i) (primeSubsetGenerator (fun i=>Ideal.span {p i}) E) core t Y

theorem parentPoisson_fixed_whole (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (b : CubeCoordinates ι) (C E extra D : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (negative : Bool)
    (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (slots J : Finset σ)  lists   a 
     om   X t Y   r   core  :
    parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra) a om X t Y r core
      (parent p (fixedPoint b C E old D)) =
    wholePriorityPoisson p hp hg hinj pool b C E extra negative Ψ m slots J lists a om X t Y r core D := by
  have hl : residualLists p negative (fun i=>lists i\extra)
      (parent p (fixedPoint b C E old D)) =
      (fun i=>lists i\((extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)) := by
    funext i
    unfold residualLists
    rw [quotientSupport_parent p hinj]
    change (lists i\extra)\(((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)=_
    ext k
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  unfold parentPoisson wholePriorityPoisson
  rw [quotientSupport_parent p hinj,hl]
  rfl

variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))

end SevenEighths.InverseWholePriorityValidSource

end

end OAI
