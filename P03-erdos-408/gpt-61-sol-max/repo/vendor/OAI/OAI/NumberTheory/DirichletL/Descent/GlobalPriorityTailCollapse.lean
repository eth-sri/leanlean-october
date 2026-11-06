module

public import OAI.NumberTheory.DirichletL.Descent.WholePriorityParentBounds
public import OAI.NumberTheory.DirichletL.Descent.GlobalPrioritySource

@[expose] public section

namespace OAI


open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentGlobalPriorityTail
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrioritySecondSource InverseSecondPrincipalCaller InversePrincipalEnergy

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→ActualEisensteinCubic.O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

section
variable (hp : ∀i,p i≠0) (hinj : Function.Injective (fun i=>Ideal.span {p i})) (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
include hp hinj extra pool

lemma tail_forget    
        (negative : Bool)
    (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (slots J : Finset σ)  lists   a 
     V   X Y   R 
    (y : SecondParentSource ι (Jo+(J.card+J.card))) :
    priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R
      (forgetAppended (Jo:=Jo) y)=
    priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R y := rfl

theorem original_paired_tail  
     
        (source : Finset (Source ι Jo))
    (negative : Bool) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (slots J : Finset σ)
     lists   a   w 
     V   X Y   R  :
    (∑y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
      coefficient p J a w y*priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R y)=
    ∑x∈source,w x*(‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R (parent p x) := by
  rw [wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj]
  simp only [tail_forget]

end

end SevenEighths.InverseMomentGlobalPriorityTail


end OAI
