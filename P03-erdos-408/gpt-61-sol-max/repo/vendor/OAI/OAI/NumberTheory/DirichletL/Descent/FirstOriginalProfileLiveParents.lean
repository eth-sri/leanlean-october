module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveEnergy
public import OAI.NumberTheory.DirichletL.Descent.OriginalCellPriority

@[expose] public section

namespace OAI


open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]

lemma refined_parent_source (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
     pool   Q 
     selector   k   l j  :
    globalParentSource (originalSubsetSource (refinedOuter p pool Q k (labelGate p j)))
      pool (originalSelector (fun x=>commonSelector p (selector x) l))=
      InverseFirstGlobalCaps.labelParentCell p pool Q selector k l j := by
  ext x
  rw [InverseFirstGlobalCaps.labelParentCell,Finset.mem_filter,InverseFirstGlobalCaps.mem_parentCell]
  simp only [globalParentSource,Finset.mem_biUnion,originalSubsetSource,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨y,⟨o,ho,rfl⟩,D,⟨hD,hs⟩,rfl⟩
    have ho' := Finset.mem_filter.mp ho
    refine ⟨⟨o,?_,D,hD,by simpa using hs,rfl⟩,?_⟩
    · simpa only [originalOuterCell_eq_caps] using ho'.1
    bound
  · rintro ⟨⟨o,ho,D,hD,hs,rfl⟩,hj⟩
    refine ⟨ofOriginal o,⟨o,?_,rfl⟩,D,⟨hD,by simpa using hs⟩,rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_,?_⟩
    · simpa only [originalOuterCell_eq_caps] using ho
    assumption

theorem refined_child_priority (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots : Finset σ)  lists   a 
     om   X t Y  (hY : 0<Y) :
    refinedChildEnergy p hp hg hinj pool Q k l (labelGate p j) negative Ψ m
      (fun v U=>primeMark slots lists a (v.support∪U)) om X t Y ≤
    globalPriorityOriginalEnergy p hg hp hinj
      (fun b=>if negative then b.rightExponent.support else b.leftExponent.support) pool
      (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j)
      (fun x=>(‖commonSelector p (fun _=>1) l x.quotientSupport‖:ℂ))
      negative Ψ m slots lists a om X t Y := by
  have he := original_subset_canonical_priority p hp hg hinj hc
    (refinedOuter p pool Q k (labelGate p j)) pool (fun _=>commonSelector p (fun _=>1) l)
    (fun b=>if negative then b.rightExponent.support else b.leftExponent.support)
    negative Ψ m slots lists a om X t Y hY
  rw [refined_parent_source] at he
  cases negative <;> simpa [refinedChildEnergy,divisorElement] using he

end SevenEighths.InverseMomentFirstOriginalProfile


end OAI
