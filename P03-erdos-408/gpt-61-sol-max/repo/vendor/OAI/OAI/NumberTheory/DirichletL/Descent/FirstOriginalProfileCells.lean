module

public import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileIdentity
public import OAI.NumberTheory.DirichletL.Descent.FirstChildWindowsLive

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseSecondSourceBlocks

variable {ι : Type*} [DecidableEq ι]
variable (p : ι→ActualEisensteinCubic.O) [∀i,(Ideal.span {p i}).IsMaximal]

def originalNorms (x : OriginalIndex ι)  :=
  sourceNorms (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p)
    (fun x=>divisorElement p x.1) (fun x=>x.2.2) x

def originalOuterCell (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex)  :=
  (firstOriginalOuter pool Q).filter (fun x=>∀i:Fin 5,
    dyadIndex (originalNorms p ⟨x,(1,1)⟩ i.castSucc)=k i.castSucc)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma originalNorms_outer (x : OriginalIndex ι) (i : Fin 5) :
    originalNorms p ⟨x.1,(1,1)⟩ i.castSucc=originalNorms p x i.castSucc := by
  unfold originalNorms sourceNorms
  fin_cases i <;> simp [Fin.castSucc,leftNorm,rightNorm,commonNorm,activeNorm]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem original_cell_subset  pool   Q 
     labels   Y   k  :
    sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) k ⊆
    firstGlobalRetainedSource p (originalOuterCell p pool Q k) (fun _=>labels) (fun x=>x.1) Y := by
  intro x hx
  obtain ⟨hxs,hk⟩ := Finset.mem_filter.mp hx
  obtain ⟨ho,hf⟩ := Finset.mem_sigma.mp hxs
  apply Finset.mem_sigma.mpr
  refine ⟨Finset.mem_filter.mpr ⟨ho,?_⟩,hf⟩
  intro i
  rw [originalNorms_outer p x i]
  exact congrFun hk i.castSucc

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma original_outer_cell_subset  pool   Q   k  :
    originalOuterCell p pool Q k⊆firstOriginalOuter pool Q := Finset.filter_subset _ _

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
