module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.CommonProfile

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentRemainingBox
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform

variable {ι : Type*} [Fintype ι]

def restoreTuple (B : Tuple ι) (v : Tuple (liveIndices B)) : Tuple ι :=
  Sum.elim (fun i => if h : i∈liveIndices B then v (Sum.inl ⟨i,h⟩) else 1)
    (fun j => v (Sum.inr j))

section
variable (B u : Tuple ι)


@[simp] theorem remaining_restore    v  :
    remainingTuple B (restoreTuple B v)=v := by
  funext i
  rcases i with i|j
  · simp [remainingTuple,restoreTuple]
  · rfl

theorem restore_remaining  
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1) :
    restoreTuple B (remainingTuple B u)=u := by
  funext i
  rcases i with i|j
  · simp only [restoreTuple,Sum.elim_inl]
    split_ifs with hi
    · rfl
    · exact (hf i (by simpa [liveIndices] using hi)).symm
  · rfl

end

def remainingSets (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal ActualEisensteinCubic.O)) :
    (liveIndices B ⊕ Fin 2) → Finset (Ideal ActualEisensteinCubic.O) :=
  Sum.elim (fun i => S (Sum.inl i.val)) (fun j => S (Sum.inr j))

section
variable (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal ActualEisensteinCubic.O)) (hf : ∀ i,B (Sum.inl i)≠1 → ∀ I∈S (Sum.inl i),I=1) (hg : ∀ i,B (Sum.inl i)≠1 → (1 : Ideal ActualEisensteinCubic.O)∈S (Sum.inl i)) (F : Tuple ι → ℂ)


theorem remaining_mem    
     u  (hu : u∈Fintype.piFinset S) :
    remainingTuple B u∈Fintype.piFinset (remainingSets B S) := by
  apply Fintype.mem_piFinset.mpr
  intro i
  rcases i with i|j
  · exact Fintype.mem_piFinset.mp hu (Sum.inl i.val)
  · exact Fintype.mem_piFinset.mp hu (Sum.inr j)

include hg in
theorem restore_mem    
     
     v  (hv : v∈Fintype.piFinset (remainingSets B S)) :
    restoreTuple B v∈Fintype.piFinset S := by
  apply Fintype.mem_piFinset.mpr
  intro i
  rcases i with i|j
  · simp only [restoreTuple,Sum.elim_inl]
    split_ifs with hi
    · exact Fintype.mem_piFinset.mp hv (Sum.inl ⟨i,hi⟩)
    · exact hg i (by simpa [liveIndices] using hi)
  · exact Fintype.mem_piFinset.mp hv (Sum.inr j)

include hf hg in
theorem remaining_box_sum    
     
     
      :
    (∑ u∈Fintype.piFinset S,F u)=
      ∑ v∈Fintype.piFinset (remainingSets B S),F (restoreTuple B v) := by
  apply Finset.sum_bij (fun u _ => remainingTuple B u)
  · exact remaining_mem B S
  · intro u hu v hv he
    have hu' := restore_remaining B u (fun i hi => hf i hi _ (Fintype.mem_piFinset.mp hu _))
    have hv' := restore_remaining B v (fun i hi => hf i hi _ (Fintype.mem_piFinset.mp hv _))
    rw [← hu',← hv',he]
  · intro v hv
    exact ⟨restoreTuple B v,restore_mem B S hg v hv,remaining_restore B v⟩
  · intro u hu
    rw [restore_remaining B u (fun i hi => hf i hi _ (Fintype.mem_piFinset.mp hu _))]

include hf in
theorem remaining_box_sum_gate    
     
      :
    (∑ u∈Fintype.piFinset S,F u)=
      if (∀ i,B (Sum.inl i)≠1 → (1 : Ideal ActualEisensteinCubic.O)∈S (Sum.inl i)) then
        ∑ v∈Fintype.piFinset (remainingSets B S),F (restoreTuple B v) else 0 := by
  split_ifs with hg
  · exact remaining_box_sum B S hf hg F
  · have he : Fintype.piFinset S=∅ := by
      grind
    rw [he,Finset.sum_empty]

end

end SevenEighths.CenteredMomentRemainingBox

end

end OAI
