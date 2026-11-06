module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.SourceLiveColumn
public import OAI.NumberTheory.DirichletL.Moments.SourceCommonMask

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentLiveSupport
open CenteredMomentSourceLiveColumn CenteredMomentSourceLiveAllocation CenteredMomentRemainingBox
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum CenteredMomentFirstSectors CenteredMomentSourceCommonMask

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

section
variable (S : (ι ⊕ Fin 2) → Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I) (C : Ideal ActualEisensteinCubic.O) (B : Tuple ι) (hB : ∀ i,B i≠0) (hlabel : B∈allocationLabels S C) (v : Tuple (liveIndices B))


theorem restore_frozen     :
    ∀ i,B (Sum.inl i)≠1 → restoreTuple B v (Sum.inl i)=1 := by
  simp_all [restoreTuple, liveIndices]

theorem restore_product     :
    finiteTupleProduct (restoreTuple B v)=finiteTupleProduct v := by
  rw [remaining_product B _ (restore_frozen B v),remaining_restore]

include hp hlabel in
theorem restored_original_mem  
       
         
      (hv : v∈liveBox S B hB) :
    (fun i => B i*restoreTuple B v i)∈Fintype.piFinset S := by
  have hg : ∀ i,B (Sum.inl i)≠1 →
      (1:Ideal ActualEisensteinCubic.O)∈residualPool (B (Sum.inl i)) (hB _) (S (Sum.inl i)) := by
    intro i hi
    rw [mem_residualPool,mul_one]
    exact allocation_frozen_gate S hp C B hlabel i hi
  have hu := restore_mem B (fun i => residualPool (B i) (hB i) (S i)) hg v (by simpa only [liveBox,Fintype.mem_piFinset] using hv)
  simp_all

include hS hp in
theorem live_column_original_support  
       
        (C R a : Ideal ActualEisensteinCubic.O)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal ActualEisensteinCubic.O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal ActualEisensteinCubic.O)
    (hne : finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) a≠0) :
    C*a∈finiteColumns (Fintype.piFinset S) ∧ a≠0 ∧ IsCoprime C a := by
  obtain ⟨v,hv,hvn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hv,ha⟩ := Finset.mem_filter.mp hv
  have hm := profile_nonzero_masks (R*C) (fun i : liveIndices B => ν i.val)
    (fun i => Wslot i.val) (fun i => P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂
    (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1 v hvn
  rw [ha,IsCoprime.mul_right_iff] at hm
  have hsrc := restored_original_mem S hp C B hB hlabel v hv
  have he : finiteTupleProduct (fun i => B i*restoreTuple B v i)=C*a := by
    rw [finiteTupleProduct,Finset.prod_mul_distrib]
    change finiteTupleProduct B*finiteTupleProduct (restoreTuple B v)=_
    rw [hprod,restore_product,ha]
  have hn : C*a≠0 := by
    rw [← he,finiteTupleProduct]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hS i _ (Fintype.mem_piFinset.mp hsrc i))
  exact ⟨Finset.mem_image.mpr ⟨_,hsrc,he⟩,right_ne_zero_of_mul hn,hm.1.2.symm⟩

end

end SevenEighths.CenteredMomentLiveSupport

end

end OAI
