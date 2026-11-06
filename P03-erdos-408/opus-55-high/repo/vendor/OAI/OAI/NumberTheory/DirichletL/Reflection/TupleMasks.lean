module

public import OAI.NumberTheory.DirichletL.Reflection.SlotChoices
public import OAI.NumberTheory.DirichletL.Reflection.OriginalMask

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open ActualEisensteinCubic
noncomputable section
variable {σ φ : Type*} [Fintype σ] [DecidableEq σ]

omit [Fintype σ] in
lemma slot_choice_fixed_split (L : σ→Finset (Ideal ActualEisensteinCubic.O)) (T : Finset σ)
    (a : ∀ i : T,L i.val) (b : ∀ i : {i // i∉T},L i.val) (F : φ→Ideal ActualEisensteinCubic.O) :
    (∀ j i,((slotChoiceSplit L T).symm (a,b) i).val≠F j) ↔
      (∀ j,∀ i : T,(a i).val≠F j) ∧ (∀ j,∀ i : {i // i∉T},(b i).val≠F j) := by
  constructor
  · intro h
    constructor
    · intro j i
      simpa only [slotChoiceSplit_active] using h j i.val
    · intro j i
      simpa only [slotChoiceSplit_inactive] using h j i.val
  · rintro ⟨ha,hb⟩ j i
    by_cases hi : i∈T
    · rw [slotChoiceSplit_active L T a b ⟨i,hi⟩]
      simp_all
    · rw [slotChoiceSplit_inactive L T a b ⟨i,hi⟩]
      simp_all

lemma slot_choice_mask_split (L : σ→Finset (Ideal ActualEisensteinCubic.O)) (T : Finset σ)
    (a : ∀ i : T,L i.val) (b : ∀ i : {i // i∉T},L i.val)
    (F : φ→Ideal ActualEisensteinCubic.O) (K : Ideal ActualEisensteinCubic.O) :
    (IsCoprime K (∏ i,((slotChoiceSplit L T).symm (a,b) i).val) ∧
      ∀ j i,((slotChoiceSplit L T).symm (a,b) i).val≠F j) ↔
    (IsCoprime K (∏ i : {i // i∉T},(b i).val) ∧ ∀ j,∀ i : {i // i∉T},(b i).val≠F j) ∧
      (IsCoprime K (∏ i : T,(a i).val) ∧ ∀ j,∀ i : T,(a i).val≠F j) := by
  rw [slot_choice_coprime_split,slot_choice_fixed_split]
  tauto

end
end SevenEighths.InverseReflectedPhase

end OAI
