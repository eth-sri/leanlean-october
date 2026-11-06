module
public import OAI.NumberTheory.DirichletL.Reflection.SlotChoices
public import OAI.NumberTheory.DirichletL.Reflection.OriginalMask
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ : Type*} [Fintype σ] [DecidableEq σ]

section
variable (L : σ→ Finset (Ideal Eis)) (T : Finset σ) (a : ∀ i : T,L i.val) (b : ∀ i : {i // i∉T},L i.val) (F : φ→ Ideal Eis)
include L T a b F
omit [Fintype σ] in
lemma slot_choice_fixed_split :
    (∀ j i,((slotChoiceSplit L T).symm (a,b) i).val≠F j) ↔
      (∀ j,∀ i : T,(a i).val≠F j) ∧ (∀ j,∀ i : {i // i∉T},(b i).val≠F j) := by
  constructor
  · intro h
    constructor
    pm_8547 slotChoiceSplit_active
    pm_8547 slotChoiceSplit_inactive
  · rintro ⟨ha,hb⟩ j i
    by_cases hi : i∈T
    pm_7076 slotChoiceSplit_active ha
    pm_7076 slotChoiceSplit_inactive hb

lemma slot_choice_mask_split (K : Ideal Eis) :
    (IsCoprime K (∏ i,((slotChoiceSplit L T).symm (a,b) i).val) ∧
      ∀ j i,((slotChoiceSplit L T).symm (a,b) i).val≠F j) ↔
    (IsCoprime K (∏ i : {i // i∉T},(b i).val) ∧ ∀ j,∀ i : {i // i∉T},(b i).val≠F j) ∧
      (IsCoprime K (∏ i : T,(a i).val) ∧ ∀ j,∀ i : T,(a i).val≠F j) := by
  rw [slot_choice_coprime_split,slot_choice_fixed_split]
  tauto
end

end
end SevenEighths.InverseReflectedPhase

end OAI
