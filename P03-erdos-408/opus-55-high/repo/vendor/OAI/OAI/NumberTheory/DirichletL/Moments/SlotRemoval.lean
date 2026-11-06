module

public import OAI.NumberTheory.DirichletL.Hecke.DetectorSlotSelection

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.CenteredMomentSlotRemoval

theorem whole_slot_removal {α : Type*} (s : Finset α) (length : α → ℝ)
    (η κ F : ℝ) (hη : 0 ≤ η) (hκ : 0 < κ) (hF : 0 ≤ F)
    (hL : ∀ i ∈ s, 0 ≤ length i) (hmesh : ∀ i ∈ s, length i ≤ η) :
    ∃ R : Finset α, R ⊆ s ∧
      (∑ i ∈ R, length i) ≤ min (∑ i ∈ s, length i) (F/(6*κ)+η) ∧
      (R=s ∨ F ≤ 6*κ*(∑ i ∈ R, length i)) := by
  have hthreshold : 0 ≤ F/(6*κ) := by positivity
  by_cases htotal : (∑ i ∈ s, length i) ≤ F/(6*κ)
  · grind
  · have htarget : 0 ≤ (∑ i ∈ s, length i)-F/(6*κ) := by linarith
    obtain ⟨T,hTs,hTupper,hTlower⟩ := HeckeDetectorSlotSelection.whole_slots
      s length (fun _ => 1) 1 η (by norm_num) hη hL hmesh
      (by simp) (by simp) 1
      ((∑ i ∈ s, length i)-F/(6*κ)) (by norm_num) (by norm_num)
      htarget (by linarith) (by simp)
    simp only [one_mul,mul_one] at hTlower
    have hsum : (∑ i ∈ s, length i)=(∑ i ∈ s\T, length i)+(∑ i ∈ T, length i) :=
      (Finset.sum_sdiff hTs).symm
    have hTnonneg : 0 ≤ ∑ i ∈ T, length i := Finset.sum_nonneg (by grind)
    refine ⟨s\T,Finset.sdiff_subset,by grind,Or.inr ?_⟩
    have hremove : F/(6*κ) ≤ ∑ i ∈ s\T, length i := by linarith
    exact (div_le_iff₀ (by positivity)).mp hremove |>.trans_eq (by linarith)

end SevenEighths.CenteredMomentSlotRemoval

end

end OAI
