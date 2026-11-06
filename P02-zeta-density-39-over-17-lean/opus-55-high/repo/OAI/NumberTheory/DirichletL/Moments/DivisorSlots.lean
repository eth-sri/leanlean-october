module
public import OAI.NumberTheory.DirichletL.Moments.DivisorTensor

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorSlots
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentHeckeSlots HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

section
variable (η : Character) (m A z : O) (t : ℝ) (D P : Ideal O) (hP : Prime P) (hPD : P∣D) (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Prime I) (β : Ideal O → ℂ)
include η m A z t D P hP hPD S hS β
theorem selected_slot_exact :
    rowSlot η m A z S (fun I => if D∣I then β I else 0) t =
      if P ∈ S ∧ D∣P then β P*rowWeight η m A z t P else 0 := by
  rw [rowSlot_eq_weight]
  have hz (I : Ideal O) (hI : I ∈ S) (hne : I ≠ P) :
      (if D∣I then β I else 0)*rowWeight η m A z t I=0 := by
    have hnd : ¬D∣I := fun hd => hne ((prime_dvd_prime_iff_eq hP (hS I hI)).mp (hPD.trans hd)).symm
    grind
  by_cases hmem : P ∈ S
  · rw [Finset.sum_eq_single P (fun I hI hne => hz I hI hne) (fun h => (h hmem).elim)]
    by_cases hd : D∣P <;> simp only [hmem,hd,and_self,true_and,ite_true,ite_false,zero_mul]
  · rw [Finset.sum_eq_zero (fun I hI => hz I hI (fun he => hmem (he ▸ hI)))]
    simp only [hmem,false_and,ite_false]

theorem selected_slot_bound (M : ℝ) (hM : 0 ≤ M) (hβ : ∀ I ∈ S, ‖β I‖ ≤ M) :
    ‖rowSlot η m A z S (fun I => if D∣I then β I else 0) t‖ ≤ M := by
  rw [selected_slot_exact η m A z t D P hP hPD S hS β]
  split_ifs with h
  · rw [norm_mul]
    exact (mul_le_mul (hβ P h.1) (row_twisted_coefficient_norm η m A z t P hP.ne_zero)
      (norm_nonneg _) hM).trans_eq (mul_one M)
  · simpa only [norm_zero] using hM
end

theorem selectedDivisor_empty (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι)
    (he : selectedPrimes D s a i=∅) : selectedDivisor D s a i=1 := by
  simp only [selectedDivisor,he,Finset.prod_empty]

end SevenEighths.CenteredMomentDivisorSlots

end

end OAI
