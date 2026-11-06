module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.DivisorTensor

@[expose] public section

namespace OAI


open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorSlots
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentHeckeSlots HeckeFamily

variable {ι : Type*} [DecidableEq ι]

section
variable (η : Character) (m A z : ActualEisensteinCubic.O) (t : ℝ) (D P : Ideal ActualEisensteinCubic.O) (hP : Prime P) (hPD : P∣D) (S : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀ I ∈ S, Prime I) (β : Ideal ActualEisensteinCubic.O → ℂ)


include hP hPD hS in
theorem selected_slot_exact      
         
          :
    rowSlot η m A z S (fun I => if D∣I then β I else 0) t =
      if P ∈ S ∧ D∣P then β P*rowWeight η m A z t P else 0 := by
  rw [rowSlot_eq_weight]
  have hz (I : Ideal ActualEisensteinCubic.O) (hI : I ∈ S) (hne : I ≠ P) :
      (if D∣I then β I else 0)*rowWeight η m A z t I=0 := by
    have hnd : ¬D∣I := fun hd => hne ((prime_dvd_prime_iff_eq hP (hS I hI)).mp (hPD.trans hd)).symm
    simp only [ite_eq_right hnd,zero_mul]
  by_cases hmem : P ∈ S
  · rw [Finset.sum_eq_single P (hz) (fun h => (h hmem).elim)]
    grind
  · rw [Finset.sum_eq_zero (fun I hI => hz I hI (fun he => hmem (he ▸ hI)))]
    simp only [hmem,false_and,ite_false]

include hP hPD hS in
theorem selected_slot_bound      
         
       
       M  (hM : 0 ≤ M) (hβ : ∀ I ∈ S, ‖β I‖ ≤ M) :
    ‖rowSlot η m A z S (fun I => if D∣I then β I else 0) t‖ ≤ M := by
  rw [selected_slot_exact η m A z t D P hP hPD S hS β]
  split_ifs with h
  · rw [norm_mul]
    exact (mul_le_mul (hβ P h.1) (row_twisted_coefficient_norm η m A z t P hP.ne_zero)
      (norm_nonneg _) hM).trans_eq (mul_one M)
  · simpa only [norm_zero] using hM

theorem selectedDivisor_empty   (s : Finset ι)  a   i 
    (he : selectedPrimes D s a i=∅) : selectedDivisor D s a i=1 := by
  simp only [selectedDivisor,he,Finset.prod_empty]

end

end SevenEighths.CenteredMomentDivisorSlots



end OAI
