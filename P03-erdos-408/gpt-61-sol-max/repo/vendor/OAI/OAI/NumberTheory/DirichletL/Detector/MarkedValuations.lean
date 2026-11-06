module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.HighExcludedEuler
public import OAI.NumberTheory.DirichletL.Detector.EulerMarked

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic UniqueFactorizationMonoid ProbeCompleted

local notation "Id" => Ideal ActualEisensteinCubic.O

lemma prime_dvd_iff_valuation  P   I  (hI : I≠0) :
    P.val∣I ↔ primeValuations I P≠0 := by
  rw [primeValuations_apply,Multiset.count_ne_zero,mem_normalizedFactors_iff hI]
  exact ⟨fun h=>⟨P.property,h⟩,fun h=>h.2⟩

lemma prime_dvd_high_completed  P   v  :
    P.val∣(highIdeals v).1.1*(highIdeals v).1.2^3 ↔ (v P).1.1+3*(v P).1.2≠0 := by
  have hI : (highIdeals v).1.1≠0 := idealFromValuations_ne_zero _
  have hJ : (highIdeals v).1.2≠0 := idealFromValuations_ne_zero _
  rw [prime_dvd_iff_valuation P _ (mul_ne_zero hI (pow_ne_zero _ hJ)),
    primeValuations_mul _ _ hI (pow_ne_zero _ hJ),primeValuations_pow]
  simp_all [highIdeals]

lemma primeProduct_dvd (T : Finset PrimeIdeal)  I  :
    (∏P∈T,P.val)∣I ↔ ∀P∈T,P.val∣I := { mp := fun h P hP => Dvd.dvd.trans (Finset.dvd_prod_of_mem Subtype.val hP) h, mpr := Finset.prod_dvd_of_coprime fun P x Q x_1 => OAI.SevenEighths.ProbePhysical.primeIdeal_coprime P Q }

def completedValuationMark (_P : PrimeIdeal) (b : HighValuation) : ℂ :=
  if b.1.1+3*b.1.2≠0 then 1 else 0

lemma completedValuationMark_norm  _P   b  :
    ‖completedValuationMark _P b‖≤1 := by
  unfold completedValuationMark
  split_ifs <;> norm_num

lemma completedValuationMark_product  T   v  :
    (∏P∈T,completedValuationMark P (v P))=
      if (∏P∈T,P.val)∣(highIdeals v).1.1*(highIdeals v).1.2^3 then 1 else 0 := by
  rw [primeProduct_dvd]
  simp only [prime_dvd_high_completed]
  by_cases h : ∀P∈T,(v P).1.1+3*(v P).1.2≠0
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro P hP
    exact ite_eq_left (h P hP)
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨P,hP,hv⟩ := h
    apply Finset.prod_eq_zero hP
    simp_all [completedValuationMark]

lemma highIdealMask_mark  S   D I J K L  :
    highIdealMask S D I J K L=(if D∣I*J^3 then 1 else 0)*highIdealMask S 1 I J K L := by
  unfold highIdealMask completedMask
  simp only [one_dvd,true_and]
  split_ifs <;> simp_all

lemma markedIdealHighSummand_mark  S   D   η 
     u   x w z   I J K L  :
    markedIdealHighSummand S D η u x w z I J K L=
      (if D∣I*J^3 then 1 else 0)*markedIdealHighSummand S 1 η u x w z I J K L := by
  rw [markedIdealHighSummand,highIdealMask_mark,markedIdealHighSummand,mul_assoc]

end SevenEighths.ProbePhysical
end

end OAI
