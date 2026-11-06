module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.GramGcd

@[expose] public section

namespace OAI


open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentCorrelation CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

section
variable (C n₁ n₂ j : O) (hC : Supported (Ideal.span {C})) (h₁ : Supported (Ideal.span {n₁})) (h₂ : Supported (Ideal.span {n₂}))

lemma actual_common_frequency_zero  
       
      (hj : ¬C∣j) :
    actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
      (supported_mul_elements C n₂ hC h₂) j=0 := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero C hC) (supported_element_ne_zero n₁ h₁))
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero C hC) (supported_element_ne_zero n₂ h₂))
  let : Fintype (O⧸Ideal.span {C*n₁}) := Fintype.ofFinite _
  let : Fintype (O⧸Ideal.span {C*n₂}) := Fintype.ofFinite _
  exact fullModulusCorrelation_eq_zero_of_common_not_dvd _ _ C j _ _
    (dvd_mul_right _ _) (dvd_mul_right _ _) hj

lemma tsum_element_divisible   (hC : C≠0) (f : O→ℂ) :
    (∑'j : O,if C∣j then f j else 0)=∑'k : O,f (C*k) := by
  have hinj : Function.Injective (fun k : O=>C*k) := fun _ _ h=>mul_left_cancel₀ hC h
  have hs : Function.support (fun j : O=>if C∣j then f j else 0)⊆Set.range (fun k : O=>C*k) := by
    intro j hj
    have hd : C∣j := by by_contra h;simp [h] at hj
    obtain ⟨k,rfl⟩ := hd
    exact ⟨k,rfl⟩
  have ht := hinj.tsum_eq hs
  calc
    _ = ∑'k : O,if C∣C*k then f (C*k) else 0 := ht.symm
    _ = _ := by simp only [dvd_mul_right,ite_true]

theorem actual_common_frequency_tsum  
       
      (W : O→ℂ) :
    (∑'j : O,actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
      (supported_mul_elements C n₂ hC h₂) j*W j)=
      ∑'k : O,actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
        (supported_mul_elements C n₂ hC h₂) (C*k)*W (C*k) := by
  rw [←tsum_element_divisible C (supported_element_ne_zero C hC) (fun j=>
    actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
      (supported_mul_elements C n₂ hC h₂) j*W j)]
  apply tsum_congr
  simp_all [actual_common_frequency_zero]

end

end SevenEighths.ProbeGramCommon


end OAI
