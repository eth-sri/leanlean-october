module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Foundation

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredExceptionalCount
open UniqueFactorizationMonoid


def valuation (I P : Ideal ActualEisensteinCubic.O)  := (normalizedFactors I).count P

def factorMultiset (I : Ideal ActualEisensteinCubic.O) (e : ℕ → ℕ)  :=
  ∑ P ∈ (normalizedFactors I).toFinset, Multiset.replicate (e (valuation I P)) P

section
variable (I P : Ideal ActualEisensteinCubic.O) (e : ℕ → ℕ)

theorem factorMultiset_subset     :
    factorMultiset I e ⊆ normalizedFactors I := by
  intro P hP
  obtain ⟨Q, hQ, hPQ⟩ := Multiset.mem_sum.mp hP
  have he : P = Q := (Multiset.mem_replicate.mp hPQ).2
  exact he ▸ Multiset.mem_toFinset.mp hQ

theorem factorMultiset_count     (he : e 0 = 0) :
    (factorMultiset I e).count P = e (valuation I P) := by
  unfold factorMultiset
  simp only [Multiset.count_sum', Multiset.count_replicate, Finset.sum_ite_eq']
  split_ifs with hP
  · rfl
  · have hz : valuation I P = 0 := Multiset.count_eq_zero.mpr
      (fun h => hP (Multiset.mem_toFinset.mpr h))
    rw [hz, he]

end

def factorPart (I : Ideal ActualEisensteinCubic.O) (e : ℕ → ℕ)  := (factorMultiset I e).prod

section
variable (I P : Ideal ActualEisensteinCubic.O) (e : ℕ → ℕ)

theorem factorPart_ne_zero     : factorPart I e ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors (factorMultiset_subset I e)

theorem factorPart_valuation     (he : e 0 = 0) :
    valuation (factorPart I e) P = e (valuation I P) := by
  unfold valuation factorPart
  rw [normalizedFactors_prod_eq_self_of_subset (factorMultiset_subset I e)]
  exact factorMultiset_count I P e he

end

def sixthRemainder (I : Ideal ActualEisensteinCubic.O)  := factorPart I (fun n => n % 6)

def sixthQuotient (I : Ideal ActualEisensteinCubic.O)  := factorPart I (fun n => n / 6)

section
variable (I J P : Ideal ActualEisensteinCubic.O)

theorem sixthRemainder_ne_zero   : sixthRemainder I ≠ 0 := factorPart_ne_zero I _
theorem sixthQuotient_ne_zero   : sixthQuotient I ≠ 0 := factorPart_ne_zero I _

@[simp] theorem sixthRemainder_valuation   :
    valuation (sixthRemainder I) P = valuation I P % 6 :=
  factorPart_valuation I P _ (by norm_num)

@[simp] theorem sixthQuotient_valuation   :
    valuation (sixthQuotient I) P = valuation I P / 6 :=
  factorPart_valuation I P _ (by norm_num)

theorem valuation_mul   (hI : I ≠ 0) (hJ : J ≠ 0) :
    valuation (I * J) P = valuation I P + valuation J P := by
  simp only [valuation, normalizedFactors_mul hI hJ, Multiset.count_add]

theorem valuation_pow    n  :
    valuation (I ^ n) P = n * valuation I P := by
  simp only [valuation, normalizedFactors_pow, Multiset.count_nsmul]

end

section
variable {I J : Ideal ActualEisensteinCubic.O} (hI : I ≠ 0) (hJ : J ≠ 0) {R : Ideal ActualEisensteinCubic.O}

include hI hJ in
theorem ideal_eq_of_valuation_eq      
    (h : ∀ P, valuation I P = valuation J P) : I = J := by
  rw [← Ideal.prod_normalizedFactors_eq_self hI, ← Ideal.prod_normalizedFactors_eq_self hJ]
  exact congrArg Multiset.prod (Multiset.ext.mpr h)

theorem sixth_normal_form  I  (hI : I ≠ 0) :
    sixthRemainder I * sixthQuotient I ^ 6 = I := by
  apply ideal_eq_of_valuation_eq
    (mul_ne_zero (sixthRemainder_ne_zero I) (pow_ne_zero _ (sixthQuotient_ne_zero I))) hI
  intro P
  rw [valuation_mul _ _ _ (sixthRemainder_ne_zero I)
    (pow_ne_zero _ (sixthQuotient_ne_zero I)), valuation_pow,
    sixthRemainder_valuation, sixthQuotient_valuation]
  omega

theorem sixthRemainder_valuation_lt  I P  : valuation (sixthRemainder I) P < 6 := by
  rw [sixthRemainder_valuation]
  omega

include hI hJ in
theorem sixthQuotient_injective_on_remainder  
        (hr : sixthRemainder I = sixthRemainder J)
    (hq : sixthQuotient I = sixthQuotient J) : I = J := by
  rw [← sixth_normal_form I hI, ← sixth_normal_form J hJ, hr, hq]

theorem sixthRemainder_eq_of_profile   (hR : R ≠ 0)
    (hprofile : ∀ P, valuation I P % 6 = valuation R P) : sixthRemainder I = R := by
  apply ideal_eq_of_valuation_eq (sixthRemainder_ne_zero I) hR
  intro P
  simpa only [sixthRemainder_valuation] using hprofile P

theorem forced_fourth_power_dvd  I D  (hD : Squarefree D)
    (hfour : ∀ P ∈ normalizedFactors D, valuation I P % 6 = 4) :
    D ^ 4 ∣ sixthRemainder I := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hD.ne_zero)
    (sixthRemainder_ne_zero I)).mpr
  apply Multiset.le_iff_count.mpr
  intro P
  change valuation (D ^ 4) P ≤ valuation (sixthRemainder I) P
  rw [valuation_pow, sixthRemainder_valuation]
  have hcount : valuation D P ≤ 1 := Multiset.nodup_iff_count_le_one.mp
    ((squarefree_iff_nodup_normalizedFactors hD.ne_zero).mp hD) P
  by_cases hP : P ∈ normalizedFactors D
  · rw [hfour P hP]
    omega
  simp_all [valuation]

include hI in
theorem norm_pos     : 0 < (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

include hI in
theorem norm_one_le     : 1 ≤ (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

include hJ in
theorem norm_le_of_dvd     (hIJ : I ∣ J) :
    (Ideal.absNorm I : ℝ) ≤ (Ideal.absNorm J : ℝ) := by
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun h => hJ (Ideal.absNorm_eq_zero_iff.mp h)))
    (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hIJ))

end

section
variable (I D : Ideal ActualEisensteinCubic.O) (hI : I ≠ 0)

theorem forced_fourth_power_norm_le   (hD : Squarefree D)
    (hfour : ∀ P ∈ normalizedFactors D, valuation I P % 6 = 4) :
    (Ideal.absNorm D : ℝ) ^ 4 ≤ (Ideal.absNorm (sixthRemainder I) : ℝ) := by
  simpa only [map_pow, Nat.cast_pow] using
    norm_le_of_dvd (sixthRemainder_ne_zero I) (forced_fourth_power_dvd I D hD hfour)

include hI in
theorem sixth_normal_form_norm     :
    (Ideal.absNorm (sixthRemainder I) : ℝ) *
      (Ideal.absNorm (sixthQuotient I) : ℝ) ^ 6 = (Ideal.absNorm I : ℝ) := by
  have h := congrArg (fun J : Ideal ActualEisensteinCubic.O => (Ideal.absNorm J : ℝ)) (sixth_normal_form I hI)
  simp_all

include hI in
theorem sixthQuotient_norm_le      {H}  (hH : 0 ≤ H)
    (hNI : (Ideal.absNorm I : ℝ) ≤ H) :
    (Ideal.absNorm (sixthQuotient I) : ℝ) ≤
      (H / Ideal.absNorm (sixthRemainder I)) ^ (1 / 6 : ℝ) := by
  have hr := norm_pos (sixthRemainder_ne_zero I)
  have hp : (Ideal.absNorm (sixthQuotient I) : ℝ) ^ (6 : ℝ) ≤
      H / Ideal.absNorm (sixthRemainder I) := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, le_div_iff₀ hr]
    rw [mul_comm, sixth_normal_form_norm I hI]
    exact hNI
  simpa only [one_div] using
    (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg _) (div_nonneg hH hr.le)
      (by norm_num : (0 : ℝ) < 6)).mpr hp

end

theorem ideal_count_fixed_remainder (S : Finset (Ideal ActualEisensteinCubic.O)) (R : Ideal ActualEisensteinCubic.O) (hR : R ≠ 0)
     H  (hH : 0 ≤ H) (hS : ∀ I ∈ S, I ≠ 0)
    (hrem : ∀ I ∈ S, sixthRemainder I = R)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ H) :
    (S.card : ℝ) ≤ 128 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) := by
  by_cases hne : S.Nonempty
  · have hqbound (I : Ideal ActualEisensteinCubic.O) (hI : I ∈ S) :
        (Ideal.absNorm (sixthQuotient I) : ℝ) ≤ (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) := by
      simpa only [hrem I hI] using sixthQuotient_norm_le I (hS I hI) hH (hN I hI)
    obtain ⟨I, hI⟩ := hne
    have hscale : 1 ≤ (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) :=
      (norm_one_le (sixthQuotient_ne_zero I)).trans (hqbound I hI)
    have hinj : Set.InjOn sixthQuotient S := by
      intro I hI J hJ he
      exact sixthQuotient_injective_on_remainder (hS I hI) (hS J hJ)
        ((hrem I hI).trans (hrem J hJ).symm) he
    have hc := DescentFiberCost.finite_ideal_count_real (S.image sixthQuotient)
      ((H / Ideal.absNorm R) ^ (1 / 6 : ℝ)) hscale
      (by intro J hJ; obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
          exact sixthQuotient_ne_zero I)
      (by intro J hJ; obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
          exact hqbound I hI)
    rwa [Finset.card_image_iff.mpr hinj] at hc
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
    positivity

section
variable (S : Finset ActualEisensteinCubic.O) (R : Ideal ActualEisensteinCubic.O) (hR : R ≠ 0) (Rs : Finset (Ideal ActualEisensteinCubic.O)) (hRs : ∀ R ∈ Rs, R ≠ 0) (H : ℝ) (hH : 0 ≤ H) (Z C m d : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C) (hRnorm : Z ^ d ≤ (Ideal.absNorm R : ℝ)) (hS : ∀ z ∈ S, z ≠ 0) (hrem : ∀ z ∈ S, sixthRemainder (Ideal.span {z}) = R)

include hS in
theorem element_count_le_six_ideal_count     :
    (S.card : ℝ) ≤ 6 * ((S.image (fun z => Ideal.span {z})).card : ℝ) := by
  have h := CompletedUnitRows.sum_nonzero_element_le_units S hS (fun _ => 1)
    (fun _ => by norm_num)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    CompletedUnitRows.unit_card, Nat.cast_ofNat] using h

include hR hH hS hrem in
theorem element_count_fixed_remainder      
         
     
    (hN : ∀ z ∈ S, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ H) :
    (S.card : ℝ) ≤ 768 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) := by
  have hc := ideal_count_fixed_remainder (S.image (fun z => Ideal.span {z})) R hR H hH
    (by intro I hI; obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
        exact Ideal.span_singleton_eq_bot.not.mpr (hS z hz))
    (by intro I hI; obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
        exact hrem z hz)
    (by intro I hI; obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
        exact hN z hz)
  calc
    (S.card : ℝ) ≤ 6 * ((S.image (fun z => Ideal.span {z})).card : ℝ) :=
      element_count_le_six_ideal_count S hS
    _ ≤ 6 * (128 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ)) := by gcongr
    _ = 768 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) := by ring

include hRs hH hS in
theorem element_count_remainder_family    
         
      (hrem : ∀ z ∈ S, sixthRemainder (Ideal.span {z}) ∈ Rs)
    (hN : ∀ z ∈ S, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ H) :
    (S.card : ℝ) ≤ ∑ R ∈ Rs, 768 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) := by
  rw [Finset.card_eq_sum_card_fiberwise (t := Rs) hrem, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro R hR
  exact element_count_fixed_remainder (S.filter (fun z => sixthRemainder (Ideal.span {z}) = R)) R
    (hRs R hR) H hH
    (fun z hz => hS z (Finset.mem_filter.mp hz).1)
    (fun z hz => (Finset.mem_filter.mp hz).2)
    (fun z hz => hN z (Finset.mem_filter.mp hz).1)

include hR hZ hC hRnorm hS hrem in
theorem element_count_power_scale      
         
       
     
    (hN : ∀ z ∈ S, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ m) :
    (S.card : ℝ) ≤ 768 * C ^ (1 / 6 : ℝ) * Z ^ ((m - d) / 6) := by
  have hM : 0 ≤ C * Z ^ m := mul_nonneg hC (Real.rpow_nonneg hZ.le _)
  have hdiv : (C * Z ^ m) / Ideal.absNorm R ≤ (C * Z ^ m) / Z ^ d :=
    div_le_div_of_nonneg_left hM (Real.rpow_pos_of_pos hZ _) hRnorm
  calc
    (S.card : ℝ) ≤ 768 * ((C * Z ^ m) / Ideal.absNorm R) ^ (1 / 6 : ℝ) :=
      element_count_fixed_remainder S R hR _ hM hS hrem hN
    _ ≤ 768 * ((C * Z ^ m) / Z ^ d) ^ (1 / 6 : ℝ) := by gcongr
    _ = 768 * C ^ (1 / 6 : ℝ) * Z ^ ((m - d) / 6) := by
      rw [mul_div_assoc, ← Real.rpow_sub hZ, Real.mul_rpow hC (Real.rpow_nonneg hZ.le _),
        ← Real.rpow_mul hZ.le]
      ring

theorem sixthRemainder_eq_of_prime_profile  {I R}  (hR : R ≠ 0)
    (hprofile : ∀ P, Prime P → valuation I P % 6 = valuation R P) :
    sixthRemainder I = R := by
  apply sixthRemainder_eq_of_profile hR
  intro P
  by_cases hP : Prime P
  · exact hprofile P hP
  · have hI0 : valuation I P = 0 := Multiset.count_eq_zero.mpr
      (fun h => hP (prime_of_normalized_factor P h))
    have hR0 : valuation R P = 0 := Multiset.count_eq_zero.mpr
      (fun h => hP (prime_of_normalized_factor P h))
    simp only [hI0, hR0, Nat.zero_mod]

include hRs hZ hC in
theorem element_count_power_scale_family    
           
    (hRnorm : ∀ R ∈ Rs, Z ^ d ≤ (Ideal.absNorm R : ℝ))
    (hS : ∀ z ∈ S, z ≠ 0) (hrem : ∀ z ∈ S, sixthRemainder (Ideal.span {z}) ∈ Rs)
    (hN : ∀ z ∈ S, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ m) :
    (S.card : ℝ) ≤ 768 * (Rs.card : ℝ) * C ^ (1 / 6 : ℝ) * Z ^ ((m - d) / 6) := by
  have hcard : (S.card : ℝ) =
      ∑ R ∈ Rs, ((S.filter (fun z => sixthRemainder (Ideal.span {z}) = R)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise (t := Rs) hrem
  rw [hcard]
  calc
    _ ≤ ∑ R ∈ Rs, 768 * C ^ (1 / 6 : ℝ) * Z ^ ((m - d) / 6) := by
      apply Finset.sum_le_sum
      intro R hR
      exact element_count_power_scale
        (S.filter (fun z => sixthRemainder (Ideal.span {z}) = R)) R (hRs R hR)
        Z C m d hZ hC (hRnorm R hR)
        (fun z hz => hS z (Finset.mem_filter.mp hz).1)
        (fun z hz => (Finset.mem_filter.mp hz).2)
        (fun z hz => hN z (Finset.mem_filter.mp hz).1)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end

end SevenEighths.CenteredExceptionalCount
end

end OAI
