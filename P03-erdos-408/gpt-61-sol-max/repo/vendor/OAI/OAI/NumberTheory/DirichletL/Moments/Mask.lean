module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Foundation
public import OAI.NumberTheory.DirichletL.Moments.Basic

@[expose] public section

namespace OAI


open scoped BigOperators Classical
open scoped ContDiff

namespace SevenEighths.CenteredMomentMask
open ActualEisensteinCubic IdealMobiusDivisorSum
open UniqueFactorizationMonoid

section
variable (I R : Ideal ActualEisensteinCubic.O) (hR : R ≠ 0) (D : Ideal ActualEisensteinCubic.O) (hD : D ≠ 0) (f : Ideal ActualEisensteinCubic.O → ℂ)

include hR in
theorem ideal_coprime_mobius     :
    (if IsCoprime I R then (1 : ℂ) else 0) =
      ∑ D ∈ idealDivisors R, if D ∣ I then (moebius D : ℂ) else 0 := by
  let G : Ideal ActualEisensteinCubic.O := R ⊔ I
  have hG : G ≠ 0 := by
    intro hz
    apply hR
    apply le_antisymm _ bot_le
    exact le_sup_left.trans_eq hz
  have hdiv : (idealDivisors R).filter (fun D => D ∣ I) = idealDivisors G := by
    ext D
    simp only [Finset.mem_filter, mem_idealDivisors hR, mem_idealDivisors hG,
      Ideal.dvd_iff_le, G, sup_le_iff]
  rw [← Finset.sum_filter, hdiv, sum_moebius_divisors G hG]
  simp only [Ideal.isCoprime_iff_sup_eq, G, sup_comm]

include hD in
theorem tsum_ideal_divisible       :
    (∑' I : Ideal ActualEisensteinCubic.O, if D ∣ I then f I else 0) =
      ∑' J : Ideal ActualEisensteinCubic.O, f (D * J) := by
  let F : Ideal ActualEisensteinCubic.O → ℂ := fun I => if D ∣ I then f I else 0
  have hrange : Function.support F ⊆ Set.range (fun J : Ideal ActualEisensteinCubic.O => D * J) := by
    intro I hI
    have hd : D ∣ I := by
      aesop
    obtain ⟨J, hJ⟩ := hd
    exact ⟨J, hJ.symm⟩
  have ht := (mul_right_injective₀ hD).tsum_eq hrange
  calc
    _ = ∑' J : Ideal ActualEisensteinCubic.O, F (D * J) := ht.symm
    _ = _ := by
      apply tsum_congr
      intro J
      simp only [F, dvd_mul_right, ite_true]

include hR in
theorem masked_ideal_sum_eq    
      (hf : Summable f) :
    (∑' I : Ideal ActualEisensteinCubic.O, (if IsCoprime I R then (1 : ℂ) else 0) * f I) =
      ∑ D ∈ idealDivisors R, (moebius D : ℂ) * ∑' J : Ideal ActualEisensteinCubic.O, f (D * J) := by
  have hterm (I : Ideal ActualEisensteinCubic.O) : (if IsCoprime I R then (1 : ℂ) else 0) * f I =
      ∑ D ∈ idealDivisors R, (moebius D : ℂ) * (if D ∣ I then f I else 0) := by
    rw [ideal_coprime_mobius I R hR, Finset.sum_mul]
    grind
  have hsum (D : Ideal ActualEisensteinCubic.O) :
      Summable (fun I : Ideal ActualEisensteinCubic.O => (moebius D : ℂ) * (if D ∣ I then f I else 0)) := by
    have h := (hf.indicator {I : Ideal ActualEisensteinCubic.O | D ∣ I}).mul_left (moebius D : ℂ)
    simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using h
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun D _ => hsum D)]
  apply Finset.sum_congr rfl
  intro D hD
  rw [tsum_mul_left, tsum_ideal_divisible D (ne_zero_of_dvd_ne_zero hR
    ((mem_idealDivisors hR).mp hD))]

theorem annular_ideal_sum_summable (χ : Ideal ActualEisensteinCubic.O → ℂ) (W : ℝ → ℂ)
    (b X : ℝ) (hX : 0 < X) (hs : Function.support W ⊆ Set.Iic b) :
    Summable (fun I : Ideal ActualEisensteinCubic.O => χ I * W ((Ideal.absNorm I : ℝ) / X)) := by
  apply summable_of_hasFiniteSupport
  apply (Ideal.finite_setOfPred_absNorm_le (S := ActualEisensteinCubic.O) (Nat.ceil (b * X))).subset
  intro I hI
  have hw : W ((Ideal.absNorm I : ℝ) / X) ≠ 0 := by
    intro hz
    exact hI (by simp only [hz, mul_zero])
  have hn : (Ideal.absNorm I : ℝ) ≤ b * X := (div_le_iff₀ hX).mp (hs hw)
  exact_mod_cast hn.trans (Nat.le_ceil (b * X))

include hR in
theorem masked_plain_ideal_sum    
    (χ : Ideal ActualEisensteinCubic.O →* ℂ) (W : ℝ → ℂ) (b X : ℝ) (hX : 0 < X)
    (hs : Function.support W ⊆ Set.Iic b) :
    (∑' I : Ideal ActualEisensteinCubic.O, (if IsCoprime I R then (1 : ℂ) else 0) *
        (χ I * W ((Ideal.absNorm I : ℝ) / X))) =
      ∑ D ∈ idealDivisors R, (moebius D : ℂ) * χ D *
        ∑' J : Ideal ActualEisensteinCubic.O, χ J * W ((Ideal.absNorm J : ℝ) / (X / Ideal.absNorm D)) := by
  rw [masked_ideal_sum_eq R hR _ (annular_ideal_sum_summable χ W b X hX hs)]
  apply Finset.sum_congr rfl
  intro D hD
  have hD0 : D ≠ 0 := ne_zero_of_dvd_ne_zero hR ((mem_idealDivisors hR).mp hD)
  
  have hterms (J : Ideal ActualEisensteinCubic.O) :
      χ (D * J) * W ((Ideal.absNorm (D * J) : ℝ) / X) =
        χ D * (χ J * W ((Ideal.absNorm J : ℝ) / (X / Ideal.absNorm D))) := by
    rw [map_mul, map_mul, Nat.cast_mul]
    field_simp <;> ring
  simp_rw [hterms]
  rw [tsum_mul_left]
  ring

end

theorem polynomial_mask_divisor_bound (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ R : Ideal ActualEisensteinCubic.O, R ≠ 0 →
      (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ((idealDivisors R).card : ℝ) ≤ C * Z ^ ε := by
  let δ := ε / (B + 1)
  have hden : 0 < B + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨C, hC, hcount⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨C, hC, ?_⟩
  intro Z hZ R hR hnorm
  have hexp : B * δ ≤ ε := by
    dsimp only [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  calc
    _ ≤ C * (Ideal.absNorm R : ℝ) ^ δ := hcount R hR
    _ ≤ C * (Z ^ B) ^ δ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hnorm hδ.le) hC.le
    _ = C * Z ^ (B * δ) := by rw [← Real.rpow_mul (by linarith : 0 ≤ Z)]
    _ ≤ C * Z ^ ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ hexp) hC.le

end SevenEighths.CenteredMomentMask


end OAI
