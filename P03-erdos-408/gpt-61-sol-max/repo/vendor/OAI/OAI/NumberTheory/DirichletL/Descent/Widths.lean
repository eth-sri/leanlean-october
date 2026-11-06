module
import Batteries.Tactic.Alias
import OAI.NumberTheory.DirichletL.Moments.FirstScale

public import OAI.NumberTheory.DirichletL.Foundation

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss



alias actual_ideal_norm_pos := _root_.OAI.SevenEighths.CenteredMomentFirstScale.norm_pos

theorem actual_residual_norm_width  I Q  (hI : I ≠ 0) :
    (Ideal.absNorm (rowResidualPart I Q) : ℝ) *
      (Ideal.absNorm (rowPowerfulPart I) : ℝ) ≤ (Ideal.absNorm I : ℝ) := by
  have hm : 1 ≤ (Ideal.absNorm (rowMaskPart I Q) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz =>
      squarefreeMaskPart_ne_zero (rowSimplePart I) Q (Ideal.absNorm_eq_zero_iff.mp hz))
  have he := congrArg (fun J : Ideal ActualEisensteinCubic.O => (Ideal.absNorm J : ℝ))
    (row_powerful_mask_residual_product I Q hI)
  simp only [map_mul, Nat.cast_mul] at he
  calc
    _ ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ) *
        (Ideal.absNorm (rowMaskPart I Q) : ℝ) * (Ideal.absNorm (rowResidualPart I Q) : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hm
        (show 0 ≤ (Ideal.absNorm (rowResidualPart I Q) : ℝ) *
          (Ideal.absNorm (rowPowerfulPart I) : ℝ) by positivity)
      nlinarith [hh]
    _ = _ := he

section
variable {ι : Type*} [Fintype ι]

theorem actual_common_width_charge    
    (I F Q : Ideal ActualEisensteinCubic.O) (hI : I ≠ 0) (hQ : Q ≠ 0)
    (P : ι → Ideal ActualEisensteinCubic.O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * Q)
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I Q)  e  :
    (Ideal.absNorm (rowResidualPart I Q) : ℝ)^2 *
      reflectionConductorCost P (fun i => completedLocalExponent I F (P i)) e ≤
      (Ideal.absNorm I : ℝ)^2 / (Ideal.absNorm (rowPowerfulPart I) : ℝ) *
        (Ideal.absNorm Q : ℝ) := by
  have hp := actual_ideal_norm_pos (rowPowerfulPart I) (rowPowerfulPart_ne_zero I)
  have hm := actual_ideal_norm_pos (rowMaskPart I Q)
    (squarefreeMaskPart_ne_zero (rowSimplePart I) Q)
  have he := rowResidualPart_norm I Q hI
  calc
    _ ≤ (Ideal.absNorm (rowResidualPart I Q) : ℝ)^2 *
        ((Ideal.absNorm (rowPowerfulPart I) : ℝ) *
          (Ideal.absNorm (rowMaskPart I Q) : ℝ)^2 * (Ideal.absNorm Q : ℝ)) :=
      mul_le_mul_of_nonneg_left (reflectionConductorCost_bound I F Q hI hQ P hcop hpool hres e)
        (sq_nonneg _)
    _ = _ := by rw [he]; field_simp

theorem actual_common_width_charge_label_puncture    
    (I F rho S : Ideal ActualEisensteinCubic.O) (hI : I ≠ 0) (hF : F ≠ 0) (hrho : rho ≠ 0) (hS : S ≠ 0)
    (P : ι → Ideal ActualEisensteinCubic.O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * (S * F * rho))
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I (S * F * rho))  e  :
    (Ideal.absNorm (rowResidualPart I (S * F * rho)) : ℝ)^2 *
      reflectionConductorCost P (fun i => completedLocalExponent I F (P i)) e ≤
      (Ideal.absNorm S : ℝ) *
        ((Ideal.absNorm I : ℝ)^2 / (Ideal.absNorm (rowPowerfulPart I) : ℝ)) *
        (Ideal.absNorm F : ℝ) * (Ideal.absNorm rho : ℝ) := by
  convert actual_common_width_charge I F (S * F * rho) hI
    (mul_ne_zero (mul_ne_zero hS hF) hrho) P hcop hpool hres e using 1
  simp only [map_mul, Nat.cast_mul]
  ring

end


end SevenEighths.InverseMoment

end OAI
