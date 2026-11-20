module
public import OAI.NumberTheory.DirichletL.Detector.LowSeparated
public import OAI.NumberTheory.DirichletL.Moments.Cauchy

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

def lowNumeratorWeight (C : CalibrationData) (Ω : ℝ→ℂ) (X Y : ℝ) (m : O) (v : ℝ) : ℂ :=
  Ω (elementNorm m/lowPhysicalScale C X Y)*C.residueMonoid m*
    ((elementNorm m/lowPhysicalScale C X Y:ℝ):ℂ)^(-((v:ℂ)*Complex.I))

lemma lowOuterCutoff_norm (a b x : ℝ) : ‖lowOuterCutoff a b x‖≤1 := by
  rw [lowOuterCutoff,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (Real.smoothTransition.nonneg _),abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact (mul_le_of_le_one_left (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _)

lemma lowNumeratorWeight_norm (C : CalibrationData) (Ω : ℝ→ℂ)
    (hΩ : ∀x,‖Ω x‖≤1) (hΩ0 : Ω 0=0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (m : O) (v : ℝ) :
    ‖lowNumeratorWeight C Ω X Y m v‖≤1 := by
  by_cases hm : m=0
  · simp [lowNumeratorWeight,hm,elementNorm,hΩ0]
  have hmpos : 0<elementNorm m := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hm))
  have he : -((v:ℂ)*Complex.I)=((-v:ℝ):ℂ)*Complex.I := by simp
  rw [lowNumeratorWeight,norm_mul,norm_mul,he,
    low_mellin_phase_norm _ (-v) (div_pos hmpos (lowPhysicalScale_pos C X Y hX hY)),mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hΩ _)).trans (C.residueMonoid_norm_le_one m)

end SevenEighths.ProbePhysical
end

end OAI
