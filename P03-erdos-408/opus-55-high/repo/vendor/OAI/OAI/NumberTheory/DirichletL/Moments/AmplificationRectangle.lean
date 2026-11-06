module

public import OAI.NumberTheory.DirichletL.Moments.AmplificationShortening

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.CenteredMomentAmplificationRectangle
open CenteredMomentAmplificationShortening

theorem centralRoot_extract (p : ActualEisensteinCubic.O) (hp : p ≠ 0) (k : ℕ) (T : ℝ) (hT : 0 < T) :
    (Real.sqrt T : ℂ)⁻¹ = (primeRoot p k)⁻¹ *
      (Real.sqrt (T / (Ideal.absNorm (Ideal.span {p}) : ℝ)^k) : ℂ)⁻¹ := by
  have hN : 0 < (Ideal.absNorm (Ideal.span {p}) : ℝ) := Nat.cast_pos.mpr
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp)))
  have hroot : Real.sqrt T = Real.sqrt ((Ideal.absNorm (Ideal.span {p}) : ℝ)^k) *
      Real.sqrt (T / (Ideal.absNorm (Ideal.span {p}) : ℝ)^k) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  rw [hroot,Complex.ofReal_mul,mul_inv,primeRoot]

end SevenEighths.CenteredMomentAmplificationRectangle

end

end OAI
