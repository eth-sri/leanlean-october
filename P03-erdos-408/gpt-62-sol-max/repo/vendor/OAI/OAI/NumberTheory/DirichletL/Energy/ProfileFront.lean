module

public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPair

@[expose] public section

namespace OAI.SevenEighths

open CenteredMomentFiniteProfileExceptional

/-- The common smooth-profile and height factor in the Gaussian coefficients. -/
noncomputable abbrev gaussianFront {a b : ℝ} (p : Profiles a b) (U : Finset (ℕ × ℕ))
    (J : ℕ) (C C₀ C₁ t height : ℝ) : ℝ :=
  C * (C₀ + C₁ + 1) * (p.control U)^2 * (1 + |t| + height)^J

lemma front_mono {a b:ℝ}(p:Profiles a b)(U V:Finset (ℕ×ℕ))(hUV:U⊆V)
    (J K:ℕ)(hJK:J≤K)(c d C₀ C₁ t height:ℝ)
    (hc:0≤c)(hcd:c≤d)(hC₀:0≤C₀)(hC₁:0≤C₁)(hh:0≤height):
    gaussianFront p U J c C₀ C₁ t height ≤ gaussianFront p V K d C₀ C₁ t height := by
  unfold gaussianFront
  have hp := p.control_mono hUV
  have hp0:=p.control_nonneg U
  have hp1:=p.control_nonneg V
  have ht:(1+|t|+height)^J≤(1+|t|+height)^K:=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hJK
  have hd:0≤d:=hc.trans hcd
  gcongr

/-- A termwise comparison of the Gaussian weights with a common mass and volume. -/
lemma gaussian_sum_mono {a b P E : Fin 4 → ℝ} {V M : ℝ}
    (h : ∀ j, a j ≤ b j) (hP : ∀ j, 0 ≤ P j) (hV : 0 ≤ V) :
    (∑ j, a j * P j * V ^ E j) * M^2 ≤ (∑ j, b j * P j * V ^ E j) * M^2 :=
  mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (h j) (hP j))
      (Real.rpow_nonneg hV _)) (sq_nonneg M)

end OAI.SevenEighths
