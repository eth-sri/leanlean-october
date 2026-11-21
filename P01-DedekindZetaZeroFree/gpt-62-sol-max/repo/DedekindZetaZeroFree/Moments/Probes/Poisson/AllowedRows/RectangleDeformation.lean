module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.ExceptionalPrefix
public import DedekindZetaZeroFree.ZeroDetection.ExceptionalZeros.Poisson.RightHalfPlane
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRowCount
public import DedekindZetaZeroFree.ZeroDetection.Conductors.Poisson.MaximalSieve
public import DedekindZetaZeroFree.ZeroDetection.ExceptionalZeros.Poisson.CountCore
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.AnalyticContinuation
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Reciprocals.LogarithmicDisks
public import DedekindZetaZeroFree.Analysis.Complex.ThreeCircles
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Reciprocals.EulerBounds
public import DedekindZetaZeroFree.Analysis.ContourIntegration.KernelWeightIntegration
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.KernelHolomorphy

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RowRectangleDeformation

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory DedekindZetaZeroFree.Quantitative.PoissonKernel
  DedekindZetaZeroFree.Quantitative.DetectorDef DedekindZetaZeroFree.Quantitative.DetectorHeight
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem rect_cauchy (f : ℂ → ℂ) (a b T : ℝ)
    (hf : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc (-T) T)) :
    (∫ σ in a..b, f ((σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
      (∫ σ in a..b, f ((σ : ℂ) + (T : ℂ) * Complex.I)) +
      Complex.I * (∫ t in (-T)..T, f ((b : ℂ) + (t : ℂ) * Complex.I)) -
      Complex.I * (∫ t in (-T)..T, f ((a : ℂ) + (t : ℂ) * Complex.I)) = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ((b : ℂ) + (T : ℂ) * Complex.I) (by simpa using hf)
  simpa using h



theorem rect_decomp (f : ℂ → ℂ) (a b T : ℝ) (hab : a ≤ b) (hT : 0 ≤ T)
    (hf : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc (-T) T))
    (hint : Integrable (fun t : ℝ => f ((b : ℂ) + (t : ℂ) * Complex.I))) :
    (2 * (Real.pi : ℂ))⁻¹ * (∫ t : ℝ, f ((b : ℂ) + (t : ℂ) * Complex.I)) =
      (2 * (Real.pi : ℂ))⁻¹ * (∫ t in Set.Icc (-T) T, f ((a : ℂ) + (t : ℂ) * Complex.I)) +
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (∫ σ in a..b, f ((σ : ℂ) + ((1 * T : ℝ) : ℂ) * Complex.I)) +
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (∫ σ in b..a, f ((σ : ℂ) + (((-1) * T : ℝ) : ℂ) * Complex.I)) +
      (2 * (Real.pi : ℂ))⁻¹ *
        (∫ t in {t : ℝ | T < |t|}, f ((b : ℂ) + (t : ℂ) * Complex.I)) := by
  have hC := rect_cauchy f a b T hf
  have hsplit : ∫ t : ℝ, f ((b : ℂ) + (t : ℂ) * Complex.I) =
      (∫ t in Set.Icc (-T) T, f ((b : ℂ) + (t : ℂ) * Complex.I)) +
        ∫ t in {t : ℝ | T < |t|}, f ((b : ℂ) + (t : ℂ) * Complex.I) := by
    have hc : {t : ℝ | T < |t|} = (Set.Icc (-T) T)ᶜ := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le]
      constructor
      · intro h
        rcases lt_abs.mp h with h | h
        · right; exact h
        · left; linarith
      · rintro (h | h)
        · exact lt_of_lt_of_le (by linarith) (neg_le_abs t)
        · exact lt_of_lt_of_le h (le_abs_self t)
    rw [hc]
    exact (integral_add_compl measurableSet_Icc hint).symm
  have hIcc : ∀ g : ℝ → ℂ, ∫ t in Set.Icc (-T) T, g t = ∫ t in (-T)..T, g t := by
    intro g
    rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hsplit, hIcc, hIcc, intervalIntegral.integral_symm a b]
  simp only [one_mul, neg_mul, Complex.ofReal_neg] at hC ⊢
  have hRL : Complex.I * (∫ t in (-T)..T, f ((b : ℂ) + (t : ℂ) * Complex.I)) =
      Complex.I * (∫ t in (-T)..T, f ((a : ℂ) + (t : ℂ) * Complex.I)) +
        ((∫ σ in a..b, f ((σ : ℂ) + (T : ℂ) * Complex.I)) -
          ∫ σ in a..b, f ((σ : ℂ) + -((T : ℂ) * Complex.I))) := by
    linear_combination hC
  have hR : (∫ t in (-T)..T, f ((b : ℂ) + (t : ℂ) * Complex.I)) =
      (∫ t in (-T)..T, f ((a : ℂ) + (t : ℂ) * Complex.I)) +
        Complex.I⁻¹ * ((∫ σ in a..b, f ((σ : ℂ) + (T : ℂ) * Complex.I)) -
          ∫ σ in a..b, f ((σ : ℂ) + -((T : ℂ) * Complex.I))) := by
    rw [← inv_mul_cancel_left₀ hI (∫ t in (-T)..T, f ((b : ℂ) + (t : ℂ) * Complex.I)), hRL,
      mul_add, inv_mul_cancel_left₀ hI]
  rw [hR]
  ring


end

end DedekindZetaZeroFree.Quantitative.RowRectangleDeformation
