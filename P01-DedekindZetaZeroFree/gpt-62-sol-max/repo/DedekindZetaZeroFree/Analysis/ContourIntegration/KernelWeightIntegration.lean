module

public import DedekindZetaZeroFree.Analysis.GaussianWeightConvolution

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.KernelWeightIntegration

noncomputable section

open DedekindZetaZeroFree MeasureTheory DedekindZetaZeroFree.Quantitative.WeightConvolution

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem one_add_abs_rpow_integrable (B : ℝ) (hB : 1 < B) :
    Integrable (fun t : ℝ => (1 + |t|) ^ (-B)) volume := by
  have := integrable_one_add_norm (μ := volume) (E := ℝ) (r := B) (by norm_num; linarith)
  simpa [Real.norm_eq_abs] using this

theorem joint_integral_bound (a₁ b₁ a₂ b₂ x₀ x₁ : ℝ) (ha₁ : 0 < a₁) (hab₁ : a₁ ≤ b₁)
    (hab₂ : a₂ ≤ b₂) (hx : x₀ ≤ x₁) (B k : ℝ) (hB : 0 < B) (hk : 0 ≤ k) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ ξ : ℂ, x₀ ≤ ξ.re → ξ.re ≤ x₁ →
      ∀ v y : ℝ, a₁ ≤ v → v ≤ b₁ → a₂ ≤ y → y ≤ b₂ →
      ∀ (C : ℝ), 0 ≤ C → ∀ Fn : ℝ × ℝ → ℂ, AEStronglyMeasurable Fn volume →
        (∀ p, ‖Fn p‖ ≤ C * weightModulus D ξ v y p * (2 + |p.1| + |p.2| + |ξ.im|) ^ k) →
        Integrable Fn volume ∧
          ‖∫ p, Fn p‖ ≤ C * Cw * (1 + |ξ.im|) ^ (-B) := by
  obtain ⟨C, hC0, hdec⟩ := weight_kernel_decay D a₁ b₁ a₂ b₂ x₀ x₁ ha₁ hab₁ hab₂ hx B k hB hk
  refine ⟨C, hC0, fun ξ hx0 hx1 v y hv1 hv2 hy1 hy2 Cc hCc Fn hmeas hbd => ?_⟩
  obtain ⟨hint, hle⟩ := hdec ξ hx0 hx1 v y hv1 hv2 hy1 hy2
  have hI' : Integrable (fun p : ℝ × ℝ => Cc * (weightModulus D ξ v y p *
      (2 + |p.1| + |p.2| + |ξ.im|) ^ k)) volume := hint.const_mul Cc
  refine ⟨Integrable.mono' hI' hmeas (Filter.Eventually.of_forall fun p => by
    simpa only [mul_assoc] using hbd p), ?_⟩
  calc ‖∫ p, Fn p‖ ≤ ∫ p, ‖Fn p‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ p, Cc * (weightModulus D ξ v y p * (2 + |p.1| + |p.2| + |ξ.im|) ^ k) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => norm_nonneg _) hI'
          (Filter.Eventually.of_forall fun p => by simpa only [mul_assoc] using hbd p)
    _ = Cc * ∫ p, weightModulus D ξ v y p * (2 + |p.1| + |p.2| + |ξ.im|) ^ k :=
        integral_const_mul _ _
    _ ≤ Cc * (C * (1 + |ξ.im|) ^ (-B)) := mul_le_mul_of_nonneg_left hle hCc
    _ = Cc * C * (1 + |ξ.im|) ^ (-B) := by ring

theorem nested_integral_bound (a₁ b₁ a₂ b₂ x₀ x₁ : ℝ) (ha₁ : 0 < a₁) (hab₁ : a₁ ≤ b₁)
    (hab₂ : a₂ ≤ b₂) (hx : x₀ ≤ x₁) (B k : ℝ) (hB : 0 < B) (hk : 0 ≤ k) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ ξ : ℂ, x₀ ≤ ξ.re → ξ.re ≤ x₁ →
      ∀ v y : ℝ, a₁ ≤ v → v ≤ b₁ → a₂ ≤ y → y ≤ b₂ →
      ∀ (C : ℝ), 0 ≤ C → ∀ G : ℂ → ℂ → ℂ,
        AEStronglyMeasurable (fun p : ℝ × ℝ =>
          G ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I)) volume →
        (∀ p : ℝ × ℝ, ‖G ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖ ≤
          C * weightModulus D ξ v y p * (2 + |p.1| + |p.2| + |ξ.im|) ^ k) →
        Integrable (fun p : ℝ × ℝ =>
          G ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I)) volume ∧
        (∀ᵐ t : ℝ ∂volume, Integrable (fun s : ℝ =>
          G ((y : ℂ) + (t : ℂ) * Complex.I) ((v : ℂ) + (s : ℂ) * Complex.I)) volume) ∧
        Integrable (fun t : ℝ =>
          comparisonVerticalIntegral v (fun z => G ((y : ℂ) + (t : ℂ) * Complex.I) z)) volume ∧
        ‖comparisonVerticalIntegral y (fun w => comparisonVerticalIntegral v (fun z => G w z))‖ ≤
          ((2 * Real.pi)⁻¹) ^ 2 * (C * Cw * (1 + |ξ.im|) ^ (-B)) := by
  obtain ⟨Cw, hCw0, hCw⟩ := joint_integral_bound D a₁ b₁ a₂ b₂ x₀ x₁ ha₁ hab₁ hab₂ hx B k hB hk
  refine ⟨Cw, hCw0, fun ξ hx0 hx1 v y hv1 hv2 hy1 hy2 C hC G hmeas hbd => ?_⟩
  obtain ⟨hint, hle⟩ := hCw ξ hx0 hx1 v y hv1 hv2 hy1 hy2 C hC
    (fun p : ℝ × ℝ => G ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I))
    hmeas hbd
  have hle' : ‖∫ p : ℝ × ℝ, G ((y : ℂ) + (p.2 : ℂ) * Complex.I)
      ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖ ≤ C * Cw * (1 + |ξ.im|) ^ (-B) := hle
  have hint' : Integrable (fun p : ℝ × ℝ =>
      G ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I))
      (volume.prod volume) := hint
  have hfub : ∫ p : ℝ × ℝ, G ((y : ℂ) + (p.2 : ℂ) * Complex.I) ((v : ℂ) + (p.1 : ℂ) * Complex.I)
      = ∫ t : ℝ, ∫ s : ℝ, G ((y : ℂ) + (t : ℂ) * Complex.I) ((v : ℂ) + (s : ℂ) * Complex.I) :=
    integral_prod_symm _ hint'
  refine ⟨hint, hint'.prod_left_ae, ?_, ?_⟩
  · simp only [comparisonVerticalIntegral]
    exact (hint'.integral_prod_right).const_mul _
  · have e : comparisonVerticalIntegral y (fun w => comparisonVerticalIntegral v (fun z => G w z))
        = (2 * (Real.pi : ℂ))⁻¹ * ((2 * (Real.pi : ℂ))⁻¹ *
          ∫ p : ℝ × ℝ, G ((y : ℂ) + (p.2 : ℂ) * Complex.I)
            ((v : ℂ) + (p.1 : ℂ) * Complex.I)) := by
      rw [hfub]
      simp only [comparisonVerticalIntegral, integral_const_mul]
    have hpi : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
    have h2 : ((2 * (Real.pi : ℂ))⁻¹) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) := by push_cast; ring
    rw [e, h2, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi]
    calc (2 * Real.pi)⁻¹ * ((2 * Real.pi)⁻¹ * ‖∫ p : ℝ × ℝ, G ((y : ℂ) + (p.2 : ℂ) * Complex.I)
            ((v : ℂ) + (p.1 : ℂ) * Complex.I)‖)
        ≤ (2 * Real.pi)⁻¹ * ((2 * Real.pi)⁻¹ * (C * Cw * (1 + |ξ.im|) ^ (-B))) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle' hpi) hpi
      _ = ((2 * Real.pi)⁻¹) ^ 2 * (C * Cw * (1 + |ξ.im|) ^ (-B)) := by ring


end

end DedekindZetaZeroFree.Quantitative.KernelWeightIntegration
