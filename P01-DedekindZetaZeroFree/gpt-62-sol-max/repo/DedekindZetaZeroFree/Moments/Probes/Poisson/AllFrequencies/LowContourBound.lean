module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.KernelNorm
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllFrequencies.GoodKernelBounds
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllFrequencies.LowXiControls

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawLowRowBound31

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory Set Filter Complex
open DedekindZetaZeroFree.PrincipalMellinComparison
  DedekindZetaZeroFree.Quantitative.RawLowXiControls31
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawFixed.FixedData
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

private theorem vertical_norm_le' (G : ℂ → ℂ) (x A B : ℝ) (hB : 1 < B)
    (h : ∀ t : ℝ, ‖G ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A * (1 + |t|) ^ (-B)) :
    ‖comparisonVerticalIntegral x G‖ ≤
      (2 * Real.pi)⁻¹ * (A * ∫ t : ℝ, (1 + |t|) ^ (-B)) := by
  have hI : Integrable (fun t : ℝ => (1 + |t|) ^ (-B)) volume :=
    KernelWeightIntegration.one_add_abs_rpow_integrable B hB
  have hpi : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
  unfold comparisonVerticalIntegral
  have h2 : ((2 * (Real.pi : ℂ))⁻¹) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [h2, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi]
  apply mul_le_mul_of_nonneg_left _ hpi
  calc ‖∫ t : ℝ, G ((x : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ∫ t : ℝ, ‖G ((x : ℂ) + (t : ℂ) * Complex.I)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, A * (1 + |t|) ^ (-B) := integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun t => norm_nonneg _) (hI.const_mul A)
          (Filter.Eventually.of_forall fun t => h t)
    _ = A * ∫ t : ℝ, (1 + |t|) ^ (-B) := integral_const_mul _ _

private theorem triple_bound_of_majorant (k : ℝ) (hk : 0 ≤ k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
      (Z : ℝ) (hZ : 0 < Z) (Cc : ℝ) (hCc : 0 ≤ Cc),
      (∀ (ξ : ℂ), ξ.re = Scales.rightLine → ∀ p : ℝ × ℝ,
        ‖rawKernel D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
          ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ ≤
          Cc * WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
            (2 + |p.1| + |p.2| + |ξ.im|) ^ k) →
      ‖triple D u Scales.rightLine Scales.wLine Scales.zLine Z‖ ≤ K * Cc := by
  obtain ⟨C, hC, h⟩ := Iwz_bound_of_majorant D Scales.rightLine Scales.rightLine 2 k le_rfl two_pos hk
  obtain ⟨_, _, hne⟩ := RawReciprocal31.raw_reciprocal_right D
  have hI0 : 0 ≤ ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ)) := integral_nonneg (fun _ => by positivity)
  refine ⟨(2 * Real.pi)⁻¹ * (C * ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ))), by positivity, ?_⟩
  intro u hu Z hZ M hM hmaj
  have hv := vertical_norm_le' (fun ξ => Iwz D u ξ Scales.wLine Scales.zLine Z) Scales.rightLine (C * M) 2
    (by norm_num) (fun t => by
    let ξ : ℂ := (Scales.rightLine : ℂ) + (t : ℂ) * I
    have hre : ξ.re = Scales.rightLine := by simp [ξ]
    have hpad : Scales.goodLine - EulerDomain.pad ≤ ξ.re := by
      rw [hre]
      norm_num [Scales.goodLine, EulerDomain.pad, Scales.rightLine_eq]
    simpa [ξ] using h u hu Z hZ ξ hre.ge hre.le hpad (hne u hu ξ hre.ge).1 M hM (hmaj ξ hre))
  calc
    _ ≤ _ := hv
    _ = _ := by ring

theorem raw_low_dyad_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Frequency D.recipe), u ≠ principalFrequency D.recipe →
      ∀ U : ℝ, 2 ≤ U → U ≤ frequencyNorm D.recipe u → frequencyNorm D.recipe u < 2 * U →
      ∀ Z : ℝ, 2 ≤ Z →
        ‖triple D u Scales.rightLine Scales.wLine Scales.zLine Z‖ ≤
          C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ ((1 : ℝ) / 25 + ε) := by
  obtain ⟨A, ρ, hA, hconv, -⟩ := RawDetectorHeightPrefix31.height_exists D
  obtain ⟨C0, hC0, hmaj⟩ := RawGoodKernelBounds31.rawKernel_majorant_right D A hA hconv ε hε
  obtain ⟨K, hK0, hK⟩ := triple_bound_of_majorant D A hA
  refine ⟨K * C0 + 1, by positivity, ?_⟩
  intro u hu U hU hUq hUq2 Z hZ
  have hZ0 : 0 < Z := by linarith
  have hZp : 0 ≤ Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) := Real.rpow_nonneg hZ0.le _
  have hUp : 0 ≤ U ^ ((1 : ℝ) / 25 + ε) := Real.rpow_nonneg (by linarith) _
  have hCc : 0 ≤ C0 * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ ((1 : ℝ) / 25 + ε) :=
    mul_nonneg (mul_nonneg hC0.le hZp) hUp
  have := hK u hu Z hZ0 _ hCc (fun ξ hξ p => by
    have h1 := hmaj U hU u hu hUq hUq2 ξ Z p hZ0 hξ
    have hw : 0 ≤ WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p := norm_nonneg _
    have hP : (2 + |p.2|) ^ A ≤ (2 + |p.1| + |p.2| + |ξ.im|) ^ A :=
      Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg p.1, abs_nonneg ξ.im]) hA
    calc _ ≤ _ := h1
      _ = (C0 * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ ((1 : ℝ) / 25 + ε)) *
          WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p * (2 + |p.2|) ^ A := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hP
          (mul_nonneg (mul_nonneg (mul_nonneg hC0.le hZp) hUp) hw))
  calc _ ≤ _ := this
    _ = (K * C0) * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ ((1 : ℝ) / 25 + ε) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hZp) hUp

theorem raw_low_fixed_row_bound (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe) :
    ∃ Cu : ℝ, 0 ≤ Cu ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖triple D u Scales.rightLine Scales.wLine Scales.zLine Z‖ ≤ Cu * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) := by
  obtain ⟨C, k, hC, hk, hb⟩ := RawLowXiControls31.rawKernel_weight_bound D u hu 2 (by norm_num)
  obtain ⟨K, hK0, hK⟩ := triple_bound_of_majorant D k hk
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine := ⟨_, rfl⟩
  rw [← hE]
  refine ⟨K * ((2 : ℝ) ^ E)⁻¹ * C, by positivity, ?_⟩
  intro Z hZ
  have hZ0 : 0 < Z := by linarith
  have hZp : 0 ≤ Z ^ E := Real.rpow_nonneg hZ0.le _
  have h2p : 0 < (2 : ℝ) ^ E := Real.rpow_pos_of_pos (by norm_num) _
  have hCc : 0 ≤ Z ^ E * ((2 : ℝ) ^ E)⁻¹ * C := by positivity
  have := hK u hu Z hZ0 _ hCc (fun ξ hξ p => by
    have hx : 1 + Scales.contourOffset / 2 ≤ ξ.re := by
      rw [hξ]; unfold Scales.rightLine Scales.contourOffset; norm_num
    have hx5 : ξ.re ≤ 5 := by rw [hξ, Scales.rightLine_eq]; norm_num
    have h1 : ‖rawKernel D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
          ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) 2‖ ≤
        C * WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p *
          (2 + |p.1| + |p.2| + |ξ.im|) ^ k := hb ξ hx hx5 p.1 p.2
    have n1 := RawKernelNorm.norm_rawKernel D u ξ Scales.zLine Scales.wLine p Z hZ0
    have n2 := RawKernelNorm.norm_rawKernel D u ξ Scales.zLine Scales.wLine p 2 (by norm_num)
    rw [hξ, ← hE] at n1 n2
    have hw : 0 ≤ WeightConvolution.weightModulus D ξ Scales.zLine Scales.wLine p := norm_nonneg _
    have hq : 0 < frequencyNorm D.recipe u ^ (-Scales.zLine) :=
      Real.rpow_pos_of_pos (RawKernelNorm.frequencyNorm_pos D u) _
    have hrat : ‖rawKernel D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
          ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) Z‖ = Z ^ E * ((2 : ℝ) ^ E)⁻¹ *
        ‖rawKernel D u ξ ((Scales.wLine : ℂ) + (p.2 : ℂ) * Complex.I)
          ((Scales.zLine : ℂ) + (p.1 : ℂ) * Complex.I) 2‖ := by
      rw [n1, n2]
      have key : ∀ a b c d e : ℝ, e ≠ 0 → a * b * c * d = a * e⁻¹ * (e * b * c * d) := by
        intro a b c d e he; field_simp
      exact key _ _ _ _ _ h2p.ne'
    rw [hrat]
    have hnn : 0 ≤ Z ^ E * ((2 : ℝ) ^ E)⁻¹ := by positivity
    calc _ ≤ _ := mul_le_mul_of_nonneg_left h1 hnn
      _ = _ := by ring)
  calc _ ≤ _ := this
    _ = _ := by ring

end

end DedekindZetaZeroFree.Quantitative.RawLowRowBound31
