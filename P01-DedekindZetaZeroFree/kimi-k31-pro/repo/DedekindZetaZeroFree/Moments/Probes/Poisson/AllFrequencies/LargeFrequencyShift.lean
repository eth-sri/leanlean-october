module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Reciprocals.FrequencyRectangles
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllFrequencies.LargeZControls
public import DedekindZetaZeroFree.Analysis.FrequencyPowerTails

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawLargeRowShift31

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory Set Filter Complex
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawFixed.FixedData
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

theorem raw_z_shift (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 2 ≤ Z) (ξ w : ℂ) (hξ : ξ.re = 4) (hw : w.re = 4) :
    Iz D u ξ w 2 Z = Iz D u ξ w Scales.tailShift Z :=
  DedekindZetaZeroFree.Quantitative.RawLargeZControls31.Iz_shift_two_R D u hu Z hZ ξ w hξ hw

private lemma cvi_congr {σ : ℝ} {f g : ℂ → ℂ}
    (h : ∀ t : ℝ, f ((σ : ℂ) + (t : ℂ) * Complex.I) = g ((σ : ℂ) + (t : ℂ) * Complex.I)) :
    comparisonVerticalIntegral σ f = comparisonVerticalIntegral σ g := by
  unfold comparisonVerticalIntegral
  grind

theorem raw_Iwz_shift (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 2 ≤ Z) (ξ : ℂ) (hξ : ξ.re = 4) :
    Iwz D u ξ 4 2 Z = Iwz D u ξ 4 Scales.tailShift Z := by
  unfold Iwz
  refine cvi_congr (fun t => ?_)
  exact raw_z_shift D u hu Z hZ ξ _ hξ (by simp)

theorem raw_initialRowIntegral_shift (u : Frequency D.recipe)
    (hu : u ≠ principalFrequency D.recipe) (Z : ℝ) (hZ : 2 ≤ Z) :
    initialRowIntegral D u Z = triple D u 4 4 Scales.tailShift Z := by
  unfold initialRowIntegral triple
  refine cvi_congr (fun t => ?_)
  exact raw_Iwz_shift D u hu Z hZ _ (by simp)

theorem raw_large_triple_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Frequency D.recipe), u ≠ principalFrequency D.recipe →
      ∀ (Z : ℝ), 2 ≤ Z →
      Integrable (fun t : ℝ × ℝ × ℝ =>
        rawKernel D u ((4 : ℂ) + (t.1 : ℂ) * I) ((4 : ℂ) + (t.2.1 : ℂ) * I)
          (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) Z) ∧
      ∫ t : ℝ × ℝ × ℝ, ‖rawKernel D u ((4 : ℂ) + (t.1 : ℂ) * I) ((4 : ℂ) + (t.2.1 : ℂ) * I)
          (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * I) Z‖ ≤
        C * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) *
          frequencyNorm D.recipe u ^ (-Scales.tailShift + ε) := by
  obtain ⟨C, hC, H⟩ := DedekindZetaZeroFree.Quantitative.RawLargeZControls31.triple_norm_le D ε hε
  refine ⟨C, hC, fun u hu Z hZ => ?_⟩
  obtain ⟨h1, h2⟩ := H u hu Z hZ
  refine ⟨h1, h2.trans ?_⟩
  have hZ0 : 0 < Z := by linarith
  have hE : Z ^ (Scales.kernelExponent 4 4 Scales.tailShift) ≤ Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    unfold Scales.kernelExponent Scales.xExponent Scales.yExponent Scales.smoothingExponent
    linarith
  have hq : 0 ≤ frequencyNorm D.recipe u ^ (-Scales.tailShift + ε) :=
    Real.rpow_nonneg (by linarith [RawFrequencyCount.one_le_frequencyNorm D.recipe u]) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hC.le) hq

private lemma iter_triple (g : ℝ → ℝ → ℝ → ℂ)
    (hg : MeasureTheory.Integrable (fun t : ℝ × ℝ × ℝ => g t.1 t.2.1 t.2.2)) :
    ∫ a : ℝ, ∫ b : ℝ, ∫ c : ℝ, g a b c = ∫ t : ℝ × ℝ × ℝ, g t.1 t.2.1 t.2.2 := by
  have h1 : ∀ᵐ a : ℝ ∂MeasureTheory.volume,
      MeasureTheory.Integrable (fun y : ℝ × ℝ => g a y.1 y.2) MeasureTheory.volume :=
    MeasureTheory.Integrable.prod_right_ae hg
  calc ∫ a : ℝ, ∫ b : ℝ, ∫ c : ℝ, g a b c
      = ∫ a : ℝ, ∫ y : ℝ × ℝ, g a y.1 y.2 := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [h1] with a ha
        exact (MeasureTheory.integral_prod (fun y : ℝ × ℝ => g a y.1 y.2) ha).symm
    _ = ∫ t : ℝ × ℝ × ℝ, g t.1 t.2.1 t.2.2 :=
        (MeasureTheory.integral_prod (fun t : ℝ × ℝ × ℝ => g t.1 t.2.1 t.2.2) hg).symm

theorem raw_large_row_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Frequency D.recipe), u ≠ principalFrequency D.recipe →
      ∀ (Z : ℝ), 2 ≤ Z →
        initialRowIntegral D u Z = triple D u 4 4 Scales.tailShift Z ∧
        ‖initialRowIntegral D u Z‖ ≤
          C * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) *
            frequencyNorm D.recipe u ^ (-Scales.tailShift + ε) := by
  obtain ⟨C0, hC0, H⟩ := raw_large_triple_bound D ε hε
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ‖(2 * (Real.pi : ℂ))⁻¹‖ *
      (‖(2 * (Real.pi : ℂ))⁻¹‖ * ‖(2 * (Real.pi : ℂ))⁻¹‖) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  refine ⟨(A + 1) * C0, by positivity, fun u hu Z hZ => ⟨raw_initialRowIntegral_shift D u hu Z hZ, ?_⟩⟩
  obtain ⟨hint, hb⟩ := H u hu Z hZ
  rw [raw_initialRowIntegral_shift D u hu Z hZ]
  have h := iter_triple (fun a b c => rawKernel D u ((4 : ℂ) + (a : ℂ) * Complex.I)
    ((4 : ℂ) + (b : ℂ) * Complex.I) (((Scales.tailShift : ℝ) : ℂ) + (c : ℂ) * Complex.I) Z) hint
  have hval : triple D u 4 4 Scales.tailShift Z =
      (2 * (Real.pi : ℂ))⁻¹ * ((2 * (Real.pi : ℂ))⁻¹ * ((2 * (Real.pi : ℂ))⁻¹ *
        ∫ t : ℝ × ℝ × ℝ,
          rawKernel D u ((4 : ℂ) + (t.1 : ℂ) * Complex.I) ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
            (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * Complex.I) Z)) := by
    rw [← h]
    simp only [triple, Iwz, Iz, comparisonVerticalIntegral, MeasureTheory.integral_const_mul,
      Complex.ofReal_ofNat]
  rw [hval]
  simp only [norm_mul]
  have h1 := (MeasureTheory.norm_integral_le_integral_norm _).trans hb
  have hn : 0 ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ := norm_nonneg _
  have hB : 0 ≤ C0 * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) *
      frequencyNorm D.recipe u ^ (-Scales.tailShift + ε) := by
    have := hb
    exact le_trans (MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)) this
  calc ‖(2 * (Real.pi : ℂ))⁻¹‖ * (‖(2 * (Real.pi : ℂ))⁻¹‖ * (‖(2 * (Real.pi : ℂ))⁻¹‖ *
        ‖∫ t : ℝ × ℝ × ℝ, rawKernel D u ((4 : ℂ) + (t.1 : ℂ) * Complex.I)
          ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
          (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * Complex.I) Z‖))
      = A * ‖∫ t : ℝ × ℝ × ℝ, rawKernel D u ((4 : ℂ) + (t.1 : ℂ) * Complex.I)
          ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
          (((Scales.tailShift : ℝ) : ℂ) + (t.2.2 : ℂ) * Complex.I) Z‖ := by grind
    _ ≤ A * (C0 * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) *
          frequencyNorm D.recipe u ^ (-Scales.tailShift + ε)) := mul_le_mul_of_nonneg_left h1 hA0
    _ ≤ (A + 1) * (C0 * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) *
          frequencyNorm D.recipe u ^ (-Scales.tailShift + ε)) :=
        mul_le_mul_of_nonneg_right (by linarith) hB
    _ = _ := by ring

end

end DedekindZetaZeroFree.Quantitative.RawLargeRowShift31
