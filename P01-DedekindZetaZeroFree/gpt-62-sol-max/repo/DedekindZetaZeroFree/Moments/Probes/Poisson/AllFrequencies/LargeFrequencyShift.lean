module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Reciprocals.FrequencyRectangles
public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllFrequencies.LargeZControls
public import DedekindZetaZeroFree.Analysis.FrequencyPowerTails
public import DedekindZetaZeroFree.Moments.Principal.Contour.WShift

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawLargeRowShift31

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory Set Filter Complex
open DedekindZetaZeroFree.PrincipalMellinComparison
open PrincipalWShift (cvi_congr cvi_iter_eq sec3)
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawFixed.FixedData
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

theorem raw_large_row_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Frequency D.recipe), u ≠ principalFrequency D.recipe →
      ∀ (Z : ℝ), 2 ≤ Z →
        initialRowIntegral D u Z = triple D u 4 4 Scales.tailShift Z ∧
        ‖initialRowIntegral D u Z‖ ≤
          C * Z ^ ((44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift) *
            frequencyNorm D.recipe u ^ (-Scales.tailShift + ε) := by
  obtain ⟨C, hC, H⟩ := RawLargeZControls31.triple_norm_le D ε hε
  have hE : Scales.kernelExponent 4 4 Scales.tailShift =
      (44675 / 10000 : ℝ) + 33 / 100 * Scales.tailShift := by
    unfold Scales.kernelExponent Scales.xExponent Scales.yExponent Scales.smoothingExponent
    ring
  let c : ℂ := ((2 * (Real.pi : ℂ))⁻¹) ^ 3
  refine ⟨(‖c‖ + 1) * C, by positivity, fun u hu Z hZ => ?_⟩
  have hshift : initialRowIntegral D u Z = triple D u 4 4 Scales.tailShift Z := by
    unfold initialRowIntegral triple Iwz
    exact cvi_congr fun _ => cvi_congr fun _ =>
      RawLargeZControls31.Iz_shift_two_R D u hu Z hZ _ _ (by simp) (by simp)
  refine ⟨hshift, ?_⟩
  obtain ⟨hint, hb⟩ := H u hu Z hZ
  rw [hE] at hb
  let G (a b d : ℝ) := rawKernel D u (4 + (a : ℂ) * I) (4 + (b : ℂ) * I)
    ((Scales.tailShift : ℂ) + (d : ℂ) * I) Z
  have h := (integral_congr_ae (sec3 G hint).2.1).trans (integral_prod _ hint).symm
  rw [hshift]
  simp only [triple, Iwz, Iz]
  rw [cvi_iter_eq]
  simp only [Complex.ofReal_ofNat]
  change ‖c * (∫ a : ℝ, ∫ b : ℝ, ∫ d : ℝ, G a b d)‖ ≤ _
  rw [h, norm_mul]
  have hnonneg := (integral_nonneg (fun t : ℝ × ℝ × ℝ => norm_nonneg (G t.1 t.2.1 t.2.2))).trans hb
  calc
    _ ≤ ‖c‖ * _ := mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans hb) (norm_nonneg c)
    _ ≤ (‖c‖ + 1) * _ := mul_le_mul_of_nonneg_right (by linarith [norm_nonneg c]) hnonneg
    _ = _ := by ring

end

end DedekindZetaZeroFree.Quantitative.RawLargeRowShift31
