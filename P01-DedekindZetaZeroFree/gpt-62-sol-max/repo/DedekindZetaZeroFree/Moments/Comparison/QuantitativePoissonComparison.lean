module

public import DedekindZetaZeroFree.Moments.Principal.Contour.Comparison
public import DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencySumBound

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.Compare

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem c₀_ne_zero : Spectral.c₀ D ≠ 0 :=
  (Principal.principal_comparison D).1

theorem Iscale_sub_main_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖D.Iscale Z - Spectral.c₀ D * Spectral.f D Z‖ ≤ C * Z ^ (717 / 2000 : ℝ) := by
  obtain ⟨-, hJ, ⟨Cw, hCw, hw⟩, ⟨Cz, hCz, hz⟩, -, -⟩ := Principal.principal_comparison D
  obtain ⟨Cr, hCr, hr⟩ := RawNonprincipalRowsAssembly.nonprincipalSum_bound D
  have hexp1 : ∀ Z : ℝ, 2 ≤ Z → Z ^ (Scales.mainExponent - 37749867 / 1000000000) ≤ Z ^ (717 / 2000 : ℝ) := by
    intro Z hZ
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    norm_num [Scales.mainExponent]
  have hexp2 : ∀ Z : ℝ, 2 ≤ Z → Z ^ (Scales.mainExponent - 384999 / 10000000) ≤ Z ^ (717 / 2000 : ℝ) := by
    intro Z hZ
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    norm_num [Scales.mainExponent]
  refine ⟨Cw + Cz + Cr, by positivity, fun Z hZ => ?_⟩
  have h1 : D.Iscale Z - Spectral.c₀ D * Spectral.f D Z =
      PrincipalWShift.Rw D Z + PrincipalZShift.Rz D Z + RawInitialKernel31.nonprincipalSum D Z := by
    rw [RawInitialKernel31.Iscale_eq_principal_add_nonprincipal D Z (by linarith), hJ Z hZ]; ring
  rw [h1]
  have hp : 0 ≤ Z ^ (717 / 2000 : ℝ) := Real.rpow_nonneg (by linarith) _
  have a1 := (hw Z hZ).trans (mul_le_mul_of_nonneg_left (hexp1 Z hZ) hCw.le)
  have a2 := (hz Z hZ).trans (mul_le_mul_of_nonneg_left (hexp2 Z hZ) hCz.le)
  have a3 := hr Z hZ
  exact norm_add₃_le.trans (by linarith)

end

end DedekindZetaZeroFree.Quantitative.Compare
