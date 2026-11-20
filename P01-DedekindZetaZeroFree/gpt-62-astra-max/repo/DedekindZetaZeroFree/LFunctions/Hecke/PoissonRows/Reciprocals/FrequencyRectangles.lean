module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.FrequencyDetector
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Reciprocals.FrequencySubpowerBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.FrequencyRightBounds

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawReciprocal31

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawDetectorHeightPrefix31
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (D : FixedData S η)

theorem raw_reciprocal_right :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Frequency D.recipe, u ≠ principalFrequency D.recipe →
      ∀ ξ : ℂ, Scales.rightLine ≤ ξ.re →
        (FixedData.pkg D).minus u ξ ≠ 0 ∧ ‖((FixedData.pkg D).minus u ξ)⁻¹‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := RawRightHecke31.minus_right D Scales.rightLine (by rw [Scales.rightLine_eq]; norm_num)
  exact ⟨C, hC, fun u _ ξ hξ => ⟨(h u ξ hξ).1, (h u ξ hξ).2.2⟩⟩

end

end DedekindZetaZeroFree.Quantitative.RawReciprocal31
