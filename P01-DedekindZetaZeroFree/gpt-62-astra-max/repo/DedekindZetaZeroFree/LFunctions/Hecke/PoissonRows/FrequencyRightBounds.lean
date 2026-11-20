module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.MaskedIdentification
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.RightBounds

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawRightHecke31

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (D : FixedData S η)

section

variable (σ : ℝ) (hσ : 1 < σ)

include hσ in
theorem plus_right :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Frequency D.recipe) (w : ℂ), σ ≤ w.re →
      (RawFixed.FixedData.pkg D).plus u w ≠ 0 ∧
        ‖(RawFixed.FixedData.pkg D).plus u w‖ ≤ C ∧
        ‖((RawFixed.FixedData.pkg D).plus u w)⁻¹‖ ≤ C := by
  refine ⟨Real.exp ((3 / 2 : ℝ) * ∑' I : NonzeroIdeal F, (idealNorm I.val) ^ (-σ)),
    Real.exp_pos _, fun u w hw => ?_⟩
  rw [(RawFixed.FixedData.pkg D).plus_eq u w (by linarith)]
  exact RightHeckeBounds.euler_data _
    (AllRowEuler.InitialSeparation.raw_plus_isCoefficient
      ((RawFixed.FixedData.pkg D).U u)) σ hσ w hw

include hσ in
theorem minus_right :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Frequency D.recipe) (ξ : ℂ), σ ≤ ξ.re →
      (RawFixed.FixedData.pkg D).minus u ξ ≠ 0 ∧
        ‖(RawFixed.FixedData.pkg D).minus u ξ‖ ≤ C ∧
        ‖((RawFixed.FixedData.pkg D).minus u ξ)⁻¹‖ ≤ C := by
  refine ⟨Real.exp ((3 / 2 : ℝ) * ∑' I : NonzeroIdeal F, (idealNorm I.val) ^ (-σ)),
    Real.exp_pos _, fun u ξ hξ => ?_⟩
  rw [(RawFixed.FixedData.pkg D).minus_eq u ξ (by linarith)]
  exact RightHeckeBounds.euler_data _
    (AllRowEuler.InitialSeparation.raw_minus_isCoefficient
       ((RawFixed.FixedData.pkg D).U u)) σ hσ ξ hξ

end

theorem recipe_L_right (σ : ℝ) (hσ : 1 / 6 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, σ ≤ z.re →
      D.recipe.L (6 * z) ≠ 0 ∧ ‖D.recipe.L (6 * z)‖ ≤ C ∧ ‖(D.recipe.L (6 * z))⁻¹‖ ≤ C := by
  obtain ⟨C1, hC1, h1⟩ := RightHeckeBounds.zetaSCont_norm_le_right D (6 * σ) (by linarith)
  obtain ⟨C2, h2⟩ := RightHeckeBounds.zetaSCont_inv_norm_le_right D (6 * σ) (by linarith)
  refine ⟨max C1 C2, lt_max_of_lt_left hC1, fun z hz => ?_⟩
  have hre : (6 * z).re = 6 * z.re := by simp
  have hz6 : 6 * σ ≤ (6 * z).re := by rw [hre]; linarith
  refine ⟨RightHeckeBounds.zetaSCont_ne_zero_of_one_lt D (6 * z) (by linarith),
    (h1 (6 * z) hz6).trans (le_max_left _ _), (h2 (6 * z) hz6).trans (le_max_right _ _)⟩

end

end DedekindZetaZeroFree.Quantitative.RawRightHecke31
