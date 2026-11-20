module

public import DedekindZetaZeroFree.Eisenstein.Induction.Cusps.IncomingSheetEvaluation

@[expose] public section

noncomputable section
open scoped Classical NumberField

namespace DedekindZetaZeroFree.KPContinuation.ChamberModerateGrowth

open KPContFlatCuspIncomingEvaluation

private lemma norm_card_inv_mul_sum_le {ι : Type*} [Fintype ι]
    (f : ι → ℂ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ i, ‖f i‖ ≤ C) :
    ‖(Fintype.card ι : ℂ)⁻¹ * ∑ i, f i‖ ≤ C := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · rw [(Finset.sum_eq_zero (fun i _ => ((Fintype.card_eq_zero_iff.mp h0).false i).elim)), mul_zero, norm_zero]; exact hC
  · have h1 : ‖((Fintype.card ι : ℂ))⁻¹‖ = (Fintype.card ι : ℝ)⁻¹ := by
      rw [norm_inv, Complex.norm_natCast]
    rw [norm_mul, h1]
    have hsum : ‖∑ i, f i‖ ≤ (Fintype.card ι : ℝ) * C := by
      calc _ ≤ ∑ i, ‖f i‖ := norm_sum_le _ _
        _ ≤ ∑ _i : ι, C := Finset.sum_le_sum (fun i _ => hf i)
        _ = Fintype.card ι * C := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc _
        ≤ (Fintype.card ι : ℝ)⁻¹ * ((Fintype.card ι : ℝ) * C) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = C := by field_simp

private alias chi_norm_aux := DedekindZetaZeroFree.KPContSectorCoveredQuotientVocabulary.chi_norm

theorem zeroProjection_norm_le
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (e : rootsOfUnity 3 F → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (he : ∀ ε, ‖e ε‖ ≤ B) :
    ∀ q : KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a,
      ‖(KPContFlatCuspIncomingEvaluation.zeroProjection F ζ hζ C R P H U a e).val q‖ ≤ B := by
  intro q
  rw [KPContFlatCuspIncomingEvaluation.zeroProjection_formula]
  letI : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _
  let TranslationDeck₀ := TranslationDeck F ζ hζ C R P H U a
  letI : Finite (TranslationDeck₀) :=
    (monodromy F ζ hζ C R P H U a).finite_deck
  letI : Fintype (TranslationDeck₀) := Fintype.ofFinite _
  let centralLevel₀ := KPContSectorPhaseComponentCharts.centralLevel F ζ hζ (atlasLevel F ζ hζ C R P H U)
  letI : Fintype (centralLevel₀) := Fintype.ofFinite _
  rw [projectedScalar]
  have hA : ‖(Fintype.card (TranslationDeck₀) : ℂ)⁻¹ *
      ∑ q : TranslationDeck₀,
        deckCoefficient F ζ hζ C R P H U a q‖ ≤ 1 := by
    apply norm_card_inv_mul_sum_le _ 1 zero_le_one
    intro q
    rw [deckCoefficient, norm_inv, chi_norm_aux F ζ hζ _]
    norm_num
  have hBc : ‖(Fintype.card (centralLevel₀) : ℂ)⁻¹ *
      ∑ η : centralLevel₀,
        (KPCuspGenuineMonodromy.chi F ζ hζ η.val : ℂ)⁻¹‖ ≤ 1 := by
    apply norm_card_inv_mul_sum_le _ 1 zero_le_one
    intro η
    rw [norm_inv, chi_norm_aux F ζ hζ _]
    norm_num
  have hD : ‖(Fintype.card (rootsOfUnity 3 F) : ℂ)⁻¹ *
      ∑ ε : rootsOfUnity 3 F,
        (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ)⁻¹ * e ε‖ ≤ B := by
    apply norm_card_inv_mul_sum_le _ B hB
    intro ε
    rw [norm_mul, norm_inv, chi_norm_aux F ζ hζ ε, inv_one, one_mul]
    exact he ε
  calc _
      = _ * _ * _ := by rw [norm_mul, norm_mul]
    _ ≤ 1 * 1 * B := by
        apply mul_le_mul
        · apply mul_le_mul hA hBc (norm_nonneg _) zero_le_one
        · exact hD
        · exact norm_nonneg _
        · positivity
    _ = B := by ring

end DedekindZetaZeroFree.KPContinuation.ChamberModerateGrowth

end
