module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencyData
public import DedekindZetaZeroFree.ZeroDetection.Conductors.Poisson.DenominatorFamily

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawDenominatorPackage31

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
open DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads
open DedekindZetaZeroFree.Quantitative.RawFixed
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

theorem primMinus_eq_denominator (u : Frequency D.recipe) :
    FixedData.primMinus D u = (RawDenominatorFamily31.denominatorFamily D.recipe).omega u := by
  have h := (RawDenominatorFamily31.denominatorFamily D.recipe).raw_minus u
    (FixedData.rawFrequency D u) (FixedData.rawFrequency_u D u)
  exact MinusArithmetic.deleted_primitive_inducers_eq D.recipe.A
    (RawHeckeRows.rawDeletionSet (FixedData.rawFrequency D u))
    (RawDenominatorExistence.rawDeletionSet_finite D.recipe (FixedData.rawFrequency D u))
    (RawDenominatorExistence.Sf_subset_rawDeletionSet D.recipe (FixedData.rawFrequency D u))
    _ _ (fun I => ((FixedData.pkg D).minus_mask u I).symm.trans (h I))

theorem primMinus_character_eq (u : Frequency D.recipe) (I : Ideal (𝓞 F)) :
    (FixedData.primMinus D u).character I =
      ((RawDenominatorFamily31.denominatorFamily D.recipe).omega u).character I := by
  rw [primMinus_eq_denominator D u]

theorem minus_conductor_sieve_finsum :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (U N : ℝ), 2 ≤ U → 2 ≤ N →
        ∀ (J : Finset (Frequency D.recipe)),
          (∀ u ∈ J, U ≤ frequencyNorm D.recipe u ∧ frequencyNorm D.recipe u < 2 * U) →
          ∀ b : Ideal (𝓞 F) → ℂ,
            (∀ I, b I ≠ 0 → I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ N) →
              (∑ u ∈ J,
                ‖∑ᶠ I : Ideal (𝓞 F), b I * (FixedData.primMinus D u).character I‖ ^ 2) ≤
                C * (N + U ^ 2) * (N * U) ^ ε * ∑ᶠ I : Ideal (𝓞 F), ‖b I‖ ^ 2 := by
  intro ε hε
  obtain ⟨C, hC, h⟩ := RawDenominatorFamily31.raw_conductor_sieve_finsum D.recipe ε hε
  refine ⟨C, hC, fun U N hU hN J hJ b hb => ?_⟩
  simp only [primMinus_character_eq D]
  exact h U N hU hN J hJ b hb

end

end DedekindZetaZeroFree.Quantitative.RawDenominatorPackage31
