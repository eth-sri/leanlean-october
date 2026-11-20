module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FixedData

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawFrequencyCount

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

alias freqOrbit_injective := DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.PrimitiveDenominatorRectanglesAndDyadicCounts.freqOrbit_injective

alias freqOrbit_norm := DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.PrimitiveDenominatorRectanglesAndDyadicCounts.freqOrbit_norm

alias one_le_frequencyNorm := DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.PrimitiveDenominatorRectanglesAndDyadicCounts.one_le_frequencyNorm

alias frequency_count_le := DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.PrimitiveDenominatorRectanglesAndDyadicCounts.freq_count_linear

theorem frequency_count_lt (R : PrincipalMellin.ActualRecipe S η) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 1 ≤ X →
      {u : Frequency R | frequencyNorm R u < X}.Finite ∧
      (Set.ncard {u : Frequency R | frequencyNorm R u < X} : ℝ) ≤ K * X := by
  obtain ⟨K, hK, h⟩ := frequency_count_le R
  refine ⟨K, hK, fun X hX => ?_⟩
  obtain ⟨hfin, hcard⟩ := h X hX
  have hsub : {u : Frequency R | frequencyNorm R u < X} ⊆
      {u : Frequency R | frequencyNorm R u ≤ X} :=
    fun _ hu => le_of_lt (Set.mem_setOf_eq.mp hu)
  exact ⟨hfin.subset hsub,
    (Nat.cast_le.mpr (Set.ncard_le_ncard hsub hfin)).trans hcard⟩

theorem frequency_dyad_count (R : PrincipalMellin.ActualRecipe S η) :
    ∃ K : ℝ, 0 < K ∧ ∀ U : ℝ, 1 ≤ U →
      {u : Frequency R | U ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * U}.Finite ∧
      (Set.ncard {u : Frequency R | U ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * U} : ℝ)
        ≤ K * U := by
  obtain ⟨K, hK, h⟩ := frequency_count_lt R
  refine ⟨2 * K, by positivity, fun U hU => ?_⟩
  obtain ⟨hfin, hcard⟩ := h (2 * U) (by linarith)
  have hsub : {u : Frequency R | U ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * U} ⊆
      {u : Frequency R | frequencyNorm R u < 2 * U} := fun _ hu => hu.2
  refine ⟨hfin.subset hsub, ?_⟩
  calc (Set.ncard {u : Frequency R | U ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * U} : ℝ)
      ≤ (Set.ncard {u : Frequency R | frequencyNorm R u < 2 * U} : ℝ) :=
        Nat.cast_le.mpr (Set.ncard_le_ncard hsub hfin)
    _ ≤ K * (2 * U) := hcard
    _ = 2 * K * U := by ring

theorem frequency_dyad_count_nonprincipal (R : PrincipalMellin.ActualRecipe S η) :
    ∃ K : ℝ, ∀ U : ℝ, 1 ≤ U →
      {u : Frequency R | u ≠ principalFrequency R ∧
        U ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * U}.Finite ∧
      (Set.ncard {u : Frequency R | u ≠ principalFrequency R ∧
        U ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * U} : ℝ) ≤ K * U := by
  obtain ⟨K, hK, h⟩ := frequency_dyad_count R
  refine ⟨K, fun U hU => ?_⟩
  obtain ⟨hfin, hcard⟩ := h U hU
  have hsub : {u : Frequency R | u ≠ principalFrequency R ∧
        U ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * U} ⊆
      {u : Frequency R | U ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * U} :=
    fun _ hu => hu.2
  exact ⟨hfin.subset hsub, (Nat.cast_le.mpr (Set.ncard_le_ncard hsub hfin)).trans hcard⟩

theorem fixedData_frequency_count_lt (D : FixedData S η) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 1 ≤ X →
      {u : Frequency D.recipe | frequencyNorm D.recipe u < X}.Finite ∧
      (Set.ncard {u : Frequency D.recipe | frequencyNorm D.recipe u < X} : ℝ) ≤ K * X :=
  frequency_count_lt D.recipe

end

end DedekindZetaZeroFree.Quantitative.RawFrequencyCount
