module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FixedData

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawDenominatorExistence

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
open DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem rawDeletionSet_finite (R : PrincipalMellin.ActualRecipe S η)
    (U : AllRowEuler.InitialSeparation.RawFrequency R.A) :
    (RawHeckeRows.rawDeletionSet U).Finite :=
  R.A.Sf.finite_toSet.union (by
    simpa only [Ideal.dvd_iff_le] using Ideal.finite_factors U.ideal.property.1)

theorem Sf_subset_rawDeletionSet (R : PrincipalMellin.ActualRecipe S η)
    (U : AllRowEuler.InitialSeparation.RawFrequency R.A) :
    (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) ⊆
      RawHeckeRows.rawDeletionSet U := by
  unfold RawHeckeRows.rawDeletionSet
  exact Set.subset_union_left

theorem mem_bad_of_not_coprime_six (R : PrincipalMellin.ActualRecipe S η)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (h : ¬ (Ideal.absNorm v.asIdeal).Coprime 6) :
    v ∈ R.A.Sf := by
  by_contra hn
  exact h (ArithmeticContext.actual_outside_norm_coprime_six R.A v hn)

/-- The deleted Euler coefficients identify the raw denominator character. -/
abbrev Identifies (R : PrincipalMellin.ActualRecipe S η)
    (ω : Frequency R → Detector.PrimitiveFrequencyCharacter F) : Prop :=
  ∀ (u : Frequency R) (U : AllRowEuler.InitialSeparation.RawFrequency R.A),
    U.u = u.val.val → ∀ I : R.A.Exterior,
      AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target U I =
        Detector.deletedPrimitiveIdealCoefficient F (ω u) (RawHeckeRows.rawDeletionSet U) I.val

/-- Simultaneously choose the representatives, Kummer family, and twisted family
used to control the conductor and the local components of each denominator. -/
theorem exists_identified_family (R : PrincipalMellin.ActualRecipe S η) :
    ∃ (V : Detector.FrequencyRepresentatives F (R.A.Sf : Set _)) (e : Frequency R ≃ V.carrier)
      (K : Detector.KummerFrequencyFamily F R.A.zeta12 R.σ (R.A.Sf : Set _) V)
      (η0 : Detector.PrimitiveFrequencyCharacter F),
      Detector.conductorSupportedOn F (R.A.Sf : Set _) η0 ∧
      ∃ T : Detector.TwistedFrequencyFamily F R.A.zeta12 R.σ (R.A.Sf : Set _) V K η0,
        Identifies R (fun u => T.denominator (e u)) ∧
        ∀ u, (Detector.frequencySNorm F (R.A.Sf : Set _) V (e u) : ℝ) = frequencyNorm R u := by
  classical
  letI : IsPrincipalIdealRing R.A.R :=
    R.A.principalIdealRing_of_classGroup_subsingleton R.classKilled
  obtain ⟨V, e, he, hnorm⟩ :=
    MinusArithmetic.actual_detector_frequency_representatives R
  obtain ⟨K⟩ := Detector.kummer_frequency_family_exists F R.A.zeta12
    R.A.primitive_zeta12 R.σ (R.A.Sf : Set _) R.A.Sf.finite_toSet (mem_bad_of_not_coprime_six R) V
  obtain ⟨η0, hη0, _, htarget⟩ := MinusArithmetic.target_primitive_inducer R
  obtain ⟨T, hT⟩ :=
    MinusArithmetic.raw_minus_family_identification R V e he K η0 hη0 htarget
  exact ⟨V, e, K, η0, hη0, T, hT, hnorm⟩

theorem raw_denominator_existence (R : PrincipalMellin.ActualRecipe S η) :
    ∃ ω : Frequency R → Detector.PrimitiveFrequencyCharacter F,
      Identifies R ω ∧
      (∀ (u : Frequency R) (U : AllRowEuler.InitialSeparation.RawFrequency R.A),
        U.u = u.val.val → ∀ ν : Detector.PrimitiveFrequencyCharacter F,
          (∀ I : R.A.Exterior,
            AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target U I =
              Detector.deletedPrimitiveIdealCoefficient F ν
                (RawHeckeRows.rawDeletionSet U) I.val) → ν = ω u) ∧
      (∀ u v : Frequency R, Detector.samePrimitiveFrequencyCharacter F (ω u) (ω v) → u = v) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ u : Frequency R,
        (Ideal.absNorm (ω u).conductor : ℝ) ≤ c * frequencyNorm R u) := by
  letI : IsPrincipalIdealRing R.A.R := R.A.principalIdealRing_of_classGroup_subsingleton R.classKilled
  obtain ⟨V, e, K, η0, hη0, T, hT, hnorm⟩ := exists_identified_family R
  have hSix := mem_bad_of_not_coprime_six R
  obtain ⟨c, hc, hbound⟩ := Detector.frequency_denominator_conductor_bound F
    R.A.zeta12 R.A.primitive_zeta12 R.σ (R.A.Sf : Set _)
    R.A.Sf.finite_toSet hSix η0 hη0
  refine ⟨fun u => T.denominator (e u), hT, ?_, ?_, c, hc, ?_⟩
  · intro u U hU ν hν
    exact MinusArithmetic.deleted_primitive_inducers_eq R.A
      (RawHeckeRows.rawDeletionSet U) (rawDeletionSet_finite R U)
      (Sf_subset_rawDeletionSet R U)
      ν (T.denominator (e u)) (fun I => (hν I).symm.trans (hT u U hU I))
  · intro u v h
    exact e.injective (Detector.twisted_frequency_character_injective F R.A.zeta12
      R.A.primitive_zeta12 R.σ (R.A.Sf : Set _) R.A.Sf.finite_toSet hSix V K η0 T
      (e u) (e v) h)
  · intro u
    rw [← hnorm u]
    exact hbound V K T (e u)

end

end DedekindZetaZeroFree.Quantitative.RawDenominatorExistence
