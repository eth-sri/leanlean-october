module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.InitialFrequencyDecomposition
public import DedekindZetaZeroFree.Moments.Reflected.AllRowEulerFactorization

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RawHeckeRows
noncomputable section
open scoped Classical NumberField
open IsDedekindDomain LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

def rawDeletionSet {A : SArithmeticData F}
    (U : AllRowEuler.InitialSeparation.RawFrequency A) :
    Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :=
  (A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) ∪
    {v | U.ideal.val ≤ v.asIdeal}

section Raw

variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η' : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private theorem rawDeletionSet_finite
    (U : AllRowEuler.InitialSeparation.RawFrequency A) :
    (rawDeletionSet U).Finite := by
  unfold rawDeletionSet
  apply Set.Finite.union
  · exact A.Sf.finite_toSet
  · let s := (UniqueFactorizationMonoid.normalizedFactors U.ideal.val).toFinset
    have hinj : Function.Injective (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) :=
      HeightOneSpectrum.asIdeal_injective
    have hsub : {v : HeightOneSpectrum (𝓞 F) | U.ideal.val ≤ v.asIdeal} ⊆
        (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) ⁻¹' (↑s : Set (Ideal (𝓞 F))) := by
      intro v hv
      simp only [Set.mem_preimage, Finset.mem_coe]
      exact Multiset.mem_toFinset.mpr
        ((Ideal.mem_normalizedFactors_iff U.ideal.property.1).mpr ⟨v.isPrime, hv⟩)
    exact (s.finite_toSet.preimage hinj.injOn).subset hsub

private theorem raw_coefficients_zero_at_frequency_primes
    (C : A.GeneralArithmeticContext σ η' hS)
    (U : AllRowEuler.InitialSeparation.RawFrequency A)
    (p : ExteriorPrime A) (hp : (U.j p).val ≠ 0) :
    AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U (primeIdeal p) = 0 ∧
      AllRowEuler.InitialSeparation.minusExteriorCoefficient σ η' U (primeIdeal p) = 0 := by
  letI : Nontrivial (A.R ⧸ A.extendIdeal (primeIdeal p)) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (A.residue_extendIdeal_ne_top (primeIdeal p) p.val.isPrime.ne_top)
  have hg : Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) (generator C p) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← (generator_generates C p).2]
    exact Ideal.mem_span_singleton_self _
  have hu : Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u = 0 := by
    rw [(AllRowEuler.InitialSeparation.RawFrequency.unitPart_spec C U p).1, map_mul, map_pow,
      hg, zero_pow hp, zero_mul]
  have hchi : chi (σ := σ) p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) = 0 := by
    rw [hu, MulChar.map_zero]
  refine ⟨?_, ?_⟩
  · exact hchi
  · rw [AllRowEuler.InitialSeparation.minusExteriorCoefficient]
    rw [show AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U (primeIdeal p) =
      chi (σ := σ) p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) from rfl,
      hchi, star_zero, mul_zero]

private theorem raw_exterior_prime_identification
    (C : A.GeneralArithmeticContext σ η' hS)
    (U : AllRowEuler.InitialSeparation.RawFrequency A)
    (χ ψ : Detector.PrimitiveFrequencyCharacter F)
    (hχ : Detector.IsKummerFrequencyCharacter F A.zeta12 σ
      (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
      (Units.mk0 (U.u : F) (by exact_mod_cast U.generates.1)) χ)
    (hψ : Detector.conductorSupportedOn F (rawDeletionSet U) ψ)
    (htwist : ∀ J : Ideal (𝓞 F), J ≠ ⊥ →
      J ⊔ (A.modulus * χ.conductor * ψ.conductor) = ⊤ →
      ψ.character J = η' J * star (χ.character J)) :
    ∀ p : ExteriorPrime A, (U.j p).val = 0 →
      (p.val.asIdeal ⊔ χ.conductor = ⊤ ∧ p.val.asIdeal ⊔ ψ.conductor = ⊤ ∧
        p.val.asIdeal ⊔ A.modulus = ⊤) ∧
      (AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U (primeIdeal p) =
        χ.character p.val.asIdeal ∧
       AllRowEuler.InitialSeparation.minusExteriorCoefficient σ η' U (primeIdeal p) =
        ψ.character p.val.asIdeal) := fun p hp =>
  FrequencyCharacterMasks.KummerConductors.exterior_prime_identification C U χ ψ hχ hψ htwist p hp

 def rawPlusCoefficient (σ : F →+* ℂ)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) (I : Ideal (𝓞 F)) : ℂ :=
  if hI : I ≠ ⊥ ∧ I ⊔ A.cS = ⊤ then
    AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U ⟨I, hI⟩ else 0

 def rawMinusCoefficient (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) (I : Ideal (𝓞 F)) : ℂ :=
  η I * star (rawPlusCoefficient σ U I)

private theorem raw_plus_mul (σ : F →+* ℂ)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) (I J : Ideal (𝓞 F)) :
    rawPlusCoefficient σ U (I * J) = rawPlusCoefficient σ U I * rawPlusCoefficient σ U J :=
  ExteriorIdealEuler.extendZero_mul (AllRowEuler.InitialSeparation.plus_ext_mul_raw (σ := σ) U) I J

private theorem raw_minus_mul (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) (I J : Ideal (𝓞 F)) :
    rawMinusCoefficient σ η U (I * J) =
      rawMinusCoefficient σ η U I * rawMinusCoefficient σ η U J := by
  unfold rawMinusCoefficient
  rw [raw_plus_mul, RayClassCharacter.map_mul', star_mul]
  ring

private theorem raw_plus_one (σ : F →+* ℂ)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) :
    rawPlusCoefficient σ U ⊤ = 1 := by
  have h := (AllRowEuler.InitialSeparation.raw_plus_isCoefficient (σ := σ) U).map_one
  simpa [rawPlusCoefficient, ExteriorIdealEuler.one] using h

private theorem raw_minus_one (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (U : AllRowEuler.InitialSeparation.RawFrequency A) :
    rawMinusCoefficient σ η U ⊤ = 1 := by
  unfold rawMinusCoefficient
  rw [raw_plus_one, star_one, RayClassCharacter.map_top', mul_one]

private theorem raw_plus_prime_value
    (C : A.GeneralArithmeticContext σ η' hS)
    (U : AllRowEuler.InitialSeparation.RawFrequency A)
    (χ ψ : Detector.PrimitiveFrequencyCharacter F)
    (hχ : Detector.IsKummerFrequencyCharacter F A.zeta12 σ
      (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
      (Units.mk0 (U.u : F) (by exact_mod_cast U.generates.1)) χ)
    (hψ : Detector.conductorSupportedOn F (rawDeletionSet U) ψ)
    (htwist : ∀ J : Ideal (𝓞 F), J ≠ ⊥ →
      J ⊔ (A.modulus * χ.conductor * ψ.conductor) = ⊤ →
      ψ.character J = η' J * star (χ.character J))
    (p : ExteriorPrime A) :
    rawPlusCoefficient σ U p.val.asIdeal =
      if (U.j p).val = 0 then χ.character p.val.asIdeal else 0 := by
  by_cases hp : (U.j p).val = 0
  · rw [if_pos hp]
    have h := (raw_exterior_prime_identification C U χ ψ hχ hψ htwist p hp).2.1
    unfold rawPlusCoefficient
    rw [dif_pos ⟨p.val.ne_bot, p.property⟩]
    exact h
  · rw [if_neg hp]
    have h := (raw_coefficients_zero_at_frequency_primes C U p hp).1
    unfold rawPlusCoefficient
    rw [dif_pos ⟨p.val.ne_bot, p.property⟩]
    exact h

private theorem raw_minus_prime_value
    (C : A.GeneralArithmeticContext σ η' hS)
    (U : AllRowEuler.InitialSeparation.RawFrequency A)
    (χ ψ : Detector.PrimitiveFrequencyCharacter F)
    (hχ : Detector.IsKummerFrequencyCharacter F A.zeta12 σ
      (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
      (Units.mk0 (U.u : F) (by exact_mod_cast U.generates.1)) χ)
    (hψ : Detector.conductorSupportedOn F (rawDeletionSet U) ψ)
    (htwist : ∀ J : Ideal (𝓞 F), J ≠ ⊥ →
      J ⊔ (A.modulus * χ.conductor * ψ.conductor) = ⊤ →
      ψ.character J = η' J * star (χ.character J))
    (p : ExteriorPrime A) :
    rawMinusCoefficient σ η' U p.val.asIdeal =
      if (U.j p).val = 0 then ψ.character p.val.asIdeal else 0 := by
  by_cases hp : (U.j p).val = 0
  · rw [if_pos hp]
    obtain ⟨⟨hpc, hpp, hpm⟩, -, -⟩ :=
      raw_exterior_prime_identification C U χ ψ hχ hψ htwist p hp
    unfold rawMinusCoefficient
    rw [raw_plus_prime_value C U χ ψ hχ hψ htwist p, if_pos hp]
    exact (htwist p.val.asIdeal p.val.ne_bot (by
      rw [Ideal.sup_mul_eq_of_coprime_right hpp,
        Ideal.sup_mul_eq_of_coprime_right hpc, hpm])).symm
  · rw [if_neg hp]
    unfold rawMinusCoefficient
    rw [raw_plus_prime_value C U χ ψ hχ hψ htwist p, if_neg hp, star_zero, mul_zero]

end Raw

theorem actual_raw_masked_inducers
    (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (hC : R.probe.correction = C.correction)
    (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
    (hU : ∀ u : Frequency R, (U u).u = u.val.val) :
    ∃ (P M : Frequency R → Detector.PrimitiveFrequencyCharacter F),
      (∀ u : Frequency R, (rawDeletionSet (U u)).Finite) ∧
      (∀ (u : Frequency R) (I : R.A.Exterior),
        AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ (U u) I =
          Detector.deletedPrimitiveIdealCoefficient F (P u) (rawDeletionSet (U u)) I.val) ∧
      (∀ (u : Frequency R) (I : R.A.Exterior),
        AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target (U u) I =
          Detector.deletedPrimitiveIdealCoefficient F (M u) (rawDeletionSet (U u)) I.val) := by
  classical
  have key : ∀ u : Frequency R, ∃ (χ ψ : Detector.PrimitiveFrequencyCharacter F),
      (∀ I : R.A.Exterior,
        AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ (U u) I =
          Detector.deletedPrimitiveIdealCoefficient F χ (rawDeletionSet (U u)) I.val) ∧
      (∀ I : R.A.Exterior,
        AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target (U u) I =
          Detector.deletedPrimitiveIdealCoefficient F ψ (rawDeletionSet (U u)) I.val) := by
    intro u
    obtain ⟨χ, hχ, hχS, hχord⟩ :=
      FrequencyCharacterMasks.KummerConductors.kummer_inducer_exists R.A R.σ (U u).ideal (U u).u
        (U u).generates
    obtain ⟨ψ, htwist, hψS, hψord⟩ :=
      FrequencyCharacterMasks.KummerConductors.finite_order_twist_inducer_exists R.A R.target
        (rawDeletionSet (U u)) (Set.subset_union_left) χ hχS 6 (by decide) hχord
    refine ⟨χ, ψ, ?_, ?_⟩
    · intro I
      have hmask := FrequencyCharacterMasks.KummerConductors.multiplicative_mask_identification (A := R.A) (U u) χ
        (rawPlusCoefficient R.σ (U u)) (raw_plus_one R.σ (U u))
        (raw_plus_mul R.σ (U u))
        (fun I hI => by simp only [rawPlusCoefficient]; exact dif_neg hI)
        (raw_plus_prime_value C (U u) χ ψ hχ hψS htwist)
        I.val
      have hbridge : rawPlusCoefficient R.σ (U u) I.val =
          AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ (U u) I := by
        unfold rawPlusCoefficient
        rw [dif_pos I.property]
        exact congrArg (AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ (U u))
          (Subtype.ext (rfl : (⟨I.val, I.property⟩ : R.A.Exterior).val = I.val))
      rw [← hbridge]
      simpa [rawDeletionSet] using hmask
    · intro I
      have hmask := FrequencyCharacterMasks.KummerConductors.multiplicative_mask_identification (A := R.A) (U u) ψ
        (rawMinusCoefficient R.σ R.target (U u)) (raw_minus_one R.σ R.target (U u))
        (raw_minus_mul R.σ R.target (U u))
        (fun I hI => by
          unfold rawMinusCoefficient
          rw [show rawPlusCoefficient R.σ (U u) I = 0 from by
            unfold rawPlusCoefficient; exact dif_neg hI]
          rw [star_zero, mul_zero])
        (raw_minus_prime_value C (U u) χ ψ hχ hψS htwist)
        I.val
      have hbridge : rawMinusCoefficient R.σ R.target (U u) I.val =
          AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target (U u) I := by
        unfold rawMinusCoefficient
        rw [show rawPlusCoefficient R.σ (U u) I.val =
          AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ (U u) I from by
            unfold rawPlusCoefficient
            rw [dif_pos I.property]
            exact congrArg (AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ (U u))
              (Subtype.ext (rfl : (⟨I.val, I.property⟩ : R.A.Exterior).val = I.val))]
        rfl
      rw [← hbridge]
      simpa [rawDeletionSet] using hmask
  choose P M hP hM using key
  exact ⟨P, M, fun u => rawDeletionSet_finite (U u), hP, hM⟩

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RawHeckeRows
