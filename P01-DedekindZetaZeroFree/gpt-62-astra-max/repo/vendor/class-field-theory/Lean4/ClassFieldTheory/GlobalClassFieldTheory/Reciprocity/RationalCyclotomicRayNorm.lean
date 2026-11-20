module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerAlgEquivNaturality
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianLocalConductorComparison
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidue
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicFinitePlaceArtin
public import ClassFieldTheory.KroneckerWeber.RayClassComparison
public import GaloisCohomology.Kummer.Concrete.Cyclotomic.RationalCyclotomicCharacterEquiv

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Rational cyclotomic ray norm groups

For a positive integer `m`, the genuine idèle-class norm range of the
actual cyclotomic level `ℚ(μ_m)` is the rational ray congruence subgroup
modulo `(m)`.

The local input is the cyclotomic higher-unit calculation: at a rational prime
`q`, an
`m.factorization q`-th higher unit has trivial Artin action on every
prime-power cyclotomic part.  On the `q`-primary part this is the actual
multiplicative Lubin--Tate norm theorem; on every other primary part it is
the unramified Artin formula together with valuation zero.  The finite
cyclotomic character then detects that the full local Artin symbol is
trivial.
-/

open scoped Classical NNReal NumberField ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open LubinTate

local instance (q : Nat.Primes) : Fact q.1.Prime :=
  ⟨q.2⟩

attribute [local instance]
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional
  rationalCyclotomicPrincipalPrimeLevelIsAbelianGalois

section FinitePlaceLocalCalculation

attribute [local instance]
  rationalFinitePlaceBaseNontriviallyNormedField
  rationalFinitePlaceBaseLocallyCompactSpace
  rationalFinitePlaceBaseIsUltrametricDist
  rationalFinitePlaceBaseValued
  rationalFinitePlaceBaseValuativeRel
  rationalFinitePlaceBaseValuationIsNontrivial
  rationalFinitePlaceBaseValuationCompatible
  rationalFinitePlaceBaseValuativeRelIsNontrivial
  rationalFinitePlaceBaseIsValuativeTopology
  rationalFinitePlaceBaseIsNonarchimedeanLocalField

private theorem
    rationalRayNorm_integerUnitsMap_mem_higherPrincipalUnits_iff
    (q : Nat.Primes) (n : ℕ)
    (u : 𝒪[RationalCyclotomicPrincipalPrimeCompletion q]ˣ) :
    Units.mapEquiv
          (((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q).trans
            (padicIntEquivValuationSubring q.1)).toMulEquiv) u ∈
        higherPrincipalUnitGroup
          (padicLocalField q.1).toCompleteDVF n ↔
      u ∈ principalUnits
        (RationalCyclotomicPrincipalPrimeCompletion q) n := by
  let F := RationalCyclotomicPrincipalPrimeCompletion q
  let eO :
      𝒪[F] ≃+* (padicLocalField q.1).valuationSubring :=
    (rationalFinitePlaceCompletionIntegerRingEquivPadicInt q).trans
      (padicIntEquivValuationSubring q.1)
  change
    eO (u : 𝒪[F]) - 1 ∈
        (padicLocalField q.1).toCompleteDVF.maximalIdeal ^ n ↔
      (u : 𝒪[F]) - 1 ∈
        (IsLocalRing.maximalIdeal 𝒪[F]) ^ n
  simpa only [map_sub, map_one] using
    (ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff
      eO n ((u : 𝒪[F]) - 1))

private theorem rationalRayNorm_fieldUnitsMap_integerUnits
    (q : Nat.Primes)
    (u : 𝒪[RationalCyclotomicPrincipalPrimeCompletion q]ˣ) :
    Units.map
        (rationalFinitePlaceCompletionRingEquivPadic q).toMonoidHom
        (IsNonarchimedeanLocalField.integerUnitsToFieldUnits
          (RationalCyclotomicPrincipalPrimeCompletion q) u) =
      CompleteDVF.valuationSubringUnitsToFieldUnits
        (padicLocalField q.1).toCompleteDVF
        (Units.mapEquiv
          (((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q).trans
            (padicIntEquivValuationSubring q.1)).toMulEquiv) u) := by
  let F := RationalCyclotomicPrincipalPrimeCompletion q
  let eK := rationalFinitePlaceCompletionRingEquivPadic q
  let eO :=
    (rationalFinitePlaceCompletionIntegerRingEquivPadicInt q).trans
      (padicIntEquivValuationSubring q.1)
  apply Units.ext
  let algebraMap₀ := algebraMap (padicLocalField q.1).valuationSubring ℚ_[q.1]
  change
    eK (algebraMap 𝒪[F] F
        (u : 𝒪[F])) =
      algebraMap₀
        (eO (u : 𝒪[F]))
  calc
    _ =
      algebraMap ℤ_[q.1] ℚ_[q.1]
        ((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q)
          (u : 𝒪[F])) :=
      rationalFinitePlaceCompletionIntegerRingEquivPadicInt_coe
        q (u : 𝒪[F])
    _ =
      algebraMap₀
        (padicIntEquivValuationSubring q.1
          ((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q)
            (u : 𝒪[F]))) := by
        change
          (((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q)
              (u : 𝒪[F]) : ℤ_[q.1]) : ℚ_[q.1]) =
            ((padicIntEquivValuationSubring q.1
              ((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q)
                (u : 𝒪[F])) :
                (padicDVRValuation q.1).valuationSubring) : ℚ_[q.1])
        exact
          (padicIntEquivValuationSubring_coe q.1
            ((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q)
              (u : 𝒪[F]))).symm
    _ =
      algebraMap₀
        (eO (u : 𝒪[F])) :=
      rfl

/-- The canonical rational-completion equivalence transports the
topology-first principal-unit subgroup to the packaged higher-principal-unit
subgroup in the standard `q`-adic field. -/
theorem
    rationalFinitePlaceFieldPrincipalUnits_map_eq_padicHigherPrincipalUnits
    (q : Nat.Primes) (n : ℕ) :
    let vQ :=
      HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)
    let eK :=
      rationalFinitePlaceCompletionRingEquivPadic q
    (fieldPrincipalUnits vQ.Completion n).map
        (Units.map eK.toMonoidHom) =
      (higherPrincipalUnitGroup
        (padicLocalField q.1).toCompleteDVF n).map
        (CompleteDVF.valuationSubringUnitsToFieldUnits
          (padicLocalField q.1).toCompleteDVF) := by
  let vQ :=
    HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)
  let eU :=
    Units.mapEquiv ((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q).trans
      (padicIntEquivValuationSubring q.1)).toMulEquiv
  let jQ :=
    IsNonarchimedeanLocalField.integerUnitsToFieldUnits vQ.Completion
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    change
      z ∈
        (principalUnits vQ.Completion n).map jQ at hz
    obtain ⟨u, hu, rfl⟩ := hz
    refine
      ⟨eU u,
        (rationalRayNorm_integerUnitsMap_mem_higherPrincipalUnits_iff
          q n u).2 hu,
        ?_⟩
    exact (rationalRayNorm_fieldUnitsMap_integerUnits q u).symm
  · rintro ⟨u, hu, rfl⟩
    let z := eU.symm u
    have hzu :=
      eU.apply_symm_apply u
    refine
      ⟨jQ z, ⟨z, ?_, rfl⟩, ?_⟩
    · apply
      (rationalRayNorm_integerUnitsMap_mem_higherPrincipalUnits_iff
          q n z).1
      exact hzu.symm ▸ hu
    · exact
        (rationalRayNorm_fieldUnitsMap_integerUnits q z).trans
          (congrArg
            (CompleteDVF.valuationSubringUnitsToFieldUnits
              (padicLocalField q.1).toCompleteDVF)
            hzu)

section PrimePowerCalculation

attribute [local instance]
  rationalCyclotomicPrincipalPrimePadicLevelFiniteDimensional

noncomputable local instance
    rationalCyclotomicRayNormPadicLevelIsAbelianGalois
    (q : Nat.Primes) (n : ℕ) :
    IsAbelianGalois ℚ_[q.1]
      (RationalCyclotomicPrincipalPrimePadicLevel q n) :=
  standardLubinTateLevelField_isAbelianGalois
    (padicLocalField q.1)
    (padicMultiplicativeLubinTateSeries_isUniformizer q.1) n

/-- A rational higher unit has trivial local Artin image in the standard
multiplicative Lubin--Tate level.  This is the purely `q`-adic part of the
prime-power argument; the semilinear transport to the localized global
cyclotomic field is handled separately below. -/
private theorem rationalPrimePowerPadicAbelianLocalArtin_eq_one
    (q : Nat.Primes) (n : ℕ)
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ)
    (hx :
      x ∈ RayClass.localHigherUnitGroup
        (RayClass.rationalPrime q) (n + 1)) :
    abelianLocalArtinMonoidHom ℚ_[q.1]
        (RationalCyclotomicPrincipalPrimePadicLevel q n)
        (Units.map
          (rationalFinitePlaceCompletionRingEquivPadic q).toMonoidHom
          ((finitePlaceCompletionUnitsContinuousMulEquiv
            (RayClass.rationalPrime q)).symm x)) = 1 := by
  let v :=
    RayClass.rationalPrime q
  let vQ := HeightOneSpectrum.adicAbv ℚ v
  let eK := rationalFinitePlaceCompletionRingEquivPadic q
  let eC :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  let localInput := eC.symm x
  let T := RationalCyclotomicPrincipalPrimePadicLevel q n
  have hxMap :
      x ∈
        (fieldPrincipalUnits vQ.Completion (n + 1)).map
          eC.toMonoidHom := by
    rw [
      GlobalClassFields.finitePlaceFieldPrincipalUnits_map_eq_localHigherUnitGroup
           v (n + 1)]
    exact hx
  have hlocalInput :
      localInput ∈
        fieldPrincipalUnits vQ.Completion (n + 1) := by
    obtain ⟨y, hy, hyx⟩ := hxMap
    have hylocal : y = localInput := by
      apply eC.injective
      exact hyx.trans (eC.apply_symm_apply x).symm
    rw [← hylocal]
    exact hy
  have hxMapped :
      Units.map eK.toMonoidHom localInput ∈
        (higherPrincipalUnitGroup
          (padicLocalField q.1).toCompleteDVF (n + 1)).map
          (CompleteDVF.valuationSubringUnitsToFieldUnits
            (padicLocalField q.1).toCompleteDVF) := by
    rw [←
      rationalFinitePlaceFieldPrincipalUnits_map_eq_padicHigherPrincipalUnits
        q (n + 1)]
    exact ⟨localInput, hlocalInput, rfl⟩
  obtain ⟨u, hu, hux⟩ := hxMapped
  have hPadic :
      abelianLocalArtinMonoidHom ℚ_[q.1] T
          (Units.map eK.toMonoidHom localInput) = 1 := by
    rw [← hux]
    simpa only [standardLubinTateUnitFactorFieldUnit] using
      (padicMultiplicativeAbelianLocalArtin_eq_one_of_mem_higherPrincipalUnitGroup
        q.1 n u hu)
  simpa only [T, eK, localInput, eC, vQ, v] using hPadic

/-- The chosen ramified finite-place Artin value, with the cyclotomic level
and its instance arguments frozen behind a named boundary. -/
 noncomputable def rationalPrimePowerChosenFinitePlaceArtinValue
    (q : Nat.Primes) (n : ℕ)
    (x :
      ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    KummerTheory.rationalCyclotomicLevel
          (rationalCyclotomicPrincipalPrimeModulus q n) ≃ₐ[ℚ]
        KummerTheory.rationalCyclotomicLevel
          (rationalCyclotomicPrincipalPrimeModulus q n) :=
  chosenFinitePlaceArtinMonoidHom
    (K := ℚ)
    (L :=
      KummerTheory.rationalCyclotomicLevel
        (rationalCyclotomicPrincipalPrimeModulus q n))
    (RayClass.rationalPrime q) x

section

variable (q : Nat.Primes) (n : ℕ) (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ)
    (hx : x ∈ RayClass.localHigherUnitGroup (RayClass.rationalPrime q) (n + 1))

include hx in
/-- The standard `q`-adic calculation evaluated on the canonical input used
by the finite-place Artin construction. -/
private theorem rationalPrimePowerFinitePlaceLocalInputPadicArtin_eq_one :
    abelianLocalArtinMonoidHom ℚ_[q.1]
        (RationalCyclotomicPrincipalPrimePadicLevel q n)
        (Units.map
          (rationalFinitePlaceCompletionRingEquivPadic q).toMonoidHom
          (finitePlaceLocalArtinInput
            (RayClass.rationalPrime q) x)) = 1 := by
  change
    abelianLocalArtinMonoidHom ℚ_[q.1]
        (RationalCyclotomicPrincipalPrimePadicLevel q n)
        (Units.map
          (rationalFinitePlaceCompletionRingEquivPadic q).toMonoidHom
          ((finitePlaceCompletionUnitsContinuousMulEquiv
            (RayClass.rationalPrime q)).symm x)) = 1
  exact rationalPrimePowerPadicAbelianLocalArtin_eq_one q n x hx

include hx in
/-- The normalized local calculation, transported through the decomposition
group inclusion.  This bridge contains no semilinear instance search. -/
private theorem rationalPrimePowerFinitePlaceArtinOfExtension_eq_one :
    finitePlaceArtinMonoidHomOfExtension
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel
          (rationalCyclotomicPrincipalPrimeModulus q n))
        (RayClass.rationalPrime q)
        (rationalCyclotomicChosenFinitePlaceExtension
          (rationalCyclotomicPrincipalPrimeModulus q n)
          (RayClass.rationalPrime q)) x = 1 := rationalCyclotomicPrincipalPrime_finitePlaceArtinOfExtension_eq_one_of_padic
      q n x
      (rationalPrimePowerFinitePlaceLocalInputPadicArtin_eq_one q n x hx)

include hx in
/-- The local semilinear calculation for a ramified prime-power level.  Its
statement only exposes the named global Artin value. -/
private theorem
    rationalPrimePowerChosenFinitePlaceArtinValue_eq_one_of_mem_localHigherUnitGroup :
    rationalPrimePowerChosenFinitePlaceArtinValue q n x = 1 := by
  simpa only [rationalPrimePowerChosenFinitePlaceArtinValue,
    chosenFinitePlaceArtinMonoidHom,
    rationalCyclotomicChosenFinitePlaceExtension] using
    rationalPrimePowerFinitePlaceArtinOfExtension_eq_one q n x hx

end

/-- A principal unit of depth `n + 1` has trivial chosen finite-place
Artin symbol in the genuine `q ^ (n + 1)`-st rational cyclotomic level. -/
theorem
    rationalPrimePowerChosenFinitePlaceArtin_eq_one_of_mem_localHigherUnitGroup
    (q : Nat.Primes) (n : ℕ)
    (x :
      ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ)
    (hx :
      x ∈ RayClass.localHigherUnitGroup
        (RayClass.rationalPrime q) (n + 1)) :
    chosenFinitePlaceArtinMonoidHom
        (K := ℚ)
        (L :=
          KummerTheory.rationalCyclotomicLevel
            (rationalCyclotomicPrincipalPrimeModulus q n))
        (RayClass.rationalPrime q) x =
      1 := by apply @rationalPrimePowerChosenFinitePlaceArtinValue_eq_one_of_mem_localHigherUnitGroup <;> assumption

/-- The positive-depth form of the prime-power calculation.  Eliminating
the successor before introducing a cyclotomic level avoids transporting its
dependent field and instance data later in the full-level coordinate proof. -/
private theorem
    rationalPrimePowerChosenFinitePlaceArtin_eq_one_of_mem_localHigherUnitGroup_pos
    (q : Nat.Primes) (k : ℕ) (hk : k ≠ 0)
    (mp : ℕ+) (hmp : (mp : ℕ) = q.1 ^ k)
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ)
    (hx :
      x ∈ RayClass.localHigherUnitGroup
        (RayClass.rationalPrime q) k) :
    chosenFinitePlaceArtinMonoidHom
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel mp)
        (RayClass.rationalPrime q) x = 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hlevel :
      mp = rationalCyclotomicPrincipalPrimeModulus q n := by
    apply Subtype.ext
    exact hmp
  subst mp
  exact
    rationalPrimePowerChosenFinitePlaceArtin_eq_one_of_mem_localHigherUnitGroup
      q n x hx

/-- A valuation-zero input away from a named cyclotomic level has trivial
chosen Artin value.  Keeping the level as a positive-natural variable makes
the instance owner identical on both sides of the imported calculation. -/
private theorem rationalCyclotomicRayNormAwayChosenFinitePlaceArtin_eq_one
    (mp : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (mp : ℕ))
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ)
    (hzero : rationalCyclotomicArtinLocalExponent q x = 0) :
    chosenFinitePlaceArtinMonoidHom
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel mp)
        (RayClass.rationalPrime q) x = 1 := chosenFinitePlaceArtinMonoidHom_eq_one_of_not_dvd_of_localExponent_eq_zero
      mp q hq x hzero

end PrimePowerCalculation

end FinitePlaceLocalCalculation

end Reciprocity
end GlobalClassFieldTheory

end
