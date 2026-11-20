module

public import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.CompletionToIdeal
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.LocalNorm
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.BaseChange
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Core
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormComparison
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormalClosureNorm
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Tower
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerAlgEquivNaturality
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.FinitePlaceTensorNorm
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicFinitePlace
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicLocalization
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalPrimeFactorization
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalPrincipalLocalUnit
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SemilinearNaturality
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormalization
public import ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.PadicMultiplicativeArtinComparison
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PadicValuationComparison
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius
public import ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.EisensteinPolynomial
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Finite-place Artin symbols in rational cyclotomic levels

At a rational prime away from the cyclotomic level, the chosen completed
extension is unramified.  Its normalized local Artin map is therefore the
arithmetic Frobenius raised to the local valuation.  The genuine primitive
root in the localized cyclotomic level identifies the image of arithmetic
Frobenius under the global cyclotomic character with the residue prime.
-/

open scoped Classical NNReal NumberField ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

-- Specializing the generic finite-place comparison to `ℚ` must retain its
-- `Algebra.id` owner rather than selecting the competing rational-field
-- instance introduced after specialization.
@[reducible] noncomputable local instance
    rationalFinitePlaceCompletionRatAlgebra
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Algebra ℚ (HeightOneSpectrum.adicAbv ℚ v).Completion := by
  letI : Algebra ℚ ℚ := Algebra.id ℚ
  exact
    @UniformSpace.Completion.algebra
      (WithAbs (HeightOneSpectrum.adicAbv ℚ v)) _ _ _ _
      ℚ _ (WithAbs.instAlgebra _) (WithAbs.instUniformContinuousConstSMulReal _)

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open LubinTate

private theorem mappedAbelianLocalArtin_eq_frobenius_zpow
    {F E G : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [UniformSpace E] [IsUniformAddGroup E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [FiniteDimensional F E] [IsAbelianGalois F E]
    [Valuation.HasExtension
      (ValuativeRel.valuation F) (ValuativeRel.valuation E)]
    [IsNonarchimedeanLocalField.IsUnramifiedValuedExtension F E]
    [Group G]
    (f : (E ≃ₐ[F] E) →* G) (x : Fˣ) :
    f (LocalClassFieldTheory.abelianLocalArtinMonoidHom F E x) =
      (f (arithmeticFrobeniusOfUnramifiedValuation F E)) ^
        IsNonarchimedeanLocalField.valuationMap F
          (Additive.ofMul x) := by
  rw [LocalClassFieldTheory.abelianLocalArtinMonoidHom_eq_frobenius_zpow,
    map_zpow]

local instance (q : Nat.Primes) : Fact q.1.Prime :=
  ⟨q.2⟩

local instance (m : ℕ+) : NeZero (m : ℕ) :=
  ⟨m.ne_zero⟩

noncomputable local instance
    rationalCyclotomicLevelFiniteDimensional
    (m : ℕ+) :
    FiniteDimensional ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  IsCyclotomicExtension.finiteDimensional
    {(m : ℕ)} ℚ (KummerTheory.rationalCyclotomicLevel m)

noncomputable local instance
    rationalCyclotomicLevelIsAbelianGalois
    (m : ℕ+) :
    IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) := by
  have : IsGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
    inferInstance
  exact
    { is_comm.comm σ τ := by
        apply (IsCyclotomicExtension.Rat.galEquivZMod
          (m : ℕ) (KummerTheory.rationalCyclotomicLevel m)).injective
        simp only [map_mul]
        exact mul_comm _ _ }

@[reducible]
noncomputable local instance rationalFinitePlaceBaseNontriviallyNormedField
    (q : Nat.Primes) :
    NontriviallyNormedField
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  absoluteValueExtension_completionNontriviallyNormedField
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q))
    (RayClass.adicAbv_isNontrivial
      (RayClass.rationalPrime q))

noncomputable local instance rationalFinitePlaceBaseLocallyCompactSpace
    (q : Nat.Primes) :
    LocallyCompactSpace
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  AbsoluteValue.Completion.locallyCompactSpace
    (finitePlaceCompletionBaseMap_isometry
      (RayClass.rationalPrime q))

noncomputable local instance rationalFinitePlaceBaseIsUltrametricDist
    (q : Nat.Primes) :
    IsUltrametricDist
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  finitePlaceArtinCompletionIsUltrametricDist
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q))
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (RayClass.rationalPrime q))

@[reducible]
noncomputable local instance rationalFinitePlaceBaseValued
    (q : Nat.Primes) :
    Valued
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion ℝ≥0 :=
  finitePlaceArtinCompletionValued
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q))
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (RayClass.rationalPrime q))

@[reducible]
noncomputable local instance rationalFinitePlaceBaseValuativeRel
    (q : Nat.Primes) :
    ValuativeRel
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  finitePlaceLocalArtinCompletionValuativeRel
    (K := ℚ) (RayClass.rationalPrime q)

noncomputable local instance
    rationalFinitePlaceBaseValuationIsNontrivial
    (q : Nat.Primes) :
    (Valued.v :
      Valuation
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        ℝ≥0).IsNontrivial :=
  (inferInstance :
    (NormedField.valuation
      (K :=
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion)).IsNontrivial)

noncomputable local instance rationalFinitePlaceBaseValuationCompatible
    (q : Nat.Primes) :
    (Valued.v :
      Valuation
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation _

noncomputable local instance
    rationalFinitePlaceBaseValuativeRelIsNontrivial
    (q : Nat.Primes) :
    ValuativeRel.IsNontrivial
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v :
      Valuation
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        ℝ≥0)).2 inferInstance

noncomputable local instance rationalFinitePlaceBaseIsValuativeTopology
    (q : Nat.Primes) :
    IsValuativeTopology
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  isValuativeTopology_of_valued_ofValuation
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion ℝ≥0

noncomputable local instance
    rationalFinitePlaceBaseIsNonarchimedeanLocalField
    (q : Nat.Primes) :
    IsNonarchimedeanLocalField
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField
    (K := ℚ) (RayClass.rationalPrime q)

/-! Named compatibility witnesses used by the ramified-prime and ray-norm
modules.  They are not installed as a duplicate module-level instance family;
the canonical instances above already provide the same data. -/

/-- Rational cyclotomic levels are finite-dimensional over `ℚ`. -/
theorem rationalCyclotomicPrincipalPrimeLevelFiniteDimensional
    (m : ℕ+) :
    FiniteDimensional ℚ (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicLevelFiniteDimensional m

/-- Rational cyclotomic levels are abelian Galois extensions of `ℚ`. -/
theorem rationalCyclotomicPrincipalPrimeLevelIsAbelianGalois
    (m : ℕ+) :
    IsAbelianGalois ℚ (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicLevelIsAbelianGalois m

/-- The positive conductor of the `n`-th ramified cyclotomic level at
`p`. -/
def rationalCyclotomicPrincipalPrimeModulus
    (p : Nat.Primes) (n : ℕ) : ℕ+ :=
  ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩

/-- The rational finite-place completion used at the prime `p`. -/
abbrev RationalCyclotomicPrincipalPrimeCompletion
    (p : Nat.Primes) :=
  (HeightOneSpectrum.adicAbv ℚ
    (RayClass.rationalPrime p)).Completion

/-- The standard multiplicative Lubin--Tate field at level `n`. -/
abbrev RationalCyclotomicPrincipalPrimePadicLevel
    (p : Nat.Primes) (n : ℕ) :=
  standardLubinTateLevelField
    (padicMultiplicativeLubinTateSeries_isUniformizer p.1) n

section

variable (q : Nat.Primes)

/-- The valuation ring of the absolute-value completion at `q`, identified
with the standard p-adic integer ring `ℤ_q`. -/
noncomputable def rationalFinitePlaceCompletionIntegerRingEquivPadicInt :
    𝒪[(HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion] ≃+*
      ℤ_[q.1] := by
  let v :=
    RayClass.rationalPrime q
  exact
    (finitePlaceCompletionIntegerRingEquiv v).trans
      (PadicInt.adicCompletionIntegersEquiv
        (𝓞 ℚ) q).symm.toRingEquiv

/-- The absolute-value completion at the rational prime `q`, identified
with the standard field `ℚ_q`. -/
noncomputable def rationalFinitePlaceCompletionRingEquivPadic :
    (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion ≃+*
      ℚ_[q.1] :=
  IsFractionRing.ringEquivOfRingEquiv
    (rationalFinitePlaceCompletionIntegerRingEquivPadicInt q)

/-- The completion-to-`ℚ_q` equivalence respects the rational embedding. -/
theorem rationalFinitePlaceCompletionRingEquivPadic_algebraMap (a : ℚ) :
    rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap ℚ
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion a) =
      algebraMap ℚ ℚ_[q.1] a := (rationalFinitePlaceCompletionRingEquivPadic q).toRingHom.map_rat_algebraMap a

/-- The completion field equivalence and its restriction to valuation
rings commute with the natural inclusions into the fields. -/
theorem rationalFinitePlaceCompletionIntegerRingEquivPadicInt_coe
    (a :
      𝒪[(HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion]) :
    rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap
          𝒪[(HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion]
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion a) =
      algebraMap ℤ_[q.1] ℚ_[q.1]
        (rationalFinitePlaceCompletionIntegerRingEquivPadicInt q a) := (IsFractionRing.ringEquivOfRingEquiv_algebraMap
      (rationalFinitePlaceCompletionIntegerRingEquivPadicInt q) a)

end

/-- The canonical rational-completion equivalence preserves the canonical
valuations. -/
theorem
    rationalFinitePlaceCompletionRingEquivPadic_semilinearValuationCompatible
    (p : Nat.Primes) :
    SemilinearValuationCompatible
      (RationalCyclotomicPrincipalPrimeCompletion p) ℚ_[p.1]
      (rationalFinitePlaceCompletionRingEquivPadic p) := by
  let F := RationalCyclotomicPrincipalPrimeCompletion p
  let := (rationalFinitePlaceCompletionRingEquivPadic p).toRingHom.toAlgebra
  change
    (ValuativeRel.valuation F).HasExtension
      (ValuativeRel.valuation ℚ_[p.1])
  have hChosen :
      (localCompleteDVF F).valuation.HasExtension
        (padicDVRValuation p.1) := by
    change
      (localCompleteDVF F).valuation.HasExtension
        (padicCompleteDVF p.1).valuation
    apply
      ValuationTheory.DiscreteValuationField.ValuedExtension.valuation_hasExtension_of_valuationSubring_equiv
        (localCompleteDVF F)
        (padicCompleteDVF p.1)
        ((rationalFinitePlaceCompletionIntegerRingEquivPadicInt p).trans
          (padicIntEquivValuationSubring p.1))
    intro z
    change
      algebraMap
          (padicDVRValuation p.1).valuationSubring ℚ_[p.1]
          (padicIntEquivValuationSubring p.1
            (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
              p z)) =
        rationalFinitePlaceCompletionRingEquivPadic p
          (algebraMap 𝒪[F] F z)
    symm
    calc
      _ =
        algebraMap ℤ_[p.1] ℚ_[p.1]
          (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
            p z) :=
        rationalFinitePlaceCompletionIntegerRingEquivPadicInt_coe
          p z
      _ =
        algebraMap
          (padicDVRValuation p.1).valuationSubring ℚ_[p.1]
          (padicIntEquivValuationSubring p.1
            (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
              p z)) := by
        rw [PadicInt.algebraMap_apply,
          ValuationSubring.algebraMap_apply]
        exact
          (padicIntEquivValuationSubring_coe p.1
            (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
              p z)).symm
  have hBase :
      (ValuativeRel.valuation F).HasExtension
        (padicDVRValuation p.1) := by
    rw [← localCompleteDVF_valuation_eq]
    exact hChosen
  refine
    { val_isEquiv_comap := ?_ }
  exact
    hBase.val_isEquiv_comap.trans
      ((padicDVRValuation_isEquiv_valuativeRelValuation
        p.1).comap (algebraMap F ℚ_[p.1]))

/-- The rational prime, pulled back from `ℤ_q` to the valuation ring of
the absolute-value completion at `q`. -/
noncomputable def rationalPrimeFinitePlaceInteger
    (q : Nat.Primes) :
    𝒪[(HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion] :=
  (rationalFinitePlaceCompletionIntegerRingEquivPadicInt q).symm
    (q.1 : ℤ_[q.1])

/-- The pulled-back rational prime is irreducible in the completion
valuation ring. -/
theorem rationalPrimeFinitePlaceInteger_irreducible
    (q : Nat.Primes) :
    Irreducible (rationalPrimeFinitePlaceInteger q) := (MulEquiv.irreducible_iff
      (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
        q).symm.toMulEquiv).2
      (PadicInt.prime_p.irreducible)

/-- Coercing the pulled-back prime to the completion field gives the
ordinary image of the rational number `q`. -/
theorem rationalPrimeFinitePlaceInteger_coe
    (q : Nat.Primes) :
    ((rationalPrimeFinitePlaceInteger q :
      𝒪[(HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion]) :
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion) =
      algebraMap ℚ
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (q.1 : ℚ) := by
  apply
    (rationalFinitePlaceCompletionRingEquivPadic q).injective
  let adicAbv₀ := HeightOneSpectrum.adicAbv ℚ (RayClass.rationalPrime q)
  change
    rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap
          𝒪[(adicAbv₀).Completion]
          (adicAbv₀).Completion
          (rationalPrimeFinitePlaceInteger q)) =
      rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap ℚ
          (adicAbv₀).Completion
          (q.1 : ℚ))
  calc
    _ =
      algebraMap ℤ_[q.1] ℚ_[q.1]
        ((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q)
          (rationalPrimeFinitePlaceInteger q)) :=
        rationalFinitePlaceCompletionIntegerRingEquivPadicInt_coe
          q (rationalPrimeFinitePlaceInteger q)
    _ = q.1 := by
      rw [rationalPrimeFinitePlaceInteger,
        (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
          q).apply_symm_apply,
        PadicInt.algebraMap_apply,
        PadicInt.coe_natCast]
    _ =
      rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap ℚ
          (adicAbv₀).Completion
          (q.1 : ℚ)) := by
      rw [
        rationalFinitePlaceCompletionRingEquivPadic_algebraMap]
      norm_num

/-- The rational prime as a field unit of its absolute-value completion. -/
noncomputable def rationalPrimeFinitePlaceFieldUnit
    (q : Nat.Primes) :
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completionˣ :=
  Units.mk0
    (rationalPrimeFinitePlaceInteger q :
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion)
    (fun hzero => (rationalPrimeFinitePlaceInteger_irreducible q).ne_zero
          (Subtype.ext hzero))

/-- In the inverse-standard local reciprocity normalization, the rational
prime itself has normalized additive value `-1`. -/
theorem rationalPrimeFinitePlaceFieldUnit_valuationMap
    (q : Nat.Primes) :
    IsNonarchimedeanLocalField.valuationMap
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (Additive.ofMul
          (rationalPrimeFinitePlaceFieldUnit q)) =
      -1 := by
  simpa [IsNonarchimedeanLocalField.valuationMap_apply] using
    (LocalFieldTheory.v_integerRingIrreducibleFieldUnit
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion
      (rationalPrimeFinitePlaceInteger q)
      (rationalPrimeFinitePlaceInteger_irreducible q)
      (rationalPrimeFinitePlaceFieldUnit q) rfl)

/-- The rational `q`-unit part of `x`, pulled back from `ℤ_qˣ` to the
valuation ring of the absolute-value completion. -/
noncomputable def rationalPrimeUnitFinitePlaceIntegerUnit
    (x : ℚˣ) (q : Nat.Primes) :
    𝒪[(HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion]ˣ :=
  Units.map
      (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
        q).symm.toMonoidHom
    (padicIntUnitOfRat q
      (rationalPrimeUnit x q : ℚ)
      (rationalPrimeUnit x q).ne_zero
      (padicValRat_rationalPrimeUnit x q))

/-- Forgetting the integrality proof from the pulled-back `q`-unit gives
the ordinary image of the rational `q`-unit in the completion field. -/
theorem rationalPrimeUnitFinitePlaceIntegerUnit_coe
    (x : ℚˣ) (q : Nat.Primes) :
    (((rationalPrimeUnitFinitePlaceIntegerUnit x q :
        𝒪[(HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion]ˣ) :
        𝒪[(HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion]) :
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion) =
      algebraMap ℚ
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (rationalPrimeUnit x q : ℚ) := by
  apply
    (rationalFinitePlaceCompletionRingEquivPadic q).injective
  let adicAbv₀ := HeightOneSpectrum.adicAbv ℚ (RayClass.rationalPrime q)
  change
    rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap
          𝒪[(adicAbv₀).Completion]
          (adicAbv₀).Completion
          (rationalPrimeUnitFinitePlaceIntegerUnit x q :
            𝒪[(adicAbv₀).Completion])) =
      rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap ℚ
          (adicAbv₀).Completion
          (rationalPrimeUnit x q : ℚ))
  calc
    _ =
      algebraMap ℤ_[q.1] ℚ_[q.1]
        ((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q)
          (rationalPrimeUnitFinitePlaceIntegerUnit x q :
            𝒪[(adicAbv₀).Completion])) :=
        rationalFinitePlaceCompletionIntegerRingEquivPadicInt_coe q
          (rationalPrimeUnitFinitePlaceIntegerUnit x q :
            𝒪[(adicAbv₀).Completion])
    _ =
      ((padicIntUnitOfRat q
        (rationalPrimeUnit x q : ℚ)
        (rationalPrimeUnit x q).ne_zero
        (padicValRat_rationalPrimeUnit x q) :
          ℤ_[q.1]) : ℚ_[q.1]) := by
      rw [rationalPrimeUnitFinitePlaceIntegerUnit]
      simp [PadicInt.algebraMap_apply]
    _ = ((rationalPrimeUnit x q : ℚ) : ℚ_[q.1]) := by
      rw [padicIntUnitOfRat_coe]
    _ =
      rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap ℚ
          (adicAbv₀).Completion
          (rationalPrimeUnit x q : ℚ)) := by
      rw [
        rationalFinitePlaceCompletionRingEquivPadic_algebraMap]
      simp

/-- The completion field unit underlying the pulled-back rational `q`-unit
has normalized additive value zero. -/
theorem rationalPrimeUnitFinitePlaceField_valuationMap
    (x : ℚˣ) (q : Nat.Primes) :
    IsNonarchimedeanLocalField.valuationMap
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (Additive.ofMul
          (IsNonarchimedeanLocalField.integerUnitsToFieldUnits
            (HeightOneSpectrum.adicAbv ℚ
              (RayClass.rationalPrime q)).Completion
            (rationalPrimeUnitFinitePlaceIntegerUnit x q))) =
      0 := by
  rw [IsNonarchimedeanLocalField.valuationMap_apply]
  exact
    IsNonarchimedeanLocalField.v_integerUnitsToFieldUnits
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion
      (rationalPrimeUnitFinitePlaceIntegerUnit x q)

/-- The rational prime `q`, regarded as a unit of `ℚ`. -/
def rationalPrimeGeneratorUnit (q : Nat.Primes) : ℚˣ :=
  Units.mk0 (q.1 : ℚ) (by exact_mod_cast q.2.ne_zero)

/-- The underlying rational number of the prime generator unit is `q`. -/
@[simp]
theorem rationalPrimeGeneratorUnit_coe (q : Nat.Primes) :
    (rationalPrimeGeneratorUnit q : ℚ) = q.1 :=
  rfl

/-- Reattaching the removed `q`-power to the rational `q`-unit recovers
the original rational field unit. -/
theorem rationalPrimeGeneratorUnit_zpow_mul_rationalPrimeUnit
    (x : ℚˣ) (q : Nat.Primes) :
    rationalPrimeGeneratorUnit q ^
          padicValRat q.1 (x : ℚ) *
        rationalPrimeUnit x q =
      x := by
  rw [rationalPrimeGeneratorUnit, rationalPrimeUnit,
    ← mul_assoc, ← zpow_add]
  simp

/-- The source unit in the absolute-value completion represented by the
finite component of a rational principal idele. -/
noncomputable def rationalPrincipalFinitePlaceInput
    (x : ℚˣ) (q : Nat.Primes) :
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completionˣ :=
  (finitePlaceCompletionUnitsContinuousMulEquiv
      (RayClass.rationalPrime q)).symm
    (IdeleGroup.finiteComponent
      (RayClass.rationalPrime q)
      (IdeleGroup.principalIdele ℚ x))

/-- The source unit represented by a principal finite component is the
ordinary image of the rational field unit in the absolute-value
completion. -/
theorem rationalPrincipalFinitePlaceInput_eq_algebraMap
    (x : ℚˣ) (q : Nat.Primes) :
    rationalPrincipalFinitePlaceInput x q =
      Units.map
        (algebraMap ℚ
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion).toMonoidHom
        x := by
  apply Units.ext
  let v :=
    RayClass.rationalPrime q
  let vQ := HeightOneSpectrum.adicAbv ℚ v
  let component :=
    IdeleGroup.finiteComponent v
      (IdeleGroup.principalIdele ℚ x)
  apply (finitePlaceCompletionRingEquiv v).injective
  change
    finitePlaceCompletionRingEquiv v
        (rationalPrincipalFinitePlaceInput x q : vQ.Completion) =
      finitePlaceCompletionRingEquiv v
        (algebraMap ℚ vQ.Completion (x : ℚ))
  have hCompletion :
      finitePlaceCompletionRingEquiv v
          (rationalPrincipalFinitePlaceInput x q :
            vQ.Completion) =
        component := by
    exact congrArg Units.val
      ((finitePlaceCompletionUnitsContinuousMulEquiv v).apply_symm_apply
        component)
  let algebraMap₀ := algebraMap ℚ (v.adicCompletion ℚ) (x : ℚ)
  have hComponent :
      component =
        algebraMap₀ := by
    let adicCompletionEquiv₀ := Padic.adicCompletionEquiv (𝓞 ℚ) q
    apply (adicCompletionEquiv₀).symm.injective
    calc
      _ =
        algebraMap ℚ ℚ_[q.1] (x : ℚ) := by
          dsimp only [component]
          rw [IdeleGroup.finiteComponent_principalIdele]
          exact
            (adicCompletionEquiv₀).symm.commutes (x : ℚ)
      _ = (adicCompletionEquiv₀).symm
          (algebraMap₀) := by
        symm
        exact
          (adicCompletionEquiv₀).symm.commutes (x : ℚ)
  calc
    _ =
      (component : v.adicCompletion ℚ) := hCompletion
    _ = algebraMap₀ := hComponent
    _ = finitePlaceCompletionRingEquiv v
        (algebraMap ℚ vQ.Completion (x : ℚ)) := by
      symm
      exact
        (finitePlaceCompletionAlgEquiv v).commutes (x : ℚ)

/-- The normalized local exponent of a rational principal finite
component is the negative of the usual `q`-adic exponent.  The minus sign
records the inverse-standard local reciprocity convention in which a
prime element has normalized value `-1`. -/
theorem rationalPrincipalFiniteComponent_valuationMap
    (x : ℚˣ) (q : Nat.Primes) :
    IsNonarchimedeanLocalField.valuationMap
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (Additive.ofMul
          ((finitePlaceCompletionUnitsContinuousMulEquiv
            (RayClass.rationalPrime q)).symm
            (IdeleGroup.finiteComponent
              (RayClass.rationalPrime q)
              (IdeleGroup.principalIdele ℚ x)))) =
      -padicValRat q.1 (x : ℚ) := by
  let F :=
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion
  let embed :=
    Units.map (algebraMap ℚ F).toMonoidHom
  have hInput := rationalPrincipalFinitePlaceInput_eq_algebraMap x q
  have hPrime :
      embed (rationalPrimeGeneratorUnit q) =
        (rationalPrimeFinitePlaceFieldUnit q) := by
    apply Units.ext
    exact
      (rationalPrimeFinitePlaceInteger_coe q).symm
  have hUnit :
      embed (rationalPrimeUnit x q) =
        (IsNonarchimedeanLocalField.integerUnitsToFieldUnits
          F (rationalPrimeUnitFinitePlaceIntegerUnit x q)) := by
    apply Units.ext
    exact
      (rationalPrimeUnitFinitePlaceIntegerUnit_coe
        x q).symm
  change
    IsNonarchimedeanLocalField.valuationMap F
        (Additive.ofMul
          (rationalPrincipalFinitePlaceInput x q)) =
      -padicValRat q.1 (x : ℚ)
  rw [hInput]
  conv_lhs =>
    rw [← rationalPrimeGeneratorUnit_zpow_mul_rationalPrimeUnit
      x q]
  rw [map_mul, map_zpow, hPrime, hUnit,
    IsNonarchimedeanLocalField.valuationMap_ofMul_mul,
    IsNonarchimedeanLocalField.valuationMap_ofMul_zpow,
    rationalPrimeFinitePlaceFieldUnit_valuationMap,
    rationalPrimeUnitFinitePlaceField_valuationMap]
  ring

/-- A cyclotomic automorphism which raises the selected primitive root to
the `q`-th power has cyclotomic character equal to the residue-prime unit. -/
private theorem rationalCyclotomicLevel_galEquivZMod_eq_unitOfCoprime
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ))
    (σ : KummerTheory.rationalCyclotomicLevel m ≃ₐ[ℚ]
      KummerTheory.rationalCyclotomicLevel m)
    (hσ :
      σ (rationalCyclotomicLevelPrimitiveRoot m) =
        rationalCyclotomicLevelPrimitiveRoot m ^ q.1) :
    IsCyclotomicExtension.Rat.galEquivZMod
        (m : ℕ) (KummerTheory.rationalCyclotomicLevel m) σ =
      ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq) := by
  let ζ := rationalCyclotomicLevelPrimitiveRoot m
  have hζ :=
    rationalCyclotomicLevelPrimitiveRoot_isPrimitiveRoot m
  have hPowers :
      ζ ^
          (IsCyclotomicExtension.Rat.galEquivZMod
            (m : ℕ) (KummerTheory.rationalCyclotomicLevel m) σ).val.val =
        ζ ^ q.1 :=
    (IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
      (m : ℕ) (KummerTheory.rationalCyclotomicLevel m) σ
      hζ.pow_eq_one).symm.trans hσ
  rw [(hζ.isOfFinOrder m.ne_zero).pow_inj_mod,
    ← hζ.eq_orderOf,
    ← ZMod.natCast_eq_natCast_iff',
    ZMod.natCast_val] at hPowers
  apply Units.ext
  simpa using hPowers

 abbrev rationalCyclotomicArtinPlace (q : Nat.Primes) :
    HeightOneSpectrum (𝓞 ℚ) :=
  RayClass.rationalPrime q

 abbrev rationalCyclotomicArtinBaseAbv (q : Nat.Primes) :
    AbsoluteValue ℚ ℝ :=
  HeightOneSpectrum.adicAbv ℚ (rationalCyclotomicArtinPlace q)

 section

variable (m : ℕ+)

abbrev rationalCyclotomicArtinLevel :=
  KummerTheory.rationalCyclotomicLevel m

 abbrev rationalCyclotomicArtinExtension (q : Nat.Primes) :
    AbsoluteValueExtension
      (rationalCyclotomicArtinBaseAbv q)
      (rationalCyclotomicArtinLevel m) :=
  chosenFinitePlaceExtension
    (L := rationalCyclotomicArtinLevel m)
    (rationalCyclotomicArtinPlace q)

 abbrev rationalCyclotomicArtinLocalizedField (q : Nat.Primes) :=
  AlgebraicNumberTheory.Valuations.LocalizedCompletion
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)

end

@[reducible]
noncomputable local instance rationalCyclotomicArtinExtensionAlgebra
    (m : ℕ+) (q : Nat.Primes) :
    Algebra ℚ
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra
    (K := ℚ) (rationalCyclotomicArtinExtension m q).1

@[reducible]
noncomputable local instance rationalCyclotomicArtinExtensionSMul
    (m : ℕ+) (q : Nat.Primes) :
    SMul ℚ
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  (rationalCyclotomicArtinExtensionAlgebra m q).toSMul

@[reducible]
noncomputable local instance
    rationalCyclotomicArtinCompletionAlgebra
    (m : ℕ+) (q : Nat.Primes) :
    Algebra (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  AbsoluteValue.completionAlgebra
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q).1
    (rationalCyclotomicArtinExtension m q).2

@[reducible]
noncomputable local instance rationalCyclotomicArtinLocalizedAlgebra
    (m : ℕ+) (q : Nat.Primes) :
    Algebra (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) :=
  finitePlaceLocalArtinLocalizedAlgebra
    (K := ℚ) (L := rationalCyclotomicArtinLevel m)
    (rationalCyclotomicArtinPlace q)
    (rationalCyclotomicArtinExtension m q)

noncomputable local instance
    rationalCyclotomicArtinLocalizedGlobalAlgebra
    (m : ℕ+) (q : Nat.Primes) :
    Algebra ℚ (rationalCyclotomicArtinLocalizedField m q) :=
  LocalClassFieldTheory.localizedCompletionGlobalAlgebra
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)

noncomputable local instance
    rationalCyclotomicArtinLocalizedGlobalSMul
    (m : ℕ+) (q : Nat.Primes) :
    SMul ℚ (rationalCyclotomicArtinLocalizedField m q) :=
  (rationalCyclotomicArtinLocalizedGlobalAlgebra m q).toSMul

noncomputable local instance
    rationalCyclotomicArtinLocalizedScalarTower
    (m : ℕ+) (q : Nat.Primes) :
    IsScalarTower ℚ
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) := by
  constructor
  intro r x y
  simp

noncomputable local instance
    rationalCyclotomicArtinLocalizedFiniteDimensional
    (m : ℕ+) (q : Nat.Primes) :
    FiniteDimensional
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) :=
  finitePlaceLocalArtinFiniteDimensional
    (K := ℚ) (L := rationalCyclotomicArtinLevel m)
    (rationalCyclotomicArtinPlace q)
    (rationalCyclotomicArtinExtension m q)

noncomputable local instance
    rationalCyclotomicArtinLocalizedIsAbelianGalois
    (m : ℕ+) (q : Nat.Primes) :
    IsAbelianGalois
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) :=
  finitePlaceLocalArtinIsAbelianGalois
    (K := ℚ) (L := rationalCyclotomicArtinLevel m)
    (rationalCyclotomicArtinPlace q)
    (rationalCyclotomicArtinExtension m q)
    (inferInstance :
      FiniteDimensional ℚ (rationalCyclotomicArtinLevel m))

noncomputable local instance
    rationalCyclotomicArtinLocalizedIsSeparable
    (m : ℕ+) (q : Nat.Primes) :
    Algebra.IsSeparable
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) :=
  (rationalCyclotomicArtinLocalizedIsAbelianGalois m q).toIsGalois.to_isSeparable

noncomputable local instance
    rationalCyclotomicArtinLocalizedIsCyclotomic
    (m : ℕ+) (q : Nat.Primes) :
    IsCyclotomicExtension {(m : ℕ)}
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) :=
  rationalCyclotomicLevel_localizedCompletion_isCyclotomicExtension
    m (rationalCyclotomicArtinPlace q)

noncomputable local instance
    rationalCyclotomicArtinExtensionFiniteDimensional
    (m : ℕ+) (q : Nat.Primes) :
    FiniteDimensional
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  completionModuleFinite
    (rationalCyclotomicArtinBaseAbv q)
    (RayClass.adicAbv_isNontrivial
      (rationalCyclotomicArtinPlace q))
    (rationalCyclotomicArtinExtension m q)

noncomputable local instance
    rationalCyclotomicArtinExtensionContinuousSMul
    (m : ℕ+) (q : Nat.Primes) :
    ContinuousSMul
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  continuousSMul_of_algebraMap _ _
    (AbsoluteValue.completionMap_isometry
      (rationalCyclotomicArtinBaseAbv q)
      (rationalCyclotomicArtinExtension m q).1
      (rationalCyclotomicArtinExtension m q).2).continuous

noncomputable local instance
    rationalCyclotomicArtinExtensionLocallyCompact
    (m : ℕ+) (q : Nat.Primes) :
    LocallyCompactSpace
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  LocallyCompactSpace.of_finiteDimensional_of_complete
    (rationalCyclotomicArtinBaseAbv q).Completion
    (rationalCyclotomicArtinExtension m q).1.Completion

 noncomputable def
    rationalCyclotomicArtinLocalizedEquivCompletion
    (m : ℕ+) (q : Nat.Primes) :
    rationalCyclotomicArtinLocalizedField m q ≃ᵢ
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  { toEquiv :=
      (localizedCompletionEquivCompletion
        (rationalCyclotomicArtinBaseAbv q)
        (RayClass.adicAbv_isNontrivial
          (rationalCyclotomicArtinPlace q))
        (rationalCyclotomicArtinExtension m q)).toEquiv
    isometry_toFun :=
      Isometry.of_dist_eq fun _ _ => rfl }

noncomputable local instance
    rationalCyclotomicArtinLocalizedLocallyCompact
    (m : ℕ+) (q : Nat.Primes) :
    LocallyCompactSpace
      (rationalCyclotomicArtinLocalizedField m q) :=
  ((rationalCyclotomicArtinLocalizedEquivCompletion m q).toHomeomorph.locallyCompactSpace_iff).2
    inferInstance

noncomputable local instance
    rationalCyclotomicArtinLocalizedIsUltrametricDist
    (m : ℕ+) (q : Nat.Primes) :
    IsUltrametricDist
      (rationalCyclotomicArtinLocalizedField m q) :=
  localizedCompletionIsUltrametricDist
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))

noncomputable local instance rationalCyclotomicArtinLocalizedValued
    (m : ℕ+) (q : Nat.Primes) :
    Valued (rationalCyclotomicArtinLocalizedField m q) ℝ≥0 :=
  localizedCompletionFinitePlaceValued
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))

@[reducible]
noncomputable local instance
    rationalCyclotomicArtinLocalizedValuativeRel
    (m : ℕ+) (q : Nat.Primes) :
    ValuativeRel (rationalCyclotomicArtinLocalizedField m q) :=
  localizedCompletionFinitePlaceValuativeRel
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))

noncomputable local instance
    rationalCyclotomicArtinLocalizedValuationCompatible
    (m : ℕ+) (q : Nat.Primes) :
    (Valued.v : Valuation
      (rationalCyclotomicArtinLocalizedField m q) ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation _

noncomputable local instance
    rationalCyclotomicArtinLocalizedValuationHasExtension
    (m : ℕ+) (q : Nat.Primes) :
    Valuation.HasExtension
      (ValuativeRel.valuation
        (rationalCyclotomicArtinBaseAbv q).Completion)
      (ValuativeRel.valuation
        (rationalCyclotomicArtinLocalizedField m q)) :=
  localizedCompletionValuationHasExtension
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))

noncomputable local instance
    rationalCyclotomicArtinLocalizedValuationIsNontrivial
    (m : ℕ+) (q : Nat.Primes) :
    (ValuativeRel.valuation
      (rationalCyclotomicArtinLocalizedField m q)).IsNontrivial :=
  Valuation.IsNontrivial.of_hasExtension
    (ValuativeRel.valuation
      (rationalCyclotomicArtinBaseAbv q).Completion)
    (ValuativeRel.valuation
      (rationalCyclotomicArtinLocalizedField m q))

noncomputable local instance
    rationalCyclotomicArtinLocalizedValuativeRelIsNontrivial
    (m : ℕ+) (q : Nat.Primes) :
    ValuativeRel.IsNontrivial
      (rationalCyclotomicArtinLocalizedField m q) :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (ValuativeRel.valuation
      (rationalCyclotomicArtinLocalizedField m q))).2 inferInstance

noncomputable local instance
    rationalCyclotomicArtinLocalizedIsValuativeTopology
    (m : ℕ+) (q : Nat.Primes) :
    IsValuativeTopology
      (rationalCyclotomicArtinLocalizedField m q) :=
  isValuativeTopology_of_valued_ofValuation
    (rationalCyclotomicArtinLocalizedField m q) ℝ≥0

noncomputable local instance
    rationalCyclotomicArtinLocalizedIsNonarchimedeanLocalField
    (m : ℕ+) (q : Nat.Primes) :
    IsNonarchimedeanLocalField
      (rationalCyclotomicArtinLocalizedField m q) :=
  { toIsValuativeTopology := inferInstance
    toLocallyCompactSpace := inferInstance
    toIsNontrivial := inferInstance }

noncomputable local instance
    rationalCyclotomicArtinLocalizedIntegerAlgebra
    (m : ℕ+) (q : Nat.Primes) :
    Algebra
      𝒪[(rationalCyclotomicArtinBaseAbv q).Completion]
      (rationalCyclotomicArtinLocalizedField m q) :=
  Algebra.ofSubsemiring
    𝒪[(rationalCyclotomicArtinBaseAbv q).Completion]

noncomputable local instance
    rationalCyclotomicArtinLocalizedIsIntegralClosure
    (m : ℕ+) (q : Nat.Primes) :
    IsIntegralClosure
      𝒪[rationalCyclotomicArtinLocalizedField m q]
      𝒪[(rationalCyclotomicArtinBaseAbv q).Completion]
      (rationalCyclotomicArtinLocalizedField m q) :=
  localizedCompletionIsIntegralClosureWithExtension
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (RayClass.adicAbv_isNontrivial
      (rationalCyclotomicArtinPlace q))
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))

noncomputable local instance
    rationalCyclotomicArtinLocalizedIntegerModuleFinite
    (m : ℕ+) (q : Nat.Primes) :
    Module.Finite
      𝒪[(rationalCyclotomicArtinBaseAbv q).Completion]
      𝒪[rationalCyclotomicArtinLocalizedField m q] :=
  integerRing_moduleFinite_of_isIntegralClosure
    (rationalCyclotomicArtinBaseAbv q).Completion
    (rationalCyclotomicArtinLocalizedField m q)

section RationalCyclotomicPrincipalPrime

/-! ## Ramified prime-power transport

This section reuses the canonical finite-place Artin tower above.  In
particular, it introduces no parallel completion/localization instance tower. -/

noncomputable local instance
    rationalCyclotomicPrincipalPrimeLevelIsCyclotomicExtension
    (p : Nat.Primes) (n : ℕ) :
    IsCyclotomicExtension {p.1 ^ (n + 1)} ℚ
      (KummerTheory.rationalCyclotomicLevel
        (rationalCyclotomicPrincipalPrimeModulus p n)) := by
  change
    IsCyclotomicExtension
      {(rationalCyclotomicPrincipalPrimeModulus p n : ℕ)} ℚ
      (KummerTheory.rationalCyclotomicLevel
        (rationalCyclotomicPrincipalPrimeModulus p n))
  exact
    KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
      (rationalCyclotomicPrincipalPrimeModulus p n)

 abbrev rationalCyclotomicPrincipalPrimeLevel
    (m : ℕ+) :=
  rationalCyclotomicArtinLevel m

/-- The `ℚ_[p]`-algebra structure on the localized cyclotomic completion,
transported through the canonical comparison with the `p`-adic completion. -/
@[reducible]
noncomputable def
    rationalCyclotomicPrincipalPrimeLocalizedPadicAlgebra
    (m : ℕ+) (p : Nat.Primes) :
    Algebra ℚ_[p.1]
      (rationalCyclotomicLocalizedCompletion m
        (RayClass.rationalPrime p)) :=
  ((algebraMap
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion
      (rationalCyclotomicLocalizedCompletion m
        (RayClass.rationalPrime p))).comp
    (rationalFinitePlaceCompletionRingEquivPadic p).symm.toRingHom).toAlgebra

@[reducible]
noncomputable local instance
    rationalCyclotomicArtinLocalizedPadicAlgebra
    (m : ℕ+) (p : Nat.Primes) :
    Algebra ℚ_[p.1] (rationalCyclotomicArtinLocalizedField m p) :=
  rationalCyclotomicPrincipalPrimeLocalizedPadicAlgebra m p

 noncomputable def rationalFinitePlaceCompletionAlgEquivPadic
    (p : Nat.Primes) :
    (rationalCyclotomicArtinBaseAbv p).Completion ≃ₐ[ℚ] ℚ_[p.1] :=
  AlgEquiv.ofRingEquiv
    (f := rationalFinitePlaceCompletionRingEquivPadic p)
    (rationalFinitePlaceCompletionRingEquivPadic_algebraMap p)

noncomputable local instance
    rationalCyclotomicArtinLocalizedPadicScalarTower
    (m : ℕ+) (p : Nat.Primes) :
    IsScalarTower ℚ ℚ_[p.1]
      (rationalCyclotomicArtinLocalizedField m p) := by
  constructor
  intro r x y
  simp

section

variable (m : ℕ+) (p : Nat.Primes)

private theorem rationalCyclotomicArtin_padic_algebraMap :
    algebraMap (rationalCyclotomicArtinBaseAbv p).Completion
        (rationalCyclotomicArtinLocalizedField m p) =
      (algebraMap ℚ_[p.1]
        (rationalCyclotomicArtinLocalizedField m p)) ∘
        (rationalFinitePlaceCompletionAlgEquivPadic p) := by
  funext a
  let algebraMap₀ := algebraMap (rationalCyclotomicArtinBaseAbv p).Completion (rationalCyclotomicArtinLocalizedField m p)
  change
    algebraMap₀ a =
      algebraMap₀
        ((rationalFinitePlaceCompletionRingEquivPadic p).symm
          (rationalFinitePlaceCompletionRingEquivPadic p a))
  exact
    congrArg
      (algebraMap₀)
      ((rationalFinitePlaceCompletionRingEquivPadic p).symm_apply_apply a).symm

private theorem rationalCyclotomicArtin_algebraAdjoin_restrictScalars :
    (Algebra.adjoin (rationalCyclotomicArtinBaseAbv p).Completion
      (Set.singleton (rationalCyclotomicLocalizedPrimitiveRoot m
        (rationalCyclotomicArtinPlace p)) :
        Set (rationalCyclotomicArtinLocalizedField m p))).restrictScalars ℚ =
      (Algebra.adjoin ℚ_[p.1]
        (Set.singleton (rationalCyclotomicLocalizedPrimitiveRoot m
          (rationalCyclotomicArtinPlace p)) :
          Set (rationalCyclotomicArtinLocalizedField m p))).restrictScalars ℚ := Algebra.restrictScalars_adjoin_of_algEquiv

      (rationalFinitePlaceCompletionAlgEquivPadic p)
      (rationalCyclotomicArtin_padic_algebraMap m p)
      (Set.singleton (rationalCyclotomicLocalizedPrimitiveRoot m
        (rationalCyclotomicArtinPlace p)) :
        Set (rationalCyclotomicArtinLocalizedField m p))

private theorem
    rationalCyclotomicArtin_baseAlgebraAdjoin_restrict_eq_top :
    (Algebra.adjoin (rationalCyclotomicArtinBaseAbv p).Completion
      (Set.singleton (rationalCyclotomicLocalizedPrimitiveRoot m
        (rationalCyclotomicArtinPlace p)) :
        Set (rationalCyclotomicArtinLocalizedField m p))).restrictScalars ℚ =
      (⊤ : Subalgebra (rationalCyclotomicArtinBaseAbv p).Completion
      (rationalCyclotomicArtinLocalizedField m p)).restrictScalars ℚ := by
  exact congrArg
    (fun A : Subalgebra (rationalCyclotomicArtinBaseAbv p).Completion
      (rationalCyclotomicArtinLocalizedField m p) => A.restrictScalars ℚ)
    (IsCyclotomicExtension.adjoin_primitive_root_eq_top

      (rationalCyclotomicLocalizedPrimitiveRoot_isPrimitiveRoot
       m (rationalCyclotomicArtinPlace p)))

private theorem rationalCyclotomicArtin_restrictScalars_top_base_eq_padic :
    (⊤ : Subalgebra (rationalCyclotomicArtinBaseAbv p).Completion
        (rationalCyclotomicArtinLocalizedField m p)).restrictScalars ℚ =
      (⊤ : Subalgebra ℚ_[p.1]
        (rationalCyclotomicArtinLocalizedField m p)).restrictScalars ℚ :=
  (Subalgebra.restrictScalars_top ℚ).trans
    (Subalgebra.restrictScalars_top ℚ).symm

private theorem
    rationalCyclotomicArtin_padicAlgebraAdjoin_restrict_eq_top :
    (Algebra.adjoin ℚ_[p.1]
      (Set.singleton (rationalCyclotomicLocalizedPrimitiveRoot m
        (rationalCyclotomicArtinPlace p)) :
        Set (rationalCyclotomicArtinLocalizedField m p))).restrictScalars ℚ =
      (⊤ : Subalgebra ℚ_[p.1]
        (rationalCyclotomicArtinLocalizedField m p)).restrictScalars ℚ := (rationalCyclotomicArtin_algebraAdjoin_restrictScalars m p).symm.trans
      ((rationalCyclotomicArtin_baseAlgebraAdjoin_restrict_eq_top m p).trans
        (rationalCyclotomicArtin_restrictScalars_top_base_eq_padic m p))

end

/-- The finite-dimensional instance for the standard multiplicative level,
named once so all consumers use the same proof term. -/
theorem rationalCyclotomicPrincipalPrimePadicLevelFiniteDimensional
    (p : Nat.Primes) (n : ℕ) :
    FiniteDimensional ℚ_[p.1]
      (standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p.1) n) :=
  standardLubinTateLevelField_finiteDimensional
    (padicMultiplicativeLubinTateSeries_isUniformizer p.1) n

attribute [local instance]
  rationalCyclotomicPrincipalPrimePadicLevelFiniteDimensional

noncomputable local instance
    rationalCyclotomicPrincipalPrimePadicLevelIsAbelianGalois
    (p : Nat.Primes) (n : ℕ) :
    IsAbelianGalois ℚ_[p.1]
      (RationalCyclotomicPrincipalPrimePadicLevel p n) :=
  standardLubinTateLevelField_isAbelianGalois
    (padicLocalField p.1)
    (padicMultiplicativeLubinTateSeries_isUniformizer p.1) n

@[reducible]
noncomputable local instance rationalPrimeFactorCompletionPadicAlgebra
    (p : Nat.Primes) :
    Algebra (RationalCyclotomicPrincipalPrimeCompletion p) ℚ_[p.1] :=
  (rationalFinitePlaceCompletionRingEquivPadic p).toRingHom.toAlgebra

section

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- The genuine multiplicative Lubin--Tate level is generated by its
primitive `p ^ (n + 1)`-st root of unity. -/
theorem padicMultiplicativePrimitiveRoot_adjoin_eq_top :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    let T := standardLubinTateLevelField hπ n
    Algebra.adjoin ℚ_[p]
        ({padicMultiplicativePrimitiveRoot p n} : Set T) =
      ⊤ := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let T := standardLubinTateLevelField hπ n
  let ζ := padicMultiplicativePrimitiveRoot p n
  let m := p ^ (n + 1)
  let : NeZero m :=
    ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩
  let :=
    standardLubinTateLevelField_finiteDimensional hπ n
  have hζ : IsPrimitiveRoot ζ m := by
    simpa using
      padicMultiplicativePrimitiveRoot_isPrimitiveRoot p n
  let A :=
    IntermediateField.adjoin ℚ_[p] {ζ}
  let :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ_[p]
  have hAfin := IsCyclotomicExtension.finrank A
        (by
          simpa using
            padicCyclotomicPolynomial_irreducible_prime_pow_succ
              p n)
  have hTfin :
      Module.finrank ℚ_[p] T = Nat.totient m := by
    rw [standardLubinTateLevelField_finrank hπ n]
    have hcard :
        Nat.card (padicLocalField p).residueField = p := by
      simpa [padicLocalField] using
        padicCompleteDVF_residueField_card p
    rw [hcard, Nat.totient_prime_pow
      Fact.out (Nat.succ_pos n)]
    simp [Nat.mul_comm]
  have hAeq : A = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    simpa using hAfin.trans hTfin.symm
  calc
    _ = A.toSubalgebra := (IntermediateField.adjoin_toSubalgebra
          ({ζ} : Set T)).symm
    _ = (⊤ : IntermediateField ℚ_[p] T).toSubalgebra :=
      congrArg IntermediateField.toSubalgebra hAeq
    _ = ⊤ := rfl

/-- The standard multiplicative Lubin--Tate level is the actual
`p ^ (n + 1)`-cyclotomic extension of `ℚ_p`. -/
theorem padicMultiplicativeLevel_isCyclotomicExtension :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    let T := standardLubinTateLevelField hπ n
    IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] T := by
  exact
    padic_isCyclotomicExtension_of_primitiveRoot_adjoin_eq_top
      (padicMultiplicativePrimitiveRoot p n)
      (padicMultiplicativePrimitiveRoot_isPrimitiveRoot p n)
      (padicMultiplicativePrimitiveRoot_adjoin_eq_top p n)

end

private theorem
    rationalCyclotomicPrincipalPrimeLocalizedPrimitiveRoot_isPrimitiveRoot
    (p : Nat.Primes) (n : ℕ) :
    IsPrimitiveRoot
      (rationalCyclotomicLocalizedPrimitiveRoot
        (rationalCyclotomicPrincipalPrimeModulus p n)
        (RayClass.rationalPrime p))
      (p.1 ^ (n + 1)) := by
  change
    IsPrimitiveRoot
      (rationalCyclotomicLocalizedPrimitiveRoot
        (rationalCyclotomicPrincipalPrimeModulus p n)
        (RayClass.rationalPrime p))
      (rationalCyclotomicPrincipalPrimeModulus p n : ℕ)
  exact
    rationalCyclotomicLocalizedPrimitiveRoot_isPrimitiveRoot
      (rationalCyclotomicPrincipalPrimeModulus p n)
      (RayClass.rationalPrime p)

 section

variable (p : Nat.Primes) (n : ℕ)

theorem
    rationalCyclotomicPrincipalPrimeLocalizedLevel_isCyclotomicExtension :
    IsCyclotomicExtension {p.1 ^ (n + 1)} ℚ_[p.1]
      (rationalCyclotomicArtinLocalizedField
        (rationalCyclotomicPrincipalPrimeModulus p n) p) := padic_isCyclotomicExtension_of_primitiveRoot_adjoin_eq_top
      (rationalCyclotomicLocalizedPrimitiveRoot
        (rationalCyclotomicPrincipalPrimeModulus p n)
        (rationalCyclotomicArtinPlace p))
      (rationalCyclotomicPrincipalPrimeLocalizedPrimitiveRoot_isPrimitiveRoot
        p n)
      (((Subalgebra.restrictScalars_injective ℚ)
      (rationalCyclotomicArtin_padicAlgebraAdjoin_restrict_eq_top
        (rationalCyclotomicPrincipalPrimeModulus p n) p)))

/-- The chosen localized global cyclotomic level, transported over the
completion equivalence, is the standard multiplicative Lubin--Tate level. -/
noncomputable def rationalCyclotomicLocalizedCompletionPadicAlgEquiv :
    rationalCyclotomicArtinLocalizedField
        (rationalCyclotomicPrincipalPrimeModulus p n) p ≃ₐ[ℚ_[p.1]]
      RationalCyclotomicPrincipalPrimePadicLevel p n := by
  letI : IsCyclotomicExtension {p.1 ^ (n + 1)} ℚ_[p.1]
      (rationalCyclotomicArtinLocalizedField
        (rationalCyclotomicPrincipalPrimeModulus p n) p) :=
    rationalCyclotomicPrincipalPrimeLocalizedLevel_isCyclotomicExtension p n
  letI : IsCyclotomicExtension {p.1 ^ (n + 1)} ℚ_[p.1]
      (RationalCyclotomicPrincipalPrimePadicLevel p n) :=
    padicMultiplicativeLevel_isCyclotomicExtension p.1 n
  exact
    IsCyclotomicExtension.algEquiv
      {p.1 ^ (n + 1)} ℚ_[p.1]
      (rationalCyclotomicArtinLocalizedField
        (rationalCyclotomicPrincipalPrimeModulus p n) p)
      (RationalCyclotomicPrincipalPrimePadicLevel p n)

end

/-! ## The ramified principal finite-place factor -/

private theorem
    rationalCyclotomicPrincipalPrime_galEquivZMod_eq_of_action
    (p : Nat.Primes) (n : ℕ)
    (sigma : Gal(
      rationalCyclotomicPrincipalPrimeLevel
        (rationalCyclotomicPrincipalPrimeModulus p n) / ℚ))
    (a : (ZMod (p.1 ^ (n + 1)))ˣ)
    (haction :
      sigma (rationalCyclotomicLevelPrimitiveRoot
          (rationalCyclotomicPrincipalPrimeModulus p n)) =
        rationalCyclotomicLevelPrimitiveRoot
            (rationalCyclotomicPrincipalPrimeModulus p n) ^ a.val.val) :
    IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ (n + 1))
        (rationalCyclotomicPrincipalPrimeLevel
          (rationalCyclotomicPrincipalPrimeModulus p n))
        (hK :=
          KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
            (rationalCyclotomicPrincipalPrimeModulus p n)) sigma =
      a := by
  let m := rationalCyclotomicPrincipalPrimeModulus p n
  let L := rationalCyclotomicPrincipalPrimeLevel m
  let zeta := rationalCyclotomicLevelPrimitiveRoot m
  have hzeta : IsPrimitiveRoot zeta (p.1 ^ (n + 1)) := by
    change
      IsPrimitiveRoot
        (rationalCyclotomicLevelPrimitiveRoot m) (m : ℕ)
    exact rationalCyclotomicLevelPrimitiveRoot_isPrimitiveRoot m
  change
    IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ (n + 1)) L

        sigma = a
  let c :=
    IsCyclotomicExtension.Rat.galEquivZMod
      (p.1 ^ (n + 1)) L

      sigma
  have hc :=
    IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq

      (p.1 ^ (n + 1)) L sigma hzeta.pow_eq_one
  have hpowers :=
    hc.symm.trans haction
  rw [(hzeta.isOfFinOrder m.ne_zero).pow_inj_mod,
    ← hzeta.eq_orderOf,
    ← ZMod.natCast_eq_natCast_iff'] at hpowers
  change
      (c.val.val : ZMod (p.1 ^ (n + 1))) =
        (a.val.val : ZMod (p.1 ^ (n + 1))) at hpowers
  have hValues : c.val = a.val := by
    calc
      c.val = c.val.val :=
        (ZMod.natCast_zmod_val c.val).symm
      _ = a.val.val := hpowers
      _ = a.val := ZMod.natCast_zmod_val a.val
  apply Units.ext
  exact hValues

section

variable {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv K v) L)

/-- The chosen finite-place Artin map factors through any extension identified
with the chosen one. -/
theorem chosenFinitePlaceArtinMonoidHom_apply_factor_of_extension_eq
    (hw : chosenFinitePlaceExtension (L := L) v = w)
    (x : (v.adicCompletion K)ˣ) :
    chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x =
      finitePlaceLocalToGlobalMonoidHom
        (K := K) (L := L) v w
        (finitePlaceLocalArtinMonoidHom
          (K := K) (L := L) v w x) := by
  subst w
  exact
    congrArg
      (fun f : (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) => f x)
      (finitePlaceArtinMonoidHomOfExtension_factor
          v
        (chosenFinitePlaceExtension v))

private theorem finitePlaceLocalToGlobalMonoidHom_apply_pow_of_localized_action
    (sigma :
      let vK := HeightOneSpectrum.adicAbv K v
      let E := LocalizedCompletion vK w
      letI : Algebra vK.Completion E :=
        finitePlaceLocalArtinLocalizedAlgebra v w
      Gal(E / vK.Completion))
    (z : L)
    (zLocal :
      let vK := HeightOneSpectrum.adicAbv K v
      LocalizedCompletion vK w)
    (e : ℕ)
    (hLocalization :
      let vK := HeightOneSpectrum.adicAbv K v
      let E := LocalizedCompletion vK w
      letI : Algebra vK.Completion E :=
        finitePlaceLocalArtinLocalizedAlgebra v w
      let eLoc : L →+* E :=
        AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
      eLoc z = zLocal)
    (hlocal : sigma zLocal = zLocal ^ e) :
    finitePlaceLocalToGlobalMonoidHom
        (K := K) (L := L) v w sigma z = z ^ e := by
  let vK := HeightOneSpectrum.adicAbv K v
  let hvK := RayClass.adicAbv_isNontrivial v
  let E := LocalizedCompletion vK w
  let :=
    finitePlaceLocalArtinLocalizedAlgebra v w
  let eD :=
    decompositionGroupEquivAlgebraicLocalizationAut vK hvK w
  let eLoc :=
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  let delta := eD.symm sigma
  apply eLoc.injective
  calc
    eLoc (finitePlaceLocalToGlobalMonoidHom
          v w sigma z) =
        eD delta (eLoc z) :=
      (localizationRamificationGroups_decompositionGroupEquiv_toLocalization
        vK hvK w delta z).symm
    _ = sigma (eLoc z) :=
      congrArg (fun tau : Gal(E / vK.Completion) => tau (eLoc z))
        (eD.apply_symm_apply sigma)
    _ = sigma zLocal :=
      congrArg (fun y : E => sigma y) hLocalization
    _ = zLocal ^ e := hlocal
    _ = (eLoc z) ^ e :=
      congrArg (fun y : E => y ^ e) hLocalization.symm
    _ = eLoc (z ^ e) := (map_pow eLoc z e).symm

end

private theorem map_primitiveRoot_eq_pow_of_eq_pow
    {M : Type} [CommRing M] [IsDomain M]
    (f : M →* M) (zeta rho : M) (order exponent : ℕ)
    [NeZero order]
    (hzeta : IsPrimitiveRoot zeta order)
    (hrho : IsPrimitiveRoot rho order)
    (hf : f zeta = zeta ^ exponent) :
    f rho = rho ^ exponent := by
  obtain ⟨j, -, hj⟩ :=
    hzeta.eq_pow_of_pow_eq_one hrho.pow_eq_one
  calc
    f rho = f (zeta ^ j) := congrArg f hj.symm
    _ = (f zeta) ^ j := map_pow f zeta j
    _ = (zeta ^ exponent) ^ j := congrArg (fun z => z ^ j) hf
    _ = zeta ^ (exponent * j) := (pow_mul zeta exponent j).symm
    _ = zeta ^ (j * exponent) :=
      congrArg (fun e : ℕ => zeta ^ e) (Nat.mul_comm exponent j)
    _ = (zeta ^ j) ^ exponent := pow_mul zeta j exponent
    _ = rho ^ exponent := congrArg (fun z => z ^ exponent) hj

section

variable {K L K' L' : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    [hKLfinite : FiniteDimensional K L] [IsAbelianGalois K L] [Field K'] [ValuativeRel K']
    [TopologicalSpace K'] [IsNonarchimedeanLocalField K'] [Field L'] [Algebra K' L']
    [FiniteDimensional K' L'] [IsAbelianGalois K' L'] (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv K v) L)
    (eK : (HeightOneSpectrum.adicAbv K v).Completion ≃+* K')
    (eL : LocalizedCompletion (HeightOneSpectrum.adicAbv K v) w ≃+* L')
    (hcomm : ∀ y : (HeightOneSpectrum.adicAbv K v).Completion, eL (@algebraMap (HeightOneSpectrum.adicAbv K v).Completion (LocalizedCompletion (HeightOneSpectrum.adicAbv K v) w) _ _ (finitePlaceLocalArtinLocalizedAlgebra v w) y) = algebraMap K' L' (eK y))
    (hExt : SemilinearValuationCompatible (HeightOneSpectrum.adicAbv K v).Completion K' eK)
    (x : (v.adicCompletion K)ˣ)

include hcomm hExt in
private theorem finitePlaceLocalArtinMonoidHom_apply_semilinear
    (z : LocalizedCompletion (HeightOneSpectrum.adicAbv K v) w) :
    eL (finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w x z) =
      LocalClassFieldTheory.abelianLocalArtinMonoidHom K' L'
        (Units.map eK.toMonoidHom
          (finitePlaceLocalArtinInput v x)) (eL z) := by
  calc
    eL (finitePlaceLocalArtinMonoidHom
          v w x z) =
      eL ((@LocalClassFieldTheory.abelianLocalArtinMonoidHom
        (HeightOneSpectrum.adicAbv K v).Completion
        (LocalizedCompletion (HeightOneSpectrum.adicAbv K v) w)
        inferInstance
        inferInstance
        (finitePlaceLocalArtinLocalizedAlgebra v w)
        (finitePlaceLocalArtinCompletionValuativeRel v)
        inferInstance
        (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v)
        (finitePlaceLocalArtinFiniteDimensional v w)
        (finitePlaceLocalArtinIsAbelianGalois v w hKLfinite)
        (finitePlaceLocalArtinInput v x)) z) :=
      congrArg eL
        (finitePlaceLocalArtinMonoidHom_apply_normalized_at
            v w x z)
    _ = LocalClassFieldTheory.abelianLocalArtinMonoidHom K' L'
          (Units.map eK.toMonoidHom
            (finitePlaceLocalArtinInput v x)) (eL z) :=
      @abelianLocalArtinMonoidHom_semilinear_action
        (HeightOneSpectrum.adicAbv K v).Completion K'
        (LocalizedCompletion (HeightOneSpectrum.adicAbv K v) w) L'
        inferInstance
        (finitePlaceLocalArtinCompletionValuativeRel v)
        inferInstance
        (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v)
        inferInstance
        inferInstance
        inferInstance
        inferInstance
        inferInstance
        inferInstance
        (finitePlaceLocalArtinLocalizedAlgebra v w)
        inferInstance
        (finitePlaceLocalArtinFiniteDimensional v w)
        (finitePlaceLocalArtinIsAbelianGalois v w hKLfinite)
        inferInstance
        inferInstance
        eK eL hcomm hExt (finitePlaceLocalArtinInput v x) z

include hcomm hExt in
/-- If a semilinearly identified target local Artin value is trivial, then the
corresponding global finite-place Artin value is trivial.  This generic bridge
keeps concrete completion and localization instance towers out of downstream
proof terms. -/
theorem finitePlaceArtinMonoidHomOfExtension_eq_one_of_semilinear
    (htrivial :
      LocalClassFieldTheory.abelianLocalArtinMonoidHom K' L'
          (Units.map eK.toMonoidHom
            (finitePlaceLocalArtinInput v x)) = 1) :
    finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w x = 1 := by
  rw [finitePlaceArtinMonoidHomOfExtension_factor,
    MonoidHom.comp_apply]
  have hlocal :
      finitePlaceLocalArtinMonoidHom
            v w x = 1 := by
    rw [finitePlaceLocalArtinMonoidHom_apply_normalized]
    exact
      @abelianLocalArtinMonoidHom_eq_one_of_semilinear
        (HeightOneSpectrum.adicAbv K v).Completion K'
        (LocalizedCompletion (HeightOneSpectrum.adicAbv K v) w) L'
        inferInstance
        (finitePlaceLocalArtinCompletionValuativeRel v)
        inferInstance
        (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v)
        inferInstance
        inferInstance
        inferInstance
        inferInstance
        inferInstance
        inferInstance
        (finitePlaceLocalArtinLocalizedAlgebra v w)
        inferInstance
        (finitePlaceLocalArtinFiniteDimensional v w)
        (finitePlaceLocalArtinIsAbelianGalois v w hKLfinite)
        inferInstance
        inferInstance
        eK eL hcomm hExt (finitePlaceLocalArtinInput v x) htrivial
  rw [hlocal, map_one]

end

 section

variable (p : Nat.Primes) (n : ℕ)

noncomputable def rationalCyclotomicPrincipalPrimeLocalizedRoot :
    rationalCyclotomicArtinLocalizedField
      (rationalCyclotomicPrincipalPrimeModulus p n) p :=
  rationalCyclotomicLocalizedPrimitiveRoot
    (rationalCyclotomicPrincipalPrimeModulus p n)
    (RayClass.rationalPrime p)

 noncomputable def rationalCyclotomicPrincipalPrimeResidueUnit (x : ℚˣ) :
    (ZMod (p.1 ^ (n + 1)))ˣ :=
  Units.map
    (PadicInt.toZModPow (p := p.1) (n + 1)).toMonoidHom
    (padicIntUnitOfRat p
      (rationalPrimeUnit x p : ℚ)
      (rationalPrimeUnit x p).ne_zero
      (padicValRat_rationalPrimeUnit x p))

private theorem rationalCyclotomicPrincipalPrime_localizedBase_commutes
    (y : (rationalCyclotomicArtinBaseAbv p).Completion) :
    rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
        (algebraMap (rationalCyclotomicArtinBaseAbv p).Completion
          (rationalCyclotomicArtinLocalizedField
            (rationalCyclotomicPrincipalPrimeModulus p n) p) y) =
      algebraMap ℚ_[p.1]
        (RationalCyclotomicPrincipalPrimePadicLevel p n)
        (rationalFinitePlaceCompletionRingEquivPadic p y) := by
  let E := rationalCyclotomicArtinLocalizedField (rationalCyclotomicPrincipalPrimeModulus p n) p
  let eL := rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
  let algebraMap₀ := algebraMap (rationalCyclotomicArtinBaseAbv p).Completion E
  have hy :
      algebraMap₀ y =
        algebraMap ℚ_[p.1] E
          (rationalFinitePlaceCompletionRingEquivPadic p y) := by
    change
      algebraMap₀ y =
        algebraMap₀
          ((rationalFinitePlaceCompletionRingEquivPadic p).symm
            (rationalFinitePlaceCompletionRingEquivPadic p y))
    exact
      (congrArg
        (algebraMap₀)
        ((rationalFinitePlaceCompletionRingEquivPadic p).symm_apply_apply y)).symm
  calc
    _ =
        eL (algebraMap ℚ_[p.1] E
          (rationalFinitePlaceCompletionRingEquivPadic p y)) :=
      congrArg eL hy
    _ = algebraMap ℚ_[p.1]
        (RationalCyclotomicPrincipalPrimePadicLevel p n)
        (rationalFinitePlaceCompletionRingEquivPadic p y) :=
      eL.commutes (rationalFinitePlaceCompletionRingEquivPadic p y)

/-- Specialized ramified-prime bridge from the standard `p`-adic Artin value
to the canonical global finite-place Artin value.  The localized completion
and all of its dependent instances remain private to this provider. -/
theorem
    rationalCyclotomicPrincipalPrime_finitePlaceArtinOfExtension_eq_one_of_padic
    (x : ((RayClass.rationalPrime p).adicCompletion ℚ)ˣ)
    (htrivial :
      abelianLocalArtinMonoidHom ℚ_[p.1]
          (RationalCyclotomicPrincipalPrimePadicLevel p n)
          (Units.map
            (rationalFinitePlaceCompletionRingEquivPadic p).toMonoidHom
            (finitePlaceLocalArtinInput (RayClass.rationalPrime p) x)) = 1) :
    finitePlaceArtinMonoidHomOfExtension
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel
          (rationalCyclotomicPrincipalPrimeModulus p n))
        (RayClass.rationalPrime p)
        (rationalCyclotomicChosenFinitePlaceExtension
          (rationalCyclotomicPrincipalPrimeModulus p n)
          (RayClass.rationalPrime p)) x = 1 := finitePlaceArtinMonoidHomOfExtension_eq_one_of_semilinear

      (RayClass.rationalPrime p)
      (rationalCyclotomicChosenFinitePlaceExtension
        (rationalCyclotomicPrincipalPrimeModulus p n)
        (RayClass.rationalPrime p))
      (rationalFinitePlaceCompletionRingEquivPadic p)
      (rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n).toRingEquiv
      (rationalCyclotomicPrincipalPrime_localizedBase_commutes p n)
      (rationalFinitePlaceCompletionRingEquivPadic_semilinearValuationCompatible p)
      x htrivial

end

section

variable (p : Nat.Primes) (n : ℕ) (x : ℚˣ)

private theorem
    padicMultiplicativePrimitiveRoot_rationalPrimeUnitParameterGaloisAction :
    standardLubinTateUnitParameterEquivGal
        (padicLocalField p.1)
        (padicMultiplicativeLubinTateSeries_isUniformizer p.1) n
        (standardLubinTateUnitParameterClass
          (padicLocalField p.1) n
          (rationalPrimeUnitValuationSubringUnit x p))
        (padicMultiplicativePrimitiveRoot p.1 n) =
      padicMultiplicativePrimitiveRoot p.1 n ^
        (PadicInt.toZModPow (p := p.1) (n + 1)
          (padicIntUnitOfRat p
            (rationalPrimeUnit x p : ℚ)
            (rationalPrimeUnit x p).ne_zero
            (padicValRat_rationalPrimeUnit x p) : ℤ_[p.1])).val := by
  let uZ :=
    padicIntUnitOfRat p
      (rationalPrimeUnit x p : ℚ)
      (rationalPrimeUnit x p).ne_zero
      (padicValRat_rationalPrimeUnit x p)
  let u : (padicLocalField p.1).valuationSubringˣ :=
    Units.map (padicIntEquivValuationSubring p.1).toMonoidHom uZ
  have huRational :
      rationalPrimeUnitValuationSubringUnit x p = u := rfl
  have huPreimage :
      (padicIntEquivValuationSubring p.1).symm
          ((u : (padicLocalField p.1).valuationSubringˣ) :
            (padicLocalField p.1).valuationSubring) =
        (uZ : ℤ_[p.1]) := by
    change
      (padicIntEquivValuationSubring p.1).symm
          (padicIntEquivValuationSubring p.1 uZ) =
        uZ
    exact
      (padicIntEquivValuationSubring p.1).symm_apply_apply
        uZ
  have hAction :=
    padicMultiplicativePrimitiveRoot_unitParameterGaloisAction
      p.1 n u
  rw [huPreimage] at hAction
  rw [huRational]
  exact hAction

 noncomputable def rationalCyclotomicPrincipalPrimePadicTargetArtin :
    Gal(RationalCyclotomicPrincipalPrimePadicLevel p n / ℚ_[p.1]) :=
  @LocalClassFieldTheory.abelianLocalArtinMonoidHom
    ℚ_[p.1] (RationalCyclotomicPrincipalPrimePadicLevel p n)
    (inferInstance : Field ℚ_[p.1])
    (inferInstance : Field
      (RationalCyclotomicPrincipalPrimePadicLevel p n))
    (inferInstance : Algebra ℚ_[p.1]
      (RationalCyclotomicPrincipalPrimePadicLevel p n))
    (inferInstance : ValuativeRel ℚ_[p.1])
    (inferInstance : TopologicalSpace ℚ_[p.1])
    (inferInstance : IsNonarchimedeanLocalField ℚ_[p.1])
    (rationalCyclotomicPrincipalPrimePadicLevelFiniteDimensional p n)
    (standardLubinTateLevelField_isAbelianGalois
      (padicLocalField p.1)
      (padicMultiplicativeLubinTateSeries_isUniformizer p.1) n)
    (Units.map
      (rationalFinitePlaceCompletionRingEquivPadic p).toMonoidHom
      (rationalPrincipalFinitePlaceInput x p))

 noncomputable def
    rationalCyclotomicPrincipalPrimePadicUnitParameterArtin :
    Gal(RationalCyclotomicPrincipalPrimePadicLevel p n / ℚ_[p.1]) :=
  standardLubinTateUnitParameterEquivGal
    (padicLocalField p.1)
    (padicMultiplicativeLubinTateSeries_isUniformizer p.1) n
    (standardLubinTateUnitParameterClass
      (padicLocalField p.1) n
      (rationalPrimeUnitValuationSubringUnit x p))

private theorem
    rationalCyclotomicPrincipalPrime_padicTargetArtin_eq_unitParameter :
    rationalCyclotomicPrincipalPrimePadicTargetArtin p n x =
      rationalCyclotomicPrincipalPrimePadicUnitParameterArtin p n x := by
  let T := RationalCyclotomicPrincipalPrimePadicLevel p n
  let eK := rationalFinitePlaceCompletionRingEquivPadic p
  let :=
    rationalCyclotomicPrincipalPrimePadicLevelFiniteDimensional p n
  let hpi := padicMultiplicativeLubinTateSeries_isUniformizer p.1
  let :=
    standardLubinTateLevelField_isAbelianGalois
      (padicLocalField p.1) hpi n
  have hsource :
      Units.map eK.toMonoidHom (rationalPrincipalFinitePlaceInput x p) =
        Units.map (algebraMap ℚ ℚ_[p.1]).toMonoidHom x := by
    rw [rationalPrincipalFinitePlaceInput_eq_algebraMap]
    apply Units.ext
    exact rationalFinitePlaceCompletionRingEquivPadic_algebraMap p (x : ℚ)
  change
    LocalClassFieldTheory.abelianLocalArtinMonoidHom ℚ_[p.1] T
        (Units.map eK.toMonoidHom
          (rationalPrincipalFinitePlaceInput x p)) =
      standardLubinTateUnitParameterEquivGal
        (padicLocalField p.1) hpi n
        (standardLubinTateUnitParameterClass
          (padicLocalField p.1) n
          (rationalPrimeUnitValuationSubringUnit x p))
  rw [hsource]
  rw [
    padicMultiplicativeAbelianLocalArtin_eq_uniformizerUnitPart,
    rationalPadicFieldUnit_uniformizerUnitPart,
    padicMultiplicativeAbelianLocalArtin_eq_unitParameter]

private theorem
    rationalCyclotomicPrincipalPrime_padicArtin_action_eq_unitParameter :
    (@LocalClassFieldTheory.abelianLocalArtinMonoidHom
      ℚ_[p.1] (RationalCyclotomicPrincipalPrimePadicLevel p n)
      (inferInstance : Field ℚ_[p.1])
      (inferInstance : Field
        (RationalCyclotomicPrincipalPrimePadicLevel p n))
      (inferInstance : Algebra ℚ_[p.1]
        (RationalCyclotomicPrincipalPrimePadicLevel p n))
      (inferInstance : ValuativeRel ℚ_[p.1])
      (inferInstance : TopologicalSpace ℚ_[p.1])
      (inferInstance : IsNonarchimedeanLocalField ℚ_[p.1])
      (rationalCyclotomicPrincipalPrimePadicLevelFiniteDimensional p n)
      (standardLubinTateLevelField_isAbelianGalois
        (padicLocalField p.1)
        (padicMultiplicativeLubinTateSeries_isUniformizer p.1) n)
      (Units.map
        (rationalFinitePlaceCompletionRingEquivPadic p).toMonoidHom
        (finitePlaceLocalArtinInput
          (K := ℚ) (RayClass.rationalPrime p)
          (IdeleGroup.finiteComponent
            (RayClass.rationalPrime p)
            (IdeleGroup.principalIdele ℚ x)))))
        ((rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n).toRingEquiv
          (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)) =
      rationalCyclotomicPrincipalPrimePadicUnitParameterArtin p n x
        (rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
          (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)) := by
  let eK := rationalFinitePlaceCompletionRingEquivPadic p
  let rationalCyclotomicLocalizedCompletionPadicAlgEquiv₀ := rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)
  calc
    _ = rationalCyclotomicPrincipalPrimePadicTargetArtin p n x
          (rationalCyclotomicLocalizedCompletionPadicAlgEquiv₀) := congrArg
        (fun uQp =>
          (@LocalClassFieldTheory.abelianLocalArtinMonoidHom
            ℚ_[p.1] (RationalCyclotomicPrincipalPrimePadicLevel p n)
            inferInstance
            inferInstance
            inferInstance
            inferInstance
            inferInstance
            inferInstance
            (rationalCyclotomicPrincipalPrimePadicLevelFiniteDimensional p n)
            (standardLubinTateLevelField_isAbelianGalois
              (padicLocalField p.1)
              (padicMultiplicativeLubinTateSeries_isUniformizer p.1) n)
            uQp)
              (rationalCyclotomicLocalizedCompletionPadicAlgEquiv₀))
        (congrArg (Units.map eK.toMonoidHom) rfl)
    _ = rationalCyclotomicPrincipalPrimePadicUnitParameterArtin p n x
          (rationalCyclotomicLocalizedCompletionPadicAlgEquiv₀) :=
      congrArg
        (fun tau => tau
          (rationalCyclotomicLocalizedCompletionPadicAlgEquiv₀))
        (rationalCyclotomicPrincipalPrime_padicTargetArtin_eq_unitParameter
          p n x)

private theorem
    rationalCyclotomicPrincipalPrime_padicUnitParameterArtin_action :
    rationalCyclotomicPrincipalPrimePadicUnitParameterArtin p n x
        (rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
          (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)) =
      (rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
        (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)) ^
        (rationalCyclotomicPrincipalPrimeResidueUnit p n x).val.val := by
  let m := rationalCyclotomicPrincipalPrimeModulus p n
  let E := rationalCyclotomicArtinLocalizedField m p
  let T := RationalCyclotomicPrincipalPrimePadicLevel p n
  let eL :=
    rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
  let zetaE := rationalCyclotomicPrincipalPrimeLocalizedRoot p n
  let tau :=
    rationalCyclotomicPrincipalPrimePadicUnitParameterArtin p n x
  let a := rationalCyclotomicPrincipalPrimeResidueUnit p n x
  let zetaT := padicMultiplicativePrimitiveRoot p.1 n
  have hzetaE : IsPrimitiveRoot zetaE (p.1 ^ (n + 1)) := by
    change
      IsPrimitiveRoot
        (rationalCyclotomicLocalizedPrimitiveRoot m
          (RayClass.rationalPrime p)) (m : ℕ)
    exact
      rationalCyclotomicLocalizedPrimitiveRoot_isPrimitiveRoot
        m (RayClass.rationalPrime p)
  exact
    map_primitiveRoot_eq_pow_of_eq_pow
      tau.toMonoidHom zetaT (eL zetaE)
      (p.1 ^ (n + 1)) a.val.val (padicMultiplicativePrimitiveRoot_isPrimitiveRoot p.1 n) (hzetaE.map_of_injective eL.injective) (padicMultiplicativePrimitiveRoot_rationalPrimeUnitParameterGaloisAction
        p n x)

private theorem rationalCyclotomicPrincipalPrime_localArtin_action :
    finitePlaceLocalArtinMonoidHom
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel
          (rationalCyclotomicPrincipalPrimeModulus p n))
        (RayClass.rationalPrime p)
        (rationalCyclotomicChosenFinitePlaceExtension
          (rationalCyclotomicPrincipalPrimeModulus p n)
          (RayClass.rationalPrime p))
        (IdeleGroup.finiteComponent
          (RayClass.rationalPrime p)
          (IdeleGroup.principalIdele ℚ x))
        (rationalCyclotomicPrincipalPrimeLocalizedRoot p n) =
      (rationalCyclotomicPrincipalPrimeLocalizedRoot p n) ^
        (rationalCyclotomicPrincipalPrimeResidueUnit p n x).val.val := by
  let eL := rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
  apply eL.injective
  calc
    _ = _ :=
      finitePlaceLocalArtinMonoidHom_apply_semilinear

        (RayClass.rationalPrime p)
        (rationalCyclotomicChosenFinitePlaceExtension
          (rationalCyclotomicPrincipalPrimeModulus p n)
          (RayClass.rationalPrime p))
        (rationalFinitePlaceCompletionRingEquivPadic p)
        eL.toRingEquiv
        (rationalCyclotomicPrincipalPrime_localizedBase_commutes p n)
        (rationalFinitePlaceCompletionRingEquivPadic_semilinearValuationCompatible
          p)
        (IdeleGroup.finiteComponent
          (RayClass.rationalPrime p)
          (IdeleGroup.principalIdele ℚ x))
        (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)
    _ = rationalCyclotomicPrincipalPrimePadicUnitParameterArtin p n x
          (eL (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)) :=
      rationalCyclotomicPrincipalPrime_padicArtin_action_eq_unitParameter
        p n x
    _ = (eL (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)) ^
          (rationalCyclotomicPrincipalPrimeResidueUnit p n x).val.val :=
      rationalCyclotomicPrincipalPrime_padicUnitParameterArtin_action p n x
    _ = eL ((rationalCyclotomicPrincipalPrimeLocalizedRoot p n) ^
          (rationalCyclotomicPrincipalPrimeResidueUnit p n x).val.val) :=
      (map_pow eL (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)
        (rationalCyclotomicPrincipalPrimeResidueUnit p n x).val.val).symm

end

/-- The finite-place Artin symbol at the ramified prime, in its canonical
local-to-global factored form.  Keeping this specialization opaque prevents its
dependent local/global instance tower from being unfolded downstream. -/
noncomputable def rationalCyclotomicPrincipalPrimeChosenArtin
    (p : Nat.Primes) (n : ℕ) (x : ℚˣ) :
    KummerTheory.rationalCyclotomicLevel
        (rationalCyclotomicPrincipalPrimeModulus p n) ≃ₐ[ℚ]
      KummerTheory.rationalCyclotomicLevel
        (rationalCyclotomicPrincipalPrimeModulus p n) :=
  finitePlaceLocalToGlobalMonoidHom
    (K := ℚ)
    (L := KummerTheory.rationalCyclotomicLevel
      (rationalCyclotomicPrincipalPrimeModulus p n))
    (RayClass.rationalPrime p)
    (rationalCyclotomicChosenFinitePlaceExtension
      (rationalCyclotomicPrincipalPrimeModulus p n)
      (RayClass.rationalPrime p))
    (finitePlaceLocalArtinMonoidHom
      (K := ℚ)
      (L := KummerTheory.rationalCyclotomicLevel
        (rationalCyclotomicPrincipalPrimeModulus p n))
      (RayClass.rationalPrime p)
      (rationalCyclotomicChosenFinitePlaceExtension
        (rationalCyclotomicPrincipalPrimeModulus p n)
        (RayClass.rationalPrime p))
      (IdeleGroup.finiteComponent
        (RayClass.rationalPrime p)
        (IdeleGroup.principalIdele ℚ x)))

/-- At the ramified prime, the cyclotomic character of the chosen finite-place
Artin symbol is the direct reduction of the rational `p`-adic unit. -/
theorem galEquivZMod_chosenFinitePlaceArtinMonoidHom_principal_at_prime
    (p : Nat.Primes) (n : ℕ) (x : ℚˣ) :
    IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ (n + 1))
        (KummerTheory.rationalCyclotomicLevel
          (rationalCyclotomicPrincipalPrimeModulus p n))
        (hK :=
          KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
            (rationalCyclotomicPrincipalPrimeModulus p n))
        (rationalCyclotomicPrincipalPrimeChosenArtin p n x) =
      Units.map
        (PadicInt.toZModPow (p := p.1) (n + 1)).toMonoidHom
        (padicIntUnitOfRat p
          (rationalPrimeUnit x p : ℚ)
          (rationalPrimeUnit x p).ne_zero
          (padicValRat_rationalPrimeUnit x p)) := by
  apply rationalCyclotomicPrincipalPrime_galEquivZMod_eq_of_action p n
  simp only [rationalCyclotomicPrincipalPrimeChosenArtin]
  apply finitePlaceLocalToGlobalMonoidHom_apply_pow_of_localized_action

  · rfl
  · exact rationalCyclotomicPrincipalPrime_localArtin_action p n x

end RationalCyclotomicPrincipalPrime

 section

variable (m : ℕ+) (q : Nat.Primes)

theorem rationalCyclotomicArtinUnramified
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) := by
  simpa [ChosenFinitePlaceIsUnramified] using
    (rationalCyclotomicLevel_chosenFinitePlaceIsUnramified
      m q hq)

 noncomputable def rationalCyclotomicArtinLocalFrobeniusOf
    (hUnramified :
      IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
        (rationalCyclotomicArtinBaseAbv q).Completion
        (rationalCyclotomicArtinLocalizedField m q)) :
    rationalCyclotomicArtinLocalizedField m q ≃ₐ[
      (rationalCyclotomicArtinBaseAbv q).Completion]
      rationalCyclotomicArtinLocalizedField m q := by
  letI := hUnramified
  exact arithmeticFrobeniusOfUnramifiedValuation
    (rationalCyclotomicArtinBaseAbv q).Completion
    (rationalCyclotomicArtinLocalizedField m q)

 noncomputable def rationalCyclotomicArtinLocalFrobenius
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    rationalCyclotomicArtinLocalizedField m q ≃ₐ[
      (rationalCyclotomicArtinBaseAbv q).Completion]
      rationalCyclotomicArtinLocalizedField m q :=
  rationalCyclotomicArtinLocalFrobeniusOf m q
    (rationalCyclotomicArtinUnramified m q hq)

 noncomputable def rationalCyclotomicArtinDecompositionEquiv :
    absoluteValueDecompositionGroup ℚ
        (rationalCyclotomicArtinExtension m q).1 ≃*
      (rationalCyclotomicArtinLocalizedField m q ≃ₐ[
        (rationalCyclotomicArtinBaseAbv q).Completion]
        rationalCyclotomicArtinLocalizedField m q) :=
  decompositionGroupEquivAlgebraicLocalizationAut
    (rationalCyclotomicArtinBaseAbv q)
    (RayClass.adicAbv_isNontrivial
      (rationalCyclotomicArtinPlace q))
    (rationalCyclotomicArtinExtension m q)

 noncomputable def rationalCyclotomicArtinLocalToGlobalMonoidHom :
    (rationalCyclotomicArtinLocalizedField m q ≃ₐ[
      (rationalCyclotomicArtinBaseAbv q).Completion]
      rationalCyclotomicArtinLocalizedField m q) →*
        (rationalCyclotomicArtinLevel m ≃ₐ[ℚ]
          rationalCyclotomicArtinLevel m) :=
  finitePlaceLocalToGlobalMonoidHom
    (K := ℚ) (L := rationalCyclotomicArtinLevel m)
    (rationalCyclotomicArtinPlace q)
    (rationalCyclotomicArtinExtension m q)

 noncomputable abbrev rationalCyclotomicArtinLocalArtin
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    rationalCyclotomicArtinLocalizedField m q ≃ₐ[
      (rationalCyclotomicArtinBaseAbv q).Completion]
      rationalCyclotomicArtinLocalizedField m q :=
  finitePlaceLocalArtinMonoidHom
    (K := ℚ) (L := rationalCyclotomicArtinLevel m)
    (rationalCyclotomicArtinPlace q)
    (rationalCyclotomicArtinExtension m q) x

 noncomputable def rationalCyclotomicArtinGlobalFrobeniusOf
    (hUnramified :
      IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
        (rationalCyclotomicArtinBaseAbv q).Completion
        (rationalCyclotomicArtinLocalizedField m q)) :
    rationalCyclotomicArtinLevel m ≃ₐ[ℚ]
      rationalCyclotomicArtinLevel m :=
  rationalCyclotomicArtinLocalToGlobalMonoidHom m q
    (rationalCyclotomicArtinLocalFrobeniusOf
      m q hUnramified)

/-- The global decomposition-group lift of arithmetic Frobenius at the
chosen place above `q`.  Keeping the local construction opaque prevents its
many completion instances from leaking into later theorem statements. -/
 noncomputable def rationalCyclotomicChosenArithmeticFrobenius
    (hq : ¬ q.1 ∣ (m : ℕ)) :
      KummerTheory.rationalCyclotomicLevel m ≃ₐ[ℚ]
      KummerTheory.rationalCyclotomicLevel m := rationalCyclotomicArtinGlobalFrobeniusOf m q
      (rationalCyclotomicArtinUnramified m q hq)

end

 section

variable (q : Nat.Primes) (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ)

noncomputable abbrev rationalCyclotomicArtinLocalInput :
    (rationalCyclotomicArtinBaseAbv q).Completionˣ :=
  finitePlaceLocalArtinInput
    (K := ℚ) (rationalCyclotomicArtinPlace q) x

/-- The normalized valuation of the canonical completion input used by the
rational finite-place Artin map.  This named endpoint keeps the completion
instances out of downstream theorem statements. -/
noncomputable def rationalCyclotomicArtinLocalExponent : ℤ :=
  IsNonarchimedeanLocalField.valuationMap
    (rationalCyclotomicArtinBaseAbv q).Completion
    (Additive.ofMul (rationalCyclotomicArtinLocalInput q x))

end

/-- The chosen finite-place Artin value in a rational cyclotomic level, with
the completion and Galois instance arguments frozen at the provider boundary. -/
noncomputable def rationalCyclotomicChosenFinitePlaceArtinValue
    (m : ℕ+) (q : Nat.Primes)
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    Gal(KummerTheory.rationalCyclotomicLevel m / ℚ) :=
  chosenFinitePlaceArtinMonoidHom
    (K := ℚ)
    (L := KummerTheory.rationalCyclotomicLevel m)
    (RayClass.rationalPrime q) x

private theorem
    rationalCyclotomicFinitePlaceMappedLocalArtin_eq_frobenius_zpow_of
    (m : ℕ+) (q : Nat.Primes)
    (hAbelian :
      IsAbelianGalois
        (rationalCyclotomicArtinBaseAbv q).Completion
        (rationalCyclotomicArtinLocalizedField m q))
    (hUnramified :
      IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
        (rationalCyclotomicArtinBaseAbv q).Completion
        (rationalCyclotomicArtinLocalizedField m q))
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    rationalCyclotomicArtinLocalToGlobalMonoidHom m q
        (LocalClassFieldTheory.abelianLocalArtinMonoidHom
          (rationalCyclotomicArtinBaseAbv q).Completion
          (rationalCyclotomicArtinLocalizedField m q)
          (rationalCyclotomicArtinLocalInput q x)) =
      (rationalCyclotomicArtinGlobalFrobeniusOf
        m q hUnramified) ^
        rationalCyclotomicArtinLocalExponent q x := by
  let := hAbelian
  let := hUnramified
  change
    rationalCyclotomicArtinLocalToGlobalMonoidHom m q
        (LocalClassFieldTheory.abelianLocalArtinMonoidHom
          (rationalCyclotomicArtinBaseAbv q).Completion
          (rationalCyclotomicArtinLocalizedField m q)
          (rationalCyclotomicArtinLocalInput q x)) =
      (rationalCyclotomicArtinLocalToGlobalMonoidHom m q
        (arithmeticFrobeniusOfUnramifiedValuation
          (rationalCyclotomicArtinBaseAbv q).Completion
          (rationalCyclotomicArtinLocalizedField m q))) ^
        rationalCyclotomicArtinLocalExponent q x
  exact
    mappedAbelianLocalArtin_eq_frobenius_zpow

      (rationalCyclotomicArtinLocalToGlobalMonoidHom m q)
      (rationalCyclotomicArtinLocalInput q x)

section

variable (m : ℕ+) (q : Nat.Primes) (hq : ¬ q.1 ∣ (m : ℕ))
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ)

private theorem
    rationalCyclotomicFinitePlaceMappedLocalArtin_eq_frobenius_zpow :
    rationalCyclotomicArtinLocalToGlobalMonoidHom m q
        (rationalCyclotomicArtinLocalArtin m q x) =
      (rationalCyclotomicChosenArithmeticFrobenius m q hq) ^
        rationalCyclotomicArtinLocalExponent q x := by
  change
    rationalCyclotomicArtinLocalToGlobalMonoidHom m q
        (rationalCyclotomicArtinLocalArtin m q x) =
      (rationalCyclotomicArtinGlobalFrobeniusOf m q
        (rationalCyclotomicArtinUnramified m q hq)) ^
        rationalCyclotomicArtinLocalExponent q x
  calc
    _ =
        rationalCyclotomicArtinLocalToGlobalMonoidHom m q
          (LocalClassFieldTheory.abelianLocalArtinMonoidHom
            (rationalCyclotomicArtinBaseAbv q).Completion
            (rationalCyclotomicArtinLocalizedField m q)
            (rationalCyclotomicArtinLocalInput q x)) :=
      congrArg
        (fun σ =>
          rationalCyclotomicArtinLocalToGlobalMonoidHom m q σ)
        (by
          rfl)
    _ =
        (rationalCyclotomicArtinGlobalFrobeniusOf m q
          (rationalCyclotomicArtinUnramified m q hq)) ^
          rationalCyclotomicArtinLocalExponent q x :=
      rationalCyclotomicFinitePlaceMappedLocalArtin_eq_frobenius_zpow_of
        m q (rationalCyclotomicArtinLocalizedIsAbelianGalois m q)
        (rationalCyclotomicArtinUnramified m q hq) x

/-- The chosen local Artin symbol is the chosen global Frobenius lift raised
to the normalized local valuation. -/
private theorem
    chosenFinitePlaceArtin_eq_chosenArithmeticFrobenius_zpow :
    chosenFinitePlaceArtinMonoidHom
        (K := ℚ) (L := rationalCyclotomicArtinLevel m)
        (rationalCyclotomicArtinPlace q) x =
      (rationalCyclotomicChosenArithmeticFrobenius m q hq) ^
        rationalCyclotomicArtinLocalExponent q x := by
  let finitePlaceArtinMonoidHomOfExtension₀ := finitePlaceArtinMonoidHomOfExtension (rationalCyclotomicArtinPlace q) (rationalCyclotomicArtinExtension m q) x
  change
    finitePlaceArtinMonoidHomOfExtension₀ =
      (rationalCyclotomicChosenArithmeticFrobenius m q hq) ^
        rationalCyclotomicArtinLocalExponent q x
  have hFactor :
      finitePlaceArtinMonoidHomOfExtension₀ =
        rationalCyclotomicArtinLocalToGlobalMonoidHom m q
          (rationalCyclotomicArtinLocalArtin m q x) := by
    change
      finitePlaceArtinMonoidHomOfExtension₀ =
        finitePlaceLocalToGlobalMonoidHom

          (rationalCyclotomicArtinPlace q)
          (rationalCyclotomicArtinExtension m q)
          (finitePlaceLocalArtinMonoidHom

            (rationalCyclotomicArtinPlace q)
            (rationalCyclotomicArtinExtension m q) x)
    exact
      congrArg
        (fun φ :
          ((rationalCyclotomicArtinPlace q).adicCompletion ℚ)ˣ →*
            (rationalCyclotomicArtinLevel m ≃ₐ[ℚ]
              rationalCyclotomicArtinLevel m) => φ x)
        (finitePlaceArtinMonoidHomOfExtension_factor

          (rationalCyclotomicArtinPlace q)
          (rationalCyclotomicArtinExtension m q))
  exact
    hFactor.trans
      (rationalCyclotomicFinitePlaceMappedLocalArtin_eq_frobenius_zpow
        m q hq x)

end

private theorem rationalCyclotomicArtinResidueFieldCard
    (q : Nat.Primes) :
    Nat.card 𝓀[(rationalCyclotomicArtinBaseAbv q).Completion] = q.1 := by
  simpa [rationalCyclotomicArtinPlace,
    rationalCyclotomicArtinBaseAbv] using
    rationalFinitePlaceCompletion_residueField_card
      (rationalCyclotomicArtinPlace q)

section

variable (m : ℕ+) (q : Nat.Primes) (hq : ¬ q.1 ∣ (m : ℕ))

private theorem rationalCyclotomicArtinLocalFrobenius_apply_root :
    rationalCyclotomicArtinLocalFrobenius m q hq
        (rationalCyclotomicLocalizedPrimitiveRoot
          m (rationalCyclotomicArtinPlace q)) =
      (rationalCyclotomicLocalizedPrimitiveRoot
        m (rationalCyclotomicArtinPlace q)) ^ q.1 := by
  let := rationalCyclotomicArtinUnramified m q hq
  refine
    (arithmeticFrobeniusOfUnramifiedValuation_apply_primitiveRoot
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q)
      (rationalCyclotomicLocalizedPrimitiveRoot_isPrimitiveRoot
        m (rationalCyclotomicArtinPlace q)) ?_).trans
      (congrArg
        (fun n : ℕ => (rationalCyclotomicLocalizedPrimitiveRoot
          m (rationalCyclotomicArtinPlace q)) ^ n)
        (rationalCyclotomicArtinResidueFieldCard q))
  rw [rationalCyclotomicArtinResidueFieldCard q]
  exact q.2.coprime_iff_not_dvd.mpr hq

private theorem rationalCyclotomicArtinFrobeniusLift_localization :
    AbsoluteValue.toAlgebraicLocalization
        (rationalCyclotomicArtinBaseAbv q)
        (rationalCyclotomicArtinExtension m q).1
        (rationalCyclotomicArtinExtension m q).2
        (((absoluteValueDecompositionGroup ℚ
          (rationalCyclotomicArtinExtension m q).1).subtype
          ((rationalCyclotomicArtinDecompositionEquiv m q).symm
            (rationalCyclotomicArtinLocalFrobenius m q hq)))
          (rationalCyclotomicLevelPrimitiveRoot m)) =
      rationalCyclotomicArtinLocalFrobenius m q hq
        (AbsoluteValue.toAlgebraicLocalization
          (rationalCyclotomicArtinBaseAbv q)
          (rationalCyclotomicArtinExtension m q).1
          (rationalCyclotomicArtinExtension m q).2
          (rationalCyclotomicLevelPrimitiveRoot m)) := by
  let toAlgebraicLocalization₀ := AbsoluteValue.toAlgebraicLocalization (rationalCyclotomicArtinBaseAbv q) (rationalCyclotomicArtinExtension m q).1 (rationalCyclotomicArtinExtension m q).2 (rationalCyclotomicLevelPrimitiveRoot m)
  calc
    _ =
      rationalCyclotomicArtinDecompositionEquiv m q
          ((rationalCyclotomicArtinDecompositionEquiv m q).symm
            (rationalCyclotomicArtinLocalFrobenius m q hq))
        (toAlgebraicLocalization₀) :=
      (localizationRamificationGroups_decompositionGroupEquiv_toLocalization
        (rationalCyclotomicArtinBaseAbv q)
        (RayClass.adicAbv_isNontrivial
          (rationalCyclotomicArtinPlace q))
        (rationalCyclotomicArtinExtension m q)
        ((rationalCyclotomicArtinDecompositionEquiv m q).symm
          (rationalCyclotomicArtinLocalFrobenius m q hq))
        (rationalCyclotomicLevelPrimitiveRoot m)).symm
    _ = rationalCyclotomicArtinLocalFrobenius m q hq
        (toAlgebraicLocalization₀) :=
      congrArg
        (fun σ : rationalCyclotomicArtinLocalizedField m q ≃ₐ[
          (rationalCyclotomicArtinBaseAbv q).Completion]
          rationalCyclotomicArtinLocalizedField m q =>
            σ (toAlgebraicLocalization₀))
        ((rationalCyclotomicArtinDecompositionEquiv m q).apply_symm_apply
          (rationalCyclotomicArtinLocalFrobenius m q hq))

private theorem rationalCyclotomicChosenArithmeticFrobenius_localization :
    AbsoluteValue.toAlgebraicLocalization
        (rationalCyclotomicArtinBaseAbv q)
        (rationalCyclotomicArtinExtension m q).1
        (rationalCyclotomicArtinExtension m q).2
        (rationalCyclotomicChosenArithmeticFrobenius m q hq
          (rationalCyclotomicLevelPrimitiveRoot m)) =
      rationalCyclotomicArtinLocalFrobenius m q hq
        (AbsoluteValue.toAlgebraicLocalization
          (rationalCyclotomicArtinBaseAbv q)
          (rationalCyclotomicArtinExtension m q).1
          (rationalCyclotomicArtinExtension m q).2
          (rationalCyclotomicLevelPrimitiveRoot m)) := by
  let toAlgebraicLocalization₀ := AbsoluteValue.toAlgebraicLocalization (rationalCyclotomicArtinBaseAbv q) (rationalCyclotomicArtinExtension m q).1 (rationalCyclotomicArtinExtension m q).2
  calc
    _ =
      toAlgebraicLocalization₀
        (((absoluteValueDecompositionGroup ℚ
          (rationalCyclotomicArtinExtension m q).1).subtype
          ((rationalCyclotomicArtinDecompositionEquiv m q).symm
            (rationalCyclotomicArtinLocalFrobenius m q hq)))
          (rationalCyclotomicLevelPrimitiveRoot m)) :=
      congrArg
        (fun σ : rationalCyclotomicArtinLevel m ≃ₐ[ℚ]
          rationalCyclotomicArtinLevel m =>
            toAlgebraicLocalization₀
              (σ (rationalCyclotomicLevelPrimitiveRoot m)))
        (rfl)
    _ = rationalCyclotomicArtinLocalFrobenius m q hq
        (toAlgebraicLocalization₀
          (rationalCyclotomicLevelPrimitiveRoot m)) :=
      rationalCyclotomicArtinFrobeniusLift_localization m q hq

end

private theorem rationalCyclotomicArtinLocalizedRoot_pow
    (m : ℕ+) (q : Nat.Primes) :
    (rationalCyclotomicLocalizedPrimitiveRoot
        m (rationalCyclotomicArtinPlace q)) ^ q.1 =
      rationalCyclotomicGlobalToLocalizedAlgHom
        m (rationalCyclotomicArtinPlace q)
        (rationalCyclotomicLevelPrimitiveRoot m ^ q.1) := by
  calc
    _ =
      (rationalCyclotomicGlobalToLocalizedAlgHom
        m (rationalCyclotomicArtinPlace q)
        (rationalCyclotomicLevelPrimitiveRoot m)) ^ q.1 :=
      congrArg (fun z => z ^ q.1)
        (rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot m
          (rationalCyclotomicArtinPlace q)).symm
    _ = rationalCyclotomicGlobalToLocalizedAlgHom
        m (rationalCyclotomicArtinPlace q)
        (rationalCyclotomicLevelPrimitiveRoot m ^ q.1) :=
      (map_pow
        (rationalCyclotomicGlobalToLocalizedAlgHom
          m (rationalCyclotomicArtinPlace q))
        (rationalCyclotomicLevelPrimitiveRoot m) q.1).symm

variable (m : ℕ+) (q : Nat.Primes) (hq : ¬ q.1 ∣ (m : ℕ))

private theorem rationalCyclotomicChosenArithmeticFrobenius_apply_root :
    rationalCyclotomicChosenArithmeticFrobenius m q hq
        (rationalCyclotomicLevelPrimitiveRoot m) =
      rationalCyclotomicLevelPrimitiveRoot m ^ q.1 := by
  apply
    (AbsoluteValue.toAlgebraicLocalization
      (rationalCyclotomicArtinBaseAbv q)
      (rationalCyclotomicArtinExtension m q).1
      (rationalCyclotomicArtinExtension m q).2).injective
  exact
    Eq.trans (rationalCyclotomicChosenArithmeticFrobenius_localization m q hq)
      (Eq.trans (congrArg
        (rationalCyclotomicArtinLocalFrobenius m q hq)
        (rfl))
        (Eq.trans (rationalCyclotomicArtinLocalFrobenius_apply_root m q hq)
          (Eq.trans (rationalCyclotomicArtinLocalizedRoot_pow m q) (rationalCyclotomicGlobalToLocalizedAlgHom_apply
            m (rationalCyclotomicArtinPlace q)
            (rationalCyclotomicLevelPrimitiveRoot m ^ q.1)))))

/-- The cyclotomic character sends the chosen arithmetic Frobenius lift to
the residue prime. -/
private theorem galEquivZMod_chosenArithmeticFrobenius :
    IsCyclotomicExtension.Rat.galEquivZMod
        (m : ℕ) (KummerTheory.rationalCyclotomicLevel m)
        (rationalCyclotomicChosenArithmeticFrobenius m q hq) =
      ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq) := rationalCyclotomicLevel_galEquivZMod_eq_unitOfCoprime
      m q hq (rationalCyclotomicChosenArithmeticFrobenius m q hq)
      (rationalCyclotomicChosenArithmeticFrobenius_apply_root m q hq)

/-- At a rational prime not dividing the level, the cyclotomic character
of the chosen finite-place Artin symbol is the residue prime raised to the
normalized local valuation. -/
theorem galEquivZMod_chosenFinitePlaceArtinMonoidHom_of_not_dvd
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    let v : HeightOneSpectrum (𝓞 ℚ) :=
      RayClass.rationalPrime q
    let L := KummerTheory.rationalCyclotomicLevel m
    let vQ := HeightOneSpectrum.adicAbv ℚ v
    let localInput :=
      (finitePlaceCompletionUnitsContinuousMulEquiv v).symm x
    let localExponent :=
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap
        vQ.Completion (Additive.ofMul localInput)
    IsCyclotomicExtension.Rat.galEquivZMod
        (m : ℕ) L
        (chosenFinitePlaceArtinMonoidHom
          (K := ℚ)
          (L := L) v x) =
      (ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq)) ^ localExponent := by
  dsimp only
  rw [chosenFinitePlaceArtin_eq_chosenArithmeticFrobenius_zpow
      m q hq x, map_zpow,
    galEquivZMod_chosenArithmeticFrobenius m q hq]
  rfl

include hq in
/-- Away from the cyclotomic level, a finite-place input of normalized
valuation zero has trivial cyclotomic character. -/
theorem
    galEquivZMod_chosenFinitePlaceArtinMonoidHom_eq_one_of_not_dvd_of_localExponent_eq_zero
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ)
    (hzero : rationalCyclotomicArtinLocalExponent q x = 0) :
    IsCyclotomicExtension.Rat.galEquivZMod
        (m : ℕ) (KummerTheory.rationalCyclotomicLevel m)
        (chosenFinitePlaceArtinMonoidHom
          (K := ℚ)
          (L := KummerTheory.rationalCyclotomicLevel m)
          (RayClass.rationalPrime q) x) =
      1 := by
  rw [chosenFinitePlaceArtin_eq_chosenArithmeticFrobenius_zpow
      m q hq x,
    map_zpow, galEquivZMod_chosenArithmeticFrobenius m q hq,
    hzero, zpow_zero]

include hq in
/-- Away from the cyclotomic level, valuation zero makes the chosen
finite-place Artin symbol itself trivial.  Returning the Galois element,
rather than an equality between cyclotomic characters with frozen instance
arguments, lets downstream restriction arguments apply their own canonical
character without a dependent instance transport. -/
theorem
    chosenFinitePlaceArtinMonoidHom_eq_one_of_not_dvd_of_localExponent_eq_zero
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ)
    (hzero : rationalCyclotomicArtinLocalExponent q x = 0) :
    chosenFinitePlaceArtinMonoidHom
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel m)
        (RayClass.rationalPrime q) x =
      1 := by
  apply
    (IsCyclotomicExtension.Rat.galEquivZMod
      (m : ℕ) (KummerTheory.rationalCyclotomicLevel m)).injective
  simpa using
    galEquivZMod_chosenFinitePlaceArtinMonoidHom_eq_one_of_not_dvd_of_localExponent_eq_zero
      m q hq x hzero

/-- For a rational principal idele, the unramified finite-place
cyclotomic Artin symbol at `q` is `q` raised to the negative usual
`q`-adic exponent. -/
theorem
    galEquivZMod_chosenFinitePlaceArtinMonoidHom_principal_of_not_dvd (x : ℚˣ) :
    IsCyclotomicExtension.Rat.galEquivZMod
        (m : ℕ)
        (KummerTheory.rationalCyclotomicLevel m)
        (chosenFinitePlaceArtinMonoidHom
          (K := ℚ)
          (L := KummerTheory.rationalCyclotomicLevel m)
          (RayClass.rationalPrime q)
          (IdeleGroup.finiteComponent
            (RayClass.rationalPrime q)
            (IdeleGroup.principalIdele ℚ x))) =
      (ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq)) ^
          (-padicValRat q.1 (x : ℚ)) := by
  rw [
    galEquivZMod_chosenFinitePlaceArtinMonoidHom_of_not_dvd
      m q hq,
    rationalPrincipalFiniteComponent_valuationMap]

end Reciprocity
end GlobalClassFieldTheory

end
