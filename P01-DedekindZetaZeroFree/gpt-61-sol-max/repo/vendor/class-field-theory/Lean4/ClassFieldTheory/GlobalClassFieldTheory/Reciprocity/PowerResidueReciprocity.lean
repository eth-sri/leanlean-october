module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.FinitePlaceCharacterComparison
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteIdeleArtin
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.HilbertProductFormula
public import ClassFieldTheory.AlgebraicNumberTheory.PowerResidueSymbols.Ideal
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.FinitePlaces
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
public import ClassFieldTheory.AlgebraicNumberTheory.QuadraticReciprocity
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Rational
public import ClassFieldTheory.LocalClassFieldTheory.Kummer.PowerResidueTameFormula
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
public import ValuedFieldTheory.Valuation.Completion.ExtensionInvariants
public import ClassFieldTheory.KummerTheory.Concrete.SimpleExtensionLocalBehavior
public import ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.FiniteRadicalSupport
public import ClassFieldTheory.LocalClassFieldTheory.Finite.CyclotomicNorm.PrincipalUnits

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


















set_option autoImplicit false

/-!
# Bad-place support and correction for power-residue reciprocity

For two global units `a` and `b`, the local Kummer factor can be nontrivial
only where `a`, `b`, or the exponent fails to be a valuation-ring unit.  This
file records that concrete finite set, proves triviality outside it from the
unramified simple-Kummer criterion and the local norm kernel, and constructs
the exponent-place and infinite-place correction in the common field-valued
group of roots of unity.
-/

open scoped BigOperators Classical NumberField NumberTheorySymbols ValuativeRel WithZero
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open KummerTheory
open AlgebraicNumberTheory.PowerResidueSymbols
open LocalClassFieldTheory.Kummer
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K : Type) [Field K] [NumberField K]

/-- Equality for the valuation used to define a valuative relation transports
to equality in the relation's canonical value group. -/
private theorem canonicalValuation_eq_of_valuation_eq
    {R Γ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation R Γ) (x y : R) (hxy : v x = v y) :
    letI : ValuativeRel R := ValuativeRel.ofValuation v
    ValuativeRel.valuation R x = ValuativeRel.valuation R y := by
  let : ValuativeRel R := ValuativeRel.ofValuation v
  change
    ValuativeRel.ValueGroupWithZero.mk x 1 =
      ValuativeRel.ValueGroupWithZero.mk y 1
  rw [ValuativeRel.ValueGroupWithZero.mk_eq_mk]
  constructor
  · change v (x * (1 : R)) ≤ v (y * (1 : R))
    simpa only [mul_one] using hxy.le
  · change v (y * (1 : R)) ≤ v (x * (1 : R))
    simpa only [mul_one] using hxy.ge

/-- The bounded-natural-number form of nonarchimedeanness for a finite-place
absolute value.  Naming this bridge keeps all completion residue constructions
on one proof-irrelevant provider. -/
 theorem finitePlaceAdicAbv_nonarchimedeanAbsoluteValue
    (v : HeightOneSpectrum (𝓞 K)) :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue
      (HeightOneSpectrum.adicAbv K v) :=
  (AbsoluteValue.isNonarchimedean_iff_bounded_nat
    (HeightOneSpectrum.adicAbv K v)).1
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v)

/-- Finite-field power-residue symbols commute with a field equivalence.
The statement is made on underlying units so it can be reused with every
roots-of-unity transport occurring below. -/
theorem finiteFieldPowerResidueSymbol_unitsMap_ringEquiv
    {k l : Type*} [Field k] [Field l] [Fintype k] [Fintype l]
    (e : k ≃+* l) (n : ℕ+)
    (hnk : (n : ℕ) ∣ Fintype.card k - 1)
    (hnl : (n : ℕ) ∣ Fintype.card l - 1)
    (u : kˣ) :
    Units.map e.toMonoidHom
        ((AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol
            k n hnk u :
            rootsOfUnity (n : ℕ) k) : kˣ) =
      ((AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol
          l n hnl
          (Units.map e.toMonoidHom u) :
            rootsOfUnity (n : ℕ) l) : lˣ) := by
  rw [
    AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol_apply,
    AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol_apply,
    map_pow]
  rw [Fintype.card_congr e.toEquiv]

/-- The residue field of a finite-place completion is canonically the
prime-ideal residue field.  The construction passes through the localization
at the prime and then through the residue equivalence induced by completion. -/
noncomputable def finitePlacePrimeResidueEquivLocalResidue
    (v : HeightOneSpectrum (𝓞 K)) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    (𝓞 K ⧸ v.asIdeal) ≃+* 𝓀[C] := by
  let a := HeightOneSpectrum.adicAbv K v
  let ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a :=
    finitePlaceAdicAbv_nonarchimedeanAbsoluteValue K v
  let C := a.Completion
  letI : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let V := LubinTate.Valuations.exponentialValuationSubring
    (AlgebraicNumberTheory.Valuations.absoluteValueExponentialValuation a ha)
  let aC := AbsoluteValue.completionAbsoluteValue a
  let haC : LubinTate.Valuations.NonarchimedeanAbsoluteValue aC :=
    (AbsoluteValue.isNonarchimedean_iff_bounded_nat aC).1
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean a
        ((AbsoluteValue.isNonarchimedean_iff_bounded_nat a).2 ha))
  let VC := LubinTate.Valuations.exponentialValuationSubring
    (AlgebraicNumberTheory.Valuations.absoluteValueExponentialValuation aC haC)
  let Rv := v.valuationSubringAtPrime K
  letI : IsLocalRing Rv :=
    IsLocalization.AtPrime.isLocalRing Rv v.asIdeal
  have hBase : Rv.toSubring = V := by
    ext x
    rw [AlgebraicNumberTheory.Valuations.mem_absoluteValueExponentialSubring_iff]
    change x ∈ v.valuationSubringAtPrime K ↔ _
    rw [v.valuationSubringAtPrime_eq_valuationSubring]
    change v.valuation K x ≤ 1 ↔ a x ≤ 1
    rw [HeightOneSpectrum.adicAbv_def]
    exact_mod_cast
      (WithZeroMulInt.toNNReal_le_one_iff
        (HeightOneSpectrum.one_lt_absNorm_nnreal v)).symm
  let eBase : Rv ≃+* V := RingEquiv.subringCongr hBase
  have hCompletion : VC = 𝒪[C] := by
    ext x
    rw [AlgebraicNumberTheory.Valuations.mem_absoluteValueExponentialSubring_iff]
    change ‖x‖ ≤ 1 ↔ x ∈ 𝒪[C]
    exact
      (finitePlaceCompletion_mem_integers_iff_norm_le_one
        a (HeightOneSpectrum.isNonarchimedean_adicAbv K v) x).symm
  let eCompletionRing : VC ≃+* 𝒪[C] :=
    RingEquiv.subringCongr hCompletion
  let eIdeal : (𝓞 K ⧸ v.asIdeal) ≃+* v.asIdeal.ResidueField :=
    RingEquiv.ofBijective
      (algebraMap (𝓞 K ⧸ v.asIdeal) v.asIdeal.ResidueField)
      v.asIdeal.bijective_algebraMap_quotient_residueField
  let eLocalization : Localization.AtPrime v.asIdeal ≃ₐ[𝓞 K] Rv :=
    IsLocalization.algEquiv v.asIdeal.primeCompl _ _
  exact
    eIdeal |>.trans
      (IsLocalRing.ResidueField.mapEquiv eLocalization.toRingEquiv) |>.trans
      (IsLocalRing.ResidueField.mapEquiv eBase) |>.trans
      (AlgebraicNumberTheory.Valuations.completionResidueEquiv a ha) |>.trans
      (IsLocalRing.ResidueField.mapEquiv eCompletionRing)

/-- The image of an algebraic integer in the valuation ring of a finite-place
completion. -/
noncomputable def finitePlaceIntegralCompletionElement
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    𝒪[C] := by
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  letI : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  exact ⟨algebraMap K C (x : K), by
    rw [finitePlaceCompletion_mem_integers_iff_norm_le_one
      (HeightOneSpectrum.adicAbv K v)
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v)]
    calc
      ‖algebraMap K C (x : K)‖ =
          HeightOneSpectrum.adicAbv K v (x : K) :=
        AbsoluteValue.completionAbsoluteValue_coe
          (HeightOneSpectrum.adicAbv K v) (x : K)
      _ ≤ 1 :=
        v.adicAbv_coe_le_one
          (HeightOneSpectrum.one_lt_absNorm_nnreal v) x⟩

/-- The finite-place integral element has the expected underlying completion
value. -/
@[simp]
theorem finitePlaceIntegralCompletionElement_coe
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    (finitePlaceIntegralCompletionElement K v x : C) =
      algebraMap K C (x : K) :=
  rfl

/-- The finite-place residue equivalence sends the class of an algebraic
integer to the residue of its canonical image in the completion. -/
@[simp]
theorem finitePlacePrimeResidueEquivLocalResidue_mk
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    finitePlacePrimeResidueEquivLocalResidue K v
        (Ideal.Quotient.mk v.asIdeal x) =
      IsLocalRing.residue 𝒪[C]
        (finitePlaceIntegralCompletionElement K v x) := by
  simp only [finitePlacePrimeResidueEquivLocalResidue,
    finitePlaceIntegralCompletionElement, RingEquiv.trans_apply]
  rw [RingEquiv.ofBijective_apply,
    Ideal.algebraMap_quotient_residueField_mk]
  rw [IsScalarTower.algebraMap_apply
    (NumberField.RingOfIntegers K) (Localization.AtPrime v.asIdeal)]
  rw [IsLocalRing.ResidueField.algebraMap_eq]
  simp only [IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue]
  rw [AlgebraicNumberTheory.Valuations.completionResidueEquiv_residue]
  simp only [IsLocalRing.ResidueField.map_residue]
  congr 1
  apply Subtype.ext
  change
    algebraMap K (HeightOneSpectrum.adicAbv K v).Completion
        (((IsLocalization.algEquiv v.asIdeal.primeCompl
            (Localization.AtPrime v.asIdeal)
            (v.valuationSubringAtPrime K))
          (algebraMap (𝓞 K) (Localization.AtPrime v.asIdeal) x) :
        v.valuationSubringAtPrime K) : K) =
      algebraMap K (HeightOneSpectrum.adicAbv K v).Completion (x : K)
  rw [AlgEquiv.commutes]
  rw [IsScalarTower.algebraMap_apply
    (NumberField.RingOfIntegers K) (v.valuationSubringAtPrime K)]
  rfl

/-- A nonzero algebraic integer, regarded as a global field unit. -/
def nonzeroIntegralFieldUnit (x : 𝓞 K) (hx : x ≠ 0) : Kˣ :=
  Units.mk0 (x : K) (by
    intro hxK
    apply hx
    apply Subtype.ext
    exact hxK)

omit [NumberField K] in
@[simp]
theorem nonzeroIntegralFieldUnit_coe (x : 𝓞 K) (hx : x ≠ 0) :
    ((nonzeroIntegralFieldUnit K x hx : Kˣ) : K) = (x : K) :=
  rfl

/-- An algebraic integer avoiding a prime ideal, regarded as a nonzero
element of the global field. -/
noncomputable def primeAvoidingIntegralFieldUnit
    (v : HeightOneSpectrum (𝓞 K))
    (x : 𝓞 K) (hx : x ∉ v.asIdeal) : Kˣ :=
  nonzeroIntegralFieldUnit K x (by
    intro hx0
    apply hx
    rw [hx0]
    exact Ideal.zero_mem _)

omit [NumberField K] in
@[simp]
theorem primeAvoidingIntegralFieldUnit_coe
    (v : HeightOneSpectrum (𝓞 K))
    (x : 𝓞 K) (hx : x ∉ v.asIdeal) :
    ((primeAvoidingIntegralFieldUnit K v x hx : Kˣ) : K) = (x : K) :=
  rfl

/-- An algebraic integer nonzero modulo `v`, regarded as a unit of the
valuation ring of the finite-place completion. -/
noncomputable def finitePlaceIntegralCompletionUnit
    (v : HeightOneSpectrum (𝓞 K))
    (x : 𝓞 K) (hx : x ∉ v.asIdeal) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    𝒪[C]ˣ := by
  let a := HeightOneSpectrum.adicAbv K v
  let C := a.Completion
  letI : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let y : C := algebraMap K C (x : K)
  have hyNorm : ‖y‖ = 1 := by
    calc
      ‖y‖ = a (x : K) :=
        AbsoluteValue.completionAbsoluteValue_coe a (x : K)
      _ = ‖NumberField.FinitePlace.embedding v (x : K)‖ :=
        (NumberField.FinitePlace.norm_embedding v (x : K)).symm
      _ = 1 :=
        (NumberField.FinitePlace.norm_eq_one_iff_notMem K v x).2 hx
  have hyNe : y ≠ 0 := by
    intro hy
    rw [hy, norm_zero] at hyNorm
    exact zero_ne_one hyNorm
  let yIntegral : 𝒪[C] := ⟨y, by
    rw [finitePlaceCompletion_mem_integers_iff_norm_le_one
      a (HeightOneSpectrum.isNonarchimedean_adicAbv K v)]
    exact hyNorm.le⟩
  let yInvIntegral : 𝒪[C] := ⟨y⁻¹, by
    rw [finitePlaceCompletion_mem_integers_iff_norm_le_one
      a (HeightOneSpectrum.isNonarchimedean_adicAbv K v),
      norm_inv, hyNorm, inv_one]⟩
  exact {
    val := yIntegral
    inv := yInvIntegral
    val_inv := by
      apply Subtype.ext
      exact mul_inv_cancel₀ hyNe
    inv_val := by
      apply Subtype.ext
      exact inv_mul_cancel₀ hyNe }

/-- Forgetting the integral-unit structure recovers the ordinary image of
the algebraic integer in the finite-place completion. -/
@[simp]
theorem finitePlaceIntegralCompletionUnit_coe
    (v : HeightOneSpectrum (𝓞 K))
    (x : 𝓞 K) (hx : x ∉ v.asIdeal) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    (((finitePlaceIntegralCompletionUnit K v x hx : 𝒪[C]ˣ) : 𝒪[C]) : C) =
      algebraMap K C (x : K) := by
  rfl

/-- The completion image of a prime-avoiding algebraic integer is the field
unit underlying its canonical valuation-ring unit. -/
theorem finitePlaceHilbert_completionUnit_primeAvoidingIntegralFieldUnit
    (v : HeightOneSpectrum (𝓞 K))
    (x : 𝓞 K) (hx : x ∉ v.asIdeal) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    finitePlaceHilbert_completionUnit K v
        (primeAvoidingIntegralFieldUnit K v x hx) =
      integerUnitsToFieldUnits C
        (finitePlaceIntegralCompletionUnit K v x hx) := by
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  let : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  dsimp only
  apply Units.ext
  change
    algebraMap K C (x : K) =
      (((finitePlaceIntegralCompletionUnit K v x hx : 𝒪[C]ˣ) :
        𝒪[C]) : C)
  exact (finitePlaceIntegralCompletionUnit_coe K v x hx).symm

/-- As an element of the completion valuation ring, the lifted unit is the
canonical lifted algebraic integer. -/
@[simp]
theorem finitePlaceIntegralCompletionUnit_val
    (v : HeightOneSpectrum (𝓞 K))
    (x : 𝓞 K) (hx : x ∉ v.asIdeal) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    (finitePlaceIntegralCompletionUnit K v x hx : 𝒪[C]) =
      finitePlaceIntegralCompletionElement K v x := by
  dsimp only
  apply Subtype.ext
  exact finitePlaceIntegralCompletionUnit_coe K v x hx

/-- Reduction of the canonical completion unit agrees with reduction modulo
the corresponding global prime ideal. -/
theorem finitePlace_integerUnitsToResidueUnits_integralUnit
    (v : HeightOneSpectrum (𝓞 K))
    (x : 𝓞 K) (hx : x ∉ v.asIdeal) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    integerUnitsToResidueUnits C
        (finitePlaceIntegralCompletionUnit K v x hx) =
      Units.map
        (finitePlacePrimeResidueEquivLocalResidue K v).toMonoidHom
        (AlgebraicNumberTheory.PowerResidueSymbols.primeIdealResidueUnit
          K v x hx) := by
  dsimp only
  apply Units.ext
  change
    IsLocalRing.residue 𝒪[(HeightOneSpectrum.adicAbv K v).Completion]
        (finitePlaceIntegralCompletionUnit K v x hx :
          𝒪[(HeightOneSpectrum.adicAbv K v).Completion]) =
      finitePlacePrimeResidueEquivLocalResidue K v
        (Ideal.Quotient.mk v.asIdeal x)
  simpa only [finitePlaceIntegralCompletionUnit_val] using
    (finitePlacePrimeResidueEquivLocalResidue_mk K v x).symm

/-- The canonical inclusion from integral roots of unity into the common
field-valued group used by the global Hilbert symbols. -/
def integralRootsOfUnityToNthRoots
    (n : ℕ) :
    rootsOfUnity n (𝓞 K) →* nthRootsSubgroup K n where
  toFun z :=
    ⟨Units.map (algebraMap (𝓞 K) K).toMonoidHom z.1, by
      calc
        Units.map (algebraMap (𝓞 K) K).toMonoidHom z.1 ^ n =
            Units.map (algebraMap (𝓞 K) K).toMonoidHom (z.1 ^ n) :=
          (map_pow
            (Units.map (algebraMap (𝓞 K) K).toMonoidHom) z.1 n).symm
        _ = 1 := by rw [z.2, map_one]⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (Units.map (algebraMap (𝓞 K) K).toMonoidHom)
  map_mul' := by
    intro z w
    apply Subtype.ext
    exact map_mul
      (Units.map (algebraMap (𝓞 K) K).toMonoidHom) z.1 w.1

omit [NumberField K] in
/-- The integral-root inclusion is the underlying unit map. -/
@[simp]
theorem integralRootsOfUnityToNthRoots_apply
    (n : ℕ) (z : rootsOfUnity n (𝓞 K)) :
    (integralRootsOfUnityToNthRoots K n z).1 =
      Units.map (algebraMap (𝓞 K) K).toMonoidHom z.1 :=
  rfl














/-- Reduction after embedding an integral global root of unity into a
finite-place completion is the transport of reduction modulo the
corresponding prime ideal. -/
theorem finitePlace_localNthRootsReduction_integralRoots
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (z : rootsOfUnity (n : ℕ) (𝓞 K)) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    (localNthRootsReduction C n
        (nthRootsSubgroupMap K C (n : ℕ)
          (integralRootsOfUnityToNthRoots K (n : ℕ) z))).1 =
      Units.map
        (finitePlacePrimeResidueEquivLocalResidue K v).toMonoidHom
        (AlgebraicNumberTheory.PowerResidueSymbols.rootsOfUnityReduction
          K v (n : ℕ) z).1 := by
  dsimp only
  apply Units.ext
  change
    IsLocalRing.residue 𝒪[(HeightOneSpectrum.adicAbv K v).Completion]
        (nthRootIntegerUnit
          (HeightOneSpectrum.adicAbv K v).Completion n
          (nthRootsSubgroupMap K
            (HeightOneSpectrum.adicAbv K v).Completion (n : ℕ)
            (integralRootsOfUnityToNthRoots K (n : ℕ) z)) :
          𝒪[(HeightOneSpectrum.adicAbv K v).Completion]) =
      finitePlacePrimeResidueEquivLocalResidue K v
        (Ideal.Quotient.mk v.asIdeal (z.1 : 𝓞 K))
  rw [finitePlacePrimeResidueEquivLocalResidue_mk]
  congr 1

/-- The integral principal ideal generated by the exponent. -/
def powerResidueExponentIdeal (n : ℕ+) : Ideal (𝓞 K) :=
  Ideal.span {((n : ℕ) : 𝓞 K)}

/-- The exponent ideal is nonzero in a number field. -/
theorem powerResidueExponentIdeal_ne_zero (n : ℕ+) :
    powerResidueExponentIdeal K n ≠ 0 := by
  change Ideal.span {((n : ℕ) : 𝓞 K)} ≠ ⊥
  exact Ideal.span_singleton_eq_bot.not.mpr
    (Nat.cast_ne_zero.mpr n.ne_zero)






/-- The finite places dividing the exponent.  These, together with all
infinite places, are precisely the correction places in the reciprocity
formula once the two principal denominator supports are removed. -/
noncomputable def powerResidueExponentFinitePlaces
    (n : ℕ+) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (Ideal.finite_factors
    (powerResidueExponentIdeal_ne_zero K n)).toFinset

/-- Membership in the exponent-place support is divisibility by the exponent
ideal. -/
@[simp]
theorem mem_powerResidueExponentFinitePlaces_iff
    (n : ℕ+) (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ powerResidueExponentFinitePlaces K n ↔
      v.asIdeal ∣ powerResidueExponentIdeal K n :=
  Set.Finite.mem_toFinset
    (Ideal.finite_factors
      (powerResidueExponentIdeal_ne_zero K n))

/-- At a finite place not dividing the exponent, the exponent is a unit in
the canonical completion. -/
theorem finitePlace_natCast_valuation_eq_one_of_not_mem_exponent
    (n : ℕ+) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ powerResidueExponentFinitePlaces K n) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    ValuativeRel.valuation C ((n : ℕ) : C) = 1 := by
  dsimp only
  let : IsUltrametricDist
      (HeightOneSpectrum.adicAbv K v).Completion :=
    finitePlaceArtinCompletionIsUltrametricDist
      (HeightOneSpectrum.adicAbv K v)
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v)
  have hvNotDvd :
      ¬ v.asIdeal ∣ powerResidueExponentIdeal K n := by
    simpa only [mem_powerResidueExponentFinitePlaces_iff] using hv
  have hvNotMem : ((n : ℕ) : 𝓞 K) ∉ v.asIdeal := by
    intro hvMem
    apply hvNotDvd
    rw [powerResidueExponentIdeal, Ideal.dvd_span_singleton]
    exact hvMem
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  have hNorm : ‖((n : ℕ) : C)‖ = 1 := by
    calc
      ‖((n : ℕ) : C)‖ =
          ‖algebraMap K C (((n : ℕ) : K))‖ := by rw [map_natCast]
      _ = HeightOneSpectrum.adicAbv K v (((n : ℕ) : K)) :=
        AbsoluteValue.completionAbsoluteValue_coe
          (HeightOneSpectrum.adicAbv K v) (((n : ℕ) : K))
      _ = ‖NumberField.FinitePlace.embedding v (((n : ℕ) : K))‖ :=
        (NumberField.FinitePlace.norm_embedding v (((n : ℕ) : K))).symm
      _ = 1 :=
        (NumberField.FinitePlace.norm_eq_one_iff_notMem K v
          (((n : ℕ) : 𝓞 K))).2 hvNotMem
  let vCNorm := NormedField.valuation (K := C)
  let : vCNorm.Compatible := Valuation.Compatible.ofValuation vCNorm
  have hnCNorm : vCNorm ((n : ℕ) : C) = 1 := by
    change ‖((n : ℕ) : C)‖₊ = 1
    exact NNReal.eq (by simpa using hNorm)
  exact
    (ValuativeRel.isEquiv vCNorm (ValuativeRel.valuation C))
      |>.eq_one_iff_eq_one.mp hnCNorm

 noncomputable def finitePlaceLocalTamePowerResidueSymbolValue
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hv : v ∉ powerResidueExponentFinitePlaces K n)
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) :
    nthRootsSubgroup (HeightOneSpectrum.adicAbv K v).Completion (n : ℕ) := by
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  letI : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  exact localTamePowerResidueSymbol C n
    (finitePlace_natCast_valuation_eq_one_of_not_mem_exponent K n v hv)
    (finitePlaceHilbert_primitiveRoots_nonempty K n hmu v)
    (finitePlaceIntegralCompletionUnit K v a ha)

 noncomputable def finitePlaceLocalTamePowerResidueSymbolFieldValue
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hv : v ∉ powerResidueExponentFinitePlaces K n)
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) :
    (HeightOneSpectrum.adicAbv K v).Completion :=
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  letI : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  ((localTamePowerResidueSymbol C n
      (finitePlace_natCast_valuation_eq_one_of_not_mem_exponent K n v hv)
      (finitePlaceHilbert_primitiveRoots_nonempty K n hmu v)
      (finitePlaceIntegralCompletionUnit K v a ha)).1 : C)

 noncomputable def finitePlacePrimeIdealPowerResidueIntegralRoot
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm v.asIdeal).Coprime (n : ℕ))
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) :
    rootsOfUnity (n : ℕ) (𝓞 K) :=
  AlgebraicNumberTheory.PowerResidueSymbols.primeIdealPowerResidueSymbol
    K v n hmu hcoprime a ha

 noncomputable def finitePlacePrimeIdealPowerResidueGlobalRoot
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm v.asIdeal).Coprime (n : ℕ))
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) : nthRootsSubgroup K (n : ℕ) :=
  integralRootsOfUnityToNthRoots K (n : ℕ)
    (finitePlacePrimeIdealPowerResidueIntegralRoot K v n hmu hcoprime a ha)

 noncomputable def finitePlacePrimeIdealPowerResidueFactorValue
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm v.asIdeal).Coprime (n : ℕ))
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) :
    nthRootsSubgroup (HeightOneSpectrum.adicAbv K v).Completion (n : ℕ) :=
  nthRootsSubgroupMap K (HeightOneSpectrum.adicAbv K v).Completion (n : ℕ)
    (finitePlacePrimeIdealPowerResidueGlobalRoot K v n hmu hcoprime a ha)

 noncomputable def finitePlacePrimeIdealPowerResidueFactorFieldValue
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm v.asIdeal).Coprime (n : ℕ))
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) :
    (HeightOneSpectrum.adicAbv K v).Completion :=
  (((nthRootsSubgroupMap K
      (HeightOneSpectrum.adicAbv K v).Completion (n : ℕ))
    (finitePlacePrimeIdealPowerResidueGlobalRoot K v n hmu hcoprime a ha)).1 :
      (HeightOneSpectrum.adicAbv K v).Completion)

 noncomputable def finitePlaceLocalTamePowerResidueSymbolResidueValue
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hv : v ∉ powerResidueExponentFinitePlaces K n)
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    𝓀[C] := by
  dsimp only
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  letI : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  letI : Fintype 𝓀[C] := Fintype.ofFinite _
  have hnLocal : (n : ℕ) ∣ Fintype.card 𝓀[C] - 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact dvd_residueCard_sub_one_of_primitiveRoots C n
      (finitePlace_natCast_valuation_eq_one_of_not_mem_exponent K n v hv)
      (finitePlaceHilbert_primitiveRoots_nonempty K n hmu v)
  exact
    (((AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol
        𝓀[C] n hnLocal
        (integerUnitsToResidueUnits C
          (finitePlaceIntegralCompletionUnit K v a ha)) :
      rootsOfUnity (n : ℕ) 𝓀[C]).1 : 𝓀[C]ˣ) : 𝓀[C])

 noncomputable def finitePlacePrimeIdealPowerResidueFactorResidueValue
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm v.asIdeal).Coprime (n : ℕ))
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    𝓀[C] := by
  dsimp only
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  letI : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  exact
    (((localNthRootsReduction C n
        (nthRootsSubgroupMap K C (n : ℕ)
          (integralRootsOfUnityToNthRoots K (n : ℕ)
            (AlgebraicNumberTheory.PowerResidueSymbols.primeIdealPowerResidueSymbol
              K v n hmu hcoprime a ha)))).1 : 𝓀[C]ˣ) : 𝓀[C])

/-- The tame symbol in a finite-place completion is the image of the
prime-ideal power-residue symbol.  All comparisons are canonical: the only
place hypothesis says that the place does not divide the exponent. -/
private theorem finitePlaceLocalTamePowerResidueSymbol_residueValue_eq
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm v.asIdeal).Coprime (n : ℕ))
    (hv : v ∉ powerResidueExponentFinitePlaces K n)
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) :
    finitePlaceLocalTamePowerResidueSymbolResidueValue K v n hmu hv a ha =
      finitePlacePrimeIdealPowerResidueFactorResidueValue
        K v n hmu hcoprime a ha := by
  unfold finitePlaceLocalTamePowerResidueSymbolResidueValue
  unfold finitePlacePrimeIdealPowerResidueFactorResidueValue
  dsimp only
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  let : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  let : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  let : Fintype 𝓀[C] := Fintype.ofFinite _
  let hnC := finitePlace_natCast_valuation_eq_one_of_not_mem_exponent K n v hv
  let hmuC := finitePlaceHilbert_primitiveRoots_nonempty K n hmu v
  have hnPrime :
      (n : ℕ) ∣ Fintype.card (𝓞 K ⧸ v.asIdeal) - 1 := by
    rw [AlgebraicNumberTheory.PowerResidueSymbols.card_primeIdealResidueField K v]
    exact
      AlgebraicNumberTheory.PowerResidueSymbols.dvd_absNorm_sub_one_of_primitiveRoots
        K v n hmu hcoprime
  have hnLocal : (n : ℕ) ∣ Fintype.card 𝓀[C] - 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact dvd_residueCard_sub_one_of_primitiveRoots C n hnC hmuC
  rw [finitePlace_localNthRootsReduction_integralRoots]
  rw [← AlgebraicNumberTheory.PowerResidueSymbols.rootsOfUnityReductionEquiv_apply
      K v n hmu hcoprime,
    AlgebraicNumberTheory.PowerResidueSymbols.rootsOfUnityReductionEquiv_primeIdealPowerResidueSymbol
      K v n hmu hcoprime a ha]
  rw [finitePlace_integerUnitsToResidueUnits_integralUnit]
  exact congrArg (fun u : 𝓀[C]ˣ => (u : 𝓀[C]))
    (finiteFieldPowerResidueSymbol_unitsMap_ringEquiv
      (finitePlacePrimeResidueEquivLocalResidue K v)
      n hnPrime hnLocal
      (AlgebraicNumberTheory.PowerResidueSymbols.primeIdealResidueUnit
        K v a ha)).symm

private theorem finitePlaceLocalTamePowerResidueSymbolFieldValue_eq_primeIdealValue
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm v.asIdeal).Coprime (n : ℕ))
    (hv : v ∉ powerResidueExponentFinitePlaces K n)
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) :
    @Eq (HeightOneSpectrum.adicAbv K v).Completion
      (finitePlaceLocalTamePowerResidueSymbolFieldValue K v n hmu hv a ha)
      (finitePlacePrimeIdealPowerResidueFactorFieldValue
        K v n hmu hcoprime a ha) := by
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  let : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let hnC :=
    finitePlace_natCast_valuation_eq_one_of_not_mem_exponent K n v hv
  let hmuC := finitePlaceHilbert_primitiveRoots_nonempty K n hmu v
  unfold finitePlaceLocalTamePowerResidueSymbolFieldValue
  unfold finitePlacePrimeIdealPowerResidueFactorFieldValue
  unfold finitePlacePrimeIdealPowerResidueGlobalRoot
  unfold finitePlacePrimeIdealPowerResidueIntegralRoot
  have hRoots :
      localTamePowerResidueSymbol C n hnC hmuC
          (finitePlaceIntegralCompletionUnit K v a ha) =
        nthRootsSubgroupMap K C (n : ℕ)
          (integralRootsOfUnityToNthRoots K (n : ℕ)
            (AlgebraicNumberTheory.PowerResidueSymbols.primeIdealPowerResidueSymbol
              K v n hmu hcoprime a ha)) := by
    apply (localNthRootsReductionEquiv C n hnC hmuC).injective
    rw [localNthRootsReductionEquiv_localTamePowerResidueSymbol]
    apply Subtype.ext
    apply Units.ext
    have hResidue := finitePlaceLocalTamePowerResidueSymbol_residueValue_eq
      K v n hmu hcoprime hv a ha
    unfold finitePlaceLocalTamePowerResidueSymbolResidueValue at hResidue
    unfold finitePlacePrimeIdealPowerResidueFactorResidueValue at hResidue
    dsimp only at hResidue
    exact hResidue
  exact congrArg (fun q : nthRootsSubgroup C (n : ℕ) => (q.1 : C)) hRoots

/-- The normalized additive valuation of a global field unit in the
canonical completion at a finite place. -/
noncomputable def finitePlaceNormalizedValuation
    (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) : ℤ := by
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  letI : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  exact valuationMap C
    (Additive.ofMul (finitePlaceHilbert_completionUnit K v x))

/-- Away from the exponent, a finite-place Hilbert factor with integral-unit
first entry is the prime-ideal power-residue symbol raised to the negative
normalized valuation of the second entry. -/
theorem finitePlaceHilbertSymbol_eq_primeIdealPowerResidueFactor_zpow
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ powerResidueExponentFinitePlaces K n)
    (hcoprime : (Ideal.absNorm v.asIdeal).Coprime (n : ℕ))
    (a : 𝓞 K) (ha : a ∉ v.asIdeal) (b : Kˣ) :
    finitePlaceHilbertSymbol K n hnK hmu v
        (primeAvoidingIntegralFieldUnit K v a ha) b =
      integralRootsOfUnityToNthRoots K (n : ℕ)
          (AlgebraicNumberTheory.PowerResidueSymbols.primeIdealPowerResidueSymbol
              K v n hmu hcoprime a ha) ^
        (-finitePlaceNormalizedValuation K v b) := by
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  let : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let hnC :=
    finitePlace_natCast_valuation_eq_one_of_not_mem_exponent K n v hv
  let hmuC := finitePlaceHilbert_primitiveRoots_nonempty K n hmu v
  let bC := finitePlaceHilbert_completionUnit K v b
  apply nthRootsSubgroupMap_injective K C (n : ℕ)
  rw [finitePlaceHilbertSymbol_map_eq_localHilbertSymbol]
  change
    localHilbertSymbol C n
        (finitePlaceHilbert_natCast_ne_zero K n hnK v) hmuC
        (finitePlaceHilbert_completionUnit K v
          (primeAvoidingIntegralFieldUnit K v a ha)) bC =
      nthRootsSubgroupMap K C (n : ℕ)
        (integralRootsOfUnityToNthRoots K (n : ℕ)
            (AlgebraicNumberTheory.PowerResidueSymbols.primeIdealPowerResidueSymbol
                K v n hmu hcoprime a ha) ^
          (-finitePlaceNormalizedValuation K v b))
  rw [finitePlaceHilbert_completionUnit_primeAvoidingIntegralFieldUnit]
  rw [localHilbertSymbol_tame_formula C n hnC hmuC]
  change
    finitePlaceLocalTamePowerResidueSymbolValue K v n hmu hv a ha ^
        (-finitePlaceNormalizedValuation K v b) = _
  have hBase :
      finitePlaceLocalTamePowerResidueSymbolValue K v n hmu hv a ha =
        finitePlacePrimeIdealPowerResidueFactorValue
          K v n hmu hcoprime a ha := by
    apply Subtype.ext
    apply Units.ext
    simpa only [finitePlaceLocalTamePowerResidueSymbolValue,
      finitePlacePrimeIdealPowerResidueFactorValue,
      finitePlaceLocalTamePowerResidueSymbolFieldValue,
      finitePlacePrimeIdealPowerResidueFactorFieldValue] using
      finitePlaceLocalTamePowerResidueSymbolFieldValue_eq_primeIdealValue
        K v n hmu hcoprime hv a ha
  rw [hBase]
  unfold finitePlacePrimeIdealPowerResidueFactorValue
  unfold finitePlacePrimeIdealPowerResidueGlobalRoot
  unfold finitePlacePrimeIdealPowerResidueIntegralRoot
  rw [map_zpow]


















/-- The Dedekind prime multiplicity is the exponent occurring in the
integer-valued adic valuation. -/
theorem intValuation_eq_exp_neg_idealPrimeMultiplicity
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0) :
    v.intValuation x =
      WithZero.exp
        (-(AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeMultiplicity K v (Ideal.span {x}) : ℤ)) := by
  rw [v.intValuation_if_neg hx]
  rfl

/-- For an integral element, the normalized valuation in the canonical
finite-place completion is the negative multiplicity of the prime in its
principal ideal. -/
theorem finitePlaceNormalizedValuation_nonzeroIntegralFieldUnit
    (v : HeightOneSpectrum (𝓞 K))
    (x : 𝓞 K) (hx : x ≠ 0) :
    finitePlaceNormalizedValuation K v
        (nonzeroIntegralFieldUnit K x hx) =
      -(AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeMultiplicity K v (Ideal.span {x}) : ℤ) := by
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  let : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let : IsUltrametricDist C :=
    finitePlaceArtinCompletionIsUltrametricDist
      (HeightOneSpectrum.adicAbv K v)
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v)
  let m := AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeMultiplicity K v (Ideal.span {x})
  let πData := chosenFinitePlaceCompletionIntegralUniformizer v
  have hπIrreducible : Irreducible πData.completionInteger := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    let completionDVF :
        ValuationTheory.DiscreteValuationField.DVF C :=
      { ValueGroup := ValuativeRel.ValueGroupWithZero C
        valuation := ValuativeRel.valuation C }
    exact
      completionDVF.maximalIdeal_eq_span_uniformizer
        πData.completionInteger_isUniformizer
  let πC : Cˣ :=
    Units.mk0 (πData.completionInteger : C)
      πData.completionInteger_isUniformizer.ne_zero
  let xC : Cˣ :=
    finitePlaceHilbert_completionUnit K v
      (nonzeroIntegralFieldUnit K x hx)
  have hIntX :
      v.intValuation x = WithZero.exp (-(m : ℤ)) := by
    exact intValuation_eq_exp_neg_idealPrimeMultiplicity K v x hx
  have hIntPiPow :
      v.intValuation (πData.integer ^ m) =
        WithZero.exp (-(m : ℤ)) := by
    rw [map_pow, πData.intValuation_eq_exp_neg_one]
    calc
      WithZero.exp (-1 : ℤ) ^ m =
          WithZero.exp (m • (-1 : ℤ)) :=
        (WithZero.exp_nsmul m (-1 : ℤ)).symm
      _ = WithZero.exp (-(m : ℤ)) := by simp
  have hnormX :
      ‖(xC : C)‖ =
        (WithZeroMulInt.toNNReal
          (HeightOneSpectrum.absNorm_ne_zero v)
          (WithZero.exp (-(m : ℤ))) : ℝ) := by
    change ‖algebraMap K C (x : K)‖ = _
    calc
      ‖algebraMap K C (x : K)‖ =
          HeightOneSpectrum.adicAbv K v (x : K) :=
        AbsoluteValue.completionAbsoluteValue_coe
          (HeightOneSpectrum.adicAbv K v) (x : K)
      _ = _ := by
        rw [HeightOneSpectrum.adicAbv_def,
          HeightOneSpectrum.valuation_of_algebraMap, hIntX]
  have hnormPiPow :
      ‖((πC ^ m : Cˣ) : C)‖ =
        (WithZeroMulInt.toNNReal
          (HeightOneSpectrum.absNorm_ne_zero v)
          (WithZero.exp (-(m : ℤ))) : ℝ) := by
    have hπC :
        (πC : C) = algebraMap K C (πData.integer : K) := by
      exact πData.coe_completionInteger
    have hπCPow :
        ((πC ^ m : Cˣ) : C) =
          algebraMap K C (((πData.integer ^ m : 𝓞 K) : K)) := by
      have hIntegerPow :
          (((πData.integer ^ m : 𝓞 K) : K)) =
            (πData.integer : K) ^ m := by
        exact map_pow (algebraMap (𝓞 K) K) πData.integer m
      rw [Units.val_pow_eq_pow_val, hπC, hIntegerPow, map_pow]
    calc
      ‖((πC ^ m : Cˣ) : C)‖ =
          ‖algebraMap K C ((πData.integer ^ m : 𝓞 K) : K)‖ :=
        congrArg norm hπCPow
      _ = HeightOneSpectrum.adicAbv K v
          ((πData.integer ^ m : 𝓞 K) : K) :=
        AbsoluteValue.completionAbsoluteValue_coe
          (HeightOneSpectrum.adicAbv K v)
          ((πData.integer ^ m : 𝓞 K) : K)
      _ =
          (WithZeroMulInt.toNNReal
            (HeightOneSpectrum.absNorm_ne_zero v)
            (WithZero.exp (-(m : ℤ))) : ℝ) := by
        rw [HeightOneSpectrum.adicAbv_def,
          HeightOneSpectrum.valuation_of_algebraMap, hIntPiPow]
  have hraw :
      ValuativeRel.valuation C (xC : C) =
        ValuativeRel.valuation C ((πC ^ m : Cˣ) : C) := by
    apply canonicalValuation_eq_of_valuation_eq
      (v := NormedField.valuation (K := C))
    apply NNReal.eq
    simpa only [NormedField.valuation_apply, coe_nnnorm] using
      hnormX.trans hnormPiPow.symm
  have hValuationMap :
      valuationMap C (Additive.ofMul xC) =
        valuationMap C (Additive.ofMul (πC ^ m)) := by
    rw [valuationMap_apply, valuationMap_apply]
    unfold IsNonarchimedeanLocalField.v
    congr 2
    exact congrArg
      (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt C) hraw
  have hπCValuation :
      valuationMap C (Additive.ofMul πC) = -1 := by
    rw [valuationMap_apply]
    exact
      v_integerRingIrreducibleFieldUnit C πData.completionInteger
        hπIrreducible πC rfl
  calc
    finitePlaceNormalizedValuation K v
        (nonzeroIntegralFieldUnit K x hx) =
        valuationMap C (Additive.ofMul xC) := rfl
    _ = valuationMap C (Additive.ofMul (πC ^ m)) := hValuationMap
    _ = (m : ℤ) * valuationMap C (Additive.ofMul πC) := by
      rw [valuationMap_ofMul_pow]
    _ = -(m : ℤ) := by rw [hπCValuation]; simp
    _ = -(AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeMultiplicity K v (Ideal.span {x}) : ℤ) := rfl

/-- Prime avoidance is the common special case of the integral valuation
formula used for numerator units. -/
theorem finitePlaceNormalizedValuation_primeAvoidingIntegralFieldUnit
    (v : HeightOneSpectrum (𝓞 K))
    (x : 𝓞 K) (hx : x ∉ v.asIdeal) :
    finitePlaceNormalizedValuation K v
        (primeAvoidingIntegralFieldUnit K v x hx) =
      -(AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeMultiplicity K v (Ideal.span {x}) : ℤ) := by
  let hx0 : x ≠ 0 := by
    intro hxzero
    apply hx
    rw [hxzero]
    exact Ideal.zero_mem _
  change finitePlaceNormalizedValuation K v
      (nonzeroIntegralFieldUnit K x hx0) = _
  exact finitePlaceNormalizedValuation_nonzeroIntegralFieldUnit K v x hx0






























/-- Finite-place Hilbert symbols inherit skew symmetry from the local
Hilbert symbol in the canonical completion. -/
theorem finitePlaceHilbertSymbol_skew
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ) :
    finitePlaceHilbertSymbol K n hnK hmu v a b =
      (finitePlaceHilbertSymbol K n hnK hmu v b a)⁻¹ := by
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  let : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  apply nthRootsSubgroupMap_injective K C (n : ℕ)
  rw [map_inv,
    finitePlaceHilbertSymbol_map_eq_localHilbertSymbol,
    finitePlaceHilbertSymbol_map_eq_localHilbertSymbol]
  exact
    localHilbertSymbol_skew C n
      (finitePlaceHilbert_natCast_ne_zero K n hnK v)
      (finitePlaceHilbert_primitiveRoots_nonempty K n hmu v)
      (finitePlaceHilbert_completionUnit K v a)
      (finitePlaceHilbert_completionUnit K v b)









































































































































/-- A concrete finite set containing every finite place where a local
power-residue factor of `a` and `b` may be nontrivial.  Its exponent part is
the exact set of prime divisors of `(n)`. -/
noncomputable def powerResidueBadFinitePlaces
    (n : ℕ+) (a b : Kˣ) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (chosenUnitFiniteSupport (K := K) a ∪
      chosenUnitFiniteSupport (K := K) b) ∪
    powerResidueExponentFinitePlaces K n













private theorem valuation_eq_one_of_not_mem_chosenUnitFiniteSupport
    (x : Kˣ) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ chosenUnitFiniteSupport (K := K) x) :
    v.valuation K (x : K) = 1 :=
  (mem_SUnitGroup_iff (K := K)
      (chosenUnitFiniteSupport (K := K) x) x).mp
    (mem_sUnitGroup_chosenUnitFiniteSupport (K := K) x) v hv

/-- The finite-place Hilbert symbol is trivial when the exponent and both
global arguments are units at this place. -/
theorem finitePlaceHilbertSymbol_eq_one_of_valuation_eq_one
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : Kˣ) (v : HeightOneSpectrum (𝓞 K))
    (hva : v.valuation K (a : K) = 1)
    (hvb : v.valuation K (b : K) = 1)
    (hvn : v.valuation K ((n : ℕ) : K) = 1) :
    finitePlaceHilbertSymbol K n hnK hmu v a b = 1 := by
  let L := chosenSimpleKummerExtension K n hnK b
  let : FiniteDimensional K L :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K L :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let : NumberField L := NumberField.of_module_finite K L
  have haIntegral :
      IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K a) ∈
        (v.adicCompletionIntegers K).units := by
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
    rw [IdeleGroup.finiteComponent_principalIdele,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hva
  have hUnramified :
      Algebra.IsUnramifiedAt (𝓞 K)
        (finitePlaceExtensionCentre
          (K := K) (L := L) v
          (chosenFinitePlaceExtension (L := L) v)).asIdeal := by
    apply
      chosenSimpleKummerExtension_isUnramifiedAt_at_all_finitePlacesAbove_of_valuation_eq_one
        (K := K) n hnK hmu b v hvb hvn
    exact
      finitePlaceBelow_finitePlaceExtensionCentre
        (K := K) (L := L) v
          (chosenFinitePlaceExtension (L := L) v)
  have hArtin :
      chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v
          (IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K a)) = 1 :=
    chosenFinitePlaceArtinMonoidHom_eq_one_of_integral_of_unramifiedAt
      (K := K) (L := L) v (IdeleGroup.principalIdele K a)
        haIntegral hUnramified
  rw [← finitePlaceKummerRootCharacter_localGlobal K n hnK hmu v a b]
  unfold finitePlaceKummerRootCharacter
  unfold finitePlaceKummerRootCharacterOfExtension
  have hcomponent :
      (IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K a) :
          (v.adicCompletion K)ˣ) =
        Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a := by
    apply Units.ext
    calc
      ((IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K a) :
          (v.adicCompletion K)ˣ) : v.adicCompletion K) =
          ((a : K) : v.adicCompletion K) :=
        IdeleGroup.finiteComponent_principalIdele a v
      _ = algebraMap K (v.adicCompletion K) (a : K) := by
        symm
        have hmap := congrFun
          (IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion
            (R := 𝓞 K) (S := K) (K := K) (v := v)) (a : K)
        simpa using hmap
  rw [hcomponent] at hArtin
  unfold chosenFinitePlaceArtinMonoidHom at hArtin
  dsimp only at hArtin ⊢
  rw [hArtin, map_one, map_one]

/-- Outside the concrete bad-place set, the finite-place Hilbert factor is
trivial. -/
theorem finitePlaceHilbertSymbol_eq_one_of_not_mem_powerResidueBadFinitePlaces
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : Kˣ) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ powerResidueBadFinitePlaces K n a b) :
    finitePlaceHilbertSymbol K n hnK hmu v a b = 1 := by
  have hvaSupport : v ∉ chosenUnitFiniteSupport (K := K) a := by
    intro hva
    apply hv
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hva)
  have hvbSupport : v ∉ chosenUnitFiniteSupport (K := K) b := by
    intro hvb
    apply hv
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hvb)
  have hvnSupport :
      v ∉ powerResidueExponentFinitePlaces K n := by
    intro hvn
    apply hv
    exact Finset.mem_union_right _ hvn
  have hva : v.valuation K (a : K) = 1 :=
    valuation_eq_one_of_not_mem_chosenUnitFiniteSupport K a v hvaSupport
  have hvb : v.valuation K (b : K) = 1 :=
    valuation_eq_one_of_not_mem_chosenUnitFiniteSupport K b v hvbSupport
  have hvn : v.valuation K ((n : ℕ) : K) = 1 := by
    have hvnNotDvd :
        ¬ v.asIdeal ∣ powerResidueExponentIdeal K n := by
      simpa only [mem_powerResidueExponentFinitePlaces_iff] using hvnSupport
    have hvnNotMem : ((n : ℕ) : 𝓞 K) ∉ v.asIdeal := by
      intro hvnMem
      apply hvnNotDvd
      rw [powerResidueExponentIdeal, Ideal.dvd_span_singleton]
      exact hvnMem
    simpa only [map_natCast] using
      (v.valuation_eq_one_iff_notMem (K := K)
        (r := ((n : ℕ) : 𝓞 K))).2 hvnNotMem
  exact finitePlaceHilbertSymbol_eq_one_of_valuation_eq_one
    K n hnK hmu a b v hva hvb hvn





































































































































































































































































































































































/-! ## Quadratic specialization over the rational field -/

open AlgebraicNumberTheory.PowerResidueSymbols




















































































































































































































































/-! ## Rational principal-ideal factorization -/

/-- The principal ideal of `𝓞 ℚ` generated by a natural number, expressed
through the canonical equivalence `𝓞 ℚ ≃+* ℤ`. -/
noncomputable def rationalPrincipalIdeal (b : ℕ) : Ideal (𝓞 ℚ) :=
  Ideal.span {Rat.ringOfIntegersEquiv.symm (b : ℤ)}











/-- The height-one prime of `𝓞 ℚ` attached to `p` is generated by the
corresponding rational integer. -/
theorem rationalPrime_asIdeal_eq_span
    (p : Nat.Primes) :
    (RayClass.rationalPrime p).asIdeal =
      Ideal.span {Rat.ringOfIntegersEquiv.symm (p.1 : ℤ)} := by
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    RayClass.rationalPrime p
  have hIntEquiv :
      Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) =
        Rat.ringOfIntegersEquiv := by
    ext x
    exact
      Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv x
  have hspan :
      Ideal.span {(p.1 : ℤ)} =
        v.asIdeal.map Rat.ringOfIntegersEquiv := by
    simpa only [v, RayClass.natGenerator_rationalPrime,
      hIntEquiv] using
      Rat.HeightOneSpectrum.span_natGenerator v
  apply
    ((RingEquiv.idealComapOrderIso
      Rat.ringOfIntegersEquiv).symm).injective
  simp only [RingEquiv.idealComapOrderIso_symm_apply]
  calc
    (RayClass.rationalPrime p).asIdeal.map
          Rat.ringOfIntegersEquiv =
        Ideal.span {(p.1 : ℤ)} := by
      simpa only [v] using hspan.symm
    _ =
      (Ideal.span
          {Rat.ringOfIntegersEquiv.symm (p.1 : ℤ)}).map
            Rat.ringOfIntegersEquiv := by
      rw [Ideal.map_span, Set.image_singleton,
        Rat.ringOfIntegersEquiv.apply_symm_apply]

/-- Divisibility of a rational principal ideal by the prime over `p` is
exactly natural-number divisibility by `p`. -/
theorem rationalPrime_dvd_rationalPrincipalIdeal_iff
    (p : Nat.Primes) (b : ℕ) :
    (RayClass.rationalPrime p).asIdeal ∣ rationalPrincipalIdeal b ↔
      p.1 ∣ b := by
  rw [rationalPrincipalIdeal, rationalPrime_asIdeal_eq_span,
    Ideal.dvd_iff_le, Ideal.span_singleton_le_span_singleton,
    map_dvd_iff Rat.ringOfIntegersEquiv.symm,
    Int.natCast_dvd_natCast]













































































































/-- Prime divisors of the rational principal ideal `(b)` are canonically the
natural prime factors of `b`. -/
noncomputable def rationalPrincipalIdealPrimeDivisorsEquiv
    (b : ℕ) (hb : b ≠ 0) :
    idealPrimeDivisors ℚ (rationalPrincipalIdeal b) ≃
      b.primeFactors where
  toFun P :=
    ⟨Rat.HeightOneSpectrum.natGenerator P.1,
      (Nat.mem_primeFactors_of_ne_zero hb).mpr
        ⟨Rat.HeightOneSpectrum.prime_natGenerator P.1,
            (rationalPrime_dvd_rationalPrincipalIdeal_iff
            ⟨Rat.HeightOneSpectrum.natGenerator P.1,
              Rat.HeightOneSpectrum.prime_natGenerator P.1⟩ b).mp
            (by
              have hprimeEq :
                  RayClass.rationalPrime
                      ⟨Rat.HeightOneSpectrum.natGenerator P.1,
                        Rat.HeightOneSpectrum.prime_natGenerator P.1⟩ =
                    P.1 :=
                (Rat.HeightOneSpectrum.primesEquiv
                  (R := 𝓞 ℚ)).symm_apply_apply P.1
              rw [hprimeEq]
              exact P.2)⟩⟩
  invFun p :=
    ⟨RayClass.rationalPrime
        ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩,
      (rationalPrime_dvd_rationalPrincipalIdeal_iff
        ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ b).mpr
        (Nat.dvd_of_mem_primeFactors p.2)⟩
  left_inv P := by
    apply Subtype.ext
    have hq :
        (⟨Rat.HeightOneSpectrum.natGenerator P.1,
          Rat.HeightOneSpectrum.prime_natGenerator P.1⟩ : Nat.Primes) =
          Rat.HeightOneSpectrum.primesEquiv P.1 :=
      Subtype.ext rfl
    simpa only [RayClass.rationalPrime, hq] using
      (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm_apply_apply P.1
  right_inv p := by
    apply Subtype.ext
    exact
      RayClass.natGenerator_rationalPrime
        ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩

/-- Reindexing a natural prime factor back to a height-one prime gives the
standard rational prime above it. -/
@[simp]
theorem rationalPrincipalIdealPrimeDivisorsEquiv_symm_apply_val
    (b : ℕ) (hb : b ≠ 0) (p : b.primeFactors) :
    ((rationalPrincipalIdealPrimeDivisorsEquiv b hb).symm p).1 =
      RayClass.rationalPrime
        ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ :=
  rfl

















































































































































































































end Reciprocity
end GlobalClassFieldTheory

end
