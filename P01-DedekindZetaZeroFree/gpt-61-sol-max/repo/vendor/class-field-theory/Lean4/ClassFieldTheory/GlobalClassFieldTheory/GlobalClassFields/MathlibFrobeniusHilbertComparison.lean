module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticHilbertClassFieldReciprocity
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.ExtensionIndex
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.IntegerRingComparison
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
public import ClassFieldTheory.AlgebraicNumberTheory.SUnit.GaloisAction
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Core
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.BigHilbertClassFieldOverOriginalBase
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorFrobenius
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldMaximalSubextension
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldPrimeSplitting
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldUnramifiedMaximality
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassFieldMaximalSubextension
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassFieldOverOriginalBase
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealDecompositionLaw
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertPrincipalization
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertSplitting
public import ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlaceIdeal
public import ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.NormalClosure
public import ClassFieldTheory.AlgebraicNumberTheory.SUnit.Herbrand
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Frobenius
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius
public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt
public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeSplitsCompletely
public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeFractionalIdeal
public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsBigHilbertClassField
public import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
public import ClassFieldTheory.AlgebraicNumberTheory.NumberField.MathlibUnramifiedInterface

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
































set_option autoImplicit false

/-!
# Frobenius and Hilbert class fields implementation

This module supplies the implementation proofs for the compact public
statements in `ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields`.

The prime element exposed below is the arithmetic-normalized prime Artin
element.  Its residue action identifies it with Mathlib's arithmetic
Frobenius at every unramified finite prime.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory.GlobalClassFieldComparison

open NumberField IsDedekindDomain
open LocalFieldTheory
open scoped ValuativeRel

section PrimeArtin

open scoped Pointwise
open AlgebraicNumberTheory.Valuations

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]


























































































































































end PrimeArtin

section ArithmeticFrobenius

open scoped Pointwise































































end ArithmeticFrobenius

/-- In an abelian extension, Mathlib's chosen arithmetic Frobenius is
independent of the prime above a fixed base prime.  Mathlib chooses
conjugate lifts, and conjugacy is equality in the abelian Galois group. -/
theorem arithmeticFrobeniusAt_eq_of_liesOver
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w w' : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal.LiesOver v.asIdeal)
    (hw' : w'.asIdeal.LiesOver v.asIdeal) :
    arithmeticFrobeniusAt (K := K) w =
      arithmeticFrobeniusAt (K := K) w' := by
  obtain ⟨τ, hτ⟩ := isConj_iff.mp
    (isConj_arithFrobAt (𝓞 K) (L ≃ₐ[K] L)
      w.asIdeal w'.asIdeal (hw.over.symm.trans hw'.over))
  calc
    arithmeticFrobeniusAt (K := K) w =
        τ * arithmeticFrobeniusAt (K := K) w * τ⁻¹ := by
      rw [IsMulCommutative.is_comm.comm τ
        (arithmeticFrobeniusAt (K := K) w), mul_assoc,
        mul_inv_cancel, mul_one]
    _ = arithmeticFrobeniusAt (K := K) w' := hτ

/-- At an unramified finite prime, the arithmetic-normalized prime Artin
element is Mathlib's arithmetic Frobenius, independently of the chosen prime
above the base prime. -/
theorem arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal.LiesOver v.asIdeal)
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) :
    GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := L) v =
      arithmeticFrobeniusAt (K := K) w := by
  classical
  let w₀ := chosenFinitePlaceExtension (L := L) v
  let W := finitePlaceExtensionCentre (K := K) (L := L) v w₀
  let P : Ideal (𝓞 K) := v.asIdeal
  let Q : Ideal (𝓞 L) := W.asIdeal
  let G := L ≃ₐ[K] L
  let C := ChosenFinitePlaceBaseCompletion (K := K) v
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v
  let : Algebra C E :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinLocalizedAlgebra v w₀
  have hW : Q.LiesOver P :=
    finitePlaceExtensionCentre_liesOver (K := K) (L := L) v w₀
  let : Q.LiesOver P := hW
  let : w.asIdeal.LiesOver P := hw
  let : Finite G := IsGaloisGroup.finite G K L
  let : IsGaloisGroup G (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing G (𝓞 K) (𝓞 L) K L
  have hEw : w.asIdeal.ramificationIdx (𝓞 K) = 1 :=
    (Ideal.ramificationIdx_eq_one_iff).mpr hunram
  have hEQ : Q.ramificationIdx (𝓞 K) =
      w.asIdeal.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx_eq_of_isGaloisGroup P Q w.asIdeal G
  have hunramQ : Algebra.IsUnramifiedAt (𝓞 K) Q :=
    (Ideal.ramificationIdx_eq_one_iff).mp (hEQ.trans hEw)
  have hChosen : ChosenFinitePlaceIsUnramified
      (K := K) (L := L) v :=
    chosenFinitePlaceIsUnramified_of_isUnramifiedAt
      (K := K) (L := L) v hunramQ
  let : IsNonarchimedeanLocalField.IsUnramifiedValuedExtension C E := hChosen
  let vK := HeightOneSpectrum.adicAbv K v
  let eD : HilbertRamification.absoluteValueDecompositionGroup K w₀.1 ≃*
      (E ≃ₐ[C] E) :=
    HilbertRamification.decompositionGroupEquivAlgebraicLocalizationAut
      vK (RayClass.adicAbv_isNontrivial v) w₀
  let f : E ≃ₐ[C] E := arithmeticFrobeniusOfUnramifiedValuation C E
  let δ : HilbertRamification.absoluteValueDecompositionGroup K w₀.1 :=
    eD.symm f
  have heDδ : eD δ = f := eD.apply_symm_apply f
  have hδ : (δ : G) =
      GlobalClassFieldTheory.GlobalClassFields.chosenFinitePlaceArithmeticFrobenius
        (K := K) (L := L) v hChosen := by
    change (eD.symm f : G) =
      GlobalClassFieldTheory.Reciprocity.finitePlaceLocalToGlobalMonoidHom
        (K := K) (L := L) v w₀ f
    rfl
  let e : (𝓞 L ⧸ Q) ≃+* 𝓀[E] :=
    chosenFinitePlaceLocalizedResidueEquiv (K := K) (L := L) v
  have hCard : Nat.card 𝓀[C] =
      Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) := by
    rw [finitePlaceCompletion_residueField_card (K := K) v,
      hW.over.symm]
  have hResidue (x : 𝓞 L) :
      Ideal.Quotient.mk Q
          (NumberField.RingOfIntegers.mapAlgEquiv (δ : G) x) =
        (Ideal.Quotient.mk Q x) ^
          Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) := by
    apply e.injective
    calc
      e (Ideal.Quotient.mk Q
          (NumberField.RingOfIntegers.mapAlgEquiv (δ : G) x)) =
          LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure C E
            (eD δ) (e (Ideal.Quotient.mk Q x)) :=
        chosenFinitePlaceLocalizedResidueEquiv_equivariant
          (K := K) (L := L) v δ x
      _ = LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure C E
            f (e (Ideal.Quotient.mk Q x)) := by
        simp only [heDδ]
      _ = (e (Ideal.Quotient.mk Q x)) ^ Nat.card 𝓀[C] :=
        galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_apply
          C E (e (Ideal.Quotient.mk Q x))
      _ = e ((Ideal.Quotient.mk Q x) ^
            Nat.card (𝓞 K ⧸ Q.under (𝓞 K))) := by
        exact (congrArg
          (fun n : ℕ => (e (Ideal.Quotient.mk Q x)) ^ n) hCard).trans
          (map_pow e (Ideal.Quotient.mk Q x) _).symm
  have hArith : IsArithFrobAt (𝓞 K) (δ : G) Q := by
    intro x
    change NumberField.RingOfIntegers.mapAlgEquiv (δ : G) x -
        x ^ Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) ∈ Q
    rw [← Ideal.Quotient.eq, map_pow]
    exact hResidue x
  have hMath : IsArithFrobAt (𝓞 K)
      (arithmeticFrobeniusAt (K := K) W) Q := by
    change IsArithFrobAt (𝓞 K) (arithFrobAt (𝓞 K) G Q) Q
    exact IsArithFrobAt.arithFrobAt (𝓞 K) G Q
  have hInertiaCard : Nat.card (Q.inertia G) = 1 := by
    calc
      Nat.card (Q.inertia G) = P.ramificationIdxIn (𝓞 L) :=
        Ideal.card_inertia_eq_ramificationIdxIn (G := G) P Q
      _ = Q.ramificationIdx (𝓞 K) :=
        Ideal.ramificationIdxIn_eq_ramificationIdx P Q G
      _ = 1 := hEQ.trans hEw
  have hInertiaBot : Q.inertia G = ⊥ :=
    (Subgroup.eq_bot_iff_card (Q.inertia G)).mpr hInertiaCard
  have hDiff : (δ : G) * (arithmeticFrobeniusAt (K := K) W)⁻¹ ∈
      Q.inertia G := hArith.mul_inv_mem_inertia hMath
  have hDiffEq : (δ : G) * (arithmeticFrobeniusAt (K := K) W)⁻¹ = 1 := by
    simpa only [hInertiaBot, Subgroup.mem_bot] using hDiff
  have hδEq : (δ : G) = arithmeticFrobeniusAt (K := K) W :=
    mul_inv_eq_one.mp hDiffEq
  calc
    GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := L) v =
        GlobalClassFieldTheory.GlobalClassFields.chosenFinitePlaceArithmeticFrobenius
          (K := K) (L := L) v hChosen :=
      GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin_eq_chosenFinitePlaceArithmeticFrobenius
        (K := K) (L := L) v hChosen
    _ = (δ : G) := hδ.symm
    _ = arithmeticFrobeniusAt (K := K) W := hδEq
    _ = arithmeticFrobeniusAt (K := K) w :=
      arithmeticFrobeniusAt_eq_of_liesOver
        (K := K) (L := L) v W w hW hw





























































section HilbertClassFields

variable (K : Type) [Field K] [NumberField K]












































































































































































































































































































end HilbertClassFields

end ClassFieldTheory.GlobalClassFieldComparison

end
