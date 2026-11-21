module

public import ValuedFieldTheory.Valuation.LocalRingEquiv
public import ValuedFieldTheory.LocalField.Analytic.PrincipalUnitExpLogEquiv
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PadicPowerIndex
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence
public import ValuedFieldTheory.LocalField.Padic.NonarchimedeanLocalField
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import Mathlib.NumberTheory.Padics.ProperSpace

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/











set_option autoImplicit false

/-!
# Principal units of the p-adic field

This file identifies the standard p-adic integer and complete-DVF models,
computes their principal-unit quotients, and records the logarithm/exponential
power formulas used by local cyclotomic norm calculations.
-/

noncomputable section

open scoped ValuativeRel WithZero

namespace LocalFieldTheory.Padic

open LocalFieldTheory
open ValuationTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (p : ℕ) [Fact p.Prime]

/-- The valuative integer ring of `ℚ_p` is canonically equivalent to
`ℤ_p`. -/
noncomputable def integerRingEquivPadicInt :
    𝒪[ℚ_[p]] ≃+* ℤ_[p] where
  toFun x := ⟨x, (integer_mem_iff_norm_le_one p x).1 x.property⟩
  invFun x := ⟨x, (integer_mem_iff_norm_le_one p x).2 x.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

/-- The equivalence with `ℤ_p` preserves the underlying element of `ℚ_p`. -/
@[simp] theorem integerRingEquivPadicInt_coe (x : 𝒪[ℚ_[p]]) :
    ((integerRingEquivPadicInt p x : ℤ_[p]) : ℚ_[p]) = (x : ℚ_[p]) := rfl

/-- The valuative integer ring of `ℚ_p` is canonically equivalent to the
valuation subring of the bundled p-adic complete discrete valuation field. -/
noncomputable def integerRingEquivPadicDVRValuationSubring :
    𝒪[ℚ_[p]] ≃+*
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuationSubring :=
  (integerRingEquivPadicInt p).trans
    (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicIntEquivValuationSubring p)

/-- The equivalence with the bundled p-adic valuation subring preserves the
underlying field element. -/
@[simp] theorem integerRingEquivPadicDVRValuationSubring_coe
    (x : 𝒪[ℚ_[p]]) :
    ((integerRingEquivPadicDVRValuationSubring p x :
        (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuationSubring) :
      ℚ_[p]) = (x : ℚ_[p]) := by
  rfl







/-- The rational prime `p`, regarded as an element of the p-adic integer
ring. -/
noncomputable def padicPrimeInteger : 𝒪[ℚ_[p]] :=
  (integerRingEquivPadicInt p).symm (p : ℤ_[p])

/-- Coercing the p-adic prime integer back to `ℚ_p` gives `p`. -/
@[simp] theorem padicPrimeInteger_coe :
    ((padicPrimeInteger p : 𝒪[ℚ_[p]]) : ℚ_[p]) = (p : ℚ_[p]) := rfl






/-- The residue field of the canonical p-adic discrete valuation is finite. -/
noncomputable instance padicDVR_residueField_finite :
    Finite (IsLocalRing.ResidueField
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p).valuationSubring) := by
  simpa [LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF,
    ValuationTheory.DiscreteValuationField.CompleteDVF.residueField,
    ValuationTheory.DiscreteValuationField.CompleteDVF.valuationSubring,
    ValuationTheory.DiscreteValuationField.CompleteDVF.toDVF] using
      LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF_residueField_finite p


/-- The canonical multiplicative discrete valuation sends `p` to
`exp (-1)`. -/
theorem padicDVR_valuation_p :
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p (p : ℚ_[p]) =
      WithZero.exp (-1 : ℤ) := by
  change (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation ℚ_[p]
      (((p : ℤ_[p]) : ℚ_[p])) = WithZero.exp (-1 : ℤ)
  calc
    (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation ℚ_[p]
        (((p : ℤ_[p]) : ℚ_[p])) =
        (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).intValuation (p : ℤ_[p]) := by
      simpa using
        (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation_of_algebraMap
          (K := ℚ_[p]) (p : ℤ_[p])
    _ = WithZero.exp (-1 : ℤ) :=
      IsDedekindDomain.HeightOneSpectrum.intValuation_singleton
        (IsDiscreteValuationRing.maximalIdeal ℤ_[p])
        (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
        PadicInt.maximalIdeal_eq_span_p







end LocalFieldTheory.Padic

end
