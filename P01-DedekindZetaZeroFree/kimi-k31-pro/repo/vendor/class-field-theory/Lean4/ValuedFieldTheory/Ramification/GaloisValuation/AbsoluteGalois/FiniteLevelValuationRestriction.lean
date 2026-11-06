module

public import ValuedFieldTheory.Valuation.Henselian.Complete
public import ValuedFieldTheory.Valuation.Henselian.Core
public import ValuedFieldTheory.Valuation.Henselian.Factorization.AdicLimits
public import ValuedFieldTheory.Valuation.Henselian.Factorization.Assembly
public import ValuedFieldTheory.Valuation.Henselian.Factorization.Basic
public import ValuedFieldTheory.Valuation.Henselian.Factorization.CoefficientMinimum
public import ValuedFieldTheory.Valuation.Henselian.Factorization.Complete
public import ValuedFieldTheory.Valuation.Henselian.Factorization.DegreeBounds
public import ValuedFieldTheory.Valuation.Henselian.Factorization.DivisionBounds
public import ValuedFieldTheory.Valuation.Henselian.Factorization.ErrorPowers
public import ValuedFieldTheory.Valuation.Henselian.Factorization.FiniteApproximation
public import ValuedFieldTheory.Valuation.Henselian.Factorization.InfiniteApproximation
public import ValuedFieldTheory.Valuation.Henselian.Factorization.Iteration
public import ValuedFieldTheory.Valuation.Henselian.Factorization.PrincipalLimits
public import ValuedFieldTheory.Valuation.Henselian.Factorization.Step
public import ValuedFieldTheory.Valuation.Henselian.Factorization.Truncation
public import ValuedFieldTheory.Valuation.Henselian.Factorization.WeakLimits
public import ValuedFieldTheory.Valuation.Henselian.IrreduciblePolynomialBounds
public import ValuedFieldTheory.Valuation.Henselian.IrreduciblePolynomialLifting
public import ValuedFieldTheory.Valuation.Henselian.MonicFactorization
public import ValuedFieldTheory.Valuation.Henselian.NonmonicReduction
public import ValuedFieldTheory.Valuation.Henselian.PrimitiveFactorization
public import ValuedFieldTheory.Valuation.Henselian.PrimitiveReduction
public import ValuedFieldTheory.Valuation.Henselian.UniqueAlgebraicExtensions
public import ValuedFieldTheory.Valuation.Henselian.UniqueExtensionPrimitive
public import ValuedFieldTheory.Valuation.Henselian.UniqueExtensionReduction
public import ValuedFieldTheory.Valuation.Henselian.ValuationExtensionCriterion
public import ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
public import ValuedFieldTheory.Ramification.GaloisValuation.Ramification
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Sets.Opens

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/








































set_option autoImplicit false

namespace RamificationTheory

open ValuationTheory
open ValuationTheory.DiscreteValuationField.HenselianDVF

/-!
# Finite-level valuation restriction for absolute Galois arguments

This file isolates the valuation-restriction and separable-power lemmas
used to pass from absolute Galois questions to finite intermediate fields.
-/

noncomputable section

universe u v w z

namespace ValuationSubring

variable {K : Type u} [Field K] (A : ValuationSubring K)

/-- Membership in a valuation subring is detected by any positive natural
power.

This is useful in absolute arguments: after moving an element into a finite
separable level only after taking a positive power, valuation-subring
membership can be pulled back to the original element. -/
theorem mem_iff_pow_mem (x : K) {n : ℕ} (hn : 0 < n) :
    x ∈ A ↔ x ^ n ∈ A := by
  constructor
  · intro hx
    exact A.toSubring.pow_mem hx n
  · intro hxpow
    induction n with
    | zero =>
        cases hn
    | succ n ih =>
        by_cases hn0 : n = 0
        · simpa [hn0] using hxpow
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
          by_cases hx0 : x = 0
          · simp [hx0]
          rcases A.mem_or_inv_mem x with hx | hxinv
          · exact hx
          · have hxpred : x ^ n ∈ A := by
              have hmul : x ^ (n + 1) * x⁻¹ ∈ A :=
                A.mul_mem _ _ hxpow hxinv
              have hpow : x ^ (n + 1) * x⁻¹ = x ^ n := by
                rw [pow_succ, mul_assoc, mul_inv_cancel₀, mul_one]
                exact hx0
              simpa [hpow] using hmul
            exact ih hnpos hxpred

/-- States the theorem `mem_of_pow_mem`. -/
theorem mem_of_pow_mem (x : K) {n : ℕ} (hn : 0 < n) (hx : x ^ n ∈ A) :
    x ∈ A :=
  (mem_iff_pow_mem A x hn).2 hx



section RestrictIntermediateField

variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]

/-- Restrict a valuation subring of an ambient field to an intermediate field. -/
def restrictIntermediateField
    (A : ValuationSubring Ω) (E : IntermediateField K Ω) :
    ValuationSubring E :=
  A.comap (algebraMap E Ω)

/-- States the theorem `restrictIntermediateField_eq_comap`. -/
@[simp] theorem restrictIntermediateField_eq_comap
    (A : ValuationSubring Ω) (E : IntermediateField K Ω) :
    (restrictIntermediateField A E) = A.comap (algebraMap E Ω) :=
  rfl

/-- States the theorem `mem_restrictIntermediateField_iff`. -/
@[simp] theorem mem_restrictIntermediateField_iff
    (A : ValuationSubring Ω) (E : IntermediateField K Ω) (x : E) :
    x ∈ (restrictIntermediateField A E) ↔ (x : Ω) ∈ A :=
  Iff.rfl

/-- States the theorem `restrictIntermediateField_hasExtension`. -/
theorem restrictIntermediateField_hasExtension
    {Γ : Type w} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (A : ValuationSubring Ω)
    [_root_.Valuation.HasExtension v A.valuation]
    (E : IntermediateField K Ω) :
    _root_.Valuation.HasExtension v ((restrictIntermediateField A E)).valuation := by
  apply _root_.Valuation.HasExtension.ofComapInteger
  ext x
  simp only [Subring.mem_comap, Valuation.mem_integer_iff,
    ValuationSubring.valuation_le_one_iff,
    mem_restrictIntermediateField_iff]
  change algebraMap E Ω (algebraMap K E x) ∈ A ↔ v x ≤ 1
  rw [← IsScalarTower.algebraMap_apply K E Ω x]
  rw [← A.valuation_le_one_iff (algebraMap K Ω x)]
  exact _root_.Valuation.HasExtension.val_map_le_one_iff
    (vR := v) (vA := A.valuation) x

open scoped Pointwise





/-- A `K`-algebra automorphic translate of an extension valuation subring is
again an extension of the base valuation. -/
theorem smul_hasExtension
    {Γ : Type w} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (A : ValuationSubring Ω)
    [_root_.Valuation.HasExtension v A.valuation]
    (σ : Ω ≃ₐ[K] Ω) :
    _root_.Valuation.HasExtension v (σ • A).valuation := by
  apply _root_.Valuation.HasExtension.ofComapInteger
  ext x
  simp [ValuationSubring.integer_valuation, Valuation.mem_integer_iff]
  rw [Subring.mem_pointwise_smul_iff_inv_smul_mem]
  have hcomm : (σ⁻¹) (algebraMap K Ω x) = algebraMap K Ω x :=
    (σ⁻¹).commutes x
  change (σ⁻¹) (algebraMap K Ω x) ∈ A.toSubring ↔ v x ≤ 1
  rw [hcomm]
  change (algebraMap K Ω x) ∈ A ↔ v x ≤ 1
  rw [← A.valuation_le_one_iff (algebraMap K Ω x)]
  exact _root_.Valuation.HasExtension.val_map_le_one_iff
    (vR := v) (vA := A.valuation) x











end RestrictIntermediateField

end ValuationSubring






end

end RamificationTheory
