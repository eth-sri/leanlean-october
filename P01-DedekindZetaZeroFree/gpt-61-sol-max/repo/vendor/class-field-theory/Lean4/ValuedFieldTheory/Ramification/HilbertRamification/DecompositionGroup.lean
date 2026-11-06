module

public import Mathlib

public import ValuedFieldTheory.Ramification.HilbertRamification.AbsoluteValueConjugacy
public import ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Decomposition-group restriction law

This file gives the three tower-intersection formulas in their common ambient
Galois group.  The decomposition-group statement is formulated for arbitrary
absolute values, including the archimedean case.  The inertia and ramification
statements use valuation subrings and therefore cover the nonarchimedean case
in which those groups are defined.
-/

noncomputable section

universe u v w

namespace HilbertRamification

open AlgebraicNumberTheory.Valuations
open RamificationTheory.HilbertRamification.ValuationSubring

variable (K : Type u) {L : Type w} [Field K] [Field L] [Algebra K L]

/-- The decomposition group of an absolute-value class.  Membership says that pullback by the
automorphism preserves the strict unit ball, equivalently the valuation
class, rather than requiring equality of chosen absolute-value representatives.
-/
def absoluteValueDecompositionGroup (w : AbsoluteValue L ℝ) :
    Subgroup (L ≃ₐ[K] L) where
  carrier := { σ | ∀ x : L, w (σ x) < 1 ↔ w x < 1 }
  one_mem' := by
    intro x
    rfl
  mul_mem' := by
    intro σ τ hσ hτ x
    exact (hσ (τ x)).trans (hτ x)
  inv_mem' := by
    intro σ hσ x
    have h := hσ (σ⁻¹ x)
    simpa using h.symm

@[simp] theorem mem_absoluteValueDecompositionGroup_iff
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) :
    σ ∈ absoluteValueDecompositionGroup K w ↔
      ∀ x : L, w (σ x) < 1 ↔ w x < 1 :=
  Iff.rfl

/-- Membership really is preservation of the absolute-value class: the
pullback absolute value is equivalent to the chosen representative. -/
theorem mem_absoluteValueDecompositionGroup_iff_equivalent
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) :
    σ ∈ absoluteValueDecompositionGroup K w ↔
      LubinTate.Valuations.EquivalentAbsoluteValues
        (w.comp (f := σ.toRingEquiv.toRingHom) σ.injective) w := by
  rw [LubinTate.Valuations.equivalentAbsoluteValues_iff_isEquiv,
    AbsoluteValue.isEquiv_iff_lt_one_iff]
  rfl

/-- The decomposition and inertia definition: on the normalized extension type,
the decomposition group is exactly the stabilizer of the chosen extension
under `w ↦ w ∘ σ`. -/
theorem mem_absoluteValueDecompositionGroup_iff_extensionConjugate_eq
    {K₀ : Type u} {L₀ : Type w} [Field K₀] [Field L₀] [Algebra K₀ L₀]
    (vK : AbsoluteValue K₀ ℝ) (hvK : vK.IsNontrivial)
    (vL : AbsoluteValueExtension vK L₀) (σ : L₀ ≃ₐ[K₀] L₀) :
    σ ∈ absoluteValueDecompositionGroup K₀ vL.1 ↔
      absoluteValueExtensionConjugate vK vL σ = vL := by
  rw [mem_absoluteValueDecompositionGroup_iff_equivalent]
  change
    LubinTate.Valuations.EquivalentAbsoluteValues
        (absoluteValueExtensionConjugate vK vL σ).1 vL.1 ↔ _
  constructor
  · apply equivalent_exactExtensions_eq <;> assumption
  · intro h
    rw [h]
    apply LubinTate.Valuations.equivalentAbsoluteValues_refl

section IntermediateField

variable {M : Type v} [Field M] [Algebra K M] [Algebra M L]
  [IsScalarTower K M L]











/-- The decomposition-group restriction law, decomposition-group membership form: scalar restriction
does not change the action on the chosen valuation of `L`. -/
theorem decompositionGroupRestriction_mem_absoluteValueDecompositionGroup_restrictScalars_iff
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[M] L) :
    RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars (K := K) (M := M) σ ∈
        absoluteValueDecompositionGroup K w ↔
      σ ∈ absoluteValueDecompositionGroup M w :=
  Iff.rfl


























end IntermediateField

namespace ValuationSubring

section NonarchimedeanIntermediateField

variable {M : Type v} [Field M] [Algebra K M] [Algebra M L]
  [IsScalarTower K M L]













































































end NonarchimedeanIntermediateField

end ValuationSubring

end HilbertRamification

end
