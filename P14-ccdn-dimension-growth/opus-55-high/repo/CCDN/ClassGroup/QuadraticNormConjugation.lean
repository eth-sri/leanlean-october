/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Norm.Transitivity

/-! Explicit quadratic conjugation formulas. These identify the
two-element Galois group, the field norm, and its fixed field; they
connect the unit-norm obstruction with the involution formulation. -/

namespace CCDN
section

variable (F K : Type*) [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [Algebra.IsSeparable F K]

variable (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K)
include hd

/-- In a quadratic separable extension with a nontrivial automorphism `σ`, every automorphism is
either the identity or `σ`. -/
theorem quadratic_automorphism_eq_one_or
    (hσ : σ ≠ 1)
    (τ : K ≃ₐ[F] K) : τ = 1 ∨ τ = σ := by
  classical
  let : Algebra.IsQuadraticExtension F K := ⟨hd⟩
  have hc : Fintype.card (K ≃ₐ[F] K) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hd]
  by_cases hτ : τ = 1
  · grind
  · right
    have he : (Finset.univ.erase (1 : K ≃ₐ[F] K)).card ≤ 1 := by grind
    exact Finset.card_le_one.mp he _ (by grind) _ (by grind)

/-- Every automorphism of a quadratic separable extension is an involution. -/
theorem quadratic_automorphism_involutive
    :
    Function.Involutive σ := by
  let : Algebra.IsQuadraticExtension F K := ⟨hd⟩
  have hs : σ ^ 2 = 1 := by
    simpa only [IsGalois.card_aut_eq_finrank, hd] using
      (pow_card_eq_one' (x := σ))
  intro x
  simpa using
    congrArg (fun τ ↦ τ x) hs

/-- In a quadratic separable extension with nontrivial automorphism `σ`, the norm of `x` is
`x * σ x`. -/
theorem quadratic_norm_eq_mul_conjugate
    (hσ : σ ≠ 1) (x : K) :
    algebraMap F K (Algebra.norm F x) = x * σ x := by
  let : Algebra.IsQuadraticExtension F K := ⟨hd⟩
  rw [Algebra.norm_eq_prod_automorphisms]
  have hp := Fintype.prod_eq_mul (f := fun τ ↦ τ x)
    1 σ hσ.symm (fun τ hτ ↦
      False.elim ((quadratic_automorphism_eq_one_or F K hd σ hσ τ).elim hτ.1 hτ.2))
  simpa using hp

