/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Norm.Transitivity

/-! Explicit quadratic conjugation formulas. These identify the
two-element Galois group, the field norm, and its fixed field; they
connect the unit-norm obstruction with the involution formulation. -/

public section
namespace CCDN

variable (F K : Type*) [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [Algebra.IsSeparable F K]

variable (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K)

include hd in
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
  · exact Or.inl hτ
  · right
    have he : (Finset.univ.erase (1 : K ≃ₐ[F] K)).card ≤ 1 := by
      simp_all
    exact Finset.card_le_one.mp he _ (by simp [hτ]) _ (by simp [hσ])

include hd in
/-- Every automorphism of a quadratic separable extension is an involution. -/
theorem quadratic_automorphism_involutive
     :
    Function.Involutive σ := by
  let : Algebra.IsQuadraticExtension F K := ⟨hd⟩
  have hs : σ ^ 2 = 1 := by
    grind [IsGalois.card_aut_eq_finrank, pow_card_eq_one']
  intro x
  simpa only [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply] using
    congrArg (fun τ : K ≃ₐ[F] K ↦ τ x) hs

include hd in
/-- In a quadratic separable extension with nontrivial automorphism `σ`, the norm of `x` is
`x * σ x`. -/
theorem quadratic_norm_eq_mul_conjugate
     (hσ : σ ≠ 1) (x : K) :
    algebraMap F K (Algebra.norm F x) = x * σ x := by
  classical
  let : Algebra.IsQuadraticExtension F K := ⟨hd⟩
  rw [Algebra.norm_eq_prod_automorphisms]
  exact have hp :=
    Fintype.prod_eq_mul 1 σ (Ne.symm hσ) fun τ hτ =>
      False.elim (Or.elim (quadratic_automorphism_eq_one_or F K hd σ hσ τ) hτ.left hτ.right);
  hp

end CCDN
