module

public import Mathlib

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Polynomial Chinese remainder equivalence

This is the algebraic core of tensor-product decompositions.  A squarefree factorization
of the base-changed primitive polynomial gives the canonical product of its
simple factor algebras.
-/

noncomputable section

namespace ValuationTheory
namespace Completion

universe u v

open scoped Polynomial
open Function

/-- The Chinese remainder ring equivalence is an algebra equivalence over
any coefficient ring acting on the ambient commutative ring. -/
noncomputable def quotientInfAlgEquivPiQuotient
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type*} [Finite ι]
    (I : ι → Ideal A) (hI : Pairwise (IsCoprime on I)) :
    (A ⧸ ⨅ i, I i) ≃ₐ[R] ∀ i, A ⧸ I i where
  __ := Ideal.quotientInfRingEquivPiQuotient I hI
  commutes' r := by
    ext i
    rfl

section
variable {F : Type u} [Field F] {ι : Type v} [Fintype ι]
    (f : ι → F[X])
    (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j))
include F ι f hf
/-- Chinese remainder equivalence for a finite family of pairwise coprime
polynomials.  It is canonical: every polynomial class is sent to the family
of the same class modulo each factor. -/
noncomputable def adjoinRootProdEquivPi
      :
    AdjoinRoot (∏ i, f i) ≃ₐ[F] ∀ i, AdjoinRoot (f i) := by
  let I  := fun i => Ideal.span ({f i} : Set F[X])
  have hI : Pairwise (IsCoprime on I) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff (f i) (f j)).2
      (hf i j hij)
  have hInf : Ideal.span ({∏ i, f i} : Set F[X]) = ⨅ i, I i := by
    symm
    exact Ideal.iInf_span_singleton hf
  exact
    (Ideal.quotientEquivAlgOfEq F hInf).trans
      (quotientInfAlgEquivPiQuotient I hI)

/-- The product decomposition of an adjoined-root algebra evaluates
representatives coordinatewise. -/
@[simp]
theorem adjoinRootProdEquivPi_mk
     
    (g : F[X]) (i : ι) :
    adjoinRootProdEquivPi f hf (AdjoinRoot.mk (∏ i, f i) g) i =
      AdjoinRoot.mk (f i) g := by
  rfl
end


end Completion
end ValuationTheory

end
