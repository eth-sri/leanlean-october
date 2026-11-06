module

public import Mathlib

public import ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

namespace ValuationTheory

/-!
# Henselian discretely valued fields

This file contains the lightweight package for a discretely valued field whose
valuation ring is Henselian at its maximal ideal.
-/

noncomputable section

universe u v

namespace DiscreteValuationField

/-- The idempotent polynomial `X^2 - X` is monic in every nontrivial
coefficient ring. -/
theorem idempotentPolynomial_monic
    {R : Type*} [CommRing R] [Nontrivial R] :
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial R).Monic := by
  apply Polynomial.monic_X_pow_sub <;> aesop

section
variable {R : Type*} [CommRing R] {I : Ideal R} (a0 : R)
    (ha0 : IsIdempotentElem (Ideal.Quotient.mk I a0))
include R I a0 ha0
/-- A quotient idempotent is an approximate root of `X^2 - X`. -/
theorem idempotentPolynomial_eval_mem_of_quotient_idempotent
      :
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial R).eval a0 ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change
    Ideal.Quotient.mk I
      ((Polynomial.X ^ 2 - Polynomial.X : Polynomial R).eval a0) = 0
  simpa [pow_two] using sub_eq_zero.mpr ha0.eq

/-- At a quotient idempotent, the derivative of `X^2 - X` is a unit in the
quotient. -/
theorem idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotent
      :
    IsUnit
      (Ideal.Quotient.mk I
        ((Polynomial.X ^ 2 - Polynomial.X : Polynomial R).derivative.eval a0)) := by
  rw [isUnit_iff_exists]
  refine
    ⟨Ideal.Quotient.mk I
      ((Polynomial.X ^ 2 - Polynomial.X : Polynomial R).derivative.eval a0),
      ?_, ?_⟩
  · simp [pow_two]
    calc
      (Ideal.Quotient.mk I a0 + Ideal.Quotient.mk I a0 - 1) *
          (Ideal.Quotient.mk I a0 + Ideal.Quotient.mk I a0 - 1) =
        1 + (4 * (Ideal.Quotient.mk I a0 * Ideal.Quotient.mk I a0) -
          4 * Ideal.Quotient.mk I a0) := by
          ring
      _ = 1 := by
          rw [ha0.eq]
          ring
  · simp [pow_two]
    calc
      (Ideal.Quotient.mk I a0 + Ideal.Quotient.mk I a0 - 1) *
          (Ideal.Quotient.mk I a0 + Ideal.Quotient.mk I a0 - 1) =
        1 + (4 * (Ideal.Quotient.mk I a0 * Ideal.Quotient.mk I a0) -
          4 * Ideal.Quotient.mk I a0) := by
          ring
      _ = 1 := by
          rw [ha0.eq]
          ring
end


/-- Idempotents lift along a surjective ring map whose kernel is a Henselian
ideal.

This is the `X^2 - X` simple-root form of Hensel's lemma.  At an idempotent,
the derivative `2X - 1` is a unit because its square is `1`. -/
theorem exists_idempotent_lift_of_surjective_henselianRing_ker
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f)
    [HenselianRing R (RingHom.ker f)]
    (e : S) (he : IsIdempotentElem e) :
    ∃ e' : R, IsIdempotentElem e' ∧ f e' = e := by
  cases subsingleton_or_nontrivial R with
  | inl hR =>
      have hS : Subsingleton S := by
        constructor
        intro x y
        rcases hf x with ⟨a, rfl⟩
        rcases hf y with ⟨b, rfl⟩
        exact congrArg f (Subsingleton.elim a b)
      exact ⟨0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  | inr hR =>
      let  := hR
      rcases hf e with ⟨a0, ha0⟩
      let p : Polynomial R := Polynomial.X ^ 2 - Polynomial.X
      have hpmonic : p.Monic := by
        dsimp [p]
        exact idempotentPolynomial_monic
      have ha0_quotient :
          IsIdempotentElem
            (Ideal.Quotient.mk (RingHom.ker f) a0) := by
        rw [IsIdempotentElem]
        rw [← map_mul, Ideal.Quotient.eq]
        rw [RingHom.mem_ker]
        simp [ha0, he.eq]
      have hroot : p.eval a0 ∈ RingHom.ker f := by
        apply idempotentPolynomial_eval_mem_of_quotient_idempotent <;> assumption
      have hsimple :
          IsUnit
            (Ideal.Quotient.mk (RingHom.ker f) (p.derivative.eval a0)) := by
        apply idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotent <;> assumption
      rcases HenselianRing.is_henselian p hpmonic a0 hroot hsimple with
        ⟨a, haroot, hacongr⟩
      refine ⟨a, ?_, ?_⟩
      · change a * a = a
        exact sub_eq_zero.mp (by simpa [p, pow_two] using haroot)
      · have hsub : f (a - a0) = 0 := RingHom.mem_ker.mp hacongr
        rw [map_sub, ha0, sub_eq_zero] at hsub
        exact hsub





















































/-- A Henselian discretely valued field. -/
structure HenselianDVF (K : Type u) [Field K] extends DVF.{u, v} K where
  /-- The valuation ring is Henselian along its maximal ideal. -/
  [instHenselian : HenselianRing toDVF.valuationSubring toDVF.maximalIdeal]

attribute [instance] HenselianDVF.instHenselian

namespace HenselianDVF

variable {K : Type u} [Field K]

section
variable (F : HenselianDVF.{u, v} K)
include F
/-- Introduces the abbreviation `valuationSubring`. -/
abbrev valuationSubring    :=
  F.toDVF.valuationSubring

/-- Introduces the abbreviation `maximalIdeal`. -/
abbrev maximalIdeal   : Ideal F.valuationSubring :=
  F.toDVF.maximalIdeal

/-- Introduces the abbreviation `residueField`. -/
abbrev residueField    :=
  F.toDVF.residueField

/-- Introduces the abbreviation `residueMap`. -/
abbrev residueMap   :
    RingHom F.valuationSubring F.residueField :=
  F.toDVF.residueMap






























/-- The valuation subring of the henselian model is a discrete valuation ring. -/
def valuationSubring_isDiscreteValuationRing    :=
  F.toDVF.valuationSubring_isDiscreteValuationRing

/-- The valuation subring of the henselian discrete valuation field is henselian. -/
theorem henselianRing   :
    HenselianRing F.valuationSubring F.maximalIdeal := by
  change HenselianRing F.toDVF.valuationSubring F.toDVF.maximalIdeal
  infer_instance

/-- The maximal ideal of a Henselian DVF valuation ring is nonzero. -/
theorem maximalIdeal_ne_bot   :
    F.maximalIdeal ≠ ⊥ :=
  F.toDVF.maximalIdeal_ne_bot

/-- Hensel's lemma in the simple-root form used by mathlib. -/
theorem exists_lift_root_simple  
    (f : Polynomial F.valuationSubring) (hf : f.Monic) (a0 : F.valuationSubring)
    (hroot : f.eval a0 ∈ F.maximalIdeal)
    (hsimple : IsUnit (Ideal.Quotient.mk F.maximalIdeal (f.derivative.eval a0))) :
    ∃ a : F.valuationSubring, f.IsRoot a ∧ a - a0 ∈ F.maximalIdeal :=
  HenselianRing.is_henselian f hf a0 hroot hsimple
end


end HenselianDVF

end DiscreteValuationField

end

end ValuationTheory
