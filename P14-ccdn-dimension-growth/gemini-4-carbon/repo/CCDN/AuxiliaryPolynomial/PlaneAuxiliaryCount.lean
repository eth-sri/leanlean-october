/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousChart
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.AuxiliaryPolynomial.PlaneBadPrimes
import CCDN.ForMathlib.MvPolynomial

/-! Distinct-point bounds obtained from the auxiliary polynomials and
Bézout. The sharp finite-field estimate remains an explicit hypothesis. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Mapping an integer polynomial to `ℚ` preserves its total degree. -/
lemma rational_map_totalDegree {σ : Type*} (f : MvPolynomial σ ℤ) :
    (MvPolynomial.map (Int.castRingHom ℚ) f).totalDegree = f.totalDegree :=
    totalDegree_map_of_injective Int.cast_injective _

/-- If the image of an integer polynomial in a field `F` of characteristic zero is irreducible,
then its image over `ℚ` is irreducible. -/
lemma rational_irreducible_of_charZero_map {F σ : Type*} [Field F] [CharZero F]
    (f : MvPolynomial σ ℤ) (hf : Irreducible (MvPolynomial.map (Int.castRingHom F) f)) :
    Irreducible (MvPolynomial.map (Int.castRingHom ℚ) f) := by
  apply mvPolynomial_irreducible_of_field_map (algebraMap ℚ F)
  rw [map_map]
  have he : (algebraMap ℚ F).comp (Int.castRingHom ℚ) = Int.castRingHom F := by ext; simp
  rw [he]
  exact hf

/-- Enumerating the integer zeros transfers finite-family bounds to
the counting interface, including empty point sets. -/
lemma integer_zero_count_le_of_family_bound {n : ℕ} (f : MvPolynomial (Fin n) ℤ)
    (B R : ℝ)
    (hbound : ∀ (t : ℕ) (z : Fin t → Fin n → ℤ), Function.Injective z →
      (∀ i, eval (z i) f = 0) → (∀ i, InBox (z i) B) → (t : ℝ) ≤ R) :
    (count (zeroLocus (MvPolynomial.map (Int.castRingHom ℚ) f)) B : ℝ) ≤ R := by
  classical
  let S := integralPoints (zeroLocus (MvPolynomial.map (Int.castRingHom ℚ) f)) B
  let e := (Fintype.equivFin S).symm
  let z : Fin (Fintype.card S) → Fin n → ℤ := fun i => (e i).val
  have hinj : Function.Injective z := Subtype.val_injective.comp e.injective
  have hzero : ∀ i, eval (z i) f = 0 := by
    intro i
    apply Int.cast_injective (α := ℚ)
    have h := (mem_integralPoints.mp (e i).property).2
    change eval (fun j => (z i j : ℚ)) (MvPolynomial.map (Int.castRingHom ℚ) f) = 0 at h
    change (Int.castRingHom ℚ) (eval (z i) f) = 0
    rw [map_eval]
    exact h
  have hbox : ∀ i, InBox (z i) B := fun i => (mem_integralPoints.mp (e i).property).1
  have h := hbound _ z hinj hzero hbox
  simpa only [Fintype.card_coe, S, count] using h

end
end CCDN
