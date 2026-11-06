/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Height.Box
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.ZMod.Basic
import CCDN.Determinant.PlaneMultiplicity
import CCDN.Plane.FiniteFieldPolynomialZeros

/-! Smooth affine residue classes and their simultaneous cardinality
bound. The elementary d*p^(ambient-1) bound suffices when the number of
chosen primes is absorbed by a small power of the box size. -/

namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- The nonsingular `𝔽_p`-points of the reduction modulo `p` of the affine hypersurface `f = 0`. -/
def SmoothAffineResidue {n : ℕ} (f : MvPolynomial (Fin n) ℤ) (p : ℕ) :=
  {a : Fin n → ZMod p //
    eval₂ (Int.castRingHom (ZMod p)) a f = 0 ∧
    ∃ j, eval a (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0}

instance {n : ℕ} (f : MvPolynomial (Fin n) ℤ) (p : ℕ) [NeZero p] :
    Fintype (SmoothAffineResidue f p) := by
  classical
  unfold SmoothAffineResidue
  infer_instance

theorem smoothAffineResidue_card_le {n p : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 1)) ℤ) :
    Fintype.card (SmoothAffineResidue f p) ≤ f.totalDegree * p ^ n := by
  let g := map (Int.castRingHom (ZMod p)) f
  by_cases hg : g = 0
  · have hempty : IsEmpty (SmoothAffineResidue f p) := by
      refine ⟨fun a => ?_⟩
      obtain ⟨j, hj⟩ := a.property.2
      grind
    let := hempty
    simp only [Fintype.card_of_isEmpty]
    omega
  · let φ : SmoothAffineResidue f p → {a : Fin (n + 1) → ZMod p // eval a g = 0} :=
      fun a => ⟨a.val, by simpa [g, eval_map] using a.property.1⟩
    have hcard := Fintype.card_le_of_injective φ (by
      intro a b h
      apply Subtype.ext
      grind)
    have hsz := finite_field_polynomial_zeros_mul_card g hg
    rw [Nat.card_eq_fintype_card, ZMod.card, Fintype.card_fin] at hsz
    have hdeg : g.totalDegree ≤ f.totalDegree := by
      change (map (Int.castRingHom (ZMod p)) f).totalDegree ≤ _
      rw [map_eq_eval₂Hom_C_comp]
      exact linear_eval₂_totalDegree_le _ X (fun j => le_of_eq (totalDegree_X j)) f
    have hbound := ((Nat.mul_le_mul_right p hcard).trans hsz).trans
      (Nat.mul_le_mul_right (p ^ (n + 1)) hdeg)
    rw [pow_succ, ← Nat.mul_assoc] at hbound
    exact le_of_mul_le_mul_right hbound (Fact.out : p.Prime).pos

section
variable {n : ℕ}

/-- A choice, for each prime `p` in `P`, of a nonsingular `𝔽_p`-point of `f mod p`. -/
def SmoothAffineResidueFamily (f : MvPolynomial (Fin n) ℤ) (P : Finset ℕ) :=
  (p : P) → SmoothAffineResidue f p.val

end

section
variable {n : ℕ} {f : MvPolynomial (Fin n) ℤ} {P : Finset ℕ} (r : SmoothAffineResidueFamily f P)

/-- The integer lift, with coordinates in `[0, p)`, of the residue point modulo `p` chosen by the
family `r` (and `0` for `p ∉ P`). -/
def smoothResidueIntegerLift
    : ℕ → IntPoint n :=
  fun p j => if hp : p ∈ P then ((r ⟨p, hp⟩).val j).val else 0

lemma smoothResidueIntegerLift_cast
    (p : P) [NeZero p.val] (j : Fin n) :
    (smoothResidueIntegerLift r p.val j : ZMod p.val) = (r p).val j := by
  simp only [smoothResidueIntegerLift, dite_eq_left p.property, Int.cast_natCast,
    ZMod.natCast_zmod_val]

/-- The reduction of `f` modulo `p ∈ P` vanishes at the lift of the residue point chosen by `r`. -/
theorem smoothResidueIntegerLift_zero
    (p : ℕ) [NeZero p] (hp : p ∈ P) :
    eval₂ (Int.castRingHom (ZMod p)) (fun j => (smoothResidueIntegerLift r p j : ZMod p)) f =
      0 := by
  simpa [smoothResidueIntegerLift_cast r ⟨p, hp⟩] using (r ⟨p, hp⟩).property.1

/-- The lift of the residue point chosen by `r` modulo `p ∈ P` is a nonsingular point of `f mod p`.
-/
theorem smoothResidueIntegerLift_smooth
    (p : ℕ) [NeZero p] (hp : p ∈ P) :
    ∃ j, eval (fun i => (smoothResidueIntegerLift r p i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0 := by
  simpa [smoothResidueIntegerLift_cast r ⟨p, hp⟩] using (r ⟨p, hp⟩).property.2

end

variable {n : ℕ} {f : MvPolynomial (Fin n) ℤ} (x : IntPoint n) (hxf : eval x f = 0) (P : Finset ℕ)

/-- The family of residue points obtained by reducing an integer zero `x` of `f` modulo each prime
in `P` at which it is nonsingular. -/
def smoothResidueFamilyOfPoint
    (hs : ∀ p ∈ P, ∃ j, eval (fun i => (x i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0) :
    SmoothAffineResidueFamily f P := fun p =>
  ⟨fun j => (x j : ZMod p.val), by
    constructor
    · have h := congrArg (Int.castRingHom (ZMod p.val)) hxf
      rwa [map_eval, map_zero, eval_map] at h
    · exact hs p.val p.property⟩

