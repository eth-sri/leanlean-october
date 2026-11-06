/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Height.Box
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.ZMod.Basic
import CCDN.Determinant.PlaneMultiplicity
import CCDN.Plane.FiniteFieldPolynomialZeros

/-! Smooth affine residue classes and their simultaneous cardinality
bound. The elementary d*p^(ambient-1) bound suffices when the number of
chosen primes is absorbed by a small power of the box size. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

variable {n : ℕ}

/-- The nonsingular `𝔽_p`-points of the reduction modulo `p` of the affine hypersurface `f = 0`. -/
def SmoothAffineResidue  (f : CCDN.IntegerPolynomial n) (p : ℕ) :=
  {a : Fin n → ZMod p //
    eval₂ (Int.castRingHom (ZMod p)) a f = 0 ∧
    ∃ j, eval a (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0}

instance {n : ℕ} (f : CCDN.IntegerPolynomial n) (p : ℕ) [NeZero p] :
    Fintype (SmoothAffineResidue f p) := by
  classical
  unfold SmoothAffineResidue
  infer_instance

private theorem smoothAffineResidue_card_le {n p : ℕ} [Fact p.Prime]
    (f : CCDN.IntegerPolynomial (n + 1)) :
    Fintype.card (SmoothAffineResidue f p) ≤ f.totalDegree * p ^ n := by
  classical
  let g := map (Int.castRingHom (ZMod p)) f
  by_cases hg : g = 0
  · aesop (add simp [CCDN.SmoothAffineResidue])
  · let φ : SmoothAffineResidue f p → {a : Fin (n + 1) → ZMod p // eval a g = 0} :=
      fun a => ⟨a.val, by grind [eval_map]⟩
    have hφ : Function.Injective φ := by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun z : {a : Fin (n + 1) → ZMod p // eval a g = 0} => z.val) h
    have hcard := Fintype.card_le_of_injective φ hφ
    have hsz := finite_field_polynomial_zeros_mul_card g hg
    rw [Nat.card_eq_fintype_card, ZMod.card, Fintype.card_fin] at hsz
    have hdeg : g.totalDegree ≤ f.totalDegree := by
      grind [map_eq_eval₂Hom_C_comp, linear_eval₂_totalDegree_le, totalDegree_X]
    have hbound := ((Nat.mul_le_mul_right p hcard).trans hsz).trans
      (Nat.mul_le_mul_right (p ^ (n + 1)) hdeg)
    rw [pow_succ, ← Nat.mul_assoc] at hbound
    exact le_of_mul_le_mul_right hbound (Fact.out : p.Prime).pos

/-- A choice, for each prime `p` in `P`, of a nonsingular `𝔽_p`-point of `f mod p`. -/
def SmoothAffineResidueFamily  (f : CCDN.IntegerPolynomial n) (P : Finset ℕ) :=
  (p : P) → SmoothAffineResidue f p.val

/-- The number of families of nonsingular residue points of `f` modulo the primes in `P` is at most
`deg(f) ^ #P · (∏_{p ∈ P} p) ^ n`. -/
theorem smoothAffineResidueFamily_card_le 
    (f : CCDN.IntegerPolynomial (n + 1)) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    Nat.card (SmoothAffineResidueFamily f P) ≤
      f.totalDegree ^ P.card * (∏ p ∈ P, p) ^ n := by
  classical
  let (p : P) : Fact p.val.Prime := ⟨hP p.val p.property⟩
  let : Fintype (SmoothAffineResidueFamily f P) := Pi.instFintype
  rw [Nat.card_eq_fintype_card]
  change Fintype.card ((p : P) → SmoothAffineResidue f p.val) ≤ _
  rw [Fintype.card_pi]
  calc
    _ ≤ ∏ p : P, f.totalDegree * p.val ^ n :=
      prod_le_prod (fun p _ => smoothAffineResidue_card_le f)
    _ = f.totalDegree ^ P.card * (∏ p : P, p.val) ^ n := by
      simp_all [prod_mul_distrib, prod_const,   Finset.prod_pow]
    _ = _ := by grind [Finset.prod_coe_sort]

variable {n : ℕ} {f : CCDN.IntegerPolynomial n}

/-- The integer lift, with coordinates in `[0, p)`, of the residue point modulo `p` chosen by the
family `r` (and `0` for `p ∉ P`). -/
def smoothResidueIntegerLift 
    {P : Finset ℕ} (r : SmoothAffineResidueFamily f P) : ℕ → IntPoint n :=
  fun p j => if hp : p ∈ P then ((r ⟨p, hp⟩).val j).val else 0

private lemma smoothResidueIntegerLift_cast 
    {P : Finset ℕ} (r : SmoothAffineResidueFamily f P) (p : P) [NeZero p.val] (j : Fin n) :
    (smoothResidueIntegerLift r p.val j : ZMod p.val) = (r p).val j := by
  simp_all [   smoothResidueIntegerLift]

/-- The reduction of `f` modulo `p ∈ P` vanishes at the lift of the residue point chosen by `r`. -/
theorem smoothResidueIntegerLift_zero 
    {P : Finset ℕ} (r : SmoothAffineResidueFamily f P) (p : ℕ) [NeZero p] (hp : p ∈ P) :
    eval₂ (Int.castRingHom (ZMod p)) (fun j => (smoothResidueIntegerLift r p j : ZMod p)) f =
      0 := by
  simpa only [smoothResidueIntegerLift_cast r ⟨p, hp⟩] using (r ⟨p, hp⟩).property.1

/-- The lift of the residue point chosen by `r` modulo `p ∈ P` is a nonsingular point of `f mod p`.
-/
theorem smoothResidueIntegerLift_smooth 
    {P : Finset ℕ} (r : SmoothAffineResidueFamily f P) (p : ℕ) [NeZero p] (hp : p ∈ P) :
    ∃ j, eval (fun i => (smoothResidueIntegerLift r p i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0 := by
  simpa only [smoothResidueIntegerLift_cast r ⟨p, hp⟩] using (r ⟨p, hp⟩).property.2

variable (x : IntPoint n) (hxf : eval x f = 0) (P : Finset ℕ) (hs : ∀ p ∈ P, ∃ j, eval (fun i => (x i : ZMod p)) (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0)

/-- The family of residue points obtained by reducing an integer zero `x` of `f` modulo each prime
in `P` at which it is nonsingular. -/
def smoothResidueFamilyOfPoint 
     :
    SmoothAffineResidueFamily f P := fun p =>
  ⟨fun j => (x j : ZMod p.val), by
    constructor
    · have h := congrArg (Int.castRingHom (ZMod p.val)) hxf
      rw [map_eval, map_zero, eval_map] at h
      exact h
    · exact hs p.val p.property⟩

/-- An integer zero `x` of `f` is congruent modulo each `p ∈ P` to the integer lift of its own
residue family. -/
theorem smoothResidueFamilyOfPoint_congruence 
    
    (p : ℕ) [NeZero p] (hp : p ∈ P) (j : Fin n) :
    ↑p ∣ x j - smoothResidueIntegerLift (smoothResidueFamilyOfPoint x hxf P hs) p j := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  rw [Int.cast_sub, smoothResidueIntegerLift_cast _ ⟨p, hp⟩]
  exact sub_self _

end
end CCDN
