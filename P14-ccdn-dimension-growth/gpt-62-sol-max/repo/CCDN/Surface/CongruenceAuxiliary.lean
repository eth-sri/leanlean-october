/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.AffineCongruenceHeight
import CCDN.AuxiliaryPolynomial.StandardMonomialAuxiliary
import CCDN.AuxiliaryPolynomial.WeightedMonomialDeterminant
public import CCDN.Hilbert.PrincipalStandardMonomials
public import CCDN.AuxiliaryPolynomial.HypersurfaceRankProfile
import CCDN.Algebra.IntegerRationalIrreducibility
import CCDN.Surface.MonomialWeight

/-! The full standard-monomial prefix produces a proper integer auxiliary
on the entire bounded surface congruence class, with the sharp weighted
degree in the sole remaining numerical gap. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- The integer zeros of `f` in the box of radius `B` that are congruent to `a p` modulo `p`,
coordinatewise, for every `p ∈ P`. -/
def affineCongruencePoints {n : ℕ} (f : MvPolynomial (Fin n) ℤ)
    (B : ℝ) (P : Finset ℕ) (a : ℕ → IntPoint n) : Finset (IntPoint n) := by
  classical
  exact (integerBox n B).filter (fun x =>
    eval x f = 0 ∧ ∀ p ∈ P, ∀ j, (p : ℤ) ∣ x j - a p j)

/-- A point lies in `affineCongruencePoints f B P a` exactly when it lies in the box of radius
`B`, is a zero of `f` and is congruent to `a p` modulo every `p ∈ P`. -/
lemma mem_affineCongruencePoints {n : ℕ} {f : MvPolynomial (Fin n) ℤ}
    {B : ℝ} {P : Finset ℕ} {a : ℕ → IntPoint n} {x : IntPoint n} :
    x ∈ affineCongruencePoints f B P a ↔
      InBox x B ∧ eval x f = 0 ∧
        ∀ p ∈ P, ∀ j, (p : ℤ) ∣ x j - a p j := by
  simp [affineCongruencePoints, mem_filter, mem_integerBox]

/-- The bound `log s! + ((2/3) s √(2s/d) + (2d + 2) s) log B` for the logarithm of the absolute
value of a determinant formed by evaluating `s` standard monomials of a surface of degree `d`
at `s` integer points of the box of radius `B`. -/
def surfaceWeightedDeterminantUpper (d s : ℕ) (B : ℝ) : ℝ :=
  Real.log (s.factorial : ℝ) +
    ((2 / 3 : ℝ) * s * Real.sqrt (2 * s / (d : ℝ)) + (2 * d + 2) * s) * Real.log B

/-- All bounded integer zeros in specified smooth residue classes lie on
a proper auxiliary. The degree criterion is entirely numerical. -/
theorem exists_surface_congruence_auxiliary_of_gap
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : CoefficientHeightLE f H)
    {M : ℕ} (hM : f.totalDegree ≤ M)
    {B : ℝ} (hB : 1 ≤ B)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a : ℕ → IntPoint 3)
    (ha : ∀ p ∈ P, eval₂ (Int.castRingHom (ZMod p)) (fun j => (a p j : ZMod p)) f = 0)
    (hsmooth : ∀ p ∈ P, ∃ j, eval (fun i => (a p i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0)
    (hgap : let s := hypersurfaceRank 3 f.totalDegree M
      surfaceWeightedDeterminantUpper f.totalDegree s B <
        affineCongruenceDeterminantLower 1 f.totalDegree s H (∑ p ∈ P, Real.log p)) :
    ∃ g : MvPolynomial (Fin 3) ℤ, g ≠ 0 ∧
      ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) g ∧
      g.totalDegree ≤ M ∧ ∀ x ∈ affineCongruencePoints f B P a, eval x g = 0 := by
  classical
  let fQ := map (Int.castRingHom ℚ) f
  let S := standardMonomialPrefix (Ideal.span {fQ}) MonomialOrder.degLex M
  let e := (Fintype.equivFin S).symm
  let mon := Subtype.val ∘ e
  have hfQ : fQ ≠ 0 := (rational_irreducible_of_charZero_map f hir).ne_zero
  have hdQ : fQ.totalDegree = f.totalDegree := rational_map_totalDegree f
  have hMQ : fQ.totalDegree ≤ M := hdQ.symm ▸ hM
  have hc : Fintype.card S = hypersurfaceRank 3 f.totalDegree M := by
    rw [Fintype.card_coe, principal_standard_prefix_rank fQ hfQ hMQ, hdQ]
  have hN : 0 < Fintype.card S := hc ▸ hypersurface_rank_pos (r := 2) hM hd
  have hm j := (mem_standardMonomialPrefix _ _ _ _).mp (e j).property
  let X := affineCongruencePoints f B P a
  suffices ∃ g : MvPolynomial (Fin 3) ℤ, g ≠ 0 ∧ ¬ fQ ∣ map (Int.castRingHom ℚ) g ∧
      g.totalDegree ≤ M ∧ ∀ x : X, eval x.val g = 0 by
    obtain ⟨g, hg, hnd, hdeg, hzero⟩ := this
    exact ⟨g, hg, hnd, hdeg, fun x hx => hzero ⟨x, hx⟩⟩
  apply exists_standard_auxiliary_of_zero_determinants fQ mon
    (Subtype.val_injective.comp e.injective) (fun j => (hm j).1) (fun j => (hm j).2)
  intro b
  by_contra hne
  let y := Subtype.val ∘ b
  have hy i := mem_affineCongruencePoints.mp (b i).property
  have he := evaluationMatrix_eq_eval mon y
  have hlo := affine_congruence_determinant_log_lower_height hN f hir hd H hH hcoeff
    (fun j => monomial (mon j) 1) (fun j => (totalDegree_monomial_le _ _).trans (hm j).2)
    y (fun i => (hy i).2.1) (he ▸ hne) P a ⟨hP, ha, hsmooth, fun p hp i => (hy i).2.2 p hp⟩
  rw [he] at hlo
  have hupper := weighted_evaluation_det_log_bound mon y hB (fun i => (hy i).1) hne
  have hweight := surface_standard_monomial_weight fQ hfQ (hdQ.symm ▸ hd) hMQ
  have hsum : (∑ j, ((Finsupp.degree (mon j) : ℕ) : ℝ)) =
      ∑ j ∈ S, ((Finsupp.degree j : ℕ) : ℝ) := by
    rw [← Finset.sum_coe_sort S]
    exact e.sum_comp (fun j : S => ((Finsupp.degree j.val : ℕ) : ℝ))
  rw [hsum] at hupper
  have hw := mul_le_mul_of_nonneg_right hweight (Real.log_nonneg hB)
  rw [hdQ] at hw
  apply not_lt_of_ge (hlo.trans (hupper.trans (add_le_add_right hw _)))
  simpa only [surfaceWeightedDeterminantUpper, ← hc, Fintype.card_coe] using hgap

end
end CCDN
