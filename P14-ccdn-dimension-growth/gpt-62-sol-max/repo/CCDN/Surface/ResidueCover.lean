/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Surface.ResidueBoundary
import CCDN.Algebra.IntegerRationalIrreducibility
import CCDN.Surface.CurveCrossing
import CCDN.Surface.NonlinearCount
import Mathlib.Algebra.Order.Star.Real

/-! Counting the proper sections attached to the deletion edges of a residue window. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- Common scaled crossing bound, omitting the residue tuple count. -/
abbrev residueEdgeBudget (d : ℕ) (A B U X : ℝ) (W : Finset ℕ) : ℝ :=
  2 * d * A ^ 2 * (surfaceResidueLogBudget B W) ^ 2 * (U + 1) * X ^ 2

section

variable {f : MvPolynomial (Fin 3) ℤ} {A B U X : ℝ} {W : Finset ℕ}
  (F : SurfaceCongruenceFamily f B A) (hA : 0 ≤ A) (hB : 1 ≤ B)
  (hX : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) ≤ X)
  (hir : Irreducible (map (Int.castRingHom ℚ) f))
  (S : Finset (Ideal (CoordinatePolynomial 3)))
  (δ : Ideal (CoordinatePolynomial 3) → ℕ)
  (hS : ∀ I ∈ S, IsSurfaceCurve (map (Int.castRingHom ℚ) f) I (δ I))
  (R : Finset ℕ) (hRW : R ⊆ W) (hR : ∀ p ∈ R, p.Prime) (p : ℕ) (hp : p ∈ R)
  (hpU : (p : ℝ) ≤ U) (hq : (∏ q ∈ R, (q : ℝ)) ≤ X)
include f A B U X W F hA hB hX hir S δ hS R hRW hR p hp hpU hq

private theorem surface_residue_crossing_scaled_count
    (r : SmoothAffineResidueFamily f R) :
    (count (surfaceResidueCrossing F S R hR p r) B : ℝ) * (∏ q ∈ R, (q : ℝ)) ^ 2 ≤
      residueEdgeBudget f.totalDegree A B U X W := by
  let T := surfaceResidueLogBudget B W
  let q : ℝ := ∏ t ∈ R, (t : ℝ)
  let g := F.eraseAuxiliary hR p r
  let h := F.auxiliary R hR r
  have hT : 0 ≤ T := by dsimp [T, surfaceResidueLogBudget]; have := Real.log_nonneg hB; positivity
  have hX0 : 0 ≤ X := (by positivity : 0 ≤ B ^ (1 / Real.sqrt (f.totalDegree : ℝ))).trans hX
  have hqp : (∏ t ∈ R.erase p, (t : ℝ)) * p = q := prod_erase_mul R _ hp
  have hpar := mul_le_mul_of_nonneg_right (F.scaled_degree_le hA hB hX
    ((erase_subset p R).trans hRW) (fun t ht => hR t (mem_of_mem_erase ht))
    (r.restrict (erase_subset p R))) (Nat.cast_nonneg (α := ℝ) p)
  have hpar' : (g.totalDegree : ℝ) * q ≤ A * ((U + 1) * X) * T := by
    calc
      _ = (g.totalDegree : ℝ) * (∏ t ∈ R.erase p, (t : ℝ)) * p := by rw [mul_assoc, hqp]
      _ ≤ _ := hpar
      _ = A * (X * p + q) * T := by rw [← hqp]; ring
      _ ≤ _ := by
        gcongr
        change q ≤ X at hq
        nlinarith [mul_le_mul_of_nonneg_left hpU hX0]
  have hchild : (h.totalDegree : ℝ) * q ≤ A * (2 * X) * T := by
    refine (F.scaled_degree_le hA hB hX hRW hR r).trans ?_
    gcongr
    linarith
  have hq0 : 0 ≤ q := by positivity
  have hU : 0 ≤ U := (Nat.cast_nonneg _).trans hpU
  have hpair := mul_le_mul hpar' hchild (by positivity) (by positivity)
  have hc : (count (surfaceResidueCrossing F S R hR p r) B : ℝ) ≤
      (f.totalDegree : ℝ) * g.totalDegree * h.totalDegree := by
    exact_mod_cast (by simpa only [surfaceResidueCrossing, rational_map_totalDegree] using
      (surface_curve_crossing_count_le _ (map (Int.castRingHom ℚ) g) (map (Int.castRingHom ℚ) h)
        hir (F.proper _ _ _) S δ hS B) : _ ≤ f.totalDegree * g.totalDegree * h.totalDegree)
  change _ * q ^ 2 ≤ _
  dsimp only [residueEdgeBudget]
  linarith [mul_le_mul_of_nonneg_right hc (sq_nonneg q),
    mul_le_mul_of_nonneg_left hpair (Nat.cast_nonneg (α := ℝ) f.totalDegree)]

/-- Summing the smooth residue tuples cancels the square of their modulus. -/
private theorem surface_residue_edge_count_le :
    (count (⋃ r : SmoothAffineResidueFamily f R, surfaceResidueCrossing F S R hR p r) B : ℝ) ≤
      (f.totalDegree : ℝ) ^ R.card * residueEdgeBudget f.totalDegree A B U X W := by
  classical
  let (p : R) : NeZero p.val := ⟨(hR p.val p.property).ne_zero⟩
  let : Fintype (SmoothAffineResidueFamily f R) := Pi.instFintype
  let q : ℝ := ∏ p ∈ R, (p : ℝ)
  let C := residueEdgeBudget f.totalDegree A B U X W
  have hqpos : 0 < q := prod_pos (fun p hp => by exact_mod_cast (hR p hp).pos)
  have hU : 0 ≤ U := (Nat.cast_nonneg _).trans hpU
  have hC : 0 ≤ C := by positivity
  have hcard : (Fintype.card (SmoothAffineResidueFamily f R) : ℝ) ≤
      (f.totalDegree : ℝ) ^ R.card * q ^ 2 := by
    have hh := smoothAffineResidueFamily_card_le (n := 2) f R hR
    rw [Nat.card_eq_fintype_card] at hh
    simpa only [q, Nat.cast_mul, Nat.cast_pow, Nat.cast_prod] using (Nat.cast_le.mpr hh :
      (Fintype.card _ : ℝ) ≤ ((f.totalDegree ^ R.card * (∏ p ∈ R, p) ^ 2 : ℕ) : ℝ))
  have hscaled := count_biUnion_finset_mul_le (univ : Finset (SmoothAffineResidueFamily f R))
    (surfaceResidueCrossing F S R hR p) B (sq_nonneg q)
    (fun r _ => surface_residue_crossing_scaled_count F hA hB hX hir S δ hS R hRW hR p hp hpU hq r)
  simp at hscaled
  have hh := hscaled.trans (mul_le_mul_of_nonneg_right hcard hC)
  apply le_of_mul_le_mul_right _ (sq_pos_of_pos hqpos)
  exact hh.trans_eq (by ring)

end

/-- Sum the crossing bound over all deletion edges in the window. -/
theorem surface_residue_residual_count_le
    {f : MvPolynomial (Fin 3) ℤ} {A B U X : ℝ}
    (F : SurfaceCongruenceFamily f B A) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hd : 1 ≤ f.totalDegree) (hU : 0 ≤ U)
    (hX : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) ≤ X)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    (S : Finset (Ideal (CoordinatePolynomial 3)))
    (δ : Ideal (CoordinatePolynomial 3) → ℕ)
    (hS : ∀ I ∈ S, IsSurfaceCurve (map (Int.castRingHom ℚ) f) I (δ I))
    (W : Finset ℕ) (hW : ∀ p ∈ W, p.Prime) (hupper : ∀ p ∈ W, (p : ℝ) ≤ U)
    (hprod : ∀ R ⊆ W, R.card ≤ 18 → (∏ p ∈ R, (p : ℝ)) ≤ X) :
    (count (surfaceResidueResidualLocus F S W hW) B : ℝ) ≤
      (W.card : ℝ) * (2 * (f.totalDegree : ℝ)) ^ W.card *
        residueEdgeBudget f.totalDegree A B U X W := by
  let T := W.powerset.filter (fun R => R.card ≤ 18)
  let C := (f.totalDegree : ℝ) ^ W.card * residueEdgeBudget f.totalDegree A B U X W
  have hC : 0 ≤ C := by positivity
  have hdR : (1 : ℝ) ≤ f.totalDegree := by exact_mod_cast hd
  have hsubset (R : Finset ℕ) (hR : R ∈ T) :
      (count (surfaceResidueSubsetLocus F S W hW R) B : ℝ) ≤ W.card * C := by
    obtain ⟨hRW, hcard⟩ := mem_filter.mp hR
    have hs := mem_powerset.mp hRW
    let hp (q : ℕ) (hq : q ∈ R) := hW q (hs hq)
    have hc : (R.card : ℝ) ≤ W.card := by exact_mod_cast card_le_card hs
    simp only [surfaceResidueSubsetLocus, dite_eq_left hs]
    have hedge (p : ℕ) (hm : p ∈ R) :
        (count (⋃ r : SmoothAffineResidueFamily f R, surfaceResidueCrossing F S R hp p r) B : ℝ) ≤ C := by
      refine (surface_residue_edge_count_le F hA hB hX hir S δ hS R hs hp p hm
        (hupper p (hs hm)) (hprod R hs hcard)).trans ?_
      dsimp only [C]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hdR (card_le_card hs)) (by positivity)
    have hsum := count_biUnion_finset_mul_le R
      (fun p => ⋃ r : SmoothAffineResidueFamily f R, surfaceResidueCrossing F S R hp p r) B
      (K := 1) zero_le_one (by simpa using hedge)
    exact (by simpa using hsum : _ ≤ (R.card : ℝ) * C).trans (mul_le_mul_of_nonneg_right hc hC)
  have hT : (T.card : ℝ) ≤ (2 : ℝ) ^ W.card := by
    exact_mod_cast (card_le_card (filter_subset _ _)).trans_eq (card_powerset W)
  have hsum := count_biUnion_finset_mul_le T (surfaceResidueSubsetLocus F S W hW) B
    (K := 1) zero_le_one (by simpa using hsubset)
  unfold surfaceResidueResidualLocus
  calc
    _ ≤ T.card * (W.card * C) := by simpa only [mul_one] using hsum
    _ ≤ (2 : ℝ) ^ W.card * (W.card * C) := mul_le_mul_of_nonneg_right hT (by positivity)
    _ = _ := by rw [mul_pow]; dsimp only [C]; ring

end
end CCDN
