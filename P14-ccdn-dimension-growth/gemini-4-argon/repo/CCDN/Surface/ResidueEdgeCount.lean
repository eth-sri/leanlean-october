/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Surface.ResidueBoundary
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.Surface.CurveCrossing
import CCDN.Surface.NonlinearCount
import Mathlib.Algebra.Order.Star.Real

/-! Counting the proper sections attached to one residue-subset
edge, including the sum over all smooth residue tuples. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

open Classical in
/-- For a congruence family `F`, a set `R` of primes, a prime `p` and smooth residues `r`
modulo `R`, the rational points on curves `I ∈ S` whose ideal contains the auxiliary of
`R.erase p` but not the one of `R`, and at which the latter auxiliary vanishes. -/
def surfaceResidueCrossing {f : MvPolynomial (Fin 3) ℤ} {A B : ℝ}
    (F : SurfaceCongruenceFamily f B A)
    (S : Finset (Ideal (CoordinatePolynomial 3)))
    (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime) (p : ℕ)
    (r : SmoothAffineResidueFamily f R) : Set (RatPoint 3) :=
  let g := map (Int.castRingHom ℚ)
    (F.auxiliary (R.erase p) (fun q hq => hR q (mem_of_mem_erase hq))
      (r.restrict (erase_subset p R)))
  let h := map (Int.castRingHom ℚ) (F.auxiliary R hR r)
  ⋃ I ∈ S.filter (fun I => g ∈ I ∧ h ∉ I), idealZeroLocus I ∩ zeroLocus h

/-- Summing all smooth residue tuples cancels the square of the
modulus. Only d to the number of selected primes remains. -/
theorem surface_residue_edge_count_le
    {f : MvPolynomial (Fin 3) ℤ} {A B L X : ℝ}
    (F : SurfaceCongruenceFamily f B A) (hA : 0 ≤ A) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hX0 : 0 ≤ X) (hX : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) ≤ X)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    (S : Finset (Ideal (CoordinatePolynomial 3)))
    (δ : Ideal (CoordinatePolynomial 3) → ℕ)
    (hS : ∀ I ∈ S, IsSurfaceCurve (map (Int.castRingHom ℚ) f) I (δ I))
    (R : Finset ℕ) (hRW : R ⊆ congruencePrimeWindow L)
    (hR : ∀ p ∈ R, p.Prime) (p : ℕ) (hp : p ∈ R)
    (hq : (∏ q ∈ R, (q : ℝ)) ≤ scalingPrimeRatio * L * X) :
    (count (⋃ r : SmoothAffineResidueFamily f R, surfaceResidueCrossing F S R hR p r) B : ℝ) ≤
      2 * (f.totalDegree : ℝ) ^ (R.card + 1) * A ^ 2 *
        (surfaceResidueLogBudget B L) ^ 2 * (scalingPrimeRatio * L + 1) ^ 2 * X ^ 2 := by
  classical
  have hscaled (R' : Finset ℕ) (hR'W : R' ⊆ congruencePrimeWindow L)
      (hR' : ∀ t ∈ R', t.Prime) (r' : SmoothAffineResidueFamily f R') :
      ((F.auxiliary R' hR' r').totalDegree : ℝ) * (∏ t ∈ R', (t : ℝ)) ≤
        A * (X + ∏ t ∈ R', (t : ℝ)) * surfaceResidueLogBudget B L := by
    have hlog : (∑ t ∈ R', Real.log t) ≤ (Real.log 4 + 4) * scalingPrimeRatio * L :=
      (sum_le_sum_of_subset_of_nonneg hR'W fun t _ _ => Real.log_natCast_nonneg t).trans
        (congruencePrimeWindow_log_upper hL)
    have hq' : 0 < ∏ t ∈ R', (t : ℝ) := prod_pos fun t ht => mod_cast (hR' t ht).pos
    have hd := F.degree_le R' hR' r'
    rw [exp_sum_log_primes R' hR'] at hd
    have hh := mul_le_mul_of_nonneg_right hd hq'.le
    rw [show A * (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) / (∏ t ∈ R', (t : ℝ)) + 1) *
        (1 + Real.log B + ∑ t ∈ R', Real.log t) * (∏ t ∈ R', (t : ℝ)) =
      A * (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) + ∏ t ∈ R', (t : ℝ)) *
        (1 + Real.log B + ∑ t ∈ R', Real.log t) by field_simp] at hh
    have hlogB := Real.log_nonneg hB
    have hQ : 0 ≤ ∑ t ∈ R', Real.log t := sum_nonneg fun t _ => Real.log_natCast_nonneg t
    exact hh.trans (mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hA)
      (by dsimp only [surfaceResidueLogBudget]; linarith) (by positivity) (by positivity))
  let (p : R) : NeZero p.val := ⟨(hR p.val p.property).ne_zero⟩
  let : Fintype (SmoothAffineResidueFamily f R) := Pi.instFintype
  let U := scalingPrimeRatio * L
  let T := surfaceResidueLogBudget B L
  let q : ℝ := ∏ p ∈ R, (p : ℝ)
  let C : ℝ := 2 * f.totalDegree * A ^ 2 * T ^ 2 * (U + 1) ^ 2 * X ^ 2
  have hqpos : 0 < q := prod_pos fun p hp => mod_cast (hR p hp).pos
  have hU : 0 ≤ U := by dsimp [U]; have := scalingPrimeRatio_one_le; positivity
  have hT : 0 ≤ T := by
    dsimp [T, surfaceResidueLogBudget]
    have := scalingPrimeRatio_one_le
    have := Real.log_nonneg hB
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpU : (p : ℝ) ≤ U := ((mem_congruencePrimeWindow hL).mp (hRW hp)).2.2
  have hqp : (∏ t ∈ R.erase p, (t : ℝ)) * p = q := prod_erase_mul R _ hp
  have hpoint (r : SmoothAffineResidueFamily f R) :
      (count (surfaceResidueCrossing F S R hR p r) B : ℝ) * q ^ 2 ≤ C := by
    let g := F.auxiliary (R.erase p) (fun t ht => hR t (mem_of_mem_erase ht))
      (r.restrict (erase_subset p R))
    let h := F.auxiliary R hR r
    have hpar := hscaled (R.erase p) ((erase_subset p R).trans hRW)
      (fun t ht => hR t (mem_of_mem_erase ht)) (r.restrict (erase_subset p R))
    have hchild : (h.totalDegree : ℝ) * q ≤ A * ((U + 1) * X) * T :=
      (hscaled R hRW hR r).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (show X + q ≤ (U + 1) * X by change q ≤ U * X at hq; linarith) hA) hT)
    have hpar' : (g.totalDegree : ℝ) * q ≤ A * (2 * (U + 1) * X) * T := by
      have hh := mul_le_mul_of_nonneg_right hpar (Nat.cast_nonneg (α := ℝ) p)
      have hh' : (g.totalDegree : ℝ) * q ≤ A * (X * p + q) * T := by
        calc (g.totalDegree : ℝ) * q
          _ = (g.totalDegree : ℝ) * (∏ t ∈ R.erase p, (t : ℝ)) * p := by rw [mul_assoc, hqp]
          _ ≤ _ := hh
          _ = A * (X * p + q) * T := by dsimp [T]; rw [← hqp]; ring
      exact hh'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (show X * p + q ≤ 2 * (U + 1) * X by
          change q ≤ U * X at hq; nlinarith [mul_le_mul_of_nonneg_left hpU hX0]) hA) hT)
    have hpair := mul_le_mul hpar' hchild (by positivity) (by positivity)
    have hh := surface_curve_crossing_count_le (map (Int.castRingHom ℚ) f)
      (map (Int.castRingHom ℚ) g) (map (Int.castRingHom ℚ) h) hir
      (F.proper _ _ _) (S.filter fun I => map (Int.castRingHom ℚ) g ∈ I) δ
      (fun I hI => ⟨hS I (mem_filter.mp hI).1, (mem_filter.mp hI).2⟩) B
    rw [show (S.filter fun I => map (Int.castRingHom ℚ) g ∈ I).filter
        (fun I => map (Int.castRingHom ℚ) h ∉ I) =
      S.filter (fun I => map (Int.castRingHom ℚ) g ∈ I ∧ map (Int.castRingHom ℚ) h ∉ I) by
        ext I; simp only [mem_filter]; tauto] at hh
    change count (surfaceResidueCrossing F S R hR p r) B ≤ _ at hh
    have hcount : (count (surfaceResidueCrossing F S R hR p r) B : ℝ) ≤
        (f.totalDegree : ℝ) * g.totalDegree * h.totalDegree := by
      exact_mod_cast (by simpa only [rational_map_totalDegree] using hh :
        count (surfaceResidueCrossing F S R hR p r) B ≤
          f.totalDegree * g.totalDegree * h.totalDegree)
    nlinarith [mul_le_mul_of_nonneg_right hcount (sq_nonneg q),
      mul_le_mul_of_nonneg_left hpair (Nat.cast_nonneg (α := ℝ) f.totalDegree)]
  have hcard : (Fintype.card (SmoothAffineResidueFamily f R) : ℝ) ≤
      (f.totalDegree : ℝ) ^ R.card * q ^ 2 := by
    have hh := smoothAffineResidueFamily_card_le (n := 2) f R hR
    rw [Nat.card_eq_fintype_card] at hh
    simpa only [q, Nat.cast_mul, Nat.cast_pow, Nat.cast_prod] using
      (by exact_mod_cast hh : (Fintype.card (SmoothAffineResidueFamily f R) : ℝ) ≤
        ((f.totalDegree ^ R.card * (∏ p ∈ R, p) ^ 2 : ℕ) : ℝ))
  have hunion : (count (⋃ r : SmoothAffineResidueFamily f R,
      surfaceResidueCrossing F S R hR p r) B : ℝ) ≤
      ∑ r : SmoothAffineResidueFamily f R, (count (surfaceResidueCrossing F S R hR p r) B : ℝ) := by
    have hh := count_biUnion_finset_le (univ : Finset (SmoothAffineResidueFamily f R))
      (fun r => surfaceResidueCrossing F S R hR p r) B
    exact_mod_cast (show count (⋃ r : SmoothAffineResidueFamily f R,
        surfaceResidueCrossing F S R hR p r) B ≤
        ∑ r : SmoothAffineResidueFamily f R, count (surfaceResidueCrossing F S R hR p r) B by
      simpa only [Finset.mem_univ, Set.iUnion_true] using hh)
  refine le_of_mul_le_mul_right ?_ (sq_pos_of_pos hqpos)
  calc (count (⋃ r : SmoothAffineResidueFamily f R, surfaceResidueCrossing F S R hR p r) B : ℝ) *
      q ^ 2
    _ ≤ (∑ r : SmoothAffineResidueFamily f R,
        (count (surfaceResidueCrossing F S R hR p r) B : ℝ)) * q ^ 2 :=
      mul_le_mul_of_nonneg_right hunion (sq_nonneg q)
    _ = ∑ r : SmoothAffineResidueFamily f R,
        (count (surfaceResidueCrossing F S R hR p r) B : ℝ) * q ^ 2 := sum_mul _ _ _
    _ ≤ ∑ _r : SmoothAffineResidueFamily f R, C := sum_le_sum fun r _ => hpoint r
    _ = (Fintype.card (SmoothAffineResidueFamily f R) : ℝ) * C := by simp
    _ ≤ ((f.totalDegree : ℝ) ^ R.card * q ^ 2) * C := mul_le_mul_of_nonneg_right hcard hC
    _ = _ := by dsimp only [C, U, T]; rw [pow_succ]; ring

end
end CCDN
