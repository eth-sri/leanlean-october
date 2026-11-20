/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.ProjectiveHypersurfaceResidueDeterminant
import CCDN.Algebra.CharZeroOrGT
import CCDN.Algebra.HomogeneousChartIrreducible
import CCDN.Determinant.PlaneMultiplicitySmooth
import CCDN.ForMathlib.MvPolynomialDerivative
import CCDN.Hilbert.CompleteIntersectionGridBound
import Mathlib.RingTheory.SimpleRing.Principal

/-!
The singular multiplicity correction for projective hypersurfaces.
Chart coordinates inject each selected residue class into an affine
singular locus, whose codimension-two point bound is proved by interpolation.

The singular points of an irreducible hypersurface satisfy a
coefficient-uniform codimension-two finite-field bound.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A nonzero partial derivative cuts the irreducible hypersurface
properly. Fixed-degree finite-field interpolation bounds all its singular points. -/
private theorem hypersurface_singular_points_card_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n p : ℕ} [Fact p.Prime] (f : MvPolynomial (Fin (n + 2)) (ZMod p))
    (hf : Irreducible f) (hpos : 0 < f.totalDegree) (hchar : f.totalDegree < p)
    (z : ι → Fin (n + 2) → ZMod p) (hz : Function.Injective z)
    (hzf : ∀ i, eval (z i) f = 0) (hzsing : ∀ i j, eval (z i) (pderiv j f) = 0) :
    Fintype.card ι ≤ (n + 2) ^ n * f.totalDegree * (f.totalDegree - 1) * p ^ n := by
  obtain ⟨j, hj⟩ := exists_pderiv_ne_zero hpos (CharZeroOrGT.of_charP hchar)
  have hdeg := pderiv_totalDegree_le f j
  have hnd := not_dvd_pderiv_of_pderiv_ne_zero hj
  have hdegrees : f.totalDegree + (pderiv j f).totalDegree ≤
      (n + 2) * (Finset.univ : Finset (ZMod p)).card.pred := by
    simp only [Finset.card_univ, ZMod.card, Nat.pred_eq_sub_one]
    exact (show f.totalDegree + (pderiv j f).totalDegree ≤ 2 * (p - 1) by omega).trans
      (Nat.mul_le_mul_right _ (by omega))
  have h := proper_intersection_grid_card_le_mul f (pderiv j f) hf.prime hnd Finset.univ
    z hz (fun _ _ => Finset.mem_univ _) hzf (fun i => hzsing i j) hdegrees
  simp only [Finset.card_univ, ZMod.card] at h
  exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hdeg))

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

private theorem hypersurfaceResidueChart_injective_of_pivot_eq {n p : ℕ} [Fact p.Prime]
    {r t : ProjectiveResidueSpace (n + 2) p}
    (hk : hypersurfaceResiduePivot r = hypersurfaceResiduePivot t)
    (ha : hypersurfaceResidueChart r = hypersurfaceResidueChart t) : r = t := by
  apply projectiveAffineCoordinatesAt_injective (hypersurfaceResiduePivot_ne_zero r)
    (hk.symm ▸ hypersurfaceResiduePivot_ne_zero t)
  simpa only [hypersurfaceResidueChart, hk] using ha

section

variable {n p d : ℕ} [Fact p.Prime]
  (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
include n p d f hf

private theorem projectiveHypersurfaceChart_irreducible_degree (hd : 2 ≤ d)
    (hir : Irreducible (map (Int.castRingHom (ZMod p)) f)) (k : Fin (n + 3)) :
    Irreducible (map (Int.castRingHom (ZMod p)) (affineChartAt k f)) ∧
      (map (Int.castRingHom (ZMod p)) (affineChartAt k f)).totalDegree = d := by
  let q := rename (Equiv.swap 0 k) (map (Int.castRingHom (ZMod p)) f)
  have hq : q.IsHomogeneous d := (hf.map _).rename_isHomogeneous
  have hqi :=
    (MulEquiv.irreducible_iff (f := renameEquiv (ZMod p) (Equiv.swap 0 k))).mpr hir
  have hX := variable_not_dvd_irreducible_homogeneous q hq hqi hd 0
  rw [map_affineChartAt]
  change Irreducible (affineChart (n + 2) q) ∧ (affineChart (n + 2) q).totalDegree = d
  exact ⟨affineChart_irreducible_of_not_variable_dvd q hq hqi hX,
    affineChart_degree_of_not_variable_dvd q hq hX⟩

private lemma projectiveHypersurfaceResidueMultiplicity_singular
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0) (r : ProjectiveHypersurfaceResidue f p)
    (hμ : 2 ≤ projectiveHypersurfaceResidueMultiplicity f r) :
    ∀ j, eval (hypersurfaceResidueChart r.val)
      (pderiv j (map (Int.castRingHom (ZMod p))
        (affineChartAt (hypersurfaceResiduePivot r.val) f))) = 0 := by
  have hp := (projectiveHypersurfaceResidueMultiplicity_spec f hf hf0 r).2.2.1
  change map (Int.castRingHom (ZMod p)) (originShift (hypersurfaceResidueChartLift r.val)
    (affineChartAt (hypersurfaceResiduePivot r.val) f)) ∈ _ at hp
  rw [originShift_map] at hp
  change originShift (fun j => (hypersurfaceResidueChartLift r.val j : ZMod p)) _ ∈ _ at hp
  simp only [cast_hypersurfaceResidueChartLift] at hp
  exact singular_of_origin_order_ge_two _ _ hμ hp

/-- Count singular classes in their n+3 possible charts. The pivots and
multiplicities here are those of the reduced projective hypersurface. -/
private theorem projective_hypersurface_singular_residue_card_le (hd : 2 ≤ d)
    (hir : Irreducible (map (Int.castRingHom (ZMod p)) f)) (hchar : d < p) :
    (Finset.univ.filter fun r : ProjectiveHypersurfaceResidue f p =>
      2 ≤ projectiveHypersurfaceResidueMultiplicity f r).card ≤
      (n + 3) * ((n + 2) ^ n * d * (d - 1) * p ^ n) := by
  classical
  let S := Finset.univ.filter fun r : ProjectiveHypersurfaceResidue f p =>
    2 ≤ projectiveHypersurfaceResidueMultiplicity f r
  let T (k : Fin (n + 3)) := S.filter fun r => hypersurfaceResiduePivot r.val = k
  have hk {k : Fin (n + 3)} (r : T k) :=
    (Finset.mem_filter.mp r.property).2
  have hT (k : Fin (n + 3)) : (T k).card ≤ (n + 2) ^ n * d * (d - 1) * p ^ n := by
    let q := map (Int.castRingHom (ZMod p)) (affineChartAt k f)
    have hq := projectiveHypersurfaceChart_irreducible_degree f hf hd hir k
    let z : T k → Fin (n + 2) → ZMod p :=
      fun r => hypersurfaceResidueChart r.val.val
    have hz : Function.Injective z := by
      intro r t he
      apply Subtype.ext
      apply Subtype.ext
      exact hypersurfaceResidueChart_injective_of_pivot_eq ((hk r).trans (hk t).symm) he
    have hzero (r : T k) : eval (z r) q = 0 := by
      have h := hypersurfaceResidueChartLift_zero f hf r.val.val r.val.property
      rw [hk r] at h
      simpa only [q, z, eval_map, cast_hypersurfaceResidueChartLift] using h
    have hsing (r : T k) (j : Fin (n + 2)) : eval (z r) (pderiv j q) = 0 := by
      have h := projectiveHypersurfaceResidueMultiplicity_singular f hf hir.ne_zero r.val
        (Finset.mem_filter.mp (Finset.mem_filter.mp r.property).1).2 j
      simpa only [hk r] using h
    have h := hypersurface_singular_points_card_le (p := p) q hq.1
      (by rw [hq.2]; omega) (by rwa [hq.2]) z hz hzero hsing
    simpa only [Fintype.card_coe, q, hq.2] using h
  have hsum : ∑ k : Fin (n + 3), (T k).card = S.card := by
    simp only [T, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  have h := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin (n + 3)))) => hT k)
  rw [hsum] at h
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_assoc]
    using h

/-- Singular classes contribute only a lower-order correction to the
projective point count; the leading term is not multiplied by the degree. -/
private theorem projectiveHypersurfaceTotalMultiplicity_le_card_add_correction
    (hd : 2 ≤ d) (hir : Irreducible (map (Int.castRingHom (ZMod p)) f)) (hchar : d < p) :
    projectiveHypersurfaceTotalMultiplicity f p ≤
      Fintype.card (ProjectiveHypersurfaceResidue f p) +
        (n + 3) * (n + 2) ^ n * d ^ 2 * (d - 1) * p ^ n := by
  classical
  let S := Finset.univ.filter fun r : ProjectiveHypersurfaceResidue f p =>
    2 ≤ projectiveHypersurfaceResidueMultiplicity f r
  have hS :=
    projective_hypersurface_singular_residue_card_le f hf hd hir hchar
  have hpoint (r : ProjectiveHypersurfaceResidue f p) :
      projectiveHypersurfaceResidueMultiplicity f r ≤
        1 + if r ∈ S then d else 0 := by
    have h := (projectiveHypersurfaceResidueMultiplicity_spec f hf hir.ne_zero r).2.1
    grind
  have hsum : projectiveHypersurfaceTotalMultiplicity f p ≤
      Fintype.card (ProjectiveHypersurfaceResidue f p) + S.card * d := by
    calc _ ≤ ∑ r : ProjectiveHypersurfaceResidue f p, (1 + if r ∈ S then d else 0) :=
           Finset.sum_le_sum fun r _ => hpoint r
         _ = _ := by simp [Finset.sum_add_distrib]
  apply hsum.trans
  apply Nat.add_le_add_left
  convert Nat.mul_le_mul_right d hS using 1
  ring

/-- Above the square-degree cutoff the multiplicity correction has the
O_n(d^2 p^(dimension-1/2)) scale required by CCDN Lemma 2.7. -/
theorem projectiveHypersurfaceTotalMultiplicity_le_card_add_sqrt_error
    (hd : 2 ≤ d) (hir : Irreducible (map (Int.castRingHom (ZMod p)) f)) (hsize : d ^ 2 < p) :
    (projectiveHypersurfaceTotalMultiplicity f p : ℝ) ≤
      Fintype.card (ProjectiveHypersurfaceResidue f p) +
        ((n + 3) * (n + 2) ^ n : ℕ) * (d : ℝ) ^ 2 * (p : ℝ) ^ n * Real.sqrt p := by
  have h := projectiveHypersurfaceTotalMultiplicity_le_card_add_correction f hf hd hir ((Nat.le_mul_self d).trans_lt (by simpa only [pow_two] using hsize))
  have hR : (projectiveHypersurfaceTotalMultiplicity f p : ℝ) ≤
      Fintype.card (ProjectiveHypersurfaceResidue f p) +
        ((n + 3) * (n + 2) ^ n * d ^ 2 * (d - 1) * p ^ n : ℕ) := by exact_mod_cast h
  have hs : (d : ℝ) ≤ Real.sqrt p := Real.le_sqrt_of_sq_le (by exact_mod_cast hsize.le)
  have hmul := mul_le_mul_of_nonneg_left ((by exact_mod_cast Nat.sub_le d 1 : ((d - 1 : ℕ) : ℝ) ≤ d).trans hs)
    (show 0 ≤ (((n + 3) * (n + 2) ^ n : ℕ) : ℝ) * (d : ℝ) ^ 2 * (p : ℝ) ^ n by positivity)
  apply hR.trans
  apply add_le_add le_rfl
  push_cast at hmul ⊢
  convert hmul using 1
  ring

end

end
end CCDN
