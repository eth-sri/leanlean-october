/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Determinant.ProjectivePlaneResidueDeterminant
import CCDN.Determinant.SingularDeterminantCutoff
import CCDN.Height.CountingHypotheses
import CCDN.Algebra.HomogeneousChartIrreducible
import CCDN.Determinant.PrimeAggregation
import CCDN.Determinant.ProjectiveMultiplicity
import CCDN.Determinant.ProjectiveResidueCardinality
import CCDN.Plane.CurveCount

/-!
Sharp prime-power and global prime-sum bounds for projective plane
evaluation matrices. The excluded-prime set is explicit.

A sharp finite-field count for an irreducible homogeneous plane
curve. Chart irreducibility, its full degree and the infinity correction
are proved; the affine input is the formalized Stepanov estimate.
-/

namespace CCDN
open MvPolynomial

end CCDN

namespace CCDN
open MvPolynomial Finset

/-- For a homogeneous integer polynomial `f` of degree `d ≥ 2` with irreducible reduction modulo a
prime `p > 27 d⁴`, the total residue multiplicity of `f mod p` is at most `p +
(projectivePlaneDeterminantConstant + 1) · d² · √p`. -/
theorem projectivePlaneTotalMultiplicity_le {p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hir : Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hsize : stepanovThreshold (d : ℝ) < p) :
    (projectiveHypersurfaceTotalMultiplicity f hf hir.ne_zero : ℝ) ≤
      p + (projectivePlaneDeterminantConstant + 1) * (d : ℝ) ^ 2 * Real.sqrt p := by
  rw [(show projectivePlaneDeterminantConstant = 164 from rfl)]
  have hp : 27 * d ^ 4 < p := mod_cast hsize
  have hmass := projectiveHypersurfaceTotalMultiplicity_le_card_add_correction f hf hd hir (by
    have h1 := Nat.le_mul_self d
    nlinarith)
  simp only [zero_add, pow_zero, mul_one] at hmass
  have hmassR : (projectiveHypersurfaceTotalMultiplicity f hf hir.ne_zero : ℝ) ≤
      Fintype.card (ProjectiveHypersurfaceResidue f p) + (3 * d ^ 2 * (d - 1) : ℕ) := by
    exact_mod_cast hmass
  have hc : (Fintype.card (ProjectiveHypersurfaceResidue f p) : ℝ) ≤
      p + projectivePlaneResidueConstant * d ^ 2 * Real.sqrt p := by
    classical
    rw [projectivePlaneResidueConstant_eq]
    let q := map (Int.castRingHom (ZMod p)) f
    have hX := variable_not_dvd_irreducible_homogeneous q (hf.map _) hir hd 0
    have hchart := affineChart_irreducible_of_not_variable_dvd q (hf.map _) hir hX
    have hdeg := affineChart_degree_of_not_variable_dvd q (hf.map _) hX
    have hproper := irreducible_homogeneous_not_dvd_variable q (hf.map _) hir hd 0
    have hcard := projectivePlaneResidue_card_le_affine_add_degree f hf hir hproper
    have hz (a : PlaneResidue (affineChart 2 f) p) :
        eval a.val (affineChart 2 q) = 0 := by
      rw [affineChart_map, eval_map]
      exact a.property
    have ha := plane_finite_field_card_bound p (affineChart 2 q) hchart
      (by grind) (fun a : PlaneResidue (affineChart 2 f) p => a.val)
      Subtype.val_injective hz
    rw [hdeg, planeResidueConstant_eq] at ha
    have hcardR : (Fintype.card (ProjectiveHypersurfaceResidue f p) : ℝ) ≤
        Fintype.card (PlaneResidue (affineChart 2 f) p) + d := mod_cast hcard
    have hdR : (1 : ℝ) ≤ d := by bound
    have hsqrt : 1 ≤ Real.sqrt p := Real.one_le_sqrt.mpr
      (mod_cast (Fact.out : p.Prime).one_le)
    have hdsqrt : d ≤ d ^ 2 * Real.sqrt p := by
      nlinarith
    linarith
  rw [projectivePlaneResidueConstant_eq] at hc
  have hcorr := singular_correction_absorb (show 0 < d by omega)
    (L := 27 * (d : ℝ) ^ 4)
    (show (d : ℝ) ^ 4 ≤ 27 * (d : ℝ) ^ 4 by nlinarith)
    hsize
  push_cast at hmassR hcorr
  nlinarith

/-- Plane case of CCDN Proposition 3.2.6 at a single rank: for an independent evaluation of forms at
`s` primitive zeros of a degree-`d ≥ 2` plane curve whose reductions modulo primes `27 d⁴ < p ≤ s`
outside `bad` are irreducible, the logarithm of the gcd of the maximal minors is at least `s² / 2 ·
(log s - 4 log d - ∑_{p ∈ bad} log p / p - E)`, with the explicit constant `E =
degreeFourDeterminantError projectivePlaneDeterminantConstant`. -/
theorem projective_determinant_log_lower_at_rank {s N d M : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    {F : Fin N → MvPolynomial (Fin 3) ℤ} {z : Fin s → IntPoint 3}
    (hev : IsIndependentEvaluation f M F z) (bad : Finset ℕ)
    (hred : ∀ p ∈ ((Ioc 0 s).filter Nat.Prime) \ bad,
      stepanovThreshold (d : ℝ) < p → Irreducible (map (Int.castRingHom (ZMod p)) f)) :
    (s : ℝ) ^ 2 / 2 * (Real.log s - 4 * Real.log d -
      (∑ p ∈ bad, Real.log p / p) - degreeFourDeterminantError projectivePlaneDeterminantConstant) ≤
        Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j))) := by
  have h := determinant_log_lower_of_local_divisors_degree_four (x := s)
    (mod_cast hs) (show 0 < d by omega)
    (by linarith [projectivePlaneDeterminantConstant_pos] :
      (0 : ℝ) ≤ projectivePlaneDeterminantConstant + 1)
    (show 0 ≤ (s : ℝ) ^ 2 / 2 by positivity) (Nat.cast_nonneg s) bad ∅ (empty_subset bad)
    (by simp) 0 (one_pos.trans_le (Int.Matrix.one_le_minorGcd hev.rows_linearIndependent)) (by
      rw [Nat.floor_natCast]
      intro p hp hcut
      have : Fact p.Prime := ⟨(mem_filter.mp (mem_sdiff.mp hp).1).2⟩
      obtain ⟨hpos, e, he, hdiv⟩ := projective_reduction_minorGcd hs f hf (hred p hp hcut).ne_zero
        F hev.isHomogeneous z hev.primitive hev.eval_eq_zero
      refine ⟨e, le_trans (sub_le_sub_right ?_ (s : ℝ)) he, hdiv⟩
      rw [div_div]
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left (projectivePlaneTotalMultiplicity_le f hf hd (hred p hp hcut) hcut)
        (by norm_num)) (by simp)
  rw [sum_empty, add_zero] at h
  convert h using 1
  dsimp [degreeFourDeterminantError]
  ring

