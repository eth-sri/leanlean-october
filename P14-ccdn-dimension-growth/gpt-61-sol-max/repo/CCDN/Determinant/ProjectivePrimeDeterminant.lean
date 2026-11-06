/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Determinant.ProjectivePlaneResidueDeterminant
public import CCDN.Determinant.SingularDeterminantCutoff
public import CCDN.Height.CountingHypotheses
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

public section
namespace CCDN
open MvPolynomial

/-- For a homogeneous integer polynomial `f` of degree `d ≥ 2` with irreducible reduction modulo a
prime `p > 27 d⁴`, the reduced plane curve has at most `p + projectivePlaneResidueConstant · d² ·
√p` points over `𝔽_p`. -/
theorem projective_plane_finite_field_card_bound {p d : ℕ} [Fact p.Prime]
    (f : CCDN.IntegerPolynomial 3) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hir : Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hsize : stepanovThreshold (d : ℝ) < p) :
    (Fintype.card (ProjectivePlaneResidue f p) : ℝ) ≤
      p + projectivePlaneResidueConstant * (d : ℝ) ^ 2 * Real.sqrt p := by
  classical
  rw [projectivePlaneResidueConstant]
  let q := map (Int.castRingHom (ZMod p)) f
  have hX := variable_not_dvd_irreducible_homogeneous q (hf.map _) hir hd 0
  have hchart := affineChart_irreducible_of_not_variable_dvd q (hf.map _) hir hX
  have hdeg := affineChart_degree_of_not_variable_dvd q (hf.map _) hX
  have hproper := irreducible_homogeneous_not_dvd_variable q (hf.map _) hir hd 0
  have hcard := projectivePlaneResidue_card_le_affine_add_degree f hf hir hproper
  have hz (a : PlaneResidue (affineChart 2 f) p) :
      eval a.val (affineChart 2 q) = 0 := by
    grind [affineChart_map, eval_map]
  have ha := plane_finite_field_card_bound p (affineChart 2 q) hchart
    (by rwa [hdeg]) (fun a : PlaneResidue (affineChart 2 f) p => a.val)
    Subtype.val_injective hz
  rw [hdeg, planeResidueConstant] at ha
  have hcardR : (Fintype.card (ProjectivePlaneResidue f p) : ℝ) ≤
      Fintype.card (PlaneResidue (affineChart 2 f) p) + d := by exact_mod_cast hcard
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hsqrt : 1 ≤ Real.sqrt ↑p := Real.one_le_sqrt.mpr
    (by exact_mod_cast (Fact.out : p.Prime).one_le)
  have hdsqrt : ↑d ≤ ↑d ^ 2 * Real.sqrt p := by
    nlinarith
  linarith

end CCDN

namespace CCDN
open MvPolynomial Finset


/-- Plane case of CCDN Proposition 3.2.6 at a single rank: for an independent evaluation of forms at
`s` primitive zeros of a degree-`d ≥ 2` plane curve whose reductions modulo primes `27 d⁴ < p ≤ s`
outside `bad` are irreducible, the logarithm of the gcd of the maximal minors is at least `s² / 2 ·
(log s - 4 log d - ∑_{p ∈ bad} log p / p - E)`, with the explicit constant `E =
degreeFourDeterminantError projectivePlaneDeterminantConstant`. -/
theorem projective_determinant_log_lower_at_rank {s N d M : ℕ} (hs : 0 < s)
    (f : CCDN.IntegerPolynomial 3) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    {F : Fin N → CCDN.IntegerPolynomial 3} {z : Fin s → IntPoint 3}
    (hev : IsIndependentEvaluation f M F z) (bad : Finset ℕ)
    (hred : ∀ p ∈ ((Ioc 0 s).filter Nat.Prime) \ bad,
      stepanovThreshold (d : ℝ) < p → Irreducible (map (Int.castRingHom (ZMod p)) f)) :
    (s : ℝ) ^ 2 / 2 * (Real.log s - 4 * Real.log d -
      (∑ p ∈ bad, Real.log p / p) - degreeFourDeterminantError projectivePlaneDeterminantConstant) ≤
        Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j))) := by
  have h := determinant_log_lower_of_local_divisors_degree_four (x := ↑s)
    (by exact_mod_cast hs) (show 0 < d by omega)
    (by linarith [projectivePlaneDeterminantConstant_pos] :
      0 ≤ projectivePlaneDeterminantConstant + 1)
    (show 0 ≤ ↑s ^ 2 / 2 by positivity) (Nat.cast_nonneg s) bad ∅ (empty_subset bad)
    (by simp) 0 (one_pos.trans_le (Int.Matrix.one_le_minorGcd hev.rows_linearIndependent)) (by
      rw [Nat.floor_natCast]
      intro p hp hcut
      have : Fact p.Prime := ⟨(mem_filter.mp (mem_sdiff.mp hp).1).2⟩
      simp only [div_div]; (
        let inline_hir := hred p hp hcut
        obtain ⟨hpos, e, _, he, hdiv⟩ := projective_reduction_minorGcd hs f hf inline_hir.ne_zero
          F hev.isHomogeneous z hev.primitive hev.eval_eq_zero
        have hm := (show ↑(projectivePlaneTotalMultiplicity f hf _) ≤ ↑p + (projectivePlaneDeterminantConstant + (1 : ℝ)) * ↑d ^ (2 : ℕ) * √↑p from (by
                     rw [projectivePlaneDeterminantConstant]
                     have hp : 27 * d ^ 4 < p := by exact_mod_cast hcut
                     have hchar : d < p := by
                       have h1 := Nat.le_mul_self d
                       have h2 := Nat.le_mul_self (d * d)
                       nlinarith only [hp, h1, h2]
                     have hmass := projectivePlaneTotalMultiplicity_le_card_add_correction f hf hd inline_hir hchar
                     have hmassR : (projectivePlaneTotalMultiplicity f hf inline_hir.ne_zero : ℝ) ≤
                         Fintype.card (ProjectivePlaneResidue f p) + (3 * d ^ 2 * (d - 1) : ℕ) := by
                       exact_mod_cast hmass
                     have hc := projective_plane_finite_field_card_bound f hf hd inline_hir hcut
                     rw [projectivePlaneResidueConstant] at hc
                     have hcorr := singular_correction_absorb (show 0 < d by omega)
                     
                       (show ↑d ^ 4 ≤ 27 * (d : ℝ) ^ 4 by nlinarith)
                       hcut
                     push_cast at hmassR hcorr
                     nlinarith))
        refine ⟨e, ?_, hdiv⟩
        apply le_trans (sub_le_sub_right ?_ (s : ℝ)) he
        apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left hm (by norm_num)
      )) (by simp)
  rw [sum_empty, add_zero] at h
  convert h using 1
  dsimp only [degreeFourDeterminantError]
  ring

end CCDN
