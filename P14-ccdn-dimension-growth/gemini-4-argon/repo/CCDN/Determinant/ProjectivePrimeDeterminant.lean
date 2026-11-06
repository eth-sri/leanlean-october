/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

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

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

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
  classical
  have h := determinant_log_lower_of_local_divisors_degree_four (x := (s : ℝ))
    (mod_cast hs) (show 0 < d by omega)
    (by linarith [projectivePlaneDeterminantConstant_pos] :
      (0 : ℝ) ≤ projectivePlaneDeterminantConstant + 1)
    (show 0 ≤ (s : ℝ) ^ 2 / 2 by positivity) (Nat.cast_nonneg s) bad ∅ (empty_subset bad)
    (by simp) 0 (one_pos.trans_le (Int.Matrix.one_le_minorGcd hev.rows_linearIndependent)) (by
      rw [Nat.floor_natCast]
      intro p hp hcut
      have hpprime : p.Prime := (mem_filter.mp (mem_sdiff.mp hp).1).2
      have : Fact p.Prime := ⟨hpprime⟩
      have hir := hred p hp hcut
      obtain ⟨hpos, e, _, he, hdiv⟩ := projective_reduction_minorGcd hs f hf hir.ne_zero
        F hev.isHomogeneous z hev.primitive hev.eval_eq_zero
      let q := map (Int.castRingHom (ZMod p)) f
      have hX := variable_not_dvd_irreducible_homogeneous q (hf.map _) hir hd 0
      have hchart := affineChart_irreducible_of_not_variable_dvd q (hf.map _) hir hX
      have hdeg := affineChart_degree_of_not_variable_dvd q (hf.map _) hX
      have hcardR : (Fintype.card (ProjectivePlaneResidue f p) : ℝ) ≤
          Fintype.card (PlaneResidue (affineChart 2 f) p) + d :=
        mod_cast projectivePlaneResidue_card_le_affine_add_degree f hf hir
          (irreducible_homogeneous_not_dvd_variable q (hf.map _) hir hd 0)
      have ha := plane_finite_field_card_bound p (affineChart 2 q) hchart
        (by rwa [hdeg]) (fun a : PlaneResidue (affineChart 2 f) p => a.val)
        Subtype.val_injective fun a => by rw [affineChart_map, eval_map]; exact a.property
      rw [hdeg, planeResidueConstant_eq] at ha
      have hdR : (1 : ℝ) ≤ d := mod_cast (show 1 ≤ d by omega)
      have hsqrt : 1 ≤ Real.sqrt (p : ℝ) := Real.one_le_sqrt.mpr (mod_cast hpprime.one_le)
      have hdsqrt : (d : ℝ) ≤ (d : ℝ) ^ 2 * Real.sqrt p := by
        nlinarith [mul_le_mul_of_nonneg_left hsqrt (sq_nonneg (d : ℝ))]
      have hchar : d < p := by
        have hpN : 27 * d ^ 4 < p := mod_cast hcut
        nlinarith only [hpN, Nat.le_mul_self d, Nat.le_mul_self (d * d)]
      have hmassR : (projectivePlaneTotalMultiplicity f hf hir.ne_zero : ℝ) ≤
          Fintype.card (ProjectivePlaneResidue f p) + (3 * d ^ 2 * (d - 1) : ℕ) :=
        mod_cast projectivePlaneTotalMultiplicity_le_card_add_correction f hf hd hir hchar
      have hcorr := singular_correction_absorb (show 0 < d by omega)
        (L := 27 * (d : ℝ) ^ 4)
        (show (d : ℝ) ^ 4 ≤ 27 * (d : ℝ) ^ 4 by nlinarith [sq_nonneg ((d : ℝ) ^ 2)]) hcut
      push_cast at hmassR hcorr
      have hm : (projectivePlaneTotalMultiplicity f hf hir.ne_zero : ℝ) ≤
          p + (projectivePlaneDeterminantConstant + 1) * (d : ℝ) ^ 2 * Real.sqrt p := by
        rw [projectivePlaneDeterminantConstant_eq]
        nlinarith
      refine ⟨e, ?_, hdiv⟩
      rw [div_div]
      exact (sub_le_sub_right (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        (mul_le_mul_of_nonneg_left hm (by norm_num))) (s : ℝ)).trans he) (by simp)
  rw [sum_empty, add_zero] at h
  convert h using 1
  dsimp only [degreeFourDeterminantError]
  ring

end
end CCDN
