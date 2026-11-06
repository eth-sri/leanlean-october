/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Plane.RationalPlaneAssembly
import CCDN.ForMathlib.MvPolynomial
import CCDN.Plane.NonabsolutePlaneCount
import CCDN.Plane.StepanovBound
import CCDN.Plane.StepanovDimension
import CCDN.Plane.StepanovParameters

/-!
Sharp finite-field counting and the complete rational-plane
integral-point bound. The finite-field proof uses the constructed Stepanov
auxiliary and retains an explicit absolute error constant.

The complete rational plane reduction to sharp finite-field counting.
The non-absolutely-irreducible case is bounded by d².

The explicit real-valued error term for the integer Stepanov parameters.

The affine residue points of an integer plane equation are the
zeros of its reduction.
-/

namespace CCDN
open MvPolynomial

lemma planeResidue_card_eq_zero_card (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) :
    Nat.card (PlaneResidue f p) =
      Nat.card {x : Fin 2 → ZMod p //
        eval x (MvPolynomial.map (Int.castRingHom (ZMod p)) f) = 0} := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  simp

end CCDN

namespace CCDN

open MvPolynomial Real

/-- Every box on a rational irreducible plane curve which splits over a field
extension has at most d² integer points, independently of the radius. -/
theorem count_nonabsolute_plane_le {F : Type*} [Field F] [CharZero F]
    (f : MvPolynomial (Fin 2) ℚ) (hf : Irreducible f) (hd : 0 < f.totalDegree)
    (hred : ¬ Irreducible (MvPolynomial.map (algebraMap ℚ F) f)) (B : ℝ) :
    count (zeroLocus f) B ≤ f.totalDegree ^ 2 := by
  let S := integralPoints (zeroLocus f) B
  let z : S → Fin 2 → ℚ := fun i => rationalPoint i.val
  have h := nonabsolute_plane_points_card_le f hf hd hred z (by
    intro i j he
    apply Subtype.ext
    funext k
    exact Int.cast_injective (congrFun he k)) (fun i => (mem_integralPoints.mp i.property).2)
  simpa [Fintype.card_coe, S, count] using h

/-- The exact PlaneCurveBound target follows from the sharp finite-field
estimate. The rational nonabsolute case is covered by the d² bound. -/
theorem planeCurveBound_of_residue_bound {C : ℝ}
    (hC : 0 ≤ C) (hres : PlaneResidueBound C) : PlaneCurveBound := by
  let K := 2 * Real.exp 1 * affineNonzeroConstantBound C
  have hK : 0 < K := mul_pos (by positivity) (affineNonzeroConstantBound_pos C)
  refine ⟨K + 1, by linarith, ?_⟩
  intro f hf hd B hB
  have hG : 0 ≤ curveBound f.totalDegree B := by
    have h := degree_four_le_curveBound hd hB
    exact (by positivity : (0 : ℝ) ≤ f.totalDegree ^ 4).trans h
  by_cases habs : AbsolutelyIrreducibleRat f
  · exact (count_rational_plane_of_residue_bound f habs hd hB hC hres).trans
      (mul_le_mul_of_nonneg_right (by linarith) hG)
  · have hh := count_nonabsolute_plane_le f hf hd habs B
    have ht : (count (zeroLocus f) B : ℝ) ≤ (f.totalDegree : ℝ) ^ 2 := mod_cast hh
    have hd1 : (1 : ℝ) ≤ f.totalDegree := mod_cast hd
    have hpow : (f.totalDegree : ℝ) ^ 2 ≤ (f.totalDegree : ℝ) ^ 4 := by bound
    have hb := ht.trans (hpow.trans (degree_four_le_curveBound hd hB))
    nlinarith

end CCDN

namespace CCDN
open MvPolynomial

/-- An irreducible plane equation over the prime field has at most
`p + planeResidueConstant * d² * √p` rational points when `p > stepanovThreshold d`. -/
theorem plane_finite_field_card_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin 2) (ZMod p)) (hf : Irreducible f)
    (hsize : stepanovThreshold (f.totalDegree : ℝ) < p)
    (z : ι → Fin 2 → ZMod p) (hz : Function.Injective z)
    (hzero : ∀ i, eval (z i) f = 0) :
    (Fintype.card ι : ℝ) ≤ p + planeResidueConstant * (f.totalDegree : ℝ) ^ 2 * Real.sqrt p := by
  have hd := totalDegree_pos_of_ne_zero_of_not_isUnit hf.ne_zero hf.not_isUnit
  have hp : 27 * f.totalDegree ^ 4 < p := mod_cast hsize
  obtain ⟨A, D, N, hA, hD, hDp, hNp, hN, hNpos, hx, hy, hpx⟩ :=
    exists_stepanov_integer_parameters f.totalDegree p hd hp
  have hdim := stepanov_hilbert_dimension_inequality f hf.ne_zero p A D N hd hp hA hD hx hy hN hNpos
  have hc := plane_stepanov_bound p f hf hd (by
    have h1 := Nat.le_mul_self f.totalDegree
    nlinarith) z hz hzero hDp hNp hdim
  have hdR : (1 : ℝ) ≤ f.totalDegree := mod_cast hd
  have hd2 : (1 : ℝ) ≤ (f.totalDegree : ℝ) ^ 2 := by nlinarith
  have hdle : (f.totalDegree : ℝ) ≤ (f.totalDegree : ℝ) ^ 2 := by nlinarith
  have hpR : 27 * (f.totalDegree : ℝ) ^ 4 < p := mod_cast hp
  have hp0 : (0 : ℝ) < p := by nlinarith
  let s := Real.sqrt (p : ℝ)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 := Real.sq_sqrt hp0.le
  have hs1 : 1 ≤ s := by nlinarith
  have hNR : (N : ℝ) + 4 * (f.totalDegree : ℝ) ^ 2 = (f.totalDegree : ℝ) * A := mod_cast hN
  have hpxR : (p : ℝ) < ((f.totalDegree : ℝ) * A + f.totalDegree) ^ 2 := mod_cast hpx
  have hxp0 : (0 : ℝ) ≤ (f.totalDegree : ℝ) * A + f.totalDegree := by positivity
  have hsnear : s < (N : ℝ) + 5 * (f.totalDegree : ℝ) ^ 2 := by nlinarith
  have hsN : s < 32 * (N : ℝ) := by nlinarith
  have hsp : (p : ℝ) ≤ 32 * N * s := by nlinarith
  have hcoef : 4 * (f.totalDegree : ℝ) ^ 2 + 1 ≤ 5 * (f.totalDegree : ℝ) ^ 2 := by grind
  have hprod1 := mul_le_mul_of_nonneg_right hcoef hp0.le
  have hprod2 := mul_le_mul_of_nonneg_left hsp (by positivity : 0 ≤ 5 * (f.totalDegree : ℝ) ^ 2)
  have hsmall := mul_le_mul_of_nonneg_left hs1 (by positivity : 0 ≤ (f.totalDegree : ℝ) ^ 2 * N)
  have hsub : f.totalDegree * (f.totalDegree - 1) ≤ f.totalDegree ^ 2 := by nlinarith [Nat.sub_le f.totalDegree 1]
  have hc : (Fintype.card ι) * N ≤ f.totalDegree * D + p * (f.totalDegree * A) + f.totalDegree ^ 2 * N := by nlinarith
  have hcR : ((Fintype.card ι) : ℝ) * N ≤ f.totalDegree * D + p * (f.totalDegree * A) + f.totalDegree ^ 2 * N := by
    exact_mod_cast hc
  have hDR : (f.totalDegree : ℝ) * D ≤ p := mod_cast hDp.le
  rw [← hNR] at hcR
  have hfin : ((Fintype.card ι) : ℝ) * N ≤ (p + 161 * (f.totalDegree : ℝ) ^ 2 * s) * N := by grind
  exact (mul_le_mul_iff_left₀ (by grind)).mp hfin

/-- The sharp finite-field hypothesis used by the affine determinant argument
holds with the absolute constant `planeResidueConstant = 161`. -/
theorem planeResidueBound : PlaneResidueBound planeResidueConstant := by
  intro f _hd p hp hsize hir
  let : Fact p.Prime := ⟨hp⟩
  let q := MvPolynomial.map (Int.castRingHom (ZMod p)) f
  have hqd : q.totalDegree ≤ f.totalDegree := totalDegree_map_le _ _
  have hs : stepanovThreshold (q.totalDegree : ℝ) < (p : ℝ) := by
    apply lt_of_le_of_lt _ hsize
    gcongr
  let S := {x : Fin 2 → ZMod p // eval x q = 0}
  have hh := plane_finite_field_card_bound p q hir hs (fun x : S => x.val)
    Subtype.val_injective (fun x => x.property)
  rw [planeResidue_card_eq_zero_card, Nat.card_eq_fintype_card]
  apply hh.trans
  gcongr
  exact planeResidueConstant_pos.le

