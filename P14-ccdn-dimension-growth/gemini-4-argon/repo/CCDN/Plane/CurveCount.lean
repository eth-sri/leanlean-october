/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Plane.RationalPlaneAssembly
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

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Real

/-- An irreducible plane equation over the prime field has at most
`p + planeResidueConstant * d² * √p` rational points when `p > stepanovThreshold d`. -/
theorem plane_finite_field_card_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin 2) (ZMod p)) (hf : Irreducible f)
    (hsize : stepanovThreshold (f.totalDegree : ℝ) < p)
    (z : ι → Fin 2 → ZMod p) (hz : Function.Injective z)
    (hzero : ∀ i, eval (z i) f = 0) :
    (Fintype.card ι : ℝ) ≤ p + planeResidueConstant * (f.totalDegree : ℝ) ^ 2 * Real.sqrt p := by
  let d := f.totalDegree
  have hd : 0 < d := totalDegree_pos_of_ne_zero_of_not_isUnit hf.ne_zero hf.not_isUnit
  have hp : 27 * d ^ 4 < p := mod_cast hsize
  have hchar : d < p := by
    nlinarith only [hp, Nat.le_mul_self d, Nat.le_mul_self (d * d)]
  obtain ⟨A, D, N, hA, hD, hDp, hNp, hN, hNpos, hx, hy, hpx⟩ :=
    exists_stepanov_integer_parameters d p hd hp
  have hdim := stepanov_hilbert_dimension_inequality f hf.ne_zero p A D N hd hp hA hD hx hy hN hNpos
  have hcount := plane_stepanov_bound p f hf hd hchar z hz hzero hDp hNp hdim
  have hdR : (1 : ℝ) ≤ d := mod_cast hd
  have hd2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith only [hdR]
  have hdle : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith only [hdR]
  have hpR : 27 * (d : ℝ) ^ 4 < p := mod_cast hp
  have hp0 : (0 : ℝ) < p := by nlinarith only [hpR, pow_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) 4]
  let s := Real.sqrt (p : ℝ)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = p := Real.sq_sqrt hp0.le
  have hs1 : 1 ≤ s := by nlinarith only [hs0, hs2, hpR, hd2]
  have hNR : (N : ℝ) + 4 * (d : ℝ) ^ 2 = (d : ℝ) * A := mod_cast hN
  have hpxR : (p : ℝ) < ((d : ℝ) * A + d) ^ 2 := mod_cast hpx
  have hxp0 : (0 : ℝ) ≤ (d : ℝ) * A + d := by positivity
  have hsnear : s < (N : ℝ) + 5 * (d : ℝ) ^ 2 := by
    have hh : s < (d : ℝ) * A + d := by nlinarith only [hpxR, hs2, hs0, hxp0]
    nlinarith only [hh, hNR, hdle]
  have hsN : s < 32 * (N : ℝ) := by
    by_contra! hn
    have hh : 31 * s < 160 * (d : ℝ) ^ 2 := by linarith only [hn, hsnear]
    nlinarith only [mul_self_lt_mul_self (by positivity : 0 ≤ 31 * s) hh, hpR, hs2]
  have hsp : (p : ℝ) ≤ 32 * N * s := by
    nlinarith only [mul_le_mul_of_nonneg_right hsN.le hs0, hs2]
  have hprod1 := mul_le_mul_of_nonneg_right (show 4 * (d : ℝ) ^ 2 + 1 ≤ 5 * (d : ℝ) ^ 2 by linarith) hp0.le
  have hprod2 := mul_le_mul_of_nonneg_left hsp (by positivity : 0 ≤ 5 * (d : ℝ) ^ 2)
  have hsmall := mul_le_mul_of_nonneg_left hs1 (by positivity : 0 ≤ (d : ℝ) ^ 2 * N)
  have hc : Fintype.card ι * N ≤ d * D + p * (d * A) + d ^ 2 * N := by
    nlinarith only [hcount, Nat.mul_le_mul_right N (show d * (d - 1) ≤ d ^ 2 by nlinarith [Nat.sub_le d 1])]
  have hcR : (Fintype.card ι : ℝ) * N ≤ (d : ℝ) * D + p * ((d : ℝ) * A) + (d : ℝ) ^ 2 * N := mod_cast hc
  have hDR : (d : ℝ) * D ≤ p := mod_cast hDp.le
  rw [← hNR] at hcR
  unfold planeResidueConstant
  change (Fintype.card ι : ℝ) ≤ p + 161 * (d : ℝ) ^ 2 * s
  exact (mul_le_mul_iff_left₀ (mod_cast hNpos : (0 : ℝ) < N)).mp
    (by nlinarith only [hcR, hDR, hprod1, hprod2, hsmall])

/-- The sharp finite-field hypothesis used by the affine determinant argument
holds with the absolute constant `planeResidueConstant = 161`. -/
theorem planeResidueBound : PlaneResidueBound planeResidueConstant := by
  intro f _hd p hp hsize hir
  let : Fact p.Prime := ⟨hp⟩
  classical
  let q := MvPolynomial.map (Int.castRingHom (ZMod p)) f
  have hqd : q.totalDegree ≤ f.totalDegree := totalDegree_map_le _ _
  have hs : stepanovThreshold (q.totalDegree : ℝ) < (p : ℝ) :=
    lt_of_le_of_lt (by gcongr) hsize
  let S := {x : Fin 2 → ZMod p // eval x q = 0}
  have hh := plane_finite_field_card_bound p q hir hs (fun x : S => x.val)
    Subtype.val_injective (fun x => x.property)
  have hcard : Nat.card (PlaneResidue f p) = Fintype.card S :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp only [q, eval_map])).trans
      (Nat.card_eq_fintype_card (α := S))
  rw [hcard]
  exact hh.trans (by have := planeResidueConstant_pos.le; gcongr)

/-- The full coefficient-uniform rational-plane integral-point bound. -/
theorem planeCurveBound : PlaneCurveBound := by
  classical
  let C := planeResidueConstant
  have hC := planeResidueConstant_pos.le
  let K := 2 * Real.exp 1 * affineNonzeroConstantBound C
  have hK : 0 < K := mul_pos (by positivity) (affineNonzeroConstantBound_pos C)
  refine ⟨K + 1, by linarith, fun f hf hd B hB => ?_⟩
  have hG4 := degree_four_le_curveBound hd hB
  have hG : 0 ≤ curveBound f.totalDegree B :=
    (by positivity : (0 : ℝ) ≤ (f.totalDegree : ℝ) ^ 4).trans hG4
  by_cases habs : AbsolutelyIrreducibleRat f
  · exact (count_rational_plane_of_residue_bound f habs hd hB hC planeResidueBound).trans
      (mul_le_mul_of_nonneg_right (by linarith) hG)
  · let S := integralPoints (zeroLocus f) B
    have hh := nonabsolute_plane_points_card_le f hf hd habs
      (fun i : S => rationalPoint i.val)
      (fun i j he => Subtype.ext (funext fun k => Int.cast_injective (congrFun he k)))
      (fun i => (mem_integralPoints.mp i.property).2)
    have ht : (count (zeroLocus f) B : ℝ) ≤ (f.totalDegree : ℝ) ^ 2 :=
      mod_cast (by simpa only [Fintype.card_coe, S, count] using hh)
    have hd1 : (1 : ℝ) ≤ f.totalDegree := mod_cast hd
    have hpow : (f.totalDegree : ℝ) ^ 2 ≤ (f.totalDegree : ℝ) ^ 4 := by
      nlinarith [sq_nonneg ((f.totalDegree : ℝ) ^ 2 - 1)]
    exact (ht.trans (hpow.trans hG4)).trans (by nlinarith)

end
end CCDN
