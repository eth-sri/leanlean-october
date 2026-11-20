/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Plane.FiniteFieldConstants
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Field.ZMod
public import CCDN.ForMathlib.MvPolynomial
import CCDN.Plane.StepanovBound
import CCDN.Plane.StepanovDimension
import CCDN.Plane.StepanovParameters

/-! The sharp finite-field plane curve bound from the Stepanov polynomial. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The Stepanov count `t N ≤ d (D + p A) + d (d - 1) N` gives the plane-curve bound
`t ≤ p + 161 d² √p`; see `planeResidueConstant` for the derivation of `161`. -/
lemma stepanov_real_bound (d p A D N t : ℕ) (hd : 0 < d)
    (hp : stepanovThreshold d < p) (hD : d * D < p)
    (hN : N + 4 * d ^ 2 = d * A) (hNpos : 0 < N)
    (hpx : p < (d * A + d) ^ 2)
    (hcount : t * N ≤ d * (D + p * A) + d * (d - 1) * N) :
    (t : ℝ) ≤ p + planeResidueConstant * (d : ℝ) ^ 2 * Real.sqrt p := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith only [hdR]
  have hdle : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith only [hdR]
  have hpR : 27 * (d : ℝ) ^ 4 < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by nlinarith only [hpR, pow_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) 4]
  let s := Real.sqrt p
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 := Real.sq_sqrt (le_of_lt hp0)
  have hs1 : 1 ≤ s := by nlinarith only [hs0, hs2, hpR, hd2]
  have hNR : (N : ℝ) + 4 * (d : ℝ) ^ 2 = (d : ℝ) * A := by exact_mod_cast hN
  have hpxR : (p : ℝ) < ((d : ℝ) * A + d) ^ 2 := by exact_mod_cast hpx
  have hxp0 : (0 : ℝ) ≤ (d : ℝ) * A + d := by positivity
  have hsnear : s < (N : ℝ) + 5 * (d : ℝ) ^ 2 := by
    have hh : s < (d : ℝ) * A + d := by nlinarith only [hpxR, hs2, hs0, hxp0]
    linarith
  have hsN : s < 32 * (N : ℝ) := by
    by_contra! hn
    have hh : 31 * s < 160 * (d : ℝ) ^ 2 := by linarith
    nlinarith only [mul_self_lt_mul_self (by positivity) hh, hpR, hs2]
  have hsp : (p : ℝ) ≤ 32 * N * s := by
    nlinarith only [mul_le_mul_of_nonneg_right (le_of_lt hsN) hs0, hs2]
  have hcoef : 4 * (d : ℝ) ^ 2 + 1 ≤ 5 * (d : ℝ) ^ 2 := by linarith only [hd2]
  have hsub : d * (d - 1) ≤ d ^ 2 := by nlinarith only [Nat.sub_le d 1]
  have hc : t * N ≤ d * D + p * (d * A) + d ^ 2 * N := by
    nlinarith only [hcount, Nat.mul_le_mul_right N hsub]
  have hcR : (t : ℝ) * N ≤ (d : ℝ) * D + p * ((d : ℝ) * A) + (d : ℝ) ^ 2 * N := by
    exact_mod_cast hc
  have hDR : (d : ℝ) * D ≤ p := by exact_mod_cast hD.le
  rw [← hNR] at hcR
  have hfin : (t : ℝ) * N ≤ (p + 161 * (d : ℝ) ^ 2 * s) * N := by
    nlinarith only [hcR, hDR, (mul_le_mul_of_nonneg_right hcoef (le_of_lt hp0)), (mul_le_mul_of_nonneg_left hsp (by positivity)), (mul_le_mul_of_nonneg_left hs1 (by positivity : 0 ≤ (d : ℝ) ^ 2 * N))]
  exact (mul_le_mul_iff_left₀ (by exact_mod_cast hNpos)).mp hfin

/-- An irreducible plane equation over the prime field has at most
`p + planeResidueConstant * d² * √p` rational points when `p > stepanovThreshold d`. -/
theorem plane_finite_field_card_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin 2) (ZMod p)) (hf : Irreducible f)
    (hsize : stepanovThreshold (f.totalDegree : ℝ) < p)
    (z : ι → Fin 2 → ZMod p) (hz : Function.Injective z)
    (hzero : ∀ i, eval (z i) f = 0) :
    (Fintype.card ι : ℝ) ≤ p + planeResidueConstant * (f.totalDegree : ℝ) ^ 2 * Real.sqrt p := by
  have hd := totalDegree_pos_of_ne_zero_of_not_isUnit hf.ne_zero hf.not_isUnit
  have hp : 27 * f.totalDegree ^ 4 < p := by exact_mod_cast hsize
  have hchar : f.totalDegree < p := by
    nlinarith [Nat.le_mul_self (f.totalDegree * f.totalDegree)]
  obtain ⟨A, D, N, hA, hD, hDp, hNp, hN, hNpos, hx, hy, hpx⟩ :=
    exists_stepanov_integer_parameters f.totalDegree p hd hp
  exact stepanov_real_bound f.totalDegree p A D N _ hd hp hDp hN hNpos hpx (plane_stepanov_bound p f hf hd hchar z hz hzero hDp hNp (stepanov_hilbert_dimension_inequality f hf.ne_zero p A D N hd hp hA hD hx hy hN hNpos))


end
end CCDN
