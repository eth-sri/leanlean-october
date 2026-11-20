/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Plane.FiniteFieldConstants
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.Real.Sqrt
import CCDN.ForMathlib.MvPolynomial
import CCDN.Plane.StepanovBound
import CCDN.Plane.StepanovDimension
import CCDN.Plane.StepanovParameters

/-! The sharp finite-field estimate for plane curves from Stepanov's auxiliary polynomial. -/

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
  unfold stepanovThreshold at hp
  have hpR : 27 * (d : ℝ) ^ 4 < p := by exact_mod_cast hp
  have hp0 := lt_of_le_of_lt (by positivity) hpR
  let s := Real.sqrt (p : ℝ)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 := Real.sq_sqrt (le_of_lt hp0)
  have hs1 : 1 ≤ s := by nlinarith only [hs0, hs2, hpR, hd2]
  have hNR : (N : ℝ) + 4 * (d : ℝ) ^ 2 = (d : ℝ) * A := by exact_mod_cast hN
  have hpxR : (p : ℝ) < ((d : ℝ) * A + d) ^ 2 := by exact_mod_cast hpx
  have hsnear : s < (N : ℝ) + 5 * (d : ℝ) ^ 2 := by
    linarith [(Real.sqrt_lt hp0.le (by positivity)).mpr hpxR]
  have hsN : s < 32 * (N : ℝ) := by
    by_contra! hn
    have hh : 31 * s < 160 * (d : ℝ) ^ 2 := by linarith only [hn, hsnear]
    have hsq := mul_self_lt_mul_self (by positivity : 0 ≤ 31 * s) hh
    nlinarith only [hsq, hpR, hs2]
  have hsp : (p : ℝ) ≤ 32 * N * s := by
    have hh := mul_le_mul_of_nonneg_right (le_of_lt hsN) hs0
    nlinarith only [hh, hs2]
  have hprod := mul_le_mul (show 4 * (d : ℝ) ^ 2 + 1 ≤ 5 * (d : ℝ) ^ 2 by linarith)
    hsp hp0.le (by positivity)
  have hsmall := mul_le_mul_of_nonneg_left hs1 (by positivity : 0 ≤ (d : ℝ) ^ 2 * N)
  have hcR := Nat.cast_le (α := ℝ).mpr hcount
  push_cast [Nat.cast_sub (show 1 ≤ d from hd)] at hcR
  have hDR : (d : ℝ) * D ≤ p := by exact_mod_cast hD.le
  rw [mul_add, mul_left_comm (d : ℝ) (p : ℝ), ← hNR] at hcR
  have hfin : (t : ℝ) * N ≤ (p + 161 * (d : ℝ) ^ 2 * s) * N := by
    nlinarith only [hprod, hsmall, hDR, hcR, show 0 ≤ (d : ℝ) * N by positivity]
  exact (mul_le_mul_iff_left₀ (by exact_mod_cast hNpos : (0 : ℝ) < N)).mp hfin

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
    have h1 := Nat.le_mul_self f.totalDegree
    have h2 := Nat.le_mul_self (f.totalDegree * f.totalDegree)
    nlinarith only [hp, h1, h2]
  obtain ⟨A, D, N, hA, hD, hDp, hNp, hN, hNpos, hx, hy, hpx⟩ :=
    exists_stepanov_integer_parameters f.totalDegree p hd hp
  have hdim := stepanov_hilbert_dimension_inequality f hf.ne_zero p A D N hd hp hA hD hx hy hN hNpos
  have hc := plane_stepanov_bound p f hf hd hchar z hz hzero hDp hNp hdim
  exact stepanov_real_bound f.totalDegree p A D N (Fintype.card ι) hd hp hDp hN hNpos hpx hc

end
end CCDN
