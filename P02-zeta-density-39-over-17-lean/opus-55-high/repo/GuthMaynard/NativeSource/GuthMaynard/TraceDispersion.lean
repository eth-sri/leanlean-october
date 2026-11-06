module
public import Mathlib.Algebra.Order.Chebyshev
public import GuthMaynard.NativeSource.GuthMaynard.LargeValuesMatrix
import WeylPort.Analytic.RealLaplace

public section

open Finset

namespace GuthMaynard.NativeMoment

/-!
# Sixth-moment trace dispersion

The first lemma is the nonnegativity assertion needed for the sixth root in
Guth--Maynard Lemma 4.2.  It is a direct finite Jensen inequality, proved here
over the reals before the spectral specialization.
-/

section
variable {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℝ)
include ι s x
theorem sixthMoment_dispersion_nonneg (hs : s.Nonempty) :
    0 ≤ (∑ i ∈ s, x i ^ 6) -
      (∑ i ∈ s, x i ^ 2) ^ 3 / (s.card : ℝ) ^ 2 := by
  have hJensen := pow_sum_le_card_mul_sum_pow
    (s := s) (f := fun i => x i ^ 2) (fun i hi => sq_nonneg (x i)) 2
  have hcard : 0 < (s.card : ℝ) ^ 2 := by
    positivity
  have hpow : ∑ i ∈ s, (x i ^ 2) ^ 3 = ∑ i ∈ s, x i ^ 6 := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [sub_nonneg]
  rw [div_le_iff₀ hcard]
  rw [hpow] at hJensen
  grind

/-- Jensen on the complement of one selected coordinate, with the ambient
cardinality in the denominator. -/
theorem sixthMoment_tail_lower (j : ι) :
    (∑ i ∈ s.erase j, x i ^ 2) ^ 3 ≤
      (s.card : ℝ) ^ 2 * ∑ i ∈ s.erase j, x i ^ 6 := by
  have hJensen := pow_sum_le_card_mul_sum_pow
    (s := s.erase j) (f := fun i => x i ^ 2)
      (fun i hi => sq_nonneg (x i)) 2
  have hcard : ((s.erase j).card : ℝ) ^ 2 ≤ (s.card : ℝ) ^ 2 := by
    have hbase : ((s.erase j).card : ℝ) ≤ (s.card : ℝ) := by
      exact_mod_cast (Finset.card_erase_le (s := s) (a := j))
    exact pow_le_pow_left₀ (by positivity) hbase 2
  have hsum : 0 ≤ ∑ i ∈ s.erase j, x i ^ 6 := by positivity
  calc
    (∑ i ∈ s.erase j, x i ^ 2) ^ 3
        ≤ ((s.erase j).card : ℝ) ^ 2 *
          ∑ i ∈ s.erase j, (x i ^ 2) ^ 3 := hJensen
    _ = ((s.erase j).card : ℝ) ^ 2 * ∑ i ∈ s.erase j, x i ^ 6 := by grind
    _ ≤ (s.card : ℝ) ^ 2 * ∑ i ∈ s.erase j, x i ^ 6 :=
      mul_le_mul_of_nonneg_right hcard hsum

/-- The sixth-power form of Guth--Maynard equation (4.3).  Taking sixth and
square roots of its two branches gives the scalar inequality used in Lemma
4.2. -/
theorem coordinate_sixth_le_trace_dispersion_max (j : ι) (hj : j ∈ s) :
    x j ^ 6 ≤ max
      (4 * ((∑ i ∈ s, x i ^ 6) -
        (∑ i ∈ s, x i ^ 2) ^ 3 / (s.card : ℝ) ^ 2))
      (8 * (∑ i ∈ s, x i ^ 2) ^ 3 / (s.card : ℝ) ^ 3) := by
  let K : ℝ := s.card
  let S : ℝ := ∑ i ∈ s, x i ^ 2
  let Q : ℝ := ∑ i ∈ s, x i ^ 6
  let y : ℝ := x j ^ 2
  let B : ℝ := ∑ i ∈ s.erase j, x i ^ 2
  let R : ℝ := ∑ i ∈ s.erase j, x i ^ 6
  let A : ℝ := Q - S ^ 3 / K ^ 2
  have hs : s.Nonempty := ⟨j, hj⟩
  have hK : 0 < K := by
    dsimp [K]
    simp_all
  have hKsq : 0 < K ^ 2 := by positivity
  pm_61 hS S
  pm_61 hy y
  pm_61 hB B
  pm_61 hR R
  have hA : 0 ≤ A := by
    dsimp [A, Q, S, K]
    exact sixthMoment_dispersion_nonneg s x hs
  have hsumTwo : B + y = S := by
    dsimp [B, y, S]
    simp_all
  have hsumSix : R + x j ^ 6 = Q := by
    dsimp [R, Q]
    simp_all
  have hyCube : y ^ 3 = x j ^ 6 := by dsimp [y]; ring
  have htail : B ^ 3 ≤ K ^ 2 * R := by
    simpa only [B, K, R] using sixthMoment_tail_lower s x j
  by_cases hAverage : y ≤ 2 * S / K
  · have hcube := pow_le_pow_left₀ hy hAverage 3
    have hbranch : x j ^ 6 ≤ 8 * S ^ 3 / K ^ 3 := by
      rw [← hyCube]
      calc
        y ^ 3 ≤ (2 * S / K) ^ 3 := hcube
        _ = 8 * S ^ 3 / K ^ 3 := by ring
    exact hbranch.trans (le_max_right _ _)
  · have hdiv : 2 * S / K < y := lt_of_not_ge hAverage
    have hmul : 2 * S < y * K := (div_lt_iff₀ hK).mp hdiv
    have hyPos : 0 < y := by
      by_contra hyNot
      have hyZero : y = 0 := le_antisymm (le_of_not_gt hyNot) hy
      rw [hyZero] at hmul
      nlinarith
    have hsquare : (2 * S) ^ 2 < (y * K) ^ 2 :=
      (sq_lt_sq₀ (by positivity) (by positivity)).2 hmul
    have hstrong : 4 * S ^ 2 * y < K ^ 2 * y ^ 3 := by
      have hmulY := mul_lt_mul_of_pos_right hsquare hyPos
      nlinarith
    have hyS : y ≤ S := by nlinarith [hB]
    have hrem : 0 ≤ y ^ 2 * (3 * S - y) := by
      exact mul_nonneg (sq_nonneg y) (by linarith)
    have hdiff : S ^ 3 - B ^ 3 ≤ 3 * S ^ 2 * y := by
      have hid : S ^ 3 - B ^ 3 = 3 * S ^ 2 * y - 3 * S * y ^ 2 + y ^ 3 := by
        rw [← hsumTwo]
        ring
      rw [hid]
      nlinarith
    have hscaled : K ^ 2 * y ^ 3 ≤ 4 * (K ^ 2 * Q - S ^ 3) := by
      nlinarith
    have hAeq : K ^ 2 * A = K ^ 2 * Q - S ^ 3 := by
      dsimp [A]
      field_simp
    have hbranchY : y ^ 3 ≤ 4 * A := by
      apply le_of_mul_le_mul_of_pos_left _ hKsq
      calc
        K ^ 2 * y ^ 3 ≤ 4 * (K ^ 2 * Q - S ^ 3) := hscaled
        _ = K ^ 2 * (4 * A) := by rw [← hAeq]; ring
    have hbranch : x j ^ 6 ≤ 4 * A := by simpa only [hyCube] using hbranchY
    exact hbranch.trans (le_max_left _ _)
end

/-- Sampling-matrix specialization of the sixth-power form of
Guth--Maynard Lemma 4.2.  The two sums are respectively the first and cubic
spectral moments of the positive row Gram matrix. -/
theorem gmMatrix_singularValue_sixth_le_dispersion_max
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) (j : GMRow W) :
    gmMatrixSingularValue cutoff N W j ^ 6 ≤
      max
        (4 * ((∑ i : GMRow W,
            (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i ^ 3) -
          (∑ i : GMRow W,
            (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i) ^ 3 /
            (W.card : ℝ) ^ 2))
        (8 * (∑ i : GMRow W,
            (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i) ^ 3 /
            (W.card : ℝ) ^ 3) := by
  pm_1581
  have hj : j ∈ s := Finset.mem_univ j
  have hbound := coordinate_sixth_le_trace_dispersion_max s x j hj
  pm_4717
  simpa only [s, x, Finset.sum_const_zero, Finset.filter_true_of_mem,
    Finset.sum_filter, Finset.card_univ, Fintype.card_coe,
    hsquare, hsixth] using hbound

end GuthMaynard.NativeMoment
