/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Height.Box
public import CCDN.Height.IntegerCoefficientHeight
public import CCDN.Analysis.PrimeCutoff
public import Mathlib.Algebra.MvPolynomial.PDeriv
import CCDN.Algebra.IntegerRationalIrreducibility
import CCDN.ForMathlib.MvPolynomialDerivative
import CCDN.Height.PolynomialBoxHeight
import CCDN.AuxiliaryPolynomial.BadPrimeCharge
import Mathlib.NumberTheory.Bertrand

/-! A fixed number of primes of size comparable to `B^(1/40)` suffices for
smooth reduction of all nonsingular points of the box. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

private theorem integer_pderiv_coefficient_bound {σ : Type*} [Fintype σ]
    (f : MvPolynomial σ ℤ) (j : σ) {H : ℝ} (hH : 0 ≤ H)
    (hcoeff : CoefficientHeightLE f H) (e : σ →₀ ℕ) :
    |((pderiv j f).coeff e : ℝ)| ≤ ((f.totalDegree : ℝ) + 1) * H := by
  classical
  rw [coeff_pderiv]
  by_cases hz : f.coeff (e + Finsupp.single j 1) = 0
  · simp only [hz, zero_mul, Int.cast_zero, abs_zero]
    positivity
  · have he : e j + 1 ≤ f.totalDegree := by
      have h := ((degreeOf_le_iff).mp (degreeOf_le_totalDegree f j))
        (e + Finsupp.single j 1) (mem_support_iff.mpr hz)
      simp_all
    push_cast
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (e j : ℝ) + 1)]
    have heR : (e j : ℝ) + 1 ≤ (f.totalDegree : ℝ) + 1 := by
      exact_mod_cast (by omega : e j + 1 ≤ f.totalDegree + 1)
    calc
      _ ≤ H * ((e j : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (hcoeff _) (by positivity)
      _ ≤ H * ((f.totalDegree : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left heR hH
      _ = _ := by ring

section

variable {n : ℕ}
  (f : MvPolynomial (Fin n) ℤ) (j : Fin n) {H B : ℝ}
include n f j H B

private theorem integer_pderiv_evaluation_bound
    (hH : 0 ≤ H) (hB : 1 ≤ B)
    (hcoeff : CoefficientHeightLE f H)
    (x : IntPoint n) (hx : InBox x B) :
    |(eval x (pderiv j f) : ℝ)| ≤
      ((f.totalDegree : ℝ) + 1) ^ (n + 1) * H * B ^ f.totalDegree := by
  have hb := polynomial_eval₂_box_bound (pderiv j f)
    (((f.totalDegree : ℝ) + 1) * H) B (by positivity) hB
    (integer_pderiv_coefficient_bound f j hH hcoeff)
    (fun i => (x i : ℝ)) hx
  have heval : (eval x (pderiv j f) : ℝ) =
      eval₂ (Int.castRingHom ℝ) (fun i => (x i : ℝ)) (pderiv j f) := by
    simpa only [eval₂_id, RingHom.comp_id, Function.comp_def, Int.coe_castRingHom] using
      eval₂_comp_left (Int.castRingHom ℝ) (RingHom.id ℤ) x (pderiv j f)
  rw [← heval, Fintype.card_fin] at hb
  have hdeg := (pderiv_totalDegree_le f j).trans (Nat.sub_le ..)
  have hdegR : ((pderiv j f).totalDegree : ℝ) ≤ f.totalDegree := by exact_mod_cast hdeg
  calc
    _ ≤ (((pderiv j f).totalDegree : ℝ) + 1) ^ n *
        (((f.totalDegree : ℝ) + 1) * H) * B ^ (pderiv j f).totalDegree := hb
    _ ≤ ((f.totalDegree : ℝ) + 1) ^ n *
        (((f.totalDegree : ℝ) + 1) * H) * B ^ f.totalDegree := by
      gcongr
    _ = _ := by ring

private theorem integer_pderiv_log_bound
    (hH : 1 ≤ H) (hB : 1 ≤ B)
    (hcoeff : CoefficientHeightLE f H)
    (x : IntPoint n) (hx : InBox x B)
    (hne : eval x (pderiv j f) ≠ 0) :
    Real.log |(eval x (pderiv j f) : ℝ)| ≤
      (n + 1 : ℝ) * Real.log ((f.totalDegree : ℝ) + 1) +
        Real.log H + f.totalDegree * Real.log B := by
  have hpos : (0 : ℝ) < |(eval x (pderiv j f) : ℝ)| :=
    abs_pos.mpr (by exact_mod_cast hne)
  have hdpos : (0 : ℝ) < (f.totalDegree : ℝ) + 1 := by positivity
  have hH0 : 0 < H := by linarith
  have hlog := Real.log_le_log hpos
    (integer_pderiv_evaluation_bound f j hH0.le hB hcoeff x hx)
  rw [Real.log_mul (mul_pos (pow_pos hdpos _) hH0).ne' (pow_pos (by linarith) _).ne',
    Real.log_mul (pow_pos hdpos _).ne' hH0.ne', Real.log_pow, Real.log_pow] at hlog
  simp_all

end

private theorem exists_primes_near (n k : ℕ) (hn : 0 < n) :
    ∃ W : Finset ℕ, W.card = k ∧ ∀ p ∈ W, p.Prime ∧ n < p ∧ p ≤ 2 ^ k * n := by
  induction k with
  | zero => exact ⟨∅, rfl, by simp⟩
  | succ k ih =>
    obtain ⟨W, hW, hw⟩ := ih
    have hpos : 0 < 2 ^ k * n := by positivity
    obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ k * n) hpos.ne'
    have hnot : p ∉ W := fun h => (not_le_of_gt hlo) (hw p h).2.2
    refine ⟨insert p W, by simp [hnot, hW], ?_⟩
    intro q hq
    have he : 2 ^ (k + 1) * n = 2 * (2 ^ k * n) := by ring
    rw [he]
    rcases mem_insert.mp hq with rfl | hq
    · have hn' : n ≤ 2 ^ k * n := by
        exact Nat.le_mul_of_pos_left _ (by positivity)
      exact ⟨hp, hn'.trans_lt hlo, hhi⟩
    · obtain ⟨hprime, hlt, hle⟩ := hw q hq
      exact ⟨hprime, hlt, by omega⟩

/-- A window of `N` primes with fixed multiplicative width and logarithmic lower endpoint.
The `+ 1` in the lower endpoint allows the same choice all the way down to `B = 1`. -/
theorem exists_surface_prime_window (N : ℕ) :
    ∃ U : ℝ, 1 ≤ U ∧ ∀ B : ℝ, 1 ≤ B →
      ∃ W : Finset ℕ, W.card = N ∧ (∀ p ∈ W, p.Prime) ∧
        ∀ p ∈ W, (Real.log B + 1) / 40 ≤ Real.log p ∧ (p : ℝ) ≤ U * B ^ (1 / 40 : ℝ) := by
  let U := (2 : ℝ) ^ (N + 1) * Real.exp (1 / 40)
  refine ⟨U, one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (Real.one_le_exp (by norm_num)), ?_⟩
  intro B hB
  let z := Real.exp ((Real.log B + 1) / 40)
  have hz : 1 ≤ z := Real.one_le_exp (by linarith [Real.log_nonneg hB])
  have hceil : 0 < ⌈z⌉₊ := Nat.ceil_pos.mpr (by linarith)
  obtain ⟨W, hW, hw⟩ := exists_primes_near ⌈z⌉₊ N hceil
  refine ⟨W, hW, fun p hp => (hw p hp).1, ?_⟩
  intro p hp
  obtain ⟨_, hlow, hhigh⟩ := hw p hp
  have hlow' : z ≤ p := (Nat.le_ceil _).trans (by exact_mod_cast hlow.le)
  have hlog := Real.log_le_log (by linarith : 0 < z) hlow'
  have hhigh' : (p : ℝ) ≤ (2 : ℝ) ^ N * (⌈z⌉₊ : ℝ) := by exact_mod_cast hhigh
  have hceil' : (⌈z⌉₊ : ℝ) ≤ 2 * z := by
    linarith [Nat.ceil_lt_add_one (by positivity : 0 ≤ z)]
  refine ⟨by simpa [z] using hlog, hhigh'.trans ?_⟩
  calc
    _ ≤ (2 : ℝ) ^ N * (2 * z) := by gcongr
    _ = _ := by
      rw [show z = Real.exp (1 / 40) * B ^ (1 / 40 : ℝ) by
        dsimp only [z]
        rw [Real.rpow_def_of_pos (by linarith : 0 < B), ← Real.exp_add]
        congr 1
        ring]
      simp only [U, pow_succ]
      ring

/-- The nonzero derivative can exclude only a bounded number of primes from such a window. -/
theorem exists_smooth_prime_subset {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) {H B : ℝ} (hH : 1 ≤ H) (hB : 1 ≤ B)
    (hcoeff : CoefficientHeightLE f H) (W : Finset ℕ) (hW : ∀ p ∈ W, p.Prime)
    (hlo : ∀ p ∈ W, (Real.log B + 1) / 40 ≤ Real.log p)
    (hheight : (n + 1 : ℝ) * Real.log ((f.totalDegree : ℝ) + 1) +
      Real.log H + f.totalDegree * Real.log B ≤ (W.card - 18 : ℝ) * ((Real.log B + 1) / 40))
    (x : IntPoint n) (hx : InBox x B) (hsmooth : ∃ j, eval x (pderiv j f) ≠ 0) :
    ∃ P : Finset ℕ, P ⊆ W ∧ P.card = 18 ∧
      ∀ p ∈ P, ∃ j, eval (fun i => (x i : ZMod p))
        (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ := hsmooth
  let D := eval x (pderiv j f)
  let bad := W.filter (fun p : ℕ => (p : ℤ) ∣ D)
  let good := W.filter (fun p : ℕ => ¬ (p : ℤ) ∣ D)
  have hl := prime_divisor_log_sum_le bad (abs_pos.mpr hj)
    (fun p hp => hW p (mem_filter.mp hp).1) (fun p hp => (dvd_abs _ _).mpr (mem_filter.mp hp).2)
  rw [Int.cast_abs] at hl
  have hb := (sum_le_sum (s := bad) (fun p hp => hlo p (mem_filter.mp hp).1)).trans
    (hl.trans ((integer_pderiv_log_bound f j hH hB hcoeff x hx hj).trans hheight))
  simp only [sum_const, nsmul_eq_mul] at hb
  have hBc : 0 < (Real.log B + 1) / 40 := by linarith [Real.log_nonneg hB]
  have hbc := (mul_le_mul_iff_left₀ hBc).mp hb
  have hc : bad.card + good.card = W.card := card_filter_add_card_filter_not _
  have hc' : (bad.card : ℝ) + good.card = W.card := by exact_mod_cast hc
  obtain ⟨P, hP, hcard⟩ := exists_subset_card_eq (show 18 ≤ good.card by exact_mod_cast (by linarith : (18 : ℝ) ≤ good.card))
  refine ⟨P, hP.trans (filter_subset _ _), hcard, fun p hp => ⟨j, ?_⟩⟩
  have hnd := (mem_filter.mp (hP hp)).2
  have he : eval (fun i => (x i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p)) f)) = (D : ZMod p) := by
    rw [pderiv_map]
    exact (map_eval (Int.castRingHom (ZMod p)) x (pderiv j f)).symm
  rw [he]
  exact fun h => hnd ((ZMod.intCast_zmod_eq_zero_iff_dvd D p).mp h)

end
end CCDN
