/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Surface.SmoothPrimeWindow
public import CCDN.Analysis.SmallDegreeSurfaceNumerics
import CCDN.AuxiliaryPolynomial.BadPrimeCharge
import Mathlib.NumberTheory.Bertrand

/-! At fixed degree we may use a bounded number of primes on the scale `B^(1/20)`.
Nine such good primes suffice to pass the surface determinant cutoff. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset MvPolynomial

abbrev boxLog (B : ℝ) := Real.log B + 1
abbrev windowUnit (B : ℝ) := Real.exp (boxLog B / 20)

lemma boxLog_one_le {B : ℝ} (hB : 1 ≤ B) : 1 ≤ boxLog B := by linarith [Real.log_nonneg hB]
lemma windowUnit_one_le {B : ℝ} (hB : 1 ≤ B) : 1 ≤ windowUnit B := Real.one_le_exp (by have := boxLog_one_le hB; linarith)

lemma surface_root_le_window {B : ℝ} (hB : 1 ≤ B) {d : ℕ} (hd : 5 ≤ d) :
    B^(1/Real.sqrt (d:ℝ)) ≤ windowUnit B ^ 9 := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hB), windowUnit, ← Real.exp_nat_mul, Real.exp_le_exp]
  have := mul_le_mul_of_nonneg_left (surface_inverse_sqrt_le_nine_twentieths hd) (Real.log_nonneg hB)
  norm_num [boxLog] at *; linarith

/-- The nineteenth power pays for the last residue edge, still leaving a logarithmic margin. -/
lemma surface_window_weight : ∃ c : ℝ, 0 < c ∧ ∀ B ≥ 1, windowUnit B ^ 19 * boxLog B ^ 2 ≤ c * B := by
  let c := (2:ℝ)/(1/20:ℝ)^2 * Real.exp (1/20)
  refine ⟨Real.exp (19/20)*c, by positivity, fun B hB => ?_⟩
  have hb := zero_lt_one.trans_le hB
  have h := logarithm_add_one_pow_le_rpow 2 (by norm_num : (0:ℝ)<1/20) hB
  have hu : windowUnit B ^ 19 = Real.exp (19/20) * B^(19/20:ℝ) := by
    rw [windowUnit, ← Real.exp_nat_mul, Real.rpow_def_of_pos hb, ← Real.exp_add]; congr 1; dsimp [boxLog]; ring
  rw [hu]
  calc _ ≤ _ * (c * B^(1/20:ℝ)) := mul_le_mul_of_nonneg_left (by simpa [c] using h) (by positivity)
       _ = _ := by rw [mul_mul_mul_comm, ← Real.rpow_add hb]; norm_num

structure SurfaceWindow (N : ℕ) (B : ℝ) where
  primes : Finset ℕ
  card : primes.card = N
  bounds : ∀ p ∈ primes, p.Prime ∧ windowUnit B < p ∧ (p:ℝ) ≤ 2^N * windowUnit B

lemma exists_surfaceWindow {B : ℝ} (hB : 1 ≤ B) (N : ℕ) : Nonempty (SurfaceWindow N B) := by
  classical
  induction N with
  | zero => exact ⟨∅, rfl, by simp⟩
  | succ n ih =>
    obtain ⟨W⟩ := ih
    let y := 2^n * windowUnit B
    have hy : windowUnit B ≤ y := le_mul_of_one_le_left (Real.exp_pos _).le (one_le_pow₀ (by norm_num))
    have h1 := (windowUnit_one_le hB).trans hy
    obtain ⟨p,hp,hl,hu⟩ := Nat.exists_prime_lt_and_le_two_mul ⌊y⌋₊ (by have := (Nat.one_le_floor_iff _).mpr h1; omega)
    have hly : y < p := Nat.lt_of_floor_lt hl
    have huy : (p:ℝ) ≤ 2*y := by exact (by exact_mod_cast hu : (p:ℝ) ≤ 2*(⌊y⌋₊:ℝ)).trans (by gcongr; exact Nat.floor_le (by linarith))
    have hn : p ∉ W.primes := fun h => hly.not_ge (W.bounds p h).2.2
    refine ⟨insert p W.primes, by simp [hn,W.card], fun q h => ?_⟩
    rw [pow_succ]; change _ ∧ _ ∧ _ ≤ 2^n*2*windowUnit B
    rcases mem_insert.mp h with rfl | h
    · exact ⟨hp,hy.trans_lt hly,by linarith⟩
    · obtain ⟨ha,hb,hc⟩ := W.bounds q h
      exact ⟨ha,hb,by linarith⟩

abbrev surfaceWindowSize (d : ℕ) (K : ℝ) := ⌈20*(4*Real.log ((d:ℝ)+1)+K+d)⌉₊ + 9

lemma SurfaceWindow.smooth_subset {B K H : ℝ} {f : IntegerPolynomial 3} (hB : 1 ≤ B)
    (W : SurfaceWindow (surfaceWindowSize f.totalDegree K) B)
    (hH : 1 ≤ H) (hc : CoefficientHeightLE f H) (height : Real.log H ≤ K*boxLog B)
    (x : IntPoint 3) (hx : InBox x B) (hs : ∃ j, eval x (pderiv j f) ≠ 0) :
    ∃ P ⊆ W.primes, P.card = 9 ∧ ∀ p ∈ P, ∃ j, eval (fun i => (x i : ZMod p)) (pderiv j (residueEquation p f)) ≠ 0 := by
  classical
  obtain ⟨j,hj⟩ := hs
  let D := eval x (pderiv j f)
  let bad := W.primes.filter fun p : ℕ => (p:ℤ) ∣ D
  let d := f.totalDegree
  let L := 4*Real.log ((d:ℝ)+1)+K+d
  have hlog := integer_pderiv_log_bound f j hH hB hc x hx hj
  norm_num at hlog
  have hT := boxLog_one_le hB
  have hdlog := Real.log_nonneg (show 1 ≤ (d:ℝ)+1 by simp)
  have hcost : Real.log |(D:ℝ)| ≤ L*boxLog B := by
    have := le_mul_of_one_le_right hdlog hT
    rw [Real.log_abs]; dsimp only [boxLog,L,D,d] at *; nlinarith
  have hmass := prime_divisor_log_sum_le bad (abs_pos.mpr hj) (fun p hp => (W.bounds p (mem_filter.mp hp).1).1)
    (fun p hp => (dvd_abs _ _).mpr (mem_filter.mp hp).2)
  rw [Int.cast_abs] at hmass
  have hl (p : ℕ) (hp : p ∈ bad) : boxLog B / 20 ≤ Real.log p :=
    (Real.le_log_iff_exp_le (by exact_mod_cast (W.bounds p (mem_filter.mp hp).1).1.pos)).mpr (W.bounds p (mem_filter.mp hp).1).2.1.le
  have hcard : (bad.card:ℝ)*(boxLog B/20) ≤ L*boxLog B := by simpa using (sum_le_sum hl).trans (hmass.trans hcost)
  have hc' : (bad.card:ℝ) ≤ 20*L := (mul_le_mul_iff_left₀ (show 0 < boxLog B by linarith)).mp (by linarith)
  have hc'' : bad.card ≤ ⌈20*L⌉₊ := by exact_mod_cast hc'.trans (Nat.le_ceil _)
  have hw := W.card
  change W.primes.card = ⌈20*L⌉₊ + 9 at hw
  obtain ⟨P,hP,h9⟩ := exists_subset_card_eq (s := W.primes \ bad) (n := 9) (by rw [card_sdiff_of_subset (show bad ⊆ W.primes from filter_subset ..)]; omega)
  refine ⟨P,hP.trans sdiff_subset,h9,fun p hp => ⟨j,?_⟩⟩
  have hn := mem_sdiff.mp (hP hp)
  intro he
  have he' : (D : ZMod p) = 0 := by
    change (Int.castRingHom (ZMod p)) (eval x (pderiv j f)) = 0; rw [map_eval]; rwa [pderiv_map] at he
  exact hn.2 (mem_filter.mpr ⟨hn.1,(ZMod.intCast_zmod_eq_zero_iff_dvd D p).mp he'⟩)

end
end CCDN
