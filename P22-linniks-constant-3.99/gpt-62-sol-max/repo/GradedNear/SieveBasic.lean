module

public import GradedNear.Expansion

/-!
# Proof-side auxiliary definitions (not part of the statement)
-/

@[expose] public section

namespace GradedNear

/-- The Selberg majorant `ν_V(n) = (Σ_{d ∣ n} ψ_d)²` with the weights of `grahamWeight`. -/
noncomputable def sieveNu (V : ℝ) (n : ℕ) : ℝ := (∑ d ∈ n.divisors, grahamWeight V d) ^ 2

lemma sieveNu_nonneg (V : ℝ) (n : ℕ) : 0 ≤ sieveNu V n := sq_nonneg _

/-- The natural numbers in the real half-open interval `[A,B)`. -/
noncomputable def realIco (A B : ℝ) : Finset ℕ := Finset.Ioc (⌈A⌉₊ - 1) (⌈B⌉₊ - 1)

lemma mem_realIco {A B : ℝ} {n : ℕ} :
    n ∈ realIco A B ↔ 1 ≤ n ∧ A ≤ (n : ℝ) ∧ (n : ℝ) < B := by
  simp only [realIco, Finset.mem_Ioc, ← Nat.ceil_le, ← Nat.lt_ceil]
  omega

noncomputable def sieveInterval (q : ℕ) (t u : ℝ) := realIco ((q : ℝ) ^ t) ((q : ℝ) ^ u)

noncomputable def wt (s : ℂ) (n : ℕ) : ℂ := (Real.log n : ℂ) * (n : ℂ) ^ (-s)

noncomputable def sieveWeight (V : ℝ) (n : ℕ) : ℝ := Real.log n / n * sieveNu V n

open Finset Complex MeasureTheory in
/-- Abel's estimate for the sieve weight on logarithmic coordinates. -/
lemma wt_sum_norm_le (s : ℂ) (hs : 1 ≤ s.re) (c : ℕ → ℂ) {A B E : ℝ} (hA : 1 ≤ A)
    (hAB : A ≤ B)
    (hP : ∀ t ∈ Set.Icc A B, ‖∑ n ∈ realIco A t, c n‖ ≤ E * t) : ‖∑ n ∈ realIco A B, wt s n * c n‖ ≤
      E * (Real.log B + (Real.log B - Real.log A + ‖s‖ * (Real.log B ^ 2 - Real.log A ^ 2) / 2)) := by
  let U := realIco A B
  let W (u : ℝ) := cexp ((u : ℂ) * (-s))
  let F (u : ℝ) := (u : ℂ) * W u
  have hAp := zero_lt_one.trans_le hA
  have hE := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hP A ⟨le_rfl, hAB⟩)) hAp
  have hLa := Real.log_nonneg hA
  have hLb := Real.log_nonneg (hA.trans hAB)
  have hN {n} (hn : n ∈ U) : 0 < (n : ℝ) := Nat.cast_pos.mpr (mem_realIco.mp hn).1
  have hW u (hu : 0 ≤ u) w z (hz : ‖z‖ ≤ E * Real.exp u) : ‖W u * w * z‖ ≤ E * ‖w‖ := by
    have hExp : ‖W u‖ ≤ (Real.exp u)⁻¹ := by
      dsimp [W]
      rw [norm_exp, re_ofReal_mul, neg_re, ← Real.exp_neg, Real.exp_le_exp]
      nlinarith
    simp only [norm_mul]
    grw [hz, hExp]
    field_simp; rfl
  have hEq n (hn : n ∈ U) : wt s n * c n = F (Real.log n) * c n := by
    rw [wt, cpow_def_of_ne_zero (by exact_mod_cast (hN hn).ne'), ← natCast_log]
  let A' := Real.log A
  let B' := Real.log B
  have hAB' : A' ≤ B' := Real.log_le_log hAp hAB
  have hU' n (hn : n ∈ U) : Real.log n ∈ Set.Ico A' B' :=
    ⟨Real.log_le_log hAp (mem_realIco.mp hn).2.1, Real.log_lt_log (hN hn) (mem_realIco.mp hn).2.2⟩
  let G (u : ℝ) := 1 + ‖s‖ * u
  have hGc : Continuous G := by unfold G; fun_prop
  have hD u (hu : u ∈ Set.Icc A' B') : ‖1 - (u : ℂ) * s‖ ≤ G u := by
    simpa [G, norm_mul, Real.norm_of_nonneg (hLa.trans hu.1), mul_comm] using
      norm_sub_le (1 : ℂ) ((u : ℂ) * s)
  have hP' u (hu : u ∈ Set.Icc A' B') :
      ‖∑ n ∈ U.filter (fun n : ℕ => Real.log n < u), c n‖ ≤ E * Real.exp u := by
    have ht : Real.exp u ∈ Set.Icc A B :=
      ⟨(Real.log_le_iff_le_exp hAp).mp hu.1, (Real.le_log_iff_exp_le (hAp.trans_le hAB)).mp hu.2⟩
    convert hP _ ht using 3
    ext n
    simp only [U, mem_filter, mem_realIco]
    by_cases hn : 1 ≤ n
    · simp only [hn, true_and, Real.log_lt_iff_lt_exp (Nat.cast_pos.mpr (show 0 < n from hn))]
      grind
    · simp [hn]
  let F' (u : ℝ) := W u * (1 - u * s)
  have hF u : HasDerivAt F (F' u) u := by
    have h : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 u := by simpa using (hasDerivAt_id u).ofReal_comp
    convert h.mul (h.mul_const (-s)).cexp using 1
    dsimp only [F', W]; ring
  have hFc : Continuous F' := by unfold F' W; fun_prop
  let K (n : ℕ) := (Set.Ioi (Real.log n)).indicator (fun t => F' t * c n)
  have hKi n : IntegrableOn (K n) (Set.Ioc A' B') :=
    ((hFc.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).mul_const _).indicator measurableSet_Ioi
  have hsum n (hn : n ∈ U) : F (Real.log n) * c n = F B' * c n - ∫ t in Set.Ioc A' B', K n t := by
    have ⟨ha, hb⟩ := hU' n hn
    dsimp only [K]
    rw [setIntegral_indicator measurableSet_Ioi, Set.Ioc_inter_Ioi, sup_eq_right.mpr ha,
      integral_mul_const, ← intervalIntegral.integral_of_le hb.le,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t) hFc.continuousOn.intervalIntegrable]
    ring
  have hI : (∫ u in A'..B', G u) = B' - A' + ‖s‖ * (B' ^ 2 - A' ^ 2) / 2 := by
    dsimp only [G]
    have hg : IntervalIntegrable (fun u : ℝ => ‖s‖ * u) volume A' B' :=
      (continuous_id.intervalIntegrable _ _).const_mul _
    rw [intervalIntegral.integral_add intervalIntegrable_const hg,
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
    simp [smul_eq_mul]; ring
  change _ ≤ E * (B' + _)
  rw [← hI]
  rw [sum_congr rfl (fun n hn => (hEq n hn).trans (hsum n hn)), sum_sub_distrib, ← mul_sum,
    ← integral_finsetSum U (fun n _ => hKi n), mul_add]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · simpa only [F, mul_comm (B' : ℂ), norm_real, Real.norm_of_nonneg (show 0 ≤ B' from hLb)] using
      hW B' hLb (B' : ℂ) _ (by simpa [B', Real.exp_log (hAp.trans_le hAB)] using hP B ⟨hAB, le_rfl⟩)
  · refine (norm_integral_le_integral_norm _).trans ?_
    rw [intervalIntegral.integral_of_le hAB', ← integral_const_mul]
    refine setIntegral_mono_on (integrable_finsetSum _ fun n _ => hKi n).norm
      ((hGc.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).const_mul _) measurableSet_Ioc fun t ht => ?_
    simp only [K, Set.indicator, Set.mem_Ioi, ← sum_filter, ← mul_sum, F']
    exact (hW t (hLa.trans ht.1.le) _ _ (hP' t ⟨ht.1.le, ht.2⟩)).trans
      (mul_le_mul_of_nonneg_left (hD t ⟨ht.1.le, ht.2⟩) hE)

end GradedNear
