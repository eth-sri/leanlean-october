module
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds
public import GuthMaynard.NativeSource.GuthMaynard.DirichletPolynomial
public import GuthMaynard.NativeSource.GuthMaynard.SecondOrderMeanValue
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Finset Set

namespace GuthMaynard.NativeMoment

/-!
# The logarithmic correlation kernel

This module specializes the project's finite Kusmin--Landau and van der Corput
estimates to the unweighted dyadic kernel occurring in the
Halász--Montgomery argument.
-/

/-- The unweighted Dirichlet-polynomial correlation kernel on `(N, 2N]`. -/
noncomputable def logarithmicKernel (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ dyadicInterval N, (n : ℂ) ^ (-(t : ℂ) * I)

theorem dyadicInterval_eq_Ico_succ (N : ℕ) :
    dyadicInterval N = Finset.Ico (N + 1) (2 * N + 1) := by
  ext n
  simp only [dyadicInterval, Finset.mem_Ioc, Finset.mem_Ico]
  omega

theorem logarithmicKernel_eq_logarithmicSum (N : ℕ) (t : ℝ) (hN : 0 < N) :
    logarithmicKernel N t = logarithmicSum t (N + 1) (2 * N + 1) := by
  rw [logarithmicSum_eq_cpow t (N + 1) (2 * N + 1) (by omega)]
  unfold logarithmicKernel
  rw [dyadicInterval_eq_Ico_succ]

section
variable (N : ℕ)
include N
theorem logarithmicKernel_eq_shifted_phaseSum (t : ℝ) (hN : 0 < N) :
    logarithmicKernel N t =
      ∑ k ∈ range N, unitaryPhase (logarithmicPhase t (N + 1 + k)) := by
  rw [logarithmicKernel_eq_logarithmicSum N t hN]
  unfold logarithmicSum phaseSum
  rw [sum_Ico_eq_sum_range]
  pm_4641 hlength N
  grind

@[simp] theorem logarithmicKernel_zero :
    logarithmicKernel N 0 = (N : ℂ) := by
  unfold logarithmicKernel
  rw [dyadicInterval_eq_Ico_succ]
  simp only [ofReal_zero, neg_zero, zero_mul, Complex.cpow_zero, sum_const,
    nsmul_eq_mul, Nat.card_Ico, mul_one]
  exact_mod_cast (show 2 * N + 1 - (N + 1) = N by omega)

theorem norm_logarithmicKernel_zero :
    ‖logarithmicKernel N 0‖ = (N : ℝ) := by simp_all

/-- Reversing the frequency conjugates the logarithmic kernel. -/
theorem logarithmicKernel_neg (t : ℝ) :
    logarithmicKernel N (-t) = star (logarithmicKernel N t) := by
  unfold logarithmicKernel
  change (∑ n ∈ dyadicInterval N, (n : ℂ) ^ (-((-t : ℝ) : ℂ) * I)) =
    starRingEnd ℂ (∑ n ∈ dyadicInterval N, (n : ℂ) ^ (-(t : ℂ) * I))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  pm_4835
  rw [← unitaryPhase_logarithmicPhase_eq_cpow (-t) n hnPos,
    ← unitaryPhase_logarithmicPhase_eq_cpow t n hnPos]
  unfold unitaryPhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [logarithmicPhase, ofReal_neg, ofReal_mul, map_mul, map_neg, conj_I,
    Complex.conj_ofReal]
  ring_nf

theorem norm_logarithmicKernel_abs (t : ℝ) :
    ‖logarithmicKernel N |t|‖ = ‖logarithmicKernel N t‖ := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht, logarithmicKernel_neg, norm_star]
end

private theorem log_succ_sub_log_bounds (m : ℕ) (hm : 0 < m) :
    1 / ((m : ℝ) + 1) ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) ∧
      Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) ≤ 1 / (m : ℝ) := by
  pm_4642
  · calc
      1 / ((m : ℝ) + 1) =
          1 - ((((m + 1 : ℕ) : ℝ) / (m : ℝ))⁻¹) := by grind
      _ ≤ Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) :=
        Real.one_sub_inv_le_log_of_pos hratio
      _ = Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := hlog
  · rw [← hlog]
    calc
      Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) ≤
          ((m + 1 : ℕ) : ℝ) / (m : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos hratio
      _ = 1 / (m : ℝ) := by grind

/-- The first-derivative estimate for the dyadic logarithmic kernel.  Its
numerical factor is deliberately generous; the decisive feature is harmonic decay in
the frequency. -/
theorem norm_logarithmicKernel_le_div
    (N : ℕ) (t : ℝ) (hN : 0 < N) (htOne : 1 ≤ |t|)
    (htN : |t| ≤ (N : ℝ)) :
    ‖logarithmicKernel N t‖ ≤ 6 * Real.pi * (N : ℝ) / |t| := by
  let q := |t|
  have hq : 0 < q := lt_of_lt_of_le zero_lt_one htOne
  pm_456 hNReal N hN
  let δ := q / (3 * (N : ℝ))
  pm_4644
  have hinc (n : ℕ) (hn : n ≤ N - 1) :
      let m := N + 1 + n
      δ ≤ logarithmicPhase q (m + 1) - logarithmicPhase q m + 2 * Real.pi ∧
        logarithmicPhase q (m + 1) - logarithmicPhase q m + 2 * Real.pi ≤
          2 * Real.pi - δ := by
    dsimp only
    let m := N + 1 + n
    pm_4647 hm m
    have hmLower : N + 1 ≤ m := by dsimp only [m]; omega
    have hmUpper : m + 1 ≤ 3 * N := by dsimp only [m]; omega
    have hlogs := log_succ_sub_log_bounds m hm
    pm_4646 q
    pm_456 hmReal m hm
    have hmLowerReal : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast (hmLower.trans' (Nat.le_add_right N 1))
    have hmUpperReal : ((m : ℝ) + 1) ≤ 3 * (N : ℝ) := by exact_mod_cast hmUpper
    pm_8184 hqOverM q htN.trans
    pm_995 N
    have hdeltaLog : δ ≤ q *
        (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) := by
      have hrecip : 1 / (3 * (N : ℝ)) ≤ 1 / ((m : ℝ) + 1) := by
        exact one_div_le_one_div_of_le (by positivity) hmUpperReal
      dsimp only [δ]
      simpa only [div_eq_mul_inv, one_mul] using
        (mul_le_mul_of_nonneg_left hrecip hq.le).trans
          (mul_le_mul_of_nonneg_left hlogs.1 hq.le)
    constructor
    · have hlogUpper : q *
          (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) ≤ 1 := by
        exact (mul_le_mul_of_nonneg_left hlogs.2 hq.le).trans (by
          simpa only [div_eq_mul_inv, one_mul] using hqOverM)
      nlinarith [Real.pi_gt_three]
    · linarith
  have hmono : ∀ n < N - 1,
      logarithmicPhase q (N + 1 + n + 1) - logarithmicPhase q (N + 1 + n) ≤
        logarithmicPhase q (N + 1 + n + 2) -
          logarithmicPhase q (N + 1 + n + 1) := by
    pm_8947 N
    pm_4643
    pm_4645 q
  have hKL := kusminLandau_interval (fun n : ℕ => logarithmicPhase q n)
    (N + 1) (N - 1)
    (-1) δ hδ
    (fun n hn => by
      simpa only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, sub_neg_eq_add,
        Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc] using (hinc n hn).1)
    (fun n hn => by
      simpa only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, sub_neg_eq_add,
        Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc] using (hinc n hn).2)
    (fun n hn => by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc] using hmono n hn)
  pm_4648 N hKL
  norm_num only [Nat.cast_add, Nat.cast_one] at hKL
  have hkernel := logarithmicKernel_eq_shifted_phaseSum N q hN
  pm_8297 hKL
  calc
    ‖logarithmicKernel N q‖ ≤ 2 * Real.pi / δ := hKL
    _ = 6 * Real.pi * (N : ℝ) / q := by
      dsimp only [δ]
      field_simp [hq.ne', hNReal.ne']
      ring

/-- The second difference of the shifted logarithmic phase has the expected
`t / N²` curvature throughout a dyadic block. -/
theorem logarithmicPhase_secondDifference_bounds
    (N n : ℕ) (t : ℝ) (hN : 0 < N) (ht : 0 < t) (hn : n < N - 1) :
    t / (9 * (N : ℝ) ^ 2) ≤
        (logarithmicPhase t (N + 1 + (n + 2)) -
          logarithmicPhase t (N + 1 + (n + 1))) -
          (logarithmicPhase t (N + 1 + (n + 1)) -
            logarithmicPhase t (N + 1 + n)) ∧
      (logarithmicPhase t (N + 1 + (n + 2)) -
          logarithmicPhase t (N + 1 + (n + 1))) -
          (logarithmicPhase t (N + 1 + (n + 1)) -
            logarithmicPhase t (N + 1 + n)) ≤ t / (N : ℝ) ^ 2 := by
  let x : ℝ := N + 1 + n
  have hxPos : 0 < x := by
    dsimp only [x]
    positivity
  obtain ⟨xi, hxi, hxiEq⟩ := second_order_mean_value
    (logarithmicPhase t)
    (fun y => -t / y)
    (fun y => t / y ^ 2) x
    (fun y hy => hasDerivAt_logarithmicPhase t (hxPos.trans_le hy.1).ne')
    (fun y hy => by
      have hyPos : 0 < y := hxPos.trans_le hy.1
      convert (hasDerivAt_inv hyPos.ne').const_mul (-t) using 1
      all_goals simp [div_eq_mul_inv])
  pm_4649
  have hxiLower : (N : ℝ) ≤ xi := by
    calc
      (N : ℝ) ≤ (N : ℝ) + 1 + (n : ℝ) := by
        pm_1199 hnNonneg n
        linarith
      _ ≤ xi := by
        have hxilt : (N : ℝ) + 1 + (n : ℝ) < xi := by
          simpa only [x, Nat.cast_add, Nat.cast_one] using hxi.1
        exact hxilt.le
  have hxiUpper : xi ≤ 3 * (N : ℝ) := by
    have hxi' : xi < (N : ℝ) + 1 + (n : ℝ) + 2 := by
      simpa only [x, Nat.cast_add, Nat.cast_one] using hxi.2
    have hnUpper : n + 3 ≤ 2 * N := by omega
    have hnUpperReal : ((n + 3 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hnUpper
    push_cast at hnUpperReal
    linarith
  have hxiPos : 0 < xi := lt_of_lt_of_le hNreal hxiLower
  have hlower : t / (9 * (N : ℝ) ^ 2) ≤ t / xi ^ 2 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 9 * (N : ℝ) ^ 2)
      (sq_pos_of_pos hxiPos)).2
    have hsq : xi ^ 2 ≤ 9 * (N : ℝ) ^ 2 := by nlinarith
    nlinarith [ht]
  have hupper : t / xi ^ 2 ≤ t / (N : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hxiPos) (sq_pos_of_pos hNreal)).2
    have hsq : (N : ℝ) ^ 2 ≤ xi ^ 2 := by nlinarith
    nlinarith [ht]
  have hEq :
      t / xi ^ 2 =
        (logarithmicPhase t (N + 1 + (n + 2)) -
          logarithmicPhase t (N + 1 + (n + 1))) -
          (logarithmicPhase t (N + 1 + (n + 1)) -
            logarithmicPhase t (N + 1 + n)) := by
    norm_num [x] at hxiEq ⊢
    have h3 : (N : ℝ) + 1 + (n : ℝ) + 2 = (N : ℝ) + (n : ℝ) + 3 := by ring
    have h2 : (N : ℝ) + 1 + (n : ℝ) + 1 = (N : ℝ) + (n : ℝ) + 2 := by ring
    have h1 : (N : ℝ) + 1 + (n : ℝ) = (N : ℝ) + (n : ℝ) + 1 := by ring
    rw [h3, h2, h1] at hxiEq
    rw [hxiEq]
    ring_nf
  constructor
  · exact hlower.trans_eq hEq
  · exact hEq.symm.trans_le hupper

section
variable (N : ℕ) (t : ℝ) (hN : 0 < N)
include N t hN
theorem logarithmic_B_process_majorant_le (hNt : (N : ℝ) ≤ t)
    (htN : t ≤ (N : ℝ) ^ 2) :
    (((N - 1 : ℕ) : ℝ) * (t / (N : ℝ) ^ 2) / (2 * Real.pi) + 2) *
        (2 * Real.pi / Real.sqrt (t / (9 * (N : ℝ) ^ 2)) +
          2 * (Real.sqrt (t / (9 * (N : ℝ) ^ 2)) /
            (t / (9 * (N : ℝ) ^ 2)) + 1)) ≤
      100 * Real.sqrt t := by
  pm_4649
  have ht : 0 < t := lt_of_lt_of_le hNreal hNt
  let y := Real.sqrt t
  have hy : 0 < y := Real.sqrt_pos.2 ht
  have hySq : y ^ 2 = t := Real.sq_sqrt ht.le
  have hyLeN : y ≤ (N : ℝ) := by
    rw [← Real.sqrt_sq (le_of_lt hNreal)]
    exact Real.sqrt_le_sqrt htN
  have hNLeYSq : (N : ℝ) ≤ y ^ 2 := by simpa only [hySq] using hNt
  have hsqrtDenom : Real.sqrt (9 * (N : ℝ) ^ 2) = 3 * (N : ℝ) := by
    rw [show 9 * (N : ℝ) ^ 2 = (3 * (N : ℝ)) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  have hsqrtLambda : Real.sqrt (t / (9 * (N : ℝ) ^ 2)) = y / (3 * (N : ℝ)) := by
    rw [Real.sqrt_div ht.le, hsqrtDenom]
  pm_5199 hlambdaPos t N
  have hfirst :
      (((N - 1 : ℕ) : ℝ) * (t / (N : ℝ) ^ 2) / (2 * Real.pi) + 2) ≤
        t / (N : ℝ) + 2 := by
    have hpred : (((N - 1 : ℕ) : ℝ)) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N 1
    have htwoPi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hcore :
        (((N - 1 : ℕ) : ℝ) * (t / (N : ℝ) ^ 2) / (2 * Real.pi)) ≤
          t / (N : ℝ) := by
      pm_585 div_le_iff₀ Real.pi
      field_simp [hNreal.ne']
      nlinarith
    linarith
  have hsecond :
      (2 * Real.pi / Real.sqrt (t / (9 * (N : ℝ) ^ 2)) +
          2 * (Real.sqrt (t / (9 * (N : ℝ) ^ 2)) /
            (t / (9 * (N : ℝ) ^ 2)) + 1)) ≤
        30 * (N : ℝ) / y + 2 := by
    rw [Real.sqrt_div_self', hsqrtLambda]
    field_simp [hy.ne', hNreal.ne']
    nlinarith [Real.pi_lt_four]
  have hfirstNonneg :
      0 ≤ (((N - 1 : ℕ) : ℝ) * (t / (N : ℝ) ^ 2) / (2 * Real.pi) + 2) := by
    positivity
  have hsecondNonneg :
      0 ≤ 2 * Real.pi / Real.sqrt (t / (9 * (N : ℝ) ^ 2)) +
          2 * (Real.sqrt (t / (9 * (N : ℝ) ^ 2)) /
            (t / (9 * (N : ℝ) ^ 2)) + 1) := by
    positivity
  have hfirstUpperNonneg : 0 ≤ t / (N : ℝ) + 2 := by positivity
  have hmul := mul_le_mul hfirst hsecond hsecondNonneg hfirstUpperNonneg
  have htDiv : t / (N : ℝ) ≤ y := by
    rw [div_le_iff₀ hNreal]
    rw [← hySq]
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hyLeN hy.le
  have hNDiv : (N : ℝ) / y ≤ y := by
    pm_1447 div_le_iff₀ hy pow_two hNLeYSq
  have hyOne : 1 ≤ y := by
    pm_77 hNone N hN
    nlinarith [hNLeYSq]
  have hexpand :
      (t / (N : ℝ) + 2) * (30 * (N : ℝ) / y + 2) =
        30 * y + 2 * (t / (N : ℝ)) + 60 * ((N : ℝ) / y) + 4 := by
    field_simp [hNreal.ne', hy.ne']
    nlinarith [hySq]
  calc
    (((N - 1 : ℕ) : ℝ) * (t / (N : ℝ) ^ 2) / (2 * Real.pi) + 2) *
        (2 * Real.pi / Real.sqrt (t / (9 * (N : ℝ) ^ 2)) +
          2 * (Real.sqrt (t / (9 * (N : ℝ) ^ 2)) /
            (t / (9 * (N : ℝ) ^ 2)) + 1)) ≤
        (t / (N : ℝ) + 2) * (30 * (N : ℝ) / y + 2) := hmul
    _ = 30 * y + 2 * (t / (N : ℝ)) + 60 * ((N : ℝ) / y) + 4 := hexpand
    _ ≤ 100 * y := by nlinarith

/-- The `(1/2,1/2)` exponent-pair estimate for the dyadic logarithmic
correlation kernel in its finite natural range. -/
theorem norm_logarithmicKernel_le_sqrt (hNt : (N : ℝ) ≤ |t|)
    (htN : |t| ≤ (N : ℝ) ^ 2) :
    ‖logarithmicKernel N t‖ ≤ 100 * Real.sqrt |t| := by
  let q := |t|
  have hq : 0 < q := lt_of_lt_of_le (by exact_mod_cast hN) hNt
  pm_5199 hlambda q N
  have hcurvLower : ∀ n < N - 1,
      q / (9 * (N : ℝ) ^ 2) ≤
        (logarithmicPhase q (N + 1 + (n + 2)) -
          logarithmicPhase q (N + 1 + (n + 1))) -
          (logarithmicPhase q (N + 1 + (n + 1)) -
            logarithmicPhase q (N + 1 + n)) := by
    intro n hn
    exact (logarithmicPhase_secondDifference_bounds N n q hN hq hn).1
  have hcurvUpper : ∀ n < N - 1,
      (logarithmicPhase q (N + 1 + (n + 2)) -
          logarithmicPhase q (N + 1 + (n + 1))) -
          (logarithmicPhase q (N + 1 + (n + 1)) -
            logarithmicPhase q (N + 1 + n)) ≤ q / (N : ℝ) ^ 2 := by
    intro n hn
    exact (logarithmicPhase_secondDifference_bounds N n q hN hq hn).2
  have hB := vanDerCorput_B_process
    (fun n => logarithmicPhase q (N + 1 + n)) (N - 1)
    (q / (9 * (N : ℝ) ^ 2)) (q / (N : ℝ) ^ 2) hlambda
    (fun n hn => by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_ofNat, Nat.add_assoc] using
        hcurvLower n hn)
    (fun n hn => by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_ofNat, Nat.add_assoc] using
        hcurvUpper n hn)
  pm_4648 N hB
  have hkernel := logarithmicKernel_eq_shifted_phaseSum N q hN
  have hmajor := logarithmic_B_process_majorant_le N q hN hNt htN
  pm_8297 hB
  exact hB.trans hmajor
end

end GuthMaynard.NativeMoment
