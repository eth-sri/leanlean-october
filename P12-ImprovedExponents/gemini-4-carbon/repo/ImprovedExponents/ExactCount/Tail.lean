module

public import ThreeSumApsp.Sec4.Corollary31
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

@[expose] public section

namespace ImprovedExponents

open ThreeSumApsp Real Finset Set

/-! ## g₂ and basePruned -/

noncomputable def g2 (c δ : ℝ) : ℝ :=
  negMulLog (c - 1 + δ) - negMulLog (c - 1) + negMulLog (1 - δ) + δ * log 9

theorem g2_antitoneOn_right {c : ℝ} (hc : 10 ≤ c) : AntitoneOn (g2 c) (Icc 0 1) := by
  have hd {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
      HasDerivAt (g2 c) (log (9 * (1 - δ) / (c - 1 + δ))) δ := by
    have hp : 0 < c - 1 + δ := by linarith
    refine (((((hasDerivAt_negMulLog hp.ne').comp δ ((hasDerivAt_id δ).const_add _)).sub_const _).add
      ((hasDerivAt_negMulLog (sub_pos.2 h1).ne').comp δ ((hasDerivAt_id δ).const_sub 1))).add
      ((hasDerivAt_id δ).mul_const (log 9))).congr_deriv ?_
    rw [log_div (by nlinarith) hp.ne', log_mul (by norm_num) (sub_pos.2 h1).ne']; ring
  refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) (by unfold g2; fun_prop)
    (fun δ hδ => ?_) (fun δ hδ => ?_)
  · rw [interior_Icc] at hδ; exact (hd hδ.1 hδ.2).differentiableAt.differentiableWithinAt
  · rw [interior_Icc] at hδ
    rw [(hd hδ.1 hδ.2).deriv]
    have hp : 0 < c - 1 + δ := by grind
    exact log_nonpos (div_nonneg (by grind) hp.le) ((div_le_one hp).2 (by grind))

theorem g2_antitoneOn_left {δ : ℝ} (hδ : 0 ≤ δ) : AntitoneOn (fun c => g2 c δ) (Ici 1) := by
  have hd {c : ℝ} (hc : 1 < c) : HasDerivAt (fun c => g2 c δ) (log ((c - 1) / (c - 1 + δ))) c := by
    have hp : 0 < c - 1 + δ := by linarith
    refine (((((hasDerivAt_negMulLog hp.ne').comp c (((hasDerivAt_id c).sub_const 1).add_const δ)).sub
      ((hasDerivAt_negMulLog (sub_pos.2 hc).ne').comp c ((hasDerivAt_id c).sub_const 1))).add_const
      _).add_const _).congr_deriv ?_
    rw [log_div (sub_pos.2 hc).ne' hp.ne']; ring
  refine antitoneOn_of_deriv_nonpos (convex_Ici 1) (by unfold g2; fun_prop)
    (fun c hc => ?_) (fun c hc => ?_)
  · rw [interior_Ici] at hc; exact (hd hc).differentiableAt.differentiableWithinAt
  · rw [interior_Ici] at hc
    have hc' : 1 < c := hc
    have hp : 0 < c - 1 + δ := by linarith
    rw [(hd hc').deriv]
    exact log_nonpos (div_nonneg (by linarith) hp.le) ((div_le_one hp).2 (by linarith))

theorem exp_neg_negMulLog_natCast (n : ℕ) : exp (-negMulLog (n : ℝ)) = (n : ℝ) ^ n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · rw [negMulLog, neg_mul, neg_neg, exp_nat_mul, exp_log (by positivity)]

theorem mul_negMulLog_div {m : ℝ} (hm : 0 < m) (x : ℝ) :
    m * negMulLog (x / m) = negMulLog x + x * log m := by
  rw [div_eq_mul_inv, negMulLog_mul]; simp  [negMulLog]; field_simp

theorem exp_mul_g2_div {L m t : ℕ} (hm : 1 ≤ m) (hmL : m ≤ L) (ht : t ≤ m) :
    exp ((m : ℝ) * g2 (L / m) (t / m))
      = (9 : ℝ) ^ t * ((m : ℝ) ^ m * ((L - m : ℕ) : ℝ) ^ (L - m))
        / (((m - t : ℕ) : ℝ) ^ (m - t) * ((L - m + t : ℕ) : ℝ) ^ (L - m + t)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hexp : (m : ℝ) * g2 (L / m) (t / m)
      = negMulLog ((L - m + t : ℕ) : ℝ) - negMulLog ((L - m : ℕ) : ℝ) + negMulLog ((m - t : ℕ) : ℝ)
        - negMulLog (m : ℝ) + t * log 9 := by
    have e1 : (L : ℝ) / m - 1 + t / m = ((L - m + t : ℕ) : ℝ) / m := by
      push_cast [Nat.cast_sub hmL]; field_simp
    have e2 : (L : ℝ) / m - 1 = ((L - m : ℕ) : ℝ) / m := by grind
    have e3 : 1 - (t : ℝ) / m = ((m - t : ℕ) : ℝ) / m := by push_cast [Nat.cast_sub ht]; field_simp
    have hsum : ((L - m + t : ℕ) : ℝ) - ((L - m : ℕ) : ℝ) + ((m - t : ℕ) : ℝ) = m := by
      push_cast [Nat.cast_sub hmL, Nat.cast_sub ht]; ring
    rw [g2, e1, e2, e3, mul_add, mul_add, mul_sub, mul_negMulLog_div hm0, mul_negMulLog_div hm0,
      mul_negMulLog_div hm0, show (m : ℝ) * ((t : ℝ) / m * log 9) = t * log 9 by field_simp,
      show negMulLog (m : ℝ) = -((m : ℝ) * log m) by rw [negMulLog]; ring]
    linear_combination (log (m : ℝ)) * hsum
  rw [hexp, ← exp_neg_negMulLog_natCast (L - m + t), ← exp_neg_negMulLog_natCast (L - m),
    ← exp_neg_negMulLog_natCast (m - t), ← exp_neg_negMulLog_natCast m,
    ← show exp ((t : ℝ) * log 9) = (9 : ℝ) ^ t by rw [exp_nat_mul, exp_log (by norm_num)],
    ← exp_add, ← exp_add, ← exp_add, ← exp_sub]
  congr 1; ring

/-! ## Tail of leaf counts -/

theorem choose_mul_nine_pow_le {L j j₀ : ℕ} (hj : j ≤ j₀) (hL : 10 * j₀ ≤ L) :
    L.choose j * 9 ^ (j₀ - j) ≤ L.choose j₀ := by
  induction hj using Nat.decreasingInduction with
  | self => simp
  | of_succ k hk ih =>
    have hstep : L.choose k * 9 ≤ L.choose (k + 1) :=
      Nat.le_of_mul_le_mul_right (by
        rw [Nat.choose_succ_right_eq]; nlinarith [show 9 * (k + 1) ≤ L - k by omega]) k.succ_pos
    calc L.choose k * 9 ^ (j₀ - k) = L.choose k * 9 * 9 ^ (j₀ - (k + 1)) := by
          rw [show j₀ - k = j₀ - (k + 1) + 1 by omega, pow_succ]; ring
      _ ≤ L.choose (k + 1) * 9 ^ (j₀ - (k + 1)) := Nat.mul_le_mul_right _ hstep
      _ ≤ L.choose j₀ := ih

theorem beta_le_exp {L m t d : ℕ} (hm : 1 ≤ m) (hL : 10 * m ≤ L) (htd : t ≤ d) (hdm : d ≤ m) :
    (beta L m d : ℝ) ≤ ((L : ℝ) + 1) * (M L m : ℝ) * exp ((m : ℝ) * g2 (L / m) (t / m)) := by
  have hmL : m ≤ L := by omega
  have ht : t ≤ m := htd.trans hdm
  have h1 : L.choose (m - d) * 9 ^ (d - t) ≤ L.choose (m - t) := by
    simpa [show m - t - (m - d) = d - t by omega] using
      choose_mul_nine_pow_le (L := L) (j := m - d) (j₀ := m - t) (by omega) (by omega)
  have h2 : L.choose (m - t) * (m - t) ^ (m - t) * (L - m + t) ^ (L - m + t) ≤ L ^ L := by
    simpa [show L - (m - t) = L - m + t by omega, show m - t + (L - m + t) = L by omega] using
      Nat.choose_mul_pow_mul_pow_le (m - t) (L - m + t) L (m - t)
  have h3 := Nat.pow_self_le_mul_choose_mul_pow_mul_pow hmL
  have hM : M L m = L.choose m * 9 ^ (L - m) := by rw [← beta_zero_eq_M, beta_zero]
  have hb : beta L m d = L.choose (m - d) * 9 ^ (d - t) * (9 ^ t * 9 ^ (L - m)) := by
    rw [beta, mul_assoc, ← pow_add, ← pow_add]; congr 2; omega
  have hnat : beta L m d * ((m - t) ^ (m - t) * (L - m + t) ^ (L - m + t))
      ≤ (L + 1) * (M L m * (9 ^ t * (m ^ m * (L - m) ^ (L - m)))) :=
    calc beta L m d * ((m - t) ^ (m - t) * (L - m + t) ^ (L - m + t))
        = L.choose (m - d) * 9 ^ (d - t) * ((m - t) ^ (m - t) * (L - m + t) ^ (L - m + t))
            * (9 ^ t * 9 ^ (L - m)) := by rw [hb]; ring
      _ ≤ L.choose (m - t) * ((m - t) ^ (m - t) * (L - m + t) ^ (L - m + t))
            * (9 ^ t * 9 ^ (L - m)) := by gcongr
      _ = L.choose (m - t) * (m - t) ^ (m - t) * (L - m + t) ^ (L - m + t)
            * (9 ^ t * 9 ^ (L - m)) := by ring
      _ ≤ L ^ L * (9 ^ t * 9 ^ (L - m)) := Nat.mul_le_mul_right _ h2
      _ ≤ (L + 1) * (L.choose m * m ^ m * (L - m) ^ (L - m)) * (9 ^ t * 9 ^ (L - m)) :=
          Nat.mul_le_mul_right _ h3
      _ = _ := by rw [hM]; ring
  have hX : (0 : ℝ) < ((m - t : ℕ) : ℝ) ^ (m - t) * ((L - m + t : ℕ) : ℝ) ^ (L - m + t) := by
    exact_mod_cast Nat.mul_pos Nat.pow_self_pos (Nat.pow_pos (by omega))
  rw [exp_mul_g2_div hm hmL ht, mul_div_assoc', le_div_iff₀ hX]
  exact (show (beta L m d : ℝ) * (((m - t : ℕ) : ℝ) ^ (m - t) * ((L - m + t : ℕ) : ℝ) ^ (L - m + t))
    ≤ ((L : ℝ) + 1) * (M L m * (9 ^ t * (m ^ m * ((L - m : ℕ) : ℝ) ^ (L - m)))) by
      exact_mod_cast hnat).trans_eq (by ring)

noncomputable def gammaX (c θ : ℝ) : ℝ := -g2 c θ / log 4

theorem sum_beta_le_rpow {c θ : ℝ} (hc : 10 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {m : ℕ}
    (hm : 1 ≤ m) :
    ∑ d ∈ Finset.Icc (switchOf θ m) m, (beta (levelsOf c m) m d : ℝ)
      ≤ ((m : ℝ) + 1) * (((levelsOf c m : ℝ) + 1) * (M (levelsOf c m) m : ℝ)
        * (D m : ℝ) ^ (-gammaX c θ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hL : c ≤ (levelsOf c m : ℝ) / m := (le_div_iff₀ hm0).2 (Nat.le_ceil _)
  have ht : θ ≤ (switchOf θ m : ℝ) / m := (le_div_iff₀ hm0).2 (Nat.le_ceil _)
  have ht1 : (switchOf θ m : ℝ) / m ≤ 1 := (div_le_one hm0).2 (by exact_mod_cast switchOf_le hθ1 m)
  have ht0 : 0 ≤ (switchOf θ m : ℝ) / m := by positivity
  have hg : g2 (levelsOf c m / m) (switchOf θ m / m) ≤ g2 c θ :=
    (g2_antitoneOn_left ht0 (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith)) hL).trans
      (g2_antitoneOn_right hc.le ⟨hθ0, hθ1⟩ ⟨ht0, ht1⟩ ht)
  have hexp : exp ((m : ℝ) * g2 (levelsOf c m / m) (switchOf θ m / m)) ≤ (D m : ℝ) ^ (-gammaX c θ) := by
    refine (exp_le_exp.2 (mul_le_mul_of_nonneg_left hg hm0.le)).trans_eq ?_
    rw [cast_D_rpow]; congr 1; unfold gammaX; field_simp
  have hL10 := ten_mul_le_levelsOf hc m
  calc ∑ d ∈ Finset.Icc (switchOf θ m) m, (beta (levelsOf c m) m d : ℝ)
      ≤ ∑ _d ∈ Finset.Icc (switchOf θ m) m,
          ((levelsOf c m : ℝ) + 1) * (M (levelsOf c m) m : ℝ) *
            exp ((m : ℝ) * g2 (levelsOf c m / m) (switchOf θ m / m)) :=
        sum_le_sum fun d hd => beta_le_exp hm hL10 (mem_Icc.1 hd).1 (mem_Icc.1 hd).2
    _ = ((m + 1 - switchOf θ m : ℕ) : ℝ) * _ := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
    _ ≤ ((m : ℝ) + 1) * (((levelsOf c m : ℝ) + 1) * (M (levelsOf c m) m : ℝ)
          * (D m : ℝ) ^ (-gammaX c θ)) := by
        have hsub : ((m + 1 - switchOf θ m : ℕ) : ℝ) ≤ (m : ℝ) + 1 := by
          exact_mod_cast Nat.sub_le (m + 1) _
        refine (mul_le_mul_of_nonneg_right hsub (by positivity)).trans ?_
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (by positivity)) (by positivity)

/-! ## Thinness bound and basePruned -/

noncomputable def thinR (A γ : ℝ) : ℝ := log 4 / (A + γ * log 4)
noncomputable def basePruned (c : ℝ) : ℝ := c / 2 * entropy (1 / c) + (c - 1) * log 3
noncomputable def RcP (c γ : ℝ) : ℝ := thinR (basePruned c) γ
noncomputable def cEntropy (c : ℝ) : ℝ := negMulLog (c - 1) - negMulLog c

theorem thinR_den_pos {A γ : ℝ} (hA : 0 < A) (hγ : 0 ≤ γ) : 0 < A + γ * log 4 :=
  add_pos_of_pos_of_nonneg hA (mul_nonneg hγ log_four_pos.le)


theorem basePruned_eq {c : ℝ} (hc : 1 < c) :
    basePruned c = 1 / 2 * cEntropy c + (c - 1) * log 3 := by
  have hc0 : 0 < c := by linarith
  have h1 : 1 - 1 / c = (c - 1) / c := by field_simp
  rw [basePruned, entropy, h1, log_div (sub_pos.2 hc).ne' hc0.ne', one_div, log_inv]
  simp  [cEntropy, negMulLog]; field_simp; ring

theorem basePruned_pos {c : ℝ} (hc : 1 < c) : 0 < basePruned c := by
  have hc0 : 0 < c := by linarith
  have hH := entropy_nonneg (by positivity : 0 ≤ 1 / c) ((div_le_one hc0).2 hc.le)
  have h3 : 0 < (c - 1) * log 3 := mul_pos (sub_pos.2 hc) (log_pos (by norm_num))
  unfold basePruned; nlinarith

theorem basePruned_continuousOn : ContinuousOn basePruned (Ioi 10) := by
  have h : Continuous fun c : ℝ => 1 / 2 * cEntropy c + (c - 1) * log 3 := by
    unfold cEntropy; fun_prop
  exact (h.continuousOn.congr fun x (hx : 1 < x) => basePruned_eq hx).mono
    (Ioi_subset_Ioi (by norm_num))

theorem K_le_exp {L m : ℕ} (hm : 1 ≤ m) (hmL : m ≤ L) :
    (K L m : ℝ) ≤ exp ((m : ℝ) * cEntropy ((L : ℝ) / m)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hexp : (m : ℝ) * cEntropy ((L : ℝ) / m)
      = negMulLog ((L - m : ℕ) : ℝ) - negMulLog (L : ℝ) + negMulLog (m : ℝ) := by
    have e1 : (L : ℝ) / m - 1 = ((L - m : ℕ) : ℝ) / m := by push_cast [Nat.cast_sub hmL]; field_simp
    have hsub : ((L - m : ℕ) : ℝ) - (L : ℝ) = -(m : ℝ) := by grind
    rw [cEntropy, e1, mul_sub, mul_negMulLog_div hm0, mul_negMulLog_div hm0]
    simp  [negMulLog]; linear_combination (log (m : ℝ)) * hsub
  have hval : exp ((m : ℝ) * cEntropy ((L : ℝ) / m))
      = (L : ℝ) ^ L / (((L - m : ℕ) : ℝ) ^ (L - m) * (m : ℝ) ^ m) := by
    rw [hexp, ← exp_neg_negMulLog_natCast (L - m), ← exp_neg_negMulLog_natCast L,
      ← exp_neg_negMulLog_natCast m, ← exp_add, ← exp_sub]
    congr 1; ring
  have hpos : (0 : ℝ) < ((L - m : ℕ) : ℝ) ^ (L - m) * (m : ℝ) ^ m := by
    exact_mod_cast Nat.mul_pos Nat.pow_self_pos (Nat.pow_pos (by omega))
  rw [hval, le_div_iff₀ hpos, K]
  have h := Nat.choose_mul_pow_mul_pow_le m (L - m) L m
  rw [Nat.add_sub_cancel' hmL] at h
  linarith [show (L.choose m : ℝ) * (m : ℝ) ^ m * ((L - m : ℕ) : ℝ) ^ (L - m) ≤ (L : ℝ) ^ L by
    exact_mod_cast h]

theorem sqrtKN0_le_exp {L m : ℕ} (hm : 1 ≤ m) (hmL : m < L) :
    sqrtKN0 L m ≤ exp ((m : ℝ) * basePruned ((L : ℝ) / m)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hLm : (1 : ℝ) < (L : ℝ) / m := (one_lt_div hm0).2 (by exact_mod_cast hmL)
  have hsqrt : Real.sqrt (K L m : ℝ) ≤ exp ((m : ℝ) * cEntropy ((L : ℝ) / m) / 2) := by
    rw [show exp ((m : ℝ) * cEntropy ((L : ℝ) / m) / 2)
        = Real.sqrt (exp ((m : ℝ) * cEntropy ((L : ℝ) / m))) by
      rw [Real.sqrt_eq_rpow, ← Real.exp_mul]; congr 1; ring]
    exact Real.sqrt_le_sqrt (K_le_exp hm hmL.le)
  have hN0 : (N0 L m : ℝ) = exp (((L : ℝ) - m) * log 3) := by
    rw [N0, Nat.cast_pow, ← Nat.cast_sub hmL.le, exp_nat_mul, exp_log (by norm_num)]; norm_num
  rw [sqrtKN0, basePruned_eq hLm, hN0]
  exact (mul_le_mul_of_nonneg_right hsqrt (exp_pos _).le).trans_eq <| by
    rw [← exp_add]; congr 1; field_simp

end ImprovedExponents
