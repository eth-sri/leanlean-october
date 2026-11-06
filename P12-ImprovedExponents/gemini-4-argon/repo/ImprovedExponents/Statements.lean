module

public import ThreeSumApsp.Sec4.Corollary31
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import ImprovedExponents.PrunedProgram.Wrapper.Program
public import ThreeSumApsp.Sec2.Orders
public import ThreeSumApsp.Programs.Sec4.Theorem30.WordSize
public import ImprovedExponents.PrunedProgram.Pre.Defs
public import ThreeSumApsp.Programs.Sec4.Theorem30.Time
public import ImprovedExponents.Pipeline.HostBound
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Costs
public import ThreeSumApsp.Spec.Sec3.Theorem17.Parameters
public import ThreeSumApsp.Sec4.Table2.LogBounds
public import ImprovedExponents.AllEdges.Chain
public import ImprovedExponents.AllEdges.Host.ClaimAE

@[expose] public section

namespace ImprovedExponents

open ThreeSumApsp Real Set Finset

noncomputable def g2 (c δ : ℝ) : ℝ :=
  negMulLog (c - 1 + δ) - negMulLog (c - 1) + negMulLog (1 - δ) + δ * log 9

theorem continuous_g2_right (c : ℝ) : Continuous (g2 c) := by
  unfold g2
  fun_prop

theorem continuous_g2_left (δ : ℝ) : Continuous fun c => g2 c δ := by
  unfold g2
  fun_prop

theorem hasDerivAt_g2_right {c δ : ℝ} (hc : 1 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    HasDerivAt (g2 c) (log (9 * (1 - δ) / (c - 1 + δ))) δ := by
  have hpos : 0 < c - 1 + δ := by linarith
  have h1 : HasDerivAt (fun δ : ℝ => negMulLog (c - 1 + δ)) ((-log (c - 1 + δ) - 1) * 1) δ :=
    (hasDerivAt_negMulLog hpos.ne').comp δ ((hasDerivAt_id δ).const_add (c - 1))
  have h2 : HasDerivAt (fun δ : ℝ => negMulLog (1 - δ)) ((-log (1 - δ) - 1) * (-1)) δ :=
    (hasDerivAt_negMulLog (sub_pos.2 hδ1).ne').comp δ ((hasDerivAt_id δ).const_sub 1)
  have h3 : HasDerivAt (fun δ : ℝ => δ * log 9) (1 * log 9) δ :=
    (hasDerivAt_id δ).mul_const (log 9)
  have h : HasDerivAt (g2 c) _ δ := ((h1.sub_const (negMulLog (c - 1))).add h2).add h3
  refine h.congr_deriv ?_
  rw [log_div (by nlinarith) hpos.ne', log_mul (by norm_num) (sub_pos.2 hδ1).ne']
  ring

theorem hasDerivAt_g2_left {c δ : ℝ} (hc : 1 < c) (hδ : 0 ≤ δ) :
    HasDerivAt (fun c => g2 c δ) (log ((c - 1) / (c - 1 + δ))) c := by
  have hpos : 0 < c - 1 + δ := by linarith
  have h1 : HasDerivAt (negMulLog ∘ fun c : ℝ => c - 1 + δ) ((-log (c - 1 + δ) - 1) * 1) c :=
    (hasDerivAt_negMulLog hpos.ne').comp c (((hasDerivAt_id c).sub_const 1).add_const δ)
  have h2 : HasDerivAt (negMulLog ∘ fun c : ℝ => c - 1) ((-log (c - 1) - 1) * 1) c :=
    (hasDerivAt_negMulLog (sub_pos.2 hc).ne').comp c ((hasDerivAt_id c).sub_const 1)
  have h : HasDerivAt (fun c => g2 c δ) _ c :=
    ((h1.sub h2).add_const (negMulLog (1 - δ))).add_const (δ * log 9)
  refine h.congr_deriv ?_
  rw [log_div (sub_pos.2 hc).ne' hpos.ne']
  ring

theorem g2_antitoneOn_right {c : ℝ} (hc : 10 ≤ c) : AntitoneOn (g2 c) (Set.Icc 0 1) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) (continuous_g2_right c).continuousOn ?_ ?_
  · intro δ hδ
    rw [interior_Icc] at hδ
    exact (hasDerivAt_g2_right (by linarith) hδ.1 hδ.2).differentiableAt.differentiableWithinAt
  · intro δ hδ
    rw [interior_Icc] at hδ
    obtain ⟨hδ0, hδ1⟩ := hδ
    rw [(hasDerivAt_g2_right (by linarith) hδ0 hδ1).deriv]
    have hpos : 0 < c - 1 + δ := by linarith
    refine log_nonpos (div_nonneg (by nlinarith) hpos.le) ?_
    rw [div_le_one hpos]
    linarith

theorem g2_antitoneOn_left {δ : ℝ} (hδ : 0 ≤ δ) : AntitoneOn (fun c => g2 c δ) (Set.Ici 1) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 1) (continuous_g2_left δ).continuousOn ?_ ?_
  · intro c hc
    rw [interior_Ici] at hc
    exact (hasDerivAt_g2_left hc hδ).differentiableAt.differentiableWithinAt
  · intro c hc
    rw [interior_Ici] at hc
    have hc' : 1 < c := hc
    rw [(hasDerivAt_g2_left hc' hδ).deriv]
    have hpos : 0 < c - 1 + δ := by linarith
    refine log_nonpos (div_nonneg (by linarith) hpos.le) ?_
    rw [div_le_one hpos]
    linarith

theorem exp_neg_negMulLog_natCast (n : ℕ) : exp (-negMulLog (n : ℝ)) = (n : ℝ) ^ n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [negMulLog, neg_mul, neg_neg, exp_nat_mul, exp_log hn']

theorem mul_negMulLog_div {m : ℝ} (hm : 0 < m) (x : ℝ) :
    m * negMulLog (x / m) = negMulLog x + x * log m := by
  rw [div_eq_mul_inv, negMulLog_mul]
  simp only [negMulLog, log_inv]
  field_simp

theorem exp_mul_g2_div {L m t : ℕ} (hm : 1 ≤ m) (hmL : m ≤ L) (ht : t ≤ m) :
    exp ((m : ℝ) * g2 (L / m) (t / m))
      = (9 : ℝ) ^ t * ((m : ℝ) ^ m * ((L - m : ℕ) : ℝ) ^ (L - m))
        / (((m - t : ℕ) : ℝ) ^ (m - t) * ((L - m + t : ℕ) : ℝ) ^ (L - m + t)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have e1 : (L : ℝ) / m - 1 + t / m = ((L - m + t : ℕ) : ℝ) / m := by
    push_cast [Nat.cast_sub hmL]; field_simp
  have e2 : (L : ℝ) / m - 1 = ((L - m : ℕ) : ℝ) / m := by
    push_cast [Nat.cast_sub hmL]; field_simp
  have e3 : 1 - (t : ℝ) / m = ((m - t : ℕ) : ℝ) / m := by
    push_cast [Nat.cast_sub ht]; field_simp
  have hsum : ((L - m + t : ℕ) : ℝ) - ((L - m : ℕ) : ℝ) + ((m - t : ℕ) : ℝ) = m := by
    push_cast [Nat.cast_sub hmL, Nat.cast_sub ht]; ring
  have hlog : negMulLog (m : ℝ) = -((m : ℝ) * log m) := by rw [negMulLog]; ring
  have ht9 : (m : ℝ) * ((t : ℝ) / m * log 9) = t * log 9 := by field_simp
  have hdiv : (m : ℝ) * g2 (L / m) (t / m)
      = negMulLog ((L - m + t : ℕ) : ℝ) - negMulLog ((L - m : ℕ) : ℝ) + negMulLog ((m - t : ℕ) : ℝ)
        - negMulLog (m : ℝ) + t * log 9 := by
    rw [g2, e1, e2, e3, mul_add, mul_add, mul_sub, mul_negMulLog_div hm0, mul_negMulLog_div hm0,
      mul_negMulLog_div hm0, hlog, ht9]
    linear_combination (log (m : ℝ)) * hsum
  have h9 : exp ((t : ℝ) * log 9) = (9 : ℝ) ^ t := by rw [exp_nat_mul, exp_log (by norm_num)]
  have hA := exp_neg_negMulLog_natCast (L - m + t)
  have hB := exp_neg_negMulLog_natCast (L - m)
  have hC := exp_neg_negMulLog_natCast (m - t)
  have hD := exp_neg_negMulLog_natCast m
  rw [hdiv, ← hA, ← hB, ← hC, ← hD, ← h9, ← exp_add, ← exp_add, ← exp_add, ← exp_sub]
  congr 1
  ring

theorem choose_mul_nine_pow_le {L j j₀ : ℕ} (hj : j ≤ j₀) (hL : 10 * j₀ ≤ L) :
    L.choose j * 9 ^ (j₀ - j) ≤ L.choose j₀ := by
  induction hj using Nat.decreasingInduction with
  | self => simp
  | of_succ k hk ih =>
    have hstep : L.choose k * 9 ≤ L.choose (k + 1) := by
      refine Nat.le_of_mul_le_mul_right ?_ (Nat.succ_pos k)
      rw [Nat.choose_succ_right_eq]
      calc L.choose k * 9 * (k + 1) = L.choose k * (9 * (k + 1)) := by ring
        _ ≤ L.choose k * (L - k) := Nat.mul_le_mul_left _ (by omega)
    calc L.choose k * 9 ^ (j₀ - k) = L.choose k * 9 * 9 ^ (j₀ - (k + 1)) := by
          rw [show j₀ - k = j₀ - (k + 1) + 1 by omega, pow_succ]
          ring
      _ ≤ L.choose (k + 1) * 9 ^ (j₀ - (k + 1)) := Nat.mul_le_mul_right _ hstep
      _ ≤ L.choose j₀ := ih

theorem M_eq (L m : ℕ) : M L m = L.choose m * 9 ^ (L - m) := by
  rw [← beta_zero_eq_M, beta_zero]

theorem beta_mul_le {L m t d : ℕ} (hL : 10 * m ≤ L) (htd : t ≤ d) (hdm : d ≤ m) :
    beta L m d * ((m - t) ^ (m - t) * (L - m + t) ^ (L - m + t))
      ≤ (L + 1) * (M L m * (9 ^ t * (m ^ m * (L - m) ^ (L - m)))) := by
  have hmL : m ≤ L := by omega
  have h1 : L.choose (m - d) * 9 ^ (d - t) ≤ L.choose (m - t) := by
    have h := choose_mul_nine_pow_le (L := L) (j := m - d) (j₀ := m - t) (by omega) (by omega)
    rwa [show m - t - (m - d) = d - t by omega] at h
  have h2 : L.choose (m - t) * (m - t) ^ (m - t) * (L - m + t) ^ (L - m + t) ≤ L ^ L := by
    have h := Nat.choose_mul_pow_mul_pow_le (m - t) (L - m + t) L (m - t)
    rwa [show L - (m - t) = L - m + t by omega, show m - t + (L - m + t) = L by omega] at h
  have h3 := Nat.pow_self_le_mul_choose_mul_pow_mul_pow hmL
  have hb : beta L m d = L.choose (m - d) * 9 ^ (d - t) * (9 ^ t * 9 ^ (L - m)) := by
    rw [beta, mul_assoc, ← pow_add, ← pow_add]
    congr 2
    omega
  calc beta L m d * ((m - t) ^ (m - t) * (L - m + t) ^ (L - m + t))
      = L.choose (m - d) * 9 ^ (d - t) * ((m - t) ^ (m - t) * (L - m + t) ^ (L - m + t)
          * (9 ^ t * 9 ^ (L - m))) := by rw [hb]; ring
    _ ≤ L.choose (m - t) * ((m - t) ^ (m - t) * (L - m + t) ^ (L - m + t)
          * (9 ^ t * 9 ^ (L - m))) := Nat.mul_le_mul_right _ h1
    _ = L.choose (m - t) * (m - t) ^ (m - t) * (L - m + t) ^ (L - m + t)
          * (9 ^ t * 9 ^ (L - m)) := by ring
    _ ≤ L ^ L * (9 ^ t * 9 ^ (L - m)) := Nat.mul_le_mul_right _ h2
    _ ≤ (L + 1) * (L.choose m * m ^ m * (L - m) ^ (L - m)) * (9 ^ t * 9 ^ (L - m)) :=
        Nat.mul_le_mul_right _ h3
    _ = (L + 1) * (M L m * (9 ^ t * (m ^ m * (L - m) ^ (L - m)))) := by rw [M_eq]; ring

theorem beta_le_exp {L m t d : ℕ} (hm : 1 ≤ m) (hL : 10 * m ≤ L) (htd : t ≤ d) (hdm : d ≤ m) :
    (beta L m d : ℝ) ≤ ((L : ℝ) + 1) * (M L m : ℝ) * exp ((m : ℝ) * g2 (L / m) (t / m)) := by
  have hmL : m ≤ L := by omega
  have ht : t ≤ m := htd.trans hdm
  have hX : (0 : ℝ) < ((m - t : ℕ) : ℝ) ^ (m - t) * ((L - m + t : ℕ) : ℝ) ^ (L - m + t) := by
    have h : 0 < (m - t) ^ (m - t) * (L - m + t) ^ (L - m + t) :=
      Nat.mul_pos (Nat.pow_self_pos) (Nat.pow_pos (by omega))
    exact_mod_cast h
  have hcast : (beta L m d : ℝ)
      * (((m - t : ℕ) : ℝ) ^ (m - t) * ((L - m + t : ℕ) : ℝ) ^ (L - m + t))
      ≤ ((L : ℝ) + 1) * ((M L m : ℝ)
        * ((9 : ℝ) ^ t * ((m : ℝ) ^ m * ((L - m : ℕ) : ℝ) ^ (L - m)))) := by
    exact_mod_cast beta_mul_le hL htd hdm
  rw [exp_mul_g2_div hm hmL ht]
  calc (beta L m d : ℝ)
      = (beta L m d : ℝ) * (((m - t : ℕ) : ℝ) ^ (m - t) * ((L - m + t : ℕ) : ℝ) ^ (L - m + t))
          / (((m - t : ℕ) : ℝ) ^ (m - t) * ((L - m + t : ℕ) : ℝ) ^ (L - m + t)) :=
        (mul_div_cancel_right₀ _ hX.ne').symm
    _ ≤ ((L : ℝ) + 1) * ((M L m : ℝ) * ((9 : ℝ) ^ t * ((m : ℝ) ^ m * ((L - m : ℕ) : ℝ) ^ (L - m))))
          / (((m - t : ℕ) : ℝ) ^ (m - t) * ((L - m + t : ℕ) : ℝ) ^ (L - m + t)) :=
        div_le_div_of_nonneg_right hcast hX.le
    _ = _ := by ring

noncomputable def gammaX (c θ : ℝ) : ℝ := -g2 c θ / log 4

theorem sum_beta_le_rpow {c θ : ℝ} (hc : 10 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {m : ℕ}
    (hm : 1 ≤ m) :
    ∑ d ∈ Finset.Icc (switchOf θ m) m, (beta (levelsOf c m) m d : ℝ)
      ≤ ((m : ℝ) + 1) * (((levelsOf c m : ℝ) + 1) * (M (levelsOf c m) m : ℝ)
        * (D m : ℝ) ^ (-gammaX c θ)) := by
  set L := levelsOf c m
  set t := switchOf θ m
  have hL10 : 10 * m ≤ L := ten_mul_le_levelsOf hc m
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hL : c ≤ (L : ℝ) / m := (le_div_iff₀ hm0).2 (Nat.le_ceil _)
  have ht : θ ≤ (t : ℝ) / m := (le_div_iff₀ hm0).2 (Nat.le_ceil _)
  have ht1 : (t : ℝ) / m ≤ 1 := (div_le_one hm0).2 (by exact_mod_cast switchOf_le hθ1 m)
  have ht0 : 0 ≤ (t : ℝ) / m := by positivity
  have hstep1 : g2 (L / m) (t / m) ≤ g2 c (t / m) :=
    g2_antitoneOn_left ht0 (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 (by linarith)) hL
  have hstep2 : g2 c (t / m) ≤ g2 c θ :=
    g2_antitoneOn_right hc.le ⟨hθ0, hθ1⟩ ⟨ht0, ht1⟩ ht
  have hexp : exp ((m : ℝ) * g2 (L / m) (t / m)) ≤ (D m : ℝ) ^ (-gammaX c θ) := by
    rw [cast_D_rpow, show -gammaX c θ * ((m : ℝ) * log 4) = (m : ℝ) * g2 c θ by
      have := log_four_pos.ne'; unfold gammaX; field_simp]
    exact exp_le_exp.2 (mul_le_mul_of_nonneg_left (hstep1.trans hstep2) hm0.le)
  have hnonneg : 0 ≤ ((L : ℝ) + 1) * (M L m : ℝ) * exp ((m : ℝ) * g2 (L / m) (t / m)) := by
    positivity
  calc ∑ d ∈ Finset.Icc t m, (beta L m d : ℝ)
      ≤ ∑ _d ∈ Finset.Icc t m, ((L : ℝ) + 1) * (M L m : ℝ) * exp ((m : ℝ) * g2 (L / m) (t / m)) :=
        sum_le_sum fun d hd => beta_le_exp hm hL10 (Finset.mem_Icc.1 hd).1 (Finset.mem_Icc.1 hd).2
    _ = ((m + 1 - t : ℕ) : ℝ)
          * (((L : ℝ) + 1) * (M L m : ℝ) * exp ((m : ℝ) * g2 (L / m) (t / m))) := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
    _ ≤ ((m : ℝ) + 1) * (((L : ℝ) + 1) * (M L m : ℝ) * exp ((m : ℝ) * g2 (L / m) (t / m))) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le (m + 1) t) hnonneg
    _ ≤ ((m : ℝ) + 1) * (((L : ℝ) + 1) * (M L m : ℝ) * (D m : ℝ) ^ (-gammaX c θ)) := by gcongr

noncomputable def thinR (A γ : ℝ) : ℝ := log 4 / (A + γ * log 4)

noncomputable def cEntropy (c : ℝ) : ℝ := negMulLog (c - 1) - negMulLog c

noncomputable def basePruned (c : ℝ) : ℝ := 1 / 2 * cEntropy c + (c - 1) * log 3

noncomputable def RcP (c γ : ℝ) : ℝ := thinR (basePruned c) γ

theorem thinR_den_pos {A γ : ℝ} (hA : 0 < A) (hγ : 0 ≤ γ) : 0 < A + γ * log 4 :=
  add_pos_of_pos_of_nonneg hA (mul_nonneg hγ log_four_pos.le)

theorem thinR_pos {A γ : ℝ} (hA : 0 < A) (hγ : 0 ≤ γ) : 0 < thinR A γ :=
  div_pos log_four_pos (thinR_den_pos hA hγ)

theorem basePruned_pos {c : ℝ} (hc : 1 < c) : 0 < basePruned c := by
  have hc1 : 0 < c - 1 := sub_pos.2 hc
  have : log (c - 1) ≤ log c := log_le_log hc1 (by linarith)
  have : 0 < log c := log_pos hc
  have : 0 < log 3 := log_pos (by norm_num)
  have heq : basePruned c =
      1 / 2 * ((c - 1) * (log c - log (c - 1)) + log c) + (c - 1) * log 3 := by
    unfold basePruned cEntropy negMulLog
    ring
  rw [heq]
  nlinarith




noncomputable def tailX (L m t : ℕ) : ℝ := (∑ d ∈ Finset.Icc t m, (beta L m d : ℝ)) / (M L m : ℝ)

theorem tailX_nonneg (L m t : ℕ) : 0 ≤ tailX L m t :=
  div_nonneg (sum_nonneg fun _ _ => Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem cost8X_first_term_nonneg (L m t N : ℕ) :
    0 ≤ (L : ℝ) * (m : ℝ) * tailX L m t * (N : ℝ) ^ 2 :=
  mul_nonneg (mul_nonneg (by positivity) (tailX_nonneg L m t)) (by positivity)

theorem boxes_costX {L m t N : ℕ} (hm : 1 ≤ m) (hL : 10 * m ≤ L) (ht : t ≤ m)
    (hN : sqrtKN0 L m ≤ N) :
    (L : ℝ) * ((numBands L m N : ℝ) ^ 2 * ((boxes L m t).card : ℝ))
      ≤ 8 * ((L : ℝ) * (m : ℝ) * tailX L m t * (N : ℝ) ^ 2) := by
  have hboxes : ((boxes L m t).card : ℝ)
      ≤ ((m : ℝ) + 1) * ∑ d ∈ Finset.Icc t m, (beta L m d : ℝ) := by
    exact_mod_cast lemma_29_count L m t hL ht
  have : (0 : ℝ) ≤ ∑ d ∈ Finset.Icc t m, (beta L m d : ℝ) :=
    sum_nonneg fun _ _ => Nat.cast_nonneg _
  have htot : ((numBands L m N : ℝ)) ^ 2 * ((boxes L m t).card : ℝ)
      ≤ 4 * ((m : ℝ) + 1) * tailX L m t * (N : ℝ) ^ 2 :=
    calc ((numBands L m N : ℝ)) ^ 2 * ((boxes L m t).card : ℝ)
        ≤ (4 * (N : ℝ) ^ 2 / (M L m : ℝ))
            * (((m : ℝ) + 1) * ∑ d ∈ Finset.Icc t m, (beta L m d : ℝ)) :=
          mul_le_mul (Theorem30.tiles hm hL hN) hboxes (Nat.cast_nonneg _) (by positivity)
      _ = 4 * ((m : ℝ) + 1) * tailX L m t * (N : ℝ) ^ 2 := by unfold tailX; ring
  have := tailX_nonneg L m t
  have : (1 : ℝ) ≤ m := by exact_mod_cast hm
  calc (L : ℝ) * ((numBands L m N : ℝ) ^ 2 * ((boxes L m t).card : ℝ))
      ≤ (L : ℝ) * (4 * ((m : ℝ) + 1) * tailX L m t * (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left htot (Nat.cast_nonneg L)
    _ ≤ (L : ℝ) * (4 * (2 * (m : ℝ)) * tailX L m t * (N : ℝ) ^ 2) := by
        gcongr
        linarith
    _ = 8 * ((L : ℝ) * (m : ℝ) * tailX L m t * (N : ℝ) ^ 2) := by ring

/-- The tail at the parameters of Corollary 31: `tailX ≤ (m + 1)(L + 1) D^{-γX(c, θ)}`. -/
theorem tailX_le_rpow {c θ : ℝ} (hc : 10 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    tailX (levelsOf c m) m (switchOf θ m)
      ≤ ((m : ℝ) + 1) * (((levelsOf c m : ℝ) + 1) * (D m : ℝ) ^ (-gammaX c θ)) := by
  have hmL : m ≤ levelsOf c m := by have := ten_mul_le_levelsOf hc m; omega
  have hM : (0 : ℝ) < M (levelsOf c m) m :=
    sqrtKN0_sq (levelsOf c m) m ▸ pow_pos (sqrtKN0_pos hmL) 2
  unfold tailX
  rw [div_le_iff₀ hM]
  exact (sum_beta_le_rpow hc hθ0 hθ1 hm).trans (le_of_eq (by ring))

/-- `m² D^{-δ} ≤ 2/(δ ln 4)²` for `δ > 0` and `D = 4^m`: a power of `D` pays for `log² D`. -/
theorem sq_mul_D_rpow_le {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    (m : ℝ) ^ 2 * (D m : ℝ) ^ (-δ) ≤ 2 / (δ * log 4) ^ 2 := by
  have hlog := log_four_pos
  have hx : 0 ≤ δ * ((m : ℝ) * log 4) := by positivity
  have hexp := quadratic_le_exp_of_nonneg hx
  rw [cast_D_rpow, show -δ * ((m : ℝ) * log 4) = -(δ * ((m : ℝ) * log 4)) by ring, exp_neg,
    ← div_eq_mul_inv, div_le_div_iff₀ (exp_pos _) (by positivity)]
  have hsq : (m : ℝ) ^ 2 * (δ * log 4) ^ 2 = (δ * ((m : ℝ) * log 4)) ^ 2 := by ring
  rw [hsq]
  linarith

/-- **The first term of `cost8X`** for general `c` and `θ`, and every `γ` below the exact exponent
`γX(c, θ)`: it is `O(N² log² D/D^γ)`. The common factor `N²` is left out. This takes the place of
`ThreeSumApsp.Corollary31.first_term`. -/
theorem first_termX {c θ γ : ℝ} (hc : 10 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hγ : γ < gammaX c θ) :
    Dominated (fun m : ℕ => 1 ≤ m)
      (fun m => (levelsOf c m : ℝ) * m * tailX (levelsOf c m) m (switchOf θ m))
      fun m => (D m : ℝ) ^ (-γ) * Real.log (D m) ^ 2 := by
  have : (0 : ℝ) < c := by linarith
  have hδ : 0 < gammaX c θ - γ := sub_pos.2 hγ
  have := log_four_pos
  refine .of_le_const_mul (C := 2 * (c + 1) * (c + 2) * (2 / ((gammaX c θ - γ) * log 4) ^ 2))
    (by positivity) fun m hm => ?_
  have : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hL : (levelsOf c m : ℝ) ≤ (c + 1) * m := levelsOf_le hc hm
  have htail := tailX_le_rpow hc hθ0 hθ1 hm
  have hsplit : (D m : ℝ) ^ (-gammaX c θ)
      = (D m : ℝ) ^ (-(gammaX c θ - γ)) * (D m : ℝ) ^ (-γ) := by
    rw [← rpow_add (cast_D_pos m)]
    congr 1
    ring
  have hpow : (0 : ℝ) ≤ (D m : ℝ) ^ (-gammaX c θ) := rpow_nonneg (Nat.cast_nonneg _) _
  have : (0 : ℝ) ≤ (D m : ℝ) ^ (-γ) := rpow_nonneg (Nat.cast_nonneg _) _
  have : (m : ℝ) ≤ Real.log (D m) := cast_le_log_cast_D m
  calc (levelsOf c m : ℝ) * m * tailX (levelsOf c m) m (switchOf θ m)
      ≤ (c + 1) * m * m * (((m : ℝ) + 1) * (((levelsOf c m : ℝ) + 1)
          * (D m : ℝ) ^ (-gammaX c θ))) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg m)) htail
          (tailX_nonneg _ _ _) (by positivity)
    _ ≤ (c + 1) * m * m * ((2 * (m : ℝ)) * (((c + 2) * m) * (D m : ℝ) ^ (-gammaX c θ))) := by
        gcongr <;> linarith
    _ = 2 * (c + 1) * (c + 2) * ((m : ℝ) ^ 2 * (D m : ℝ) ^ (-(gammaX c θ - γ)))
          * ((D m : ℝ) ^ (-γ) * (m : ℝ) ^ 2) := by
        rw [hsplit]
        ring
    _ ≤ 2 * (c + 1) * (c + 2) * (2 / ((gammaX c θ - γ) * log 4) ^ 2)
          * ((D m : ℝ) ^ (-γ) * Real.log (D m) ^ 2) := by
        have := sq_mul_D_rpow_le hδ m
        gcongr

/-! ### The second term: inequality (10) for every exponent -/

-- adapted from upstream `ThreeSumApsp/Sec4/Corollary31.lean` (`eq_10`), where the exponent is
-- `gammaOf c θ`; the proof uses only that it is not negative

/-! ### The two terms together -/






open Light Light.Sec4


theorem K_le_exp {L m : ℕ} (hm : 1 ≤ m) (hmL : m ≤ L) :
    (K L m : ℝ) ≤ exp ((m : ℝ) * cEntropy ((L : ℝ) / m)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hexp : (m : ℝ) * cEntropy ((L : ℝ) / m)
      = negMulLog ((L - m : ℕ) : ℝ) - negMulLog (L : ℝ) + negMulLog (m : ℝ) := by
    have e1 : (L : ℝ) / m - 1 = ((L - m : ℕ) : ℝ) / m := by
      push_cast [Nat.cast_sub hmL]
      field_simp
    have hsub : ((L - m : ℕ) : ℝ) - (L : ℝ) = -(m : ℝ) := by
      push_cast [Nat.cast_sub hmL]
      ring
    have hlog : negMulLog (m : ℝ) = -((m : ℝ) * log m) := by rw [negMulLog]; ring
    rw [cEntropy, e1, mul_sub, mul_negMulLog_div hm0, mul_negMulLog_div hm0, hlog]
    linear_combination (log (m : ℝ)) * hsub
  have hA := exp_neg_negMulLog_natCast (L - m)
  have hB := exp_neg_negMulLog_natCast L
  have hC := exp_neg_negMulLog_natCast m
  have hval : exp ((m : ℝ) * cEntropy ((L : ℝ) / m))
      = (L : ℝ) ^ L / (((L - m : ℕ) : ℝ) ^ (L - m) * (m : ℝ) ^ m) := by
    rw [hexp, ← hA, ← hB, ← hC, ← exp_add, ← exp_sub]
    congr 1
    ring
  have hpos : (0 : ℝ) < ((L - m : ℕ) : ℝ) ^ (L - m) * (m : ℝ) ^ m := by
    have h : 0 < (L - m) ^ (L - m) * m ^ m := Nat.mul_pos Nat.pow_self_pos (Nat.pow_pos (by omega))
    exact_mod_cast h
  rw [hval, le_div_iff₀ hpos]
  have hnat : L.choose m * m ^ m * (L - m) ^ (L - m) ≤ L ^ L := by
    have h := Nat.choose_mul_pow_mul_pow_le m (L - m) L m
    rwa [Nat.add_sub_cancel' hmL] at h
  have hcast : (L.choose m : ℝ) * (m : ℝ) ^ m * ((L - m : ℕ) : ℝ) ^ (L - m) ≤ (L : ℝ) ^ L := by
    exact_mod_cast hnat
  calc (K L m : ℝ) * (((L - m : ℕ) : ℝ) ^ (L - m) * (m : ℝ) ^ m)
      = (L.choose m : ℝ) * (m : ℝ) ^ m * ((L - m : ℕ) : ℝ) ^ (L - m) := by
        rw [K]
        ring
    _ ≤ (L : ℝ) ^ L := hcast

theorem sqrtKN0_le_exp {L m : ℕ} (hm : 1 ≤ m) (hmL : m < L) :
    sqrtKN0 L m ≤ exp ((m : ℝ) * basePruned ((L : ℝ) / m)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hK := K_le_exp hm hmL.le
  have hsqrt : Real.sqrt (K L m : ℝ) ≤ exp ((m : ℝ) * cEntropy ((L : ℝ) / m) / 2) := by
    rw [show exp ((m : ℝ) * cEntropy ((L : ℝ) / m) / 2)
        = Real.sqrt (exp ((m : ℝ) * cEntropy ((L : ℝ) / m))) by
      rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
      congr 1
      ring]
    exact Real.sqrt_le_sqrt hK
  have hN0 : (N0 L m : ℝ) = exp (((L : ℝ) - m) * log 3) := by
    rw [N0, Nat.cast_pow, ← Nat.cast_sub hmL.le, exp_nat_mul, exp_log (by norm_num)]
    norm_num
  rw [sqrtKN0, basePruned, hN0]
  calc Real.sqrt (K L m : ℝ) * exp (((L : ℝ) - m) * log 3)
      ≤ exp ((m : ℝ) * cEntropy ((L : ℝ) / m) / 2) * exp (((L : ℝ) - m) * log 3) :=
        mul_le_mul_of_nonneg_right hsqrt (exp_pos _).le
    _ = exp ((m : ℝ) * (1 / 2 * cEntropy ((L : ℝ) / m) + ((L : ℝ) / m - 1) * log 3)) := by
        rw [← exp_add]
        congr 1
        field_simp

noncomputable def cost8P (L m t N : ℕ) : ℝ :=
  (L : ℝ) * (m : ℝ) * tailX L m t * (N : ℝ) ^ 2
    + (N : ℝ) * (L : ℝ) * (27 / 2 * (M L m : ℝ) / (1 - rho L m)) / sqrtKN0 L m

theorem encodingP_eq {L m : ℕ} (hmL : m ≤ L) (N : ℕ) :
    (N : ℝ) * (L : ℝ) * (27 / 2 * (M L m : ℝ) / (1 - rho L m)) / sqrtKN0 L m
      = 27 / 2 * (N : ℝ) * ((L : ℝ) * sqrtKN0 L m) / (1 - rho L m) := by
  have := (sqrtKN0_pos hmL).ne'
  have h : sqrtKN0 L m ^ 2 * (sqrtKN0 L m)⁻¹ = sqrtKN0 L m := by field_simp
  rw [← sqrtKN0_sq]
  simp only [div_eq_mul_inv]
  linear_combination ((N : ℝ) * (L : ℝ) * (27 / 2) * (1 - rho L m)⁻¹) * h

theorem eq_10P {c γ ε : ℝ} (hc : 10 < c) (hγ : 0 ≤ γ) (hε0 : 0 < ε) (hε : ε < RcP c γ) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ D₀ N : ℕ, 4 ^ (m - 1) < D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
      (D m : ℝ) ^ γ * ((levelsOf c m : ℝ) * sqrtKN0 (levelsOf c m) m) ≤ (N : ℝ) := by
  have hlog4 := log_four_pos
  have hA : 0 < basePruned c := basePruned_pos (by linarith)
  have hden : 0 < basePruned c + γ * log 4 := thinR_den_pos hA hγ
  have hε' : ε < log 4 / (basePruned c + γ * log 4) := hε
  set G : ℝ := log 4 / ε with hGdef
  have hG : basePruned c + γ * log 4 < G := by
    rw [hGdef, lt_div_iff₀ hε0]
    have := (lt_div_iff₀ hden).1 hε'
    linarith
  set B : ℝ := (basePruned c + (G - γ * log 4)) / 2 with hBdef
  have hB1 : basePruned c < B := by rw [hBdef]; linarith
  set η : ℝ := G - γ * log 4 - B with hηdef
  have hη : 0 < η := by rw [hηdef, hBdef]; linarith
  have hcont : ContinuousAt basePruned c :=
    (by unfold basePruned cEntropy; fun_prop : Continuous basePruned).continuousAt
  obtain ⟨δ₀, hδ₀, hnear⟩ := Metric.eventually_nhds_iff.1
    (hcont.eventually (gt_mem_nhds hB1))
  refine ⟨max 1 (max ⌈1 / δ₀⌉₊ ⌈2 * (c + 1) * exp G / η ^ 2⌉₊),
    fun m hm D₀ N hgt hthin => ?_⟩
  have hm1 : 1 ≤ m := (le_max_left _ _).trans hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmδ : 1 / δ₀ ≤ (m : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_left _ _).trans ((le_max_right _ _).trans hm))
  have hmη : 2 * (c + 1) * exp G / η ^ 2 ≤ (m : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hm))
  have hLge : c * m ≤ (levelsOf c m : ℝ) := Nat.le_ceil _
  have hLlt : (levelsOf c m : ℝ) < c * m + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmL : m < levelsOf c m := by
    have h : (m : ℝ) < (levelsOf c m : ℝ) := by nlinarith
    exact_mod_cast h
  have hratio1 : c ≤ (levelsOf c m : ℝ) / m := by rwa [le_div_iff₀ hm0]
  have hratio2 : (levelsOf c m : ℝ) / m < c + δ₀ := by
    rw [div_lt_iff₀ hm0]
    have : 1 ≤ δ₀ * m := by
      have := (div_le_iff₀ hδ₀).1 hmδ
      linarith
    nlinarith
  have hbase : basePruned ((levelsOf c m : ℝ) / m) < B := by
    refine hnear ?_
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hLle : (levelsOf c m : ℝ) ≤ (c + 1) * m := levelsOf_le hc hm1
  have hsqrt : sqrtKN0 (levelsOf c m) m ≤ exp ((m : ℝ) * B) :=
    (sqrtKN0_le_exp hm1 hmL).trans (exp_le_exp.2 (mul_le_mul_of_nonneg_left hbase.le hm0.le))
  have hN : exp (((m : ℝ) - 1) * G) ≤ (N : ℝ) := by
    have h := Corollary31.hypothesis hm1 hε0 hgt hthin
    rwa [rpow_def_of_pos (by norm_num),
      show log 4 * (((m : ℝ) - 1) / ε) = ((m : ℝ) - 1) * (log 4 / ε) by ring] at h
  have hexp : (c + 1) * m * exp G ≤ exp ((m : ℝ) * η) := by
    have := quadratic_le_exp_of_nonneg (mul_nonneg hm0.le hη.le)
    have h1 : 2 * (c + 1) * exp G ≤ (m : ℝ) * η ^ 2 := by
      have := (div_le_iff₀ (pow_pos hη 2)).1 hmη
      linarith
    have := mul_le_mul_of_nonneg_left h1 hm0.le
    have : 0 ≤ (m : ℝ) * η := mul_nonneg hm0.le hη.le
    linarith
  have hE : exp (γ * ((m : ℝ) * log 4)) * exp ((m : ℝ) * B)
      = exp G * exp ((m : ℝ) * (B + γ * log 4) - G) := by
    rw [← exp_add, ← exp_add]
    congr 1
    ring
  calc (D m : ℝ) ^ γ * ((levelsOf c m : ℝ) * sqrtKN0 (levelsOf c m) m)
      ≤ exp (γ * ((m : ℝ) * log 4)) * ((c + 1) * m * exp ((m : ℝ) * B)) := by
        rw [cast_D_rpow]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hLle hsqrt (sqrtKN0_pos hmL.le).le (by positivity)) (exp_pos _).le
    _ = (c + 1) * m * (exp (γ * ((m : ℝ) * log 4)) * exp ((m : ℝ) * B)) := by ring
    _ = (c + 1) * m * exp G * exp ((m : ℝ) * (B + γ * log 4) - G) := by
        rw [hE]
        ring
    _ ≤ exp ((m : ℝ) * η) * exp ((m : ℝ) * (B + γ * log 4) - G) :=
        mul_le_mul_of_nonneg_right hexp (exp_pos _).le
    _ = exp (((m : ℝ) - 1) * G) := by
        rw [← exp_add, hηdef]
        congr 1
        ring
    _ ≤ (N : ℝ) := hN

theorem exists_fitsRS {a b p q : ℕ} (hb : 1 ≤ b) (hq : 1 ≤ q) (hc : 10 * b < a)
    (hθ : 10 * p < 9 * q) {r : ℕ} (hr : 1 ≤ r) (h : basePruned ((a : ℝ) / b) < (r : ℝ) * log 4) :
    ∃ m₂ : ℕ, ∀ (m₀ : ℕ), 1 ≤ m₀ → m₂ ≤ m₀ →
      FitsRS ⟨a, b, p, q, m₀, hb, hq, hc, hθ⟩ r := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hcR : (10 : ℝ) < (a : ℝ) / b := by rw [lt_div_iff₀ hbR]; exact_mod_cast hc
  have hε : 1 / (r : ℝ) < RcP ((a : ℝ) / b) 0 := by
    unfold RcP thinR
    rw [zero_mul, add_zero, div_lt_div_iff₀ hrR (basePruned_pos (by linarith))]
    linarith
  obtain ⟨m₂, heq10⟩ := eq_10P hcR le_rfl (by positivity) hε
  refine ⟨m₂, fun m₀ hm₀ hm₂ N D₀ hN hm => ?_⟩
  have hm1 : 1 ≤ logFour D₀ := le_trans hm₀ hm
  have : 2 ≤ D₀ := two_le_of_clog hm1
  have hpow : 4 ^ (logFour D₀ - 1) < D₀ := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hDN : (D₀ : ℝ) ≤ (N : ℝ) ^ (1 / (r : ℝ)) := by
    rw [one_div, le_rpow_inv_iff_of_pos (by positivity) (by positivity) hrR, rpow_natCast]
    exact_mod_cast hN
  have h10 := heq10 (logFour D₀) (le_trans hm₂ hm) D₀ N hpow hDN
  rw [rpow_zero, one_mul] at h10
  have := ten_mul_le_levelsOf hcR (logFour D₀)
  have hL1 : (1 : ℝ) ≤ (levelsOf ((a : ℝ) / b) (logFour D₀) : ℝ) := Nat.one_le_cast.2 (by omega)
  have hs0 : 0 ≤ sqrtKN0 (levelsOf ((a : ℝ) / b) (logFour D₀)) (logFour D₀) :=
    (sqrtKN0_pos (by omega)).le
  refine ⟨hm1, RatParams.ten_le_L _ _, RatParams.t_le _ _, ?_⟩
  change sqrtKN0 (parOf ⟨a, b, p, q, m₀, hb, hq, hc, hθ⟩ N D₀).L (logFour D₀) ≤ (N : ℝ)
  rw [show (parOf ⟨a, b, p, q, m₀, hb, hq, hc, hθ⟩ N D₀).L =
    levelsOf ((a : ℝ) / b) (logFour D₀) from (levelsOf_div a _ hb).symm]
  exact (le_mul_of_one_le_left hs0 hL1).trans h10

theorem dominated_cost8P {c θ γ : ℝ} (hc : 10 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hγ : γ < gammaX c θ) {dom : Sizes → Prop} (hset : ∀ p, dom p → p.SetUp)
    (h10 : ∀ p, dom p →
      (D p.m : ℝ) ^ γ * ((levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m) ≤ p.N) :
    Dominated dom (fun p => cost8P (levelsOf c p.m) p.m (switchOf θ p.m) p.N)
      fun p => (p.N : ℝ) ^ 2 * Real.log p.D₀ ^ 2 / (p.D₀ : ℝ) ^ γ := by
  have hρ : rhoC c < 1 := rhoC_lt_one hc
  have hboxes : Dominated dom
      (fun p => (levelsOf c p.m : ℝ) * p.m * tailX (levelsOf c p.m) p.m (switchOf θ p.m)
        * (p.N : ℝ) ^ 2)
      fun p => (D p.m : ℝ) ^ (-γ) * Real.log (D p.m) ^ 2 * (p.N : ℝ) ^ 2 :=
    ((first_termX hc hθ0 hθ1 hγ).comp Sizes.m fun p hp => (hset p hp).m_pos).mul_right
      (k := fun p => (p.N : ℝ) ^ 2) fun _ _ => sq_nonneg _
  have hencodings : Dominated dom
      (fun p => (p.N : ℝ) * (levelsOf c p.m : ℝ)
        * (27 / 2 * (M (levelsOf c p.m) p.m : ℝ) / (1 - rho (levelsOf c p.m) p.m))
        / sqrtKN0 (levelsOf c p.m) p.m)
      fun p => (D p.m : ℝ) ^ (-γ) * Real.log (D p.m) ^ 2 * (p.N : ℝ) ^ 2 := by
    refine .of_le_const_mul (C := 27 / 2 / (1 - rhoC c))
      (div_nonneg (by norm_num) (sub_pos.2 hρ).le) fun p hp => ?_
    have hm1 : 1 ≤ p.m := (hset p hp).m_pos
    have hmL : p.m ≤ levelsOf c p.m := by have := ten_mul_le_levelsOf hc p.m; omega
    have : rho (levelsOf c p.m) p.m < rhoC c := Corollary31.rho_lt hc p.m
    have hDγ : 0 < (D p.m : ℝ) ^ γ := rpow_pos_of_pos (cast_D_pos p.m) γ
    have hLs0 : 0 ≤ (levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m :=
      mul_nonneg (Nat.cast_nonneg _) (sqrtKN0_pos hmL).le
    have hLs : (levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m
        ≤ (D p.m : ℝ) ^ (-γ) * p.N := by
      rw [rpow_neg (cast_D_pos p.m).le, inv_mul_eq_div, le_div_iff₀ hDγ, mul_comm]
      exact h10 p hp
    have hlog : (1 : ℝ) ≤ Real.log (D p.m) ^ 2 :=
      one_le_pow₀ ((Nat.one_le_cast.2 hm1).trans (cast_le_log_cast_D p.m))
    have hpow : (0 : ℝ) ≤ (D p.m : ℝ) ^ (-γ) := rpow_nonneg (Nat.cast_nonneg _) _
    rw [encodingP_eq hmL]
    calc 27 / 2 * (p.N : ℝ) * ((levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m)
          / (1 - rho (levelsOf c p.m) p.m)
        ≤ 27 / 2 * (p.N : ℝ) * ((levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m)
          / (1 - rhoC c) :=
          div_le_div_of_nonneg_left (mul_nonneg (by positivity) hLs0) (sub_pos.2 hρ)
            (by linarith)
      _ ≤ 27 / 2 * (p.N : ℝ) * ((D p.m : ℝ) ^ (-γ) * p.N) / (1 - rhoC c) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLs (by positivity))
            (sub_pos.2 hρ).le
      _ = 27 / 2 / (1 - rhoC c) * ((D p.m : ℝ) ^ (-γ) * 1 * (p.N : ℝ) ^ 2) := by ring
      _ ≤ 27 / 2 / (1 - rhoC c)
            * ((D p.m : ℝ) ^ (-γ) * Real.log (D p.m) ^ 2 * (p.N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlog hpow) (sq_nonneg _))
            (div_nonneg (by norm_num) (sub_pos.2 hρ).le)
  have hpadded : Dominated dom (fun p => cost8P (levelsOf c p.m) p.m (switchOf θ p.m) p.N)
      fun p => (D p.m : ℝ) ^ (-γ) * Real.log (D p.m) ^ 2 * (p.N : ℝ) ^ 2 :=
    hboxes.add hencodings
  refine (hpadded.trans (((padded_le (-γ) 2).mono_dom hset).mul_right
    fun _ _ => sq_nonneg _)).congr (fun _ _ => rfl) fun p _ => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg _)]
  ring

theorem costsP {c θ γ ε : ℝ} (hc : 10 < c) (hθ0 : 0 < θ) (hθ1 : θ < 0.9) (hγ0 : 0 ≤ γ)
    (hγ : γ < gammaX c θ) (hε0 : 0 < ε) (hε : ε < RcP c γ) :
    ∃ (C : ℝ) (m₀ : ℕ), 0 ≤ C ∧ ∀ D₀ N m : ℕ, 2 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
      m = ⌈Real.logb 4 (D₀ : ℝ)⌉₊ → m₀ ≤ m →
      sqrtKN0 (levelsOf c m) m ≤ N ∧
      cost8P (levelsOf c m) m (switchOf θ m) N
        ≤ C * ((N : ℝ) ^ 2 * Real.log (D₀ : ℝ) ^ 2 / (D₀ : ℝ) ^ γ) ∧
      costQuery (levelsOf c m) m (switchOf θ m) ≤ C * ((D₀ : ℝ) ^ qOf θ * Real.log (D₀ : ℝ)) := by
  obtain ⟨m₀, heq10⟩ := eq_10P hc hγ0 hε0 hε
  have h10 : ∀ p : Sizes, p.Corollary31 ε m₀ →
      (D p.m : ℝ) ^ γ * ((levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m) ≤ p.N :=
    fun p hp => heq10 p.m hp.large p.D₀ p.N hp.setUp.gt hp.thin
  have hpre := dominated_cost8P hc hθ0.le (by linarith) hγ
    (fun p (hp : p.Corollary31 ε m₀) => hp.setUp) h10
  have hquery : Dominated (Sizes.Corollary31 ε m₀)
      (fun p => costQuery (levelsOf c p.m) p.m (switchOf θ p.m))
      fun p => (p.D₀ : ℝ) ^ qOf θ * Real.log p.D₀ :=
    (((Corollary31.query_cost hc hθ0 hθ1).comp Sizes.m fun _ (hp : Sizes.SetUp _) => hp.m_pos).trans
      (by simpa only [pow_one] using padded_le (qOf θ) 1)).mono_dom fun p hp => hp.setUp
  obtain ⟨C, hC, hboth⟩ := hpre.exists_const_and hquery
    (fun p _ => div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    fun p hp => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.log_nonneg (Nat.one_le_cast.2 (one_le_two.trans hp.setUp.two_le)))
  refine ⟨C, m₀, hC, fun D₀ N m hD hDN hm hm₀ => ?_⟩
  have hp : Sizes.Corollary31 ε m₀ ⟨D₀, N, m⟩ := ⟨⟨hD, hm⟩, hDN, hm₀⟩
  have : 1 ≤ m := hp.setUp.m_pos
  have : 10 * m ≤ levelsOf c m := ten_mul_le_levelsOf hc m
  have hD1 : (1 : ℝ) ≤ (D m : ℝ) ^ γ := Real.one_le_rpow (one_le_cast_D m) hγ0
  have hL1 : (1 : ℝ) ≤ (levelsOf c m : ℝ) := Nat.one_le_cast.2 (by omega)
  have hs : 0 ≤ sqrtKN0 (levelsOf c m) m := (sqrtKN0_pos (by omega)).le
  have hfit : sqrtKN0 (levelsOf c m) m ≤ N :=
    calc sqrtKN0 (levelsOf c m) m
        ≤ (levelsOf c m : ℝ) * sqrtKN0 (levelsOf c m) m := le_mul_of_one_le_left hs hL1
      _ ≤ (D m : ℝ) ^ γ * ((levelsOf c m : ℝ) * sqrtKN0 (levelsOf c m) m) :=
          le_mul_of_one_le_left (mul_nonneg (by positivity) hs) hD1
      _ ≤ N := h10 ⟨D₀, N, m⟩ hp
  exact ⟨hfit, hboth ⟨D₀, N, m⟩ hp⟩


/-!
# The pruned preprocessing of Theorem 30 runs within `cost8P`

`ImprovedExponents.Cost8X.Within` shows that upstream's preprocessing of Theorem 30 takes at most
a constant times `cost8X`, the expression (8) with the exact tail of the leaf counts. This file
repeats that analysis for the pruned preprocessing, whose time function `tPreCoreP` has the shape
`sharedShapeP` of the pruned shared stage: the work `encWorkP L m` of the pruned encoder takes the
place of the `10^L` cells of a full encoding. The cost is `cost8P`, whose second summand

  `N L (27/2) M/(1 - ρ)/(√K N₀)`

replaces the `N 10^L/(√K N₀)` of `cost8X`: `Within8P`, and `exists_tPreCore_leP`.

`cost8P` has no standalone `10^L` term, so the small summands of the shared stage (the tables, the
list of subsets, the directory, the digit tables) cannot be absorbed into one as upstream does
(`sharedShape_le`). They are bounded by `N L √K N₀`, which is at most `2/27` of the second
summand (`base_le_cost8P`): `K ≤ N₀`, `D ≤ N₀`, `L ≤ 10 N₀` for `10 m ≤ L` (`K_le_N0`, `D_le_N0`,
`L_le_ten_mul_N0`). The work of the pruned encoder is at most `(9/2) M/(1 - ρ)`
(`encWorkP_le_M_div`), and the input array of a band takes `O(L 7^L)` with `7^L ≤ 9^{L-m} ≤ M`
(`seven_pow_le_M`), so that the bands cost `O(N L M/((1 - ρ) √K N₀))`, the second summand. The
tries of all tiles are as in `Cost8X.Within` (`boxes_costX`, upstream's private
`exists_tTile_le`).

The statements and proofs are adapted from upstream
`ThreeSumApsp/Programs/Sec4/Theorem30/Time.lean` and `TimeOfBlock.lean` (Apache-2.0) and from
`ImprovedExponents/Cost8X/Within.lean`.
-/


open ThreeSumApsp.Spec Light.Sec4

/-! ### Powers for `10 m ≤ L` -/

/-- For `a^10 ≤ b^9` and `10 m ≤ L`: `a^L ≤ b^{L-m}`, because `10 (L - m) ≥ 9 L`. -/
theorem pow_le_pow_sub_of_ten_mul_le {a b L m : ℕ} (hb : 0 < b) (hab : a ^ 10 ≤ b ^ 9)
    (hL : 10 * m ≤ L) : a ^ L ≤ b ^ (L - m) := by
  rw [← Nat.pow_le_pow_iff_left (by norm_num : (10 : ℕ) ≠ 0)]
  calc (a ^ L) ^ 10 = (a ^ 10) ^ L := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ (b ^ 9) ^ L := Nat.pow_le_pow_left hab L
    _ = b ^ (9 * L) := by rw [← pow_mul]
    _ ≤ b ^ (10 * (L - m)) := Nat.pow_le_pow_right hb (by omega)
    _ = (b ^ (L - m)) ^ 10 := by rw [← pow_mul, mul_comm]

/-- `K = binom(L, m) ≤ 2^L ≤ 3^{L-m} = N₀` for `10 m ≤ L`. -/
theorem K_le_N0 {L m : ℕ} (hL : 10 * m ≤ L) : K L m ≤ N0 L m :=
  (Nat.choose_le_two_pow L m).trans (pow_le_pow_sub_of_ten_mul_le (by norm_num) (by norm_num) hL)

/-- `D = 4^m ≤ 3^{9m} ≤ 3^{L-m} = N₀` for `10 m ≤ L`. -/
theorem D_le_N0 {L m : ℕ} (hL : 10 * m ≤ L) : D m ≤ N0 L m :=
  calc D m = 4 ^ m := rfl
    _ ≤ (3 ^ 9) ^ m := Nat.pow_le_pow_left (by norm_num) m
    _ = 3 ^ (9 * m) := by rw [← pow_mul]
    _ ≤ 3 ^ (L - m) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `L ≤ 10 (L - m) ≤ 10 N₀` for `10 m ≤ L`. -/
theorem L_le_ten_mul_N0 {L m : ℕ} (hL : 10 * m ≤ L) : L ≤ 10 * N0 L m :=
  calc L ≤ 10 * (L - m) := by omega
    _ ≤ 10 * 3 ^ (L - m) := Nat.mul_le_mul_left _ (Nat.lt_pow_self (by norm_num)).le

/-- `7^L ≤ 9^{L-m} = N₀² ≤ K N₀² = M` for `10 m ≤ L`. -/
theorem seven_pow_le_M {L m : ℕ} (hL : 10 * m ≤ L) : 7 ^ L ≤ M L m :=
  calc 7 ^ L ≤ 9 ^ (L - m) := pow_le_pow_sub_of_ten_mul_le (by norm_num) (by norm_num) hL
    _ = N0 L m ^ 2 := by
        change (3 ^ 2) ^ (L - m) = (3 ^ (L - m)) ^ 2
        rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ K L m * N0 L m ^ 2 := Nat.le_mul_of_pos_left _ (Nat.choose_pos (by omega))

/-! ### The second summand of `cost8P` -/

/-- `√K N₀ ≥ N₀ ≥ 1`. -/
theorem one_le_sqrtKN0 {L m : ℕ} (hmL : m ≤ L) : 1 ≤ sqrtKN0 L m := by
  have hK : (1 : ℝ) ≤ Real.sqrt (K L m : ℝ) :=
    Real.one_le_sqrt.2 (by exact_mod_cast Nat.choose_pos hmL)
  have hN0 : (1 : ℝ) ≤ (N0 L m : ℝ) := by exact_mod_cast N0_pos L m
  exact one_le_mul_of_one_le_of_one_le hK hN0

/-- `N₀ ≤ √K N₀`. -/
theorem N0_le_sqrtKN0 {L m : ℕ} (hmL : m ≤ L) : (N0 L m : ℝ) ≤ sqrtKN0 L m := by
  have hK : (1 : ℝ) ≤ Real.sqrt (K L m : ℝ) :=
    Real.one_le_sqrt.2 (by exact_mod_cast Nat.choose_pos hmL)
  exact le_mul_of_one_le_left (Nat.cast_nonneg _) hK

/-- The second summand of `cost8P` is not negative. -/
theorem cost8P_second_term_nonneg {L m : ℕ} (hL : 10 * m ≤ L) (N : ℕ) :
    0 ≤ (N : ℝ) * (L : ℝ) * (27 / 2 * (M L m : ℝ) / (1 - rho L m)) / sqrtKN0 L m := by
  have hρ := sec4_rho_lt_one L m hL
  have := sqrtKN0_pos (L := L) (m := m) (by omega)
  have : 0 ≤ 27 / 2 * (M L m : ℝ) / (1 - rho L m) :=
    div_nonneg (by positivity) (sub_pos.2 hρ).le
  positivity

/-- **The base `N L √K N₀`**: the second summand of `cost8P` is at least `(27/2) N L √K N₀`,
because `M/√K N₀ = √K N₀` and `1/(1 - ρ) ≥ 1`. -/
theorem base_le_cost8P {L m : ℕ} (hL : 10 * m ≤ L) (t N : ℕ) :
    27 / 2 * ((N : ℝ) * (L : ℝ) * sqrtKN0 L m) ≤ cost8P L m t N := by
  have := cost8X_first_term_nonneg L m t N
  have hρ0 := rho_nonneg hL
  have hρ1 := sec4_rho_lt_one L m hL
  have := (sqrtKN0_pos (L := L) (m := m) (by omega)).le
  have : 0 ≤ (N : ℝ) * ((L : ℝ) * sqrtKN0 L m) := by positivity
  have : 27 / 2 * ((N : ℝ) * (L : ℝ) * sqrtKN0 L m)
      ≤ (N : ℝ) * (L : ℝ) * (27 / 2 * (M L m : ℝ) / (1 - rho L m)) / sqrtKN0 L m := by
    rw [encodingP_eq (by omega), le_div_iff₀ (sub_pos.2 hρ1)]
    nlinarith
  unfold cost8P
  linarith

/-- `cost8P` is at least 1 (for `L ≥ 1`; at `L = 0` it vanishes). -/
theorem one_le_cost8P (L m t N : ℕ) (hL1 : 1 ≤ L) (hL : 10 * m ≤ L)
    (hN : sqrtKN0 L m ≤ (N : ℝ)) : 1 ≤ cost8P L m t N := by
  have := base_le_cost8P hL t N
  have hs1 := one_le_sqrtKN0 (L := L) (m := m) (by omega)
  have hN1 : (1 : ℝ) ≤ N := hs1.trans hN
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have : (1 : ℝ) ≤ (N : ℝ) * (L : ℝ) * sqrtKN0 L m :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hN1 hL1) hs1
  linarith

/-! ### `Within8P` -/

/-- `f = O(cost8P)`: at most a constant times `cost8P`, for all parameters that satisfy the
hypotheses of Theorem 30. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (Within8X)
def Within8P (f : Sec2.Par → ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ p t, Hyp30 p t → (f p t : ℝ) ≤ C * cost8P p.L p.m t p.N

namespace Within8P

variable {f g : Sec2.Par → ℕ → ℕ}

/-- A smaller function. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (Within8X.of_le)
theorem of_le (hg : Within8P g) (h : ∀ p t, Hyp30 p t → f p t ≤ g p t) : Within8P f :=
  let ⟨C, hC, hg⟩ := hg
  ⟨C, hC, fun p t hp => le_trans (by exact_mod_cast h p t hp) (hg p t hp)⟩

/-- A sum. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (Within8X.add)
theorem add (hf : Within8P f) (hg : Within8P g) : Within8P fun p t => f p t + g p t := by
  obtain ⟨A, hA, hf⟩ := hf
  obtain ⟨B, hB, hg⟩ := hg
  refine ⟨A + B, add_nonneg hA hB, fun p t hp => ?_⟩
  rw [Nat.cast_add, add_mul]
  exact add_le_add (hf p t hp) (hg p t hp)

/-- A multiple. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (Within8X.const_mul)
theorem const_mul (c : ℕ) (hf : Within8P f) : Within8P fun p t => c * f p t := by
  obtain ⟨A, hA, hf⟩ := hf
  refine ⟨c * A, by positivity, fun p t hp => ?_⟩
  rw [Nat.cast_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf p t hp) (Nat.cast_nonneg c)

end Within8P

/-- The number 1 is within `cost8P`. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (within8X_one)
theorem within8P_one : Within8P fun _ _ => 1 :=
  ⟨1, zero_le_one, fun p t h => by
    simpa using one_le_cost8P p.L p.m t p.N h.L_pos h.L_ge h.N_ge⟩

/-! ### The small summands of the shared stage -/

/-- `N ≥ 1` under the hypotheses of Theorem 30, because `N ≥ √K N₀ ≥ 1`. -/
theorem hyp30_N_pos {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) : 1 ≤ p.N := by
  have := (one_le_sqrtKN0 h.m_le).trans h.N_ge
  exact_mod_cast this

/-- The tables, the list of subsets, the directory and the digit tables of the shared stage: at
most `52 N L N₀`, in natural numbers. -/
theorem tables_le {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) :
    (p.L + 1) ^ 2 + (Nat.sqrt p.K + 1) + (p.KK + 1) * (p.L + 1) + (p.N + 1) * (p.Lo + 1)
        + (p.D + 1) * (p.m + 1)
      ≤ 52 * (p.N * p.L * N0 p.L p.m) := by
  have hL := h.L_ge
  have := h.m_pos
  have := hyp30_N_pos h
  have : p.K ≤ N0 p.L p.m := K_le_N0 hL
  have : Nat.sqrt p.K ≤ p.K := Nat.sqrt_le_self _
  have : p.KK ≤ p.K := Nat.sqrt_le _
  have : p.D ≤ N0 p.L p.m := D_le_N0 hL
  have : p.L ≤ 10 * N0 p.L p.m := L_le_ten_mul_N0 hL
  have : p.Lo ≤ p.L := Nat.sub_le _ _
  have : 1 ≤ N0 p.L p.m := N0_pos p.L p.m
  generalize N0 p.L p.m = n at *
  generalize p.K = K at *
  generalize p.KK = KK at *
  generalize p.D = D at *
  generalize p.Lo = Lo at *
  generalize p.N = N at *
  generalize p.L = L at *
  generalize p.m = m at *
  have : (L + 1) ^ 2 ≤ 40 * (N * L * n) :=
    calc (L + 1) ^ 2 ≤ (2 * L) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 4 * (L * L) := by ring
      _ ≤ 4 * (L * (10 * n)) := by gcongr
      _ = 40 * (1 * L * n) := by ring
      _ ≤ 40 * (N * L * n) := by gcongr
  have : Nat.sqrt K + 1 ≤ 2 * (N * L * n) :=
    calc Nat.sqrt K + 1 ≤ 2 * n := by omega
      _ = 2 * (1 * 1 * n) := by ring
      _ ≤ 2 * (N * L * n) := by gcongr; omega
  have : (KK + 1) * (L + 1) ≤ 4 * (N * L * n) :=
    calc (KK + 1) * (L + 1) ≤ (2 * n) * (2 * L) := Nat.mul_le_mul (by omega) (by omega)
      _ = 4 * (1 * L * n) := by ring
      _ ≤ 4 * (N * L * n) := by gcongr
  have : (N + 1) * (Lo + 1) ≤ 4 * (N * L * n) :=
    calc (N + 1) * (Lo + 1) ≤ (2 * N) * (2 * L) := Nat.mul_le_mul (by omega) (by omega)
      _ = 4 * (N * L * 1) := by ring
      _ ≤ 4 * (N * L * n) := by gcongr
  have : (D + 1) * (m + 1) ≤ 2 * (N * L * n) :=
    calc (D + 1) * (m + 1) ≤ (2 * n) * L := Nat.mul_le_mul (by omega) (by omega)
      _ = 2 * (1 * L * n) := by ring
      _ ≤ 2 * (N * L * n) := by gcongr
  generalize N * L * n = P at *
  omega

/-- The input array of a band: `bandArrayShape ≤ 5 L 7^L`, because `K₀² N₀ D ≤ K N₀ D ≤ 7^L`. -/
theorem bandArrayShape_le {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) :
    Sec2.bandArrayShape p ≤ 5 * (p.L * 7 ^ p.L) := by
  have hL1 := h.L_pos
  have hKK : p.KK ≤ p.K := Nat.sqrt_le _
  have hKND : p.K * p.N0 * p.D ≤ 7 ^ p.L := Theorem30.K_mul_N0_mul_D_le p.L p.m
  have : p.KK * p.N0 * p.D ≤ 7 ^ p.L :=
    le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hKK)) hKND
  have hS1 : 1 ≤ 7 ^ p.L := Nat.one_le_pow _ _ (by norm_num)
  unfold Sec2.bandArrayShape
  change 7 ^ p.L + (p.KK * p.N0 * p.D + 1) * (p.L + 1) ≤ _
  generalize p.KK * p.N0 * p.D = E at *
  generalize 7 ^ p.L = S7 at *
  generalize p.L = L at *
  have : (E + 1) * (L + 1) ≤ L * S7 + S7 + L + 1 :=
    (Nat.mul_le_mul_right _ (by omega) : _ ≤ (S7 + 1) * (L + 1)).trans (le_of_eq (by ring))
  have : S7 ≤ L * S7 := Nat.le_mul_of_pos_left _ hL1
  have : L ≤ L * S7 := Nat.le_mul_of_pos_right _ hS1
  omega

/-- The work for one band, `encWorkP + bandArrayShape`, is at most `10 L M/(1 - ρ)`. -/
theorem band_work_le {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) :
    ((encWorkP p.L p.m + Sec2.bandArrayShape p : ℕ) : ℝ)
      ≤ 10 * ((p.L : ℝ) * ((M p.L p.m : ℝ) / (1 - rho p.L p.m))) := by
  have hL := h.L_ge
  have hρ := sec4_rho_lt_one p.L p.m hL
  have hρ0 := rho_nonneg hL
  have hM0 : (0 : ℝ) ≤ (M p.L p.m : ℝ) := Nat.cast_nonneg _
  have hMρ : (M p.L p.m : ℝ) ≤ (M p.L p.m : ℝ) / (1 - rho p.L p.m) :=
    le_div_self hM0 (sub_pos.2 hρ) (by linarith)
  have hMρ0 : 0 ≤ (M p.L p.m : ℝ) / (1 - rho p.L p.m) := hM0.trans hMρ
  have hL1 : (1 : ℝ) ≤ (p.L : ℝ) := by exact_mod_cast h.L_pos
  have henc : (encWorkP p.L p.m : ℝ) ≤ 9 / 2 * ((M p.L p.m : ℝ) / (1 - rho p.L p.m)) := by
    have := encWorkP_le_M_div hL
    rwa [mul_div_assoc] at this
  have hseven : ((7 : ℕ) : ℝ) ^ p.L ≤ (M p.L p.m : ℝ) := by exact_mod_cast seven_pow_le_M hL
  have hband : (Sec2.bandArrayShape p : ℝ) ≤ 5 * ((p.L : ℝ) * (7 : ℝ) ^ p.L) := by
    exact_mod_cast bandArrayShape_le h
  have : 5 * ((p.L : ℝ) * (7 : ℝ) ^ p.L)
      ≤ 5 * ((p.L : ℝ) * ((M p.L p.m : ℝ) / (1 - rho p.L p.m))) := by
    gcongr
    exact_mod_cast hseven.trans hMρ
  have : 9 / 2 * ((M p.L p.m : ℝ) / (1 - rho p.L p.m))
      ≤ 9 / 2 * ((p.L : ℝ) * ((M p.L p.m : ℝ) / (1 - rho p.L p.m))) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hMρ0 hL1) (by norm_num)
  push_cast
  linarith

/-- The work for the bands: `nB (encWorkP + bandArrayShape)` is at most twice the second summand of
`cost8P`, because `nB ≤ 2 N/(√K N₀)`. -/
theorem within8P_bands :
    Within8P fun p _ => p.nB * (encWorkP p.L p.m + Sec2.bandArrayShape p) := by
  refine ⟨2, by norm_num, fun p t h => ?_⟩
  have hL := h.L_ge
  have hs := sqrtKN0_pos h.m_le
  have hρ := sec4_rho_lt_one p.L p.m hL
  have hMρ0 : 0 ≤ (M p.L p.m : ℝ) / (1 - rho p.L p.m) :=
    div_nonneg (Nat.cast_nonneg _) (sub_pos.2 hρ).le
  have hnB : (p.nB : ℝ) ≤ 2 * (p.N : ℝ) / sqrtKN0 p.L p.m := by
    have := Theorem30.bands h.m_pos hL h.N_ge
    change (2 * (numBands p.L p.m p.N) : ℝ) ≤ _ at this
    have h2 : (p.nB : ℝ) = (numBands p.L p.m p.N : ℝ) := rfl
    have : 4 * (p.N : ℝ) / sqrtKN0 p.L p.m = 2 * (2 * (p.N : ℝ) / sqrtKN0 p.L p.m) := by
      ring
    rw [h2]
    linarith
  have hwork := band_work_le h
  have := cost8X_first_term_nonneg p.L p.m t p.N
  have : 0 ≤ (p.N : ℝ) * (p.L : ℝ) * ((M p.L p.m : ℝ) / (1 - rho p.L p.m)) / sqrtKN0 p.L p.m :=
    by positivity
  have : (p.nB : ℝ) * ((encWorkP p.L p.m + Sec2.bandArrayShape p : ℕ) : ℝ)
      ≤ (2 * (p.N : ℝ) / sqrtKN0 p.L p.m)
          * (10 * ((p.L : ℝ) * ((M p.L p.m : ℝ) / (1 - rho p.L p.m)))) :=
    mul_le_mul hnB hwork (Nat.cast_nonneg _) (by positivity)
  have heq : (2 * (p.N : ℝ) / sqrtKN0 p.L p.m)
        * (10 * ((p.L : ℝ) * ((M p.L p.m : ℝ) / (1 - rho p.L p.m))))
      = 20 * ((p.N : ℝ) * (p.L : ℝ) * ((M p.L p.m : ℝ) / (1 - rho p.L p.m))
          / sqrtKN0 p.L p.m) := by ring
  have heq' : 2 * ((p.N : ℝ) * (p.L : ℝ) * (27 / 2 * (M p.L p.m : ℝ) / (1 - rho p.L p.m))
        / sqrtKN0 p.L p.m)
      = 27 * ((p.N : ℝ) * (p.L : ℝ) * ((M p.L p.m : ℝ) / (1 - rho p.L p.m))
          / sqrtKN0 p.L p.m) := by ring
  rw [Nat.cast_mul]
  unfold cost8P
  rw [mul_add, heq']
  linarith

/-- The tables of the shared stage are within `cost8P`: `52 N L N₀ ≤ 52 N L √K N₀`. -/
theorem within8P_tables :
    Within8P fun p _ => (p.L + 1) ^ 2 + (Nat.sqrt p.K + 1) + (p.KK + 1) * (p.L + 1)
      + (p.N + 1) * (p.Lo + 1) + (p.D + 1) * (p.m + 1) := by
  refine ⟨52 * (2 / 27), by norm_num, fun p t h => ?_⟩
  have hnat := tables_le h
  have := base_le_cost8P h.L_ge t p.N
  have : (N0 p.L p.m : ℝ) ≤ sqrtKN0 p.L p.m := N0_le_sqrtKN0 h.m_le
  have : (((p.L + 1) ^ 2 + (Nat.sqrt p.K + 1) + (p.KK + 1) * (p.L + 1)
        + (p.N + 1) * (p.Lo + 1) + (p.D + 1) * (p.m + 1) : ℕ) : ℝ)
      ≤ 52 * ((p.N : ℝ) * (p.L : ℝ) * (N0 p.L p.m : ℝ)) := by exact_mod_cast hnat
  have : 52 * ((p.N : ℝ) * (p.L : ℝ) * (N0 p.L p.m : ℝ))
      ≤ 52 * ((p.N : ℝ) * (p.L : ℝ) * sqrtKN0 p.L p.m) := by gcongr
  linarith

/-- **The pruned shared stage** runs within `cost8P`. -/
theorem within8P_sharedShapeP : Within8P fun p _ => Sec2.sharedShapeP p :=
  (within8P_tables.add within8P_bands).of_le fun p _ _ => by
    unfold Sec2.sharedShapeP
    exact le_rfl

/-! ### The tiles -/

/-- The work for the boxes: `L` for each box of each tile; `boxes_costX` against the first
summand. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (within8X_boxes)
theorem within8P_boxes : Within8P fun p t => p.L * (p.nB ^ 2 * (boxes p.L p.m t).card) := by
  refine ⟨8, by norm_num, fun p t h => ?_⟩
  have := boxes_costX h.m_pos h.L_ge h.t_le h.N_ge
  have := cost8P_second_term_nonneg h.L_ge p.N
  push_cast
  change (p.L : ℝ) * ((numBands p.L p.m p.N : ℝ) ^ 2 * _) ≤ _
  unfold cost8P
  linarith

/-- **The tries of all tiles** are built within `cost8P`. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (within8X_tAllTiles)
theorem within8P_tAllTiles : Within8P fun p t => tAllTiles p.L p.m t p.nB := by
  obtain ⟨c, hc⟩ := exists_tTile_le
  refine ((within8P_boxes.const_mul c).add (within8P_one.const_mul 30)).of_le fun p t h => ?_
  have := hc p.L p.m t h.L_pos h.m_le
  have : p.nB ≤ p.nB ^ 2 := Nat.le_self_pow (by norm_num) _
  calc tAllTiles p.L p.m t p.nB
      = p.nB ^ 2 * (tTile p.L p.m t + 80) + p.nB * 40 + 30 := by simp only [tAllTiles]; ring
    _ ≤ p.nB ^ 2 * (tTile p.L p.m t + 80) + p.nB ^ 2 * 40 + 30 := by gcongr
    _ = p.nB ^ 2 * (tTile p.L p.m t + 120) + 30 := by ring
    _ ≤ p.nB ^ 2 * (c * (p.L * (boxes p.L p.m t).card)) + 30 := by gcongr
    _ = c * (p.L * (p.nB ^ 2 * (boxes p.L p.m t).card)) + 30 * 1 := by ring

/-! ### The two quantities of the set-up -/

/-- `N (L + 1)` is within `cost8P`: `N (L + 1) ≤ 2 N L ≤ 2 N L √K N₀`. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (N_mul_le_cost8X)
theorem N_mul_le_cost8P {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) :
    (p.N : ℝ) * ((p.L : ℝ) + 1) ≤ cost8P p.L p.m t p.N := by
  have := base_le_cost8P h.L_ge t p.N
  have hs1 := one_le_sqrtKN0 h.m_le
  have : (1 : ℝ) ≤ (p.L : ℝ) := by exact_mod_cast h.L_pos
  have : (0 : ℝ) ≤ p.N := Nat.cast_nonneg _
  have hNL : 0 ≤ (p.N : ℝ) * (p.L : ℝ) := by positivity
  have : (p.N : ℝ) * ((p.L : ℝ) + 1) ≤ 2 * ((p.N : ℝ) * (p.L : ℝ)) := by nlinarith
  have : (p.N : ℝ) * (p.L : ℝ) ≤ (p.N : ℝ) * (p.L : ℝ) * sqrtKN0 p.L p.m :=
    le_mul_of_one_le_right hNL hs1
  linarith

/-- `N 4^m` is within `cost8P`: `4^m = D ≤ N₀ ≤ √K N₀ ≤ L √K N₀`. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (N_mul_pow_le_cost8X)
theorem N_mul_pow_le_cost8P {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) :
    (p.N : ℝ) * (4 : ℝ) ^ p.m ≤ cost8P p.L p.m t p.N := by
  have := base_le_cost8P h.L_ge t p.N
  have hD : ((4 : ℕ) : ℝ) ^ p.m ≤ (N0 p.L p.m : ℝ) := by exact_mod_cast D_le_N0 h.L_ge
  have hN0 := N0_le_sqrtKN0 h.m_le
  have hL1 : (1 : ℝ) ≤ (p.L : ℝ) := by exact_mod_cast h.L_pos
  have hs := (sqrtKN0_pos h.m_le).le
  have : (p.N : ℝ) * (4 : ℝ) ^ p.m ≤ (p.N : ℝ) * sqrtKN0 p.L p.m := by
    gcongr
    exact_mod_cast hD.trans hN0
  have : (p.N : ℝ) * sqrtKN0 p.L p.m ≤ (p.N : ℝ) * (p.L : ℝ) * sqrtKN0 p.L p.m := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hs hL1) (Nat.cast_nonneg _)
  have : 0 ≤ (p.N : ℝ) * (p.L : ℝ) * sqrtKN0 p.L p.m := by positivity
  linarith

/-- **The pruned preprocessing** takes `O(cost8P)` steps. `c` is the constant of the pruned shared
stage. -/
-- adapted from ImprovedExponents/Cost8X/Within.lean (exists_tPreCore_leX)
theorem exists_tPreCore_leP (c : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Sec2.Par) (t : ℕ), Hyp30 p t →
    (tPreCoreP c p t : ℝ) ≤ C * cost8P p.L p.m t p.N :=
  (((within8P_sharedShapeP.const_mul c).add within8P_tAllTiles).add
    (within8P_one.const_mul 300)).of_le fun _ _ _ => le_of_eq (by simp [tPreCoreP])


/-!
# The solver of Lop-AE-SparseTri from a thin-product claim

Corollary 16 for arbitrary exponents: "This is Corollary 26 with N = n, applied to the two
biadjacency matrices". The matrices have entries 0 and 1; writing them down and copying the answers
costs `O(nD + w + 1)`, and telling which counts are nonzero `O(w + 1)`. Both are absorbed by the
bound `n² (log D + 1)²/D^γ + w D^q (log D + 1)` when `D ≤ n^ε` with `ε (1 + γ) ≤ 1`, because then
`D^{1+γ} ≤ n`, that is `n D ≤ n²/D^γ`.
-/



/-- For `1 ≤ D ≤ n^ε` with `ε (1 + γ) ≤ 1`, the size `n D` of the two matrices is at most the bound
on the preprocessing. -/
theorem mul_le_preBound31 {ε γ : ℝ} {n D : ℕ} (hn : 1 ≤ n) (hD : 1 ≤ D) (hγ : 0 ≤ γ)
    (hε : ε * (1 + γ) ≤ 1) (hDn : (D : ℝ) ≤ (n : ℝ) ^ ε) :
    (n : ℝ) * D ≤ preBound31 γ n D := by
  have hNR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < D := by linarith
  have hpow : (D : ℝ) ^ (1 + γ) ≤ n := by
    calc (D : ℝ) ^ (1 + γ) ≤ ((n : ℝ) ^ ε) ^ (1 + γ) :=
          Real.rpow_le_rpow hD0.le hDn (by linarith)
      _ = (n : ℝ) ^ (ε * (1 + γ)) := by rw [← Real.rpow_mul (by positivity)]
      _ ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNR hε
      _ = n := Real.rpow_one _
  have hsplit : (D : ℝ) ^ (1 + γ) = D * (D : ℝ) ^ γ := by rw [Real.rpow_add hD0, Real.rpow_one]
  have := Real.log_nonneg hDR
  have hDγ : 0 < (D : ℝ) ^ γ := Real.rpow_pos_of_pos hD0 _
  rw [preBound31, le_div_iff₀ hDγ]
  calc (n : ℝ) * D * (D : ℝ) ^ γ = n * (D * (D : ℝ) ^ γ) := by ring
    _ ≤ n * n := mul_le_mul_of_nonneg_left (hsplit.symm.trans_le hpow) (by positivity)
    _ = (n : ℝ) ^ 2 * 1 := by ring
    _ ≤ (n : ℝ) ^ 2 * (Real.log D + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ (by linarith)) (by positivity)

/-- **Corollary 16 for arbitrary exponents**: a thin-product claim gives a solver of
Lop-AE-SparseTri with the same bound, by the two transfer claims of the proof of Corollary 15. -/
theorem lopClaim_of_thinClaim (M : DetTimeModel) {ε γ q : ℝ} (hγ : 0 ≤ γ) (hq : 0 ≤ q)
    (hε : ε * (1 + γ) ≤ 1) (h : ThinClaim M ε γ q) (hlop : Claim.LopCountFromThinProduct M)
    (hdet : Claim.LopDetectFromCount M) : LopClaim M ε γ q := by
  obtain ⟨C, T, hT, hb⟩ := h
  obtain ⟨C₁, hlop⟩ := hlop
  obtain ⟨C₃, hdet⟩ := hdet
  refine ⟨|C| + 2 * |C₁| + |C₃|, _, hdet _ (hlop T hT), fun n D w hn hD hDn => ?_⟩
  have hNR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have : (1 : ℝ) ≤ (n : ℝ) * D := one_le_mul_of_one_le_of_one_le hNR hDR
  have := mul_le_preBound31 hn hD hγ hε hDn
  have hquery1 : 1 ≤ queryBound31 q D := one_le_queryBound31 hD hq
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have : (w : ℝ) ≤ w * queryBound31 q D := le_mul_of_one_le_right hw0 hquery1
  have hB0 : 0 ≤ preBound31 γ n D + w * queryBound31 q D := by linarith
  have : T n D w 1 ≤ |C| * (preBound31 γ n D + w * queryBound31 q D) :=
    (hb n D w 1 hn hD hDn).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hB0)
  have : C₁ * ((n : ℝ) * D + w + 1)
      ≤ |C₁| * (2 * (preBound31 γ n D + w * queryBound31 q D)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C₁) (by linarith)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))
  have : C₃ * ((w : ℝ) + 1) ≤ |C₃| * (preBound31 γ n D + w * queryBound31 q D) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C₃) (by linarith)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))
  change T n D w 1 + C₁ * ((n : ℝ) * D + w + 1) + C₃ * ((w : ℝ) + 1)
    ≤ (|C| + 2 * |C₁| + |C₃|) * (preBound31 γ n D + w * queryBound31 q D)
  linarith







theorem le_rpow_max_log_div {s : ℕ} {u : ℝ} (hs : 3 ≤ s) (hu : 1 ≤ u) :
    u ≤ (s : ℝ) ^ max 1 (Real.log u / Real.log s) := by
  have hs0 : (0 : ℝ) < s := Nat.cast_pos.2 (by omega)
  have : 1 ≤ Real.log s := Real.one_le_log_natCast_of_three_le hs
  calc u = (s : ℝ) ^ (Real.log u / Real.log s) := by
        rw [Real.rpow_def_of_pos hs0, mul_div_cancel₀ _ (by linarith),
          Real.exp_log (zero_lt_one.trans_le hu)]
    _ ≤ (s : ℝ) ^ max 1 (Real.log u / Real.log s) :=
        Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 (by omega)) (le_max_right _ _)

theorem max_log_div_le {s : ℕ} {u : ℝ} (hs : 3 ≤ s) (hu : 1 ≤ u) :
    max 1 (Real.log u / Real.log s) ≤ 1 + logU u := by
  refine max_le (one_le_one_add_logU u) ?_
  linarith [div_le_self (Real.log_nonneg hu) (Real.one_le_log_natCast_of_three_le hs),
    log_le_logU (zero_lt_one.trans_le hu)]

theorem exactTriangleUniform_of_explicitFrom (M : DetTimeModel) {δ : ℝ} (e : ℕ) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hex : ExplicitFrom M δ e) (hbf : Claim.BruteForce M)
    (hch : Closure.ChooseBySize M) (hmono : Closure.MonoExactTriangle M) :
    Claim.ExactTriangleUniform M δ e := by
  obtain ⟨n₀, K, T, hT, hb⟩ := hex
  obtain ⟨C, hbf⟩ := hbf
  set n₁ := max n₀ 3
  obtain ⟨C₀, hch⟩ := hch n₁
  refine ⟨1 + (|C| * (n₁ : ℝ) ^ δ + |K| + |C₀|),
    le_add_of_nonneg_right (by positivity),
    hmono _ _ (fun s u hs hu => ?_) (hch _ T hbf hT)⟩
  set S := (s : ℝ) ^ (3 - δ) * (Real.log s + 1) ^ e * (1 + logU u) ^ 2
  have hs0 : (0 : ℝ) < s := Nat.cast_pos.2 hs
  have : 0 ≤ Real.log s := Real.log_natCast_nonneg s
  have hle : 1 ≤ (Real.log s + 1) ^ e := one_le_pow₀ (by linarith)
  have hlu : 1 ≤ 1 + logU u := one_le_one_add_logU u
  have hlu2 : 1 + logU u ≤ (1 + logU u) ^ 2 := le_self_pow₀ hlu two_ne_zero
  have hS1 : 1 ≤ S := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (Nat.one_le_cast.2 hs) (by linarith)) hle)
    (one_le_pow₀ hlu)
  have : 0 ≤ S := zero_le_one.trans hS1
  have : C₀ ≤ |C₀| * S := (le_abs_self C₀).trans (le_mul_of_one_le_right (abs_nonneg _) hS1)
  have : (if s < n₁ then C * ((s : ℝ) ^ 3 * (1 + logU u)) else T s u)
      ≤ (|C| * (n₁ : ℝ) ^ δ + |K|) * S := by
    split_ifs with hlt
    · have hsplit : (s : ℝ) ^ 3 = (s : ℝ) ^ δ * (s : ℝ) ^ (3 - δ) := by
        rw [← Real.rpow_add hs0, ← Real.rpow_natCast]
        congr 1; push_cast; ring
      have : (s : ℝ) ^ δ ≤ (n₁ : ℝ) ^ δ :=
        Real.rpow_le_rpow hs0.le (Nat.cast_le.2 hlt.le) hδ0
      have h1 : (s : ℝ) ^ 3 * (1 + logU u) ≤ (n₁ : ℝ) ^ δ * S := by
        calc (s : ℝ) ^ 3 * (1 + logU u)
            = (s : ℝ) ^ δ * ((s : ℝ) ^ (3 - δ) * 1 * (1 + logU u)) := by rw [hsplit]; ring
          _ ≤ (n₁ : ℝ) ^ δ * ((s : ℝ) ^ (3 - δ) * (Real.log s + 1) ^ e * (1 + logU u) ^ 2) := by
              gcongr
      have h2 := (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
        (mul_le_mul_of_nonneg_left h1 (abs_nonneg C))
      have : 0 ≤ |K| * S := by positivity
      linarith
    · have hs3 : 3 ≤ s := (le_max_right _ _).trans (not_lt.1 hlt)
      have hT_le := hb s _ u ((le_max_left _ _).trans (not_lt.1 hlt)) (le_max_left _ _)
        (le_rpow_max_log_div hs3 hu)
      have hκ := (max_log_div_le hs3 hu).trans hlu2
      have h1 : max 1 (Real.log u / Real.log s) * ((s : ℝ) ^ (3 - δ) * Real.log s ^ e) ≤ S := by
        calc max 1 (Real.log u / Real.log s) * ((s : ℝ) ^ (3 - δ) * Real.log s ^ e)
            ≤ (1 + logU u) ^ 2 * ((s : ℝ) ^ (3 - δ) * (Real.log s + 1) ^ e) := by
              gcongr; linarith
          _ = S := by ring
      have := hT_le.trans ((mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)).trans
        (mul_le_mul_of_nonneg_left h1 (abs_nonneg K)))
      have : 0 ≤ |C| * (n₁ : ℝ) ^ δ * S := by positivity
      linarith
  simp only [uniformTime]
  change _ ≤ _ * S
  linarith







noncomputable abbrev preCostP (G : RatParams) (N D₀ : ℕ) : ℝ :=
  cost8P (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N

structure CostsWithinP (G : RatParams) (C : ℝ) (N D₀ : ℕ) (tp tq : ℝ) : Prop where
  one_le_N : 1 ≤ N
  one_le_pre : 1 ≤ tp
  one_le_query : 1 ≤ tq
  above : G.m₀ ≤ logFour D₀ → Hyp30 (parOf G N D₀) (switchOf31 G D₀) ∧
    cost8P (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N ≤ C * tp ∧
    costQuery (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) ≤ C * tq

variable {G : RatParams}

theorem CostsWithinP.hyp {C : ℝ} {N D₀ : ℕ} {tp tq : ℝ} (h : CostsWithinP G C N D₀ tp tq)
    (hm : G.m₀ ≤ logFour D₀) : G.Hyp N D₀ :=
  (h.above hm).1

theorem CostsWithinP.pre_le {C : ℝ} {N D₀ : ℕ} {tp tq : ℝ} (h : CostsWithinP G C N D₀ tp tq)
    (hm : G.m₀ ≤ logFour D₀) : preCostP G N D₀ ≤ C * tp :=
  (h.above hm).2.1

theorem CostsWithinP.query_le {C : ℝ} {N D₀ : ℕ} {tp tq : ℝ} (h : CostsWithinP G C N D₀ tp tq)
    (hm : G.m₀ ≤ logFour D₀) : G.queryCost D₀ ≤ C * tq :=
  (h.above hm).2.2

theorem tPre31P_add_tPreCore (c0 : ℕ) (N D₀ : ℕ) (hm : G.m₀ ≤ logFour D₀) :
    tPre31P c0 G N D₀ + tPreCore c0 (parOf G N D₀) (switchOf31 G D₀)
      = tPre31 c0 G N D₀ + tPreCoreP c0 (parOf G N D₀) (switchOf31 G D₀) := by
  unfold tPre31P tPre31
  rw [ite_eq_right (not_lt.2 hm), ite_eq_right (not_lt.2 hm)]
  ring

theorem exists_tPre31P_le_setup : ∃ k : ℕ, ∀ c0 N D₀ : ℕ, G.m₀ ≤ logFour D₀ →
    tPre31P c0 G N D₀ ≤ k * (G.L (logFour D₀) + 1 + N * 4 ^ logFour D₀ + N)
      + tPreCoreP c0 (parOf G N D₀) (switchOf31 G D₀) := by
  obtain ⟨k, hk⟩ := exists_tPre31_le_setup G
  refine ⟨k, fun c0 N D₀ hm => ?_⟩
  have := hk c0 N D₀ hm
  have := tPre31P_add_tPreCore (G := G) c0 N D₀ hm
  omega

theorem exists_tPre31P_le_cost8P (G : RatParams) (c0 : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ N D₀ : ℕ, 1 ≤ N →
    G.m₀ ≤ logFour D₀ → G.Hyp N D₀ → (tPre31P c0 G N D₀ : ℝ) ≤ K * preCostP G N D₀ := by
  obtain ⟨k, hk⟩ := exists_tPre31P_le_setup (G := G)
  obtain ⟨Cp, hCp0, hCp⟩ := exists_tPreCore_leP c0
  refine ⟨k * 4 + Cp, by positivity, fun N D₀ hN hm h => ?_⟩
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have : (0 : ℝ) ≤ (G.L (logFour D₀) : ℝ) := by positivity
  have : (tPreCoreP c0 (parOf G N D₀) (switchOf31 G D₀) : ℝ)
      ≤ Cp * preCostP G N D₀ := hCp (parOf G N D₀) (switchOf31 G D₀) h
  have : (N : ℝ) * (4 : ℝ) ^ logFour D₀ ≤ preCostP G N D₀ := N_mul_pow_le_cost8P h
  have : (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) ≤ preCostP G N D₀ := N_mul_le_cost8P h
  have : (tPre31P c0 G N D₀ : ℝ)
      ≤ k * ((G.L (logFour D₀) : ℝ) + 1 + N * (4 : ℝ) ^ logFour D₀ + N)
        + (tPreCoreP c0 (parOf G N D₀) (switchOf31 G D₀) : ℝ) := by exact_mod_cast hk c0 N D₀ hm
  have : (G.L (logFour D₀) : ℝ) + 1 ≤ (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) :=
    le_mul_of_one_le_left (by positivity) hN'
  have : (N : ℝ) ≤ (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) :=
    le_mul_of_one_le_right (by positivity) (by linarith)
  have : (k : ℝ) * ((G.L (logFour D₀) : ℝ) + 1 + N * (4 : ℝ) ^ logFour D₀ + N)
      ≤ k * (4 * preCostP G N D₀) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

theorem exists_tPre31P_le (G : RatParams) {C : ℝ} (hC : 0 ≤ C) (c0 : ℕ) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ {N D₀ : ℕ} {tp tq : ℝ}, CostsWithinP G C N D₀ tp tq → (tPre31P c0 G N D₀ : ℝ) ≤ A * tp := by
  obtain ⟨K, hK0, hK⟩ := exists_tPre31P_le_cost8P G c0
  obtain ⟨A, hA0, hA⟩ := exists_le_of_small_of_large G hC
    (S := ((20 * G.m₀ + 50 : ℕ) : ℝ)) (by positivity) hK0
  refine ⟨A, hA0, fun {N D₀ tp tq} h =>
    hA D₀ _ tp _ h.one_le_pre h.pre_le (fun hm => ?_) fun hm => ?_⟩
  · have hsmall : tPre31P c0 G N D₀ ≤ 20 * G.m₀ + 50 := by
      unfold tPre31P tLog4
      rw [ite_eq_left hm]
      omega
    exact_mod_cast hsmall
  · have := hK N D₀ h.one_le_N hm (h.hyp hm)
    have : (0 : ℝ) ≤ ((20 * G.m₀ + 50 : ℕ) : ℝ) := by positivity
    linarith

theorem exists_tOffline32P_le (G : RatParams) {C : ℝ} (hC : 0 ≤ C) (c0 k : ℕ) : ∃ A : ℝ,
    ∀ {N D₀ : ℕ} {tp tq : ℝ} (w : ℕ), CostsWithinP G C N D₀ tp tq →
      (tOffline32P c0 G N D₀ w : ℝ) + k ≤ A * (tp + w * tq) := by
  obtain ⟨Ap, hAp0, hAp⟩ := exists_tPre31P_le G hC c0
  obtain ⟨Aq, hAq0, hAq⟩ := exists_tQuery31_le G hC
  refine ⟨(Ap + 20 + k) + (Aq + 30), fun {N D₀ tp tq} w h => ?_⟩
  have := hAp h
  have := hAq h.one_le_query h.hyp h.query_le
  have htp := h.one_le_pre
  have := h.one_le_query
  have hw : (0 : ℝ) ≤ (w : ℝ) := by positivity
  have : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hwtq : 0 ≤ (w : ℝ) * tq := mul_nonneg hw (by linarith)
  have htime : (tOffline32P c0 G N D₀ w : ℝ)
      = (tPre31P c0 G N D₀ : ℝ) + (w : ℝ) * ((tQuery31 G D₀ : ℝ) + 30) + 20 := by
    simp only [tOffline32P]
    push_cast
    ring
  have : (tPre31P c0 G N D₀ : ℝ) + 20 + k ≤ (Ap + 20 + k) * tp := by
    linarith [le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ 20 + (k : ℝ)) htp]
  have : (w : ℝ) * ((tQuery31 G D₀ : ℝ) + 30) ≤ (Aq + 30) * ((w : ℝ) * tq) := by
    calc (w : ℝ) * ((tQuery31 G D₀ : ℝ) + 30) ≤ (w : ℝ) * ((Aq + 30) * tq) :=
          mul_le_mul_of_nonneg_left (by linarith) hw
      _ = (Aq + 30) * ((w : ℝ) * tq) := by ring
  have : 0 ≤ (Ap + 20 + k) * ((w : ℝ) * tq) := mul_nonneg (by positivity) hwtq
  have : 0 ≤ (Aq + 30) * tp := mul_nonneg (by positivity) (by linarith)
  rw [htime]
  linarith

theorem eps_mul_gamma_le_P {c γ ε : ℝ} (hc : 10 < c) (hγ : 0 < γ) (hε : ε < RcP c γ) :
    ε * γ ≤ 1 := by
  have hA := basePruned_pos (by linarith : 1 < c)
  have hden := thinR_den_pos hA hγ.le
  have : RcP c γ * γ ≤ 1 := by
    unfold RcP thinR
    rw [div_mul_eq_mul_div, div_le_one hden]
    linarith
  nlinarith

theorem offlineWithinP (c₀ : ℕ) {a b p q : ℕ} (hb : 1 ≤ b) (hq : 1 ≤ q) (hc : 10 * b < a)
    (hp : 1 ≤ p) (hθ : 10 * p < 9 * q) {γ ε : ℝ} (hγ0 : 0 < γ)
    (hγ : γ < gammaX ((a : ℝ) / b) ((p : ℝ) / q)) (hε : ε < RcP ((a : ℝ) / b) γ) :
    ∃ m₁ : ℕ, ∀ (m₀ : ℕ), 1 ≤ m₀ → m₁ ≤ m₀ →
      ∃ A : ℝ, ∀ N D₀ w : ℕ, 1 ≤ N → 1 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
        (tOffline32P c₀ ⟨a, b, p, q, m₀, hb, hq, hc, hθ⟩ N D₀ w : ℝ) + 400
          ≤ A * (preBound31 γ N D₀ + (w : ℝ) * queryBound31 (qOf ((p : ℝ) / q)) D₀) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcR : (10 : ℝ) < (a : ℝ) / b := by
    rw [lt_div_iff₀ hbR]
    exact_mod_cast hc
  have hθ0 : (0 : ℝ) < (p : ℝ) / q := div_pos (by exact_mod_cast hp) hqR
  have hθ1 : (p : ℝ) / q < 0.9 := by
    rw [div_lt_iff₀ hqR]
    have : (10 : ℝ) * p < 9 * q := by exact_mod_cast hθ
    linarith
  have : 0 < RcP ((a : ℝ) / b) γ := thinR_pos (basePruned_pos (by linarith)) hγ0.le
  set ε₁ := max ε (RcP ((a : ℝ) / b) γ / 2) with hε₁
  have hε₁0 : 0 < ε₁ := lt_max_of_lt_right (by positivity)
  have hε₁R : ε₁ < RcP ((a : ℝ) / b) γ := max_lt hε (by linarith)
  have hεε₁ : ε ≤ ε₁ := le_max_left _ _
  obtain ⟨C, m₁, hC, hcost⟩ := costsP hcR hθ0 hθ1 hγ0.le hγ hε₁0 hε₁R
  have hεγ : ε₁ * γ ≤ 1 := eps_mul_gamma_le_P hcR hγ0 hε₁R
  refine ⟨m₁, fun m₀ hm₀ hm₁ => ?_⟩
  obtain ⟨A, hA⟩ := exists_tOffline32P_le ⟨a, b, p, q, m₀, hb, hq, hc, hθ⟩ hC c₀ 400
  refine ⟨A, fun N D₀ w hN hD hDN => hA w ?_⟩
  have hDN₁ : (D₀ : ℝ) ≤ (N : ℝ) ^ ε₁ :=
    hDN.trans (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hεε₁)
  refine ⟨hN,
    one_le_preBound31 hD (rpow_le_sq hN hγ0.le hεγ hDN₁),
    one_le_queryBound31 hD (qOf_nonneg _ hθ0 hθ1), fun hm => ?_⟩
  have hm1 : 1 ≤ logFour D₀ := le_trans hm₀ hm
  obtain ⟨hfit, hpre, hquery⟩ := hcost D₀ N (logFour D₀) (two_le_of_clog hm1) hDN₁
    (ceil_logb_four D₀).symm (le_trans hm₁ hm)
  rw [levelsOf_div a _ hb] at hfit hpre hquery
  rw [switchOf_div p _ hq] at hpre hquery
  exact ⟨⟨hm1, RatParams.ten_le_L _ _, RatParams.t_le _ _, hfit⟩,
    hpre.trans (mul_le_mul_of_nonneg_left (le_preBound31 hD) hC),
    hquery.trans (mul_le_mul_of_nonneg_left (le_queryBound31 hD) hC)⟩





/-!
# The parameters `D = ⌊n^d⌋`, `g = ⌈D^η⌉` and the dimension `Dc` of a call

For `0 < d ≤ 1` and `0 < η < 1/2`, the parameters `D(n) = ⌊n^d⌋` and `g(n) = ⌈D(n)^η⌉` satisfy,
from some `n` on, the hypotheses of Theorem 17 and the two-sided bounds `n^d/2 ≤ D ≤ n^d`,
`D^η ≤ g ≤ 2 D^η` (`HostParams`, `eventually_hostParams`). If the dimension `Dc(n)` of a call is
`Θ(D^a)` with `d a < min(ε, 1)`, then from some `n` on `1 ≤ Dc ≤ n^ε` and the powers of `Dc` are
bounded by powers of `n` (`CallParams`, `eventually_callParams`).

The two dimensions that are used: `Dc = D` (`eventually_self_bounds`) and
`Dc = ⌈⌊√D⌋/g⌉ ⌊√D⌋ = Θ(D^{1-η})` (`eventually_pieceSize_bounds`).
-/


open Filter

/-- For `d > 0`, `n^d` is eventually at least any given number. -/
theorem eventually_le_rpow {d : ℝ} (hd0 : 0 < d) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, B ≤ (n : ℝ) ^ d :=
  ((tendsto_rpow_atTop hd0).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop B

/-- What is used of the parameters `D = ⌊n^d⌋` and `g = ⌈D^η⌉` at a large `n`: the hypotheses of
Theorem 17 and two-sided bounds. -/
structure HostParams (d η : ℝ) (n Dn gn : ℕ) : Prop where
  /-- `n ≥ 1`. -/
  one_le_n : 1 ≤ n
  /-- `D ≥ 16`. -/
  sixteen_le : 16 ≤ Dn
  /-- `D ≤ n`. -/
  le_n : Dn ≤ n
  /-- `g ≥ 1`. -/
  one_le_g : 1 ≤ gn
  /-- `g ≤ √D`. -/
  g_le_sqrt : (gn : ℝ) ≤ Real.sqrt Dn
  /-- `D ≤ n^d`. -/
  D_le : (Dn : ℝ) ≤ (n : ℝ) ^ d
  /-- `n^d/2 ≤ D`. -/
  le_D : (n : ℝ) ^ d / 2 ≤ Dn
  /-- `D^η ≤ g`. -/
  rpow_le_g : (Dn : ℝ) ^ η ≤ gn
  /-- `g ≤ 2 D^η`. -/
  g_le_rpow : (gn : ℝ) ≤ 2 * (Dn : ℝ) ^ η

/-- `D = ⌊n^d⌋` and `g = ⌈D^η⌉` satisfy `HostParams` from some `n` on. -/
theorem eventually_hostParams {d η : ℝ} {D g : ℕ → ℕ} (hd0 : 0 < d) (hd1 : d ≤ 1) (hη0 : 0 < η)
    (hη1 : η < 1 / 2) (hD : ∀ n, D n = ⌊(n : ℝ) ^ d⌋₊) (hg : ∀ n, g n = ⌈(D n : ℝ) ^ η⌉₊) :
    ∀ᶠ n : ℕ in atTop, HostParams d η n (D n) (g n) := by
  have hτ : 0 < 1 / 2 - η := by linarith
  filter_upwards [eventually_le_rpow hd0 (max 16 (2 * (2 : ℝ) ^ (1 / (1 / 2 - η)))),
    eventually_ge_atTop 1] with n hn hn1
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have h16 : (16 : ℝ) ≤ (n : ℝ) ^ d := (le_max_left _ _).trans hn
  have hB : 2 * (2 : ℝ) ^ (1 / (1 / 2 - η)) ≤ (n : ℝ) ^ d := (le_max_right _ _).trans hn
  have hfl : (D n : ℝ) ≤ (n : ℝ) ^ d := by rw [hD]; exact Nat.floor_le (by positivity)
  have hlt : (n : ℝ) ^ d < (D n : ℝ) + 1 := by rw [hD]; exact Nat.lt_floor_add_one _
  have hD16 : 16 ≤ D n := by rw [hD]; exact Nat.le_floor (by exact_mod_cast h16)
  have hX16 : (16 : ℝ) ≤ D n := by exact_mod_cast hD16
  have hX0 : (0 : ℝ) < D n := by linarith
  have hXη1 : 1 ≤ (D n : ℝ) ^ η := Real.one_le_rpow (by linarith) hη0.le
  have hgl : (D n : ℝ) ^ η ≤ g n := by rw [hg]; exact Nat.le_ceil _
  have hgu : (g n : ℝ) < (D n : ℝ) ^ η + 1 := by
    rw [hg]; exact Nat.ceil_lt_add_one (by positivity)
  have hhalf : (2 : ℝ) ^ (1 / (1 / 2 - η)) ≤ (D n : ℝ) := by linarith
  have h2 : (2 : ℝ) ≤ (D n : ℝ) ^ (1 / 2 - η) := by
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / (1 / 2 - η))) ^ (1 / 2 - η) := by
          rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hτ.ne', Real.rpow_one]
      _ ≤ (D n : ℝ) ^ (1 / 2 - η) := Real.rpow_le_rpow (by positivity) hhalf hτ.le
  have hsqrt : Real.sqrt (D n) = (D n : ℝ) ^ η * (D n : ℝ) ^ (1 / 2 - η) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hX0]
    congr 1
    ring
  refine ⟨hn1, hD16, ?_, ?_, ?_, hfl, by linarith, hgl, by linarith⟩
  · have : (D n : ℝ) ≤ (n : ℝ) :=
      hfl.trans ((Real.rpow_le_rpow_of_exponent_le hN1 hd1).trans_eq (Real.rpow_one _))
    exact_mod_cast this
  · have : (1 : ℝ) ≤ g n := hXη1.trans hgl
    exact_mod_cast this
  · rw [hsqrt]
    have := mul_le_mul_of_nonneg_left h2 (zero_le_one.trans hXη1)
    linarith

namespace HostParams

variable {d η : ℝ} {n Dn gn : ℕ}

/-- `g ≤ 2 n^{dη}`. -/
theorem g_le (h : HostParams d η n Dn gn) (hη0 : 0 ≤ η) :
    (gn : ℝ) ≤ 2 * (n : ℝ) ^ (d * η) := by
  have h1 : (Dn : ℝ) ^ η ≤ ((n : ℝ) ^ d) ^ η := Real.rpow_le_rpow (Nat.cast_nonneg _) h.D_le hη0
  rw [← Real.rpow_mul (Nat.cast_nonneg _)] at h1
  linarith [h.g_le_rpow]

/-- `n^{dη}/2 ≤ g`. -/
theorem le_g (h : HostParams d η n Dn gn) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (n : ℝ) ^ (d * η) / 2 ≤ gn := by
  have hN0 : (0 : ℝ) ≤ (n : ℝ) ^ d := by positivity
  have h1 : ((n : ℝ) ^ d / 2) ^ η ≤ (Dn : ℝ) ^ η := Real.rpow_le_rpow (by positivity) h.le_D hη0
  rw [Real.div_rpow hN0 (by norm_num), ← Real.rpow_mul (Nat.cast_nonneg _)] at h1
  have h2 : (2 : ℝ) ^ η ≤ 2 :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hη1).trans_eq (Real.rpow_one _)
  have : (n : ℝ) ^ (d * η) / 2 ≤ (n : ℝ) ^ (d * η) / (2 : ℝ) ^ η :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) h2
  linarith [h.rpow_le_g]

/-- `1/g ≤ 2 n^{-dη}`. -/
theorem inv_g_le (h : HostParams d η n Dn gn) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    1 / (gn : ℝ) ≤ 2 * (n : ℝ) ^ (-(d * η)) := by
  have hg0 : (0 : ℝ) < gn := by exact_mod_cast h.one_le_g
  have hN0 : (0 : ℝ) < n := by exact_mod_cast h.one_le_n
  have hp : (0 : ℝ) < (n : ℝ) ^ (d * η) := by positivity
  rw [Real.rpow_neg hN0.le, ← div_eq_mul_inv, div_le_div_iff₀ hg0 hp]
  linarith [h.le_g hη0 hη1]

/-- `1/√D ≤ 2 n^{-d/2}`. -/
theorem inv_sqrt_le (h : HostParams d η n Dn gn) :
    1 / Real.sqrt Dn ≤ 2 * (n : ℝ) ^ (-(d / 2)) := by
  have hN0 : (0 : ℝ) < n := by exact_mod_cast h.one_le_n
  have hX0 : (0 : ℝ) < Dn := by exact_mod_cast (by norm_num : 0 < 16).trans_le h.sixteen_le
  have hs : 0 < Real.sqrt Dn := Real.sqrt_pos.2 hX0
  have hp : (0 : ℝ) < (n : ℝ) ^ (d / 2) := by positivity
  have : (n : ℝ) ^ (d / 2) ≤ 2 * Real.sqrt Dn := by
    have e : (n : ℝ) ^ (d / 2) = Real.sqrt ((n : ℝ) ^ d) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]
      congr 1
      ring
    rw [e, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hX0.le]
    linarith [h.le_D]
  rw [Real.rpow_neg hN0.le, ← div_eq_mul_inv, div_le_div_iff₀ hs hp]
  linarith

end HostParams

/-- What is used of the dimension `Dc` of a call at a large `n`: it is at least 1 and at most
`n^ε` and `n`, and its powers `Dc^{-γ}` and `Dc^q` are at most constants times powers of `n`. -/
structure CallParams (d a ε γ q K₁ K₂ : ℝ) (n Dcn : ℕ) : Prop where
  /-- `Dc ≥ 1`. -/
  one_le : 1 ≤ Dcn
  /-- `Dc ≤ n^ε`. -/
  le_rpow : (Dcn : ℝ) ≤ (n : ℝ) ^ ε
  /-- `Dc ≤ n`. -/
  le_n : (Dcn : ℝ) ≤ n
  /-- `Dc^{-γ} ≤ K₁ n^{-daγ}`. -/
  neg_rpow_le : (Dcn : ℝ) ^ (-γ) ≤ K₁ * (n : ℝ) ^ (d * a * -γ)
  /-- `Dc^q ≤ K₂ n^{daq}`. -/
  rpow_le : (Dcn : ℝ) ^ q ≤ K₂ * (n : ℝ) ^ (d * a * q)

theorem HostParams.pieceSize_bounds {d η : ℝ} {n Dn gn : ℕ} (P : HostParams d η n Dn gn) :
    1 / 8 * (Dn : ℝ) ^ (1 - η) ≤ ((pieceSizeNat Dn gn * Nat.sqrt Dn : ℕ) : ℝ) ∧
      ((pieceSizeNat Dn gn * Nat.sqrt Dn : ℕ) : ℝ) ≤ 2 * (Dn : ℝ) ^ (1 - η) := by
  have hX0 : (0 : ℝ) < Dn := by exact_mod_cast (by norm_num : 0 < 16).trans_le P.sixteen_le
  have hg0 : (0 : ℝ) < gn := by exact_mod_cast P.one_le_g
  have hXη : (0 : ℝ) < (Dn : ℝ) ^ η := by positivity
  have hS1 : (Nat.sqrt Dn : ℝ) ≤ Real.sqrt Dn := Real.nat_sqrt_le_real_sqrt
  have hS2 : Real.sqrt Dn < (Nat.sqrt Dn : ℝ) + 1 := Real.real_sqrt_lt_nat_sqrt_succ
  have hgS : (gn : ℝ) ≤ Nat.sqrt Dn := by
    have : gn ≤ Nat.sqrt Dn := by
      rw [← Real.nat_floor_real_sqrt_eq_nat_sqrt]
      exact Nat.le_floor P.g_le_sqrt
    exact_mod_cast this
  have hS0 : (0 : ℝ) ≤ Nat.sqrt Dn := Nat.cast_nonneg _
  have hpiece : pieceSizeNat Dn gn = ⌈(Nat.sqrt Dn : ℝ) / (gn : ℝ)⌉₊ :=
    (Nat.ceil_div_eq_ceilDiv _ P.one_le_g).symm
  have hPl : (Nat.sqrt Dn : ℝ) / gn ≤ pieceSizeNat Dn gn := by
    rw [hpiece]; exact Nat.le_ceil _
  have : (pieceSizeNat Dn gn : ℝ) < (Nat.sqrt Dn : ℝ) / gn + 1 := by
    rw [hpiece]; exact Nat.ceil_lt_add_one (by positivity)
  have : 1 ≤ (Nat.sqrt Dn : ℝ) / gn := (one_le_div hg0).2 hgS
  have hSS : (Nat.sqrt Dn : ℝ) * Nat.sqrt Dn ≤ Dn :=
    (mul_le_mul hS1 hS1 hS0 (Real.sqrt_nonneg _)).trans_eq (Real.mul_self_sqrt hX0.le)
  have hSS' : (Dn : ℝ) / 4 ≤ (Nat.sqrt Dn : ℝ) * Nat.sqrt Dn := by
    have : (1 : ℝ) ≤ gn := by exact_mod_cast P.one_le_g
    have h1 : Real.sqrt Dn / 2 ≤ Nat.sqrt Dn := by linarith
    have := mul_le_mul h1 h1 (by positivity) hS0
    have := Real.mul_self_sqrt hX0.le
    nlinarith
  have hpow : (Dn : ℝ) ^ (1 - η) = (Dn : ℝ) / (Dn : ℝ) ^ η := by
    rw [Real.rpow_sub hX0, Real.rpow_one]
  rw [hpow, Nat.cast_mul]
  constructor
  · calc 1 / 8 * ((Dn : ℝ) / (Dn : ℝ) ^ η) = (Dn : ℝ) / 4 / (2 * (Dn : ℝ) ^ η) := by ring
      _ ≤ (Nat.sqrt Dn : ℝ) * Nat.sqrt Dn / gn :=
          div_le_div₀ (mul_nonneg hS0 hS0) hSS' hg0 P.g_le_rpow
      _ = (Nat.sqrt Dn : ℝ) / gn * Nat.sqrt Dn := by ring
      _ ≤ (pieceSizeNat Dn gn : ℝ) * Nat.sqrt Dn := mul_le_mul_of_nonneg_right hPl hS0
  · calc (pieceSizeNat Dn gn : ℝ) * Nat.sqrt Dn
        ≤ 2 * ((Nat.sqrt Dn : ℝ) / gn) * Nat.sqrt Dn :=
          mul_le_mul_of_nonneg_right (by linarith) hS0
      _ = 2 * ((Nat.sqrt Dn : ℝ) * Nat.sqrt Dn / gn) := by ring
      _ ≤ 2 * ((Dn : ℝ) / (Dn : ℝ) ^ η) :=
          mul_le_mul_of_nonneg_left (div_le_div₀ hX0.le hSS hXη P.rpow_le_g) (by norm_num)

theorem eventually_callParams {d η a ε γ q : ℝ} {D g : ℕ → ℕ} (ha : a = 1 - η) (ha0 : 0 < a)
    (hda1 : d * a < 1) (hγ : 0 ≤ γ) (hq : 0 ≤ q) (hthin : d * a < ε)
    (hP : ∀ᶠ n : ℕ in atTop, HostParams d η n (D n) (g n)) :
    ∃ K₁ K₂ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧
      ∀ᶠ n : ℕ in atTop,
        CallParams d a ε γ q K₁ K₂ n (pieceSizeNat (D n) (g n) * Nat.sqrt (D n)) := by
  have hτ : 0 < min ε 1 - d * a := sub_pos.2 (lt_min hthin hda1)
  have hc₀ : 0 < (1 / 8 : ℝ) / (2 : ℝ) ^ a := by positivity
  refine ⟨((1 / 8 : ℝ) / (2 : ℝ) ^ a) ^ (-γ), (2 : ℝ) ^ q, by positivity, by positivity, ?_⟩
  filter_upwards [hP, eventually_le_rpow hτ 2] with n P hn
  obtain ⟨hYl, hYu⟩ := ha ▸ P.pieceSize_bounds
  set Dcn := pieceSizeNat (D n) (g n) * Nat.sqrt (D n)
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast P.one_le_n
  have hN0 : (0 : ℝ) < n := by linarith
  have hX0 : (0 : ℝ) ≤ D n := Nat.cast_nonneg _
  have hXa : (D n : ℝ) ^ a ≤ (n : ℝ) ^ (d * a) := by
    rw [Real.rpow_mul hN0.le]
    exact Real.rpow_le_rpow hX0 P.D_le ha0.le
  have hXa' : (n : ℝ) ^ (d * a) / (2 : ℝ) ^ a ≤ (D n : ℝ) ^ a := by
    rw [Real.rpow_mul hN0.le, ← Real.div_rpow (by positivity) (by norm_num)]
    exact Real.rpow_le_rpow (by positivity) P.le_D ha0.le
  have : 0 ≤ (D n : ℝ) ^ a := by positivity
  have hlow : (1 / 8 : ℝ) / (2 : ℝ) ^ a * (n : ℝ) ^ (d * a) ≤ Dcn := by
    calc (1 / 8 : ℝ) / (2 : ℝ) ^ a * (n : ℝ) ^ (d * a)
        = 1 / 8 * ((n : ℝ) ^ (d * a) / (2 : ℝ) ^ a) := by ring
      _ ≤ 1 / 8 * (D n : ℝ) ^ a := mul_le_mul_of_nonneg_left hXa' (by norm_num)
      _ ≤ Dcn := hYl
  have hup : (Dcn : ℝ) ≤ 2 * (n : ℝ) ^ (d * a) :=
    hYu.trans (mul_le_mul_of_nonneg_left hXa (by norm_num))
  have hup' : 2 * (n : ℝ) ^ (d * a) ≤ (n : ℝ) ^ min ε 1 := by
    calc 2 * (n : ℝ) ^ (d * a) ≤ (n : ℝ) ^ (min ε 1 - d * a) * (n : ℝ) ^ (d * a) :=
          mul_le_mul_of_nonneg_right hn (by positivity)
      _ = (n : ℝ) ^ min ε 1 := by
          rw [← Real.rpow_add hN0]
          congr 1
          ring
  have hlow0 : 0 < (1 / 8 : ℝ) / (2 : ℝ) ^ a * (n : ℝ) ^ (d * a) := by positivity
  have hY0 : (0 : ℝ) < Dcn := hlow0.trans_le hlow
  refine ⟨Nat.succ_le_of_lt (by exact_mod_cast hY0), ?_, ?_, ?_, ?_⟩
  · exact (hup.trans hup').trans (Real.rpow_le_rpow_of_exponent_le hN1 (min_le_left _ _))
  · exact (hup.trans hup').trans
      ((Real.rpow_le_rpow_of_exponent_le hN1 (min_le_right _ _)).trans_eq (Real.rpow_one _))
  · calc (Dcn : ℝ) ^ (-γ) ≤ ((1 / 8 : ℝ) / (2 : ℝ) ^ a * (n : ℝ) ^ (d * a)) ^ (-γ) :=
          Real.rpow_le_rpow_of_nonpos hlow0 hlow (by linarith)
      _ = ((1 / 8 : ℝ) / (2 : ℝ) ^ a) ^ (-γ) * (n : ℝ) ^ (d * a * -γ) := by
          rw [Real.mul_rpow hc₀.le (by positivity), ← Real.rpow_mul hN0.le]
  · calc (Dcn : ℝ) ^ q ≤ (2 * (n : ℝ) ^ (d * a)) ^ q := Real.rpow_le_rpow hY0.le hup hq
      _ = (2 : ℝ) ^ q * (n : ℝ) ^ (d * a * q) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hN0.le]







theorem prod5_le {N x₁ x₂ x₃ x₄ x₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ E : ℝ} (hN : 1 ≤ N)
    (h0₂ : 0 ≤ x₂) (h0₃ : 0 ≤ x₃) (h0₄ : 0 ≤ x₄) (h0₅ : 0 ≤ x₅)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (hc₄ : 0 ≤ c₄) (hc₅ : 0 ≤ c₅)
    (h₁ : x₁ ≤ c₁ * N ^ e₁) (h₂ : x₂ ≤ c₂ * N ^ e₂) (h₃ : x₃ ≤ c₃ * N ^ e₃)
    (h₄ : x₄ ≤ c₄ * N ^ e₄) (h₅ : x₅ ≤ c₅ * N ^ e₅) (hE : e₁ + e₂ + e₃ + e₄ + e₅ ≤ E) :
    x₁ * x₂ * x₃ * x₄ * x₅ ≤ c₁ * c₂ * c₃ * c₄ * c₅ * N ^ E := by
  have hN0 : 0 < N := by linarith
  calc x₁ * x₂ * x₃ * x₄ * x₅
      ≤ c₁ * N ^ e₁ * (c₂ * N ^ e₂) * (c₃ * N ^ e₃) * (c₄ * N ^ e₄) * (c₅ * N ^ e₅) := by gcongr
    _ = c₁ * c₂ * c₃ * c₄ * c₅ * N ^ (e₁ + e₂ + e₃ + e₄ + e₅) := by
        rw [Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_add hN0]
        ring
    _ ≤ c₁ * c₂ * c₃ * c₄ * c₅ * N ^ E :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN hE) (by positivity)

theorem log_add_one_pow_three_le {N τ : ℝ} (hN : 1 ≤ N) (hτ : 0 < τ) :
    (Real.log N + 1) ^ 3 ≤ (3 / τ + 1) ^ 3 * N ^ τ := by
  have hN0 : 0 < N := by linarith
  have h3 : 0 < τ / 3 := by positivity
  have : Real.log N ≤ N ^ (τ / 3) / (τ / 3) := Real.log_le_rpow_div hN0.le h3
  have : 1 ≤ N ^ (τ / 3) := Real.one_le_rpow hN h3.le
  have hle : Real.log N + 1 ≤ (3 / τ + 1) * N ^ (τ / 3) := by
    have : N ^ (τ / 3) / (τ / 3) = 3 / τ * N ^ (τ / 3) := by field_simp
    linarith
  have hcube : (N ^ (τ / 3)) ^ 3 = N ^ τ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  calc (Real.log N + 1) ^ 3 ≤ ((3 / τ + 1) * N ^ (τ / 3)) ^ 3 :=
        pow_le_pow_left₀ (by linarith [Real.log_nonneg hN]) hle 3
    _ = (3 / τ + 1) ^ 3 * N ^ τ := by rw [mul_pow, hcube]

theorem logb_two_seven_le : Real.logb 2 7 ≤ 2.81 := by
  have h : Real.logb 2 7 ≤ 59 / 21 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
    refine le_of_pow_le_pow_left₀ (n := 21) (by norm_num) (by positivity) ?_
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (59 / 21 : ℝ)) 21, ← Real.rpow_mul (by norm_num)]
    norm_num
  exact h.trans (by norm_num)

theorem explicitFrom_mid (M : DetTimeModel) {d η ε γ q δ s : ℝ} {D g : ℕ → ℕ}
    (hd0 : 0 < d) (hη0 : 0 < η) (hη1 : η < 1 / 2) (hγ : 0 ≤ γ) (hq : 0 ≤ q) (hδ0 : 0 ≤ δ)
    (hsmall : 3 / 2 * d + δ ≤ 19 / 100)
    (hD : ∀ n, D n = ⌊(n : ℝ) ^ d⌋₊) (hg : ∀ n, g n = ⌈(D n : ℝ) ^ η⌉₊)
    (hhost : HostBound M strassen D g (fun n => pieceSizeNat (D n) (g n) * Nat.sqrt (D n)))
    (hlop : LopClaim M ε γ q) (hthin : d * (1 - η) < ε)
    (hs1 : s ≤ d * η) (hs2 : s ≤ d * (γ * (1 - η) - η))
    (hs3 : s ≤ d * (1 / 2 - q * (1 - η) - η)) (hδ : δ < s) : ExplicitFrom M δ 1 := by
  set a := 1 - η
  set Dc := fun n => pieceSizeNat (D n) (g n) * Nat.sqrt (D n)
  have ha0 : 0 < a := by linarith
  have ha1 : a ≤ 1 := by linarith
  have hd1 : d ≤ 1 := by linarith
  obtain ⟨C, hC, hhost⟩ := hhost
  obtain ⟨CL, Td, hTd, hlop⟩ := hlop
  obtain ⟨T, hT, hhost⟩ := hhost Td hTd
  have : d * a ≤ d * 1 := mul_le_mul_of_nonneg_left ha1 hd0.le
  have hP := eventually_hostParams hd0 hd1 hη0 hη1 hD hg
  obtain ⟨K₁, K₂, hK₁, hK₂, hQ⟩ := eventually_callParams (ε := ε) (γ := γ) (q := q) rfl ha0
    (by linarith) hγ hq hthin hP
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hP.and hQ)
  have hτ : 0 < s - δ := sub_pos.2 hδ
  obtain ⟨K', hK'⟩ : ∃ K' : ℝ, K' = (3 / (s - δ) + 1) ^ 3 := ⟨_, rfl⟩
  have hK'0 : 0 ≤ K' := by rw [hK']; positivity
  refine ⟨max n₀ 3, 4 * |CL| * (2 * K₁ * K') + 4 * |CL| * (4 * K₂ * K') + 4 * C * (4 * K')
    + C * (2 * K') + C + C * 2, T, hT, fun n κ u hn hκ hu => ?_⟩
  obtain ⟨P, Q⟩ := hn₀ n ((le_max_left _ _).trans hn)
  have hn3 : 3 ≤ n := (le_max_right _ _).trans hn
  have h17 := hhost n κ u P.sixteen_le P.le_n P.one_le_g P.g_le_sqrt hκ hu
  have hL := hlop n (Dc n) (queryCap n (D n)) P.one_le_n Q.one_le Q.le_rpow
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast P.one_le_n
  have hN0 : (0 : ℝ) < n := by linarith
  have hY1 : (1 : ℝ) ≤ Dc n := by exact_mod_cast Q.one_le
  have hY0 : (0 : ℝ) < Dc n := by linarith
  have hG0 : (0 : ℝ) ≤ g n := Nat.cast_nonneg _
  have hX0 : (0 : ℝ) ≤ D n := Nat.cast_nonneg _
  have hlogn : 1 ≤ Real.log n := Real.one_le_log_natCast_of_three_le hn3
  have : 0 ≤ Real.log (Dc n) := Real.log_nonneg hY1
  have : Real.log (Dc n) ≤ Real.log n := Real.log_le_log hY0 Q.le_n
  have hL1 : 1 ≤ Real.log n + 1 := by linarith
  have hL3 : (Real.log n + 1) ^ 3 ≤ K' * (n : ℝ) ^ (s - δ) := by
    rw [hK']; exact log_add_one_pow_three_le hN1 hτ
  have hlam2 : (Real.log (Dc n) + 1) ^ 2 ≤ K' * (n : ℝ) ^ (s - δ) :=
    ((pow_le_pow_left₀ (by linarith) (by linarith) 2).trans
      (pow_le_pow_right₀ hL1 (by norm_num))).trans hL3
  have hlam1 : Real.log (Dc n) + 1 ≤ K' * (n : ℝ) ^ (s - δ) :=
    ((by linarith : Real.log (Dc n) + 1 ≤ Real.log n + 1).trans
      (le_self_pow₀ hL1 (by norm_num))).trans hL3
  have hlam0 : (1 : ℝ) ≤ K' * (n : ℝ) ^ (s - δ) := (one_le_pow₀ hL1).trans hL3
  have hlamn : Real.log n ≤ K' * (n : ℝ) ^ (s - δ) :=
    ((by linarith : Real.log n ≤ Real.log n + 1).trans (le_self_pow₀ hL1 (by norm_num))).trans hL3
  have fN : (n : ℝ) ≤ 1 * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one, one_mul]
  have fN2 : (n : ℝ) ^ 2 ≤ 1 * (n : ℝ) ^ (2 : ℝ) := by rw [Real.rpow_two, one_mul]
  have fN3 : (n : ℝ) ^ 3 ≤ 1 * (n : ℝ) ^ (3 : ℝ) := by
    rw [one_mul, ← Real.rpow_natCast]
    norm_num
  have f1 : (1 : ℝ) ≤ 1 * (n : ℝ) ^ (0 : ℝ) := by rw [Real.rpow_zero, one_mul]
  have fG := P.g_le hη0.le
  have fGi := P.inv_g_le hη0.le (by linarith)
  have hw : (queryCap n (D n) : ℝ) ≤ (n : ℝ) ^ 2 / Real.sqrt (D n) :=
    Nat.floor_le (by positivity)
  have fW : (n : ℝ) ^ 2 / Real.sqrt (D n) ≤ 2 * (n : ℝ) ^ (2 + -(d / 2)) := by
    rw [Real.rpow_add hN0, Real.rpow_two, div_eq_mul_one_div]
    calc (n : ℝ) ^ 2 * (1 / Real.sqrt (D n)) ≤ (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ (-(d / 2))) :=
          mul_le_mul_of_nonneg_left P.inv_sqrt_le (by positivity)
      _ = 2 * ((n : ℝ) ^ 2 * (n : ℝ) ^ (-(d / 2))) := by ring
  have fX : (D n : ℝ) ≤ 1 * (n : ℝ) ^ d := by rw [one_mul]; exact P.D_le
  have fX32 : (D n : ℝ) ^ (3 / 2 : ℝ) ≤ 1 * (n : ℝ) ^ (d * (3 / 2)) := by
    rw [one_mul, Real.rpow_mul hN0.le]
    exact Real.rpow_le_rpow hX0 P.D_le (by norm_num)
  have fMM : strassen n ≤ 1 * (n : ℝ) ^ (2.81 : ℝ) := by
    rw [one_mul]
    exact Real.rpow_le_rpow_of_exponent_le hN1 logb_two_seven_le
  have hdη : d * η ≤ d * (1 / 2) := mul_le_mul_of_nonneg_left hη1.le hd0.le
  have : 0 ≤ d * (q * a) := by positivity
  have t1 : (n : ℝ) * g n * preBound31 γ n (Dc n) ≤ 2 * K₁ * K' * (n : ℝ) ^ (3 - δ) := by
    have e : (n : ℝ) * g n * preBound31 γ n (Dc n)
        = (n : ℝ) * g n * (n : ℝ) ^ 2 * (Dc n : ℝ) ^ (-γ) * (Real.log (Dc n) + 1) ^ 2 := by
      rw [preBound31, Real.rpow_neg hY0.le]
      ring
    rw [e]
    exact (prod5_le (E := 3 - δ) hN1 hG0 (by positivity) (by positivity) (by positivity)
      (by norm_num) (by norm_num) (by norm_num) hK₁ hK'0 fN fG fN2 Q.neg_rpow_le hlam2
      (by linarith)).trans_eq (by ring)
  have t2 : (n : ℝ) * g n * ((queryCap n (D n) : ℝ) * queryBound31 q (Dc n))
      ≤ 4 * K₂ * K' * (n : ℝ) ^ (3 - δ) := by
    have e : (n : ℝ) * g n * ((queryCap n (D n) : ℝ) * queryBound31 q (Dc n))
        = (n : ℝ) * g n * (queryCap n (D n) : ℝ) * (Dc n : ℝ) ^ q * (Real.log (Dc n) + 1) := by
      rw [queryBound31]
      ring
    rw [e]
    exact (prod5_le (E := 3 - δ) hN1 hG0 (by positivity) (by positivity) (by linarith)
      (by norm_num) (by norm_num) (by norm_num) hK₂ hK'0 fN fG (hw.trans fW) Q.rpow_le hlam1
      (by linarith)).trans_eq (by ring)
  have t3 : (n : ℝ) * g n * ((n : ℝ) ^ 2 / Real.sqrt (D n)) ≤ 4 * K' * (n : ℝ) ^ (3 - δ) := by
    have e : (n : ℝ) * g n * ((n : ℝ) ^ 2 / Real.sqrt (D n))
        = (n : ℝ) * g n * ((n : ℝ) ^ 2 / Real.sqrt (D n)) * 1 * 1 := by ring
    rw [e]
    exact (prod5_le (E := 3 - δ) hN1 hG0 (by positivity) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hK'0 fN fG fW f1 hlam0
      (by linarith)).trans_eq (by ring)
  have t4 : termScans n (g n) κ ≤ κ * (2 * K' * (n : ℝ) ^ (3 - δ)) := by
    have e : termScans n (g n) κ
        = κ * ((n : ℝ) ^ 3 * (1 / (g n : ℝ)) * 1 * 1 * Real.log n) := by
      rw [termScans]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left ((prod5_le (E := 3 - δ) hN1 (by positivity) (by norm_num)
      (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hK'0
      fN3 fGi f1 f1 hlamn (by linarith)).trans_eq (by ring)) (by linarith)
  have t5 : termPrime strassen n (D n) ≤ (n : ℝ) ^ (3 - δ) := by
    have e : termPrime strassen n (D n) = strassen n * (D n : ℝ) ^ (3 / 2 : ℝ) * 1 * 1 * 1 := by
      rw [termPrime]
      ring
    rw [e]
    exact (prod5_le (E := 3 - δ) hN1 (by positivity) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) fMM fX32 f1 f1 f1
      (by linarith)).trans_eq (by ring)
  have t6 : termBuild n (D n) (g n) ≤ 2 * (n : ℝ) ^ (3 - δ) := by
    have e : termBuild n (D n) (g n) = (n : ℝ) ^ 2 * (D n : ℝ) * (g n : ℝ) * 1 * 1 := by
      rw [termBuild]
      ring
    rw [e]
    exact (prod5_le (E := 3 - δ) hN1 hX0 hG0 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) fN2 fX fG f1 f1
      (by linarith)).trans_eq (by ring)
  have hS0 : 0 ≤ (n : ℝ) ^ (3 - δ) := by positivity
  have hpre0 : 0 ≤ preBound31 γ n (Dc n) := by rw [preBound31]; positivity
  have hquery0 : 0 ≤ queryBound31 q (Dc n) := by
    rw [queryBound31]
    exact mul_nonneg (by positivity) (by linarith)
  have hS : (n : ℝ) ^ (3 - δ) ≤ κ * ((n : ℝ) ^ (3 - δ) * Real.log n ^ 1) := by
    rw [pow_one]
    calc (n : ℝ) ^ (3 - δ) = 1 * ((n : ℝ) ^ (3 - δ) * 1) := by ring
      _ ≤ κ * ((n : ℝ) ^ (3 - δ) * Real.log n) :=
          mul_le_mul hκ (mul_le_mul_of_nonneg_left hlogn hS0) (by positivity) (by linarith)
  have hκS : κ * (n : ℝ) ^ (3 - δ) ≤ κ * ((n : ℝ) ^ (3 - δ) * Real.log n ^ 1) := by
    rw [pow_one]
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hS0 hlogn) (by linarith)
  have := abs_nonneg CL
  have hB : 0 ≤ preBound31 γ n (Dc n) + (queryCap n (D n) : ℝ) * queryBound31 q (Dc n) :=
    add_nonneg hpre0 (mul_nonneg (Nat.cast_nonneg _) hquery0)
  have := hL.trans (mul_le_mul_of_nonneg_right (le_abs_self CL) hB)
  have : 4 * (n : ℝ) * g n *
        (Td n (Dc n) (queryCap n (D n)) + C * ((n : ℝ) ^ 2 / Real.sqrt (D n)))
      ≤ 4 * (n : ℝ) * g n *
        (|CL| * (preBound31 γ n (Dc n) + (queryCap n (D n) : ℝ) * queryBound31 q (Dc n)) +
          C * ((n : ℝ) ^ 2 / Real.sqrt (D n))) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have := mul_le_mul_of_nonneg_left t1 (by positivity : 0 ≤ 4 * |CL|)
  have := mul_le_mul_of_nonneg_left t2 (by positivity : 0 ≤ 4 * |CL|)
  have := mul_le_mul_of_nonneg_left t3 (by positivity : 0 ≤ 4 * C)
  have := mul_le_mul_of_nonneg_left t4 hC
  have := mul_le_mul_of_nonneg_left t5 hC
  have := mul_le_mul_of_nonneg_left t6 hC
  have := mul_le_mul_of_nonneg_left hS
    (by positivity : 0 ≤ 4 * |CL| * (2 * K₁ * K') + 4 * |CL| * (4 * K₂ * K') +
      4 * C * (4 * K') + C + C * 2)
  have := mul_le_mul_of_nonneg_left hκS (by positivity : 0 ≤ C * (2 * K'))
  linarith [h17]






open ThreeSumApsp.WordRam Light.Sec3

noncomputable def g2Hi (k : ℤ) (c δ : ℝ) : ℝ :=
  -(c - 1) * logLo 0 ((c - 1 + δ) / (c - 1)) - δ * logLo k (c - 1 + δ)
    - (1 - δ) * logLo 0 (1 - δ) + δ * (2 * logThreeHi)

noncomputable def cEntHi (k : ℤ) (c : ℝ) : ℝ := (c - 1) * logHi 0 (c / (c - 1)) + logHi k c

theorem le_gammaX (k : ℤ) {c θ r : ℝ} (hc : 1 < c := by numerics) (h0 : 0 ≤ θ := by numerics)
    (h1 : θ < 1 := by numerics) (hr : 0 ≤ r := by numerics)
    (h : r * (2 * logTwoHi) ≤ -g2Hi k c θ := by unfold g2Hi; numerics) : r ≤ gammaX c θ := by
  have hc1 : 0 < c - 1 := sub_pos.2 hc
  have hcδ : 0 < c - 1 + θ := by linarith
  have hθ1 : 0 < 1 - θ := sub_pos.2 h1
  have heq : g2 c θ = -(c - 1) * log ((c - 1 + θ) / (c - 1)) - θ * log (c - 1 + θ)
      - (1 - θ) * log (1 - θ) + θ * (2 * log 3) := by
    rw [g2, log_div hcδ.ne' hc1.ne', log_nine]
    simp only [negMulLog]; ring
  rw [gammaX, le_div_iff₀ log_four_pos]
  unfold g2Hi logLo at h
  linarith [heq, mul_le_mul_of_nonneg_left (log_mem 0 4 (div_pos hcδ hc1)).1 hc1.le,
    mul_le_mul_of_nonneg_left (log_mem k 4 hcδ).1 h0,
    mul_le_mul_of_nonneg_left (log_mem 0 4 hθ1).1 hθ1.le,
    mul_le_mul_of_nonneg_left log_three_le h0,
    mul_le_mul_of_nonneg_left logFour_mem.2 hr]

theorem basePruned_le (k : ℤ) {c r : ℝ} (hc : 1 < c := by numerics)
    (h : 1 / 2 * cEntHi k c + (c - 1) * logThreeHi ≤ r := by unfold cEntHi; numerics) :
    basePruned c ≤ r := by
  have hc1 : 0 < c - 1 := sub_pos.2 hc
  have hc0 : 0 < c := by linarith
  have heq : cEntropy c = (c - 1) * log (c / (c - 1)) + log c := by
    rw [cEntropy, log_div hc0.ne' hc1.ne']
    simp only [negMulLog]; ring
  rw [basePruned, heq]
  unfold cEntHi logHi at h
  linarith [mul_le_mul_of_nonneg_left (log_mem 0 4 (div_pos hc0 hc1)).2 hc1.le,
    (log_mem k 4 hc0).2, mul_le_mul_of_nonneg_left log_three_le hc1.le]

theorem explicitFrom_22 (M : DetTimeModel) (hM : M.lopDetect = lightModel.lopDetect)
    (hhost : MidHostRat M) : ExplicitFrom M 0.0020905 1 := by
  have : basePruned ((109 : ℕ) / (5 : ℕ)) ≤ 24.88045 := by
    simpa using (basePruned_le 4 : basePruned (109 / 5) ≤ 24.88045)
  have hγX : (0.075383 : ℝ) ≤ gammaX ((109 : ℕ) / (5 : ℕ)) ((29 : ℕ) / (250 : ℕ)) := by
    simpa using (le_gammaX 4 : (0.075383 : ℝ) ≤ gammaX (109 / 5) (29 / 250))
  have hq_hi : qOf ((29 : ℕ) / (250 : ℕ)) ≤ 0.44274 := by
    simpa using (qOf_le (-3) : qOf (29 / 250) ≤ 0.44274)
  have h4 := logFour_mem
  have : 0 < basePruned ((109 : ℕ) / (5 : ℕ)) := basePruned_pos (by norm_num)
  obtain ⟨m₁, h₁⟩ := offlineWithinP cShared30 (a := 109) (b := 5) (p := 29) (q := 250)
    (γ := 0.07538) (ε := 0.05548) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by linarith)
    (by
      unfold RcP thinR
      norm_num [logTwoLo, logTwoHi] at h4
      rw [lt_div_iff₀ (by linarith [h4.1])]
      linarith [h4.1, h4.2])
  obtain ⟨m₂, h₂⟩ := exists_fitsRS (a := 109) (b := 5) (p := 29) (q := 250) (r := 18)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [logTwoLo] at h4; linarith [h4.1])
  have hm₀ : 1 ≤ max (max m₁ m₂) 1 := le_max_right _ _
  have hthin : ThinClaim lightModel 0.05548 0.07538 (qOf ((29 : ℕ) / (250 : ℕ))) :=
    thinClaimP_of_offlineWithinT
      (G := ⟨109, 5, 29, 250, max (max m₁ m₂) 1, by norm_num, by norm_num, by norm_num,
        by norm_num⟩)
      (by norm_num) (h₂ _ hm₀ ((le_max_right _ _).trans (le_max_left _ _))) (by norm_num)
      (h₁ _ hm₀ ((le_max_left _ _).trans (le_max_left _ _)))
  have hq0 := qOf_nonneg (θ := (29 : ℕ) / (250 : ℕ)) (by norm_num) (by norm_num)
  obtain ⟨C, Td, hTd, hb⟩ :=
    lopClaim_of_thinClaim lightModel (by norm_num) hq0 (by norm_num) hthin
      claim_lopCountFromThinProduct claim_lopDetectFromCount
  exact explicitFrom_mid M (d := (27 : ℕ) / (469 : ℕ)) (η := (13 : ℕ) / (358 : ℕ))
    (s := 0.002090505) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hq0 (by norm_num)
    (by norm_num) (fun _ => rfl) (fun _ => rfl) hhost ⟨C, Td, hM ▸ hTd, hb⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num at hq_hi ⊢; linarith) (by norm_num)

theorem threeSum_pruned : EndStatement.ThreeSum.SolvedInTime 1.99896 :=
  threeSum_of_uniform (by norm_num)
    (exactTriangleUniform_of_explicitFrom lightModel 1 (by norm_num) (by norm_num)
      (explicitFrom_22 lightModel rfl midHostRat_light) claim_bruteForce'
      closure_chooseBySize fun _ _ hle hT => SolvedIn.mono hT hle)
    (by norm_num) (by norm_num)

theorem exactTriangle_pruned : EndStatement.ExactTriangle.SolvedInTime 2.99791 := by
  obtain ⟨n₀, K, T, hT, hb⟩ := explicitFrom_22 lightModel rfl midHostRat_light
  refine FromClaims.solvedInTime_of_claim realized_exactTriangle (by norm_num) fun κ _ =>
    ⟨T, hT, UpperPowPolylog.upperBigOPow (a := 3 - 0.0020905) ⟨K * max κ 1, 1, ?_⟩ (by norm_num)⟩
  filter_upwards [Filter.eventually_ge_atTop (max n₀ 1)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have := hb n (max κ 1) ((n : ℝ) ^ κ) (le_trans (le_max_left _ _) hn) (le_max_right _ _)
    (Real.rpow_le_rpow_of_exponent_le hn1 (le_max_left _ _))
  linarith

theorem minPlus_allEdges_pruned : EndStatement.MinPlusProduct.SolvedInTime 2.99791 :=
  FromClaims.solvedInTime_of_claim realized_minPlusProduct (by norm_num)
    ((AllEdges.minPlusInPolylog_of_explicitFrom (by norm_num)
      (explicitFrom_22 AllEdges.lightModelAE rfl AllEdges.midHostRat_ae)).mono
      fun _ hf => hf.upperBigOPow (by norm_num))

theorem apsp_allEdges_pruned : EndStatement.APSP.SolvedInTime 2.99791 :=
  FromClaims.solvedInTime_of_claim realized_apsp (by norm_num)
    ((AllEdges.apspInPolylog_of_explicitFrom (by norm_num)
      (explicitFrom_22 AllEdges.lightModelAE rfl AllEdges.midHostRat_ae)).mono
      fun _ hf => hf.upperBigOPow (by norm_num))

end ImprovedExponents
