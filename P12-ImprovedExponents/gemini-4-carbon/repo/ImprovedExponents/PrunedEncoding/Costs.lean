module

public import ThreeSumApsp.Sec4.Theorem30
public import ImprovedExponents.ExactCount.Tail
public import ImprovedExponents.PrunedProgram.Work
public import ThreeSumApsp.Sec2.Orders
import all ThreeSumApsp.Sec4.Corollary31

@[expose] public section

namespace ImprovedExponents

open ThreeSumApsp Real Finset

open private levelsOf_le from ThreeSumApsp.Sec4.Corollary31

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
  have hboxes : ((boxes L m t).card : ℝ) ≤ ((m : ℝ) + 1) * ∑ d ∈ Finset.Icc t m, (beta L m d : ℝ) := by
    exact_mod_cast lemma_29_count L m t hL ht
  have h1 : ((numBands L m N : ℝ)) ^ 2 * ((boxes L m t).card : ℝ)
      ≤ 4 * ((m : ℝ) + 1) * tailX L m t * (N : ℝ) ^ 2 :=
    (mul_le_mul (Theorem30.tiles hm hL hN) hboxes (Nat.cast_nonneg _) (by positivity)).trans_eq
      (by unfold tailX; ring)
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have htail := tailX_nonneg L m t
  calc (L : ℝ) * ((numBands L m N : ℝ) ^ 2 * ((boxes L m t).card : ℝ))
      ≤ (L : ℝ) * (4 * ((m : ℝ) + 1) * tailX L m t * (N : ℝ) ^ 2) := by gcongr
    _ ≤ (L : ℝ) * (4 * (2 * (m : ℝ)) * tailX L m t * (N : ℝ) ^ 2) := by gcongr; linarith
    _ = 8 * ((L : ℝ) * (m : ℝ) * tailX L m t * (N : ℝ) ^ 2) := by ring

theorem first_termX {c θ γ : ℝ} (hc : 10 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hγ : γ < gammaX c θ) :
    Dominated (fun m : ℕ => 1 ≤ m)
      (fun m => (levelsOf c m : ℝ) * m * tailX (levelsOf c m) m (switchOf θ m))
      fun m => (D m : ℝ) ^ (-γ) * Real.log (D m) ^ 2 := by
  refine .of_le_const_mul (C := 2 * (c + 1) * (c + 2) * (2 / ((gammaX c θ - γ) * log 4) ^ 2))
    (by positivity) fun m hm => ?_
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hL : (levelsOf c m : ℝ) ≤ (c + 1) * m := levelsOf_le hc hm
  have hmL : m ≤ levelsOf c m := by have := ten_mul_le_levelsOf hc m; omega
  have hM : (0 : ℝ) < M (levelsOf c m) m := sqrtKN0_sq (levelsOf c m) m ▸ pow_pos (sqrtKN0_pos hmL) 2
  have htail : tailX (levelsOf c m) m (switchOf θ m)
      ≤ ((m : ℝ) + 1) * (((levelsOf c m : ℝ) + 1) * (D m : ℝ) ^ (-gammaX c θ)) := by
    unfold tailX; rw [div_le_iff₀ hM]; exact (sum_beta_le_rpow hc hθ0 hθ1 hm).trans_eq (by ring)
  have hsplit : (D m : ℝ) ^ (-gammaX c θ) = (D m : ℝ) ^ (-(gammaX c θ - γ)) * (D m : ℝ) ^ (-γ) := by
    rw [← rpow_add (cast_D_pos m)]; congr 1; ring
  have hsq : (m : ℝ) ^ 2 * (D m : ℝ) ^ (-(gammaX c θ - γ)) ≤ 2 / ((gammaX c θ - γ) * log 4) ^ 2 := by
    have hx : 0 ≤ (gammaX c θ - γ) * ((m : ℝ) * log 4) := by positivity
    have hexp := quadratic_le_exp_of_nonneg hx
    rw [cast_D_rpow, show -(gammaX c θ - γ) * ((m : ℝ) * log 4) = -((gammaX c θ - γ) * ((m : ℝ) * log 4)) by ring,
      exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (exp_pos _) (by positivity)]
    linarith 
  have hmlog : (m : ℝ) ≤ Real.log (D m) := cast_le_log_cast_D m
  calc (levelsOf c m : ℝ) * m * tailX (levelsOf c m) m (switchOf θ m)
      ≤ (c + 1) * m * m * (((m : ℝ) + 1) * (((levelsOf c m : ℝ) + 1) * (D m : ℝ) ^ (-gammaX c θ))) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg m)) htail (tailX_nonneg _ _ _) (by positivity)
    _ ≤ (c + 1) * m * m * ((2 * (m : ℝ)) * (((c + 2) * m) * (D m : ℝ) ^ (-gammaX c θ))) := by
        gcongr <;> linarith
    _ = 2 * (c + 1) * (c + 2) * ((m : ℝ) ^ 2 * (D m : ℝ) ^ (-(gammaX c θ - γ)))
          * ((D m : ℝ) ^ (-γ) * (m : ℝ) ^ 2) := by rw [hsplit]; ring
    _ ≤ 2 * (c + 1) * (c + 2) * (2 / ((gammaX c θ - γ) * log 4) ^ 2)
          * ((D m : ℝ) ^ (-γ) * Real.log (D m) ^ 2) := by gcongr

noncomputable def cost8P (L m t N : ℕ) : ℝ :=
  (L : ℝ) * (m : ℝ) * tailX L m t * (N : ℝ) ^ 2
    + (N : ℝ) * (L : ℝ) * (27 / 2 * (M L m : ℝ) / (1 - rho L m)) / sqrtKN0 L m

theorem encodingP_eq {L m : ℕ} (hmL : m ≤ L) (N : ℕ) :
    (N : ℝ) * (L : ℝ) * (27 / 2 * (M L m : ℝ) / (1 - rho L m)) / sqrtKN0 L m
      = 27 / 2 * (N : ℝ) * ((L : ℝ) * sqrtKN0 L m) / (1 - rho L m) := by
  rw [← sqrtKN0_sq]; grind

theorem eq_10P {c γ ε : ℝ} (hc : 10 < c) (hγ : 0 ≤ γ) (hε0 : 0 < ε) (hε : ε < RcP c γ) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ D₀ N : ℕ, 4 ^ (m - 1) < D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
      (D m : ℝ) ^ γ * ((levelsOf c m : ℝ) * sqrtKN0 (levelsOf c m) m) ≤ (N : ℝ) := by
  have hden := thinR_den_pos (basePruned_pos (c := c) (by linarith)) hγ
  set G : ℝ := log 4 / ε with hGdef
  have hG : basePruned c + γ * log 4 < G := by
    rw [hGdef, lt_div_iff₀ hε0]; linarith [(lt_div_iff₀ hden).1 hε]
  set B : ℝ := (basePruned c + (G - γ * log 4)) / 2 with hBdef
  have hB1 : basePruned c < B := by rw [hBdef]; linarith
  set η : ℝ := G - γ * log 4 - B with hηdef
  have hη : 0 < η := by rw [hηdef, hBdef]; linarith
  obtain ⟨δ₀, hδ₀, hnear⟩ := Metric.eventually_nhds_iff.1
    ((basePruned_continuousOn.continuousAt (Ioi_mem_nhds hc)).eventually (gt_mem_nhds hB1))
  refine ⟨max 1 (max ⌈1 / δ₀⌉₊ ⌈2 * (c + 1) * exp G / η ^ 2⌉₊), fun m hm D₀ N hgt hthin => ?_⟩
  have hm1 : 1 ≤ m := (le_max_left _ _).trans hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmδ : 1 / δ₀ ≤ (m : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_left _ _).trans ((le_max_right _ _).trans hm))
  have hmη : 2 * (c + 1) * exp G / η ^ 2 ≤ (m : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hm))
  have hLge : c * m ≤ (levelsOf c m : ℝ) := Nat.le_ceil _
  have hLlt : (levelsOf c m : ℝ) < c * m + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmL : m < levelsOf c m := by exact_mod_cast (show (m : ℝ) < levelsOf c m by nlinarith)
  have hbase : basePruned ((levelsOf c m : ℝ) / m) < B := by
    refine hnear ?_; rw [Real.dist_eq, abs_lt]
    have := (div_le_iff₀ hδ₀).1 hmδ
    have : c ≤ (levelsOf c m : ℝ) / m := (le_div_iff₀ hm0).2 hLge
    exact ⟨by linarith, by rw [sub_lt_iff_lt_add, div_lt_iff₀ hm0]; nlinarith⟩
  have hLle : (levelsOf c m : ℝ) ≤ (c + 1) * m := levelsOf_le hc hm1
  have hsqrt : sqrtKN0 (levelsOf c m) m ≤ exp ((m : ℝ) * B) :=
    (sqrtKN0_le_exp hm1 hmL).trans (exp_le_exp.2 (mul_le_mul_of_nonneg_left hbase.le hm0.le))
  have hN : exp (((m : ℝ) - 1) * G) ≤ (N : ℝ) := by
    have h := Corollary31.hypothesis hm1 hε0 hgt hthin
    rwa [rpow_def_of_pos (by norm_num),
      show log 4 * (((m : ℝ) - 1) / ε) = ((m : ℝ) - 1) * (log 4 / ε) by ring] at h
  have hexp : (c + 1) * m * exp G ≤ exp ((m : ℝ) * η) := by
    have hq := quadratic_le_exp_of_nonneg (mul_nonneg hm0.le hη.le)
    have h1 := mul_le_mul_of_nonneg_left ((div_le_iff₀ (pow_pos hη 2)).1 hmη) hm0.le
    have : 0 ≤ (m : ℝ) * η := mul_nonneg hm0.le hη.le
    linarith
  calc (D m : ℝ) ^ γ * ((levelsOf c m : ℝ) * sqrtKN0 (levelsOf c m) m)
      ≤ exp (γ * ((m : ℝ) * log 4)) * ((c + 1) * m * exp ((m : ℝ) * B)) := by
        rw [cast_D_rpow]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hLle hsqrt (sqrtKN0_pos hmL.le).le (by positivity)) (exp_pos _).le
    _ = (c + 1) * m * (exp (γ * ((m : ℝ) * log 4)) * exp ((m : ℝ) * B)) := by ring
    _ = (c + 1) * m * exp G * exp ((m : ℝ) * (B + γ * log 4) - G) := by
        rw [show exp (γ * ((m : ℝ) * log 4)) * exp ((m : ℝ) * B)
          = exp G * exp ((m : ℝ) * (B + γ * log 4) - G) by rw [← exp_add, ← exp_add]; congr 1; ring]
        ring
    _ ≤ exp ((m : ℝ) * η) * exp ((m : ℝ) * (B + γ * log 4) - G) :=
        mul_le_mul_of_nonneg_right hexp (exp_pos _).le
    _ = exp (((m : ℝ) - 1) * G) := by rw [← exp_add, hηdef]; congr 1; ring
    _ ≤ N := hN

theorem costsP {c θ γ ε : ℝ} (hc : 10 < c) (hθ0 : 0 < θ) (hθ1 : θ < 0.9) (hγ0 : 0 ≤ γ)
    (hγ : γ < gammaX c θ) (hε0 : 0 < ε) (hε : ε < RcP c γ) :
    ∃ (C : ℝ) (m₀ : ℕ), 0 ≤ C ∧ ∀ D₀ N m : ℕ, 2 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
      m = ⌈Real.logb 4 (D₀ : ℝ)⌉₊ → m₀ ≤ m →
      sqrtKN0 (levelsOf c m) m ≤ N ∧
      cost8P (levelsOf c m) m (switchOf θ m) N
        ≤ C * ((N : ℝ) ^ 2 * Real.log (D₀ : ℝ) ^ 2 / (D₀ : ℝ) ^ γ) ∧
      costQuery (levelsOf c m) m (switchOf θ m) ≤ C * ((D₀ : ℝ) ^ qOf θ * Real.log (D₀ : ℝ)) := by
  obtain ⟨m₀, heq10⟩ := eq_10P hc hγ0 hε0 hε
  have h10 (p : Sizes) (hp : p.Corollary31 ε m₀) :
      (D p.m : ℝ) ^ γ * ((levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m) ≤ p.N :=
    heq10 p.m hp.large p.D₀ p.N hp.setUp.gt hp.thin
  have hρ : rhoC c < 1 := rhoC_lt_one hc
  have hboxes : Dominated (Sizes.Corollary31 ε m₀)
      (fun p => (levelsOf c p.m : ℝ) * p.m * tailX (levelsOf c p.m) p.m (switchOf θ p.m) * (p.N : ℝ) ^ 2)
      fun p => (D p.m : ℝ) ^ (-γ) * Real.log (D p.m) ^ 2 * (p.N : ℝ) ^ 2 :=
    ((first_termX hc hθ0.le (by linarith) hγ).comp Sizes.m fun _ hp => hp.setUp.m_pos).mul_right
      fun _ _ => sq_nonneg _
  have henc : Dominated (Sizes.Corollary31 ε m₀)
      (fun p => (p.N : ℝ) * (levelsOf c p.m : ℝ)
        * (27 / 2 * (M (levelsOf c p.m) p.m : ℝ) / (1 - rho (levelsOf c p.m) p.m))
        / sqrtKN0 (levelsOf c p.m) p.m)
      fun p => (D p.m : ℝ) ^ (-γ) * Real.log (D p.m) ^ 2 * (p.N : ℝ) ^ 2 := by
    refine .of_le_const_mul (C := 27 / 2 / (1 - rhoC c))
      (div_nonneg (by norm_num) (sub_pos.2 hρ).le) fun p hp => ?_
    have hm1 : 1 ≤ p.m := hp.setUp.m_pos
    have hmL : p.m ≤ levelsOf c p.m := by have := ten_mul_le_levelsOf hc p.m; omega
    have hrho : rho (levelsOf c p.m) p.m < rhoC c := Corollary31.rho_lt hc p.m
    have hLs0 : 0 ≤ (levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m :=
      mul_nonneg (Nat.cast_nonneg _) (sqrtKN0_pos hmL).le
    have hLs : (levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m ≤ (D p.m : ℝ) ^ (-γ) * p.N := by
      rw [rpow_neg (cast_D_pos p.m).le, inv_mul_eq_div,
        le_div_iff₀ (rpow_pos_of_pos (cast_D_pos p.m) γ), mul_comm]
      exact h10 p hp
    have hlog : (1 : ℝ) ≤ Real.log (D p.m) ^ 2 :=
      one_le_pow₀ ((Nat.one_le_cast.2 hm1).trans (cast_le_log_cast_D p.m))
    rw [encodingP_eq hmL]
    calc 27 / 2 * (p.N : ℝ) * ((levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m)
          / (1 - rho (levelsOf c p.m) p.m)
        ≤ 27 / 2 * (p.N : ℝ) * ((levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m) / (1 - rhoC c) :=
          div_le_div_of_nonneg_left (mul_nonneg (by positivity) hLs0) (sub_pos.2 hρ) (by linarith)
      _ ≤ 27 / 2 * (p.N : ℝ) * ((D p.m : ℝ) ^ (-γ) * p.N) / (1 - rhoC c) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLs (by positivity)) (sub_pos.2 hρ).le
      _ = 27 / 2 / (1 - rhoC c) * ((D p.m : ℝ) ^ (-γ) * 1 * (p.N : ℝ) ^ 2) := by ring
      _ ≤ 27 / 2 / (1 - rhoC c) * ((D p.m : ℝ) ^ (-γ) * Real.log (D p.m) ^ 2 * (p.N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlog (rpow_nonneg (Nat.cast_nonneg _) _)) (sq_nonneg _))
            (div_nonneg (by norm_num) (sub_pos.2 hρ).le)
  have hpre : Dominated (Sizes.Corollary31 ε m₀)
      (fun p => cost8P (levelsOf c p.m) p.m (switchOf θ p.m) p.N)
      fun p => (p.N : ℝ) ^ 2 * Real.log p.D₀ ^ 2 / (p.D₀ : ℝ) ^ γ :=
    ((hboxes.add henc).trans (((padded_le (-γ) 2).mono_dom fun _ hp => hp.setUp).mul_right
      fun _ _ => sq_nonneg _)).congr (fun _ _ => rfl) fun p _ => by
      rw [Real.rpow_neg (Nat.cast_nonneg _)]; ring
  have hquery : Dominated (Sizes.Corollary31 ε m₀)
      (fun p => costQuery (levelsOf c p.m) p.m (switchOf θ p.m))
      fun p => (p.D₀ : ℝ) ^ qOf θ * Real.log p.D₀ :=
    (((Corollary31.query_cost hc hθ0 hθ1).comp Sizes.m fun _ hp => hp.m_pos).trans
      (by simpa  using padded_le (qOf θ) 1)).mono_dom fun _ hp => hp.setUp
  obtain ⟨C, hC, hboth⟩ := hpre.exists_const_and hquery
    (fun _ _ => by positivity)
    fun _ hp => mul_nonneg (by positivity)
      (Real.log_nonneg (Nat.one_le_cast.2 (one_le_two.trans hp.setUp.two_le)))
  refine ⟨C, m₀, hC, fun D₀ N m hD hDN hm hm₀ => ?_⟩
  have hp : Sizes.Corollary31 ε m₀ ⟨D₀, N, m⟩ := ⟨⟨hD, hm⟩, hDN, hm₀⟩
  have hm1 : 1 ≤ m := hp.setUp.m_pos
  have hL10 := ten_mul_le_levelsOf hc m
  have hs := (sqrtKN0_pos (by omega : m ≤ levelsOf c m)).le
  refine ⟨?_, hboth ⟨D₀, N, m⟩ hp⟩
  calc sqrtKN0 (levelsOf c m) m
      ≤ (levelsOf c m : ℝ) * sqrtKN0 (levelsOf c m) m :=
        le_mul_of_one_le_left hs (Nat.one_le_cast.2 (by omega))
    _ ≤ (D m : ℝ) ^ γ * ((levelsOf c m : ℝ) * sqrtKN0 (levelsOf c m) m) :=
        le_mul_of_one_le_left (by positivity) (Real.one_le_rpow (one_le_cast_D m) hγ0)
    _ ≤ N := h10 ⟨D₀, N, m⟩ hp

end ImprovedExponents
