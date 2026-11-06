module

public import AnalyticESC.Dimension.Defs

public section

set_option hygiene false
local notation "𝕼" => (hP t ht).add_const _
local notation "𝕻" => pow_pos hcmax n
local notation "𝕺" => sub_nonneg.2 hxy
local notation "𝖇" => Φ.pressureSum t n

local notation "𝖆" => Φ.supDeriv_pos hN _

local notation "𝔜" => List.ofFn v

local notation "𝔛" => t + h

/-!
# The pressure and the conformality dimension

The pressure `P(t) = lim_n (1/n) log ∑_{w ∈ Σ_n} ‖f_w'‖^t` of Section 1.2.1 exists for every `t`,
by sub-additivity, and vanishes at exactly one `t = s(Φ) ≥ 0`, the conformality dimension.
-/

namespace AnalyticESC

variable {t : ℝ}

open Set Filter Topology

namespace IFS

variable (Φ : IFS N ε)

/-- Sub-multiplicativity `‖f_{uv}'‖ ≤ ‖f_u'‖ ‖f_v'‖`, from the chain rule and `f_v(I) ⊆ I`. -/
theorem pr_supDeriv_append_le u v :
    Φ.supDeriv (u ++ v) ≤ Φ.supDeriv u * Φ.supDeriv v := by
  refine ciSup_le fun x => ?_
  have hu := Φ.norm_deriv_le_supDeriv u (Φ.re_comp_mem_I v x.2)
  rw [Φ.deriv_comp_append u v (Φ.ofReal_mem_cl x.2), norm_mul, Φ.comp_ofReal v x.2]
  exact mul_le_mul hu (Φ.norm_deriv_le_supDeriv v x.2) (norm_nonneg _)
    ((norm_nonneg _).trans hu)

variable (hN : 0 < N)
include hN

/-- Each term of the pressure sum is at most the sum. -/
theorem pr_term_le_pressureSum t (v : Fin n → Fin N) :
    Φ.supDeriv 𝔜 ^ t ≤ Φ.pressureSum t n :=
  Finset.single_le_sum
    (fun _ _ => (Real.rpow_pos_of_pos 𝖆 t).le) (Finset.mem_univ v)

/-- For `t ≥ 0`, the pressure sums are sub-multiplicative. -/
theorem pr_pressureSum_add_le (ht : 0 ≤ t) m n :
    Φ.pressureSum t (m + n) ≤ Φ.pressureSum t m * Φ.pressureSum t n := by
  rw [pressureSum, pressureSum, pressureSum, Finset.sum_mul_sum, ← Fintype.sum_prod_type',
    ← (Fin.appendEquiv m n).sum_comp]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [funext (Fin.appendEquiv_apply m n p), List.ofFn_fin_append, ← Real.mul_rpow (Φ.supDeriv_pos hN _).le
    (Φ.supDeriv_pos hN _).le]
  exact Real.rpow_le_rpow (Φ.supDeriv_pos hN _).le (Φ.pr_supDeriv_append_le _ _) ht

/-- Raising the exponent from `t` to `t + h` multiplies each term by a factor between
`c_min^{nh}` and `c_max^{nh}`. -/
theorem pr_log_pressureSum_add t (hh : 0 ≤ h) n :
    Real.log 𝖇 + n * (h * Real.log Φ.cmin) ≤
        Real.log (Φ.pressureSum 𝔛 n) ∧
      Real.log (Φ.pressureSum 𝔛 n) ≤
        Real.log 𝖇 + n * (h * Real.log Φ.cmax) := by
  have hcmin := Φ.cmin_pos hN
  have hcmax := Φ.cmax_pos hN
  have hlog : ∀ c, 0 < c → Real.log ((c ^ n) ^ h) = n * (h * Real.log c) := by
    intro c hc
    rw [Real.log_rpow (pow_pos hc n), Real.log_pow]
    ring
  have hterm : ∀ v : Fin n → Fin N, Φ.supDeriv 𝔜 ^ 𝔛 =
      Φ.supDeriv 𝔜 ^ t * Φ.supDeriv 𝔜 ^ h := fun v =>
    Real.rpow_add 𝖆 t h
  have hP := Φ.pressureSum_pos hN
  constructor
  · have hle : Φ.pressureSum t n * (Φ.cmin ^ n) ^ h ≤ Φ.pressureSum 𝔛 n := by
      rw [pressureSum, pressureSum, Finset.sum_mul]
      refine Finset.sum_le_sum fun v _ => ?_
      rw [hterm]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_pos_of_pos 𝖆 t).le
      have := Φ.cmin_pow_le_supDeriv 𝔜
      rw [List.length_ofFn] at this
      bound
    have := Real.log_le_log (mul_pos (hP t n) (Real.rpow_pos_of_pos (pow_pos hcmin n) h)) hle
    rwa [Real.log_mul (hP t n).ne' (Real.rpow_pos_of_pos (pow_pos hcmin n) h).ne',
      hlog _ hcmin] at this
  · have hle : Φ.pressureSum 𝔛 n ≤ Φ.pressureSum t n * (Φ.cmax ^ n) ^ h := by
      rw [pressureSum, pressureSum, Finset.sum_mul]
      refine Finset.sum_le_sum fun v _ => ?_
      rw [hterm]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_pos_of_pos 𝖆 t).le
      have := Φ.supDeriv_le 𝔜
      rw [List.length_ofFn] at this
      exact Real.rpow_le_rpow (Φ.supDeriv_pos hN _).le this hh
    have := Real.log_le_log (hP 𝔛 n) hle
    rwa [Real.log_mul (hP t n).ne' (Real.rpow_pos_of_pos 𝕻 h).ne',
      hlog _ hcmax] at this

/-- For `t ≥ 0`, `(1/n) log ∑_{w ∈ Σ_n} ‖f_w'‖^t` converges, by Fekete's lemma. -/
theorem pr_exists_tendsto (ht : 0 ≤ t) :
    ∃ p, Tendsto (fun n => Real.log 𝖇 / n) atTop (𝓝 p) := by
  have hsub : Subadditive fun n => Real.log 𝖇 := by
    intro m n
    have hP := Φ.pressureSum_pos hN t
    rw [← Real.log_mul (hP m).ne' (hP n).ne']
    exact Real.log_le_log (hP _) (Φ.pr_pressureSum_add_le hN ht m n)
  refine ⟨hsub.lim, hsub.tendsto_lim ⟨t * Real.log Φ.cmin, ?_⟩⟩
  rintro _ ⟨n, rfl⟩
  have hlmin : Real.log Φ.cmin < 0 :=
    Real.log_neg (Φ.cmin_pos hN) ((Φ.cmin_le_cmax hN).trans_lt Φ.cmax_lt_one)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
    nlinarith
  · have h := (Φ.pr_log_pressureSum_add hN 0 ht n).1
    have h0 : Real.log (Φ.pressureSum 0 n) ≥ 0 := by
      refine Real.log_nonneg ?_
      have := Φ.pr_term_le_pressureSum hN 0 (fun _ : Fin n => (⟨0, hN⟩ : Fin N))
      rwa [Real.rpow_zero] at this
    rw [zero_add] at h
    rw [le_div_iff₀ (by exact_mod_cast hn)]
    nlinarith

/-- The pressure has a unique zero `s(Φ) ≥ 0`: the limit `lim_n (1/n) log ∑_{w ∈ Σ_n} ‖f_w'‖^t`
exists and equals `0` exactly for `t = s(Φ)`. -/
theorem exists_pressure_zero :
    ∃ s, Φ.PressureZero s := by
  set a : ℝ → ℕ → ℝ := fun t n => Real.log 𝖇 / n with ha_def
  set P : ℝ → ℝ := fun t => limUnder atTop (a t)
  have hP : ∀ t, 0 ≤ t → Tendsto (a t) atTop (𝓝 (P t)) := fun t ht =>
    tendsto_nhds_limUnder (Φ.pr_exists_tendsto hN ht)
  have hcmin := Φ.cmin_pos hN
  have hcmax := Φ.cmax_pos hN
  set lmin := Real.log Φ.cmin
  set lmax := Real.log Φ.cmax
  have hlmax := Real.log_neg hcmax Φ.cmax_lt_one
  -- `P(t) + h log c_min ≤ P(t + h) ≤ P(t) + h log c_max`
  have hmono : ∀ t h, 0 ≤ t → 0 ≤ h → P t + h * lmin ≤ P 𝔛 ∧ P 𝔛 ≤ P t + h * lmax := by
    intro t h ht hh
    have hev : ∀ᶠ n : ℕ in atTop, a t n + h * lmin ≤ a 𝔛 n ∧
        a 𝔛 n ≤ a t n + h * lmax := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      obtain ⟨h1, h2⟩ := Φ.pr_log_pressureSum_add hN t hh n
      rw [div_add' _ _ _ hn'.ne', div_add' _ _ _ hn'.ne', div_le_div_iff_of_pos_right hn',
        div_le_div_iff_of_pos_right hn']
      constructor <;> linarith
    exact ⟨le_of_tendsto_of_tendsto 𝕼 (hP 𝔛 (by linarith))
        (hev.mono fun n hn => hn.1),
      le_of_tendsto_of_tendsto (hP 𝔛 (by linarith)) 𝕼
        (hev.mono fun n hn => hn.2)⟩
  -- `P(0) ≥ 0`
  have hP0 : 0 ≤ P 0 := by
    refine ge_of_tendsto' (hP 0 le_rfl) fun n => div_nonneg (Real.log_nonneg ?_) n.cast_nonneg
    have := Φ.pr_term_le_pressureSum hN 0 (fun _ : Fin n => (⟨0, hN⟩ : Fin N))
    rwa [Real.rpow_zero] at this
  -- `P` is continuous on `[0, ∞)`
  have hcont : ContinuousOn P (Ici 0) := by
    refine (LipschitzOnWith.of_dist_le' (K := -lmin) fun x hx y hy => ?_).continuousOn
    rw [Real.dist_eq, Real.dist_eq]
    rcases le_total x y with hxy | hxy
    · obtain ⟨h1, h2⟩ := hmono x (y - x) hx 𝕺
      rw [add_sub_cancel] at h1 h2
      rw [abs_sub_comm x y, abs_of_nonneg 𝕺, abs_le]
      constructor <;> nlinarith
    · obtain ⟨h1, h2⟩ := hmono y (x - y) hy 𝕺
      rw [add_sub_cancel] at h1 h2
      rw [abs_of_nonneg 𝕺, abs_le]
      constructor <;> nlinarith
  -- the intermediate value theorem on `[0, T]` with `P(T) ≤ 0`
  set T := P 0 / -lmax with hT_def
  have hT : 0 ≤ T := div_nonneg hP0 (by linarith)
  have hPT : P T ≤ 0 := by
    have h2 := (hmono 0 T le_rfl hT).2
    rw [zero_add] at h2
    have : T * lmax = -P 0 := by
      rw [hT_def, div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self hlmax.ne, mul_one]
    linarith
  obtain ⟨s, hs, hPs⟩ : 0 ∈ P '' Icc 0 T :=
    intermediate_value_Icc' hT (hcont.mono fun x hx => hx.1) ⟨hPT, hP0⟩
  refine ⟨s, fun t => ⟨fun h => ?_, ?_⟩⟩
  · rcases lt_or_ge t 0 with ht | ht
    · -- for `t < 0`, every term is at least `c_max^{nt} ≥ 1`
      exfalso
      have hpos := mul_pos_of_neg_of_neg ht hlmax
      have hev : ∀ᶠ n : ℕ in atTop, t * lmax ≤ a t n := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        have h2 := Φ.supDeriv_le (List.ofFn fun _ : Fin n => (⟨0, hN⟩ : Fin N))
        rw [List.length_ofFn] at h2
        have h4 := Real.log_le_log (Real.rpow_pos_of_pos 𝕻 t) ((Real.rpow_le_rpow_of_nonpos 𝖆 h2 ht.le).trans (Φ.pr_term_le_pressureSum hN t (fun _ : Fin n => (⟨0, hN⟩ : Fin N))))
        rw [Real.log_rpow 𝕻, Real.log_pow] at h4
        rw [le_div_iff₀ (by exact_mod_cast hn)]
        linarith
      have := ge_of_tendsto h hev
      linarith
    · have hPt := tendsto_nhds_unique (hP t ht) h
      by_contra hts
      rcases lt_or_gt_of_ne hts with hts | hts
      · have := (hmono t (s - t) ht (sub_nonneg.2 hts.le)).2
        rw [add_sub_cancel] at this
        nlinarith
      · have := (hmono s (t - s) hs.1 (sub_nonneg.2 hts.le)).2
        rw [add_sub_cancel] at this
        nlinarith
  · rintro rfl
    rw [← hPs]
    exact hP t hs.1

end IFS

end AnalyticESC
