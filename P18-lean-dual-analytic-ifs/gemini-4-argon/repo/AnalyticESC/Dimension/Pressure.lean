module

public import AnalyticESC.Dimension.Defs

@[expose] public section

/-!
# The pressure and the conformality dimension

The pressure `P(t) = lim_n (1/n) log ∑_{w ∈ Σ_n} ‖f_w'‖^t` of Section 1.2.1 exists for every `t`,
by sub-additivity, and vanishes at exactly one `t = s(Φ) ≥ 0`, the conformality dimension.
-/

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- `‖f_w'‖ > 0` for a nonempty alphabet. -/
theorem supDeriv_pos (hN : 0 < N) (w : List (Fin N)) : 0 < Φ.supDeriv w :=
  (pow_pos (Φ.cmin_pos hN) _).trans_le (Φ.cmin_pow_le_supDeriv w)

/-- Sub-multiplicativity `‖f_{uv}'‖ ≤ ‖f_u'‖ ‖f_v'‖`, from the chain rule and `f_v(I) ⊆ I`. -/
private theorem pr_supDeriv_append_le (u v : List (Fin N)) :
    Φ.supDeriv (u ++ v) ≤ Φ.supDeriv u * Φ.supDeriv v := by
  have : Nonempty I := ⟨⟨0, le_rfl, zero_le_one⟩⟩
  refine ciSup_le fun x => ?_
  have hx := x.2
  have hz : ((x : ℝ) : ℂ) ∈ closure (nbhd ε) := subset_closure (ofReal_mem_nbhd Φ.ε_pos hx)
  have hu := Φ.norm_deriv_le_supDeriv u (Φ.re_comp_mem_I v hx)
  rw [Φ.deriv_comp_append u v hz, norm_mul, Φ.comp_ofReal v hx]
  exact mul_le_mul hu (Φ.norm_deriv_le_supDeriv v hx) (norm_nonneg _)
    ((norm_nonneg _).trans hu)

theorem pressureSum_pos (hN : 0 < N) (t : ℝ) (n : ℕ) : 0 < Φ.pressureSum t n :=
  Finset.sum_pos (fun _ _ => Real.rpow_pos_of_pos (Φ.supDeriv_pos hN _) t)
    ⟨fun _ => ⟨0, hN⟩, Finset.mem_univ _⟩

/-- For `t ≥ 0`, the pressure sums are sub-multiplicative. -/
private theorem pr_pressureSum_add_le (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) (m n : ℕ) :
    Φ.pressureSum t (m + n) ≤ Φ.pressureSum t m * Φ.pressureSum t n := by
  rw [pressureSum, pressureSum, pressureSum, Finset.sum_mul_sum, ← Fintype.sum_prod_type',
    ← (Fin.appendEquiv m n).sum_comp]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [show Fin.appendEquiv m n p = Fin.append p.1 p.2 from funext (Fin.appendEquiv_apply m n p),
    List.ofFn_fin_append, ← Real.mul_rpow (Φ.supDeriv_pos hN _).le (Φ.supDeriv_pos hN _).le]
  exact Real.rpow_le_rpow (Φ.supDeriv_pos hN _).le (Φ.pr_supDeriv_append_le _ _) ht

/-- Raising the exponent from `t` to `t + h` multiplies each term by a factor between
`c_min^{nh}` and `c_max^{nh}`. -/
private theorem pr_log_pressureSum_add (hN : 0 < N) (t : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    Real.log (Φ.pressureSum t n) + n * (h * Real.log Φ.cmin) ≤
        Real.log (Φ.pressureSum (t + h) n) ∧
      Real.log (Φ.pressureSum (t + h) n) ≤
        Real.log (Φ.pressureSum t n) + n * (h * Real.log Φ.cmax) := by
  have hcmin := Φ.cmin_pos hN
  have hcmax := Φ.cmax_pos hN
  have hlog (c : ℝ) (hc : 0 < c) : Real.log ((c ^ n) ^ h) = n * (h * Real.log c) := by
    rw [Real.log_rpow (pow_pos hc n), Real.log_pow]; ring
  have hP := Φ.pressureSum_pos hN
  constructor
  · have hle : Φ.pressureSum t n * (Φ.cmin ^ n) ^ h ≤ Φ.pressureSum (t + h) n := by
      rw [pressureSum, pressureSum, Finset.sum_mul]
      refine Finset.sum_le_sum fun v _ => ?_
      rw [Real.rpow_add (Φ.supDeriv_pos hN _) t h]
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (pow_pos hcmin n).le ?_ hh)
        (Real.rpow_pos_of_pos (Φ.supDeriv_pos hN _) t).le
      simpa using Φ.cmin_pow_le_supDeriv (List.ofFn v)
    have := Real.log_le_log (mul_pos (hP t n) (Real.rpow_pos_of_pos (pow_pos hcmin n) h)) hle
    rwa [Real.log_mul (hP t n).ne' (Real.rpow_pos_of_pos (pow_pos hcmin n) h).ne',
      hlog _ hcmin] at this
  · have hle : Φ.pressureSum (t + h) n ≤ Φ.pressureSum t n * (Φ.cmax ^ n) ^ h := by
      rw [pressureSum, pressureSum, Finset.sum_mul]
      refine Finset.sum_le_sum fun v _ => ?_
      rw [Real.rpow_add (Φ.supDeriv_pos hN _) t h]
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Φ.supDeriv_pos hN _).le ?_ hh)
        (Real.rpow_pos_of_pos (Φ.supDeriv_pos hN _) t).le
      simpa using Φ.supDeriv_le (List.ofFn v)
    have := Real.log_le_log (hP (t + h) n) hle
    rwa [Real.log_mul (hP t n).ne' (Real.rpow_pos_of_pos (pow_pos hcmax n) h).ne',
      hlog _ hcmax] at this

private theorem pr_log_pressureSum_zero_nonneg (hN : 0 < N) (n : ℕ) :
    0 ≤ Real.log (Φ.pressureSum 0 n) := by
  have h := Finset.single_le_sum (f := fun v : Fin n → Fin N => Φ.supDeriv (List.ofFn v) ^ (0 : ℝ))
    (fun _ _ => by positivity) (Finset.mem_univ fun _ => ⟨0, hN⟩)
  exact Real.log_nonneg (by simpa [pressureSum] using h)

/-- For `t ≥ 0`, `(1/n) log ∑_{w ∈ Σ_n} ‖f_w'‖^t` converges, by Fekete's lemma. -/
private theorem pr_exists_tendsto (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) :
    ∃ p, Tendsto (fun n : ℕ => Real.log (Φ.pressureSum t n) / n) atTop (𝓝 p) := by
  have hsub : Subadditive fun n => Real.log (Φ.pressureSum t n) := fun m n => by
    have hP := Φ.pressureSum_pos hN t
    rw [← Real.log_mul (hP m).ne' (hP n).ne']
    exact Real.log_le_log (hP _) (Φ.pr_pressureSum_add_le hN ht m n)
  refine ⟨hsub.lim, hsub.tendsto_lim ⟨t * Real.log Φ.cmin, ?_⟩⟩
  rintro _ ⟨n, rfl⟩
  have hlmin : Real.log Φ.cmin < 0 :=
    Real.log_neg (Φ.cmin_pos hN) ((Φ.cmin_le_cmax hN).trans_lt Φ.cmax_lt_one)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, div_zero]
    exact mul_nonpos_of_nonneg_of_nonpos ht hlmin.le
  · have h := (Φ.pr_log_pressureSum_add hN 0 ht n).1
    rw [zero_add] at h
    have h0 := Φ.pr_log_pressureSum_zero_nonneg hN n
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hn']
    nlinarith

/-- The pressure has a unique zero `s(Φ) ≥ 0`: the limit `lim_n (1/n) log ∑_{w ∈ Σ_n} ‖f_w'‖^t`
exists and equals `0` exactly for `t = s(Φ)`. -/
theorem exists_pressure_zero (hN : 0 < N) :
    ∃ s : ℝ, 0 ≤ s ∧
      ∀ t, Tendsto (fun n : ℕ => Real.log (Φ.pressureSum t n) / n) atTop (𝓝 0) ↔ t = s := by
  set a : ℝ → ℕ → ℝ := fun t n => Real.log (Φ.pressureSum t n) / n with ha_def
  set P : ℝ → ℝ := fun t => limUnder atTop (a t)
  have hP (t : ℝ) (ht : 0 ≤ t) : Tendsto (a t) atTop (𝓝 (P t)) :=
    tendsto_nhds_limUnder (Φ.pr_exists_tendsto hN ht)
  have hcmin := Φ.cmin_pos hN
  have hcmax := Φ.cmax_pos hN
  set lmin := Real.log Φ.cmin
  set lmax := Real.log Φ.cmax
  have hlmax : lmax < 0 := Real.log_neg hcmax Φ.cmax_lt_one
  have hlmin : lmin ≤ lmax := Real.log_le_log hcmin (Φ.cmin_le_cmax hN)
  have hbound {t₁ t₂ p₁ p₂ : ℝ} (ht : t₁ ≤ t₂)
      (h₁ : Tendsto (a t₁) atTop (𝓝 p₁)) (h₂ : Tendsto (a t₂) atTop (𝓝 p₂)) :
      p₁ + (t₂ - t₁) * lmin ≤ p₂ ∧ p₂ ≤ p₁ + (t₂ - t₁) * lmax := by
    have hev : ∀ᶠ n : ℕ in atTop, a t₁ n + (t₂ - t₁) * lmin ≤ a t₂ n ∧
        a t₂ n ≤ a t₁ n + (t₂ - t₁) * lmax := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      obtain ⟨h1, h2⟩ := Φ.pr_log_pressureSum_add hN t₁ (sub_nonneg.2 ht) n
      simp only [ha_def, add_sub_cancel] at h1 h2 ⊢
      rw [div_add' _ _ _ hn'.ne', div_add' _ _ _ hn'.ne', div_le_div_iff_of_pos_right hn',
        div_le_div_iff_of_pos_right hn']
      exact ⟨by linarith, by linarith⟩
    exact ⟨le_of_tendsto_of_tendsto (h₁.add_const _) h₂ (hev.mono fun _ h => h.1),
      le_of_tendsto_of_tendsto h₂ (h₁.add_const _) (hev.mono fun _ h => h.2)⟩
  have hP0 : 0 ≤ P 0 :=
    ge_of_tendsto' (hP 0 le_rfl) fun n =>
      div_nonneg (Φ.pr_log_pressureSum_zero_nonneg hN n) n.cast_nonneg
  have hdist {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : |P x - P y| ≤ -lmin * (y - x) := by
    obtain ⟨h1, h2⟩ := hbound hxy (hP x hx) (hP y (hx.trans hxy))
    rw [abs_le]; constructor <;> nlinarith
  have hcont : ContinuousOn P (Ici 0) :=
    (LipschitzOnWith.of_dist_le' (K := -lmin) fun x hx y hy => by
      rw [Real.dist_eq, Real.dist_eq]
      rcases le_total x y with hxy | hxy
      · exact (hdist hx hxy).trans_eq (by rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hxy)])
      · rw [abs_sub_comm]
        exact (hdist hy hxy).trans_eq (by rw [abs_of_nonneg (sub_nonneg.2 hxy)])).continuousOn
  set T := P 0 / -lmax with hT_def
  have hT : 0 ≤ T := div_nonneg hP0 (by linarith)
  have hPT : P T ≤ 0 := by
    have h2 := (hbound hT (hP 0 le_rfl) (hP T hT)).2
    have : (T - 0) * lmax = -P 0 := by
      rw [sub_zero, hT_def, div_neg, neg_mul, div_mul_cancel₀ _ hlmax.ne]
    linarith
  obtain ⟨s, hs, hPs⟩ : (0 : ℝ) ∈ P '' Icc 0 T :=
    intermediate_value_Icc' hT (hcont.mono fun x hx => hx.1) ⟨hPT, hP0⟩
  have hs0 : Tendsto (a s) atTop (𝓝 0) := hPs ▸ hP s hs.1
  refine ⟨s, hs.1, fun t => ⟨fun h => ?_, fun h => h ▸ hs0⟩⟩
  by_contra hts
  rcases lt_or_gt_of_ne hts with hts | hts
  · nlinarith [(hbound hts.le h hs0).2]
  · nlinarith [(hbound hts.le hs0 h).2]

end IFS

end AnalyticESC
