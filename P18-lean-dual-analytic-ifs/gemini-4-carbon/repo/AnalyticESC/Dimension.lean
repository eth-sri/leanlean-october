module

public import AnalyticESC.Generic

@[expose] public section

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory
open scoped Interval

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

noncomputable def supDeriv (w : List (Fin N)) : ℝ := ⨆ x : I, ‖deriv (Φ.comp w) x‖

noncomputable def pressureSum (t : ℝ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → Fin N, Φ.supDeriv (List.ofFn w) ^ t

theorem measurable_natProj : Measurable Φ.natProj := Φ.continuous_natProj.measurable

theorem norm_deriv_le_supDeriv (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    ‖deriv (Φ.comp w) x‖ ≤ Φ.supDeriv w :=
  le_ciSup (f := fun x : I => ‖deriv (Φ.comp w) ((x : ℝ) : ℂ)‖) ⟨Φ.cmax ^ w.length, by
    rintro _ ⟨y, rfl⟩; exact Φ.norm_deriv_comp_le w (subset_closure (ofReal_mem_nbhd Φ.ε_pos y.2))⟩
    ⟨x, hx⟩

theorem supDeriv_le (w : List (Fin N)) : Φ.supDeriv w ≤ Φ.cmax ^ w.length := by
  have : Nonempty I := ⟨⟨0, le_rfl, zero_le_one⟩⟩
  exact ciSup_le fun x => Φ.norm_deriv_comp_le w (subset_closure (ofReal_mem_nbhd Φ.ε_pos x.2))

theorem cmin_pow_le_supDeriv (w : List (Fin N)) : Φ.cmin ^ w.length ≤ Φ.supDeriv w :=
  (Φ.cmin_pow_le_norm_deriv_comp w
    (subset_closure (ofReal_mem_nbhd Φ.ε_pos ⟨le_rfl, zero_le_one⟩))).trans
    (Φ.norm_deriv_le_supDeriv w ⟨le_rfl, zero_le_one⟩)

theorem supDeriv_pos (hN : 0 < N) (w : List (Fin N)) : 0 < Φ.supDeriv w :=
  (pow_pos (Φ.cmin_pos hN) _).trans_le (Φ.cmin_pow_le_supDeriv w)

end IFS

theorem scaleZero_map : map (fun r : Scale => (r : ℝ)) scaleZero = 𝓝[>] (0 : ℝ) := by
  apply map_comap_of_mem
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from zero_lt_one)] with r hr
  exact ⟨⟨r, hr⟩, rfl⟩

theorem positive_length_tendsto_iff (g : ℕ → ℝ) :
    Tendsto (fun n : ℕ => divide (g (n + 1)) ((n + 1 : ℕ) : ℝ)
      (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))) atTop (𝓝 0) ↔
    Tendsto (fun n : ℕ => g n / n) atTop (𝓝 0) := by
  simpa only [divide] using (tendsto_add_atTop_iff_nat (f := fun n : ℕ => g n / (n : ℝ)) (l := 𝓝 0) 1)

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

private theorem pr_supDeriv_append_le (u v : List (Fin N)) :
    Φ.supDeriv (u ++ v) ≤ Φ.supDeriv u * Φ.supDeriv v := by
  have : Nonempty I := ⟨⟨0, le_rfl, zero_le_one⟩⟩
  refine ciSup_le fun x => ?_
  have hx := x.2
  have hu := Φ.norm_deriv_le_supDeriv u (Φ.re_comp_mem_I v hx)
  rw [Φ.deriv_comp_append u v (subset_closure (ofReal_mem_nbhd Φ.ε_pos hx)), norm_mul,
    Φ.comp_ofReal v hx]
  exact mul_le_mul hu (Φ.norm_deriv_le_supDeriv v hx) (norm_nonneg _) ((norm_nonneg _).trans hu)

private theorem pr_pressureSum_pos (hN : 0 < N) (t : ℝ) (n : ℕ) : 0 < Φ.pressureSum t n :=
  Finset.sum_pos (fun _ _ => Real.rpow_pos_of_pos (Φ.supDeriv_pos hN _) t)
    ⟨fun _ => ⟨0, hN⟩, Finset.mem_univ _⟩

private theorem pr_term_le_pressureSum (hN : 0 < N) (t : ℝ) {n : ℕ} (v : Fin n → Fin N) :
    Φ.supDeriv (List.ofFn v) ^ t ≤ Φ.pressureSum t n :=
  Finset.single_le_sum (f := fun v : Fin n → Fin N => Φ.supDeriv (List.ofFn v) ^ t)
    (fun _ _ => (Real.rpow_pos_of_pos (Φ.supDeriv_pos hN _) t).le) (Finset.mem_univ v)

private theorem pr_log_pressureSum_add (hN : 0 < N) (t : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    Real.log (Φ.pressureSum t n) + n * (h * Real.log Φ.cmin) ≤
        Real.log (Φ.pressureSum (t + h) n) ∧
      Real.log (Φ.pressureSum (t + h) n) ≤
        Real.log (Φ.pressureSum t n) + n * (h * Real.log Φ.cmax) := by
  have hcmin := Φ.cmin_pos hN
  have hcmax : 0 < Φ.cmax := hcmin.trans_le (Φ.cmin_le_cmax hN)
  have hlog : ∀ c : ℝ, 0 < c → Real.log ((c ^ n) ^ h) = n * (h * Real.log c) := fun c hc => by
    rw [Real.log_rpow (pow_pos hc n), Real.log_pow]; ring
  have hP := Φ.pr_pressureSum_pos hN
  constructor
  · have hle : Φ.pressureSum t n * (Φ.cmin ^ n) ^ h ≤ Φ.pressureSum (t + h) n := by
      rw [pressureSum, pressureSum, Finset.sum_mul]
      refine Finset.sum_le_sum fun v _ => ?_
      rw [Real.rpow_add (Φ.supDeriv_pos hN _) t h]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (pow_pos hcmin n).le (by simpa using Φ.cmin_pow_le_supDeriv (List.ofFn v)) hh)
        (Real.rpow_pos_of_pos (Φ.supDeriv_pos hN _) t).le
    simpa [Real.log_mul (hP t n).ne' (Real.rpow_pos_of_pos (pow_pos hcmin n) h).ne', hlog _ hcmin]
      using Real.log_le_log (mul_pos (hP t n) (Real.rpow_pos_of_pos (pow_pos hcmin n) h)) hle
  · have hle : Φ.pressureSum (t + h) n ≤ Φ.pressureSum t n * (Φ.cmax ^ n) ^ h := by
      rw [pressureSum, pressureSum, Finset.sum_mul]
      refine Finset.sum_le_sum fun v _ => ?_
      rw [Real.rpow_add (Φ.supDeriv_pos hN _) t h]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Φ.supDeriv_pos hN _).le (by simpa using Φ.supDeriv_le (List.ofFn v)) hh)
        (Real.rpow_pos_of_pos (Φ.supDeriv_pos hN _) t).le
    simpa [Real.log_mul (hP t n).ne' (Real.rpow_pos_of_pos (pow_pos hcmax n) h).ne', hlog _ hcmax]
      using Real.log_le_log (hP (t + h) n) hle

private theorem pr_exists_tendsto (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) :
    ∃ p, Tendsto (fun n : ℕ => Real.log (Φ.pressureSum t n) / n) atTop (𝓝 p) := by
  have hP := Φ.pr_pressureSum_pos hN t
  have hsub : Subadditive fun n => Real.log (Φ.pressureSum t n) := fun m n => by
    rw [← Real.log_mul (hP m).ne' (hP n).ne']
    refine Real.log_le_log (hP _) ?_
    rw [pressureSum, pressureSum, pressureSum, Finset.sum_mul_sum, ← Fintype.sum_prod_type',
      ← (Fin.appendEquiv m n).sum_comp]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [show Fin.appendEquiv m n p = Fin.append p.1 p.2 from funext (Fin.appendEquiv_apply m n p),
      List.ofFn_fin_append, ← Real.mul_rpow (Φ.supDeriv_pos hN _).le (Φ.supDeriv_pos hN _).le]
    exact Real.rpow_le_rpow (Φ.supDeriv_pos hN _).le (Φ.pr_supDeriv_append_le _ _) ht
  refine ⟨hsub.lim, hsub.tendsto_lim ⟨t * Real.log Φ.cmin, ?_⟩⟩
  rintro _ ⟨n, rfl⟩
  have hlmin : Real.log Φ.cmin < 0 :=
    Real.log_neg (Φ.cmin_pos hN) ((Φ.cmin_le_cmax hN).trans_lt Φ.cmax_lt_one)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, div_zero]; exact mul_nonpos_of_nonneg_of_nonpos ht hlmin.le
  · have h := (Φ.pr_log_pressureSum_add hN 0 ht n).1
    have h0 : 0 ≤ Real.log (Φ.pressureSum 0 n) :=
      Real.log_nonneg (by simpa using Φ.pr_term_le_pressureSum hN 0 (fun _ : Fin n => ⟨0, hN⟩))
    rw [zero_add] at h
    rw [le_div_iff₀ (by exact_mod_cast hn)]
    nlinarith

theorem exists_pressure_zero (hN : 0 < N) :
    ∃ s : ℝ, 0 ≤ s ∧
      ∀ t, Tendsto (fun n : ℕ => Real.log (Φ.pressureSum t n) / n) atTop (𝓝 0) ↔ t = s := by
  set a : ℝ → ℕ → ℝ := fun t n => Real.log (Φ.pressureSum t n) / n with ha_def
  set P : ℝ → ℝ := fun t => limUnder atTop (a t)
  have hP : ∀ t, 0 ≤ t → Tendsto (a t) atTop (𝓝 (P t)) := fun t ht =>
    tendsto_nhds_limUnder (Φ.pr_exists_tendsto hN ht)
  have hcmin := Φ.cmin_pos hN
  have hcmax : 0 < Φ.cmax := hcmin.trans_le (Φ.cmin_le_cmax hN)
  set lmin := Real.log Φ.cmin
  set lmax := Real.log Φ.cmax
  have hlmax : lmax < 0 := Real.log_neg hcmax Φ.cmax_lt_one
  have hlmin : lmin ≤ lmax := Real.log_le_log hcmin (Φ.cmin_le_cmax hN)
  have hmono : ∀ t h, 0 ≤ t → 0 ≤ h → P t + h * lmin ≤ P (t + h) ∧ P (t + h) ≤ P t + h * lmax := by
    intro t h ht hh
    have hev : ∀ᶠ n : ℕ in atTop, a t n + h * lmin ≤ a (t + h) n ∧
        a (t + h) n ≤ a t n + h * lmax := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      obtain ⟨h1, h2⟩ := Φ.pr_log_pressureSum_add hN t hh n
      simp only [ha_def]
      rw [div_add' _ _ _ hn'.ne', div_add' _ _ _ hn'.ne', div_le_div_iff_of_pos_right hn',
        div_le_div_iff_of_pos_right hn']
      exact ⟨by linarith, by linarith⟩
    exact ⟨le_of_tendsto_of_tendsto ((hP t ht).add_const _) (hP (t + h) (by linarith)) (hev.mono fun _ hn => hn.1),
      le_of_tendsto_of_tendsto (hP (t + h) (by linarith)) ((hP t ht).add_const _) (hev.mono fun _ hn => hn.2)⟩
  have hP0 : 0 ≤ P 0 := ge_of_tendsto' (hP 0 le_rfl) fun n =>
    div_nonneg (Real.log_nonneg (by simpa using Φ.pr_term_le_pressureSum hN 0 (fun _ : Fin n => ⟨0, hN⟩)))
      n.cast_nonneg
  have hcont : ContinuousOn P (Ici 0) := by
    refine (LipschitzOnWith.of_dist_le' (K := -lmin) fun x hx y hy => ?_).continuousOn
    wlog hxy : x ≤ y generalizing x y
    · rw [dist_comm, dist_comm x y]; exact this y hy x hx (le_of_not_ge hxy)
    obtain ⟨h1, h2⟩ := hmono x (y - x) hx (sub_nonneg.2 hxy)
    rw [add_sub_cancel] at h1 h2
    rw [Real.dist_eq, Real.dist_eq, abs_sub_comm x y, abs_of_nonneg (sub_nonneg.2 hxy), abs_le]
    exact ⟨by nlinarith, by nlinarith⟩
  set T := P 0 / -lmax with hT_def
  have hT : 0 ≤ T := div_nonneg hP0 (by linarith)
  have hPT : P T ≤ 0 := by
    have h2 := (hmono 0 T le_rfl hT).2
    rw [zero_add] at h2
    have hlne := hlmax.ne
    have : T * lmax = -P 0 := by rw [hT_def]; field_simp
    linarith
  obtain ⟨s, hs, hPs⟩ : (0 : ℝ) ∈ P '' Icc 0 T :=
    intermediate_value_Icc' hT (hcont.mono fun _ hx => hx.1) ⟨hPT, hP0⟩
  refine ⟨s, hs.1, fun t => ⟨fun h => ?_, fun h => h ▸ hPs ▸ hP s hs.1⟩⟩
  rcases lt_or_ge t 0 with ht | ht
  · exfalso
    have hpos : 0 < t * lmax := mul_pos_of_neg_of_neg ht hlmax
    have hev : ∀ᶠ n : ℕ in atTop, t * lmax ≤ a t n := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have h1 := Φ.pr_term_le_pressureSum hN t (fun _ : Fin n => ⟨0, hN⟩)
      have h2 := Φ.supDeriv_le (List.ofFn fun _ : Fin n => (⟨0, hN⟩ : Fin N))
      rw [List.length_ofFn] at h2
      have h4 := Real.log_le_log (Real.rpow_pos_of_pos (pow_pos hcmax n) t)
        ((Real.rpow_le_rpow_of_nonpos (Φ.supDeriv_pos hN _) h2 ht.le).trans h1)
      rw [Real.log_rpow (pow_pos hcmax n), Real.log_pow] at h4
      simp only [ha_def]; rw [le_div_iff₀ hn']; linarith
    linarith [ge_of_tendsto h hev]
  · have hPt : P t = 0 := tendsto_nhds_unique (hP t ht) h
    by_contra hts
    rcases lt_or_gt_of_ne hts with hts | hts
    · have := (hmono t (s - t) ht (sub_nonneg.2 hts.le)).2; rw [add_sub_cancel] at this; nlinarith
    · have := (hmono s (t - s) hs.1 (sub_nonneg.2 hts.le)).2; rw [add_sub_cancel] at this; nlinarith

end IFS

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

theorem natProj_eq_realMaps (ω : ℕ → Fin N) :
    Φ.natProj ω = Φ.realMaps (ω 0) (Φ.natProj fun j => ω (j + 1)) := by
  rw [Φ.natProj_eq_comp_prefix ω 1]; simp [realMaps]

theorem exists_attractor_eq_singleton_iff (hN : 0 < N) :
    (∃ x, Φ.attractor = {x}) ↔ ∃ x ∈ I, ∀ i, Φ.realMaps i x = x := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, Φ.attractor_subset_I (hx ▸ mem_singleton x), fun i => ?_⟩
    have h1 : Φ.natProj (fun _ => i) = x := by
      have h : Φ.natProj (fun _ => i) ∈ Φ.attractor := ⟨_, rfl⟩
      rwa [hx] at h
    have h2 := Φ.natProj_eq_realMaps (fun _ => i)
    rwa [h1, eq_comm] at h2
  · rintro ⟨p, hp, hfix⟩
    have hp' : (p : ℂ) ∈ nbhd ε := ofReal_mem_nbhd Φ.ε_pos hp
    have hf : ∀ i, Φ.f i p = p := fun i =>
      Complex.ext (hfix i) (by simpa using Φ.im_f_ofReal i (nbhd_subset_two hp'))
    have hc : ∀ w, Φ.comp w p = p := by
      intro w; induction w with
      | nil => rfl
      | cons i w ih => rw [comp_cons, Function.comp_apply, ih, hf]
    have hπ : ∀ ω, Φ.natProj ω = p := fun ω => sub_eq_zero.1 <| abs_nonpos_iff.1 <|
      ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one) fun n => by
        have h := Φ.abs_re_comp_sub_le (List.ofFn fun k : Fin n => ω k)
          (Φ.attractor_subset_I ⟨fun j => ω (j + n), rfl⟩) hp
        rwa [List.length_ofFn, hc, Complex.ofReal_re, ← Φ.natProj_eq_comp_prefix] at h
    exact ⟨p, Set.ext fun x => ⟨by rintro ⟨ω, rfl⟩; exact hπ ω, by rintro rfl; exact ⟨fun _ => ⟨0, hN⟩, hπ _⟩⟩⟩

theorem realComp_realMaps (w : List (Fin N)) {x : ℝ} (hx : (x : ℂ) ∈ nbhd ε) :
    realComp Φ.realMaps w x = (Φ.comp w x).re := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have h : ((Φ.comp w x).re : ℂ) = Φ.comp w x := Complex.ext rfl (by simp [Φ.im_comp_ofReal w hx])
    show Φ.realMaps i (realComp Φ.realMaps w x) = (Φ.f i (Φ.comp w x)).re
    rw [ih, realMaps, h]

theorem abs_deriv_realComp_realMaps (w : List (Fin N)) {x : ℝ} (hx : (x : ℂ) ∈ nbhd ε) :
    |deriv (realComp Φ.realMaps w) x| = ‖deriv (Φ.comp w) x‖ := by
  have heq : realComp Φ.realMaps w =ᶠ[𝓝 x] fun t : ℝ => (Φ.comp w t).re :=
    Filter.eventuallyEq_of_mem ((isOpen_setOf_ofReal_mem (isOpen_nbhd ε)).mem_nhds hx)
      fun _ ht => Φ.realComp_realMaps w ht
  rw [heq.deriv_eq, (hasDerivAt_re_ofReal (Φ.differentiableAt_comp w (subset_closure hx))).deriv]
  exact Complex.abs_re_eq_norm.2 (Φ.im_deriv_comp_ofReal w hx)

theorem abs_deriv_realMaps (i : Fin N) {x : ℝ} (hx : (x : ℂ) ∈ nbhd ε) :
    |deriv (Φ.realMaps i) x| = ‖deriv (Φ.f i) x‖ :=
  Φ.abs_deriv_realComp_realMaps [i] hx

theorem rapaportHyp (hN : 0 < N) (hnd : ¬ ∃ x, Φ.attractor = {x}) (hesc : Φ.ESC) :
    RapaportHyp Φ.realMaps where
  mapsTo i := (Φ.inClass i).re_mem_I
  analytic i x hx := (Complex.reCLM.analyticAt _).comp
    ((((Φ.differentiableOn_f i).analyticOnNhd (isOpen_nbhd _) _
      (nbhd_subset_two (ofReal_mem_nbhd Φ.ε_pos hx))).restrictScalars).comp
      (Complex.ofRealCLM.analyticAt x))
  deriv_pos i x hx := by
    have hx' := ofReal_mem_nbhd Φ.ε_pos hx
    rw [Φ.abs_deriv_realMaps i hx']
    exact norm_pos_iff.2 ((Φ.inClass i).deriv_ne_zero _ (subset_closure hx'))
  deriv_lt_one i x hx := by
    have hx' := ofReal_mem_nbhd Φ.ε_pos hx
    rw [Φ.abs_deriv_realMaps i hx']
    exact (Φ.inClass i).norm_deriv_lt_one _ (subset_closure hx')
  no_common_fixed_point h := hnd ((Φ.exists_attractor_eq_singleton_iff hN).2 h)
  exp_separated := by
    obtain ⟨c, hc, hfreq⟩ := hesc
    refine ⟨c, hc, hfreq.mono fun n hn u v huv => (hn u v huv).trans_eq ?_⟩
    refine iSup_congr fun x => ?_
    have hx := ofReal_mem_nbhd Φ.ε_pos x.2
    rw [Φ.realComp_realMaps _ hx, Φ.realComp_realMaps _ hx]
    change ‖Φ.comp (List.ofFn u) x - Φ.comp (List.ofFn v) x‖ = _
    conv_lhs => rw [Φ.comp_ofReal (List.ofFn u) x.2, Φ.comp_ofReal (List.ofFn v) x.2]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

private theorem dim_integral_le (hN : 0 < N) (i : Fin N) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμ : μ Iᶜ = 0) :
    ∫ x, Real.log |deriv (Φ.realMaps i) x| ∂μ ≤ Real.log Φ.cmax := by
  have hb : ∀ᵐ x ∂μ, Real.log Φ.cmin ≤ Real.log |deriv (Φ.realMaps i) x| ∧
      Real.log |deriv (Φ.realMaps i) x| ≤ Real.log Φ.cmax :=
    (ae_iff.2 hμ).mono fun x hx => by
      have hx' := ofReal_mem_nbhd Φ.ε_pos hx
      have hcl := subset_closure hx'
      have h1 := Φ.cmin_le_norm_deriv i hcl
      have h0 := Φ.cmin_pos hN
      rw [Φ.abs_deriv_realMaps i hx']
      exact ⟨Real.log_le_log h0 h1, Real.log_le_log (h0.trans_le h1) (Φ.norm_deriv_le_cmax i hcl)⟩
  have hint : Integrable (fun x => Real.log |deriv (Φ.realMaps i) x|) μ :=
    Integrable.of_bound
      ((continuous_abs.measurable.comp (measurable_deriv (Φ.realMaps i))).log.aestronglyMeasurable)
      (|Real.log Φ.cmin| + |Real.log Φ.cmax|) (hb.mono fun x hx => by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [neg_abs_le (Real.log Φ.cmin), abs_nonneg (Real.log Φ.cmax)],
          by linarith [le_abs_self (Real.log Φ.cmax), abs_nonneg (Real.log Φ.cmin)]⟩)
  exact (integral_mono_ae hint (integrable_const _) (hb.mono fun _ hx => hx.2)).trans_eq (by simp)

theorem neg_log_cmax_le_lyapunov (hN : 0 < N) {p : Fin N → ℝ} (hp : IsProbVec p)
    {μ : Measure ℝ} (hμ : Φ.IsSelfConformal p μ) : -Real.log Φ.cmax ≤ Φ.lyapunov p μ := by
  obtain ⟨_, hμ2, -⟩ := hμ
  rw [lyapunov, Challenge.lyapunov, neg_le_neg_iff, ← mul_one (Real.log Φ.cmax), ← hp.2, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    (mul_le_mul_of_nonneg_left (Φ.dim_integral_le hN i hμ2) (hp.1 i).le).trans_eq (mul_comm _ _)

theorem theorem_1_6 (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) (hN : 0 < N)
    (hnd : ¬ ∃ x, Φ.attractor = {x}) (hesc : Φ.ESC) : Challenge.DimEquality Φ.f := by
  have hφ := Φ.rapaportHyp hN hnd hesc
  obtain ⟨s, -, hs⟩ := Φ.exists_pressure_zero hN
  have hinv : Φ.attractor = ⋃ i, Φ.realMaps i '' Φ.attractor := Set.ext fun x => by
    simp only [mem_iUnion, mem_image]
    refine ⟨by rintro ⟨ω, rfl⟩; exact ⟨ω 0, _, ⟨_, rfl⟩, (Φ.natProj_eq_realMaps ω).symm⟩, ?_⟩
    rintro ⟨i, _, ⟨ω, rfl⟩, rfl⟩
    exact ⟨fun | 0 => i | j + 1 => ω j, Φ.natProj_eq_realMaps _⟩
  refine ⟨⟨s, fun t => (positive_length_tendsto_iff _).trans (hs t),
      hS Φ.realMaps hφ Φ.attractor ⟨_, mem_range_self (fun _ => ⟨0, hN⟩)⟩
        (isCompact_range Φ.continuous_natProj) Φ.attractor_subset_I hinv s ?_⟩,
    fun p hp μ hμ hχ => hM Φ.realMaps hφ p hp.1 hp.2 μ hμ.1 hμ.2.1 hμ.2.2 hχ⟩
  refine (positive_length_tendsto_iff (fun n : ℕ => Real.log (∑ u : Fin n → Fin N,
    (⨆ x : I, |deriv (realComp Φ.realMaps (List.ofFn u)) x|) ^ s))).mpr
    (((hs s).2 rfl).congr fun n => ?_)
  simp only [pressureSum, supDeriv]
  congr 3; ext u; congr 1
  exact iSup_congr fun x => (Φ.abs_deriv_realComp_realMaps _ (ofReal_mem_nbhd Φ.ε_pos x.2)).symm

end IFS

namespace OpenDense

theorem d2Sys_self {N : ℕ} (f : Fin N → ℂ → ℂ) : d2Sys f f = 0 := by
  simp [d2Sys, Challenge.d2]

theorem d2Sys_le_add {N : ℕ} {f g h : Fin N → ℂ → ℂ} (hf : InUnionClass f)
    (hg : InUnionClass g) (hh : InUnionClass h) : d2Sys f h ≤ d2Sys f g + d2Sys g h := by
  obtain ⟨ε, hε, hf⟩ := hf; obtain ⟨ε', hε', hg⟩ := hg; obtain ⟨ε'', hε'', hh⟩ := hh
  exact d2_le_add (⟨f, hε, hf⟩ : IFS N ε) (⟨g, hε', hg⟩ : IFS N ε') (⟨h, hε'', hh⟩ : IFS N ε'')

theorem eq_of_re_eq_self {ε : ℝ} (hε : 0 < ε) {h : ℂ → ℂ} (hh : InClass ε h) {x y : ℝ}
    (hx : x ∈ I) (hy : y ∈ I) (hhx : (h x).re = x) (hhy : (h y).re = y) : x = y := by
  let Ψ : IFS 1 ε := ⟨fun _ => h, hε, fun _ => hh⟩
  have hle : |x - y| ≤ Ψ.cmax * |x - y| := by
    simpa [Ψ, IFS.comp_cons, IFS.comp_nil, hhx, hhy] using Ψ.abs_re_comp_sub_le_mul [0] hx hy
  by_contra hne
  nlinarith [Ψ.cmax_lt_one, abs_pos.2 (sub_ne_zero.2 hne)]

theorem exists_forall_d2Sys_lt_not_fixed {N : ℕ} {f : Fin N → ℂ → ℂ} (hf : InUnionClass f)
    (hfix : ¬ ∃ x ∈ I, ∀ i, (f i x).re = x) :
    ∃ r > 0, ∀ g, InUnionClass g → d2Sys f g < r → ¬ ∃ x ∈ I, ∀ i, (g i x).re = x := by
  obtain ⟨ε, hε, hfε⟩ := hf
  push Not at hfix
  set F : ℝ → ℝ := fun x => ∑ i, |(f i x).re - x|
  have hcont : ContinuousOn F I := continuousOn_finsetSum _ fun i _ =>
    ((Complex.continuous_re.comp_continuousOn
      ((hfε i).differentiableOn.continuousOn.comp Complex.continuous_ofReal.continuousOn
        fun _ hx => ofReal_mem_nbhd (by linarith) hx)).sub continuousOn_id).abs
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, le_rfl, zero_le_one⟩ hcont
  obtain ⟨i₀, hi₀⟩ := hfix x₀ hx₀
  have hm : 0 < F x₀ := Finset.sum_pos' (fun _ _ => abs_nonneg _)
    ⟨i₀, Finset.mem_univ _, abs_pos.2 (sub_ne_zero.2 hi₀)⟩
  refine ⟨F x₀ / (N + 1), div_pos hm (by positivity), ?_⟩
  rintro g ⟨ε', hε', hgε⟩ hd ⟨x, hx, hgx⟩
  let Φ : IFS N ε := ⟨f, hε, hfε⟩
  let Ψ : IFS N ε' := ⟨g, hε', hgε⟩
  have hsum : F x ≤ N * d2Sys f g := by
    calc F x ≤ ∑ _i : Fin N, d2Sys f g := Finset.sum_le_sum fun i _ => by
          rw [show (f i x).re - x = (f i x - g i x).re by rw [Complex.sub_re, hgx i] ]
          exact (Complex.abs_re_le_norm _).trans (IFS.Continuity.norm_sub_le_d2 Φ Ψ i hx).1
      _ = N * d2Sys f g := by simp
  have hmx : F x₀ ≤ F x := isMinOn_iff.1 hmin x hx
  have h1 : (N : ℝ) * d2Sys f g ≤ N * (F x₀ / (N + 1)) :=
    mul_le_mul_of_nonneg_left hd.le (Nat.cast_nonneg N)
  have h2 : (N : ℝ) * (F x₀ / (N + 1)) < F x₀ := by
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]; linarith
  linarith

theorem exists_not_fixed_d2Sys_lt {N : ℕ} (hN : 2 ≤ N) {f : Fin N → ℂ → ℂ}
    (hf : InUnionClass f) {r : ℝ} (hr : 0 < r) :
    ∃ g, InUnionClass g ∧ (¬ ∃ x ∈ I, ∀ i, (g i x).re = x) ∧ d2Sys f g < r := by
  by_cases hfix : ∃ x ∈ I, ∀ i, (f i x).re = x
  swap
  · exact ⟨f, hf, hfix, by rw [d2Sys_self]; exact hr⟩
  obtain ⟨p, hp, hfp⟩ := hfix
  obtain ⟨ε, hε, hfε⟩ := hf
  let Φ : IFS N ε := ⟨f, hε, hfε⟩
  obtain ⟨j, hj⟩ : ∃ j : Fin N, IFS.Coincidences.slope N * p + IFS.Coincidences.offset j ≠ p := by
    by_contra! h
    have h01 : (⟨0, by omega⟩ : Fin N) < ⟨1, by omega⟩ := Fin.mk_lt_mk.2 one_pos
    linarith [IFS.Coincidences.offset_add_slope_lt_offset h01, h ⟨0, by omega⟩,
      h ⟨1, by omega⟩, IFS.Coincidences.slope_pos (N := N)]
  have : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.2 hN
  obtain ⟨k, hk⟩ := exists_ne j
  set c := Φ.cmin
  have hc : 0 < c := Φ.cmin_pos (by omega)
  obtain ⟨K, hK, hK'⟩ := IFS.Coincidences.exists_deriv_deriv_bound Φ
  set t := min (c / (c + 1)) (r / (4 + K)) / 2
  have ht0 : 0 < t := half_pos (lt_min (by positivity) (by positivity))
  have htt : t < min (c / (c + 1)) (r / (4 + K)) := half_lt_self (lt_min (by positivity) (by positivity))
  have ht1 : t * (c + 1) < c := (lt_div_iff₀ (by positivity)).1 (htt.trans_le (min_le_left _ _))
  have ht2 : t * (4 + K) < r := (lt_div_iff₀ (by positivity)).1 (htt.trans_le (min_le_right _ _))
  set g := Function.update f j (IFS.Coincidences.homotopy Φ t j) with hg
  refine ⟨g, ⟨ε, hε, fun i => ?_⟩, ?_, ?_⟩
  · by_cases hi : i = j
    · rw [hi, hg, Function.update_self]; exact IFS.Coincidences.inClass_homotopy Φ ht0 ht1 j
    · rw [hg, Function.update_of_ne hi]; exact hfε i
  · rintro ⟨x, hx, hgx⟩
    obtain rfl := eq_of_re_eq_self hε (hfε k) hx hp (by simpa [g, Function.update_of_ne hk] using hgx k) (hfp k)
    have h := hgx j
    rw [hg, Function.update_self, IFS.Coincidences.re_homotopy_ofReal,
      show (Φ.f j x).re = x from hfp j] at h
    exact hj (by nlinarith)
  · refine (Real.iSup_le (fun i => ?_) (by positivity)).trans_lt ht2
    by_cases hi : i = j
    · rw [hi, hg, Function.update_self]
      exact IFS.Coincidences.d2Map_homotopy_le Φ j hK (hK' j) ⟨ht0.le, by nlinarith⟩
    · rw [hg, Function.update_of_ne hi]
      simp only [sub_self, norm_zero, ciSup_const, add_zero]; positivity

end OpenDense

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

theorem exdim_entropy_lt (hN : 0 < N) (hc : N * Φ.cmax < 1) {p : Fin N → ℝ}
    (hp : IsProbVec p) : entropy p < -Real.log Φ.cmax := by
  have hc0 : 0 < Φ.cmax := (Φ.cmin_pos hN).trans_le (Φ.cmin_le_cmax hN)
  have hsum : ∑ i, (p i * Real.log Φ.cmax - p i * Real.log (p i)) ≤ ∑ _i : Fin N, Φ.cmax - ∑ i, p i := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hpi := hp.1 i
    have hl := Real.log_le_sub_one_of_pos (div_pos hc0 hpi)
    rw [Real.log_div hc0.ne' hpi.ne'] at hl
    calc p i * Real.log Φ.cmax - p i * Real.log (p i)
        = p i * (Real.log Φ.cmax - Real.log (p i)) := by ring
      _ ≤ p i * (Φ.cmax / p i - 1) := mul_le_mul_of_nonneg_left hl hpi.le
      _ = Φ.cmax - p i := by field_simp
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, one_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [entropy]; linarith

theorem exdim_lt_one (hN : 0 < N) (hc : N * Φ.cmax < 1) {s : ℝ}
    (hs : Tendsto (fun n : ℕ => Real.log (Φ.pressureSum s n) / n) atTop (𝓝 0)) : s < 1 := by
  refine lt_of_not_ge fun h1 => ?_
  have hc0 : 0 < Φ.cmax := (Φ.cmin_pos hN).trans_le (Φ.cmin_le_cmax hN)
  have hpos := Φ.supDeriv_pos hN
  have hle : ∀ n, Φ.pressureSum s n ≤ (N * Φ.cmax) ^ n := fun n => by
    calc Φ.pressureSum s n ≤ ∑ _w : Fin n → Fin N, Φ.cmax ^ n :=
          Finset.sum_le_sum fun w _ => by
            have h : Φ.supDeriv (List.ofFn w) ≤ Φ.cmax ^ n := by simpa using Φ.supDeriv_le (List.ofFn w)
            exact (Real.rpow_le_rpow_of_exponent_ge (hpos _)
              (h.trans (pow_le_one₀ hc0.le Φ.cmax_lt_one.le)) h1).trans (by rwa [Real.rpow_one])
      _ = (N * Φ.cmax) ^ n := by simp [mul_pow]
  have hb : ∀ n : ℕ, 1 ≤ n → Real.log (Φ.pressureSum s n) / n ≤ Real.log (N * Φ.cmax) := fun n hn => by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn']
    exact (Real.log_le_log (Finset.sum_pos (fun _ _ => Real.rpow_pos_of_pos (hpos _) s)
      ⟨fun _ => ⟨0, hN⟩, Finset.mem_univ _⟩) (hle n)).trans_eq (by rw [Real.log_pow]; ring)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  linarith [le_of_tendsto hs (eventually_atTop.2 ⟨1, hb⟩), Real.log_neg (by positivity) hc]

private theorem sum_measureReal_cyl (ν : Measure (ℕ → Fin N)) [IsFiniteMeasure ν] (n : ℕ)
    (S : Finset (Fin n → Fin N)) :
    ∑ v ∈ S, ν.real {y | ∀ i (hi : i < n), y i = v ⟨i, hi⟩} =
      ν.real ((fun (ω : ℕ → Fin N) (k : Fin n) => ω k) ⁻¹' ↑S) := by
  have hm : Measurable fun (ω : ℕ → Fin N) (k : Fin n) => ω k :=
    Measurable.of_eval fun k => measurable_pi_apply (k : ℕ)
  rw [← map_measureReal_apply hm MeasurableSet.of_discrete, ← sum_measureReal_singleton]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_measureReal_apply hm MeasurableSet.of_discrete]
  congr 1; ext y; simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff, funext_iff]
  exact ⟨fun h k => h k k.2, fun h i hi => h ⟨i, hi⟩⟩

private theorem nm_exists_lip (hN : 0 < N) :
    ∃ L, 0 ≤ L ∧ ∀ i, ∀ a ∈ I, ∀ b ∈ I,
      |Real.log ‖deriv (Φ.f i) a‖ - Real.log ‖deriv (Φ.f i) b‖| ≤ L * |a - b| := by
  obtain ⟨M, hM0, hM⟩ := Φ.exists_nonlin_bound
  have hcmin := Φ.cmin_pos hN
  refine ⟨M / Φ.cmin, div_nonneg hM0 hcmin.le, fun i a ha b hb => ?_⟩
  have hd2 : ∀ z ∈ nbhd ε, ‖deriv (deriv (Φ.f i)) z‖ ≤ M := fun z hz => by
    have hz' := subset_closure hz
    rw [show deriv (deriv (Φ.f i)) z = Φ.nonlin i z * deriv (Φ.f i) z by
      rw [nonlin, div_mul_cancel₀ _ ((Φ.inClass i).deriv_ne_zero z hz')], norm_mul]
    exact (mul_le_mul (hM i z hz') ((Φ.inClass i).norm_deriv_lt_one z hz').le (norm_nonneg _) hM0).trans_eq (mul_one M)
  have hmvt := (convex_nbhd ε).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => ((Φ.differentiableOn_f i).deriv (isOpen_nbhd _) z (nbhd_subset_two hz)).differentiableAt
      ((isOpen_nbhd _).mem_nhds (nbhd_subset_two hz))) hd2
    (ofReal_mem_nbhd Φ.ε_pos hb) (ofReal_mem_nbhd Φ.ε_pos ha)
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hmvt
  have key : ∀ {X Y : ℝ}, Φ.cmin ≤ X → Φ.cmin ≤ Y → Real.log X - Real.log Y ≤ |X - Y| / Φ.cmin := by
    intro X Y hX hY
    have hX0 := hcmin.trans_le hX; have hY0 := hcmin.trans_le hY
    calc Real.log X - Real.log Y = Real.log (X / Y) := (Real.log_div hX0.ne' hY0.ne').symm
      _ ≤ X / Y - 1 := Real.log_le_sub_one_of_pos (div_pos hX0 hY0)
      _ = (X - Y) / Y := by field_simp
      _ ≤ |X - Y| / Y := div_le_div_of_nonneg_right (le_abs_self _) hY0.le
      _ ≤ |X - Y| / Φ.cmin := div_le_div_of_nonneg_left (abs_nonneg _) hcmin hY
  have ha' := Φ.cmin_le_norm_deriv i (subset_closure (ofReal_mem_nbhd Φ.ε_pos ha))
  have hb' := Φ.cmin_le_norm_deriv i (subset_closure (ofReal_mem_nbhd Φ.ε_pos hb))
  exact (abs_le.2 ⟨by have := key hb' ha'; rw [abs_sub_comm] at this; linarith, key ha' hb'⟩).trans
    ((div_le_div_of_nonneg_right ((abs_norm_sub_norm_le _ _).trans hmvt) hcmin.le).trans_eq (by ring))

private theorem nm_exists_distortion (hN : 0 < N) :
    ∃ Δ, 0 ≤ Δ ∧ ∀ (w : List (Fin N)) {y : ℝ}, y ∈ I →
      |Real.log (Φ.supDeriv w) - Real.log ‖deriv (Φ.comp w) y‖| ≤ Δ := by
  obtain ⟨L, hL0, hL⟩ := Φ.nm_exists_lip hN
  have hc1 : 0 < 1 - Φ.cmax := sub_pos.2 Φ.cmax_lt_one
  have hcl : ∀ {x : ℝ}, x ∈ I → (x : ℂ) ∈ closure (nbhd ε) := fun hx =>
    subset_closure (ofReal_mem_nbhd Φ.ε_pos hx)
  have hchain : ∀ (w : List (Fin N)) {y y' : ℝ}, y ∈ I → y' ∈ I →
      |Real.log ‖deriv (Φ.comp w) y‖ - Real.log ‖deriv (Φ.comp w) y'‖| ≤
        L * ∑ k ∈ Finset.range w.length, Φ.cmax ^ k := by
    intro w; induction w with
    | nil => intros; simp
    | cons i v ih =>
      intro y y' hy hy'
      have hne : ∀ {x : ℝ}, x ∈ I → ‖deriv (Φ.comp v) x‖ ≠ 0 := fun hx =>
        norm_ne_zero_iff.2 (Φ.deriv_comp_ne_zero v (hcl hx))
      have hne' : ∀ {x : ℝ}, x ∈ I → ‖deriv (Φ.f i) ((Φ.comp v x).re : ℂ)‖ ≠ 0 := fun hx =>
        norm_ne_zero_iff.2 ((Φ.inClass i).deriv_ne_zero _ (hcl (Φ.re_comp_mem_I v hx)))
      rw [Φ.deriv_comp_cons i v (hcl hy), Φ.deriv_comp_cons i v (hcl hy'), norm_mul, norm_mul,
        Φ.comp_ofReal v hy, Φ.comp_ofReal v hy', Real.log_mul (hne' hy) (hne hy),
        Real.log_mul (hne' hy') (hne hy'), List.length_cons, Finset.sum_range_succ, add_sub_add_comm]
      exact (abs_add_le _ _).trans ((add_le_add
        ((hL i _ (Φ.re_comp_mem_I v hy) _ (Φ.re_comp_mem_I v hy')).trans
          (mul_le_mul_of_nonneg_left (Φ.abs_re_comp_sub_le v hy hy') hL0))
        (ih hy hy')).trans_eq (by ring))
  refine ⟨L / (1 - Φ.cmax), div_nonneg hL0 hc1.le, fun w y hy => ?_⟩
  have hgeom : ∑ k ∈ Finset.range w.length, Φ.cmax ^ k ≤ 1 / (1 - Φ.cmax) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := w.length) Φ.cmax_nonneg Φ.cmax_lt_one
    rwa [← Finset.range_eq_Ico, pow_zero] at this
  have hcont : ContinuousOn (fun x : ℝ => ‖deriv (Φ.comp w) x‖) I :=
    (((Φ.differentiableOn_comp w).deriv (isOpen_nbhd ε)).continuousOn.comp
      Complex.continuous_ofReal.continuousOn fun _ hx => ofReal_mem_nbhd Φ.ε_pos hx).norm
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, zero_le_one⟩ hcont
  have : Nonempty I := ⟨⟨0, le_rfl, zero_le_one⟩⟩
  have hsup : Φ.supDeriv w = ‖deriv (Φ.comp w) x₀‖ :=
    le_antisymm (ciSup_le fun x => hmax x.2) (Φ.norm_deriv_le_supDeriv w hx₀)
  rw [hsup]
  exact (hchain w hx₀ hy).trans ((mul_le_mul_of_nonneg_left hgeom hL0).trans_eq (by ring))

private theorem nm_comp_natProj (ω : ℕ → Fin N) (k : ℕ) :
    Φ.comp (List.ofFn fun j : Fin k => ω j) (Φ.natProj fun j => ω (j + k)) = Φ.natProj ω := by
  rw [Φ.comp_ofReal _ (Φ.attractor_subset_I ⟨_, rfl⟩), ← Φ.natProj_eq_comp_prefix]

private theorem nm_birkhoff (s : ℝ) (m : ℕ) (x : ℕ → Fin N) :
    ∑ k ∈ Finset.range m, Φ.potential s (fun i => x (i + k)) =
      s * Real.log ‖deriv (Φ.comp (List.ofFn fun j : Fin m => x j))
        (Φ.natProj fun i => x (i + m))‖ := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    have hπ : Φ.natProj (fun i => x (i + m + 1)) ∈ I := Φ.attractor_subset_I ⟨_, rfl⟩
    have hz := subset_closure (ofReal_mem_nbhd Φ.ε_pos hπ)
    set v := List.ofFn fun j : Fin m => x (j + 1) with hv
    have hlist : (List.ofFn fun j : Fin (m + 1) => x j) = x 0 :: v := by rw [List.ofFn_succ]; simp [hv]
    rw [Finset.sum_range_succ',
      show (∑ k ∈ Finset.range m, Φ.potential s fun i => x (i + (k + 1))) =
        ∑ k ∈ Finset.range m, Φ.potential s fun i => x (i + k + 1) from rfl,
      ih (fun j => x (j + 1)),
      show (fun i => x (i + (m + 1))) = fun i => x (i + m + 1) from rfl,
      hlist, Φ.deriv_comp_cons _ _ hz, Φ.nm_comp_natProj (fun i => x (i + 1)) m,
      show Φ.potential s (fun i => x (i + 0)) =
        s * Real.log ‖deriv (Φ.f (x 0)) (Φ.natProj fun i => x (i + 1))‖ from rfl,
      norm_mul, Real.log_mul (norm_ne_zero_iff.2 ((Φ.inClass _).deriv_ne_zero _
        (subset_closure (ofReal_mem_nbhd Φ.ε_pos (Φ.attractor_subset_I ⟨_, rfl⟩)))))
        (norm_ne_zero_iff.2 (Φ.deriv_comp_ne_zero _ hz))]
    ring

theorem exists_isGibbsMeasure (hB : BowenGibbsStatement) (hN : 0 < N) (s : ℝ) :
    ∃ ν : Measure (ℕ → Fin N), IsProbabilityMeasure ν ∧ IsGibbsMeasure (Φ.potential s) ν := by
  obtain ⟨L, hL0, hL⟩ := Φ.nm_exists_lip hN
  have hcmin := Φ.cmin_pos hN
  have hcmax : 0 < Φ.cmax := hcmin.trans_le (Φ.cmin_le_cmax hN)
  have hlog : Real.log Φ.cmin ≤ Real.log Φ.cmax := Real.log_le_log hcmin (Φ.cmin_le_cmax hN)
  set b := |s| * (L / Φ.cmax + (Real.log Φ.cmax - Real.log Φ.cmin)) + 1 with hb_def
  have hb : 0 < b := add_pos_of_nonneg_of_pos
    (mul_nonneg (abs_nonneg s) (add_nonneg (div_nonneg hL0 hcmax.le) (sub_nonneg.2 hlog))) one_pos
  refine hB hN (Φ.potential s) hb hcmax Φ.cmax_lt_one fun k x y hxy => ?_
  simp only [potential, Challenge.potential]; rw [← mul_sub, abs_mul]
  have hx := Φ.attractor_subset_I ⟨fun i => x (i + 1), rfl⟩
  have hy := Φ.attractor_subset_I ⟨fun i => y (i + 1), rfl⟩
  rcases k with _ | k
  · have hbd : ∀ (i : Fin N) {t : ℝ}, t ∈ I → Real.log Φ.cmin ≤ Real.log ‖deriv (Φ.f i) t‖ ∧
        Real.log ‖deriv (Φ.f i) t‖ ≤ Real.log Φ.cmax := fun i t ht => by
      have hcl := subset_closure (ofReal_mem_nbhd Φ.ε_pos ht)
      exact ⟨Real.log_le_log hcmin (Φ.cmin_le_norm_deriv i hcl),
        Real.log_le_log (hcmin.trans_le (Φ.cmin_le_norm_deriv i hcl)) (Φ.norm_deriv_le_cmax i hcl)⟩
    obtain ⟨h1, h2⟩ := hbd (x 0) hx
    obtain ⟨h3, h4⟩ := hbd (y 0) hy
    have hd : |Real.log ‖deriv (Φ.f (x 0)) (Φ.natProj fun i => x (i + 1))‖ -
        Real.log ‖deriv (Φ.f (y 0)) (Φ.natProj fun i => y (i + 1))‖| ≤
        L / Φ.cmax + (Real.log Φ.cmax - Real.log Φ.cmin) :=
      abs_le.2 ⟨by linarith [div_nonneg hL0 hcmax.le], by linarith [div_nonneg hL0 hcmax.le]⟩
    rw [pow_zero, mul_one]
    linarith [mul_le_mul_of_nonneg_left hd (abs_nonneg s)]
  · have h0 : x 0 = y 0 := hxy 0 (Nat.succ_pos k)
    have hu : (List.ofFn fun j : Fin k => x (j + 1)) = List.ofFn fun j : Fin k => y (j + 1) :=
      congrArg List.ofFn (funext fun j => hxy _ (by omega))
    have hdist : |Φ.natProj (fun i => x (i + 1)) - Φ.natProj (fun i => y (i + 1))| ≤ Φ.cmax ^ k := by
      have h := Φ.abs_re_comp_sub_le (List.ofFn fun j : Fin k => x (j + 1))
        (Φ.attractor_subset_I ⟨fun j => x (j + k + 1), rfl⟩)
        (Φ.attractor_subset_I ⟨fun j => y (j + k + 1), rfl⟩)
      rwa [List.length_ofFn, Φ.nm_comp_natProj (fun i => x (i + 1)) k, Complex.ofReal_re,
        hu, Φ.nm_comp_natProj (fun i => y (i + 1)) k, Complex.ofReal_re] at h
    have hd := (hL (x 0) _ hx _ hy).trans (mul_le_mul_of_nonneg_left hdist hL0)
    rw [← h0]
    have hb' : |s| * (L / Φ.cmax) ≤ b := by
      rw [hb_def]; nlinarith [mul_nonneg (abs_nonneg s) (sub_nonneg.2 hlog)]
    calc |s| * |Real.log ‖deriv (Φ.f (x 0)) (Φ.natProj fun i => x (i + 1))‖ -
          Real.log ‖deriv (Φ.f (x 0)) (Φ.natProj fun i => y (i + 1))‖|
        ≤ |s| * (L * Φ.cmax ^ k) := mul_le_mul_of_nonneg_left hd (abs_nonneg s)
      _ = |s| * (L / Φ.cmax) * Φ.cmax ^ (k + 1) := by rw [pow_succ]; field_simp
      _ ≤ b * Φ.cmax ^ (k + 1) := mul_le_mul_of_nonneg_right hb' (pow_nonneg hcmax.le _)

private theorem pressure_eq_zero_of_gibbs (hN : 0 < N) {s c₁ c₂ P : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hs : Tendsto (fun n : ℕ => Real.log (Φ.pressureSum s n) / n) atTop (𝓝 0))
    {ν : Measure (ℕ → Fin N)} [IsProbabilityMeasure ν]
    (hG : ∀ (x : ℕ → Fin N) (m : ℕ),
      c₁ * Real.exp (-P * m + ∑ k ∈ Finset.range m, Φ.potential s (fun i => x (i + k))) ≤
          ν.real {y | ∀ i < m, y i = x i} ∧
        ν.real {y | ∀ i < m, y i = x i} ≤
          c₂ * Real.exp (-P * m + ∑ k ∈ Finset.range m, Φ.potential s (fun i => x (i + k)))) :
    P = 0 := by
  obtain ⟨Δ, hΔ0, hΔ⟩ := Φ.nm_exists_distortion hN
  set A := |s| * Δ
  set K₁ := c₁ * Real.exp (-A)
  set K₂ := c₂ * Real.exp A
  have hK₁ : 0 < K₁ := mul_pos hc₁ (Real.exp_pos _)
  have hK₂ : 0 < K₂ := mul_pos hc₂ (Real.exp_pos _)
  have key : ∀ (m : ℕ) (v : Fin m → Fin N),
      K₁ * Real.exp (-P * m) * Φ.supDeriv (List.ofFn v) ^ s ≤
          ν.real {y | ∀ i (hi : i < m), y i = v ⟨i, hi⟩} ∧
        ν.real {y | ∀ i (hi : i < m), y i = v ⟨i, hi⟩} ≤
          K₂ * Real.exp (-P * m) * Φ.supDeriv (List.ofFn v) ^ s := fun m v => by
    let x (i : ℕ) : Fin N := if hi : i < m then v ⟨i, hi⟩ else ⟨0, hN⟩
    obtain ⟨h1, h2⟩ := hG x m
    have hcyl : {y : ℕ → Fin N | ∀ i < m, y i = x i} = {y | ∀ i (hi : i < m), y i = v ⟨i, hi⟩} := by
      ext y; simp +contextual [x]
    rw [hcyl, Φ.nm_birkhoff, show (List.ofFn fun j : Fin m => x j) = List.ofFn v from
      congrArg List.ofFn (funext fun j => by simp [x, j.2])] at h1 h2
    have hd : |s * Real.log (Φ.supDeriv (List.ofFn v)) -
        s * Real.log ‖deriv (Φ.comp (List.ofFn v)) (Φ.natProj fun i => x (i + m))‖| ≤ A := by
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hΔ _ (Φ.attractor_subset_I ⟨_, rfl⟩)) (abs_nonneg s)
    rw [abs_le] at hd
    have hrpow : Φ.supDeriv (List.ofFn v) ^ s = Real.exp (s * Real.log (Φ.supDeriv (List.ofFn v))) := by
      rw [Real.rpow_def_of_pos (Φ.supDeriv_pos hN _), mul_comm]
    have e : ∀ c B : ℝ, c * Real.exp B * Real.exp (-P * m) * Φ.supDeriv (List.ofFn v) ^ s =
        c * Real.exp (-P * m + (s * Real.log (Φ.supDeriv (List.ofFn v)) + B)) := fun c B => by
      rw [hrpow, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]; congr 2; ring
    exact ⟨(e c₁ (-A)).trans_le ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hc₁.le).trans h1),
      h2.trans ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hc₂.le).trans_eq (e c₂ A).symm)⟩
  have hps : ∀ m, 0 < Φ.pressureSum s m := fun m =>
    Finset.sum_pos (fun _ _ => Real.rpow_pos_of_pos (Φ.supDeriv_pos hN _) s)
      ⟨fun _ => ⟨0, hN⟩, Finset.mem_univ _⟩
  have hlog : ∀ m : ℕ, -Real.log K₂ ≤ Real.log (Φ.pressureSum s m) - P * m ∧
      Real.log (Φ.pressureSum s m) - P * m ≤ -Real.log K₁ := fun m => by
    have huniv : ∑ v : Fin m → Fin N, ν.real {y | ∀ i (hi : i < m), y i = v ⟨i, hi⟩} = 1 := by
      rw [sum_measureReal_cyl, Finset.coe_univ, preimage_univ, probReal_univ]
    have h1 : K₁ * Real.exp (-P * m) * Φ.pressureSum s m ≤ 1 := by
      rw [← huniv, pressureSum, Finset.mul_sum]
      exact Finset.sum_le_sum fun v _ => (key m v).1
    have h2 : 1 ≤ K₂ * Real.exp (-P * m) * Φ.pressureSum s m := by
      rw [← huniv, pressureSum, Finset.mul_sum]
      exact Finset.sum_le_sum fun v _ => (key m v).2
    have hl : ∀ K : ℝ, 0 < K → Real.log (K * Real.exp (-P * m) * Φ.pressureSum s m) =
        Real.log K + -P * m + Real.log (Φ.pressureSum s m) := fun K hK => by
      rw [Real.log_mul (mul_pos hK (Real.exp_pos _)).ne' (hps m).ne',
        Real.log_mul hK.ne' (Real.exp_pos _).ne', Real.log_exp]
    have l1 := Real.log_le_log (mul_pos (mul_pos hK₁ (Real.exp_pos _)) (hps m)) h1
    have l2 := Real.log_le_log one_pos h2
    rw [hl K₁ hK₁, Real.log_one] at l1
    rw [hl K₂ hK₂, Real.log_one] at l2
    exact ⟨by linarith, by linarith⟩
  have hdiff : Tendsto (fun n : ℕ => Real.log (Φ.pressureSum s n) / n - P) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (tendsto_const_div_atTop_nhds_zero_nat (|Real.log K₁| + |Real.log K₂|))
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [sub_zero, Real.norm_eq_abs, div_sub' hn'.ne', abs_div, abs_of_pos hn']
    refine div_le_div_of_nonneg_right (abs_le.2 ⟨?_, ?_⟩) hn'.le
    · linarith [(hlog n).1, le_abs_self (Real.log K₂), abs_nonneg (Real.log K₁)]
    · linarith [(hlog n).2, neg_abs_le (Real.log K₁), abs_nonneg (Real.log K₂)]
  have hP0 := tendsto_nhds_unique ((hs.sub hdiff).congr fun _ => sub_sub_cancel _ _) (tendsto_const_nhds (x := P))
  linarith

end IFS

def ldWords (n : ℕ) : Finset (Fin n → Fin 3) := Fintype.piFinset fun _ => {0, 1}

theorem ld_mem_words {n : ℕ} {v : Fin n → Fin 3} : v ∈ ldWords n ↔ ∀ k, v k ≠ 2 := by
  rw [ldWords, Fintype.mem_piFinset]
  exact forall_congr' fun k => by generalize v k = i; revert i; decide

private theorem ld_f_ofReal (i : Fin 3) (hi : i ≠ 2) (x : ℝ) :
    ∃ y : ℝ, exampleIFS.f i x = y ∧ x / 8 ≤ y ∧ y ≤ x / 8 + x ^ 2 / 32 := by
  rcases fin3 i with rfl | rfl | rfl
  · exact ⟨x / 8, by simp [exampleIFS, exampleMaps], le_rfl, by nlinarith⟩
  · exact ⟨x / 8 + x ^ 2 / 32, by simp [exampleIFS, exampleMaps], by nlinarith, le_rfl⟩
  · exact absurd rfl hi

private theorem ld_le_re_comp {w : List (Fin 3)} (hw : ∀ i ∈ w, i ≠ 2) {x : ℝ} (hx : x ∈ I) :
    (1 / 8 : ℝ) ^ w.length * x ≤ (exampleIFS.comp w x).re := by
  induction w with
  | nil => simp
  | cons i w ih =>
    obtain ⟨y, hy', h1, -⟩ := ld_f_ofReal i (hw i List.mem_cons_self) _
    have := ih fun j hj => hw j (List.mem_cons_of_mem i hj)
    rw [IFS.comp_cons, Function.comp_apply, exampleIFS.comp_ofReal w hx, hy', Complex.ofReal_re,
      List.length_cons, pow_succ]
    nlinarith

private theorem ld_re_comp_le {w : List (Fin 3)} (hw : ∀ i ∈ w, i ≠ 2) {x : ℝ} (hx : x ∈ I) :
    (exampleIFS.comp w x).re ≤ (1 / 8 : ℝ) ^ w.length * (x * (1 + x)) := by
  induction w using List.reverseRecOn generalizing x with
  | nil => simp only [IFS.comp_nil, id, Complex.ofReal_re, List.length_nil, pow_zero, one_mul]; nlinarith [hx.1]
  | append_singleton u i ih =>
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨y, hy, h1, h2⟩ := ld_f_ofReal i (hw i (List.mem_append_right _ (List.mem_singleton_self i))) x
    rw [exampleIFS.comp_append, Function.comp_apply, show exampleIFS.comp [i] = exampleIFS.f i from rfl,
      hy, List.length_append, List.length_singleton, pow_succ]
    have hyy : y * (1 + y) ≤ 1 / 8 * (x * (1 + x)) := by
      have h3 := mul_le_mul h2 (by linarith : 1 + y ≤ 1 + (x / 8 + x ^ 2 / 32)) (by linarith) (by positivity)
      have : x ^ 2 ≤ x := by nlinarith
      have : x ^ 3 ≤ x ^ 2 := by nlinarith
      have : x ^ 4 ≤ x ^ 3 := by nlinarith
      nlinarith
    exact (ih (fun j hj => hw j (List.mem_append_left _ hj)) ⟨by linarith, by nlinarith⟩).trans
      ((mul_le_mul_of_nonneg_left hyy (by positivity)).trans_eq (by ring))

theorem ld_natProj_le {n : ℕ} {ω : ℕ → Fin 3} (h : (fun k : Fin n => ω k) ∈ ldWords n) :
    exampleIFS.natProj ω ≤ 2 * (1 / 8 : ℝ) ^ n := by
  have hy := exampleIFS.attractor_subset_I ⟨fun j => ω (j + n), rfl⟩
  rw [exampleIFS.natProj_eq_comp_prefix ω n]
  refine (ld_re_comp_le (fun _ hi => by obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hi; exact ld_mem_words.1 h k) hy).trans ?_
  rw [List.length_ofFn]
  have : exampleIFS.natProj (fun j => ω (j + n)) * (1 + exampleIFS.natProj (fun j => ω (j + n))) ≤ 2 :=
    by nlinarith [hy.1, hy.2]
  nlinarith [(show (0 : ℝ) ≤ (1 / 8) ^ n by positivity)]

private theorem ld_le_natProj {k : ℕ} {ω : ℕ → Fin 3} (hk : ω k = 2) (h : ∀ j < k, ω j ≠ 2) :
    29 / 32 * (1 / 8 : ℝ) ^ k ≤ exampleIFS.natProj ω := by
  have hw : ∀ i ∈ List.ofFn (fun j : Fin k => ω j), i ≠ 2 := fun _ hi => by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hi; exact h j j.2
  set σ : ℕ → Fin 3 := fun j => ω (j + k)
  have hy := exampleIFS.attractor_subset_I ⟨σ, rfl⟩
  have hz := exampleIFS.attractor_subset_I ⟨fun j => σ (j + 1), rfl⟩
  have h29 : 29 / 32 ≤ exampleIFS.natProj σ := by
    rw [exampleIFS.natProj_eq_comp_prefix σ 1,
      show (List.ofFn fun j : Fin 1 => σ j) = [2] by simp [σ, hk],
      IFS.comp_cons, IFS.comp_nil, Function.comp_apply, id]
    have h2 : exampleIFS.f 2 (exampleIFS.natProj fun j => σ (j + 1)) =
        (((exampleIFS.natProj fun j => σ (j + 1)) / 16 +
          (exampleIFS.natProj fun j => σ (j + 1)) ^ 2 / 32 + 29 / 32 : ℝ) : ℂ) := by
      simp [exampleIFS, exampleMaps]
    rw [h2, Complex.ofReal_re]; nlinarith [hz.1]
  rw [exampleIFS.natProj_eq_comp_prefix ω k]
  refine le_trans ?_ (ld_le_re_comp hw hy)
  rw [List.length_ofFn]; nlinarith [(show (0 : ℝ) ≤ (1 / 8) ^ k by positivity)]

private theorem ld_natProj_eq_zero {ω : ℕ → Fin 3} (h : ∀ j, ω j ≠ 2) :
    exampleIFS.natProj ω = 0 := by
  have hc0 : ∀ {w : List (Fin 3)}, (∀ i ∈ w, i ≠ 2) → exampleIFS.comp w 0 = 0 := by
    intro w hw; induction w with
    | nil => rfl
    | cons i w ih =>
      rw [IFS.comp_cons, Function.comp_apply, ih fun j hj => hw j (List.mem_cons_of_mem i hj)]
      have hi := hw i List.mem_cons_self
      rcases fin3 i with rfl | rfl | rfl <;>
        [simp [exampleIFS, exampleMaps]; simp [exampleIFS, exampleMaps]; exact absurd rfl hi]
  exact tendsto_nhds_unique (exampleIFS.tendsto_natProj ω) <| tendsto_const_nhds.congr fun n => by
    rw [hc0 fun _ hi => by obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hi; exact h k]; simp

private theorem tendsto_log_div_log_of_bounds {m : ℝ → ℝ} {lam ρ a b : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam < 1) (hρ : 0 < ρ) (ha : 0 < a) (hb : 0 < b)
    (h : ∀ (n : ℕ) (r : ℝ), lam ^ (n + 2) < r → r ≤ lam ^ (n + 1) →
      a * ρ ^ n ≤ m r ∧ m r ≤ b * ρ ^ n) :
    Tendsto (fun r => Real.log (m r) / Real.log r) (𝓝[>] 0)
      (𝓝 (Real.log ρ / Real.log lam)) := by
  set d := Real.log ρ / Real.log lam
  set K := |Real.log a| + |Real.log b| + 2 * |Real.log ρ|
  have hL : Real.log lam < 0 := Real.log_neg hlam0 hlam1
  have hbound : ∀ r, 0 < r → r < lam → |Real.log (m r) - d * Real.log r| ≤ K := by
    intro r hr0 hr
    obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one hr0 (hr.le.trans hlam1.le) hlam0 hlam1
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := by
      rcases k with _ | n
      · rw [zero_add, pow_one] at hk1; linarith
      · exact ⟨n, rfl⟩
    obtain ⟨h1, h2⟩ := h n r hk1 hk2
    have hρn := pow_pos hρ n
    have hl1 : Real.log a + n * Real.log ρ ≤ Real.log (m r) := by
      simpa [Real.log_mul ha.ne' hρn.ne', Real.log_pow] using Real.log_le_log (mul_pos ha hρn) h1
    have hl2 : Real.log (m r) ≤ Real.log b + n * Real.log ρ := by
      simpa [Real.log_mul hb.ne' hρn.ne', Real.log_pow] using
        Real.log_le_log ((mul_pos ha hρn).trans_le h1) h2
    have hr1 : (n + 2) * Real.log lam < Real.log r := by
      have := Real.log_lt_log (pow_pos hlam0 _) hk1; rw [Real.log_pow] at this; push_cast at this; linarith
    have hr2 : Real.log r ≤ (n + 1) * Real.log lam := by
      have := Real.log_le_log hr0 hk2; rw [Real.log_pow] at this; push_cast at this; linarith
    set t := Real.log r / Real.log lam
    have ht1 : n + 1 ≤ t := (le_div_iff_of_neg hL).2 hr2
    have ht2 : t ≤ n + 2 := (div_le_iff_of_neg hL).2 hr1.le
    rw [show d * Real.log r = Real.log ρ * t by simp [d, t]; ring,
      show Real.log (m r) - Real.log ρ * t =
        (Real.log (m r) - n * Real.log ρ) + (n - t) * Real.log ρ by ring]
    refine (abs_add_le _ _).trans ?_
    have hA : |Real.log (m r) - n * Real.log ρ| ≤ |Real.log a| + |Real.log b| := by
      rw [abs_le]
      constructor <;> linarith [neg_abs_le (Real.log a), le_abs_self (Real.log b),
        abs_nonneg (Real.log a), abs_nonneg (Real.log b)]
    have hB : |(n - t) * Real.log ρ| ≤ 2 * |Real.log ρ| := by
      rw [abs_mul]; gcongr; rw [abs_le]; constructor <;> linarith
    linarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    ((tendsto_const_nhds (x := K)).div_atTop (tendsto_abs_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero))
  filter_upwards [Ioo_mem_nhdsGT hlam0] with r hr
  have hlr : Real.log r ≠ 0 := (Real.log_neg hr.1 (hr.2.trans hlam1)).ne
  rw [Real.norm_eq_abs, show Real.log (m r) / Real.log r - d =
    (Real.log (m r) - d * Real.log r) / Real.log r by field_simp, abs_div]
  exact div_le_div_of_nonneg_right (hbound r hr.1 hr.2) (abs_nonneg _)

noncomputable def lqSum (μ : Measure ℝ) (q r : ℝ) : ℝ :=
  ∑' k : ℤ, μ.real (Ico (k * r) ((k + 1) * r)) ^ q

noncomputable def lqRatio (μ : Measure ℝ) (q r : ℝ) : ℝ := Real.log (lqSum μ q r) / Real.log r

private theorem lq_summable_and_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ] {q r : ℝ}
    (hq : 1 ≤ q) (hr : 0 < r) :
    Summable (fun k : ℤ => μ.real (Ico (k * r) ((k + 1) * r)) ^ q) ∧ 0 ≤ lqSum μ q r ∧
      lqSum μ q r ≤ 1 := by
  have hU : ⋃ k : ℤ, Ico (k * r) ((k + 1) * r) = univ := by
    simpa [zsmul_eq_mul] using iUnion_Ico_zsmul hr
  have hD : Pairwise (Function.onFun Disjoint fun k : ℤ => Ico (k * r) ((k + 1) * r)) := by
    simpa [zsmul_eq_mul] using pairwise_disjoint_Ico_zsmul r
  have h := measure_iUnion (μ := μ) hD fun _ => measurableSet_Ico
  rw [hU, measure_univ] at h
  have hS := ENNReal.hasSum_toReal (h ▸ ENNReal.one_ne_top)
  rw [← ENNReal.tsum_toReal_eq fun _ => measure_ne_top _ _, ← h, ENNReal.toReal_one] at hS
  have hle : ∀ k : ℤ, μ.real (Ico (k * r) ((k + 1) * r)) ^ q ≤ μ.real (Ico (k * r) ((k + 1) * r)) :=
    fun _ => Real.rpow_le_self_of_le_one measureReal_nonneg measureReal_le_one hq
  have hsum := Summable.of_nonneg_of_le (fun _ => by positivity) hle hS.summable
  exact ⟨hsum, tsum_nonneg fun _ => by positivity, (hsum.tsum_le_tsum hle hS.summable).trans_eq hS.tsum_eq⟩

theorem example_bowen_core (hB : BowenGibbsStatement) :
    ∃ s : ℝ,
      (∀ t, Tendsto (Challenge.pressureRatio exampleMaps t) atTop (𝓝 0) ↔ t = s) ∧
      (∃ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν ∧ IsGibbsMeasure (exampleIFS.potential s) ν) ∧
      ∀ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν → IsGibbsMeasure (exampleIFS.potential s) ν →
        Tendsto (fun r : Scale => logRatio ((ν.map exampleIFS.natProj).real (closedBall 0 r)) r)
          scaleZero (𝓝 (s - 1 / 3)) ∧
        ∀ q > 1, ∀ hq0 : q - 1 ≠ 0,
          Challenge.lqDim (ν.map exampleIFS.natProj) q hq0 ≤ divide q (q - 1) hq0 * (s - 1 / 3) := by
  obtain ⟨s, -, hs⟩ := exampleIFS.exists_pressure_zero (by norm_num)
  refine ⟨s, fun t => (positive_length_tendsto_iff _).trans (hs t),
    exampleIFS.exists_isGibbsMeasure hB (by norm_num) s, fun ν _ hGν => ?_⟩
  obtain ⟨c₁, hc₁, c₂, hc₂, P, hG⟩ := hGν
  obtain rfl : P = 0 := exampleIFS.pressure_eq_zero_of_gibbs (by norm_num) hc₁ hc₂ ((hs s).2 rfl) hG
  set ρ : ℝ := 2 * (1 / 8 : ℝ) ^ s with hρ_def
  have hρ : 0 < ρ := mul_pos two_pos (Real.rpow_pos_of_pos (by norm_num) s)
  obtain ⟨d0, d1, -⟩ := deriv_exampleMaps
  have hsum : ∀ n,
      c₁ * ρ ^ n ≤ ν.real ((fun (ω : ℕ → Fin 3) (k : Fin n) => ω k) ⁻¹' ↑(ldWords n)) ∧
        ν.real ((fun (ω : ℕ → Fin 3) (k : Fin n) => ω k) ⁻¹' ↑(ldWords n)) ≤ c₂ * ρ ^ n := fun n => by
    rw [← IFS.sum_measureReal_cyl]
    have hterm : ∀ v ∈ ldWords n,
        c₁ * ((1 / 8 : ℝ) ^ s) ^ n ≤ ν.real {y | ∀ i (hi : i < n), y i = v ⟨i, hi⟩} ∧
          ν.real {y | ∀ i (hi : i < n), y i = v ⟨i, hi⟩} ≤ c₂ * ((1 / 8 : ℝ) ^ s) ^ n := fun v hv => by
      let x (i : ℕ) : Fin 3 := if hi : i < n then v ⟨i, hi⟩ else 0
      have hx_ne : ∀ j, x j ≠ 2 := fun j => by
        dsimp only [x]; split_ifs with hj <;> [exact ld_mem_words.1 hv ⟨j, hj⟩; decide]
      have hpot : ∀ k, exampleIFS.potential s (fun i => x (i + k)) = s * Real.log (1 / 8) := fun k => by
        simp only [IFS.potential, Challenge.potential, ld_natProj_eq_zero fun i => hx_ne _, Complex.ofReal_zero]
        have hi := hx_ne (0 + k)
        have hd : ‖deriv (exampleIFS.f (x (0 + k))) 0‖ = 1 / 8 := by
          change ‖deriv (exampleMaps (x (0 + k))) 0‖ = 1 / 8
          rcases fin3 (x (0 + k)) with h | h | h <;> rw [h]
          · rw [d0]; norm_num
          · rw [d1]; norm_num
          · exact absurd h hi
        rw [hd]
      obtain ⟨h1, h2⟩ := hG x n
      have hcyl : {y : ℕ → Fin 3 | ∀ i < n, y i = x i} = {y | ∀ i (hi : i < n), y i = v ⟨i, hi⟩} := by
        ext y; simp +contextual [x]
      rw [hcyl] at h1 h2
      have hexp : Real.exp (-0 * ↑n +
          ∑ k ∈ Finset.range n, exampleIFS.potential s (fun i => x (i + k))) =
          ((1 / 8 : ℝ) ^ s) ^ n := by
        simp only [hpot, neg_zero, zero_mul, zero_add, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul, Real.exp_nat_mul]
        rw [mul_comm s, ← Real.rpow_def_of_pos (by norm_num)]
      rw [hexp] at h1 h2; exact ⟨h1, h2⟩
    have hcard : (ldWords n).card = 2 ^ n := by
      rw [ldWords, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]; rfl
    have hs1 := Finset.sum_le_sum fun v hv => (hterm v hv).1
    have hs2 := Finset.sum_le_sum fun v hv => (hterm v hv).2
    rw [Finset.sum_const, hcard, nsmul_eq_mul] at hs1 hs2
    push_cast at hs1 hs2
    exact ⟨(by rw [hρ_def, mul_pow]; ring : c₁ * ρ ^ n = _).trans_le hs1,
      hs2.trans_eq (by rw [hρ_def, mul_pow]; ring)⟩
  have hlow : ∀ n, c₁ * ρ ^ n ≤
      ν.real (exampleIFS.natProj ⁻¹' closedBall 0 (2 * (1 / 8 : ℝ) ^ n)) := fun n =>
    (hsum n).1.trans <| measureReal_mono fun ω hω => by
      rw [mem_preimage, mem_closedBall, Real.dist_eq, sub_zero,
        abs_of_nonneg (exampleIFS.attractor_subset_I ⟨ω, rfl⟩).1]
      exact ld_natProj_le hω
  have hup : ∀ n r, r < 29 / 32 * (1 / 8 : ℝ) ^ n →
      ν.real (exampleIFS.natProj ⁻¹' closedBall 0 r) ≤ c₂ * ρ ^ (n + 1) := fun n r hr =>
    (measureReal_mono fun ω hω => by
      rw [mem_preimage, mem_closedBall, Real.dist_eq, sub_zero] at hω
      have hle : exampleIFS.natProj ω ≤ r := (le_abs_self _).trans hω
      have key : ∀ k, k ≤ n → ω k ≠ 2 := fun k => by
        induction k using Nat.strong_induction_on with
        | _ k ih =>
          intro hk h2
          linarith [ld_le_natProj h2 fun j hj => ih j hj (hj.trans_le hk).le,
            (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk : (1 / 8 : ℝ) ^ n ≤ (1 / 8) ^ k)]
      exact ld_mem_words.2 fun k => key k (Nat.lt_succ_iff.1 k.2)).trans (hsum (n + 1)).2
  have hd : s - 1 / 3 = Real.log ρ / Real.log (1 / 8) := by
    have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have h8 : Real.log (1 / 8) = -(3 * Real.log 2) := by
      rw [one_div, Real.log_inv, show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
    rw [hρ_def, Real.log_mul two_ne_zero (Real.rpow_pos_of_pos (by norm_num) s).ne',
      Real.log_rpow (by norm_num), h8]
    field_simp; ring
  set μ := ν.map exampleIFS.natProj
  have : IsProbabilityMeasure μ :=
    ⟨by rw [Measure.map_apply exampleIFS.measurable_natProj MeasurableSet.univ, preimage_univ, measure_univ]⟩
  refine ⟨?_, fun q hq hq0 => ?_⟩
  · change Tendsto ((fun r : ℝ => Real.log (μ.real (closedBall 0 r)) / Real.log r) ∘ Subtype.val) scaleZero _
    rw [← tendsto_map'_iff, scaleZero_map, hd]
    refine tendsto_log_div_log_of_bounds (m := fun r => μ.real (closedBall 0 r)) (by norm_num) (by norm_num)
      hρ (mul_pos hc₁ (pow_pos hρ 3)) (mul_pos hc₂ hρ) fun n r hr1 hr2 => ?_
    rw [map_measureReal_apply exampleIFS.measurable_natProj measurableSet_closedBall]
    constructor
    · have hr : 2 * (1 / 8 : ℝ) ^ (n + 3) ≤ r := by
        rw [pow_add] at hr1 ⊢; nlinarith [(show (0 : ℝ) < (1 / 8) ^ n by positivity)]
      exact (by ring : c₁ * ρ ^ 3 * ρ ^ n = c₁ * ρ ^ (n + 3)).trans_le
        ((hlow (n + 3)).trans (measureReal_mono (preimage_mono (closedBall_subset_closedBall hr))))
    · have hr : r < 29 / 32 * (1 / 8 : ℝ) ^ n := by
        rw [pow_add] at hr2; nlinarith [(show (0 : ℝ) < (1 / 8) ^ n by positivity)]
      exact (hup n r hr).trans_eq (by ring)
  · let r (n : ℕ) : ℝ := 3 * (1 / 8 : ℝ) ^ n
    have hr_lim : Tendsto r atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (by simpa [r] using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 8 : ℝ)) (by norm_num) (by norm_num)).const_mul 3)
        (Eventually.of_forall fun n => show 0 < r n by dsimp [r]; positivity)
    let g (n : ℕ) : ℝ := q * (Real.log c₁ / n + Real.log ρ) / (Real.log 3 / n + Real.log (1 / 8))
    have hg : Tendsto g atTop (𝓝 (q * (s - 1 / 3))) := by
      have h8ne : Real.log (1 / 8 : ℝ) ≠ 0 := (Real.log_neg (by norm_num) (by norm_num)).ne
      have h1 := ((tendsto_const_div_atTop_nhds_zero_nat (Real.log c₁)).add_const (Real.log ρ)).const_mul q
      have h2 := (tendsto_const_div_atTop_nhds_zero_nat (Real.log 3)).add_const (Real.log (1 / 8))
      convert h1.div h2 (by simpa using h8ne) using 2
      rw [hd]; ring
    have hle : ∀ᶠ n in atTop, lqRatio μ q (r n) ≤ g n := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hr0 : 0 < r n := by dsimp [r]; positivity
      have hr1 : r n < 1 := by
        dsimp [r]; linarith [pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num) hn]
      obtain ⟨hsum_z, -, -⟩ := lq_summable_and_bounds μ hq.le hr0
      have hmI : c₁ * ρ ^ n ≤ μ.real (Ico 0 (r n)) := by
        rw [map_measureReal_apply exampleIFS.measurable_natProj measurableSet_Ico]
        exact (hsum n).1.trans <| measureReal_mono fun ω hω =>
          ⟨(exampleIFS.attractor_subset_I ⟨ω, rfl⟩).1, (ld_natProj_le hω).trans_lt
            (by dsimp [r]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 8) n])⟩
      have hcρ : 0 < c₁ * ρ ^ n := mul_pos hc₁ (pow_pos hρ n)
      have hlog : q * Real.log (c₁ * ρ ^ n) ≤ Real.log (lqSum μ q (r n)) := by
        rw [← Real.log_rpow hcρ]
        exact Real.log_le_log (Real.rpow_pos_of_pos hcρ q)
          ((Real.rpow_le_rpow hcρ.le hmI (by linarith)).trans (by simpa [lqSum] using hsum_z.le_tsum (0 : ℤ) fun _ _ => by positivity))
      have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      refine (div_le_div_of_nonpos_of_le (Real.log_neg hr0 hr1).le hlog).trans_eq ?_
      dsimp [g, r]
      rw [Real.log_mul hc₁.ne' (pow_pos hρ n).ne', Real.log_pow,
        Real.log_mul (by norm_num) (pow_pos (by norm_num) n).ne', Real.log_pow]
      field_simp
    have hbdd : IsBoundedUnder (· ≥ ·) (𝓝[>] 0) (lqRatio μ q) :=
      isBoundedUnder_of_eventually_ge (Filter.eventually_of_mem (Ioo_mem_nhdsGT one_pos) fun x hx => by
        obtain ⟨-, s0, s1⟩ := lq_summable_and_bounds μ hq.le hx.1
        exact div_nonneg_of_nonpos (Real.log_nonpos s0 s1) (Real.log_neg hx.1 hx.2).le)
    have hliminf : liminf (lqRatio μ q) (𝓝[>] 0) ≤ q * (s - 1 / 3) :=
      le_of_forall_pos_le_add fun δ hδ => liminf_le_of_frequently_le
        (hr_lim.frequently (((hg.eventually (gt_mem_nhds (lt_add_of_pos_right _ hδ))).and hle).frequently.mono
          fun _ ⟨h1, h2⟩ => h2.trans h1.le)) hbdd
    have heq : Challenge.lqDim μ q hq0 = liminf (lqRatio μ q) (𝓝[>] 0) / (q - 1) := by
      rw [Challenge.lqDim, divide, ← scaleZero_map]; rfl
    rw [heq, divide]
    exact (div_le_div_of_nonneg_right hliminf (sub_pos.2 hq).le).trans_eq (by ring)

end AnalyticESC
