module

public import AnalyticESC.Dimension.Rapaport

@[expose] public section

/-!
# The natural measure

From Bowen's theorem (`BowenGibbsStatement`), the potential `s log|f'_{ω₀}(π(σω))|` has a Gibbs
measure `ν`. When `s = s(Φ)`, `ν` has the Gibbs property `ν[w] ≍ ‖f_w'‖^s` of `IFS.IsGibbs`, so the
results of `Main.LocalDimension` apply to the natural measure `ν ∘ π⁻¹`.
-/

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-! ### Distortion -/

include Φ in
private theorem nm_mem_closure {x : ℝ} (hx : x ∈ I) : (x : ℂ) ∈ closure (nbhd ε) :=
  subset_closure (ofReal_mem_nbhd Φ.ε_pos hx)

/-- `|log A - log B| ≤ |A - B| / c` for `A, B ≥ c > 0`. -/
private theorem nm_abs_log_sub_log_le {A B c : ℝ} (hc : 0 < c) (hA : c ≤ A) (hB : c ≤ B) :
    |Real.log A - Real.log B| ≤ |A - B| / c := by
  have key {X Y : ℝ} (hX : c ≤ X) (hY : c ≤ Y) : Real.log X - Real.log Y ≤ |X - Y| / c := by
    have hX0 := hc.trans_le hX
    have hY0 := hc.trans_le hY
    rw [← Real.log_div hX0.ne' hY0.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos hX0 hY0)).trans ?_
    rw [div_sub_one hY0.ne']
    exact (div_le_div_of_nonneg_right (le_abs_self _) hY0.le).trans
      (div_le_div_of_nonneg_left (abs_nonneg _) hc hY)
  exact abs_sub_le_iff.2 ⟨key hA hB, (key hB hA).trans_eq (by rw [abs_sub_comm])⟩

/-- `log |f_i'|` is Lipschitz on `I`, uniformly in `i`: `|f_i''| ≤ M` on `B_ε` and
`|f_i'| ≥ c_min`. -/
private theorem nm_exists_lip (hN : 0 < N) :
    ∃ L, 0 ≤ L ∧ ∀ i, ∀ a ∈ I, ∀ b ∈ I,
      |Real.log ‖deriv (Φ.f i) a‖ - Real.log ‖deriv (Φ.f i) b‖| ≤ L * |a - b| := by
  obtain ⟨M, hM0, hM⟩ := Φ.exists_nonlin_bound
  have hcmin := Φ.cmin_pos hN
  refine ⟨M / Φ.cmin, div_nonneg hM0 hcmin.le, fun i a ha b hb => ?_⟩
  have hmvt := Φ.norm_deriv_f_sub_le (hM i) ha hb
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hmvt
  refine (nm_abs_log_sub_log_le hcmin (Φ.cmin_le_norm_deriv i (Φ.nm_mem_closure ha))
    (Φ.cmin_le_norm_deriv i (Φ.nm_mem_closure hb))).trans ?_
  exact (div_le_div_of_nonneg_right ((abs_norm_sub_norm_le _ _).trans hmvt) hcmin.le).trans_eq
    (div_mul_eq_mul_div _ _ _).symm

/-- Bounded distortion along a word:
`|log |f_w'(y)| - log |f_w'(y')|| ≤ L ∑_{k < |w|} c_max^k` for `y, y' ∈ I`. -/
private theorem nm_log_deriv_comp_sub_le {L : ℝ}
    (hL : ∀ i, ∀ a ∈ I, ∀ b ∈ I,
      |Real.log ‖deriv (Φ.f i) a‖ - Real.log ‖deriv (Φ.f i) b‖| ≤ L * |a - b|)
    (hL0 : 0 ≤ L) (w : List (Fin N)) {y y' : ℝ} (hy : y ∈ I) (hy' : y' ∈ I) :
    |Real.log ‖deriv (Φ.comp w) y‖ - Real.log ‖deriv (Φ.comp w) y'‖| ≤
      L * ∑ k ∈ Finset.range w.length, Φ.cmax ^ k := by
  induction w with
  | nil => simp
  | cons i v ih =>
    have hne {x : ℝ} (hx : x ∈ I) : ‖deriv (Φ.comp v) x‖ ≠ 0 :=
      norm_ne_zero_iff.2 (Φ.deriv_comp_ne_zero v (Φ.nm_mem_closure hx))
    have hne' {x : ℝ} (hx : x ∈ I) : ‖deriv (Φ.f i) ((Φ.comp v x).re : ℂ)‖ ≠ 0 :=
      norm_ne_zero_iff.2 ((Φ.inClass i).deriv_ne_zero _
        (Φ.nm_mem_closure (Φ.re_comp_mem_I v hx)))
    rw [Φ.deriv_comp_cons i v (Φ.nm_mem_closure hy), Φ.deriv_comp_cons i v (Φ.nm_mem_closure hy'),
      norm_mul, norm_mul, Φ.comp_ofReal v hy, Φ.comp_ofReal v hy', Real.log_mul (hne' hy) (hne hy),
      Real.log_mul (hne' hy') (hne hy'), List.length_cons, Finset.sum_range_succ, add_sub_add_comm]
    have h1 := (hL i _ (Φ.re_comp_mem_I v hy) _ (Φ.re_comp_mem_I v hy')).trans
      (mul_le_mul_of_nonneg_left (Φ.abs_re_comp_sub_le v hy hy') hL0)
    exact (abs_add_le _ _).trans ((add_le_add h1 ih).trans_eq (by ring))

/-- Bounded distortion: `log ‖f_w'‖` and `log |f_w'(y)|` differ by at most a constant, for all
finite words `w` and `y ∈ I`. -/
private theorem nm_exists_distortion (hN : 0 < N) :
    ∃ Δ, 0 ≤ Δ ∧ ∀ (w : List (Fin N)) {y : ℝ}, y ∈ I →
      |Real.log (Φ.supDeriv w) - Real.log ‖deriv (Φ.comp w) y‖| ≤ Δ := by
  obtain ⟨L, hL0, hL⟩ := Φ.nm_exists_lip hN
  have hc1 : 0 < 1 - Φ.cmax := sub_pos.2 Φ.cmax_lt_one
  refine ⟨L / (1 - Φ.cmax), div_nonneg hL0 hc1.le, fun w y hy => ?_⟩
  have hpos {x : ℝ} (hx : x ∈ I) : 0 < ‖deriv (Φ.comp w) x‖ :=
    norm_pos_iff.2 (Φ.deriv_comp_ne_zero w (Φ.nm_mem_closure hx))
  have hgeom : ∑ k ∈ Finset.range w.length, Φ.cmax ^ k ≤ 1 / (1 - Φ.cmax) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := w.length) Φ.cmax_nonneg Φ.cmax_lt_one
    rwa [← Finset.range_eq_Ico, pow_zero] at this
  have hdist {x : ℝ} (hx : x ∈ I) :
      Real.log ‖deriv (Φ.comp w) x‖ ≤ Real.log ‖deriv (Φ.comp w) y‖ + L / (1 - Φ.cmax) := by
    have h := (le_abs_self _).trans (Φ.nm_log_deriv_comp_sub_le hL hL0 w hx hy)
    have h' := (mul_le_mul_of_nonneg_left hgeom hL0).trans_eq (mul_one_div L _)
    linarith
  have hle : Φ.supDeriv w ≤ Real.exp (L / (1 - Φ.cmax)) * ‖deriv (Φ.comp w) y‖ := by
    have : Nonempty I := ⟨⟨0, le_rfl, zero_le_one⟩⟩
    refine ciSup_le fun x => ?_
    rw [← Real.exp_log (hpos x.2), ← Real.exp_log (hpos hy), ← Real.exp_add, add_comm]
    exact Real.exp_le_exp.2 (hdist x.2)
  have h1 := Real.log_le_log (hpos hy) (Φ.norm_deriv_le_supDeriv w hy)
  have h2 := Real.log_le_log (Φ.supDeriv_pos hN w) hle
  rw [Real.log_mul (Real.exp_pos _).ne' (hpos hy).ne', Real.log_exp] at h2
  rw [abs_le]
  constructor <;> linarith

/-! ### The natural projection and Birkhoff sums -/

/-- The Birkhoff sum of the potential: `∑_{k<m} φ_s(σ^k x) = s log |f_w'(π(σ^m x))|` with
`w = x₀ ⋯ x_{m-1}`. -/
private theorem nm_birkhoff (s : ℝ) (m : ℕ) (x : ℕ → Fin N) :
    ∑ k ∈ Finset.range m, Φ.potential s (fun i => x (i + k)) =
      s * Real.log ‖deriv (Φ.comp (List.ofFn fun j : Fin m => x j))
        (Φ.natProj fun i => x (i + m))‖ := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    have hz := Φ.nm_mem_closure (Φ.attractor_subset_I ⟨fun i => x (i + m + 1), rfl⟩)
    simp only [Finset.sum_range_succ', List.ofFn_succ, Fin.val_zero, Fin.val_succ, ← add_assoc]
    rw [ih (fun j => x (j + 1)),
      Φ.deriv_comp_cons _ _ hz, Φ.comp_ofReal _ (Φ.attractor_subset_I ⟨_, rfl⟩),
      ← Φ.natProj_eq_comp_prefix (fun i => x (i + 1)) m, norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 ((Φ.inClass _).deriv_ne_zero _
        (Φ.nm_mem_closure (Φ.attractor_subset_I ⟨_, rfl⟩))))
        (norm_ne_zero_iff.2 (Φ.deriv_comp_ne_zero _ hz))]
    change _ + Φ.potential s x = _
    rw [potential, Challenge.potential]
    ring

/-- Bowen's theorem gives a Gibbs measure for the potential `s log|f'_{ω₀}(π(σω))|`. -/
theorem exists_isGibbsMeasure (hB : BowenGibbsStatement) (hN : 0 < N) (s : ℝ) :
    ∃ ν : Measure (ℕ → Fin N), IsProbabilityMeasure ν ∧ IsGibbsMeasure (Φ.potential s) ν := by
  obtain ⟨L, hL0, hL⟩ := Φ.nm_exists_lip hN
  have hcmin := Φ.cmin_pos hN
  have hcmax := Φ.cmax_pos hN
  have hlog : Real.log Φ.cmin ≤ Real.log Φ.cmax := Real.log_le_log hcmin (Φ.cmin_le_cmax hN)
  have hK : 0 ≤ L / Φ.cmax + (Real.log Φ.cmax - Real.log Φ.cmin) :=
    add_nonneg (div_nonneg hL0 hcmax.le) (sub_nonneg.2 hlog)
  set b := |s| * (L / Φ.cmax + (Real.log Φ.cmax - Real.log Φ.cmin)) + 1 with hb_def
  have hb : 0 < b := add_pos_of_nonneg_of_pos (mul_nonneg (abs_nonneg s) hK) one_pos
  refine hB hN (Φ.potential s) hb hcmax Φ.cmax_lt_one fun k x y hxy => ?_
  simp only [potential, Challenge.potential]
  rw [← mul_sub, abs_mul]
  have hx := Φ.attractor_subset_I ⟨fun i => x (i + 1), rfl⟩
  have hy := Φ.attractor_subset_I ⟨fun i => y (i + 1), rfl⟩
  rcases k with _ | k
  · have hbd (i : Fin N) {t : ℝ} (ht : t ∈ I) :
        Real.log Φ.cmin ≤ Real.log ‖deriv (Φ.f i) t‖ ∧
        Real.log ‖deriv (Φ.f i) t‖ ≤ Real.log Φ.cmax :=
      ⟨Real.log_le_log hcmin (Φ.cmin_le_norm_deriv i (Φ.nm_mem_closure ht)),
        Real.log_le_log (hcmin.trans_le (Φ.cmin_le_norm_deriv i (Φ.nm_mem_closure ht)))
          (Φ.norm_deriv_le_cmax i (Φ.nm_mem_closure ht))⟩
    obtain ⟨h1, h2⟩ := hbd (x 0) hx
    obtain ⟨h3, h4⟩ := hbd (y 0) hy
    have hd : |Real.log ‖deriv (Φ.f (x 0)) (Φ.natProj fun i => x (i + 1))‖ -
        Real.log ‖deriv (Φ.f (y 0)) (Φ.natProj fun i => y (i + 1))‖| ≤
        Real.log Φ.cmax - Real.log Φ.cmin := abs_le.2 ⟨by linarith, by linarith⟩
    rw [pow_zero, mul_one, hb_def]
    nlinarith [mul_le_mul_of_nonneg_left hd (abs_nonneg s), div_nonneg hL0 hcmax.le, abs_nonneg s]
  · have h0 : x 0 = y 0 := hxy 0 (Nat.succ_pos k)
    have hu : (List.ofFn fun j : Fin k => x (j + 1)) = List.ofFn fun j : Fin k => y (j + 1) :=
      congrArg List.ofFn (funext fun j => hxy _ (by omega))
    have hdist : |Φ.natProj (fun i => x (i + 1)) - Φ.natProj (fun i => y (i + 1))| ≤
        Φ.cmax ^ k := by
      rw [Φ.natProj_eq_comp_prefix (fun i => x (i + 1)) k,
        Φ.natProj_eq_comp_prefix (fun i => y (i + 1)) k, ← hu]
      exact (Φ.abs_re_comp_sub_le _ (Φ.attractor_subset_I ⟨_, rfl⟩)
        (Φ.attractor_subset_I ⟨_, rfl⟩)).trans_eq (by simp)
    have hd := (hL (x 0) _ hx _ hy).trans (mul_le_mul_of_nonneg_left hdist hL0)
    rw [← h0]
    have hb' : |s| * (L / Φ.cmax) ≤ b := by rw [hb_def]; nlinarith [abs_nonneg s]
    calc |s| * |Real.log ‖deriv (Φ.f (x 0)) (Φ.natProj fun i => x (i + 1))‖ -
          Real.log ‖deriv (Φ.f (x 0)) (Φ.natProj fun i => y (i + 1))‖|
        ≤ |s| * (L * Φ.cmax ^ k) := mul_le_mul_of_nonneg_left hd (abs_nonneg s)
      _ = |s| * (L / Φ.cmax) * Φ.cmax ^ (k + 1) := by rw [pow_succ]; field_simp
      _ ≤ b * Φ.cmax ^ (k + 1) := mul_le_mul_of_nonneg_right hb' (pow_nonneg hcmax.le _)

/-- A Gibbs measure of the potential `s log|f'_{ω₀}(π(σω))|`, for the zero `s` of the pressure, has
the Gibbs property `C⁻¹ ‖f_w'‖^s ≤ ν[w] ≤ C ‖f_w'‖^s`. -/
theorem isGibbs_of_isGibbsMeasure (hN : 0 < N) {s : ℝ}
    (hs : Tendsto (fun n : ℕ => Real.log (Φ.pressureSum s n) / n) atTop (𝓝 0))
    {ν : Measure (ℕ → Fin N)} [IsProbabilityMeasure ν] (hν : IsGibbsMeasure (Φ.potential s) ν) :
    Φ.IsGibbs s ν := by
  obtain ⟨c₁, hc₁, c₂, hc₂, P, hG⟩ := hν
  obtain ⟨Δ, hΔ0, hΔ⟩ := Φ.nm_exists_distortion hN
  set A := |s| * Δ
  set K₁ := c₁ * Real.exp (-A) with hK₁_def
  set K₂ := c₂ * Real.exp A with hK₂_def
  have hK₁ : 0 < K₁ := mul_pos hc₁ (Real.exp_pos _)
  have hK₂ : 0 < K₂ := mul_pos hc₂ (Real.exp_pos _)
  have key (w : List (Fin N)) :
      K₁ * Real.exp (-P * w.length) * Φ.supDeriv w ^ s ≤ ν.real (wordCylinder w) ∧
        ν.real (wordCylinder w) ≤ K₂ * Real.exp (-P * w.length) * Φ.supDeriv w ^ s := by
    set x : ℕ → Fin N := fun i => if h : i < w.length then w[i] else ⟨0, hN⟩
    obtain ⟨h1, h2⟩ := hG x w.length
    have hcyl : {y | ∀ i < w.length, y i = x i} = wordCylinder w :=
      Set.ext fun y => by simp +contextual [wordCylinder, x, Fin.forall_iff]
    have hofFn : (List.ofFn fun j : Fin w.length => x j) = w := by simp [x]
    rw [hcyl, Φ.nm_birkhoff, hofFn] at h1 h2
    have hπ : Φ.natProj (fun i => x (i + w.length)) ∈ I := Φ.attractor_subset_I ⟨_, rfl⟩
    have hd : |s * Real.log (Φ.supDeriv w) -
        s * Real.log ‖deriv (Φ.comp w) (Φ.natProj fun i => x (i + w.length))‖| ≤ A := by
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hΔ w hπ) (abs_nonneg s)
    rw [abs_le] at hd
    have e (c B : ℝ) : c * Real.exp B * Real.exp (-P * w.length) * Φ.supDeriv w ^ s =
        c * Real.exp (-P * w.length + (s * Real.log (Φ.supDeriv w) + B)) := by
      rw [Real.rpow_def_of_pos (Φ.supDeriv_pos hN w), mul_comm (Real.log _),
        mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
      congr 2; ring
    rw [hK₁_def, hK₂_def, e, e]
    exact ⟨(mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hc₁.le).trans h1,
      h2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hc₂.le)⟩
  have hps := Φ.pressureSum_pos hN s
  have hsum (m : ℕ) : K₁ * Real.exp (-P * m) * Φ.pressureSum s m ≤ 1 ∧
      1 ≤ K₂ * Real.exp (-P * m) * Φ.pressureSum s m := by
    rw [← sum_measureReal_wordCylinder_univ ν m, pressureSum, Finset.mul_sum, Finset.mul_sum]
    exact ⟨Finset.sum_le_sum fun v _ => by simpa using (key (List.ofFn v)).1,
      Finset.sum_le_sum fun v _ => by simpa using (key (List.ofFn v)).2⟩
  have hlog (m : ℕ) : -Real.log K₂ ≤ Real.log (Φ.pressureSum s m) - P * m ∧
      Real.log (Φ.pressureSum s m) - P * m ≤ -Real.log K₁ := by
    obtain ⟨h1, h2⟩ := hsum m
    have hl {K : ℝ} (hK : 0 < K) : Real.log (K * Real.exp (-P * m) * Φ.pressureSum s m) =
        Real.log K + -P * m + Real.log (Φ.pressureSum s m) := by
      rw [Real.log_mul (mul_pos hK (Real.exp_pos _)).ne' (hps m).ne',
        Real.log_mul hK.ne' (Real.exp_pos _).ne', Real.log_exp]
    have l1 := Real.log_le_log (mul_pos (mul_pos hK₁ (Real.exp_pos _)) (hps m)) h1
    have l2 := Real.log_le_log one_pos h2
    rw [hl hK₁, Real.log_one] at l1
    rw [hl hK₂, Real.log_one] at l2
    constructor <;> linarith
  have hlim : Tendsto (fun n : ℕ => Real.log (Φ.pressureSum s n) / n) atTop (𝓝 P) := by
    have hc (c : ℝ) : Tendsto (fun n : ℕ => P + c / n) atTop (𝓝 P) := by
      simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat c)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hc (-Real.log K₂)) (hc (-Real.log K₁))
      ((eventually_ge_atTop 1).mono fun n hn => ?_) ((eventually_ge_atTop 1).mono fun n hn => ?_) <;>
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [add_div' _ _ _ hn'.ne', div_le_div_iff_of_pos_right hn']
      linarith [hlog n]
  have hP : P = 0 := tendsto_nhds_unique hlim hs
  refine ⟨max K₂ K₁⁻¹, lt_max_of_lt_left hK₂, fun w => ?_⟩
  obtain ⟨h1, h2⟩ := key w
  rw [hP, neg_zero, zero_mul, Real.exp_zero, mul_one] at h1 h2
  have hw := Real.rpow_nonneg (Φ.supDeriv_pos hN w).le s
  exact ⟨(mul_le_mul_of_nonneg_right (inv_le_of_inv_le₀ hK₁ (le_max_right _ _)) hw).trans h1,
    h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hw)⟩

end IFS

/-- The natural measure of the polynomial example in Section 1.2.2, from Bowen's theorem: the pressure of the example has
a unique zero `s = s(Φ)`, the potential `s log|f'_{ω₀}(π(σω))|` has a Gibbs measure, and for every
such Gibbs measure `ν` the natural measure `ν ∘ π⁻¹` has local dimension `s(Φ) - 1/3` at `0`. -/
theorem example_localDim_of_bowen (hB : BowenGibbsStatement) :
    ∃ s : ℝ,
      (∀ t, Tendsto (fun n : ℕ => Real.log (exampleIFS.pressureSum t n) / n) atTop (𝓝 0) ↔
        t = s) ∧
      (∃ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν ∧
        IsGibbsMeasure (exampleIFS.potential s) ν) ∧
      ∀ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν →
        IsGibbsMeasure (exampleIFS.potential s) ν →
        Tendsto (fun r => Real.log ((ν.map exampleIFS.natProj).real (closedBall 0 r)) / Real.log r)
          (𝓝[>] 0) (𝓝 (s - 1 / 3)) := by
  obtain ⟨s, -, hs⟩ := exampleIFS.exists_pressure_zero (by norm_num)
  refine ⟨s, hs, exampleIFS.exists_isGibbsMeasure hB (by norm_num) s, fun ν hν hG => ?_⟩
  exact example_localDim (exampleIFS.isGibbs_of_isGibbsMeasure (by norm_num) ((hs s).2 rfl) hG)

end AnalyticESC
