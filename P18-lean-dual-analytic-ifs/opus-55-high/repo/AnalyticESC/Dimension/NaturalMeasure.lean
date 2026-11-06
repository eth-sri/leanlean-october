module

public import AnalyticESC.Dimension.Pressure

public section

set_option hygiene false
local notation "𝔟" => Φ.ofReal_mem_cl hx
local notation "𝔞" => (Φ.inClass i).deriv_ne_zero _ (Φ.ofReal_mem_cl (Φ.re_comp_mem_I v hx))
local notation "𝕳" => j + k + 1
local notation "𝕲" => Φ.potential s
local notation "𝕱" => subset_closure hz
local notation "𝕰" => Real.rpow_nonneg (hpos w).le s
local notation "𝔈" => abs_nonneg s

local notation "𝔷" => j + 1

local notation "𝔶" => i + 1

local notation "𝔵" => Φ.attractor_subset_I ⟨_, rfl⟩

/-!
# The natural measure

From Bowen's theorem (`BowenGibbsStatement`), the potential `s log|f'_{ω₀}(π(σω))|` has a Gibbs
measure `ν`. When `s = s(Φ)`, `ν` has the Gibbs property `ν[w] ≍ ‖f_w'‖^s` of `IFS.IsGibbs`, so the
results of `Main.LocalDimension` apply to the natural measure `ν ∘ π⁻¹`.
-/

namespace AnalyticESC

open Metric Filter Topology MeasureTheory

namespace IFS

variable (Φ : IFS N ε) (hN : 0 < N)

/-! ### Cylinders -/

/-- The cylinder `[w]` is the set of sequences that agree with `w` in the first `|w|` places. -/
theorem nm_wordCylinder_eq w :
    wordCylinder w = {y | ∀ i < w.length, y i = w.getD i ⟨0, hN⟩} := by
  ext y
  exact ⟨fun h i hi => by simp [h ⟨i, hi⟩, hi], fun h k => by simp_all⟩

theorem nm_ofFn_getD (w : 𝔚 N) :
    (List.ofFn fun j : Fin w.length => w.getD j ⟨0, hN⟩) = w := by
  simp

/-! ### Distortion -/

/-- `|log A - log B| ≤ |A - B| / c` for `A, B ≥ c > 0`. -/
theorem nm_abs_log_sub_log_le (hc : 0 < c) (hA : c ≤ A) (hB : c ≤ B) :
    |Real.log A - Real.log B| ≤ |A - B| / c := by
  have key : ∀ {X Y : ℝ}, c ≤ X → c ≤ Y → Real.log X - Real.log Y ≤ |X - Y| / c := fun hX hY => by
    have := Real.log_le_sub_one_of_pos (div_pos (hc.trans_le hX) (hc.trans_le hY))
    rw [Real.log_div (hc.trans_le hX).ne' (hc.trans_le hY).ne', div_sub_one (hc.trans_le hY).ne'] at this
    exact this.trans (div_le_div₀ (abs_nonneg _) (le_abs_self _) hc hY)
  grind

/-- `log |f_i'|` is Lipschitz on `I`, uniformly in `i`: `|f_i''| ≤ M` on `B_ε` and
`|f_i'| ≥ c_min`. -/
theorem nm_exists_lip (hN : 0 < N) :
    ∃ L, 0 ≤ L ∧ ∀ i, ∀ a ∈ I, ∀ b ∈ I,
      |Real.log ‖𝔡 Φ i a‖ - Real.log ‖𝔡 Φ i b‖| ≤ L * |a - b| := by
  obtain ⟨M, hM0, hM⟩ := Φ.exists_nonlin_bound
  have hcmin := Φ.cmin_pos hN
  refine ⟨M / Φ.cmin, div_nonneg hM0 hcmin.le, fun i a ha b hb => ?_⟩
  have hmvt := (convex_nbhd ε).norm_image_sub_le_of_norm_deriv_le (fun z hz =>
    ((Φ.differentiableOn_f i).deriv isOpen_nbhd z (nbhd_subset_two hz)).differentiableAt
      (isOpen_nbhd.mem_nhds (nbhd_subset_two hz))) (fun z hz => show _ ≤ M by
    have h := hM i z 𝕱
    rw [nonlin, norm_div, div_le_iff₀ (norm_pos_iff.2 ((Φ.inClass i).deriv_ne_zero z
      𝕱))] at h
    nlinarith [(Φ.inClass i).norm_deriv_lt_one z 𝕱])
    (ofReal_mem_nbhd Φ.ε_pos hb) (ofReal_mem_nbhd Φ.ε_pos ha)
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hmvt
  rw [div_mul_eq_mul_div]
  exact (nm_abs_log_sub_log_le hcmin (Φ.cmin_le_norm_deriv i (Φ.ofReal_mem_cl ha))
    (Φ.cmin_le_norm_deriv i (Φ.ofReal_mem_cl hb))).trans
    (div_le_div_of_nonneg_right ((abs_norm_sub_norm_le _ _).trans hmvt) hcmin.le)

/-- Bounded distortion along a word:
`|log |f_w'(y)| - log |f_w'(y')|| ≤ L ∑_{k < |w|} c_max^k` for `y, y' ∈ I`. -/
theorem nm_log_deriv_comp_sub_le
    (hL : ∀ i, ∀ a ∈ I, ∀ b ∈ I,
      |Real.log ‖𝔡 Φ i a‖ - Real.log ‖𝔡 Φ i b‖| ≤ L * |a - b|)
    (hL0 : 0 ≤ L) w (hy : y ∈ I) (hy' : y' ∈ I) :
    |Real.log ‖𝔡ᶜ Φ w y‖ - Real.log ‖𝔡ᶜ Φ w y'‖| ≤
      L * ∑ k ∈ Finset.range w.length, Φ.cmax ^ k := by
  induction w with
  | nil => simp
  | cons i v ih =>
    rw [Φ.deriv_comp_cons i v (Φ.ofReal_mem_cl hy), Φ.deriv_comp_cons i v (Φ.ofReal_mem_cl hy'), norm_mul, norm_mul,
      Φ.comp_ofReal v hy, Φ.comp_ofReal v hy', Real.log_mul ((fun hx => norm_ne_zero_iff.2 𝔞) hy) ((fun hx => norm_ne_zero_iff.2 (Φ.deriv_comp_ne_zero v 𝔟)) hy),
      Real.log_mul ((fun hx => norm_ne_zero_iff.2 𝔞) hy') ((fun hx => norm_ne_zero_iff.2 (Φ.deriv_comp_ne_zero v 𝔟)) hy'), List.length_cons, Finset.sum_range_succ,
      add_sub_add_comm]
    refine (abs_add_le _ _).trans ?_
    linarith [(hL i _ (Φ.re_comp_mem_I v hy) _ (Φ.re_comp_mem_I v hy')).trans
        (mul_le_mul_of_nonneg_left (Φ.abs_re_comp_sub_le v hy hy') hL0)]

/-- Bounded distortion: `log ‖f_w'‖` and `log |f_w'(y)|` differ by at most a constant, for all
finite words `w` and `y ∈ I`. -/
theorem nm_exists_distortion (hN : 0 < N) :
    ∃ Δ, ∀ (w : 𝔚 N) {y : ℝ}, y ∈ I →
      |Real.log (Φ.supDeriv w) - Real.log ‖𝔡ᶜ Φ w y‖| ≤ Δ := by
  obtain ⟨L, hL0, hL⟩ := Φ.nm_exists_lip hN
  refine ⟨L / (1 - Φ.cmax), fun w y hy => ?_⟩
  have hg := mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one (m := 0) (n := w.length)
    Φ.cmax_nonneg Φ.cmax_lt_one) hL0
  rw [← Finset.range_eq_Ico, pow_zero, mul_one_div] at hg
  have h2 := (Real.log_le_iff_le_exp (Φ.supDeriv_pos hN w)).2 (ciSup_le fun x =>
    (Real.log_le_iff_le_exp ((fun hx => norm_pos_iff.2 (Φ.deriv_comp_ne_zero w 𝔟)) x.2)).1 (by
      linarith [(abs_le.1 (Φ.nm_log_deriv_comp_sub_le hL hL0 w x.2 hy)).2]) :
    Φ.supDeriv w ≤ Real.exp (L / (1 - Φ.cmax) + Real.log ‖𝔡ᶜ Φ w y‖))
  have h1 := Real.log_le_log ((fun hx => norm_pos_iff.2 (Φ.deriv_comp_ne_zero w 𝔟)) hy) (Φ.norm_deriv_le_supDeriv w hy)
  grind

/-! ### The natural projection and Birkhoff sums -/

/-- `f_{ω₁ ⋯ ω_k}(π(σ^k ω)) = π(ω)`, as complex numbers. -/
theorem nm_comp_natProj ω k :
    Φ.comp (List.ofFn fun j : Fin k => ω j) (Φ.natProj fun j => ω (j + k)) = Φ.natProj ω := by
  rw [Φ.comp_ofReal _ 𝔵, ← Φ.natProj_eq_comp_prefix]

/-- The Birkhoff sum of the potential: `∑_{k<m} φ_s(σ^k x) = s log |f_w'(π(σ^m x))|` with
`w = x₀ ⋯ x_{m-1}`. -/
theorem nm_birkhoff s m (x : 𝔖 N) :
    ∑ k ∈ Finset.range m, Φ.potential s (fun i => x (i + k)) =
      s * Real.log ‖𝔡ᶜ Φ (List.ofFn fun j : Fin m => x j)
        (Φ.natProj fun i => x (i + m))‖ := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    have hz := Φ.ofReal_mem_cl (Φ.attractor_subset_I ⟨fun i => x (i + (m + 1)), rfl⟩)
    have := ih (fun j => x 𝔷)
    have hc := Φ.nm_comp_natProj (fun i => x 𝔶) m
    simp only [add_assoc, List.ofFn_succ, Fin.val_succ, Fin.val_zero] at this hc ⊢
    rw [Finset.sum_range_succ', this, Φ.deriv_comp_cons _ _ hz, hc, norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 ((Φ.inClass _).deriv_ne_zero _
        (Φ.ofReal_mem_cl 𝔵)))
        (norm_ne_zero_iff.2 (Φ.deriv_comp_ne_zero _ hz)), potential]
    ring

/-- Bowen's theorem gives a Gibbs measure for the potential `s log|f'_{ω₀}(π(σω))|`. -/
theorem exists_isGibbsMeasure (hB : BowenGibbsStatement) (hN : 0 < N) s :
    ∃ ν, IsProbabilityMeasure ν ∧ IsGibbsMeasure 𝕲 ν := by
  obtain ⟨L, hL0, hL⟩ := Φ.nm_exists_lip hN
  have hcmin := Φ.cmin_pos hN
  have hcmax := Φ.cmax_pos hN
  have h0 := mul_nonneg 𝔈 (div_nonneg hcmax.le hcmin.le)
  have h1 := mul_nonneg 𝔈 (div_nonneg hL0 hcmax.le)
  refine hB hN 𝕲 (b := |s| * (L / Φ.cmax + Φ.cmax / Φ.cmin) + 1) (by linarith)
    hcmax Φ.cmax_lt_one fun k x y hxy => ?_
  simp [potential]
  rw [← mul_sub, abs_mul]
  have hx := Φ.ofReal_mem_cl (Φ.attractor_subset_I ⟨fun i => x 𝔶, rfl⟩)
  have hy := Φ.ofReal_mem_cl (Φ.attractor_subset_I ⟨fun i => y 𝔶, rfl⟩)
  rcases k with _ | k
  · -- no common prefix: `|f_i'|` takes values in `[c_min, c_max]`
    nlinarith [mul_le_mul_of_nonneg_left ((nm_abs_log_sub_log_le hcmin
      (Φ.cmin_le_norm_deriv (x 0) hx) (Φ.cmin_le_norm_deriv (y 0) hy)).trans
      (div_le_div_of_nonneg_right (abs_sub_le_of_nonneg_of_le (norm_nonneg _)
        (Φ.norm_deriv_le_cmax _ hx) (norm_nonneg _) (Φ.norm_deriv_le_cmax _ hy)) hcmin.le))
      𝔈]
  · -- a common prefix of length `k + 1`: the two points lie in `f_u(I)`, `|u| = k`
    have hu : (List.ofFn fun j => x 𝔷) = List.ofFn fun j : Fin k => y 𝔷 :=
      List.ofFn_inj.2 (funext fun j => hxy _ (by omega))
    have := Φ.abs_re_comp_sub_le (List.ofFn fun j : Fin k => x 𝔷)
      (Φ.attractor_subset_I ⟨fun j => x 𝕳, rfl⟩)
      (Φ.attractor_subset_I ⟨fun j => y 𝕳, rfl⟩)
    rw [List.length_ofFn, ← Φ.natProj_eq_comp_prefix (fun i => x 𝔶), hu,
      ← Φ.natProj_eq_comp_prefix (fun i => y 𝔶)] at this
    have e : |s| * (L / Φ.cmax) * Φ.cmax ^ (k + 1) = |s| * (L * Φ.cmax ^ k) := by grind
    rw [← hxy 0 k.succ_pos]
    nlinarith [mul_le_mul_of_nonneg_left ((hL (x 0) _ 𝔵 _
      𝔵).trans (mul_le_mul_of_nonneg_left this hL0)) 𝔈, pow_nonneg hcmax.le (k + 1)]

/-- A Gibbs measure of the potential `s log|f'_{ω₀}(π(σω))|`, for the zero `s` of the pressure, has
the Gibbs property `C⁻¹ ‖f_w'‖^s ≤ ν[w] ≤ C ‖f_w'‖^s`. -/
theorem isGibbs_of_isGibbsMeasure (hN : 0 < N)
    (hs : Tendsto (fun n : ℕ => Real.log (Φ.pressureSum s n) / n) atTop (𝓝 0))
    [IsProbabilityMeasure ν] (hν : IsGibbsMeasure 𝕲 ν) :
    Φ.IsGibbs s ν := by
  obtain ⟨c₁, hc₁, c₂, hc₂, P, hG⟩ := hν
  obtain ⟨Δ, hΔ⟩ := Φ.nm_exists_distortion hN
  have hpos := Φ.supDeriv_pos hN
  -- `ν[w] ≍ exp(-P|w|) ‖f_w'‖^s`
  have key : ∀ w,
      Real.exp (Real.log c₁ - |s| * Δ - P * w.length) * Φ.supDeriv w ^ s ≤
        ν.real (wordCylinder w) ∧
      ν.real (wordCylinder w) ≤
        Real.exp (Real.log c₂ + |s| * Δ - P * w.length) * Φ.supDeriv w ^ s := fun w => by
    set x : 𝔖 N := fun i => w.getD i ⟨0, hN⟩
    obtain ⟨h1, h2⟩ := hG x w.length
    rw [← nm_wordCylinder_eq hN w, Φ.nm_birkhoff, nm_ofFn_getD hN w] at h1 h2
    rw [← Real.exp_log hc₁, ← Real.exp_add] at h1
    rw [← Real.exp_log hc₂, ← Real.exp_add] at h2
    have hd := mul_le_mul_of_nonneg_left (hΔ w (Φ.attractor_subset_I
      ⟨fun i => x (i + w.length), rfl⟩)) 𝔈
    rw [← abs_mul, mul_sub, abs_le] at hd
    rw [Real.rpow_def_of_pos (hpos w), ← Real.exp_add, ← Real.exp_add]
    exact ⟨h1.trans' (Real.exp_le_exp.2 (by linarith)), h2.trans (Real.exp_le_exp.2 (by linarith))⟩
  -- summing over the words of length `m`: `exp(-Pm) ∑_{|w| = m} ‖f_w'‖^s ≍ 1`
  have hsum : ∀ m, Real.log c₁ - |s| * Δ - P * m + Real.log (Φ.pressureSum s m) ≤ 0 ∧
      0 ≤ Real.log c₂ + |s| * Δ - P * m + Real.log (Φ.pressureSum s m) := fun m => by
    rw [← Real.exp_le_one_iff, ← Real.one_le_exp_iff, Real.exp_add, Real.exp_add,
      Real.exp_log (Φ.pressureSum_pos hN s m), ← sum_measureReal_wordCylinder_univ ν m,
      pressureSum]
    simp [Finset.mul_sum]
    exact ⟨Finset.sum_le_sum fun v _ => by grind,
      Finset.sum_le_sum fun v _ => by grind⟩
  -- hence `(1/m) log ∑_{|w| = m} ‖f_w'‖^s → P`, so `P = 0`
  have hc : ∀ c, Tendsto (fun n : ℕ => P + c / n) atTop (𝓝 P) := by
    intro c
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat c)
  obtain rfl : P = 0 := tendsto_nhds_unique (tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (hc (-Real.log c₂ - |s| * Δ)) (hc (|s| * Δ - Real.log c₁))
    (eventually_atTop.2 ⟨1, fun n hn => by
      rw [add_div' _ _ _ (Nat.cast_pos.2 hn).ne', div_le_div_iff_of_pos_right (Nat.cast_pos.2 hn)]
      linarith [hsum n]⟩)
    (eventually_atTop.2 ⟨1, fun n hn => by
      rw [add_div' _ _ _ (Nat.cast_pos.2 hn).ne', div_le_div_iff_of_pos_right (Nat.cast_pos.2 hn)]
      linarith [hsum n]⟩)) hs
  -- the Gibbs property
  refine ⟨Real.exp (|Real.log c₁| + |Real.log c₂| + |s| * Δ), Real.exp_pos _, fun w => ?_⟩
  rw [← Real.exp_neg]
  exact ⟨(key w).1.trans' (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by
      linarith [neg_abs_le (Real.log c₁), abs_nonneg (Real.log c₂)]))
      𝕰),
    (key w).2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by
      linarith [le_abs_self (Real.log c₂), abs_nonneg (Real.log c₁)]))
      𝕰)⟩

end IFS

/-- The natural measure of the polynomial example in Section 1.2.2, from Bowen's theorem: the pressure of the example has
a unique zero `s = s(Φ)`, the potential `s log|f'_{ω₀}(π(σω))|` has a Gibbs measure, and for every
such Gibbs measure `ν` the natural measure `ν ∘ π⁻¹` has local dimension `s(Φ) - 1/3` at `0`. -/
theorem example_localDim_of_bowen (hB : BowenGibbsStatement) :
    ∃ s,
      exampleIFS.PressureZero s ∧
      (∃ ν, IsProbabilityMeasure ν ∧
        IsGibbsMeasure (exampleIFS.potential s) ν) ∧
      ∀ ν, IsProbabilityMeasure ν →
        IsGibbsMeasure (exampleIFS.potential s) ν →
        Tendsto (fun r => Real.log ((ν.map exampleIFS.natProj).real (closedBall 0 r)) / Real.log r)
          (𝓝[>] 0) (𝓝 (s - 1 / 3)) := by
  obtain ⟨s, hs⟩ := exampleIFS.exists_pressure_zero (by norm_num)
  refine ⟨s, hs, exampleIFS.exists_isGibbsMeasure hB (by norm_num) s, fun ν hν hG => ?_⟩
  exact (example_localDim (exampleIFS.isGibbs_of_isGibbsMeasure (by norm_num) ((hs s).2 rfl)
    hG)).2

end AnalyticESC
