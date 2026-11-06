module

public import AnalyticESC.Dimension.NaturalMeasure
set_option hygiene false
local notation "𝕺" => sub_pos.2 hq
local notation "𝕹" => Ico 0 r
local notation "𝔛" => 1 - 1 / q

local notation "𝔙" => closedBall 0 r

local notation "𝔘" => q - 1

local notation "𝔒" => closedBall 0 (r / 2)


@[expose] public section

/-!
# The `L^q` dimension of the natural measure of the polynomial example

`L^q` dimensions of the polynomial example in Section 1.2.2: for `q > 1`, the `L^q` spectrum
`τ_μ(q) = liminf_{r → 0} log(∑_{k ∈ ℤ} μ([kr, (k+1)r))^q) / log r` and the `L^q` dimension
`D_μ(q) = τ_μ(q)/(q - 1)` of the natural measure `μ` of the example satisfy
`D_μ(q) ≤ q (s(Φ) - 1/3) / (q - 1)`, which is smaller than `s(Φ)` for `q > 3 s(Φ)`. The sum
contains the term `μ([0,r))^q ≥ μ(B(0,r/2))^q`, and `μ(B(0,r))` has local dimension `s(Φ) - 1/3`
at `0` (`example_localDim`). The bound is deduced by contradiction through the ball-mass
estimate of Shmerkin's Lemma 1.7, proved here in the form needed at `0`.
-/

namespace AnalyticESC

variable {d q r : ℝ}

open Set Metric Filter Topology MeasureTheory

local notation "𝔦" => Ico (k * r) ((k + 1) * r)
/-- The `L^q` sum `∑_{k ∈ ℤ} μ([kr, (k+1)r))^q` of `μ` at scale `r`. -/
noncomputable def lqSum (μ : Measure ℝ) (q r : ℝ) : ℝ :=
  ∑' k : ℤ, μ.real (𝔦) ^ q

/-- The quotient `log(∑_{k ∈ ℤ} μ([kr, (k+1)r))^q) / log r`, whose limit inferior as `r → 0` is the
`L^q` spectrum. -/
noncomputable def lqRatio (μ : Measure ℝ) (q r : ℝ) : ℝ := Real.log (lqSum μ q r) / Real.log r

/-- The `L^q` dimension `D_μ(q) = τ_μ(q)/(q - 1)` of Section 1.2.2, where
`τ_μ(q) = liminf_{r → 0} log(∑_{k ∈ ℤ} μ([kr, (k+1)r))^q) / log r` is the `L^q` spectrum. -/
noncomputable def lqDim (μ : Measure ℝ) (q : ℝ) : ℝ := liminf (lqRatio μ q) (𝓝[>] 0) / 𝔘

/-! ### `L^q` sums of a probability measure on `ℝ` -/

section
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (h0 : μ (Iio 0) = 0)
  (hpos : ∀ r > 0, 0 < μ.real 𝔙)

/-- The intervals `[kr, (k+1)r)`, `k ∈ ℤ`, partition `ℝ`, so their masses sum to `1`. -/
theorem lq_hasSum (hr : 0 < r) :
    HasSum (fun k : ℤ => μ.real (𝔦)) 1 := by
  have hU : ⋃ k : ℤ, 𝔦 = univ := by
    simpa using iUnion_Ico_zsmul hr
  have h := measure_iUnion (μ := μ) (by simpa using pairwise_disjoint_Ico_zsmul r) fun _ => measurableSet_Ico
  rw [hU, measure_univ] at h
  have hS := ENNReal.hasSum_toReal (h ▸ ENNReal.one_ne_top)
  rwa [← ENNReal.tsum_toReal_eq fun _ => measure_ne_top _ _, ← h, ENNReal.toReal_one] at hS

/-- For `q ≥ 1`, the `L^q` sum converges and lies in `[0, 1]`. -/
theorem lq_summable_and_bounds (hq : 1 ≤ q) (hr : 0 < r) :
    Summable (fun k : ℤ => μ.real (𝔦) ^ q) ∧ 0 ≤ lqSum μ q r ∧
      lqSum μ q r ≤ 1 := by
  have hS := lq_hasSum μ hr
  have hle : ∀ k : ℤ, μ.real (𝔦) ^ q ≤
      μ.real (𝔦) :=
    fun _ => Real.rpow_le_self_of_le_one measureReal_nonneg measureReal_le_one hq
  have hsum : Summable fun k : ℤ => μ.real (𝔦) ^ q :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hle hS.summable
  refine ⟨hsum, tsum_nonneg fun _ => by positivity, ?_⟩
  calc lqSum μ q r ≤ ∑' k : ℤ, μ.real (𝔦) :=
        hsum.tsum_le_tsum hle hS.summable
    _ = 1 := hS.tsum_eq

/-- For `q ≥ 1` and `0 < r < 1`, the quotient `log(∑_k μ([kr, (k+1)r))^q) / log r` is
nonnegative. -/
theorem lqRatio_nonneg (hq : 1 ≤ q)
    (hr0 : 0 < r) (hr1 : r < 1) : 0 ≤ lqRatio μ q r := by
  obtain ⟨-, h0, h1⟩ := lq_summable_and_bounds μ hq hr0
  exact div_nonneg_of_nonpos (Real.log_nonpos h0 h1) (Real.log_neg hr0 hr1).le

include h0

/-- If `μ` vanishes on `(-∞, 0)`, the term `μ([0,r))^q ≥ μ(B(0,r/2))^q` of the `L^q` sum gives
`log(∑_k μ([kr, (k+1)r))^q) / log r ≤ q log μ(B(0,r/2)) / log r` for `0 < r < 1`. -/
theorem lqRatio_le (hq : 1 ≤ q) (hr0 : 0 < r) (hr1 : r < 1)
    (hm : 0 < μ.real 𝔒) :
    lqRatio μ q r ≤ q * Real.log (μ.real 𝔒) / Real.log r := by
  obtain ⟨hsum, -, -⟩ := lq_summable_and_bounds μ hq hr0
  have hmI : μ.real 𝔒 ≤ μ.real 𝕹 := by
    refine (measureReal_mono fun x hx => ?_).trans
      ((measureReal_union_le (Iio 0) 𝕹).trans (by simp [measureReal_def, h0]))
    rw [mem_closedBall, Real.dist_eq, sub_zero, abs_le] at hx
    grind
  refine div_le_div_of_nonpos_of_le (Real.log_neg hr0 hr1).le ?_
  rw [← Real.log_rpow hm]
  exact Real.log_le_log (Real.rpow_pos_of_pos hm q)
    ((Real.rpow_le_rpow hm.le hmI (by linarith)).trans (by simpa [lqSum] using hsum.le_tsum 0 fun _ _ => by positivity))

include hpos

/-- The ball-mass estimate in Shmerkin's Lemma 1.7, specialised to the point `0` of a
measure supported on `[0,∞)`. At scale `r`, one grid interval covers `B(0,r/2)` up to a null
set. This is proved here, not assumed. See P. Shmerkin, Ann. of Math. 189 (2019), 319–391,
Lemma 1.7, DOI 10.4007/annals.2019.189.2.1. -/
theorem shmerkin_ball_bound_zero (hq : 1 < q) (hs : s < lqDim μ q) :
    ∀ᶠ r in 𝓝[>] 0, μ.real 𝔒 ≤ r ^ (𝔛 * s) := by
  have ht : 𝔘 * s < liminf (lqRatio μ q) (𝓝[>] 0) := by
    linarith [(lt_div_iff₀ 𝕺).1 hs]
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 1 := Ioo_mem_nhdsGT one_pos
  filter_upwards [eventually_lt_of_lt_liminf ht
    (isBoundedUnder_of_eventually_ge (hev.mono fun r hr => lqRatio_nonneg μ hq.le hr.1 hr.2)), hev]
    with r hr hrI
  have hm := hpos (r / 2) (half_pos hrI.1)
  have he := (lt_div_iff_of_neg (Real.log_neg hrI.1 hrI.2)).1 (hr.trans_le (lqRatio_le μ h0 hq.le hrI.1 hrI.2 hm))
  apply (Real.log_le_log_iff hm (Real.rpow_pos_of_pos hrI.1 _)).1
  rw [Real.log_rpow hrI.1]
  have halg : q * (𝔛 * s * Real.log r) = 𝔘 * s * Real.log r := by
    field_simp
  nlinarith

/-- A local dimension is at least a ball-mass exponent; replacing `r` by `r/2` does not
change the logarithmic limit. -/
theorem localDim_ge_of_ball_bound
    (hlim : Tendsto (fun r => Real.log (μ.real 𝔙) / Real.log r) (𝓝[>] 0) (𝓝 d))
    (hball : ∀ᶠ r in 𝓝[>] 0, μ.real 𝔒 ≤ r ^ a) : a ≤ d := by
  refine le_of_tendsto_of_tendsto (f := fun r => a + a * Real.log 2 / Real.log r) (by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atBot Real.tendsto_log_nhdsGT_zero))
    hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_nhdsGT_zero_mul_left two_pos hball] with r hr hb
  rw [mul_div_cancel_left₀ _ two_ne_zero] at hb
  have hl := Real.log_neg hr.1 (by linarith [hr.2])
  have he := Real.log_le_log (hpos _ hr.1) hb
  rw [Real.log_rpow (by simp_all), Real.log_mul two_ne_zero hr.1.ne'] at he
  rw [le_div_iff_of_neg hl, add_mul, div_mul_cancel₀ _ hl.ne]
  linarith

/-- The contradiction used in Section 1.2.2: a larger `L^q` dimension would, by the
ball-mass estimate of Lemma 1.7, force a larger local dimension at `0`. -/
theorem lqDim_le_of_localDim (hlim : Tendsto (fun r => Real.log (μ.real 𝔙) / Real.log r) (𝓝[>] 0) (𝓝 d))
    (hq : 1 < q) :
    lqDim μ q ≤ q / 𝔘 * d := by
  by_contra! h
  obtain ⟨s, hs, hsD⟩ := exists_between h
  have hd := localDim_ge_of_ball_bound μ h0 hpos hlim (shmerkin_ball_bound_zero μ h0 hpos hq hsD)
  have he : q * (𝔛 * s) = 𝔘 * s := by field_simp
  have hs' : q * d < s * 𝔘 := by
    rw [div_mul_eq_mul_div] at hs
    exact (div_lt_iff₀ 𝕺).1 hs
  nlinarith

end

/-! ### The natural measure of the example near `0` -/

/-- If the first `m` letters of `ω` are `0`, then `π(ω) ≤ 8^{-m}`, as `f_0(z) = z/8`. -/
theorem lq_natProj_le (h : ∀ i < m, ω i = 0) :
    exampleIFS.natProj ω ≤ (1 / 8 : ℝ) ^ m := by
  have hl : (List.ofFn fun j : Fin m => ω j) = List.replicate m 0 := by simp_all
  have hc : ∀ n z, exampleIFS.comp (List.replicate n 0) z = z / 8 ^ n := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [List.replicate_succ, IFS.comp_cons, Function.comp_apply, ih]
      show z / 8 ^ n / 8 = z / 8 ^ (n + 1)
      ring
  rw [exampleIFS.natProj_eq_comp_prefix ω m, hl, hc]
  set y := exampleIFS.natProj fun j => ω (j + m)
  have hy' : (y / 8 ^ m) = ((y / 8 ^ m : ℝ) : ℂ) := by simp_all
  rw [hy', Complex.ofReal_re, one_div_pow]
  exact div_le_div_of_nonneg_right (exampleIFS.attractor_subset_I ⟨fun j => ω (j + m), rfl⟩).2 (by positivity)

/-- The natural measure of a Gibbs measure charges every ball `B(0,r)`, `r > 0`: it contains the
image of the cylinder `[0^m]` for `8^{-m} ≤ r`. -/
theorem lq_measureReal_closedBall_pos
    [IsProbabilityMeasure ν] (hG : IsGibbsMeasure φ ν) (hr : 0 < r) :
    0 < (ν.map exampleIFS.natProj).real 𝔙 := by
  obtain ⟨c₁, hc₁, c₂, -, P, hG⟩ := hG
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 8 : ℝ) < 1)
  rw [map_measureReal_apply exampleIFS.measurable_natProj measurableSet_closedBall]
  refine (mul_pos hc₁ (Real.exp_pos _)).trans_le
    ((hG (fun _ => 0) m).1.trans (measureReal_mono fun y hy => ?_))
  rw [mem_preimage, mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg (exampleIFS.attractor_subset_I ⟨y, rfl⟩).1]
  exact (lq_natProj_le hy).trans hm.le

/-- `L^q` dimensions of the polynomial example in Section 1.2.2, from Bowen's theorem:
for every Gibbs measure `ν` of the potential `s(Φ) log|f'_{ω₀}(π(σω))|` and every `q > 1`,
the natural measure `μ = ν ∘ π⁻¹` has `D_μ(q) ≤ q (s(Φ) - 1/3) / (q - 1)`, which is smaller than `s(Φ)` for `q > 3 s(Φ)`. The `L^q` sums
converge, and the quotient whose limit inferior is `τ_μ(q)` is bounded below and does not tend to
`∞`, so the limit inferior is not a junk value. -/
theorem example_lq_of_bowen (hB : BowenGibbsStatement) :
    ∃ s,
      exampleIFS.PressureZero s ∧
      ∀ ν, IsProbabilityMeasure ν →
        IsGibbsMeasure (exampleIFS.potential s) ν → ∀ q > 1,
        lqDim (ν.map exampleIFS.natProj) q ≤ q / 𝔘 * (s - 1 / 3) ∧
        (3 * s < q → lqDim (ν.map exampleIFS.natProj) q < s) := by
  obtain ⟨s, hs, -, hloc⟩ := example_localDim_of_bowen hB
  refine ⟨s, hs, fun ν hν hG q hq => ?_⟩
  have hdim := lqDim_le_of_localDim _ (by
    exact Measure.map_apply exampleIFS.measurable_natProj measurableSet_Iio ▸ measure_mono_null (fun ω hω => (not_lt.2 (exampleIFS.attractor_subset_I ⟨ω, rfl⟩).1 hω).elim)
      measure_empty) (fun _ hr => lq_measureReal_closedBall_pos hG hr) (hloc ν hν hG) hq
  refine ⟨hdim, fun h3 => hdim.trans_lt ?_⟩
  rw [div_mul_eq_mul_div, div_lt_iff₀ 𝕺]
  linarith

end AnalyticESC
