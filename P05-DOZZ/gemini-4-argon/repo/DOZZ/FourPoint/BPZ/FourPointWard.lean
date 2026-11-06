/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardLimitClean

/-! # The Ward identity for the degenerate four-point weight

For a `C¹` real test function `φ` supported away from the insertions `0`, `1` and `z`, the limit
Ward identity holds for the degenerate four-point weight `k = |x − z|^{γχ} |x|^{−γα₁} |x − 1|^{−γα₂}
|x|₊^{γ(α₁+α₂+α₃−χ)}` with `q = s + 1`:

  `E[I^{-q} ∫ ∂_v(φ k̃) |x|₊^{4+γ²q} dM] = q E[I^{-q-1} γ² ∬ (φ(x) − φ(y)) k(x) k(y) K_v(x − y)/2 dM dM]`.

The auxiliary cutoff is built from the distance to the support of `φ`, and the far set is a small
disk far away. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The open region where the degenerate four-point weight is smooth and positive. -/
def bpzRegular (z : ℂ) : Set ℂ := {x | x ≠ 0 ∧ x ≠ 1 ∧ x ≠ z}


theorem bpz_contDiffAt_norm_sub_rpow {c x : ℂ} (hx : x ≠ c) (p : ℝ) :
    ContDiffAt ℝ 1 (fun y => ‖y - c‖ ^ p) x := by
  exact ((contDiffAt_norm ℝ (sub_ne_zero.mpr hx)).comp x (contDiffAt_id.sub contDiffAt_const)).rpow_const_of_ne (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx))

variable {γ χ α₁ α₂ α₃ : ℝ}

theorem bpzTildeWeight_contDiffAt {z x : ℂ} (hx : x ∈ bpzRegular z) :
    ContDiffAt ℝ 1 (bpzTildeWeight γ χ α₁ α₂ z) x := by
  obtain ⟨h0, h1, hz⟩ := hx
  unfold bpzTildeWeight
  exact ((bpz_contDiffAt_norm_sub_rpow hz _).mul (by simpa using bpz_contDiffAt_norm_sub_rpow (c := 0) h0 (-(γ * α₁)))).mul (bpz_contDiffAt_norm_sub_rpow h1 _)


theorem bpzTildeWeight_nonneg z x : 0 ≤ bpzTildeWeight γ χ α₁ α₂ z x := by
  unfold bpzTildeWeight
  positivity


theorem bpzSoftWeight_zero_eq z x :
    bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x =
      bpzTildeWeight γ χ α₁ α₂ z x * normPlus x ^ (γ * (α₁ + α₂ + α₃ - χ)) := by
  unfold bpzSoftWeight bpzBaseWeight bpzTildeWeight
  have hn : (Complex.normSq (x - z) + (0 : ℝ) ^ 2) ^ (γ * χ / 2) = ‖x - z‖ ^ (γ * χ) := by
    rw [show ((0 : ℝ) ^ 2) = 0 by norm_num, add_zero, Complex.normSq_eq_norm_sq,
      ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    push_cast
    ring
  rw [hn]
  ring

theorem bpz_exponent_identity (hγ : 0 < γ) :
    4 + γ ^ 2 * (fourPointSExp γ (-χ) α₁ α₂ α₃ + 1) = γ * (α₁ + α₂ + α₃ - χ) := by
  unfold fourPointSExp Q
  field_simp
  ring

/-- The auxiliary cutoff: `1` within `2δ` of `K`, `0` beyond `3δ`, linear in between. -/
noncomputable def bpzRhoCut (K : Set ℂ) (δ : ℝ) (y : ℂ) : ℝ :=
  max 0 (min 1 ((3 * δ - Metric.infDist y K) / δ))

theorem continuous_bpzRhoCut K δ : Continuous (bpzRhoCut K δ) := by
  unfold bpzRhoCut
  exact continuous_const.max (continuous_const.min
    ((continuous_const.sub (Metric.continuous_infDist_pt K)).div_const _))







/-- The limit data for the degenerate four-point weight and a test function supported in the
regular region. -/
theorem bpz_fourPoint_limitData (hγ : 0 < γ) {q} (hq1 : 1 ≤ q)
    (hq : 4 + γ ^ 2 * q = γ * (α₁ + α₂ + α₃ - χ)) {z} {φ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ bpzRegular z) :
    ∃ (δ : ℝ) (ρ : ℂ → ℝ) (R : ℝ), 0 ≤ R ∧ ‖z‖ ≤ R ∧
      BPZLimitData γ q δ ρ (bpzTildeWeight γ χ α₁ α₂ z) (bpzSoftWeight γ χ α₁ α₂ α₃ 0 z) φ
        (bpzFarBall R) := by
  have bpzFarBall_norm_ge {R} (hR : 0 ≤ R) {y} (hy : y ∈ bpzFarBall R) : R + 3 ≤ ‖y‖ := by
    unfold bpzFarBall at hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have h1 := norm_sub_norm_le (((R + 4 : ℝ)) : ℂ) y
    rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h1
    linarith
  have bpzRhoCut_sep {K} {δ} (hδ : 0 < δ) {x} {y} (hx : x ∈ K) (hy : bpzRhoCut K δ y < 1) : 2 * δ ≤ ‖x - y‖ := by
    have bpzRhoCut_eq_one {K} {y} (hy : Metric.infDist y K ≤ 2 * δ) : bpzRhoCut K δ y = 1 := by
      unfold bpzRhoCut
      rw [min_eq_left (show 1 ≤ (3 * δ - Metric.infDist y K) / δ by rw [le_div_iff₀ hδ]; linarith), max_eq_right zero_le_one]
    have h : 2 * δ < Metric.infDist y K := by
      by_contra h
      push Not at h
      rw [bpzRhoCut_eq_one h] at hy
      exact lt_irrefl _ hy
    have := Metric.infDist_le_dist_of_mem (x := y) hx
    rw [dist_eq_norm, norm_sub_rev] at this
    linarith
  have bpzRhoCut_mem_of_ne_zero {K : Set ℂ} (hK : K.Nonempty) {δ} (hδ : 0 < δ) {y} (hy : bpzRhoCut K δ y ≠ 0) : y ∈ Metric.cthickening (3 * δ) K := by
    have hlt : Metric.infDist y K < 3 * δ := by
      by_contra h
      push Not at h
      apply hy
      unfold bpzRhoCut
      rw [max_eq_left (le_trans (min_le_right _ _) (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le))]
    obtain ⟨x, hxK, hxy⟩ := (Metric.infDist_lt_iff hK).mp hlt
    exact Metric.mem_cthickening_of_dist_le y x _ K hxK hxy.le
  have bpzRhoCut_le_one K δ y : bpzRhoCut K δ y ≤ 1 := max_le zero_le_one (min_le_left _ _)
  have bpzRhoCut_nonneg K δ y : 0 ≤ bpzRhoCut K δ y := le_max_left _ _
  have measurable_bpzTildeWeight : Measurable (bpzTildeWeight γ χ α₁ α₂ z) := by
    unfold bpzTildeWeight
    fun_prop
  have bpzTildeWeight_pos {z} {x} (hx : x ∈ bpzRegular z) : 0 < bpzTildeWeight γ χ α₁ α₂ z x := by
    obtain ⟨h0, h1, hz⟩ := hx
    unfold bpzTildeWeight
    have := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hz)) (γ * χ)
    have := Real.rpow_pos_of_pos (norm_pos_iff.mpr h0) (-(γ * α₁))
    have c := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h1)) (-(γ * α₂))
    positivity
  set U := bpzRegular z with hU
  set kt := bpzTildeWeight γ χ α₁ α₂ z with hkt
  set p₀ : ℂ := ((‖z‖ + 2 : ℝ) : ℂ) with hp₀
  have hp₀n : ‖p₀‖ = ‖z‖ + 2 := by
    rw [hp₀, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hp₀U : p₀ ∈ U := by
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have := congrArg norm h; rw [hp₀n, norm_zero] at this; linarith [norm_nonneg z]
    · have := congrArg norm h; rw [hp₀n, norm_one] at this; linarith [norm_nonneg z]
    · have := congrArg norm h; rw [hp₀n] at this; linarith
  set K : Set ℂ := tsupport φ ∪ {p₀} with hK
  have hKc : IsCompact K := hφc.isCompact.union isCompact_singleton
  have hKU : K ⊆ U := Set.union_subset hφU (Set.singleton_subset_iff.mpr hp₀U)
  have hKne : K.Nonempty := ⟨p₀, Or.inr rfl⟩
  obtain ⟨δ₀, hδ₀, hsub⟩ := hKc.exists_cthickening_subset_open ((show IsOpen (bpzRegular z) by rw [(show bpzRegular z = {x | x ≠ 0} ∩ ({x | x ≠ 1} ∩ {x | x ≠ z}) by ext x; simp [bpzRegular])]; exact isOpen_ne.inter (isOpen_ne.inter isOpen_ne))) hKU
  set δ : ℝ := δ₀ / 3 with hδdef
  have hδ : 0 < δ := by positivity
  set ρ : ℂ → ℝ := bpzRhoCut K δ with hρ
  set L : Set ℂ := Metric.cthickening (3 * δ) K with hL
  have hLc : IsCompact L := hKc.cthickening
  have hLU : L ⊆ U := by rw [hL, (show 3 * δ = δ₀ by rw [hδdef]; ring)]; exact hsub
  have hρL : ∀ y, ρ y ≠ 0 → y ∈ L := fun y hy => bpzRhoCut_mem_of_ne_zero hKne hδ hy
  obtain ⟨RL, hRL⟩ := hLc.isBounded.exists_norm_le
  set R : ℝ := max (max RL ‖z‖) 0 + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  have hRL' : RL < R := by
    have := le_max_left RL ‖z‖; have := le_max_left (max RL ‖z‖) 0; linarith
  have hzR : ‖z‖ ≤ R := by
    have := le_max_right RL ‖z‖; have := le_max_left (max RL ‖z‖) 0; linarith
  have hktc : ContinuousOn kt U := fun x hx =>
    (bpzTildeWeight_contDiffAt hx).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := hLc.exists_bound_of_continuousOn (hktc.mono hLU)
  obtain ⟨x₀, hx₀K, hx₀min⟩ := hKc.exists_isMinOn hKne (hktc.mono hKU)
  obtain ⟨c, hc, hck⟩ := bpzSoftWeight_ge_on_farBall (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂)
    (α₃ := α₃) R hR0
  refine ⟨δ, ρ, R, hR0, hzR, ?_⟩
  exact {
    γ_pos := hγ
    q_ge := hq1
    δ_pos := hδ
    ρ_meas := (continuous_bpzRhoCut K δ).measurable
    ρ_nonneg := bpzRhoCut_nonneg K δ
    ρ_le_one := bpzRhoCut_le_one K δ
    ρ_bdd := ⟨RL, fun y hy => by
      by_contra h
      have := hRL y (hρL y h)
      linarith⟩
    kt_meas := measurable_bpzTildeWeight
    kt_nonneg := bpzTildeWeight_nonneg z
    kt_bdd := ⟨B, fun y hy => by
      have := hB y (hρL y hy)
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans this⟩
    ρkt_cont := by
      rw [continuous_iff_continuousAt]
      intro x
      by_cases hx : x ∈ U
      · exact (continuous_bpzRhoCut K δ).continuousAt.mul
          (bpzTildeWeight_contDiffAt hx).continuousAt
      · have hxL : x ∉ L := fun h => hx (hLU h)
        exact continuousAt_const.congr (show (fun y => ρ y * kt y) =ᶠ[𝓝 x] fun _ => 0 by filter_upwards [hLc.isClosed.isOpen_compl.mem_nhds hxL] with y hy; rw [(show ρ y = 0 by by_contra h; exact hy (hρL y h)), zero_mul]).symm
    k₂_eq := fun y => by rw [bpzSoftWeight_zero_eq, hq]
    f_C1 := by
      rw [contDiff_iff_contDiffAt]
      intro x
      by_cases hx : x ∈ U
      · exact hφ.contDiffAt.mul (bpzTildeWeight_contDiffAt hx)
      · have hxt : x ∉ tsupport φ := fun h => hx (hφU h)
        exact contDiffAt_const.congr_of_eventuallyEq (by filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hxt] with y hy; rw [image_eq_zero_of_notMem_tsupport hy, zero_mul])
    φ_compact := hφc
    φ_lip := by
      obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφc hφ one_ne_zero
      exact ⟨C, hC⟩
    kt_pos := ⟨kt x₀, bpzTildeWeight_pos (hKU hx₀K), fun x hx => hx₀min (Or.inl hx)⟩
    sep := fun x hx y hy => bpzRhoCut_sep hδ (Or.inl hx) hy
    D_meas := bpzFarBall_measurableSet R
    D_rho := fun y hy => by
      by_contra h
      have := hRL y (hρL y h)
      have h2 := bpzFarBall_norm_ge hR0 hy
      linarith
    D_low := ⟨c, hc, fun y hy => hck z hzR 0 le_rfl zero_le_one y hy⟩
    D_bdd := by
      obtain ⟨Rd, hRd⟩ := (bpzFarBall_bounded R).exists_norm_le
      exact ⟨Rd, hRd⟩ }

/-- The degenerate four-point weight is almost surely integrable against the chaos. -/
theorem bpz_fourPoint_integrable_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    X (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hχ : 0 < χ) (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    {z} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    ∀ᵐ ω ∂P, Integrable (bpzSoftWeight γ χ α₁ α₂ α₃ 0 z) (M ω) := by
  filter_upwards [bpzMass_lt_top_ae P X hX hγ hγ2 M hM hχ hα₁ hα₂ hα₃ 0 z hz0 hz1] with ω hω
  refine ⟨(measurable_bpzSoftWeight 0 z).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => bpzSoftWeight_nonneg 0 z x)]
  exact hω

/-- The probabilistic data of the cutoff Ward identity for the degenerate four-point weight. -/
theorem bpz_fourPoint_wardProb {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc) (hχ : 0 < χ) (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ)
    (hα₃ : α₃ < Q γ) {z} (hz0 : z ≠ 0) (hz1 : z ≠ 1) {ρ} (hρm : Measurable ρ)
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∀ y, ρ y ≤ 1) R :
    BPZWardProb P X γ M Xc ρ (bpzSoftWeight γ χ α₁ α₂ α₃ 0 z) (bpzFarBall R) where
  hX := hX
  γ2 := hγ2
  hM := hM
  hMm := hMm
  hXc := hXc
  k₂_int := by
    filter_upwards [bpz_fourPoint_integrable_ae P X hX hγ hγ2 M hM hχ hα₁ hα₂ hα₃ hz0 hz1]
      with ω hω
    refine hω.mono' (((measurable_const.sub hρm).mul
      (measurable_bpzSoftWeight 0 z)).aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
    have hk := bpzSoftWeight_nonneg (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) 0 z y
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith [hρ1 y]) hk)]
    have := hρ0 y
    nlinarith
  D_neg := fun p hp => bpz_farBall_negMoment_lt_top P X hX hγ hγ2 M hM R p hp

/-- **The Ward identity for the degenerate four-point weight.** -/
theorem bpz_fourPoint_ward {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (hα₁ : α₁ < Q γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hs : 0 ≤ fourPointSExp γ (-χ) α₁ α₂ α₃)
    {z} (hz0 : z ≠ 0) (hz1 : z ≠ 1) {φ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ bpzRegular z) v :
    ∫ ω, (∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (-(fourPointSExp γ (-χ) α₁ α₂ α₃ + 1)) *
        ∫ x, fderiv ℝ (fun x => φ x * bpzTildeWeight γ χ α₁ α₂ z x) x v *
          normPlus x ^ (γ * (α₁ + α₂ + α₃ - χ)) ∂M ω ∂P =
      ∫ ω, (fourPointSExp γ (-χ) α₁ α₂ α₃ + 1) *
        ((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^
          (-(fourPointSExp γ (-χ) α₁ α₂ α₃ + 1) - 1) *
        (γ ^ 2 * ∫ x, ∫ y, (φ x - φ y) * (bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x *
          bpzSoftWeight γ χ α₁ α₂ α₃ 0 z y) * bpzKern v (x - y) / 2 ∂M ω ∂M ω)) ∂P := by
  set q : ℝ := fourPointSExp γ (-χ) α₁ α₂ α₃ + 1 with hqdef
  have hq := bpz_exponent_identity (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) hγ
  rw [← hqdef] at hq
  obtain ⟨Xc, hXc, -⟩ := hM.2
  obtain ⟨δ, ρ, R, hR0, hzR, hd⟩ := bpz_fourPoint_limitData (α₃ := α₃) hγ (by linarith) hq hφ hφc hφU
  have h := hd.ward_limit_clean (bpz_fourPoint_wardProb P X hX hγ hγ2 M hM hMm Xc hXc hχ hα₁ hα₂ hα₃ hz0 hz1 hd.ρ_meas hd.ρ_nonneg hd.ρ_le_one R) v
  rw [hq] at h
  exact h

end DOZZ.Proofs
