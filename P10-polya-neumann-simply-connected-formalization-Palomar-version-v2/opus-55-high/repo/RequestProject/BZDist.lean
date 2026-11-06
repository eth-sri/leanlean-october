module

public import RequestProject.BoundaryChart
public import RequestProject.LipschitzCover

/-!
# Signed distance and local transversality (towards External theorem BZ)

The signed distance `d_Ω(z) = dist(z, Ωᶜ) - dist(z, Ω)` is positive exactly on `Ω` (for open
`Ω ≠ ℂ`) and `2`-Lipschitz. In a Lipschitz chart at `p` with inward direction `n = conj(c) i`, it
increases at a definite rate along `n` near `p`: `d(z) + t/(2(K+1)) ≤ d(z + t n)`
(`signedDist_add_le_of_chart`).
-/

@[expose] public section

open Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

/-- The signed distance to the boundary, positive inside: `dist(z, Ωᶜ) - dist(z, Ω)`. -/
def signedDist (Ω : Set ℂ) (z : ℂ) : ℝ := infDist z Ωᶜ - infDist z Ω

lemma lipschitzWith_signedDist (Ω : Set ℂ) : LipschitzWith 2 (signedDist Ω) := by
  have h := (lipschitz_infDist_pt (Ωᶜ)).sub (lipschitz_infDist_pt Ω)
  have : ((1 : NNReal) + 1) = 2 := by norm_num
  rwa [this] at h

lemma continuous_signedDist (Ω : Set ℂ) : Continuous (signedDist Ω) :=
  (lipschitzWith_signedDist Ω).continuous

lemma signedDist_of_mem {Ω : Set ℂ} {z : ℂ} (hz : z ∈ Ω) : signedDist Ω z = infDist z Ωᶜ := by
  simp [signedDist, infDist_zero_of_mem hz]

lemma signedDist_of_notMem {Ω : Set ℂ} {z : ℂ} (hz : z ∉ Ω) : signedDist Ω z = -infDist z Ω := by
  simp [signedDist, infDist_zero_of_mem (show z ∈ Ωᶜ from hz)]

lemma signedDist_nonpos_of_notMem {Ω : Set ℂ} {z : ℂ} (hz : z ∉ Ω) : signedDist Ω z ≤ 0 := by
  rw [signedDist_of_notMem hz]; exact neg_nonpos.mpr infDist_nonneg

lemma signedDist_pos_of_mem {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩu : Ωᶜ.Nonempty) {z : ℂ}
    (hz : z ∈ Ω) : 0 < signedDist Ω z := by
  rw [signedDist_of_mem hz]
  exact (hΩo.isClosed_compl.notMem_iff_infDist_pos hΩu).mp (fun h => h hz)

lemma signedDist_pos_iff {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩu : Ωᶜ.Nonempty) {z : ℂ} :
    0 < signedDist Ω z ↔ z ∈ Ω :=
  ⟨fun h => by_contra fun hz => absurd (signedDist_nonpos_of_notMem hz) (not_le.mpr h),
    signedDist_pos_of_mem hΩo hΩu⟩

lemma signedDist_eq_zero_of_frontier {Ω : Set ℂ} (hΩo : IsOpen Ω) {z : ℂ}
    (hz : z ∈ frontier Ω) : signedDist Ω z = 0 := by
  rw [signedDist_of_notMem fun h => (hΩo.frontier_eq ▸ hz).2 (hΩo.interior_eq.symm ▸ h), ← infDist_closure,
    infDist_zero_of_mem (frontier_subset_closure hz), neg_zero]

/-- `|d_Ω(z)| ≤ |z - p|` for a boundary point `p` (both distances are dominated). -/
lemma infDist_compl_le_of_frontier {Ω : Set ℂ} (hΩo : IsOpen Ω) {p z : ℂ}
    (hp : p ∈ frontier Ω) : infDist z Ωᶜ ≤ ‖z - p‖ := by
  rw [← dist_eq_norm]; exact infDist_le_dist_of_mem fun h => (hΩo.frontier_eq ▸ hp).2 (hΩo.interior_eq.symm ▸ h)

lemma infDist_le_of_frontier {Ω : Set ℂ} {p z : ℂ} (hp : p ∈ frontier Ω) :
    infDist z Ω ≤ ‖z - p‖ := by
  rw [← infDist_closure, ← dist_eq_norm]; exact infDist_le_dist_of_mem (frontier_subset_closure hp)

/-- The cone property in a chart, in the form used below: a point `q ∈ Ω` of the half box,
shifted by `s` with `‖s - δ n‖ ≤ δ/(2(K+1))`, `n = conj(c) i`, stays in `Ω`. -/
lemma chart_shift_mem {Ω : Set ℂ} {p c : ℂ} {r h : ℝ} {K : NNReal} {f : ℝ → ℝ}
    (hch : IsChartAt Ω p c r h K f) {δ : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (hδh : δ ≤ h / 3)
    {q : ℂ} (hq : q ∈ Ω) (hqp : ‖q - p‖ < min r h / 2) {s : ℂ}
    (hs : ‖s - δ * (conj c * Complex.I)‖ ≤ δ / (2 * (K + 1))) : q + s ∈ Ω := by
  obtain ⟨hc, hr, hh, hf, -, -, hΩ⟩ := hch
  have hn := norm_mul_sub hc q p
  have := chart_segment hc hf hΩ hδ hδr hδh hq (lt_of_le_of_lt (Complex.abs_re_le_norm _) (by grind)) (lt_of_le_of_lt (Complex.abs_im_le_norm _) (by grind)) (by
    rw [mem_closedBall, dist_eq_norm]
    have : -s - -(starRingEnd ℂ c) * Complex.I * δ = -(s - δ * (conj c * Complex.I)) := by ring
    rw [this, norm_neg]; assumption)  ⟨zero_le_one, le_rfl⟩
  simp_all

/-- Inside the domain: the signed distance increases along the inward direction. -/
lemma signedDist_add_le_of_chart_mem {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩu : Ωᶜ.Nonempty)
    {p c : ℂ} {r h : ℝ} {K : NNReal} {f : ℝ → ℝ}
    (hch : IsChartAt Ω p c r h K f) (hp : p ∈ frontier Ω) {z : ℂ} (hzΩ : z ∈ Ω)
    (hz : ‖z - p‖ < min r h / 4) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) (hth : t ≤ h / 3) :
    signedDist Ω z + t / (2 * (K + 1)) ≤ signedDist Ω (z + t * (conj c * Complex.I)) := by
  set n : ℂ := conj c * Complex.I
  set κ : ℝ := 1 / (2 * (K + 1)) with hκ
  set e := infDist z Ωᶜ with he
  have he0 : 0 < e := (hΩo.isClosed_compl.notMem_iff_infDist_pos hΩu).mp (fun h => h hzΩ)
  have hep : e ≤ ‖z - p‖ := infDist_compl_le_of_frontier hΩo hp
  have htdiv : t / (2 * (K + 1)) = κ * t := by ring
  have hball : ball (z + t * n) (e + κ * t) ⊆ Ω := by
    intro q hq
    rw [mem_ball, dist_eq_norm] at hq
    set u := q - (z + t * n)
    have hpos : 0 < e + κ * t := by positivity
    set q' := z + (e / (e + κ * t) : ℝ) * u
    have hq'z : ‖q' - z‖ < e := by
      simp only [q', add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg he0.le hpos.le)]
      rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
      simp_all
    have hq'Ω : q' ∈ Ω := by
      by_contra hc'
      have := infDist_le_dist_of_mem (x := z) (show q' ∈ Ωᶜ from hc')
      rw [dist_comm, dist_eq_norm] at this
      linarith
    rcases ht0.eq_or_lt with rfl | htp
    · -- `t = 0`: the ball is `B(z, e)`
      have : q = q' := by
        simp [q', u, div_self he0.ne']
      simp_all
    have := chart_shift_mem hch htp htr hth hq'Ω (by
      have : ‖q' - p‖ ≤ ‖q' - z‖ + ‖z - p‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]; exact dist_triangle _ _ _
      linarith) (by
      have hqq : q - q' - t * n = (κ * t / (e + κ * t) : ℝ) * u := by
        simp only [q']
        have : e / (e + κ * t) = 1 - κ * t / (e + κ * t) := by field_simp; ring
        rw [this]; push_cast; ring
      rw [hqq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), htdiv, div_mul_eq_mul_div, div_le_iff₀ hpos]
      exact mul_le_mul_of_nonneg_left hq.le (by positivity))
    simp_all
  rw [signedDist_of_mem hzΩ, signedDist_of_mem (hball (mem_ball_self (by positivity)))]
  rw [le_infDist hΩu]
  intro y hy
  by_contra hlt
  exact hy (hball (by simp_all [dist_comm]))

/-- Outside the domain (both ends outside): the signed distance increases along the inward
direction. -/
lemma signedDist_add_le_of_chart_notMem {Ω : Set ℂ} (hΩne : Ω.Nonempty)
    {p c : ℂ} {r h : ℝ} {K : NNReal} {f : ℝ → ℝ}
    (hch : IsChartAt Ω p c r h K f) (hp : p ∈ frontier Ω) {z : ℂ} {t : ℝ}
    (hzΩ : z ∉ Ω) (hwΩ : z + t * (conj c * Complex.I) ∉ Ω)
    (hz : ‖z - p‖ < min r h / 10) (ht0 : 0 ≤ t) (htr : t ≤ min r h / 10) :
    signedDist Ω z + t / (2 * (K + 1)) ≤ signedDist Ω (z + t * (conj c * Complex.I)) := by
  set n : ℂ := conj c * Complex.I
  have hn1 : ‖n‖ = 1 := by
    simp [n, hch.1]
  set κ : ℝ := 1 / (2 * (K + 1)) with hκ
  have hK0  := K.2
  have hκ1 : κ ≤ 1 / 2 := by
    apply div_le_div_of_nonneg_left <;> nlinarith
  have htdiv : t / (2 * (K + 1)) = κ * t := by ring
  rw [signedDist_of_notMem hzΩ, signedDist_of_notMem hwΩ]
  rcases ht0.eq_or_lt with rfl | htp
  · simp
  set w := z + t * n
  set e := infDist w Ω with he
  have he0 : 0 ≤ e := infDist_nonneg
  have hwp : ‖w - p‖ ≤ ‖z - p‖ + t := by
    have : w - p = (z - p) + t * n := by ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hn1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0, mul_one]
  have hep : e ≤ ‖w - p‖ := infDist_le_of_frontier hp
  have hpos : 0 < e + κ * t := by positivity
  -- the ball `B(z, e + κ t)` misses `Ω`
  have hball : ∀ q ∈ ball z (e + κ * t), q ∉ Ω := by
    intro q hq hqΩ
    rw [mem_ball, dist_eq_norm] at hq
    set u := q - z
    set q' := w + (e / (e + κ * t) : ℝ) * u
    have hq'w : dist q' w < e ∨ e = 0 := by
      rcases he0.eq_or_lt with h0 | h0
      · simp_all
      left
      rw [dist_eq_norm]
      simp only [q', add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg he0 hpos.le)]
      rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
      simp_all
    have hq'Ω : q' ∉ Ω := by
      rcases hq'w with h1 | h1
      · intro hm
        have := infDist_le_dist_of_mem (x := w) hm
        rw [dist_comm] at this; linarith
      · have : q' = w := by simp [q', h1]
        simp_all
    have := chart_shift_mem hch htp (by grind) (by grind) hqΩ (by
      have : ‖q - p‖ ≤ ‖q - z‖ + ‖z - p‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]; exact dist_triangle _ _ _
      have : e + κ * t ≤ ‖z - p‖ + t + t / 2 := by nlinarith
      linarith) (by
      have hqq : q' - q - t * n = -((κ * t / (e + κ * t) : ℝ) * u) := by
        simp only [q']
        have : e / (e + κ * t) = 1 - κ * t / (e + κ * t) := by field_simp; ring
        rw [this]; push_cast; ring
      rw [hqq, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), htdiv, div_mul_eq_mul_div, div_le_iff₀ hpos]
      exact mul_le_mul_of_nonneg_left hq.le (by positivity))
    simp_all
  have : e + κ * t ≤ infDist z Ω := by
    rw [le_infDist hΩne]
    intro y hy
    by_contra hlt
    simp_all [dist_comm]
  linarith

/-- **Local transversality.** In a Lipschitz chart at the boundary point `p` with inward
direction `n = conj(c) i`, for `‖z - p‖ < min r h / 10` and `0 ≤ t ≤ min r h / 10`,
`d_Ω(z) + t/(2(K+1)) ≤ d_Ω(z + t n)`. -/
theorem signedDist_add_le_of_chart {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩu : Ωᶜ.Nonempty) {p c : ℂ} {r h : ℝ} {K : NNReal} {f : ℝ → ℝ}
    (hch : IsChartAt Ω p c r h K f) (hp : p ∈ frontier Ω) {z : ℂ}
    (hz : ‖z - p‖ < min r h / 10) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ min r h / 10) :
    signedDist Ω z + t / (2 * (K + 1)) ≤ signedDist Ω (z + t * (conj c * Complex.I)) := by
  set n : ℂ := conj c * Complex.I
  have hn1 : ‖n‖ = 1 := by simp [n, hch.1]
  have hpt : ∀ s : ℝ, 0 ≤ s → ‖z + s * n - p‖ ≤ ‖z - p‖ + s := fun s hs => by
    have : z + s * n - p = (z - p) + s * n := by ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hn1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs, mul_one]
  by_cases hzΩ : z ∈ Ω
  · exact signedDist_add_le_of_chart_mem hΩo hΩu hch hp hzΩ (by linarith) ht0
      (by grind) (by grind)
  by_cases hwΩ : z + t * n ∈ Ω
  swap
  · exact signedDist_add_le_of_chart_notMem hΩne hch hp hzΩ hwΩ hz ht0 htr
  -- mixed case: cross the boundary at the last time `t₁` outside `Ω`
  set S : Set ℝ := {s | s ∈ Icc 0 t ∧ z + s * n ∉ Ω}
  have hSc : IsClosed S := by
    refine isClosed_Icc.inter ?_
    exact hΩo.isClosed_compl.preimage (by fun_prop)
  have hSb : BddAbove S := ⟨t, fun s hs => hs.1.2⟩
  set t₁ := sSup S
  have ht₁S  := hSc.csSup_mem ⟨0, ⟨⟨le_rfl, ht0⟩, by simp_all⟩⟩ hSb
  have ht₁t  := ht₁S.1.2
  have h1  :=
    signedDist_add_le_of_chart_notMem hΩne hch hp hzΩ ht₁S.2 hz ht₁S.1.1 (by linarith)
  have h1'  := signedDist_nonpos_of_notMem ht₁S.2
  -- inside part: from every later time
  have h2 : ∀ s ∈ Ioc t₁ t, (t - s) / (2 * (K + 1)) ≤ signedDist Ω (z + t * n) := by
    intro s hs
    have hsΩ : z + s * n ∈ Ω := by
      by_contra hc'
      exact absurd (le_csSup hSb ⟨⟨by grind, hs.2⟩, hc'⟩) (not_le.mpr hs.1)
    have hm := signedDist_add_le_of_chart_mem hΩo hΩu hch hp hsΩ
      (by grind) (t := t - s) (by simp_all)
      (by grind) (by grind)
    have heq : z + s * n + (t - s : ℝ) * n = z + t * n := by push_cast; ring
    rw [heq] at hm
    have := signedDist_pos_of_mem hΩo hΩu hsΩ
    linarith
  have h2'  := ContinuousWithinAt.closure_le (by
      rw [closure_Ioc (lt_of_le_of_ne ht₁t (fun h => ht₁S.2 (h ▸ hwΩ))).ne]; trivial) (by fun_prop : Continuous fun s  => (t - s) / (2 * (K + 1))).continuousWithinAt continuousWithinAt_const
      (fun s hs => h2 s hs)
  grind

end PolyaNeumann

end
