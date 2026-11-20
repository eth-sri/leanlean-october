module

public import RequestProject.BoundaryChart
public import RequestProject.LipschitzCover
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Signed distance and local transversality (towards External theorem BZ)

The signed distance `d_Ω(z) = dist(z, Ωᶜ) - dist(z, Ω)` is positive exactly on `Ω` (for open
`Ω ≠ ℂ`) and `2`-Lipschitz. In a Lipschitz chart at `p` with inward direction `n = conj(c) i`, it
increases at a definite rate along `n` near `p`: `d(z) + t/(2(K+1)) ≤ d(z + t n)`
(`signedDist_add_le_of_chart`).
-/

@[expose] public section

open Set Filter Metric
open scoped ComplexConjugate Real Topology Pointwise

noncomputable section

namespace PolyaNeumann

/-- The signed distance to the boundary, positive inside: `dist(z, Ωᶜ) - dist(z, Ω)`. -/
def signedDist (Ω : Set ℂ) (z : ℂ) : ℝ := infDist z Ωᶜ - infDist z Ω

lemma lipschitzWith_signedDist (Ω : Set ℂ) : LipschitzWith 2 (signedDist Ω) := by
  have h := (lipschitz_infDist_pt (Ωᶜ)).sub (lipschitz_infDist_pt Ω)
  have : ((1 : NNReal) + 1) = 2 := by norm_num
  aesop

lemma continuous_signedDist (Ω : Set ℂ) : Continuous (signedDist Ω) :=
  (lipschitzWith_signedDist Ω).continuous

lemma signedDist_of_mem {Ω : Set ℂ} {z : ℂ} (hz : z ∈ Ω) : signedDist Ω z = infDist z Ωᶜ := by
  simp [signedDist, infDist_zero_of_mem hz]

lemma signedDist_of_notMem {Ω : Set ℂ} {z : ℂ} (hz : z ∉ Ω) : signedDist Ω z = -infDist z Ω := by
  simp [signedDist, infDist_zero_of_mem (show z ∈ Ωᶜ from hz)]

lemma signedDist_nonpos_of_notMem {Ω : Set ℂ} {z : ℂ} (hz : z ∉ Ω) : signedDist Ω z ≤ 0 := by
  rw [signedDist_of_notMem hz]; exact neg_nonpos.mpr infDist_nonneg

/-- The sharp bound follows by splitting a segment at its zero of signed distance. -/
lemma signedDist_lipschitz (Ω : Set ℂ) : LipschitzWith 1 (signedDist Ω) := by
  refine LipschitzWith.of_le_add_mul 1 fun x y => ?_
  simp  [NNReal.coe_one, one_mul]
  by_cases hx : x ∈ Ω <;> by_cases hy : y ∈ Ω
  · rw [signedDist_of_mem hx, signedDist_of_mem hy]
    exact infDist_le_infDist_add_dist
  · have hx' : 0 ≤ signedDist Ω x := by rw [signedDist_of_mem hx]; exact infDist_nonneg
    have hy' := signedDist_nonpos_of_notMem hy
    obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num)
      ((continuous_signedDist Ω).comp (show Continuous (AffineMap.lineMap (k := ℝ) x y) by
        change Continuous (fun t : ℝ => AffineMap.lineMap x y t); fun_prop)).continuousOn
      (show 0 ∈ Icc (signedDist Ω (AffineMap.lineMap x y 1))
        (signedDist Ω (AffineMap.lineMap x y 0)) by simp_all)
    let z := AffineMap.lineMap x y t
    have hz : infDist z Ωᶜ = 0 ∧ infDist z Ω = 0 := by
      change infDist z Ωᶜ - infDist z Ω = 0 at hzero
      by_cases h : z ∈ Ω
      · simp [infDist_zero_of_mem h] at hzero ⊢
        exact hzero
      · simp [infDist_zero_of_mem (show z ∈ Ωᶜ from h)] at hzero ⊢
        exact hzero
    have hxz := infDist_le_infDist_add_dist (x := x) (y := z) (s := Ωᶜ)
    have hyz := infDist_le_infDist_add_dist (x := y) (y := z) (s := Ω)
    have hsplit : dist x z + dist y z = dist x y := by
      dsimp [z]
      rw [dist_left_lineMap, dist_right_lineMap, Real.norm_of_nonneg ht.1,
        Real.norm_of_nonneg (sub_nonneg.mpr ht.2)]
      ring
    rw [hz.1, zero_add] at hxz
    rw [hz.2, zero_add] at hyz
    rw [signedDist_of_mem hx, signedDist_of_notMem hy]
    linarith
  · rw [signedDist_of_notMem hx, signedDist_of_mem hy]
    linarith [dist_nonneg (x := x) (y := y), infDist_nonneg (x := x) (s := Ω),
      infDist_nonneg (x := y) (s := Ωᶜ)]
  · rw [signedDist_of_notMem hx, signedDist_of_notMem hy]
    have := infDist_le_infDist_add_dist (x := y) (y := x) (s := Ω)
    rw [dist_comm] at this
    linarith

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
  have hz' : z ∉ Ω := fun h => (hΩo.frontier_eq ▸ hz).2 (hΩo.interior_eq.symm ▸ h)
  rw [signedDist_of_notMem hz', ← infDist_closure,
    infDist_zero_of_mem (frontier_subset_closure hz), neg_zero]

/-- `|d_Ω(z)| ≤ |z - p|` for a boundary point `p` (both distances are dominated). -/
lemma infDist_compl_le_of_frontier {Ω : Set ℂ} (hΩo : IsOpen Ω) {p z : ℂ}
    (hp : p ∈ frontier Ω) : infDist z Ωᶜ ≤ ‖z - p‖ := by
  have hp' : p ∈ Ωᶜ := fun h => (hΩo.frontier_eq ▸ hp).2 (hΩo.interior_eq.symm ▸ h)
  simpa [dist_eq_norm] using infDist_le_dist_of_mem hp'

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
  have hX : |(c * (q - p)).re| < r / 2 :=
    lt_of_le_of_lt (Complex.abs_re_le_norm _) (by grind)
  have hY : |(c * (q - p)).im| < h / 2 :=
    lt_of_le_of_lt (Complex.abs_im_le_norm _) (by grind)
  have hz : -s ∈ closedBall (-(starRingEnd ℂ c) * Complex.I * δ) (δ / (2 * (K + 1))) := by
    rw [mem_closedBall, dist_eq_norm]
    have : -s - -(starRingEnd ℂ c) * Complex.I * δ = -(s - δ * (conj c * Complex.I)) := by ring
    rw [this, norm_neg]; assumption
  have := chart_segment hc hf hΩ hδ hδr hδh hq hX hY hz (s := 1) ⟨zero_le_one, le_rfl⟩
  simpa using this

/-- A cone shift transports the whole inscribed ball, increasing its radius. -/
private lemma split_shifted_ball {z d q : ℂ} {e δ : ℝ} (he : 0 ≤ e) (hδ : 0 < δ)
    (hq : q ∈ ball (z + d) (e + δ)) :
    ∃ x : ℂ, (x ∈ ball z e ∨ x = z) ∧ q - x ∈ ball d δ := by
  rcases he.eq_or_lt with h0 | hp
  exact ⟨z, Or.inr rfl, by simpa [mem_ball, dist_eq_norm, ← h0, sub_sub] using hq⟩
  · rw [← ball_add_ball hp hδ] at hq
    obtain ⟨x, hx, y, hy, rfl⟩ := hq
    exact ⟨x, Or.inl hx, by simpa using hy⟩

private lemma add_dist_le_of_ball_subset {z : ℂ} {S : Set ℂ} {r : ℝ} (hS : S.Nonempty)
    (h : ball z r ⊆ Sᶜ) : r ≤ infDist z S :=
  (le_infDist hS).2 fun x hx => le_of_not_gt fun hlt => h (mem_ball'.2 hlt) hx

/-- Inside the domain: the signed distance increases along the inward direction. -/
lemma signedDist_add_le_of_chart_mem {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩu : Ωᶜ.Nonempty)
    {p c : ℂ} {r h : ℝ} {K : NNReal} {f : ℝ → ℝ}
    (hch : IsChartAt Ω p c r h K f) (hp : p ∈ frontier Ω) {z : ℂ} (hzΩ : z ∈ Ω)
    (hz : ‖z - p‖ < min r h / 4) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) (hth : t ≤ h / 3) :
    signedDist Ω z + t / (2 * (K + 1)) ≤ signedDist Ω (z + t * (conj c * Complex.I)) := by
  rcases ht0.eq_or_lt with rfl | ht
  · simp
  let d := t * (conj c * Complex.I)
  let e := infDist z Ωᶜ
  let δ := t / (2 * ((K : ℝ) + 1))
  have hδ : 0 < δ := by positivity
  have he : e ≤ ‖z - p‖ := infDist_compl_le_of_frontier hΩo hp
  have hball : ball (z + d) (e + δ) ⊆ Ω := by
    intro q hq
    obtain ⟨x, hx, hs⟩ := split_shifted_ball infDist_nonneg hδ hq
    have hxΩ := hx.elim (ball_infDist_compl_subset ·) (· ▸ hzΩ)
    have hxp : ‖x - p‖ < min r h / 2 := by
      rcases hx with hx | rfl
      · rw [mem_ball, dist_eq_norm] at hx
        linarith [norm_sub_le_norm_sub_add_norm_sub x z p]
      grind
    rw [mem_ball, dist_eq_norm] at hs
    simpa using chart_shift_mem hch ht htr hth hxΩ hxp hs.le
  rw [signedDist_of_mem hzΩ, signedDist_of_mem (hball (mem_ball_self (add_pos_of_nonneg_of_pos infDist_nonneg hδ)))]
  exact add_dist_le_of_ball_subset hΩu (by simpa using hball)

/-- Outside the domain the same ball comparison runs in reverse. -/
lemma signedDist_add_le_of_chart_notMem {Ω : Set ℂ} (hΩne : Ω.Nonempty)
    {p c : ℂ} {r h : ℝ} {K : NNReal} {f : ℝ → ℝ}
    (hch : IsChartAt Ω p c r h K f) (hp : p ∈ frontier Ω) {z : ℂ} {t : ℝ}
    (hzΩ : z ∉ Ω) (hwΩ : z + t * (conj c * Complex.I) ∉ Ω)
    (hz : ‖z - p‖ < min r h / 10) (ht0 : 0 ≤ t) (htr : t ≤ min r h / 10) :
    signedDist Ω z + t / (2 * (K + 1)) ≤ signedDist Ω (z + t * (conj c * Complex.I)) := by
  rcases ht0.eq_or_lt with rfl | ht
  · simp
  let d := t * (conj c * Complex.I)
  let w := z + d
  let e := infDist w Ω
  let δ := t / (2 * ((K : ℝ) + 1))
  have hδ : 0 < δ := by positivity
  have hδt : δ ≤ t / 2 := by
    dsimp [δ]
    apply div_le_div_of_nonneg_left ht.le <;> nlinarith [K.coe_nonneg]
  have hd : ‖d‖ = t := by simp [d, hch.1, abs_of_pos ht]
  have he : e ≤ ‖z - p‖ + t := calc
    _ ≤ ‖w - p‖ := infDist_le_of_frontier hp
    _ = ‖(z - p) + d‖ := by congr 1; ring
    _ ≤ _ := hd ▸ norm_add_le _ _
  have hb : ball z (e + δ) ⊆ Ωᶜ := by
    intro q hq hqΩ
    have hq' : q ∈ ball (w + -d) (e + δ) := by aesop
    obtain ⟨x, hx, hs⟩ := split_shifted_ball infDist_nonneg hδ hq'
    have hxΩ := hx.elim (ball_infDist_subset_compl ·) (· ▸ hwΩ)
    rw [mem_ball, dist_eq_norm] at hq hs
    have hqp : ‖q - p‖ < min r h / 2 := by
      linarith [norm_sub_le_norm_sub_add_norm_sub q z p]
    have hs' : ‖x - q - d‖ ≤ δ := by
      rw [show x - q - d = -(q - x - -d) by abel, norm_neg]
      gcongr
    have hmem := chart_shift_mem hch ht (by grind)
      (by grind) hqΩ hqp hs'
    simp_all
  rw [signedDist_of_notMem hzΩ, signedDist_of_notMem hwΩ]
  have := add_dist_le_of_ball_subset hΩne hb
  change -infDist z Ω + δ ≤ -e
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
  have hr := hch.2.1
  have hh := hch.2.2.1
  have hmin := lt_min hr hh
  have hK0 := K.2
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
  apply @signedDist_add_le_of_chart_notMem <;> assumption
  -- mixed case: cross the boundary at the last time `t₁` outside `Ω`
  set S : Set ℝ := {s | s ∈ Icc 0 t ∧ z + s * n ∉ Ω}
  have hSc : IsClosed S := by
    refine isClosed_Icc.inter ?_
    exact hΩo.isClosed_compl.preimage (by fun_prop)
  have hS0 : (0 : ℝ) ∈ S := ⟨⟨le_rfl, ht0⟩, by simp_all⟩
  have hSb : BddAbove S := ⟨t, fun s hs => hs.1.2⟩
  set t₁ := sSup S
  have ht₁S := hSc.csSup_mem ⟨0, hS0⟩ hSb
  have ht₁0 := ht₁S.1.1
  have ht₁t := ht₁S.1.2
  have hlt := lt_of_le_of_ne ht₁t (fun h => ht₁S.2 (h ▸ hwΩ))
  -- outside part
  have h1 :=
    signedDist_add_le_of_chart_notMem hΩne hch hp hzΩ ht₁S.2 hz ht₁0 (by linarith)
  have h1' := signedDist_nonpos_of_notMem ht₁S.2
  -- inside part: from every later time
  have h2 : ∀ s ∈ Ioc t₁ t, (t - s) / (2 * (K + 1)) ≤ signedDist Ω (z + t * n) := by
    intro s hs
    have hsΩ : z + s * n ∈ Ω := by
      by_contra hc'
      exact absurd (le_csSup hSb ⟨⟨by grind, hs.2⟩, hc'⟩) (not_le.mpr hs.1)
    have hm := signedDist_add_le_of_chart_mem hΩo hΩu hch hp hsΩ
      (by grind) (t := t - s) (by simp_all)
      (by grind) (by grind)
    have heq : z + s * n + ((t - s : ℝ) : ℂ) * n = z + t * n := by push_cast; ring
    rw [heq] at hm
    have := signedDist_pos_of_mem hΩo hΩu hsΩ
    linarith
  have h2' : (t - t₁) / (2 * (K + 1)) ≤ signedDist Ω (z + t * n) := by
    have hcont : ContinuousWithinAt (fun s : ℝ => (t - s) / (2 * (K + 1))) (Ioc t₁ t) t₁ :=
      (by fun_prop : Continuous fun s : ℝ => (t - s) / (2 * (K + 1))).continuousWithinAt
    have hcl : t₁ ∈ closure (Ioc t₁ t) := by
      rw [closure_Ioc hlt.ne]; trivial
    exact ContinuousWithinAt.closure_le hcl hcont continuousWithinAt_const
      (fun s hs => h2 s hs)
  have : t / (2 * (K + 1)) = t₁ / (2 * (K + 1)) + (t - t₁) / (2 * (K + 1)) := by ring
  linarith

end PolyaNeumann

end
