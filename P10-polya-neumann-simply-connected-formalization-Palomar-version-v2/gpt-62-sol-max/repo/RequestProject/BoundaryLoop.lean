module

public import RequestProject.BoundaryWalk

/-!
# The boundary walk closes up into a Lipschitz Jordan curve

For a bounded Lipschitz domain, the boundary walk (`walk`) eventually revisits a point
(`WalkData.exists_pair`, by compactness of `∂Ω`), hence returns to its starting point
(`WalkData.exists_return`, by backward uniqueness of the walk, which comes from consistency of
orientation). Stopping at the first return gives a closed Lipschitz curve, injective before the
return (`WalkData.exists_loop`), whose image is open and closed in `∂Ω`
(`WalkData.image_eq`). Hence, when `∂Ω` is connected, it is a single Lipschitz Jordan curve
(`exists_jordanParam_of_isPreconnected_frontier`).
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

lemma IsChartAt.center_mem_box {Ω : Set ℂ} {p c : ℂ} {r h : ℝ} {K : NNReal} {f : ℝ → ℝ}
    (hch : IsChartAt Ω p c r h K f) : p ∈ chartBox p c r h := by
  simp [chartBox, hch.2.1, hch.2.2.1]

section Loop

variable {Ω : Set ℂ} {ρ H : ℝ} {K : NNReal} {ch : ℂ → ℂ × (ℝ → ℝ)} {ℓ : ℝ} {p₀ : ℂ}

section

variable (hw : WalkData Ω ρ H K ch ℓ p₀)
include hw

lemma WalkData.ρ_pos  : 0 < ρ := hw.ℓ_pos.trans hw.ℓ_lt

/-- The walk stays in an open box for nearby times. -/
lemma WalkData.eventually_box  {s : ℝ} {p c : ℂ} {r h : ℝ}
    (hbox : walk ch ℓ p₀ s ∈ chartBox p c r h) :
    ∃ ε > 0, ∀ s' ∈ Icc (s - ε) (s + ε), walk ch ℓ p₀ s' ∈ chartBox p c r h := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp
    ((isOpen_chartBox p c r h).preimage hw.continuous_walk) s hbox
  refine ⟨δ / 2, by positivity, fun s' hs' => hball ?_⟩
  grind [mem_ball, Real.dist_eq, abs_lt]

private lemma WalkData.local_chart_interval {s δ : ℝ} (hs : 0 ≤ s) (hδ : 0 < δ)
    {p c : ℂ} {r h : ℝ} {K' : NNReal} {f : ℝ → ℝ} (hch : IsChartAt Ω p c r h K' f)
    (hbox : walk ch ℓ p₀ s ∈ chartBox p c r h) :
    ∃ ε, 0 < ε ∧ ε ≤ δ ∧ StrictMonoOn (walkX ch ℓ p₀ p c) (Icc (s - ε) (s + ε)) ∧
      MapsTo (walk ch ℓ p₀) (Icc (s - ε) (s + ε)) (chartBox p c r h) := by
  obtain ⟨a, ha, hm⟩ := hw.walk_local_strictMono hs hch hbox
  obtain ⟨b, hb, hB⟩ := hw.eventually_box hbox
  refine ⟨min δ (min a b), by positivity, min_le_left _ _, hm.mono ?_, fun x hx => hB x ?_⟩ <;> grind

/-- The walk is locally injective. -/
lemma WalkData.locally_injective  {s : ℝ} (hs : 0 ≤ s) :
    ∃ ε > 0, InjOn (walk ch ℓ p₀) (Icc (s - ε) (s + ε)) := by
  have hP := hw.walk_mem_frontier (t := s) (by linarith [hw.ρ_pos])
  have hch := hw.chart _ hP
  obtain ⟨ε, hε, hmono⟩ := hw.walk_local_strictMono hs hch hch.center_mem_box
  refine ⟨ε, hε, fun a ha b hb hab => hmono.injOn ha hb ?_⟩
  simp [walkX, hab]

/-- **Return to the start.** If the walk revisits a point, it returns to its starting point. -/
theorem WalkData.exists_return  {s₀ t₀ : ℝ} (hs₀ : 0 ≤ s₀)
    (hst : s₀ < t₀) (heq : walk ch ℓ p₀ s₀ = walk ch ℓ p₀ t₀) :
    ∃ T, 0 < T ∧ T ≤ t₀ ∧ walk ch ℓ p₀ T = walk ch ℓ p₀ 0 := by
  have hρ := hw.ρ_pos
  let γ := walk ch ℓ p₀
  have hc : Continuous γ := hw.continuous_walk
  let S : Set (ℝ × ℝ) := (Icc 0 t₀ ×ˢ Icc 0 t₀) ∩ {p | p.1 ≤ p.2 ∧ γ p.1 = γ p.2}
  have hS : IsClosed S := (isClosed_Icc.prod isClosed_Icc).inter
    ((isClosed_le continuous_fst continuous_snd).inter
      (isClosed_eq (hc.comp continuous_fst) (hc.comp continuous_snd)))
  let A : Set (ℝ × ℝ) := {p | p ∈ S ∧ p.1 ≠ p.2}
  have hAc : IsClosed A := by
    refine isClosed_of_closure_subset fun ⟨s,t⟩ hp => ?_
    have hs := closure_minimal (show A ⊆ S from fun p hp => hp.1) hS hp
    refine ⟨hs, ?_⟩
    intro he
    change s = t at he
    subst t
    have hs0 : 0 ≤ s := hs.1.1.1
    obtain ⟨ε, hε, hinj⟩ := hw.locally_injective hs0
    have hN : Icc (s - ε) (s + ε) ∈ 𝓝 s := Icc_mem_nhds (by linarith) (by linarith)
    obtain ⟨p, hpp, hpA⟩ := (mem_closure_iff_nhds.mp hp _ (prod_mem_nhds hN hN))
    exact hpA.2 (hinj hpp.1 hpp.2 hpA.1.2.2)
  have hAK : IsCompact A := (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hAc
    (fun p hp => hp.1.1)
  obtain ⟨⟨s₁,t₁⟩, hp, hmin⟩ := hAK.exists_isMinOn
    (show A.Nonempty from ⟨(s₀,t₀), ⟨⟨⟨hs₀,hst.le⟩,⟨hs₀.trans hst.le,le_rfl⟩⟩, hst.le, heq⟩, hst.ne⟩)
    continuous_fst.continuousOn
  have hs₁0 : 0 ≤ s₁ := hp.1.1.1.1
  have ht₁t : t₁ ≤ t₀ := hp.1.1.2.2
  have hlt : s₁ < t₁ := lt_of_le_of_ne hp.1.2.1 hp.2
  have hγeq : γ s₁ = γ t₁ := hp.1.2.2
  by_cases hs₁pos : 0 < s₁
  swap
  · have hs : s₁ = 0 := by linarith
    exact ⟨t₁, hs ▸ hlt, ht₁t, (hs ▸ hγeq).symm⟩
  exfalso
  -- backward step at the pair `(s₁, t₁)`
  set P := γ s₁ with hP
  have hPf : P ∈ frontier Ω := hw.walk_mem_frontier (by linarith)
  have hch := hw.chart P hPf
  set c := (ch P).1
  have hboxs : γ s₁ ∈ chartBox P c ρ H := hch.center_mem_box
  have hboxt : γ t₁ ∈ chartBox P c ρ H := by simp_all
  obtain ⟨a, ha, ha', hm, hb⟩ := hw.local_chart_interval hs₁0 (show 0 < s₁ / 2 by linarith) hch hboxs
  obtain ⟨b, hb0, hb', hn, hbox⟩ := hw.local_chart_interval (by linarith)
    (show 0 < (t₁ - s₁) / 2 by linarith) hch hboxt
  let g := walkX ch ℓ p₀ P c
  have hgst : g s₁ = g t₁ := congrArg (fun z => (c * (z - P)).re) hγeq
  have hL : g (t₁ - b) < g s₁ := by
    rw [hgst]; exact hn ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  have hev : ∀ᶠ s in 𝓝 s₁, g (t₁ - b) < g s :=
    continuousAt_const.eventually_lt (hw.continuous_walkX P c).continuousAt hL
  obtain ⟨s, hsL, hs⟩ := ((eventually_nhdsWithin_of_eventually_nhds hev).and
    (Ioo_mem_nhdsLT (show s₁ - a < s₁ by linarith))).exists
  have hsi : s ∈ Icc (s₁ - a) (s₁ + a) := ⟨hs.1.le, by linarith [hs.2]⟩
  have hs0 : 0 ≤ s := by linarith [hs.1]
  obtain ⟨t, ht, htγ⟩ := hw.capture (α := t₁ - b) (β := t₁) (by linarith) (by linarith) hch
    (fun u hu => hbox ⟨hu.1, by linarith [hu.2]⟩) (hw.walk_mem_frontier (by linarith))
    (hb hsi) hsL.le (by change g s ≤ g t₁; rw [← hgst]; exact (hm hsi ⟨by linarith, by linarith⟩ hs.2).le)
  have hst' : s < t := by linarith [hs.2, ht.1]
  have htt₀ := ht.2.trans ht₁t
  have hpair : (s,t) ∈ A := ⟨⟨⟨⟨hs0,hst'.le.trans htt₀⟩,⟨hs0.trans hst'.le,htt₀⟩⟩,
    hst'.le, htγ.symm⟩, hst'.ne⟩
  exact (not_lt_of_ge (hmin hpair)) hs.2

/-- **The first return.** If the walk revisits a point, there is a first return time `T > 0` to
the starting point, and the walk is injective on `[0, T)`. -/
theorem WalkData.exists_loop  {s₀ t₀ : ℝ} (hs₀ : 0 ≤ s₀)
    (hst : s₀ < t₀) (heq : walk ch ℓ p₀ s₀ = walk ch ℓ p₀ t₀) :
    ∃ T, 0 < T ∧ walk ch ℓ p₀ T = walk ch ℓ p₀ 0 ∧ InjOn (walk ch ℓ p₀) (Ico 0 T) := by
  obtain ⟨ε₀, hε₀, hinj₀⟩ := hw.locally_injective (s := 0) le_rfl
  set S : Set ℝ := {t | ε₀ ≤ t ∧ walk ch ℓ p₀ t = walk ch ℓ p₀ 0} with hS
  have hmemS : ∀ T, 0 < T → walk ch ℓ p₀ T = walk ch ℓ p₀ 0 → T ∈ S := fun T hT hTeq => by
    refine ⟨not_lt.mp fun hlt => ?_, hTeq⟩
    have := hinj₀ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hTeq
    linarith
  obtain ⟨T₁, hT₁, -, hT₁eq⟩ := hw.exists_return hs₀ hst heq
  have hSne : S.Nonempty := ⟨T₁, hmemS T₁ hT₁ hT₁eq⟩
  have hSbdd : BddBelow S := ⟨ε₀, fun t ht => ht.1⟩
  have hScl : IsClosed S :=
    (isClosed_le continuous_const continuous_id).inter
      (isClosed_eq hw.continuous_walk continuous_const)
  set T := sInf S
  have hTS := hScl.csInf_mem hSne hSbdd
  refine ⟨T, by grind, hTS.2, fun a ha b hb hab => ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨T', hT', hT'b, hT'eq⟩ := hw.exists_return ha.1 hlt hab
    have := csInf_le hSbdd (hmemS T' hT' hT'eq)
    grind
  · obtain ⟨T', hT', hT'a, hT'eq⟩ := hw.exists_return hb.1 hlt hab.symm
    have := csInf_le hSbdd (hmemS T' hT' hT'eq)
    grind

/-- **The walk revisits a point**, by compactness of the boundary. Here the step `ℓ` is small
compared with the uniform chart size. -/
theorem WalkData.exists_pair  (hcpt : IsCompact (frontier Ω))
    (hℓsmall : (1 + K) * ℓ ≤ min ρ H / 2) :
    ∃ s₀ t₀, 0 ≤ s₀ ∧ s₀ < t₀ ∧ walk ch ℓ p₀ s₀ = walk ch ℓ p₀ t₀ := by
  have hℓ := hw.ℓ_pos
  have hK1 : (0 : ℝ) < 1 + K := by positivity
  set q : ℕ → ℂ := walkPt ch ℓ p₀ with hq
  obtain ⟨P, hPf, φ, hφ, hqφ⟩ := hcpt.tendsto_subseq (x := q) hw.walkPt_mem
  have hch := hw.chart P hPf
  set c := (ch P).1
  set m₀ := min ρ H with hm₀
  have hm₀pos : 0 < m₀ := lt_min hw.ρ_pos (by linarith [hch.2.2.1])
  have hball : ball P m₀ ⊆ chartBox P c ρ H := ball_subset_chartBox hch.1
  set δ := min (m₀ / 4) (ℓ / (2 * (1 + K))) with hδ
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hqφ δ hδpos
  set n := φ (N + 1) with hn
  set m := φ (N + 3) with hm
  have hn1 : 1 ≤ n := by
    show 1 ≤ φ (N + 1)
    have := hφ (show N < N + 1 by omega); omega
  have hmn : n + 2 ≤ m := by
    have h1 := hφ (show N + 1 < N + 2 by omega)
    have h2 := hφ (show N + 2 < N + 3 by omega)
    omega
  have hqn : dist (q n) P < δ := hN (N + 1) (by omega)
  have hqm : dist (q m) P < δ := hN (N + 3) (by omega)
  have hwn : walk ch ℓ p₀ (n * ℓ) = q n := by
    have := hw.walk_eq n (u := 0) ⟨le_rfl, hℓ.le⟩
    rw [add_zero] at this
    rw [this, hw.stepCurve_zero (hw.walkPt_mem n)]
  have hwm : walk ch ℓ p₀ (m * ℓ) = q m := by
    have := hw.walk_eq m (u := 0) ⟨le_rfl, hℓ.le⟩
    rw [add_zero] at this
    rw [this, hw.stepCurve_zero (hw.walkPt_mem m)]
  have hL := hw.lipschitzWith_walk
  -- the walk around time `n ℓ` stays in the chart box at `P`
  have hbox : ∀ s ∈ Icc ((n : ℝ) * ℓ - ℓ) (n * ℓ + ℓ), walk ch ℓ p₀ s ∈ chartBox P c ρ H := by
    intro s hs
    refine hball ?_
    rw [mem_ball]
    have h1 : dist (walk ch ℓ p₀ s) (walk ch ℓ p₀ (n * ℓ)) ≤ (1 + K) * dist s (n * ℓ) := by
      have := hL.dist_le_mul s (n * ℓ); assumption
    have h2 : dist s (n * ℓ) ≤ ℓ := by
      rw [Real.dist_eq, abs_le]; grind
    calc dist (walk ch ℓ p₀ s) P ≤ dist (walk ch ℓ p₀ s) (walk ch ℓ p₀ (n * ℓ)) +
          dist (walk ch ℓ p₀ (n * ℓ)) P := dist_triangle _ _ _
      _ < (1 + K) * ℓ + m₀ / 4 := by
          rw [hwn] at h1 ⊢
          have := mul_le_mul_of_nonneg_left h2 hK1.le
          have := min_le_left (m₀ / 4) (ℓ / (2 * (1 + K)))
          linarith
      _ < m₀ := by linarith
  have hα : (0 : ℝ) ≤ n * ℓ - ℓ := by
    have : (1 : ℝ) ≤ n := by norm_cast
    nlinarith
  have hmono := hw.strictMonoOn_walkX hα hch hbox
  set g := walkX ch ℓ p₀ P c with hg
  have hfr : ∀ s, 0 ≤ s → walk ch ℓ p₀ s ∈ frontier Ω := fun s hs =>
    hw.walk_mem_frontier (by grind)
  -- abscissa increments over one step on each side
  have hdist : ∀ s₁ s₂, s₁ ∈ Icc ((n : ℝ) * ℓ - ℓ) (n * ℓ + ℓ) →
      s₂ ∈ Icc ((n : ℝ) * ℓ - ℓ) (n * ℓ + ℓ) → s₁ < s₂ →
      ‖walk ch ℓ p₀ s₂ - walk ch ℓ p₀ s₁‖ ≤ (1 + K) * (g s₂ - g s₁) := by
    intro s₁ s₂ hs₁ hs₂ h12
    have := norm_sub_le_of_frontier hw.isOpen hch (hfr s₂ (by linarith [hs₂.1]))
      (hfr s₁ (by linarith [hs₁.1])) (hbox s₂ hs₂) (hbox s₁ hs₁)
    have hlt : g s₁ < g s₂ := hmono hs₁ hs₂ h12
    rwa [abs_of_pos (by positivity)] at this
  have hright : ℓ / (1 + K) ≤ g (n * ℓ + ℓ) - g (n * ℓ) := by
    have h1 := hw.le_norm_walk_sub n (u := 0) (u' := ℓ) ⟨le_rfl, hℓ.le⟩ ⟨hℓ.le, le_rfl⟩
    rw [add_zero, sub_zero, abs_of_pos hℓ] at h1
    have h2 := hdist (n * ℓ) (n * ℓ + ℓ) ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩
      (by linarith)
    rw [div_le_iff₀ hK1]; nlinarith
  have hleft : ℓ / (1 + K) ≤ g (n * ℓ) - g (n * ℓ - ℓ) := by
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h1 := hw.le_norm_walk_sub k (u := 0) (u' := ℓ) ⟨le_rfl, hℓ.le⟩ ⟨hℓ.le, le_rfl⟩
    rw [add_zero, abs_of_pos (by linarith)] at h1
    have e1 : (k : ℝ) * ℓ + ℓ = n * ℓ := by rw [hk]; push_cast; ring
    have e2 : (k : ℝ) * ℓ = n * ℓ - ℓ := by rw [hk]; push_cast; ring
    rw [e1, e2, sub_zero] at h1
    have h2 := hdist (n * ℓ - ℓ) (n * ℓ) ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩
      (by linarith)
    rw [div_le_iff₀ hK1]; nlinarith
  -- the abscissa of `q m` is close to that of `q n`
  have hqmf : q m ∈ frontier Ω := hw.walkPt_mem m
  have hqmb : q m ∈ chartBox P c ρ H := hball (lt_of_lt_of_le hqm (by
    have := min_le_left (m₀ / 4) (ℓ / (2 * (1 + K))); linarith))
  have hXclose : |(c * (q m - P)).re - g (n * ℓ)| ≤ 2 * δ := by
    have hgn : g (n * ℓ) = (c * (q n - P)).re := by simp only [hg, walkX, hwn]
    rw [hgn, ← Complex.sub_re, ← mul_sub, sub_sub_sub_cancel_right]
    refine le_trans (Complex.abs_re_le_norm _) ?_
    rw [norm_mul, hch.1, one_mul]
    have := dist_triangle (q m) P (q n)
    rw [dist_comm P, dist_eq_norm] at this
    linarith
  have h2δ : 2 * δ ≤ ℓ / (1 + K) := by
    have := min_le_right (m₀ / 4) (ℓ / (2 * (1 + K)))
    have e : ℓ / (2 * (1 + K)) = ℓ / (1 + K) / 2 := by field_simp
    linarith
  rw [abs_le] at hXclose
  obtain ⟨s, hs, hseq⟩ := hw.capture (α := n * ℓ - ℓ) (β := n * ℓ + ℓ)
    (by linarith [hw.ρ_pos]) (by linarith) hch hbox hqmf hqmb
    (by linarith) (by linarith)
  refine ⟨s, m * ℓ, by linarith [hs.1], ?_, by rw [hseq, hwm]⟩
  have : ((n : ℝ) + 2) ≤ m := by norm_cast
  nlinarith [hs.2]

end

lemma isOpen_abscissa_band (p c : ℂ) (a b : ℝ) :
    IsOpen {w : ℂ | a < (c * (w - p)).re ∧ (c * (w - p)).re < b} := have hg := Continuous.comp' Complex.continuous_re (Continuous.const_mul (Continuous.fun_sub continuous_id' continuous_const) c); IsOpen.inter (isOpen_lt continuous_const hg) (isOpen_lt hg continuous_const)

/-- **The loop fills the boundary.** If `∂Ω` is preconnected and the walk returns to its start at
time `T > 0`, then the walk on `[0, T]` covers `∂Ω`. -/
theorem WalkData.image_eq (hw : WalkData Ω ρ H K ch ℓ p₀) {T : ℝ} (hT : 0 < T)
    (hTeq : walk ch ℓ p₀ T = walk ch ℓ p₀ 0) (hconn : IsPreconnected (frontier Ω)) :
    walk ch ℓ p₀ '' Icc 0 T = frontier Ω := by
  have hρ := hw.ρ_pos
  set γ := walk ch ℓ p₀ with hγ
  set Im := γ '' Icc 0 T with hIm
  have hsub : Im ⊆ frontier Ω := by
    rintro _ ⟨t, ht, rfl⟩; exact hw.walk_mem_frontier (by grind)
  refine subset_antisymm hsub ?_
  have hImc : IsClosed Im := (isCompact_Icc.image hw.continuous_walk).isClosed
  -- every point of the loop has a neighbourhood whose boundary points are on the loop
  have hloc : ∀ t ∈ Icc 0 T, ∃ V : Set ℂ, IsOpen V ∧ γ t ∈ V ∧ frontier Ω ∩ V ⊆ Im := by
    intro t ht
    have hPf := hsub ⟨t, ht, rfl⟩
    set P := γ t
    have hch := hw.chart P hPf
    set c := (ch P).1
    set g := walkX ch ℓ p₀ P c with hg
    have hPb := hch.center_mem_box
    let tL := if t = 0 then T else t
    let tR := if t = T then 0 else t
    have hL : tL ∈ Ioc 0 T ∧ γ tL = P := by
      by_cases he : t = 0 <;> simp only [tL, if_pos, he, P] <;> grind
    have hR : tR ∈ Ico 0 T ∧ γ tR = P := by
      by_cases he : t = T <;> simp only [tR, if_pos, he, P] <;> grind
    obtain ⟨a, ha, ha', hm, hboxL⟩ := hw.local_chart_interval hL.1.1.le hL.1.1 hch (hL.2 ▸ hPb)
    obtain ⟨b, hb, hb', hn, hboxR⟩ := hw.local_chart_interval hR.1.1 (sub_pos.mpr hR.1.2) hch (hR.2 ▸ hPb)
    let x (w : ℂ) := (c * (w - P)).re
    have eL : g tL = x P := congrArg x hL.2
    have eR : g tR = x P := congrArg x hR.2
    have hlt : g (tL - a) < x P := by
      rw [← eL]; exact hm ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
    have hgt : x P < g (tR + b) := by
      rw [← eR]; exact hn ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
    refine ⟨chartBox P c ρ H ∩ {w | g (tL - a) < x w ∧ x w < g (tR + b)},
      (isOpen_chartBox _ _ _ _).inter (isOpen_abscissa_band _ _ _ _), ⟨hPb, hlt, hgt⟩, ?_⟩
    rintro w ⟨hwf, hwb, h1, h2⟩
    rcases le_total (x w) (x P) with h | h
    · obtain ⟨s, hs, heq⟩ := hw.capture (α := tL - a) (β := tL) (by linarith) (by linarith) hch
        (fun u hu => hboxL ⟨hu.1, by linarith [hu.2]⟩) hwf hwb h1.le (by change x w ≤ g tL; rwa [eL])
      exact ⟨s, ⟨by linarith [hs.1], hs.2.trans hL.1.2⟩, heq⟩
    · obtain ⟨s, hs, heq⟩ := hw.capture (α := tR) (β := tR + b) (by linarith [hR.1.1]) (by linarith) hch
        (fun u hu => hboxR ⟨by linarith [hu.1], hu.2⟩) hwf hwb (by change g tR ≤ x w; rwa [eR]) h2.le
      exact ⟨s, ⟨hR.1.1.trans hs.1, by linarith [hs.2]⟩, heq⟩
  choose! V hVo hVmem hVsub using hloc
  set U := ⋃ t ∈ Icc 0 T, V t with hU
  have hUo := isOpen_biUnion fun t ht => hVo t ht
  have hcover : frontier Ω ⊆ U ∪ Imᶜ := fun x hx => by
    by_cases hxI : x ∈ Im
    · obtain ⟨t, ht, rfl⟩ := hxI
      exact Or.inl (mem_biUnion ht (hVmem t ht))
    tauto
  have hdisj : frontier Ω ∩ (U ∩ Imᶜ) = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hx hxU hxI
    obtain ⟨t, ht, hxV⟩ := mem_iUnion₂.mp hxU
    exact hxI (hVsub t ht ⟨hx, hxV⟩)
  rcases (isPreconnected_iff_subset_of_disjoint.mp hconn) U Imᶜ hUo hImc.isOpen_compl hcover
    hdisj with h | h
  · intro x hx
    obtain ⟨t, ht, hxV⟩ := mem_iUnion₂.mp (h hx)
    tauto
  · exfalso
    have h0 : γ 0 ∈ Im := ⟨0, ⟨le_rfl, hT.le⟩, rfl⟩
    tauto

end Loop

/-- A Lipschitz closed curve on `[0, T]`, injective on `[0, T)`, reparametrized linearly to
`[0, 2π]` and extended periodically, gives a Lipschitz `2π`-periodic curve injective on
`[0, 2π)` with the same image. -/
theorem exists_periodic_of_loop {Γ : ℝ → ℂ} {K : NNReal} (hΓ : LipschitzWith K Γ) {T : ℝ}
    (hT : 0 < T) (hcl : Γ T = Γ 0) (hinj : InjOn Γ (Ico 0 T)) :
    ∃ γ : ℝ → ℂ, (∃ K', LipschitzWith K' γ) ∧ Function.Periodic γ (2 * π) ∧
      InjOn γ (Ico 0 (2 * π)) ∧ γ '' Icc 0 (2 * π) = Γ '' Icc 0 T := by
  let a : ℝ := T / (2 * π)
  have ha : 0 < a := div_pos hT Real.two_pi_pos
  have haT : a * (2 * π) = T := div_mul_cancel₀ _ Real.two_pi_pos.ne'
  let G : ℝ → ℂ := Γ ∘ (a * ·)
  have hGL : LipschitzWith (K * ‖a‖₊) G := hΓ.comp (lipschitzWith_smul a)
  have he : G (2 * π) = G 0 := by simp [G, haT, hcl]
  refine ⟨periodize G, ⟨_, lipschitzWith_periodizeOn hGL.lipschitzOnWith he⟩,
    periodic_periodize G, ?_, ?_⟩
  · have hm : MapsTo (a * ·) (Ico 0 (2 * π)) (Ico 0 T) := fun x hx =>
      ⟨mul_nonneg ha.le hx.1, haT ▸ mul_lt_mul_of_pos_left hx.2 ha⟩
    exact ((hinj.comp (OrderIso.mulLeft₀ a ha).injective.injOn hm).congr fun x hx =>
      (periodize_apply_of_mem hx).symm)
  · let e := OrderIso.mulLeft₀ a ha
    calc
      _ = G '' Icc 0 (2 * π) := image_congr (periodize_eqOn_Icc he)
      _ = Γ '' (e '' Icc 0 (2 * π)) := (image_image Γ (e : ℝ → ℝ) _).symm
      _ = _ := by rw [e.image_Icc]; simp [e, haT]

section

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
include Ω hb hL

/-- **A Lipschitz Jordan loop in the boundary.** A bounded Lipschitz domain has a Lipschitz
`2π`-periodic curve `γ`, injective on `[0, 2π)`, with image in `∂Ω`; if `∂Ω` is connected, the
image is all of `∂Ω`. -/
theorem exists_jordanLoop_frontier  :
    ∃ γ : ℝ → ℂ, (∃ K, LipschitzWith K γ) ∧ Function.Periodic γ (2 * π) ∧
      InjOn γ (Ico 0 (2 * π)) ∧ γ '' Icc 0 (2 * π) ⊆ frontier Ω ∧
      (IsPreconnected (frontier Ω) → γ '' Icc 0 (2 * π) = frontier Ω) := by
  obtain ⟨ρ, H, K, hρ, hH, hKρ, hcharts⟩ := exists_uniform_charts hb hL
  choose! c f hcf using hcharts
  set ch : ℂ → ℂ × (ℝ → ℝ) := fun p => (c p, f p) with hch
  obtain ⟨p₀, hp₀⟩ : (frontier Ω).Nonempty := by
    refine nonempty_frontier_iff.mpr ⟨hL.1.2.nonempty, fun huniv => ?_⟩
    have := hb
    rw [huniv] at this
    exact NormedSpace.unbounded_univ ℝ ℂ this
  have hK1 : (0 : ℝ) < 1 + K := by positivity
  set ℓ : ℝ := min ρ H / (2 * (1 + K)) with hℓ
  have hm := lt_min hρ hH
  have hℓpos : 0 < ℓ := by positivity
  have hℓρ : ℓ < ρ := by
    have : ℓ ≤ min ρ H / 2 := by
      rw [hℓ]; apply div_le_div_of_nonneg_left hm.le (by norm_num); simp
    grind
  have hw : WalkData Ω ρ H K ch ℓ p₀ :=
    ⟨hL.1.1, fun p hp => hcf p hp, hℓpos, hℓρ, hp₀⟩
  have hsmall : (1 + K) * ℓ ≤ min ρ H / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  obtain ⟨s₀, t₀, hs₀, hst, heq⟩ := hw.exists_pair (frontier_isCompact hb) hsmall
  obtain ⟨T, hT, hTeq, hinj⟩ := hw.exists_loop hs₀ hst heq
  obtain ⟨γ, hγL, hγp, hγi, hγim⟩ := exists_periodic_of_loop hw.lipschitzWith_walk hT hTeq hinj
  refine ⟨γ, hγL, hγp, hγi, ?_, fun hconn => by rw [hγim, hw.image_eq hT hTeq hconn]⟩
  rw [hγim]
  rintro _ ⟨t, ht, rfl⟩
  exact hw.walk_mem_frontier (by grind)

/-- **External theorem E3, boundary description, for connected boundaries.** If `Ω` is a bounded
Lipschitz domain whose boundary is connected, then `∂Ω` is a single Lipschitz Jordan curve: it
has a Lipschitz `2π`-periodic parametrization, injective on `[0, 2π)`, with image `∂Ω`. -/
theorem exists_jordanParam_of_isPreconnected_frontier 
    (hconn : IsPreconnected (frontier Ω)) :
    ∃ γ : ℝ → ℂ, (∃ K, LipschitzWith K γ) ∧ Function.Periodic γ (2 * π) ∧
      InjOn γ (Ico 0 (2 * π)) ∧ γ '' Icc 0 (2 * π) = frontier Ω := by
  obtain ⟨γ, hγL, hγp, hγi, -, hγim⟩ := exists_jordanLoop_frontier hb hL
  tauto

end

end PolyaNeumann
