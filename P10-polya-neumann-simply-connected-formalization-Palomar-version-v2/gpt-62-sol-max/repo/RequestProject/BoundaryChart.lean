module

public import RequestProject.JordanWinding

/-!
# Lipschitz charts of a planar boundary

Basic facts about the Lipschitz charts of a Lipschitz domain `Ω ⊂ ℂ`:

* graph points of a chart are boundary points (`chartPt_mem_frontier`), and boundary points in a
  chart box are graph points (`eq_chartPt_of_frontier`);
* recentering of a chart at a nearby boundary point (`isChartAt_recenter`) and uniform charts
  for bounded Lipschitz domains (`exists_uniform_charts`);
* a continuous function that is "strictly increasing from the left" at every point of an interval
  is strictly increasing (`strictMonoOn_of_local_left`);
* **consistency of orientation** (`chart_orient`): along the boundary, the abscissa of one chart
  is a strictly increasing function of the abscissa of any other chart (the domain lies on the
  left in both).
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

/-- A Lipschitz chart of `Ω` at `p`: after the rigid motion `w ↦ c (w - p)`, inside the box
`|x| < r`, `|y| < h`, the domain is the region above the graph of the `K`-Lipschitz function `f`
(with `f 0 = 0`, and the graph over `|x| < r` inside the box). -/
def IsChartAt (Ω : Set ℂ) (p c : ℂ) (r h : ℝ) (K : NNReal) (f : ℝ → ℝ) : Prop :=
  ‖c‖ = 1 ∧ 0 < r ∧ 0 < h ∧ LipschitzWith K f ∧ f 0 = 0 ∧ (∀ x : ℝ, |x| < r → |f x| < h) ∧
    ∀ w : ℂ, |(c * (w - p)).re| < r → |(c * (w - p)).im| < h →
      (w ∈ Ω ↔ f (c * (w - p)).re < (c * (w - p)).im)

lemma IsLipschitzDomain.exists_chart {Ω : Set ℂ} (hL : IsLipschitzDomain Ω) {p : ℂ}
    (hp : p ∈ frontier Ω) : ∃ (c : ℂ) (r h : ℝ) (K : NNReal) (f : ℝ → ℝ),
      IsChartAt Ω p c r h K f :=
  hL.2 p hp

/-- The graph point of a chart with abscissa `x`. -/
def chartPt (p c : ℂ) (f : ℝ → ℝ) (x : ℝ) : ℂ := p + conj c * ((x : ℂ) + (f x : ℂ) * Complex.I)

section

variable {p c : ℂ} (hc : ‖c‖ = 1) (f : ℝ → ℝ) (x : ℝ)
include p c hc f x

lemma mul_chartPt_sub  :
    c * (chartPt p c f x - p) = (x : ℂ) + (f x : ℂ) * Complex.I := by
  have : c * conj c = 1 := by
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
  simp  [chartPt, add_sub_cancel_left, ← mul_assoc, this, one_mul]

lemma re_mul_chartPt_sub  :
    (c * (chartPt p c f x - p)).re = x := by
  rw [mul_chartPt_sub hc]; simp

lemma im_mul_chartPt_sub  :
    (c * (chartPt p c f x - p)).im = f x := by
  rw [mul_chartPt_sub hc]; simp

end

lemma chartPt_zero {p c : ℂ} {f : ℝ → ℝ} (hf0 : f 0 = 0) : chartPt p c f 0 = p := by
  simp [chartPt, hf0]

lemma norm_mul_sub {c : ℂ} (hc : ‖c‖ = 1) (w p : ℂ) : ‖c * (w - p)‖ = ‖w - p‖ := by simp_all

section

variable {c p w w' : ℂ} (hc : ‖c‖ = 1)
include c p w w' hc

/-- A point is determined by its chart coordinates. -/
lemma eq_of_mul_sub_eq  (h : c * (w - p) = c * (w' - p)) :
    w = w' := by aesop

lemma eq_of_re_im_eq  (hre : (c * (w - p)).re = (c * (w' - p)).re)
    (him : (c * (w - p)).im = (c * (w' - p)).im) : w = w' :=
  eq_of_mul_sub_eq hc (Complex.ext hre him)

end

/-- The graph map of a chart is `(1 + K)`-Lipschitz. -/
lemma lipschitzWith_chartPt {p c : ℂ} (hc : ‖c‖ = 1) {K : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith K f) : LipschitzWith (1 + K) (chartPt p c f) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hcc : ‖conj c‖ = 1 := by simp_all
  simp only [chartPt, dist_eq_norm, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, hcc, one_mul]
  have h1 : ‖((x : ℂ) + (f x : ℂ) * Complex.I) - ((y : ℂ) + (f y : ℂ) * Complex.I)‖ ≤
      ‖((x - y : ℝ) : ℂ)‖ + ‖((f x - f y : ℝ) : ℂ) * Complex.I‖ := by
    have : ((x : ℂ) + (f x : ℂ) * Complex.I) - ((y : ℂ) + (f y : ℂ) * Complex.I) =
        ((x - y : ℝ) : ℂ) + ((f x - f y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this]; exact norm_add_le _ _
  have h2 : |f x - f y| ≤ K * |x - y| := by
    have := hf.dist_le_mul x y; assumption
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs] at h1
  push_cast
  rw [Real.norm_eq_abs]
  nlinarith

lemma continuous_chartPt {p c : ℂ} {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (chartPt p c f) := by
  unfold chartPt; fun_prop

section

variable (p c : ℂ) (r h : ℝ)
include p c r h

/-- The open chart box. -/
def chartBox  : Set ℂ :=
  {w | |(c * (w - p)).re| < r ∧ |(c * (w - p)).im| < h}

lemma isOpen_chartBox  : IsOpen (chartBox p c r h) := by
  have hg : Continuous fun w : ℂ => c * (w - p) := by fun_prop
  exact (isOpen_lt (Complex.continuous_re.comp hg).abs continuous_const).inter
    (isOpen_lt (Complex.continuous_im.comp hg).abs continuous_const)

end

/-- A ball around the centre inside the box. -/
lemma ball_subset_chartBox {p c : ℂ} (hc : ‖c‖ = 1) {r h : ℝ} :
    ball p (min r h) ⊆ chartBox p c r h := by
  intro w hw
  rw [mem_ball, dist_eq_norm] at hw
  have hn := norm_mul_sub hc w p
  refine ⟨lt_of_le_of_lt (Complex.abs_re_le_norm _) ?_,
    lt_of_le_of_lt (Complex.abs_im_le_norm _) ?_⟩
  all_goals simp_all

private lemma vertical_chart_coordinates (q c d : ℂ) (z : ℂ) (s : ℝ) :
    d * (z + (s : ℂ) * (conj c * Complex.I) - q) =
      d * (z - q) + (s : ℂ) * (d * conj c * Complex.I) := by ring

private lemma tendsto_vertical_chart (z c : ℂ) :
    Tendsto (fun s : ℝ => z + (s : ℂ) * (conj c * Complex.I)) (𝓝[>] 0) (𝓝 z) := by
  have h : Continuous fun s : ℝ => z + (s : ℂ) * (conj c * Complex.I) := by fun_prop
  have ht := h.tendsto 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at ht
  exact ht.mono_left nhdsWithin_le_nhds

section

variable {Ω : Set ℂ} (hΩo : IsOpen Ω) {p c : ℂ} {r h : ℝ} {K : NNReal} {f : ℝ → ℝ} (hch : IsChartAt Ω p c r h K f)

include hch in
private lemma eventually_vertical_mem {x : ℝ} (hx : |x| < r) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, chartPt p c f x + (s : ℂ) * (conj c * Complex.I) ∈ Ω := by
  obtain ⟨hc, -, -, -, -, hfb, hΩ⟩ := hch
  have hfx := hfb x hx
  have hcc : c * conj c = 1 := by simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
    (eventually_lt_nhds (show (0 : ℝ) < h - |f x| by linarith)), self_mem_nhdsWithin] with s hs hs0
  simp only [mem_Ioi] at hs0
  have hre : (c * (chartPt p c f x + (s : ℂ) * (conj c * Complex.I) - p)).re = x := by
    simp [vertical_chart_coordinates, mul_chartPt_sub hc, hcc]
  have him : (c * (chartPt p c f x + (s : ℂ) * (conj c * Complex.I) - p)).im = f x + s := by
    simp [vertical_chart_coordinates, mul_chartPt_sub hc, hcc]
  apply (hΩ _ (by rwa [hre]) (by rw [him, abs_lt]; grind)).2
  rw [hre, him]; linarith

include hΩo hch

/-- Graph points of a chart are boundary points. -/
lemma chartPt_mem_frontier {x : ℝ} (hx : |x| < r) : chartPt p c f x ∈ frontier Ω := by
  have ⟨hc, _, _, _, _, hfb, hΩ⟩ := hch
  rw [hΩo.frontier_eq]
  refine ⟨mem_closure_iff_nhds.mpr fun U hU => ?_, fun hm => ?_⟩
  · have hev : ∀ᶠ s : ℝ in 𝓝[>] 0, chartPt p c f x + (s : ℂ) * (conj c * Complex.I) ∈ U :=
      tendsto_vertical_chart (chartPt p c f x) c hU
    obtain ⟨s, hsU, hsΩ⟩ := (hev.and (eventually_vertical_mem hch hx)).exists
    exact ⟨_, hsU, hsΩ⟩
  · have := (hΩ _ (by rwa [re_mul_chartPt_sub hc]) (by rw [im_mul_chartPt_sub hc]; exact hfb x hx)).1 hm
    simpa [re_mul_chartPt_sub hc, im_mul_chartPt_sub hc] using this

/-- Boundary points in a chart box are graph points. -/
lemma eq_chartPt_of_frontier  {w : ℂ} (hw : w ∈ frontier Ω)
    (hbox : w ∈ chartBox p c r h) : w = chartPt p c f (c * (w - p)).re := by
  obtain ⟨hc, hr, hh, hf, hf0, hfb, hΩ⟩ := hch
  have hgr := chart_frontier_graph hΩo hf hΩ hw hbox.1 hbox.2
  refine eq_of_re_im_eq (p := p) hc ?_ ?_
  · rw [re_mul_chartPt_sub hc]
  · rw [im_mul_chartPt_sub hc, hgr]

/-- Two boundary points in a chart box with the same abscissa coincide. -/
lemma eq_of_frontier_of_re_eq  {w w' : ℂ} (hw : w ∈ frontier Ω)
    (hw' : w' ∈ frontier Ω) (hbox : w ∈ chartBox p c r h) (hbox' : w' ∈ chartBox p c r h)
    (hre : (c * (w - p)).re = (c * (w' - p)).re) : w = w' := by
  rw [eq_chartPt_of_frontier hΩo hch hw hbox, eq_chartPt_of_frontier hΩo hch hw' hbox', hre]

/-- Along the boundary inside a chart box, distances are controlled by abscissae. -/
lemma norm_sub_le_of_frontier  {w w' : ℂ} (hw : w ∈ frontier Ω)
    (hw' : w' ∈ frontier Ω) (hbox : w ∈ chartBox p c r h) (hbox' : w' ∈ chartBox p c r h) :
    ‖w - w'‖ ≤ (1 + K) * |(c * (w - p)).re - (c * (w' - p)).re| := by
  have h1 := (lipschitzWith_chartPt (p := p) hch.1 hch.2.2.2.1).dist_le_mul
    (c * (w - p)).re (c * (w' - p)).re
  rw [← eq_chartPt_of_frontier hΩo hch hw hbox, ← eq_chartPt_of_frontier hΩo hch hw' hbox',
    dist_eq_norm] at h1
  assumption

end

/-! ### Recentering and uniform charts -/

/-- Recentering a chart at a boundary point of the half box. -/
lemma isChartAt_recenter {Ω : Set ℂ} (hΩo : IsOpen Ω) {p c : ℂ} {r h : ℝ} {K : NNReal}
    {f : ℝ → ℝ} (hch : IsChartAt Ω p c r h K f) {q : ℂ} (hq : q ∈ frontier Ω)
    (hqr : |(c * (q - p)).re| < r / 2) (hqh : |(c * (q - p)).im| < h / 2)
    {ρ H : ℝ} {K' : NNReal} (hρ : 0 < ρ) (hH : 0 < H) (hρr : ρ ≤ r / 2) (hHh : H ≤ h / 2)
    (hKK : K ≤ K') (hKρ : (K' : ℝ) * ρ < H) :
    IsChartAt Ω q c ρ H K'
      (fun x => f (x + (c * (q - p)).re) - f (c * (q - p)).re) := by
  obtain ⟨hc, hr, hh, hf, hf0, hfb, hΩ⟩ := hch
  set X := (c * (q - p)).re with hX
  have hfK' := hf.weaken hKK
  have hlip : LipschitzWith K' (fun x => f (x + X) - f X) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have := hfK'.dist_le_mul (x + X) (y + X)
    simp_all
  refine ⟨hc, hρ, hH, hlip, by simp, fun x hx => ?_, fun w hw1 hw2 => ?_⟩
  · have := hlip.dist_le_mul x 0
    simp   at this
    calc |f (x + X) - f X| ≤ K' * |x| := this
      _ ≤ K' * ρ := mul_le_mul_of_nonneg_left hx.le K'.2
      _ < H := hKρ
  · have hY :=
      chart_frontier_graph hΩo hf hΩ hq (by linarith) (by linarith)
    have hsplit : c * (w - p) = c * (w - q) + c * (q - p) := by ring
    have hre : (c * (w - p)).re = (c * (w - q)).re + X := by simp_all
    have him : (c * (w - p)).im = (c * (w - q)).im + f X := by
      simp_all
    have h1 : |(c * (w - p)).re| < r := by
      rw [hre]; calc _ ≤ |(c * (w - q)).re| + |X| := abs_add_le _ _
        _ < r := by linarith
    have h2 : |(c * (w - p)).im| < h := by
      rw [him]; calc _ ≤ |(c * (w - q)).im| + |f X| := abs_add_le _ _
        _ < h := by grind
    rw [hΩ w h1 h2, hre, him]
    grind

lemma frontier_isCompact {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) : IsCompact (frontier Ω) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_frontier
    (hb.closure.subset frontier_subset_closure)

/-- **Uniform charts.** A bounded Lipschitz domain has charts at every boundary point with
uniform size `ρ × H` and uniform Lipschitz constant `K`, with `K ρ < H`. -/
theorem exists_uniform_charts {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) :
    ∃ (ρ H : ℝ) (K : NNReal), 0 < ρ ∧ 0 < H ∧ (K : ℝ) * ρ < H ∧
      ∀ p ∈ frontier Ω, ∃ (c : ℂ) (f : ℝ → ℝ), IsChartAt Ω p c ρ H K f := by
  have hΩo := hL.1.1
  choose! c r h K f hch using fun p (hp : p ∈ frontier Ω) => hL.exists_chart hp
  set U : ℂ → Set ℂ := fun p => chartBox p (c p) (r p / 2) (h p / 2) with hU
  have hUo : ∀ p, IsOpen (U p) := fun p => isOpen_chartBox _ _ _ _
  have hcover : frontier Ω ⊆ ⋃ p ∈ frontier Ω, U p := fun q hq => by
    refine mem_biUnion hq ?_
    obtain ⟨-, hr, hh, -⟩ := hch q hq
    simp [hU, chartBox, hr, hh]
  obtain ⟨t, htΩ, htfin, hcov⟩ := (frontier_isCompact hb).elim_finite_subcover_image
    (fun p _ => hUo p) hcover
  by_cases hte : t.Nonempty
  swap
  · -- empty boundary: any constants work
    refine ⟨1, 2, 0, one_pos, two_pos, by norm_num, fun p hp => ?_⟩
    have := hcov hp
    rw [Set.not_nonempty_iff_eq_empty.mp hte] at this
    simp at this
  set Kt : NNReal := htfin.toFinset.sup' (by simp_all) K with hKt
  set Ht : ℝ := htfin.toFinset.inf' (by simp_all) (fun p => h p / 2) with hHt
  set Rt : ℝ := htfin.toFinset.inf' (by simp_all) (fun p => r p / 2) with hRt
  have hHt0 : 0 < Ht := by
    rw [Finset.lt_inf'_iff]
    intro p hp
    have := (hch p (htΩ (by simp_all))).2.2.1
    linarith
  have hRt0 : 0 < Rt := by
    rw [Finset.lt_inf'_iff]
    intro p hp
    have := (hch p (htΩ (by simp_all))).2.1
    linarith
  set ρ : ℝ := min Rt (Ht / (2 * (Kt + 1))) with hρ
  have hρ0 : 0 < ρ := lt_min hRt0 (by positivity)
  have hKρ : (Kt : ℝ) * ρ < Ht := by
    have h1 : ρ ≤ Ht / (2 * (Kt + 1)) := min_le_right _ _
    have hK0 := Kt.2
    calc (Kt : ℝ) * ρ ≤ Kt * (Ht / (2 * (Kt + 1))) := mul_le_mul_of_nonneg_left h1 hK0
      _ < Ht := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
  refine ⟨ρ, Ht, Kt, hρ0, hHt0, hKρ, fun q hq => ?_⟩
  obtain ⟨p, hpt, hqU⟩ := mem_iUnion₂.mp (hcov hq)
  have hpt' : p ∈ htfin.toFinset := by simpa using hpt
  refine ⟨c p, _, isChartAt_recenter hΩo (hch p (htΩ hpt)) hq hqU.1 hqU.2 hρ0 hHt0
    (le_trans (min_le_left _ _) (Finset.inf'_le _ hpt')) (Finset.inf'_le _ hpt')
    (Finset.le_sup' K hpt') hKρ⟩

/-! ### Local monotonicity -/

/-- A continuous function on an order-connected set that is, at every point, strictly larger
than at all nearby points to the left, is strictly increasing. -/
lemma strictMonoOn_of_local_left {g : ℝ → ℝ} {J : Set ℝ} (hJ : J.OrdConnected)
    (hg : ContinuousOn g J)
    (hloc : ∀ y ∈ J, ∃ ε > 0, ∀ y' ∈ J, y - ε < y' → y' < y → g y' < g y) :
    StrictMonoOn g J := by
  intro y1 hy1 y2 hy2 h12
  have hsub := hJ.out hy1 hy2
  obtain ⟨m, hm, hmin⟩ := (isCompact_Icc (a := y1) (b := y2)).exists_isMinOn
    (nonempty_Icc.mpr h12.le) (hg.mono hsub)
  have key : ∀ m' ∈ Icc y1 y2, y1 < m' → ¬ IsMinOn g (Icc y1 y2) m' := by
    intro m' hm' hlt hmin'
    obtain ⟨ε, hε, hε'⟩ := hloc m' (hsub hm')
    set y' := max (m' - ε / 2) ((y1 + m') / 2)
    have hy'1 : y1 < y' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hy'2 : y' < m' := max_lt (by linarith) (by linarith)
    have hy'm : y' ∈ Icc y1 y2 := ⟨hy'1.le, by grind⟩
    have := hε' y' (hsub hy'm) (lt_of_lt_of_le (by linarith) (le_max_left _ _)) hy'2
    exact absurd (hmin' hy'm) (not_le.mpr this)
  have hm1 : m = y1 := by
    grind
  subst hm1
  have hle := hmin ⟨h12.le, le_rfl⟩
  rcases lt_or_eq_of_le hle with hlt | heq
  assumption
  · exfalso
    refine key y2 ⟨h12.le, le_rfl⟩ h12 fun z hz => ?_
    rw [← heq]; tauto

/-- Mirror version: strictly smaller than at nearby points to the right gives strictly
decreasing. -/
lemma strictAntiOn_of_local_right {g : ℝ → ℝ} {J : Set ℝ} (hJ : J.OrdConnected)
    (hg : ContinuousOn g J)
    (hloc : ∀ y ∈ J, ∃ ε > 0, ∀ y' ∈ J, y < y' → y' < y + ε → g y' < g y) :
    StrictAntiOn g J := by
  have hJ' : (Neg.neg ⁻¹' J).OrdConnected := ⟨fun a ha b hb x hx => hJ.out hb ha ⟨by simp_all, by simp_all⟩⟩
  have hg' :=
    hg.comp continuous_neg.continuousOn (fun y hy => hy)
  have hmono := strictMonoOn_of_local_left hJ' hg' fun y hy => by grind
  intro a ha b hb hab
  have := hmono (show -b ∈ Neg.neg ⁻¹' J by simpa using hb)
    (show -a ∈ Neg.neg ⁻¹' J by simpa using ha) (by linarith)
  simpa using this

/-! ### Consistency of orientation -/

/-- **Orientation consistency.** Let `(p₁, c₁, f₁)` and `(p₂, c₂, f₂)` be two charts of `Ω`, and
let the chart-1 graph point with abscissa `x₀` lie in the chart-2 box. Then, near `x₀`, the
chart-2 abscissa of the chart-1 graph point is a strictly increasing function of `x₀`: both
charts traverse the boundary in the same direction (with `Ω` on the left). -/
theorem chart_orient {Ω : Set ℂ} (hΩo : IsOpen Ω) {p₁ c₁ p₂ c₂ : ℂ} {r₁ h₁ r₂ h₂ : ℝ}
    {K₁ K₂ : NNReal} {f₁ f₂ : ℝ → ℝ} (hch₁ : IsChartAt Ω p₁ c₁ r₁ h₁ K₁ f₁)
    (hch₂ : IsChartAt Ω p₂ c₂ r₂ h₂ K₂ f₂) {x₀ : ℝ} (hx₀ : |x₀| < r₁)
    (hbox : chartPt p₁ c₁ f₁ x₀ ∈ chartBox p₂ c₂ r₂ h₂) :
    ∃ ε > 0, StrictMonoOn (fun x => (c₂ * (chartPt p₁ c₁ f₁ x - p₂)).re)
      (Icc (x₀ - ε) (x₀ + ε)) := by
  have hc₁ := hch₁.1
  have hc₂ := hch₂.1
  have hf₁ := hch₁.2.2.2.1.continuous
  have hf₂ := hch₂.2.2.2.1.continuous
  have hΩ₂ := hch₂.2.2.2.2.2.2
  set σ₁ := chartPt p₁ c₁ f₁ with hσ₁
  set σ₂ := chartPt p₂ c₂ f₂ with hσ₂
  have hσ₁c : Continuous σ₁ := continuous_chartPt hf₁
  have hσ₂c : Continuous σ₂ := continuous_chartPt hf₂
  -- a small closed interval around `x₀` on which everything is inside both boxes
  set O : Set ℝ := {x | |x| < r₁} ∩ σ₁ ⁻¹' chartBox p₂ c₂ r₂ h₂ with hO
  have hOo : IsOpen O := (isOpen_lt continuous_abs continuous_const).inter
    ((isOpen_chartBox _ _ _ _).preimage hσ₁c)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hOo x₀ ⟨hx₀, hbox⟩
  refine ⟨δ / 2, by positivity, ?_⟩
  set I := Icc (x₀ - δ / 2) (x₀ + δ / 2) with hI
  have hIO : I ⊆ O := fun x hx => hball (by
    rw [mem_ball, Real.dist_eq, abs_lt]; grind)
  set ψ : ℝ → ℝ := fun x => (c₂ * (σ₁ x - p₂)).re with hψ
  have hψc : Continuous ψ := by fun_prop
  set J := ψ '' I with hJ
  have hJo : J.OrdConnected :=
    (isPreconnected_Icc.image ψ hψc.continuousOn).ordConnected
  have hfr : ∀ x ∈ I, σ₁ x ∈ frontier Ω := fun x hx =>
    chartPt_mem_frontier hΩo hch₁ (hIO hx).1
  have hσeq : ∀ x ∈ I, σ₁ x = σ₂ (ψ x) := fun x hx =>
    eq_chartPt_of_frontier hΩo hch₂ (hfr x hx) (hIO hx).2
  set φ : ℝ → ℝ := fun y => (c₁ * (σ₂ y - p₁)).re with hφ
  have hφψ : ∀ x ∈ I, φ (ψ x) = x := fun x hx => by
    simp only [hφ]; rw [← hσeq x hx, hσ₁, re_mul_chartPt_sub hc₁]
  set v : ℂ := c₂ * conj c₁ with hv
  set a := v.re
  set b := v.im
  set C := (c₁ * (p₂ - p₁)).re with hC
  have hφform : ∀ y, φ y = a * y + b * f₂ y + C := fun y => by
    simp only [hφ, hσ₂, chartPt, hC]
    have : c₁ * (p₂ + conj c₂ * ((y : ℂ) + (f₂ y : ℂ) * Complex.I) - p₁) =
        conj v * ((y : ℂ) + (f₂ y : ℂ) * Complex.I) + c₁ * (p₂ - p₁) := by
      rw [hv, map_mul, Complex.conj_conj]; ring
    rw [this, Complex.add_re]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.add_re,
      Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.add_im,
      Complex.ofReal_im]
    ring
  -- the key inequality: points above the chart-1 graph are in `Ω`
  have hkey : ∀ y ∈ J, ∀ᶠ s : ℝ in 𝓝[>] 0, f₂ (y - s * b) < f₂ y + s * a := by
    rintro y ⟨x, hx, rfl⟩
    have hgr : (c₂ * (σ₁ x - p₂)).im = f₂ (ψ x) := by
      rw [hσeq x hx, hσ₂, im_mul_chartPt_sub hc₂]
    filter_upwards [tendsto_vertical_chart (σ₁ x) c₁
      ((isOpen_chartBox _ _ _ _).mem_nhds (hIO hx).2), eventually_vertical_mem hch₁ (hIO hx).1]
      with s hs2 hsΩ
    have h := (hΩ₂ _ hs2.1 hs2.2).1 hsΩ
    dsimp only at h
    rw [vertical_chart_coordinates, ← hv, Complex.add_re, Complex.add_im,
      Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.mul_I_re, Complex.mul_I_im,
      hgr, mul_neg, ← sub_eq_add_neg] at h
    exact h
  have hev_eps : ∀ y ∈ J, ∃ ε > 0, ∀ s, 0 < s → s < ε → f₂ (y - s * b) < f₂ y + s * a :=
    fun y hy => by
      rcases (nhdsGT_basis (0:ℝ)).eventually_iff.mp (hkey y hy) with ⟨i, hi, h⟩
      exact ⟨i, hi, fun s h1 h2 => h ⟨h1, h2⟩⟩
  have hδ (y s : ℝ) : φ (y - s * b) - φ y = b * (f₂ (y - s * b) - (f₂ y + s * a)) := by
    rw [hφform, hφform]; ring
  have hφc : Continuous φ := by fun_prop
  have hφmono : StrictMonoOn φ J := by
    rcases lt_trichotomy b 0 with hb | hb | hb
    · have hanti : StrictAntiOn (fun y => -φ y) J := by
        refine strictAntiOn_of_local_right hJo hφc.neg.continuousOn fun y hy => ?_
        obtain ⟨ε, hε, h⟩ := hev_eps y hy
        refine ⟨ε * (-b), mul_pos hε (neg_pos.mpr hb), fun y' _ h1 h2 => ?_⟩
        have hs := h ((y - y') / b) (div_pos_of_neg_of_neg (by linarith) hb)
          (by rw [div_lt_iff_of_neg hb]; nlinarith)
        have hh := mul_pos_of_neg_of_neg hb (sub_neg.mpr hs)
        rwa [← hδ, div_mul_cancel₀ _ hb.ne, sub_sub_cancel, sub_pos, ← neg_lt_neg_iff] at hh
      exact fun x hx y hy hxy => neg_lt_neg_iff.mp (hanti hx hy hxy)
    · intro y hy z _ hyz
      obtain ⟨ε, hε, h⟩ := hev_eps y hy
      have hs := h (ε / 2) (by positivity) (by linarith)
      simp only [hb, mul_zero, sub_zero] at hs
      have ha : 0 < a := by nlinarith
      simpa [hφform, hb] using add_lt_add_right (mul_lt_mul_of_pos_left hyz ha) C
    · refine strictMonoOn_of_local_left hJo hφc.continuousOn fun y hy => ?_
      obtain ⟨ε, hε, h⟩ := hev_eps y hy
      refine ⟨ε * b, by positivity, fun y' _ h1 h2 => ?_⟩
      have hs := h ((y - y') / b) (div_pos (by linarith) hb)
        (by rw [div_lt_iff₀ hb]; linarith)
      have hh := mul_neg_of_pos_of_neg hb (sub_neg.mpr hs)
      rwa [← hδ, div_mul_cancel₀ _ hb.ne', sub_sub_cancel, sub_neg] at hh
  intro x hx x' hx' hxx'
  by_contra hle
  push_neg at hle
  have := hφmono.le_iff_le (mem_image_of_mem ψ hx') (mem_image_of_mem ψ hx) |>.mpr hle
  rw [hφψ x' hx', hφψ x hx] at this
  linarith

end PolyaNeumann
