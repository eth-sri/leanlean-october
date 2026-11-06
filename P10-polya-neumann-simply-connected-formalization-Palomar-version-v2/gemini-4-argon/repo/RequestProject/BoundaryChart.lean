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

variable {p c : ℂ} {g : ℝ → ℝ}

/-- A Lipschitz chart of `Ω` at `p`: after the rigid motion `w ↦ c (w - p)`, inside the box
`|x| < r`, `|y| < h`, the domain is the region above the graph of the `K`-Lipschitz function `f`
(with `f 0 = 0`, and the graph over `|x| < r` inside the box). -/
def IsChartAt (Ω : Set ℂ) (p c : ℂ) (r h : ℝ) (K : NNReal) (f : ℝ → ℝ) : Prop :=
  ‖c‖ = 1 ∧ 0 < r ∧ 0 < h ∧ LipschitzWith K f ∧ f 0 = 0 ∧ (∀ x : ℝ, |x| < r → |f x| < h) ∧
    ∀ w : ℂ, |(c * (w - p)).re| < r → |(c * (w - p)).im| < h →
      (w ∈ Ω ↔ f (c * (w - p)).re < (c * (w - p)).im)

lemma IsLipschitzDomain.exists_chart  (hL : IsLipschitzDomain Ω) 
    (hp : p ∈ frontier Ω) : ∃ c r h K f,
      IsChartAt Ω p c r h K f :=
  hL.2 p hp

/-- The graph point of a chart with abscissa `x`. -/
def chartPt (p c : ℂ) (f : ℝ → ℝ) (x : ℝ) : ℂ := p + conj c * ((x : ℂ) + (f x : ℂ) * Complex.I)

lemma mul_chartPt_sub  (hc : ‖c‖ = 1) f x :
    c * (chartPt p c f x - p) = (x : ℂ) + (f x : ℂ) * Complex.I := by
  simp [chartPt, ← mul_assoc, show c * conj c = 1 by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp]

lemma re_mul_chartPt_sub  (hc : ‖c‖ = 1) f x :
    (c * (chartPt p c f x - p)).re = x := by
  rw [mul_chartPt_sub hc]; simp

lemma im_mul_chartPt_sub  (hc : ‖c‖ = 1) f x :
    (c * (chartPt p c f x - p)).im = f x := by
  rw [mul_chartPt_sub hc]; simp

lemma chartPt_zero   (hf0 : f 0 = 0) : chartPt p c f 0 = p := by
  simp [chartPt, hf0]

lemma norm_mul_sub {c : ℂ} (hc : ‖c‖ = 1) w p : ‖c * (w - p)‖ = ‖w - p‖ := by
  rw [norm_mul, hc, one_mul]

lemma eq_of_re_im_eq {c p w w' : ℂ} (hc : ‖c‖ = 1) (hre : (c * (w - p)).re = (c * (w' - p)).re)
    (him : (c * (w - p)).im = (c * (w' - p)).im) : w = w' :=
  (show w = w' by
    have := mul_left_cancel₀ (by intro h0; rw [h0, norm_zero] at hc; exact zero_ne_one hc) (Complex.ext hre him)
    linear_combination this)

/-- The graph map of a chart is `(1 + K)`-Lipschitz. -/
lemma lipschitzWith_chartPt  (hc : ‖c‖ = 1)  
    (hf : LipschitzWith K f) : LipschitzWith (1 + K) (chartPt p c f) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [chartPt, dist_eq_norm, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, show ‖conj c‖ = 1 by rw [Complex.norm_conj, hc], one_mul]
  have h1 : ‖(x + f x * Complex.I) - (y + f y * Complex.I)‖ ≤
      ‖((x - y : ℝ) : ℂ)‖ + ‖(f x - f y : ℝ) * Complex.I‖ := by
    rw [show x + (f x : ℂ) * Complex.I - (y + (f y : ℂ) * Complex.I) = ((x - y : ℝ) : ℂ) + ((f x - f y : ℝ) : ℂ) * Complex.I by push_cast; ring]; exact norm_add_le _ _
  have h2 : |f x - f y| ≤ K * |x - y| := by
    have := hf.dist_le_mul x y; rwa [Real.dist_eq, Real.dist_eq] at this
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs] at h1
  push_cast
  rw [Real.norm_eq_abs]
  nlinarith

lemma continuous_chartPt   (hf : Continuous f) :
    Continuous (chartPt p c f) := by
  unfold chartPt; fun_prop

/-- The open chart box. -/
def chartBox (p c : ℂ) (r h : ℝ) : Set ℂ :=
  {w | |(c * (w - p)).re| < r ∧ |(c * (w - p)).im| < h}

lemma isOpen_chartBox p c r h : IsOpen (chartBox p c r h) := by
  have hg : Continuous fun w => c * (w - p) := by fun_prop
  exact (isOpen_lt (Complex.continuous_re.comp hg).abs continuous_const).inter
    (isOpen_lt (Complex.continuous_im.comp hg).abs continuous_const)

/-- A ball around the centre inside the box. -/
lemma ball_subset_chartBox  (hc : ‖c‖ = 1)  :
    ball p (min r h) ⊆ chartBox p c r h := by
  intro w hw
  rw [mem_ball, dist_eq_norm] at hw
  have hn := norm_mul_sub hc w p
  refine ⟨lt_of_le_of_lt (Complex.abs_re_le_norm _) ?_,
    lt_of_le_of_lt (Complex.abs_im_le_norm _) ?_⟩
  · rw [hn]; exact lt_of_lt_of_le hw (min_le_left _ _)
  · rw [hn]; exact lt_of_lt_of_le hw (min_le_right _ _)

/-- Graph points of a chart are boundary points. -/
lemma chartPt_mem_frontier  (hΩo : IsOpen Ω)   
     (hch : IsChartAt Ω p c r h K f)  (hx : |x| < r) :
    chartPt p c f x ∈ frontier Ω := by
  obtain ⟨hc, hr, hh, hf, hf0, hfb, hΩ⟩ := hch
  rw [hΩo.frontier_eq]
  have hfx := hfb x hx
  refine ⟨?_, ?_⟩
  · -- limit of points above the graph
    rw [mem_closure_iff_nhds]
    intro U hU
    have ht : Tendsto (fun s : ℝ => chartPt p c f x + (s : ℂ) * (conj c * Complex.I))
        (𝓝[>] 0) (𝓝 (chartPt p c f x)) := by
      have := (show Continuous fun s : ℝ => chartPt p c f x + s * (conj c * Complex.I) by
        fun_prop).tendsto 0
      simp at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    have hev : ∀ᶠ s : ℝ in 𝓝[>] 0, chartPt p c f x + s * (conj c * Complex.I) ∈ U :=
      ht hU
    obtain ⟨s, hsU, hs, hspos⟩ := (hev.and ((show ∀ᶠ s : ℝ in 𝓝[>] 0, s < h - |f x| from (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (by linarith)))).and self_mem_nhdsWithin)).exists
    refine ⟨_, hsU, ?_⟩
    have hcc : c * conj c = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
    have hcoord : c * (chartPt p c f x + s * (conj c * Complex.I) - p) =
        x + (f x + s : ℝ) * Complex.I := by
      rw [add_sub_right_comm, mul_add, mul_chartPt_sub (p := p) hc f x]
      rw [show c * (s * (conj c * Complex.I)) = s * Complex.I * (c * conj c) by
        ring, hcc]; push_cast; ring
    have hre : (c * (chartPt p c f x + s * (conj c * Complex.I) - p)).re = x := by
      rw [hcoord]; simp
    have him : (c * (chartPt p c f x + s * (conj c * Complex.I) - p)).im = f x + s := by
      rw [hcoord]; simp
    have hfx' := abs_lt.mp hfx
    refine (hΩ _ (by rw [hre]; exact hx) (by rw [him]; exact (show |f x + s| < h by
      rw [abs_lt]; constructor
      · linarith
      · linarith [le_abs_self (f x)]))).mpr ?_
    rw [hre, him]; linarith
  · intro hmem
    have := (hΩ _ (by rw [re_mul_chartPt_sub hc]; exact hx)
      (by rw [im_mul_chartPt_sub hc]; exact hfx)).mp hmem
    rw [re_mul_chartPt_sub hc, im_mul_chartPt_sub hc] at this
    exact lt_irrefl _ this

/-- Boundary points in a chart box are graph points. -/
lemma eq_chartPt_of_frontier  (hΩo : IsOpen Ω)   
    {f : ℝ → ℝ} (hch : IsChartAt Ω p c r h K f)  (hw : w ∈ frontier Ω)
    (hbox : w ∈ chartBox p c r h) : w = chartPt p c f (c * (w - p)).re := by
  obtain ⟨hc, hr, hh, hf, hf0, hfb, hΩ⟩ := hch
  refine eq_of_re_im_eq (p := p) hc ?_ ?_
  · rw [re_mul_chartPt_sub hc]
  · rw [im_mul_chartPt_sub hc, chart_frontier_graph hΩo hf hΩ hw hbox.1 hbox.2]

/-- Two boundary points in a chart box with the same abscissa coincide. -/
lemma eq_of_frontier_of_re_eq  (hΩo : IsOpen Ω)   
     (hch : IsChartAt Ω p c r h K f)  (hw : w ∈ frontier Ω)
    (hw' : w' ∈ frontier Ω) (hbox : w ∈ chartBox p c r h) (hbox' : w' ∈ chartBox p c r h)
    (hre : (c * (w - p)).re = (c * (w' - p)).re) : w = w' := by
  rw [eq_chartPt_of_frontier hΩo hch hw hbox, eq_chartPt_of_frontier hΩo hch hw' hbox', hre]

/-- Along the boundary inside a chart box, distances are controlled by abscissae. -/
lemma norm_sub_le_of_frontier  (hΩo : IsOpen Ω)   
     (hch : IsChartAt Ω p c r h K f)  (hw : w ∈ frontier Ω)
    (hw' : w' ∈ frontier Ω) (hbox : w ∈ chartBox p c r h) (hbox' : w' ∈ chartBox p c r h) :
    ‖w - w'‖ ≤ (1 + K) * |(c * (w - p)).re - (c * (w' - p)).re| := by
  have h1 := (lipschitzWith_chartPt (p := p) hch.1 hch.2.2.2.1).dist_le_mul
    (c * (w - p)).re (c * (w' - p)).re
  rw [← eq_chartPt_of_frontier hΩo hch hw hbox, ← eq_chartPt_of_frontier hΩo hch hw' hbox',
    dist_eq_norm, Real.dist_eq] at h1
  simpa using h1

/-! ### Recentering and uniform charts -/

/-- Recentering a chart at a boundary point of the half box. -/
lemma isChartAt_recenter  (hΩo : IsOpen Ω)   
     (hch : IsChartAt Ω p c r h K f)  (hq : q ∈ frontier Ω)
    (hqr : |(c * (q - p)).re| < r / 2) (hqh : |(c * (q - p)).im| < h / 2)
      (hρ : 0 < ρ) (hH : 0 < H) (hρr : ρ ≤ r / 2) (hHh : H ≤ h / 2)
    (hKK : K ≤ K') (hKρ : (K' : ℝ) * ρ < H) :
    IsChartAt Ω q c ρ H K'
      (fun x => f (x + (c * (q - p)).re) - f (c * (q - p)).re) := by
  obtain ⟨hc, hr, hh, hf, hf0, hfb, hΩ⟩ := hch
  set X := (c * (q - p)).re with hX
  have hlip : LipschitzWith K' (fun x => f (x + X) - f X) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have := (hf.weaken hKK).dist_le_mul (x + X) (y + X)
    simp [Real.dist_eq] at this ⊢
    exact this
  refine ⟨hc, hρ, hH, hlip, by simp, fun x hx => ?_, fun w hw1 hw2 => ?_⟩
  · have := hlip.dist_le_mul x 0
    simp at this
    calc _ ≤ _ := this
      _ ≤ _ := mul_le_mul_of_nonneg_left hx.le K'.2
      _ < H := hKρ
  · have hY :=
      chart_frontier_graph hΩo hf hΩ hq (by linarith [hqr]) (by linarith [hqh])
    have hsplit : c * (w - p) = c * (w - q) + c * (q - p) := by ring
    have hre : (c * (w - p)).re = (c * (w - q)).re + X := by rw [hsplit, Complex.add_re]
    have him : (c * (w - p)).im = (c * (w - q)).im + f X := by
      rw [hsplit, Complex.add_im, hY]
    rw [hΩ w (by
      rw [hre]; calc _ ≤ |(c * (w - q)).re| + |X| := abs_add_le _ _
        _ < r := by linarith) (by
      rw [him]; calc _ ≤ |(c * (w - q)).im| + |f X| := abs_add_le _ _
        _ < h := by rw [← hY]; linarith), hre, him]
    constructor <;> intro hlt <;> linarith

lemma frontier_isCompact {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) : IsCompact (frontier Ω) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_frontier
    (hb.closure.subset frontier_subset_closure)

/-- **Uniform charts.** A bounded Lipschitz domain has charts at every boundary point with
uniform size `ρ × H` and uniform Lipschitz constant `K`, with `K ρ < H`. -/
theorem exists_uniform_charts  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) :
    ∃ (ρ H : ℝ) (K : NNReal), 0 < ρ ∧ 0 < H ∧ (K : ℝ) * ρ < H ∧
      ∀ p ∈ frontier Ω, ∃ (c : ℂ) (f : ℝ → ℝ), IsChartAt Ω p c ρ H K f := by
  choose! c r h K f hch using fun p (hp : p ∈ frontier Ω) => hL.exists_chart hp
  set U : ℂ → Set ℂ := fun p => chartBox p (c p) (r p / 2) (h p / 2) with hU
  have hcover : frontier Ω ⊆ ⋃ p ∈ frontier Ω, U p := fun q hq => by
    refine mem_biUnion hq ?_
    obtain ⟨-, hr, hh, -⟩ := hch q hq
    simp [hU, chartBox, hr, hh]
  obtain ⟨t, htΩ, htfin, hcov⟩ := (frontier_isCompact hb).elim_finite_subcover_image
    (fun p _ => (fun p => isOpen_chartBox _ _ _ _) p) hcover
  by_cases hte : t.Nonempty
  swap
  · -- empty boundary: any constants work
    refine ⟨1, 2, 0, one_pos, two_pos, by norm_num, fun p hp => ?_⟩
    have := hcov hp
    rw [Set.not_nonempty_iff_eq_empty.mp hte] at this
    simp at this
  set Kt := htfin.toFinset.sup' (by simpa using hte) K with hKt
  set Ht := htfin.toFinset.inf' (by simpa using hte) (fun p => h p / 2) with hHt
  set Rt := htfin.toFinset.inf' (by simpa using hte) (fun p => r p / 2) with hRt
  have hHt0 : 0 < Ht := by
    rw [hHt, Finset.lt_inf'_iff]
    intro p hp
    have := (hch p (htΩ (by simpa using hp))).2.2.1
    linarith
  set ρ := min Rt (Ht / (2 * (Kt + 1))) with hρ
  have hρ0 : 0 < ρ := lt_min (by
    rw [hRt, Finset.lt_inf'_iff]
    intro p hp
    have := (hch p (htΩ (by simpa using hp))).2.1
    linarith) (by positivity)
  have hKρ : Kt * ρ < Ht := by
    calc Kt * ρ ≤ _ := mul_le_mul_of_nonneg_left (min_le_right _ _) Kt.2
      _ < Ht := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
  refine ⟨ρ, Ht, Kt, hρ0, hHt0, hKρ, fun q hq => ?_⟩
  obtain ⟨p, hpt, hqU⟩ := mem_iUnion₂.mp (hcov hq)
  have hpt' : p ∈ htfin.toFinset := by simpa using hpt
  refine ⟨c p, _, isChartAt_recenter hL.1.1 (hch p (htΩ hpt)) hq hqU.1 hqU.2 hρ0 hHt0
    (le_trans (min_le_left _ _) (Finset.inf'_le _ hpt')) (Finset.inf'_le _ hpt')
    (Finset.le_sup' K hpt') hKρ⟩

/-! ### Local monotonicity -/

/-- A continuous function on an order-connected set that is, at every point, strictly larger
than at all nearby points to the left, is strictly increasing. -/
lemma strictMonoOn_of_local_left   (hJ : J.OrdConnected)
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
    have hy'm : y' ∈ Icc y1 y2 := ⟨hy'1.le, by linarith [hm'.2]⟩
    exact absurd (hmin' hy'm) (not_le.mpr (hε' y' (hsub hy'm) (lt_of_lt_of_le (by linarith) (le_max_left _ _)) hy'2))
  have hm1 : m = y1 := by
    by_contra hne
    exact key m hm (lt_of_le_of_ne hm.1 (Ne.symm hne)) hmin
  subst hm1
  rcases lt_or_eq_of_le (hmin ⟨h12.le, le_rfl⟩) with hlt | heq
  · exact hlt
  · exfalso
    refine key y2 ⟨h12.le, le_rfl⟩ h12 fun z hz => ?_
    rw [← heq]; exact hmin hz

/-- Mirror version: strictly smaller than at nearby points to the right gives strictly
decreasing. -/
lemma strictAntiOn_of_local_right   (hJ : J.OrdConnected)
    (hg : ContinuousOn g J)
    (hloc : ∀ y ∈ J, ∃ ε > 0, ∀ y' ∈ J, y < y' → y' < y + ε → g y' < g y) :
    StrictAntiOn g J := by
  have hJ' : (Neg.neg ⁻¹' J).OrdConnected := ⟨fun a ha b hb x hx => by
    simp at *
    exact hJ.out hb ha ⟨by linarith [hx.2], by linarith [hx.1]⟩⟩
  have hmono := strictMonoOn_of_local_left hJ' (hg.comp continuous_neg.continuousOn (fun y hy => hy)) fun y hy => by
    obtain ⟨ε, hε, h⟩ := hloc (-y) hy
    exact ⟨ε, hε, fun y' hy' h1 h2 => h (-y') hy' (by linarith) (by linarith)⟩
  intro a ha b hb hab
  simpa using hmono (show -b ∈ Neg.neg ⁻¹' J by simpa using hb) (show -a ∈ Neg.neg ⁻¹' J by simpa using ha) (by linarith)

/-! ### Consistency of orientation -/

/-- **Orientation consistency.** Let `(p₁, c₁, f₁)` and `(p₂, c₂, f₂)` be two charts of `Ω`, and
let the chart-1 graph point with abscissa `x₀` lie in the chart-2 box. Then, near `x₀`, the
chart-2 abscissa of the chart-1 graph point is a strictly increasing function of `x₀`: both
charts traverse the boundary in the same direction (with `Ω` on the left). -/
theorem chart_orient  (hΩo : IsOpen Ω)  
      (hch₁ : IsChartAt Ω p₁ c₁ r₁ h₁ K₁ f₁)
    (hch₂ : IsChartAt Ω p₂ c₂ r₂ h₂ K₂ f₂) {x₀ : ℝ} (hx₀ : |x₀| < r₁)
    (hbox : chartPt p₁ c₁ f₁ x₀ ∈ chartBox p₂ c₂ r₂ h₂) :
    ∃ ε > 0, StrictMonoOn (fun x => (c₂ * (chartPt p₁ c₁ f₁ x - p₂)).re)
      (Icc (x₀ - ε) (x₀ + ε)) := by
  obtain ⟨hc₁, hr₁, hh₁, hf₁, hf₁0, hfb₁, hΩ₁⟩ := hch₁
  obtain ⟨hc₂, hr₂, hh₂, hf₂, hf₂0, hfb₂, hΩ₂⟩ := hch₂
  set σ₁ := chartPt p₁ c₁ f₁ with hσ₁
  set σ₂ := chartPt p₂ c₂ f₂ with hσ₂
  have hσ₁c : Continuous σ₁ := continuous_chartPt hf₁.continuous
  have hσ₂c : Continuous σ₂ := continuous_chartPt hf₂.continuous
  -- a small closed interval around `x₀` on which everything is inside both boxes
  set O : Set ℝ := {x | |x| < r₁} ∩ σ₁ ⁻¹' chartBox p₂ c₂ r₂ h₂ with hO
  have hOo : IsOpen O := (isOpen_lt continuous_abs continuous_const).inter
    ((isOpen_chartBox _ _ _ _).preimage hσ₁c)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hOo x₀ ⟨hx₀, hbox⟩
  refine ⟨δ / 2, by positivity, ?_⟩
  set I := Icc (x₀ - δ / 2) (x₀ + δ / 2) with hI
  have hIO : I ⊆ O := fun x hx => hball (by
    rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2])
  set ψ : ℝ → ℝ := fun x => (c₂ * (σ₁ x - p₂)).re with hψ
  set J := ψ '' I with hJ
  have hJo : J.OrdConnected :=
    (isPreconnected_Icc.image ψ (show Continuous ψ by simp [hψ]; fun_prop).continuousOn).ordConnected
  have hfr : ∀ x ∈ I, σ₁ x ∈ frontier Ω := fun x hx =>
    chartPt_mem_frontier hΩo ⟨hc₁, hr₁, hh₁, hf₁, hf₁0, hfb₁, hΩ₁⟩ (hIO hx).1
  have hσeq : ∀ x ∈ I, σ₁ x = σ₂ (ψ x) := fun x hx =>
    eq_chartPt_of_frontier hΩo ⟨hc₂, hr₂, hh₂, hf₂, hf₂0, hfb₂, hΩ₂⟩ (hfr x hx) (hIO hx).2
  set φ : ℝ → ℝ := fun y => (c₁ * (σ₂ y - p₁)).re with hφ
  have hφψ : ∀ x ∈ I, φ (ψ x) = x := fun x hx => by
    simp only [hφ]; rw [← hσeq x hx, hσ₁, re_mul_chartPt_sub hc₁]
  set v : ℂ := c₂ * conj c₁ with hv
  set a := v.re
  set b := v.im
  have hab : a * a + b * b = 1 := by
    have h1 : ‖v‖ = 1 := by rw [hv, norm_mul, Complex.norm_conj, hc₁, hc₂, one_mul]
    have h2 := Complex.normSq_eq_norm_sq v
    rw [h1, Complex.normSq_apply] at h2
    linarith
  set C := (c₁ * (p₂ - p₁)).re with hC
  have hφform : ∀ y, φ y = a * y + b * f₂ y + C := fun y => by
    simp only [hφ, hσ₂, chartPt, hC]
    rw [show c₁ * (p₂ + conj c₂ * (y + f₂ y * Complex.I) - p₁) = conj v * (y + f₂ y * Complex.I) + c₁ * (p₂ - p₁) by
      rw [hv, map_mul, Complex.conj_conj]; ring, Complex.add_re]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.add_re,
      Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.add_im,
      Complex.ofReal_im]
    ring
  -- the key inequality: points above the chart-1 graph are in `Ω`
  have hkey : ∀ y ∈ J, ∀ᶠ s : ℝ in 𝓝[>] 0, f₂ (y - s * b) < f₂ y + s * a := by
    rintro y ⟨x, hx, rfl⟩
    set e : ℂ := conj c₁ * Complex.I with he
    have hc1 : ∀ s : ℝ, c₁ * (σ₁ x + s * e - p₁) =
        x + (f₁ x + s : ℝ) * Complex.I := fun s => by
      rw [add_sub_right_comm, mul_add, hσ₁, mul_chartPt_sub (p := p₁) hc₁ f₁ x]
      have h2 : c₁ * (s * e) = s * Complex.I * (c₁ * conj c₁) := by
        rw [he]; ring
      rw [h2, show c₁ * conj c₁ = 1 by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc₁]; simp]; push_cast; ring
    have hc2 : ∀ s : ℝ, c₂ * (σ₁ x + s * e - p₂) =
        c₂ * (σ₁ x - p₂) + s * (v * Complex.I) := fun s => by
      rw [he, hv]; ring
    -- eventually in the chart-2 box
    have hev2 : ∀ᶠ s : ℝ in 𝓝 0, σ₁ x + (s : ℂ) * e ∈ chartBox p₂ c₂ r₂ h₂ := by
      have := (show Continuous fun s : ℝ => σ₁ x + s * e by fun_prop).tendsto 0
      simp at this
      exact this ((isOpen_chartBox _ _ _ _).mem_nhds (hIO hx).2)
    have hfx := hfb₁ x (hIO hx).1
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hev2,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (by linarith) : ∀ᶠ s : ℝ in 𝓝 0, s < h₁ - |f₁ x|), self_mem_nhdsWithin] with s hs2 hs1 hs0
    have hs0' : 0 < s := hs0
    have := (hΩ₂ _ hs2.1 hs2.2).mp (by
      have hre : (c₁ * (σ₁ x + s * e - p₁)).re = x := by rw [hc1]; simp
      have him : (c₁ * (σ₁ x + s * e - p₁)).im = f₁ x + s := by rw [hc1]; simp
      refine (hΩ₁ _ (by rw [hre]; exact (hIO hx).1) (by rw [him]; exact (by
        rw [abs_lt]; constructor
        · linarith [(abs_lt.mp hfx).1]
        · linarith [le_abs_self (f₁ x)]))).mpr ?_
      rw [hre, him]; linarith)
    rw [hc2, Complex.add_re, Complex.add_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
      Complex.mul_I_re v, Complex.mul_I_im v, show (c₂ * (σ₁ x - p₂)).im = f₂ (ψ x) by
        rw [congrArg (fun w => (c₂ * (w - p₂)).im) (hσeq x hx), hσ₂, im_mul_chartPt_sub hc₂]] at this
    rw [(rfl : (c₂ * (σ₁ x - p₂)).re = ψ x)] at this
    convert this using 2; ring
  have hev_eps : ∀ y ∈ J, ∃ ε > 0, ∀ s, 0 < s → s < ε → f₂ (y - s * b) < f₂ y + s * a :=
    fun y hy => by
      rcases (nhdsGT_basis 0).eventually_iff.mp (hkey y hy) with ⟨i, hi, h⟩
      exact ⟨i, hi, fun s h1 h2 => h ⟨h1, h2⟩⟩
  have hgc : ContinuousOn (fun y => f₂ y + a / b * y) J :=
    (hf₂.continuous.add (continuous_const.mul continuous_id)).continuousOn
  -- `φ` is strictly increasing on `J`
  intro x hx x' hx' hxx'
  by_contra hle
  push_neg at hle
  have := (show StrictMonoOn φ J by
    rcases lt_trichotomy b 0 with hb | hb | hb
    · have hb0 : b ≠ 0 := hb.ne
      have hanti : StrictAntiOn (fun y => f₂ y + a / b * y) J := by
        refine strictAntiOn_of_local_right hJo hgc fun y hy => ?_
        obtain ⟨ε, hε, h⟩ := hev_eps y hy
        refine ⟨ε * (-b), by nlinarith, fun y' _ h1 h2 => ?_⟩
        have hs := h ((y - y') / b) (div_pos_of_neg_of_neg (by linarith) hb)
          (by rw [div_lt_iff_of_neg hb]; linarith)
        have e1 : y - (y - y') / b * b = y' := by rw [div_mul_cancel₀ _ hb0]; ring
        rw [e1] at hs
        have e2 : (y - y') / b * a = a / b * y - a / b * y' := by ring
        rw [e2] at hs
        linarith
      intro y1 hy1 y2 hy2 h12
      have := hanti hy1 hy2 h12
      rw [hφform, hφform]
      simp only at this
      have hba : b * (a / b) = a := by field_simp
      have e : ∀ y, a * y + b * f₂ y + C = b * (f₂ y + a / b * y) + C := fun y => by
        rw [mul_add b, ← mul_assoc, hba]; ring
      rw [e, e]; nlinarith
    · have ha : a * a = 1 := by rw [hb] at hab; linarith
      obtain ⟨y₀, hy₀⟩ : J.Nonempty := (nonempty_Icc.mpr (by linarith)).image ψ
      obtain ⟨ε, hε, h⟩ := hev_eps y₀ hy₀
      have := h (ε / 2) (by positivity) (by linarith)
      rw [hb] at this
      simp at this
      have ha0 : 0 < a := by nlinarith
      intro y1 _ y2 _ h12
      rw [hφform, hφform, hb, show a = 1 by nlinarith]; linarith
    · have hb0 : b ≠ 0 := hb.ne'
      have hmono : StrictMonoOn (fun y => f₂ y + a / b * y) J := by
        refine strictMonoOn_of_local_left hJo hgc fun y hy => ?_
        obtain ⟨ε, hε, h⟩ := hev_eps y hy
        refine ⟨ε * b, by positivity, fun y' _ h1 h2 => ?_⟩
        have hs := h ((y - y') / b) (div_pos (by linarith) hb)
          (by rw [div_lt_iff₀ hb]; linarith)
        rw [show y - (y - y') / b * b = y' by rw [div_mul_cancel₀ _ hb0]; ring] at hs
        rw [show (y - y') / b * a = a / b * y - a / b * y' by ring] at hs
        linarith
      intro y1 hy1 y2 hy2 h12
      have := hmono hy1 hy2 h12
      rw [hφform, hφform]
      simp only at this
      have e : ∀ y, a * y + b * f₂ y + C = b * (f₂ y + a / b * y) + C := fun y => by
        rw [mul_add b, ← mul_assoc, show b * (a / b) = a by field_simp]; ring
      rw [e, e]; nlinarith).le_iff_le (mem_image_of_mem ψ hx') (mem_image_of_mem ψ hx) |>.mpr hle
  rw [hφψ x' hx', hφψ x hx] at this
  linarith

end PolyaNeumann
