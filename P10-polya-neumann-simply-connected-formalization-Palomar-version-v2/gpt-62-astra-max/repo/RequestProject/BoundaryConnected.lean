module

public import RequestProject.CircleAnalysisNotation

public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.ExtendFrom
public import RequestProject.BoundaryLoop
public import RequestProject.ExteriorConnected
public import RequestProject.PlanarNotation

/-!
# The boundary of a simply connected Lipschitz domain is connected

Let `Ω` be a bounded simply connected Lipschitz domain.

* For `z ∉ Ω̄`, the function `w ↦ w - z` has a continuous logarithm on `Ω` (lifting through the
  covering map `exp`, which uses simple connectivity), and this logarithm extends continuously to
  `Ω̄`, because near a boundary point `Ω` is the connected region above a Lipschitz graph
  (`exists_log_closure`). Hence every closed Lipschitz curve in `Ω̄` has winding number `0` about
  every point outside `Ω̄` (`windingNumber_eq_zero_of_lift`).
* A Lipschitz Jordan loop `γ` contained in `∂Ω` (from the boundary walk) separates a point of `Ω`
  from a point outside `Ω̄` near one of its points: the winding numbers differ by the jump `±1`
  (`exists_windingNumber_ne_of_frontier`).
* If `∂Ω` had a point `q` off the loop, then near `q` there would be both points of `Ω` and points
  outside `Ω̄` in a disc missing the loop, so the winding number of the loop would be `0` on `Ω`,
  contradicting the jump. Hence the loop is all of `∂Ω`, and `∂Ω` is connected
  (`isPreconnected_frontier_of_simplyConnected`).
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

/-- If a closed Lipschitz curve avoiding `z` has a continuous logarithm of `γ - z` taking the same
value at both ends, its winding number about `z` vanishes. -/
theorem windingNumber_eq_zero_of_lift {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {z : ℂ} {G : ℝ → ℂ}
    (hG : ContinuousOn G angleInterval)
    (hexp : ∀ θ ∈ angleInterval, Complex.exp (G θ) = γ θ - z) (hG2 : G anglePeriod = G 0) :
    windingNumber γ z = 0 := by
  have h := integral_deriv_div_eq_lift_sub hK Real.two_pi_pos.le (c := 1) hG
    (fun θ hθ => by simpa using hexp θ hθ)
  simp [windingNumber, h, hG2]

/-- Small charts: every boundary point of a Lipschitz domain has charts with arbitrarily small
boxes. -/
lemma exists_small_chart {Ω : Set ℂ} (hL : IsLipschitzDomain Ω) {p : ℂ} (hp : p ∈ frontier Ω)
    {d : ℝ} (hd : 0 < d) : ∃ (c : ℂ) (r h : ℝ) (K : NNReal) (f : ℝ → ℝ),
      IsChartAt Ω p c r h K f ∧ chartBox p c r h ⊆ ball p d := by
  obtain ⟨c, r, h, K, f, hch⟩ := hL.exists_chart hp
  have hr := hch.2.1
  have hh := hch.2.2.1
  set H' := min (h / 2) (d / 2) with hH'
  have hH'0 : 0 < H' := (by grind)
  set ρ' := min (r / 2) (H' / (2 * (K + 1))) with hρ'
  
  
  have hρ'H : ρ' ≤ H' / (2 * (K + 1)) := min_le_right _ _
  have hKρ : K * ρ' < H' := by
    calc _ ≤ _ := mul_le_mul_of_nonneg_left hρ'H K.coe_nonneg
      _ < H' := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  
  have hrec := isChartAt_recenter hL.1.1 hch hp (by simp [*])
    (by simp [*]) (lt_min (by linarith) (by positivity)) hH'0 (min_le_left _ _) (min_le_left _ _) le_rfl hKρ
  refine ⟨c, ρ', H', K, _, hrec, fun w hw => ?_⟩
  rw [mem_ball, dist_eq_norm, ← norm_mul_sub hch.1]
  have h1 := Complex.norm_le_abs_re_add_abs_im (c * (w - p))
  have h2 : ρ' ≤ H' / 2 := by
    have : H' / (2 * (K + 1)) ≤ H' / 2 :=
      div_le_div_of_nonneg_left hH'0.le (by norm_num) (by linarith)
    linarith
  have h3 : H' ≤ d / 2 := min_le_right _ _
  linarith [hw.1, hw.2]

/-- In a chart box, the part of `Ω` (the region above the graph) is preconnected. -/
lemma isPreconnected_chart_inter {Ω : Set ℂ} {p c : ℂ} {r h : ℝ} {K : NNReal} {f : ℝ → ℝ}
    (hch : IsChartAt Ω p c r h K f) : IsPreconnected (Ω ∩ chartBox p c r h) := by
  obtain ⟨hc, hr, hh, hf, hf0, hfb, hΩ⟩ := hch
  have hcc : c * conj c = 1 := by
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
  set Φ : ℝ × ℝ → ℂ := fun q =>
    p + conj c * (q.1 + ((f q.1 + q.2 * (h - f q.1) : ℝ) : ℂ) * Complex.I) with hΦ
  have hcoord : ∀ q : ℝ × ℝ, c * (Φ q - p) =
      (q.1 : ℂ) + ((f q.1 + q.2 * (h - f q.1) : ℝ) : ℂ) * Complex.I := fun q => by
    simp only [hΦ, add_sub_cancel_left, ← mul_assoc, hcc, one_mul]
  have hre : ∀ q : ℝ × ℝ, (c * (Φ q - p)).re = q.1 := fun q => by simp [hcoord]
  have him : ∀ q : ℝ × ℝ, (c * (Φ q - p)).im = f q.1 + q.2 * (h - f q.1) := fun q => by
    simp [hcoord]
  have hset : Ω ∩ chartBox p c r h = Φ '' (Ioo (-r) r ×ˢ Ioo 0 1) := by
    ext w
    constructor
    · rintro ⟨hwΩ, hw1, hw2⟩
      set X := (c * (w - p)).re
      set Y := (c * (w - p)).im
      
      have hlt : f X < Y := (hΩ w hw1 hw2).mp hwΩ
      have hY := abs_lt.mp hw2
      have hpos : 0 < h - f X := by linarith
      refine ⟨(X, (Y - f X) / (h - f X)), ⟨abs_lt.mp hw1, (by positivity),
        (div_lt_one hpos).mpr (by linarith)⟩, ?_⟩
      refine eq_of_re_im_eq (p := p) hc ?_ ?_
      · rw [hre]
      · rw [him]; simp only; field_simp; ring
    · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
      have hfq := abs_lt.mp (hfb q.1 (abs_lt.mpr hq1))
      have h1 : |(c * (Φ q - p)).re| < r := by grind
      have hpos : 0 < h - f q.1 := by linarith
      have hm1 : 0 < q.2 * (h - f q.1) := mul_pos hq2.1 hpos
      have hm2 : q.2 * (h - f q.1) < h - f q.1 := by nlinarith [hq2.2]
      have h2 : |(c * (Φ q - p)).im| < h := by
        grind
      refine ⟨(hΩ _ h1 h2).mpr ?_, h1, h2⟩
      rw [hre, him]; linarith
  rw [hset]
  refine (isPreconnected_Ioo.prod isPreconnected_Ioo).image Φ ?_
  have : Continuous Φ := by
    
    have := hf.continuous
    fun_prop
  exact this.continuousOn

/-- **Logarithms on the closure.** For a simply connected Lipschitz domain `Ω` and `z ∉ Ω̄`,
`w ↦ w - z` has a logarithm that is continuous on `Ω̄`. -/
theorem exists_log_closure {Ω : Set ℂ} (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω)
    {z : ℂ} (hz : z ∉ closure Ω) :
    ∃ L : ℂ → ℂ, ContinuousOn L (closure Ω) ∧ ∀ w ∈ closure Ω, Complex.exp (L w) = w - z := by
  have logOn {s : Set ℂ} (hs : IsSimplyConnected s) (ho : IsOpen s) (hn : z ∉ s) :=
    Complex.exists_continuousOn_eqOn_exp_comp hs ho (g := fun w : ℂ => w - z)
      (continuous_id.sub continuous_const).continuousOn (by
        rintro ⟨x, hx, heq⟩
        exact hn (sub_eq_zero.mp heq ▸ hx))
  obtain ⟨L, hLcont, hexp⟩ := logOn hsc hL.1.1 (fun h => hz (subset_closure h))
  have hlim (p : ℂ) (hp : p ∈ closure Ω) : ∃ y, Tendsto L (𝓝[Ω] p) (𝓝 y) := by
    by_cases hpΩ : p ∈ Ω
    · exact ⟨_, hLcont p hpΩ⟩
    have hf : p ∈ frontier Ω := hL.1.1.frontier_eq ▸ ⟨hp, hpΩ⟩
    let d := dist z p
    have hd : 0 < d := dist_pos.mpr fun h => hz (h ▸ hp)
    obtain ⟨c, r, h, K, f, hch, hsub⟩ := exists_small_chart hL hf hd
    let B := chartBox p c r h
    have hB : B ∈ 𝓝 p := (isOpen_chartBox _ _ _ _).mem_nhds hch.center_mem_box
    haveI := (convex_ball p d).contractibleSpace (nonempty_ball.mpr hd)
    obtain ⟨g, hgc, hge⟩ := logOn (s := ball p d) (inferInstanceAs (SimplyConnectedSpace _))
      isOpen_ball (lt_irrefl d)
    obtain ⟨w, hwB, hwΩ⟩ := mem_closure_iff_nhds.mp hp B hB
    let G := fun x => g x + (L w - g w)
    have hG : ContinuousOn G (ball p d) := hgc.add continuousOn_const
    have he : EqOn L G (Ω ∩ B) := by
      refine eqOn_of_exp_eq (isPreconnected_chart_inter hch) (hLcont.mono inter_subset_left)
        (hG.mono (inter_subset_right.trans hsub)) (fun x hx => ?_) ⟨hwΩ, hwB⟩ (by simp [G])
      change Complex.exp (L x) = Complex.exp (g x + (L w - g w))
      rw [Complex.exp_add, Complex.exp_eq_exp_iff_exp_sub_eq_one.mp
        ((hexp hwΩ).trans (hge (hsub hwB)).symm), mul_one]
      exact (hexp hx.1).trans (hge (hsub hx.2)).symm
    refine ⟨_, (hG.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hd))).continuousWithinAt.congr' ?_⟩
    exact he.symm.eventuallyEq_of_mem (inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds hB))
  have hc := continuousOn_extendFrom Subset.rfl hlim
  refine ⟨_, hc, fun w hw => ?_⟩
  have he : EqOn (Complex.exp ∘ extendFrom Ω L) (fun w : ℂ => w - z) Ω := fun x hx => by
    simpa [Function.comp_def, extendFrom_extends hLcont x hx] using hexp hx
  exact he.of_subset_closure (Complex.continuous_exp.comp_continuousOn hc)
    (continuous_id.sub continuous_const).continuousOn subset_closure Subset.rfl hw

/-- **The jump across a boundary loop.** A Lipschitz `2π`-periodic curve, injective on
`[0, 2π)`, with image in `∂Ω`, has different winding numbers about some point of `Ω` and some
point outside `Ω̄`. -/
theorem exists_windingNumber_ne_of_frontier {Ω : Set ℂ} (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hper : Function.Periodic γ anglePeriod)
    (hinj : InjOn γ angleIco) (hsub : γ '' angleInterval ⊆ frontier Ω) :
    ∃ z₁ ∈ Ω, ∃ z₂, z₂ ∉ closure Ω ∧ windingNumber γ z₁ ≠ windingNumber γ z₂ := by
  obtain ⟨σ, u, v, hσ, hm, hlim⟩ := exists_frontier_winding_jump hL hK hper hinj hsub
  have hne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨s, hs, h⟩ := (hm.and (hlim.eventually (isOpen_ne.mem_nhds hne))).exists
  exact ⟨u s, hs.1, v s, hs.2, sub_ne_zero.mp h⟩

/-- Boundary points of a Lipschitz domain are limits of exterior points. -/
lemma mem_closure_compl_closure {Ω : Set ℂ} (hL : IsLipschitzDomain Ω) {q : ℂ}
    (hq : q ∈ frontier Ω) : q ∈ closure (closure Ω)ᶜ := by
  obtain ⟨V, B, -, hqV, -, hB, -, hcl⟩ := exists_exterior_box hL hq
  exact closure_mono hB ((by grind))

/-- **External theorem E3, connectedness of the boundary.** The boundary of a bounded simply
connected Lipschitz domain is connected. -/
theorem isPreconnected_frontier_of_simplyConnected {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) :
    IsPreconnected (frontier Ω) := by
  by_contra hnc
  obtain ⟨γ, ⟨K, hK⟩, hper, hinj, hsub, -⟩ := exists_jordanLoop_frontier hb hL
  have hclosed := hper.eq
  set S := γ '' angleInterval with hS
  obtain ⟨q, hqf, hqS⟩ : ∃ q ∈ frontier Ω, q ∉ S := by
    by_contra hall
    push_neg at hall
    exact hnc (subset_antisymm hsub hall ▸ isPreconnected_Icc.image γ hK.continuous.continuousOn)
  have hγcl  := fun θ =>
    frontier_subset_closure (hsub (mem_image_Icc_of_periodic hper θ))
  -- winding numbers vanish outside the closure
  have hzero : ∀ z, z ∉ closure Ω → windingNumber γ z = 0 := fun z hz => by
    obtain ⟨L, hLc, hLexp⟩ := exists_log_closure hL hsc hz
    refine windingNumber_eq_zero_of_lift hK
      (hLc.comp hK.continuous.continuousOn fun θ _ => hγcl θ)
      (fun θ _ => hLexp _ (hγcl θ)) (by simp [hclosed])
  obtain ⟨z₁, hz₁, z₂, hz₂, hne⟩ := exists_windingNumber_ne_of_frontier hL hK hper hinj hsub
  -- a disc around `q` missing the loop
  
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ((isCompact_Icc.image hK.continuous).isClosed).isOpen_compl q hqS
  
  obtain ⟨a, haΩ, haB⟩ := mem_closure_iff.mp (frontier_subset_closure hqf) ε hε
  obtain ⟨b, hbΩ, hbB⟩ := mem_closure_iff.mp (mem_closure_compl_closure hL hqf) ε hε
  have hab  :=
    windingNumber_const_of_isPreconnected hK hclosed (convex_ball q ε).isPreconnected (disjoint_left.mpr fun x hx hxS => hball hx hxS)
      (by rw [mem_ball, dist_comm]; exact haB) (by rw [mem_ball, dist_comm]; exact hbB)
  have hΩS : Disjoint Ω S := by
    refine disjoint_left.mpr fun x hx hxS => ?_
    have := hsub hxS
    rw [hL.1.1.frontier_eq] at this
    exact this.2 hx
  grind [windingNumber_const_of_isPreconnected hK hclosed hL.1.2.isPreconnected hΩS hz₁ haΩ]

end PolyaNeumann
