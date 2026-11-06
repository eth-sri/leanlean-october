module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.WindingJump

/-!
# Orientation of a Lipschitz Jordan boundary

Let `Ω` be a bounded Lipschitz domain and `γ` a Lipschitz, `2π`-periodic parametrization of
`∂Ω`, injective on `[0, 2π)`, such that the exterior `ℂ \ Ω̄` is connected. Then the winding
number of `γ` is a constant `σ = ±1` on `Ω` and vanishes off `Ω̄`
(`windingNumber_pm_one_of_jordan`). The value `±1` comes from the jump of the winding number
across the boundary at a chart point (`windingNumber_jump`).
-/

public section

open MeasureTheory Set Filter Metric
open scoped Real Topology



namespace PolyaNeumann

/-- In a Lipschitz chart box, points strictly below the graph are not in the closure. -/
lemma chart_notMem_closure     
    (hf : LipschitzWith K f)
    (hΩ : ∀ w : ℂ, |(c * (w - p)).re| < r → |(c * (w - p)).im| < h →
      (w ∈ Ω ↔ f (c * (w - p)).re < (c * (w - p)).im))
     (hr : |(c * (w - p)).re| < r) (hh : |(c * (w - p)).im| < h)
    (hlt : (c * (w - p)).im < f (c * (w - p)).re) : w ∉ closure Ω := by
  have hg : Continuous fun v : ℂ => c * (v - p) := by fun_prop
  set U : PlanarSet := {v | |(c * (v - p)).re| < r} ∩ {v | |(c * (v - p)).im| < h} ∩
    {v | (c * (v - p)).im < f (c * (v - p)).re} with hU
  have hUo : IsOpen U := by
    refine ((isOpen_lt ?_ continuous_const).inter (isOpen_lt ?_ continuous_const)).inter
      (isOpen_lt ?_ ?_)
    · fun_prop
    · fun_prop
    · exact Complex.continuous_im.comp hg
    · exact hf.continuous.comp (Complex.continuous_re.comp hg)
  have hdisj : Disjoint U Ω := by
    grind
  exact (Set.disjoint_left.mp (hdisj.closure_right hUo) ⟨⟨hr, hh⟩, hlt⟩)

/-- In a Lipschitz chart box, boundary points lie on the graph. -/
lemma chart_frontier_graph  (hΩo : IsOpen Ω)   
     (hf : LipschitzWith K f)
    (hΩ : ∀ w : ℂ, |(c * (w - p)).re| < r → |(c * (w - p)).im| < h →
      (w ∈ Ω ↔ f (c * (w - p)).re < (c * (w - p)).im))
     (hw : w ∈ frontier Ω) (hr : |(c * (w - p)).re| < r)
    (hh : |(c * (w - p)).im| < h) : (c * (w - p)).im = f (c * (w - p)).re := by
  rw [hΩo.frontier_eq] at hw
  grind [chart_notMem_closure]

/-- The winding number under a rigid motion `w ↦ c (w - p)` (`c ≠ 0`). -/
lemma windingNumber_affine γ  (hc : c ≠ 0) p w :
    windingNumber (fun θ => c * (γ θ - p)) w = windingNumber γ (p + c⁻¹ * w) := by
  unfold windingNumber
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hd : deriv (fun θ => c * (γ θ - p)) θ = c * deriv γ θ := by
    simp_all
  grind

/-- Transversal interior and exterior curves at a Jordan boundary point have winding jump ±1. -/
theorem exists_windingNumber_jump_of_frontier (hL : IsLipschitzDomain Ω)
    (hK : LipschitzWith K γ) (hper : Function.Periodic γ circlePeriod)
    (hinj : InjOn γ (Ico 0 circlePeriod)) (hsub : γ '' boundaryInterval ⊆ frontier Ω) :
    ∃ (zi ze : ℝ → ℂ) (δ : ℝ) (σ : ℂ), 0 < δ ∧ (σ = 1 ∨ σ = -1) ∧
      (∀ s ∈ Ioo 0 δ, zi s ∈ Ω ∧ ze s ∉ closure Ω) ∧
      Tendsto (fun s => windingNumber γ (zi s) - windingNumber γ (ze s))
        (𝓝[>] 0) (𝓝 σ) := by
  have hpi  := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hΩo  := hL.1.1
  have hfront  := fun θ => hsub (mem_image_Icc_of_periodic hper θ)
  set p := γ 0 with hpdef
  obtain ⟨c, r, h, K', f, hc, hr, hh, hf, hf0, -, hΩ⟩ := hL.2 p (hfront 0)
  have hc0 : c ≠ 0 := by
    measurability
  set γ' : ComplexCurve := fun θ => c * (γ θ - p) with hγ'
  have hK' : LipschitzWith K γ' := LipschitzWith.of_dist_le_mul fun x y => by
    simp only [hγ', dist_eq_norm, ← mul_sub, norm_mul, hc, one_mul, sub_sub_sub_cancel_right]
    exact?
  have hper' : Function.Periodic γ' circlePeriod := fun θ => by simp only [hγ', hper θ]
  have h0' : γ' 0 = 0 := by simp [hγ', hpdef]
  set m := min r h with hm
  have hm0  := lt_min hr hh
  set η := min (π / 2) (m / (2 * (K + 1))) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  have hηπ2 : η ≤ π / 2 := min_le_left _ _
  have hηπ : η < π := hηπ2.trans_lt (by linarith)
  have hsmall : ∀ θ ∈ Icc (-η) η, ‖γ' θ‖ < m := by
    intro θ hθ
    have h1 : ‖γ' θ‖ ≤ K * |θ| := by
      have := hK'.dist_le_mul θ 0
      rwa [h0', dist_zero_right, Real.dist_eq, sub_zero] at this
    have h2  := abs_le.mpr ⟨hθ.1, hθ.2⟩
    have h3 : (K : ℝ) * η ≤ K * (m / (2 * (K + 1))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) K.coe_nonneg
    have h4 : (K : ℝ) * (m / (2 * (K + 1))) < m := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [K.coe_nonneg]
    nlinarith
  have hbox : ∀ θ ∈ Icc (-η) η, |(γ' θ).re| < r ∧ |(γ' θ).im| < h := fun θ hθ =>
    ⟨(Complex.abs_re_le_norm _).trans_lt ((hsmall θ hθ).trans_le (min_le_left _ _)),
      (Complex.abs_im_le_norm _).trans_lt ((hsmall θ hθ).trans_le (min_le_right _ _))⟩
  have hgraph  := fun θ hθ =>
    chart_frontier_graph hΩo hf hΩ (hfront θ) (hbox θ hθ).1 (hbox θ hθ).2
  have hinj' : InjOn γ' (Icc (-η) η) := by
    intro θ₁ h₁ θ₂ h₂ he
    have he' : γ θ₁ = γ θ₂ := by
      grind
    have hmod : ∀ θ, γ (toIcoMod h2pi 0 θ) = γ θ := fun θ => hper.sub_zsmul_eq _
    have hmem := fun θ => by
      have := toIcoMod_mem_Ico h2pi 0 θ
      rwa [zero_add] at this
    have heq := hinj (hmem θ₁) (hmem θ₂) (by rw [hmod, hmod, he'])
    obtain ⟨n, hn⟩ := (toIcoMod_eq_toIcoMod h2pi).mp heq
    rw [zsmul_eq_mul] at hn
    have hb1 : θ₂ - θ₁ ≤ π := by linarith [h₁.1, h₂.2]
    have hb2 : -π ≤ θ₂ - θ₁ := by linarith [h₁.2, h₂.1]
    have hn1 : (n : ℝ) < 1 := by nlinarith
    have hn2 : (-1 : ℝ) < n := by nlinarith
    have hn0 : n = 0 := by
      have := Int.cast_lt.mp (show ((n : ℤ) : ℝ) < ((1 : ℤ) : ℝ) by simpa using hn1)
      have := Int.cast_lt.mp (show ((-1 : ℤ) : ℝ) < ((n : ℤ) : ℝ) by simpa using hn2)
      omega
    rw [hn0, Int.cast_zero, zero_mul, sub_eq_zero] at hn
    exact hn.symm
  have hfar' : ∀ θ ∈ Icc η (2 * π - η), γ' θ ≠ 0 := by
    grind [Set.InjOn]
  obtain ⟨σ', hσ', hlim⟩ := windingNumber_jump hK' hper' hη0 hηπ h0' hgraph hinj' hfar'
  have hcz : ∀ x : ℂ, c * (p + c⁻¹ * x - p) = x := fun x => by field_simp; ring
  let zi : ℝ → ℂ := fun s => p + c⁻¹ * ((s : ℂ) * Complex.I)
  let ze : ℝ → ℂ := fun s => p + c⁻¹ * (-((s : ℂ) * Complex.I))
  refine ⟨zi, ze, h, σ', hh, hσ', ?_, ?_⟩
  · intro s hs
    constructor
    · change p + c⁻¹ * ((s : ℂ) * Complex.I) ∈ Ω
      rw [hΩ _ (by rw [hcz]; simpa using hr) (by rw [hcz]; simpa [abs_of_pos hs.1] using hs.2),
        hcz]
      simpa [hf0] using hs.1
    · change p + c⁻¹ * (-((s : ℂ) * Complex.I)) ∉ closure Ω
      refine chart_notMem_closure hf hΩ (by rw [hcz]; simpa using hr)
        (by rw [hcz]; simpa [abs_of_pos hs.1] using hs.2) ?_
      rw [hcz]
      simpa [hf0] using hs.1
  · simpa only [zi, ze, hγ', windingNumber_affine γ hc0] using hlim

/-- **Orientation of a Lipschitz Jordan boundary.** For a bounded Lipschitz domain `Ω` with a
Lipschitz `2π`-periodic boundary parametrization `γ`, injective on `[0, 2π)`, and connected
exterior `ℂ \ Ω̄`, the winding number of `γ` is a constant `σ = ±1` on `Ω` and vanishes off
`Ω̄`. -/
theorem windingNumber_pm_one_of_jordan  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω)   (hK : LipschitzWith K γ)
    (hper : Function.Periodic γ circlePeriod) (hinj : Set.InjOn γ (Set.Ico 0 circlePeriod))
    (him : γ '' boundaryInterval = frontier Ω) (hext : IsConnected (closure Ω)ᶜ) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ (∀ z ∈ Ω, windingNumber γ z = σ) ∧
      ∀ z, z ∉ closure Ω → windingNumber γ z = 0 := by
  have hpi  := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hclosed : γ circlePeriod = γ 0 := by simpa using hper 0
  have hΩo  := hL.1.1
  have hΩdisj : Disjoint Ω (γ '' boundaryInterval) := by
    rw [him, Set.disjoint_iff_inter_eq_empty]
    exact hΩo.inter_frontier_eq
  obtain ⟨z₀, hz₀⟩ := hL.1.2.nonempty
  have hin : ∀ z ∈ Ω, windingNumber γ z = windingNumber γ z₀ := fun z hz =>
    windingNumber_const_of_isPreconnected hK hclosed hL.1.2.isPreconnected hΩdisj hz hz₀
  -- the winding number vanishes on the exterior
  obtain ⟨R, hR⟩ := hb.closure.subset_ball 0
  have hR0  := le_trans (norm_nonneg z₀)
    (mem_ball_zero_iff.mp (hR (subset_closure hz₀))).le
  set w : ℂ := ((R + K + 1 : ℝ) : ℂ) with hw
  have hwn : ‖w‖ = R + K + 1 := by
    rw [hw, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hwext : w ∉ closure Ω := fun h => by
    have := mem_ball_zero_iff.mp (hR h); linarith [K.coe_nonneg]
  have hw0 : windingNumber γ w = 0 := by
    refine windingNumber_eq_zero_of_far hK hclosed (d := K + 1) (by linarith) fun θ hθ => ?_
    have hγθ  :=
      mem_ball_zero_iff.mp (hR (frontier_subset_closure (him ▸ Set.mem_image_of_mem γ hθ)))
    have := norm_sub_norm_le w (γ θ)
    rw [norm_sub_rev] at this
    linarith
  have hextdisj : Disjoint (closure Ω)ᶜ (γ '' boundaryInterval) := by
    rw [him]
    exact (disjoint_compl_left (a := closure Ω)).mono_right frontier_subset_closure
  have hout : ∀ z, z ∉ closure Ω → windingNumber γ z = 0 := fun z hz =>
    (windingNumber_const_of_isPreconnected hK hclosed hext.isPreconnected hextdisj hz
      hwext).trans hw0
  obtain ⟨zi, ze, δ, σ, hδ, hσ, hside, hlim⟩ :=
    exists_windingNumber_jump_of_frontier hL hK hper hinj him.le
  have hev : ∀ᶠ s : ℝ in 𝓝[>] 0,
      windingNumber γ (zi s) - windingNumber γ (ze s) = windingNumber γ z₀ := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with s hs
    rw [hin _ (hside s hs).1, hout _ (hside s hs).2, sub_zero]
  have hσeq := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (EventuallyEq.symm hev))
  rcases hσ with h | h
  · exact ⟨1, Or.inl rfl, fun z hz => by rw [hin z hz, ← hσeq, h]; simp, hout⟩
  · exact ⟨-1, Or.inr rfl, fun z hz => by rw [hin z hz, ← hσeq, h]; simp, hout⟩

end PolyaNeumann
