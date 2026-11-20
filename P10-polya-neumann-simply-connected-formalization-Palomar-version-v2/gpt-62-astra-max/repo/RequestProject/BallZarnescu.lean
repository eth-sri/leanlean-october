module

public import Mathlib.MeasureTheory.Integral.Indicator
public import RequestProject.CircleAnalysisNotation

public import RequestProject.SmoothDomain
public import RequestProject.Transport
public import RequestProject.LipschitzChange
public import RequestProject.JordanWinding
public import RequestProject.GreenWinding
public import RequestProject.ExteriorConnected
public import RequestProject.WeightedMass
public import RequestProject.BZMap
public import RequestProject.PlanarNotation

/-!
# The Ball–Zarnescu approximation (External theorem BZ and Section 10)

* `BallZarnescuApprox Ω`: the data of External theorem BZ along a sequence `ε_n → 0`
  (homeomorphisms `f_n` of the plane with `f_n(Ω) = Ω_n ⊂ Ω` smooth, uniformly bi-Lipschitz on the
  closures, equal to the identity off shrinking closed collars, converging uniformly to the
  identity on `Ω̄`), and its existence `exists_ballZarnescu` (proved, via the flow-collar
  construction of `BZDist`–`BZMap`);
* `eventually_boundaryParam_ballZarnescu` (proved): for all large `n`, the transported curve
  `f_n ∘ γ` is a monotone Lipschitz reparametrization of a positively oriented boundary
  parametrization of `Ω_n`.
-/

@[expose] public section

open scoped Real ComplexConjugate
open MeasureTheory Filter Topology Set

noncomputable section

namespace PolyaNeumann

/-- The data of External theorem BZ (smooth topology-preserving inner approximation), along a
sequence `ε_n → 0` of the approximation parameter: homeomorphisms `f_n` of `ℝ² = ℂ` with
`f_n(Ω) = Ω_n ⊂ Ω` a bounded smooth domain (and hence `f_n(∂Ω) = ∂Ω_n`), uniformly bi-Lipschitz on
the closures, equal to the identity off closed boundary collars `C_n` which shrink to `∂Ω` (every
point of `Ω` lies outside `C_n` for all large `n`), and converging uniformly to the identity on
`Ω̄`. -/
structure BallZarnescuApprox (Ω : Set ℂ) where
  /-- The homeomorphisms `f_n`. -/
  map : ℕ → ℂ ≃ₜ ℂ
  smooth : ∀ n, IsSmoothDomain (map n '' Ω)
  /-- A common bi-Lipschitz constant. -/
  lip : NNReal
  /-- The boundary collars `C_n`. -/
  collar : ℕ → Set ℂ
  collar_closed : ∀ n, IsClosed (collar n)
  eq_self : ∀ n x, x ∉ collar n → map n x = x
  collar_shrink : ∀ x ∈ Ω, ∀ᶠ n in atTop, x ∉ collar n
  tendsto : TendstoUniformlyOn (fun n => (map n : ℂ → ℂ)) id atTop (closure Ω)
  /-- `f_n(Ω̄) ⊂ Ω`. -/
  closure_subset : ∀ n, map n '' closure Ω ⊆ Ω
  lip_pos : 0 < lip
  /-- The maps and their inverses are globally `lip`-Lipschitz. -/
  lipschitzWith : ∀ n, LipschitzWith lip (map n)
  lipschitzWith_symm : ∀ n, LipschitzWith lip (map n).symm

namespace BallZarnescuApprox

variable {Ω : Set ℂ} (A : BallZarnescuApprox Ω)

lemma subset (n : ℕ) : A.map n '' Ω ⊆ Ω := (image_mono subset_closure).trans (A.closure_subset n)

/-- Every interior point is eventually fixed, and the approximations lie in `Ω`. -/
lemma area_tendsto (hb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω) :
    Tendsto (fun n => volume (A.map n '' Ω)) atTop (𝓝 (volume Ω)) := by
  refine tendsto_measure_of_tendsto_indicator atTop (fun n => ((A.map n).isOpenMap _ hΩ).measurableSet)
    hΩ.measurableSet hb.measure_lt_top.ne (.of_forall A.subset) fun x => ?_
  by_cases hx : x ∈ Ω
  · filter_upwards [A.collar_shrink x hx] with n hn
    exact ⟨fun _ => hx, fun _ => ⟨x, hx, A.eq_self n x hn⟩⟩
  · exact .of_forall fun n => ⟨fun h => A.subset n h, fun h => (hx h).elim⟩

lemma fderiv_eq_id {n x} (h : x ∉ A.collar n) : fderiv ℝ (A.map n) x = ContinuousLinearMap.id ℝ ℂ := by
  have he : (A.map n : ℂ → ℂ) =ᶠ[𝓝 x] id :=
    Filter.mem_of_superset ((A.collar_closed n).isOpen_compl.mem_nhds h) (A.eq_self n)
  rw [he.fderiv_eq, fderiv_id]

lemma curve_tendsto {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) :
    TendstoUniformlyOn (fun n => A.map n ∘ γ) γ atTop angleInterval :=
  (A.tendsto.comp γ).mono fun _ hθ => frontier_subset_closure (hγ.image ▸ mem_image_of_mem γ hθ)

end BallZarnescuApprox

/-- External theorem BZ (Ball–Zarnescu, inner approximation case of Theorem 5.1(ii) and
Remark 5.3), along the sequence `ε_n = ε₀/(n+2)`: a bounded Lipschitz domain admits the
approximation data of `BallZarnescuApprox`. In the notation of the paper's External theorem BZ,
`C_ε = {|ρ| ≤ 3ε}` is closed, and `⋂_δ ⋃_{ε<δ} C_ε ⊂ ∂Ω` gives `collar_shrink`.

Proved here (rather than cited) by a flow-collar construction: `f_n` pushes points of the collar
`{|d_Ω| ≤ 2 M T_n}` along the flow of a field transversal to `∂Ω`, so that the boundary is moved
onto a level set `{ρ_n = ε_n}` of a smooth function close to the signed distance; here the
parameter is `T_n = T₀/(n+1)` instead of `ε₀/(n+2)`, which plays no role downstream. -/
theorem exists_ballZarnescu {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) : Nonempty (BallZarnescuApprox Ω) := by
  have hΩu : Ωᶜ.Nonempty := by
    obtain ⟨R, hR⟩ := hb.subset_closedBall 0
    refine ⟨((|R| + 1 : ℝ) : ℂ), fun h => ?_⟩
    have := hR h
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)] at this
    linarith [le_abs_self R]
  obtain ⟨S⟩ := exists_bzSetting hb hL hL.1.2.nonempty hΩu
  set T : ℕ → ℝ := fun n => S.T₀ * (1 / (n + 1))
  have hTpos : ∀ n, 0 < T n := fun n => by have := S.T₀_pos; positivity
  have hTle : ∀ n, T n ≤ S.T₀ := fun n => by
    have := S.T₀_pos
    bound
  have hTlim : Tendsto T atTop (𝓝 0) := by
    grind [(tendsto_one_div_add_atTop_nhds_zero_nat ).const_mul S.T₀]
  choose D hD using fun n => exists_bzLevelData S (hTpos n) (hTle n)
  have hM := S.M_pos
  refine ⟨{
    map := fun n => (D n).homeo
    smooth := fun n => (D n).isSmoothDomain_image hL.1 hΩu
    lip := Real.toNNReal (max S.K₁ S.K₂)
    collar := fun n => {x | |signedDist Ω x| ≤ 2 * S.M * T n}
    collar_closed := fun n =>
      isClosed_le (continuous_signedDist Ω).abs continuous_const
    eq_self := fun n x hx => by
      
      apply (D n).f_eq_self
      rw [hD n]; exact not_le.mp hx
    collar_shrink := fun x hx => by
      have hd  := (signedDist_pos_iff hL.1.1 hΩu).mpr hx
      have h1 : Tendsto (fun n => 2 * S.M * T n) atTop (𝓝 0) := by
        grind [hTlim.const_mul (2 * S.M)]
      filter_upwards [h1.eventually (gt_mem_nhds hd)] with n hn
      simp [not_le, abs_of_pos hd]
      exact hn
    tendsto := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro e he
      have h1 : Tendsto (fun n => S.M * (T n / 2)) atTop (𝓝 0) := by
        simpa using (hTlim.div_const 2).const_mul S.M
      filter_upwards [h1.eventually (gt_mem_nhds he)] with n hn x _
      rw [dist_comm, dist_eq_norm]
      have := (D n).norm_f_sub_le x
      rw [hD n] at this
      exact lt_of_le_of_lt this hn
    closure_subset := fun n => by
      rintro _ ⟨x, hx, rfl⟩
      exact (D n).f_mem_of_mem_closure hL.1.1 hΩu hx
    lip_pos := by
      have : 0 < S.K₁ := by
        unfold BZSetting.K₁
        have := S.La_nonneg; have := S.Lb_nonneg
        positivity
      positivity
    lipschitzWith := fun n => (D n).lipschitzWith_f.weaken
      (Real.toNNReal_le_toNNReal (le_max_left _ _))
    lipschitzWith_symm := fun n => (D n).lipschitzWith_g.weaken
      (Real.toNNReal_le_toNNReal (le_max_right _ _)) }⟩

/-- Lemma 10.14 (geometric part): for all large `n`, the transported curve `f_n ∘ γ` is a
monotone Lipschitz reparametrization of a positively oriented boundary parametrization of
`Ω_n = f_n(Ω)`. Positive orientation for large `n` comes from the convergence of the signed
area integrals of `f_n ∘ γ` to that of `γ`, which is `2|Ω| > 0`. -/
theorem eventually_boundaryParam_ballZarnescu {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    (A : BallZarnescuApprox Ω) :
    ∀ᶠ n in atTop, ∃ γ' : ℝ → ℂ, IsBoundaryParam (A.map n '' Ω) γ' ∧
      ∃ τ : ℝ → ℝ, Monotone τ ∧ (∃ Kτ, LipschitzWith Kτ τ) ∧ τ 0 = 0 ∧
        τ anglePeriod = anglePeriod ∧ γ' ∘ τ = A.map n ∘ γ := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  have hαL := fun n => (A.lipschitzWith n).comp hKγ
  have hαp : ∀ n, Function.Periodic (A.map n ∘ γ) anglePeriod := fun n θ => by
    simp [hγ.periodic θ]
  have hαinj  := fun n =>
    (A.map n).injective.comp_injOn hγ.injOn
  have hαim : ∀ n, (A.map n ∘ γ) '' angleInterval = frontier (A.map n '' Ω) := fun n => by
    rw [Set.image_comp, hγ.image, Homeomorph.image_frontier]
  have htend := A.curve_tendsto hγ
  have hconv := tendsto_integral_signedAreaDensity 
    (fun n => (hαL n).weaken (le_max_left _ _)) (hKγ.weaken (le_max_right _ _)) hαp
    hγ.periodic htend
  have harea0 : ∫ₚ θ, signedAreaDensity γ θ = 2 * (volume Ω).toReal :=
    hγ.area
  rw [harea0] at hconv
  
  filter_upwards [hconv.eventually (Ioi_mem_nhds (by
    have := ENNReal.toReal_pos (hL.1.1.measure_pos volume hL.1.2.nonempty).ne'
      hb.measure_lt_top.ne
    positivity))] with n hn
  have hLn  := (A.smooth n).isLipschitzDomain
  have hbn  := hb.subset (A.subset n)
  
  obtain ⟨σ, hσ, hin, hout⟩ :=
    windingNumber_pm_one_of_jordan hbn hLn (hαL n) (hαp n) (hαinj n) (hαim n) (isConnected_compl_closure_of_frontier hbn hLn (by
      rw [← hαim n]; exact isPreconnected_Icc.image _ (hαL n).continuous.continuousOn))
  have harea := integral_signedAreaDensity_of_winding hLn.1.1 hbn (hαL n) (hαim n) σ hin hout
  obtain ⟨γ1, ⟨K1, hK1⟩, hper1, hinj1, him1, hspeed, harea1, τ, hτm, hτL, hτ0, hτ2, hτc⟩ :=
    exists_constSpeed_reparam (hαL n) (hαp n) (hαinj n)
  refine ⟨γ1, ⟨⟨K1, hK1⟩, hper1, hinj1, him1.trans (hαim n), hspeed, ?_⟩,
    τ, hτm, hτL, hτ0, hτ2, hτc⟩
  show ∫ₚ θ, signedAreaDensity γ1 θ = _
  rw [harea1, harea]
  
  rcases hσ with rfl | rfl
  · ring
  · rw [harea] at hn
    have : 0 ≤ (volume (A.map n '' Ω)).toReal := ENNReal.toReal_nonneg
    linarith

end PolyaNeumann

end
