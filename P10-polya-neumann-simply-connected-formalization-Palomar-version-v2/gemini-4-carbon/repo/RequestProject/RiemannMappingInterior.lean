module

public import RequestProject.LocalConformalH1
public import RequestProject.GreenWinding
public import RequestProject.BoundaryConnected
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.Order.IsLUB
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Topology.Piecewise
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Tactic

@[expose] public section
noncomputable section

namespace PolyaNeumann.RiemannInterior

section

open Complex Metric Filter Topology Set

theorem deriv_ne_zero_of_injOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) {a : ℂ} (ha : a ∈ U) :
    deriv f a ≠ 0 := by
  intro h0
  have hUa : U ∈ 𝓝 a := hU.mem_nhds ha
  have han : AnalyticAt ℂ f a := (hf.analyticOnNhd hU) a ha
  set g : ℂ → ℂ := fun z => f z - f a with hg
  have hgan : AnalyticAt ℂ g a := han.sub analyticAt_const
  have hnz : ¬ ∀ᶠ z in 𝓝 a, g z = 0 := fun hev => by
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1 (inter_mem hev hUa)
    have hmem : a + (ε / 2 : ℝ) ∈ ball a ε := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]; linarith
    have h1 := hεsub hmem
    have h2 : ((ε / 2 : ℝ) : ℂ) = 0 := by linear_combination hinj h1.2 ha (sub_eq_zero.1 h1.1)
    linarith [show ε / 2 = 0 by exact_mod_cast h2]
  obtain ⟨n, h, hhan, hha, hgeq⟩ := hgan.exists_eventuallyEq_pow_smul_nonzero_iff.2 hnz
  simp only [smul_eq_mul] at hgeq
  have hga : g a = 0 := by simp [hg]
  have hderg : deriv g a = 0 := by rw [hg, deriv_sub_const, h0]
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with hn | hn
    · exfalso; interval_cases n
      · have := hgeq.self_of_nhds; simp only [pow_zero, one_mul] at this; exact hha (this ▸ hga)
      · have hd : HasDerivAt (fun z => (z - a) ^ 1 * h z) (1 * h a + (a - a) ^ 1 * deriv h a) a :=
          (by simpa using (hasDerivAt_id a).sub_const a : HasDerivAt (fun z => (z - a) ^ 1) 1 a).mul
            hhan.differentiableAt.hasDerivAt
        have := hd.deriv
        rw [← Filter.EventuallyEq.deriv_eq hgeq, hderg] at this; simp at this; exact hha this.symm
    · exact hn
  have hn0 : n ≠ 0 := by omega
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c ^ n = h a := IsAlgClosed.exists_pow_nat_eq _ (by omega)
  have hc0 : c ≠ 0 := by rintro rfl; exact hha (by rw [← hc, zero_pow hn0])
  set q : ℂ → ℂ := fun z => h z / h a with hq
  have hqa : q a = 1 := div_self hha
  have hqan : AnalyticAt ℂ q a := hhan.div analyticAt_const hha
  have hslit : q a ∈ slitPlane := hqa.symm ▸ one_mem_slitPlane
  set ψ : ℂ → ℂ := fun z => c * exp (log (q z) / n) with hψ
  have hψan : AnalyticAt ℂ ψ a :=
    analyticAt_const.mul ((hqan.clog hslit).div analyticAt_const (by exact_mod_cast hn0)).cexp
  have hψpow : ∀ᶠ z in 𝓝 a, ψ z ^ n = h z := by
    filter_upwards [hqan.continuousAt.preimage_mem_nhds (isOpen_slitPlane.mem_nhds hslit)] with z hz
    rw [hψ, mul_pow, hc, ← exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hn0),
      exp_log (slitPlane_ne_zero hz), hq]
    field_simp
  set φ : ℂ → ℂ := fun z => (z - a) * ψ z with hφ
  have hφan : AnalyticAt ℂ φ a := (analyticAt_id.sub analyticAt_const).mul hψan
  have hφa : φ a = 0 := by simp [hφ]
  have hψa : ψ a = c := by simp [hψ, hqa]
  have hφd : HasDerivAt φ c a := by
    simpa [hψa, Pi.mul_def] using ((hasDerivAt_id a).sub_const a).mul hψan.differentiableAt.hasDerivAt
  have hφnc : ¬ ∀ᶠ z in 𝓝 a, φ z = φ a := fun hev => by
    have : deriv φ a = 0 := by rw [Filter.EventuallyEq.deriv_eq (hev : φ =ᶠ[𝓝 a] fun _ => φ a)]; simp
    exact hc0 (hφd.deriv ▸ this)
  have hopen : 𝓝 (φ a) ≤ map φ (𝓝 a) :=
    hφan.eventually_constant_or_nhds_le_map_nhds.resolve_left hφnc
  have hVmem : {z | z ∈ U ∧ g z = φ z ^ n} ∈ 𝓝 a := by
    filter_upwards [hUa, hgeq, hψpow] with z hz h1 h2; exact ⟨hz, by rw [h1, hφ, mul_pow, h2]⟩
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 (show φ '' {z | z ∈ U ∧ g z = φ z ^ n} ∈ 𝓝 0 by
    rw [← hφa]; exact hopen (image_mem_map hVmem))
  set ε : ℂ := ((δ / 2 : ℝ) : ℂ) with hε
  set ζ : ℂ := exp (2 * Real.pi * I / n)
  have hζprim : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  have hεnorm : ‖ε‖ = δ / 2 := by rw [hε, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hε0 : ε ≠ 0 := fun h => by rw [h, norm_zero] at hεnorm; linarith
  obtain ⟨z1, ⟨hz1U, hz1g⟩, hz1⟩ := hδsub (show ε ∈ ball (0 : ℂ) δ by rw [mem_ball_zero_iff, hεnorm]; linarith)
  obtain ⟨z2, ⟨hz2U, hz2g⟩, hz2⟩ := hδsub (show ε * ζ ∈ ball (0 : ℂ) δ by
    rw [mem_ball_zero_iff, norm_mul, hεnorm, hζprim.norm'_eq_one hn0]; linarith)
  have hgz : g z1 = g z2 := by rw [hz1g, hz2g, hz1, hz2, mul_pow, hζprim.pow_eq_one, mul_one]
  rw [hinj hz1U hz2U (by simpa [hg] using hgz), hz2] at hz1
  have : ε * (ζ - 1) = 0 := by linear_combination hz1
  exact (mul_eq_zero.1 this).elim hε0 fun h => hζprim.ne_one (by omega) (sub_eq_zero.1 h)

private def mob (a z : ℂ) : ℂ := (z - a) / (1 - (starRingEnd ℂ) a * z)

private lemma mob_denom_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 - (starRingEnd ℂ) a * z ≠ 0 := fun h => by
  have h1 : (starRingEnd ℂ) a * z = 1 := by linear_combination -h
  have : ‖(starRingEnd ℂ) a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]; nlinarith [mul_le_mul_of_nonneg_left hz.le (norm_nonneg a)]
  rw [h1] at this; simp at this

private lemma norm_mob_lt_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : ‖mob a z‖ < 1 := by
  have hd := mob_denom_ne_zero ha hz
  unfold mob
  rw [norm_div, div_lt_one (norm_pos_iff.2 hd)]
  have hid : normSq (1 - (starRingEnd ℂ) a * z) - normSq (z - a) = (1 - normSq a) * (1 - normSq z) := by
    simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, conj_re, conj_im, one_re, one_im]; ring
  have ha2 : normSq a < 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hz2 : normSq z < 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have : normSq (z - a) < normSq (1 - (starRingEnd ℂ) a * z) := by
    nlinarith [mul_pos (sub_pos.2 ha2) (sub_pos.2 hz2)]
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at this
  nlinarith [norm_nonneg (z - a), norm_nonneg (1 - (starRingEnd ℂ) a * z)]

@[simp] private lemma mob_self (a : ℂ) : mob a a = 0 := by simp [mob]
@[simp] private lemma mob_zero (a : ℂ) : mob a 0 = -a := by simp [mob]

private lemma mob_neg_mob {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : mob (-a) (mob a z) = z := by
  have hd := mob_denom_ne_zero ha hz
  have hna := mob_denom_ne_zero ha ha
  unfold mob; rw [map_neg]
  have h2 : 1 - -(starRingEnd ℂ) a * ((z - a) / (1 - (starRingEnd ℂ) a * z)) =
      (1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z) := by field_simp; ring
  rw [h2, div_eq_iff (div_ne_zero hna hd)]
  generalize (starRingEnd ℂ) a = c at *
  rw [div_sub' hd, mul_div_assoc', div_left_inj' hd]; ring

private lemma mob_injOn {a : ℂ} (ha : ‖a‖ < 1) : Set.InjOn (mob a) (ball 0 1) := fun z hz w hw h => by
  rw [mem_ball_zero_iff] at hz hw
  rw [← mob_neg_mob ha hz, ← mob_neg_mob ha hw, h]

private lemma hasDerivAt_mob {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    HasDerivAt (mob a) ((1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z) ^ 2) z := by
  have hd := mob_denom_ne_zero ha hz
  have h2 : HasDerivAt (fun w => 1 - (starRingEnd ℂ) a * w) (-(starRingEnd ℂ) a) z := by
    simpa using ((hasDerivAt_id z).const_mul ((starRingEnd ℂ) a)).const_sub 1
  have := ((hasDerivAt_id z).sub_const a).div h2 hd
  simp only [Pi.div_def] at this
  convert this using 1; · rfl
  simp only [id_eq]; field_simp; ring

private lemma mob_eq_zero_iff {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : mob a z = 0 ↔ z = a :=
  ⟨fun h => by
    unfold mob at h
    exact (div_eq_zero_iff.mp h).elim sub_eq_zero.1 fun h0 => absurd h0 (mob_denom_ne_zero ha hz),
   by rintro rfl; simp⟩

private lemma hasDerivAt_of_sq_eq {g f : ℂ → ℂ} {z : ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 z)
    (hg : ContinuousAt g z) (hsq : ∀ w ∈ U, g w ^ 2 = f w) (hf : DifferentiableAt ℂ f z)
    (hgz : g z ≠ 0) : HasDerivAt g (deriv f z / (2 * g z)) z := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hsum : Tendsto (fun w => g w + g z) (𝓝[≠] z) (𝓝 (2 * g z)) := by
    rw [two_mul]; exact (hg.add tendsto_const_nhds).mono_left nhdsWithin_le_nhds
  have h2 : 2 * g z ≠ 0 := mul_ne_zero two_ne_zero hgz
  refine (hf.hasDerivAt.tendsto_slope.div hsum h2).congr' ?_
  filter_upwards [hsum.eventually_ne h2, nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with w hw1 hw2 hw3
  rw [Pi.div_apply, slope_def_field, slope_def_field, ← hsq w hw2, ← hsq z (mem_of_mem_nhds hU)]
  have hwz : w - z ≠ 0 := sub_ne_zero.2 hw3
  field_simp; ring

open Classical in
private theorem exists_sqrt_of_simplyConnected {Ω : Set ℂ} (hΩ : IsOpen Ω) [SimplyConnectedSpace Ω]
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) (hf0 : ∀ z ∈ Ω, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ Ω, g z ^ 2 = f z := by
  haveI := hΩ.locPathConnectedSpace
  obtain ⟨z0⟩ : Nonempty Ω := inferInstance
  have hp := isCoveringMap_npow (𝕜 := ℂ) 2 (by norm_num)
  let F : C(Ω, {x : ℂ // x ≠ 0}) := ⟨fun z => ⟨f z, hf0 z z.2⟩, hf.continuousOn.restrict.subtype_mk _⟩
  obtain ⟨e0, he0⟩ : ∃ e : ℂ, e ^ 2 = f z0 := IsAlgClosed.exists_pow_nat_eq _ two_pos
  have he0' : e0 ≠ 0 := by rintro rfl; exact hf0 z0 z0.2 (by simpa using he0.symm)
  obtain ⟨G, ⟨-, hGp⟩, -⟩ := hp.existsUnique_continuousMap_lifts F z0 ⟨e0, he0'⟩ (Subtype.ext he0)
  set g : ℂ → ℂ := fun z => if h : z ∈ Ω then ((G ⟨z, h⟩ : {x : ℂ // x ≠ 0}) : ℂ) else 0 with hg_def
  have hsq (z : ℂ) (hz : z ∈ Ω) : g z ^ 2 = f z := by
    simp only [hg_def, hz, dite_true]
    exact congrArg Subtype.val (congrFun hGp ⟨z, hz⟩)
  have hcont : ContinuousOn g Ω := by
    rw [continuousOn_iff_continuous_domRestrict,
      show Ω.domRestrict g = fun z : Ω => ((G z : {x : ℂ // x ≠ 0}) : ℂ) from
        funext fun z => by simp [Set.domRestrict_apply, hg_def, z.2]]
    exact continuous_subtype_val.comp G.continuous
  refine ⟨g, fun z hz => ?_, hsq⟩
  have hU : Ω ∈ 𝓝 z := hΩ.mem_nhds hz
  exact (hasDerivAt_of_sq_eq hU (hcont.continuousAt hU) hsq (hf.differentiableAt hU)
    (by simp only [hg_def, hz, dite_true]; exact (G ⟨z, hz⟩).2)).differentiableAt.differentiableWithinAt

private lemma equicontinuousAt_of_norm_le_one {ι : Type*} {F : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hb : ∀ i, ∀ z ∈ U, ‖F i z‖ ≤ 1) {z : ℂ}
    (hz : z ∈ U) : EquicontinuousAt F z := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z hz
  set r := ε / 3 with hr
  have hr0 : 0 < r := by positivity
  have hsub (y : ℂ) (hy : y ∈ ball z r) : closedBall y r ⊆ U := fun w hw => hεU <| by
    rw [mem_ball] at hy ⊢; rw [mem_closedBall] at hw
    linarith [dist_triangle w y z, show r + r < ε by rw [hr]; linarith]
  have hderiv (i : ι) (y : ℂ) (hy : y ∈ ball z r) : ‖deriv (F i) y‖ ≤ 1 / r :=
    norm_deriv_le_of_forall_mem_sphere_norm_le hr0
      (by apply DifferentiableOn.diffContOnCl; rw [closure_ball y hr0.ne']; exact (hF i).mono (hsub y hy))
      fun w hw => hb i w (hsub y hy (sphere_subset_closedBall hw))
  have hlip (i : ι) (y : ℂ) (hy : y ∈ ball z r) : ‖F i y - F i z‖ ≤ 1 / r * ‖y - z‖ :=
    (convex_ball z r).norm_image_sub_le_of_norm_deriv_le
      (fun y hy => (hF i).differentiableAt (hU.mem_nhds (hsub y hy (mem_closedBall_self hr0.le))))
      (hderiv i) (mem_ball_self hr0) hy
  refine Metric.equicontinuousAt_iff.2 fun e he => ⟨min r (e * r / 2), by positivity, fun y hy i => ?_⟩
  have hy1 : y ∈ ball z r := mem_ball.2 (hy.trans_le (min_le_left _ _))
  have hy2 : dist y z < e * r / 2 := hy.trans_le (min_le_right _ _)
  rw [dist_comm, dist_eq_norm]
  calc ‖F i y - F i z‖ ≤ 1 / r * ‖y - z‖ := hlip i y hy1
    _ ≤ 1 / r * (e * r / 2) := by gcongr; rw [← dist_eq_norm]; exact hy2.le
    _ = e / 2 := by field_simp
    _ < e := by linarith

private theorem montel {ι : Type*} (l : Ultrafilter ι) {F : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hb : ∀ i, ∀ z ∈ U, ‖F i z‖ ≤ 1) :
    ∃ f : ℂ → ℂ, TendstoLocallyUniformlyOn F f (l : Filter ι) U := by
  have hpt (z : ℂ) : ∃ w, z ∈ U → Tendsto (fun i => F i z) (l : Filter ι) (𝓝 w) := by
    by_cases hz : z ∈ U
    · obtain ⟨w, -, hw⟩ := (isCompact_closedBall (0 : ℂ) 1).ultrafilter_le_nhds (l.map fun i => F i z)
        (by rw [Ultrafilter.coe_map]; exact tendsto_principal.2 (Eventually.of_forall fun i =>
            mem_closedBall_zero_iff.2 (hb i z hz)))
      exact ⟨w, fun _ => by rwa [Ultrafilter.coe_map] at hw⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose f hf using hpt
  refine ⟨f, (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).2 fun K hKU hK => ?_⟩
  have heq : ∀ K' ∈ ({K} : Set (Set ℂ)), EquicontinuousOn F K' := by
    rintro K' rfl x hx
    exact (equicontinuousAt_of_norm_le_one hU hF hb (hKU hx)).equicontinuousWithinAt _
  have key := (EquicontinuousOn.tendsto_uniformOnFun_iff_pi' (𝔖 := {K})
    (by simpa using hK) heq (l : Filter ι) f).2 (by
      rw [tendsto_pi_nhds]; rintro ⟨x, hx⟩; simp only [sUnion_singleton] at hx; exact hf x (hKU hx))
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at key
  exact key K rfl

private theorem hurwitz_ne_zero {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → ℂ → ℂ} {g : ℂ → ℂ}
    {a : ℂ} {r : ℝ} (hr : 0 < r) (hF : ∀ i, DifferentiableOn ℂ (F i) (closedBall a r))
    (hF0 : ∀ i, ∀ z ∈ closedBall a r, F i z ≠ 0)
    (hconv : TendstoUniformlyOn F g l (closedBall a r))
    (hg : ContinuousOn g (sphere a r)) (hg0 : ∀ z ∈ sphere a r, g z ≠ 0) : g a ≠ 0 := by
  obtain ⟨z1, hz1, hmin⟩ := (isCompact_sphere a r).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 hr.le) hg.norm
  set m := ‖g z1‖
  have hm0 : 0 < m := norm_pos_iff.2 (hg0 z1 hz1)
  obtain ⟨i, hi⟩ := ((Metric.tendstoUniformlyOn_iff.1 hconv) (m / 2) (by positivity)).exists
  have hbd (z : ℂ) (hz : z ∈ sphere a r) : ‖(F i z)⁻¹‖ ≤ 2 / m := by
    have h1 : m ≤ ‖g z‖ := hmin hz
    have h2 : ‖g z - F i z‖ < m / 2 := by rw [← dist_eq_norm]; exact hi z (sphere_subset_closedBall hz)
    have h3 : m / 2 ≤ ‖F i z‖ := by
      have := norm_sub_norm_le (g z) (g z - F i z); simp only [sub_sub_cancel] at this; linarith
    rw [norm_inv]; exact (inv_anti₀ (by positivity) h3).trans_eq (inv_div m 2)
  have hd : DiffContOnCl ℂ (fun z => (F i z)⁻¹) (ball a r) := by
    apply DifferentiableOn.diffContOnCl; rw [closure_ball a hr.ne']; exact (hF i).inv (hF0 i)
  have hFa : ‖(F i a)⁻¹‖ ≤ 2 / m :=
    norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd
      (by rw [frontier_ball a hr.ne']; exact hbd) (subset_closure (mem_ball_self hr))
  rw [norm_inv, inv_le_comm₀ (norm_pos_iff.2 (hF0 i a (mem_closedBall_self hr.le))) (by positivity),
    inv_div] at hFa
  have hga : ‖g a - F i a‖ < m / 2 := by rw [← dist_eq_norm]; exact hi a (mem_closedBall_self hr.le)
  intro h0; rw [h0, zero_sub, norm_neg] at hga; linarith

private theorem hurwitz_injOn {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hinj : ∀ i, InjOn (F i) U)
    (hconv : TendstoLocallyUniformlyOn F f l U) {z0 : ℂ} (hz0 : z0 ∈ U)
    (hd : deriv f z0 ≠ 0) : InjOn f U := by
  intro a ha b hb hab
  by_contra hne
  have hfd : DifferentiableOn ℂ f U := hconv.differentiableOn (Eventually.of_forall hF) hU
  set g : ℂ → ℂ := fun z => f z - f b with hg
  have hgan : AnalyticOnNhd ℂ g U := fun z hz => ((hfd.analyticOnNhd hU) z hz).sub analyticAt_const
  have hnz : ¬ ∀ᶠ z in 𝓝 a, g z = 0 := fun hev => by
    have hEq := hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc ha hev
    have hloc : f =ᶠ[𝓝 z0] fun _ => f b := by
      filter_upwards [hU.mem_nhds hz0] with z hz; exact sub_eq_zero.1 (hEq hz)
    apply hd; rw [hloc.deriv_eq]; simp
  have hev : ∀ᶠ z in 𝓝[≠] a, g z ≠ 0 :=
    ((hgan a ha).eventually_eq_zero_or_eventually_ne_zero).resolve_left hnz
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1
    (inter_mem (inter_mem hev (hU.mem_nhds ha)) (isOpen_compl_singleton.mem_nhds hne))
  set r := ε / 2 with hr
  have hr0 : 0 < r := by positivity
  have hcb : closedBall a r ⊆ ball a ε := closedBall_subset_ball (by rw [hr]; linarith)
  have hcbU : closedBall a r ⊆ U := fun z hz => (hεsub (hcb hz)).1.2
  have hunif : TendstoUniformlyOn F f l (closedBall a r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv _ hcbU (isCompact_closedBall a r)
  have key := hurwitz_ne_zero hr0 (F := fun i z => F i z - F i b) (g := g)
    (fun i => ((hF i).mono hcbU).sub_const _)
    (fun i z hz h => (hεsub (hcb hz)).2 (hinj i (hcbU hz) hb (sub_eq_zero.1 h)))
    (hunif.sub ((hconv.tendsto_at hb).tendstoUniformlyOn_const _))
    (((hfd.mono hcbU).continuousOn.sub continuousOn_const).mono sphere_subset_closedBall)
    fun z hz => (hεsub (hcb (sphere_subset_closedBall hz))).1.1 (by
      rintro rfl; rw [mem_sphere, dist_self] at hz; exact hr0.ne hz)
  exact key (by simp [hg, hab])

lemma isOpen_image_of_injOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) {s : Set ℂ} (hs : s ⊆ U)
    (hso : IsOpen s) : IsOpen (f '' s) := by
  rcases (hf.analyticOnNhd hU).is_constant_or_isOpen hUc with ⟨w, hw⟩ | h
  · rcases s.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
    · simp
    · exfalso
      obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z (hs hz)
      have hmem : z + (ε / 2 : ℝ) ∈ ball z ε := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]; linarith
      have h2 : ((ε / 2 : ℝ) : ℂ) = 0 := by
        linear_combination hinj (hεU hmem) (hs hz) ((hw _ (hεU hmem)).trans (hw z (hs hz)).symm)
      linarith [show ε / 2 = 0 by exact_mod_cast h2]
  · exact h s hs hso

lemma exists_holomorphic_inverse {D : Set ℂ} (hD : IsOpen D) (hDc : IsPreconnected D)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) (hinj : InjOn f D) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (f '' D) ∧ MapsTo g (f '' D) D ∧
      (∀ z ∈ D, g (f z) = z) ∧ ∀ w ∈ f '' D, f (g w) = w := by
  classical
  set g := Function.invFunOn f D
  have hgmem (w : ℂ) (hw : w ∈ f '' D) : g w ∈ D ∧ f (g w) = w := Function.invFunOn_pos hw
  have hgf (z : ℂ) (hz : z ∈ D) : g (f z) = z :=
    hinj (hgmem _ (mem_image_of_mem f hz)).1 hz (hgmem _ (mem_image_of_mem f hz)).2
  have hopen : IsOpen (f '' D) := isOpen_image_of_injOn hD hDc hf hinj subset_rfl hD
  refine ⟨g, fun w hw => ?_, fun w hw => (hgmem w hw).1, hgf, fun w hw => (hgmem w hw).2⟩
  obtain ⟨hgw, hfgw⟩ := hgmem w hw
  have hcont : ContinuousAt g w := by
    rw [ContinuousAt, (nhds_basis_opens (g w)).tendsto_right_iff]
    rintro V ⟨hV, hVo⟩
    filter_upwards [(isOpen_image_of_injOn hD hDc hf hinj inter_subset_right (hVo.inter hD)).mem_nhds
      ⟨g w, ⟨hV, hgw⟩, hfgw⟩] with y hy
    obtain ⟨z, ⟨hzV, hzD⟩, rfl⟩ := hy
    rwa [hgf z hzD]
  exact (((hf.differentiableAt (hD.mem_nhds hgw)).hasDerivAt).of_local_left_inverse hcont
    (deriv_ne_zero_of_injOn hD hf hinj hgw)
    (by filter_upwards [hopen.mem_nhds hw] with y hy using (hgmem y hy).2)).differentiableAt.differentiableWithinAt

private def Admissible (Ω : Set ℂ) (z₀ : ℂ) (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f Ω ∧ InjOn f Ω ∧ MapsTo f Ω (ball 0 1) ∧ f z₀ = 0

private lemma exists_admissible {Ω : Set ℂ} (hΩ : IsOpen Ω) [SimplyConnectedSpace Ω]
    (hne : Ω ≠ univ) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) : ∃ f, Admissible Ω z₀ f := by
  have hUc : IsPreconnected Ω := isPreconnected_iff_preconnectedSpace.2 inferInstance
  obtain ⟨a, ha⟩ : ∃ a, a ∉ Ω := by by_contra h; push_neg at h; exact hne (eq_univ_of_forall h)
  have hza (z : ℂ) (hz : z ∈ Ω) : z - a ≠ 0 := fun h => ha (sub_eq_zero.1 h ▸ hz)
  obtain ⟨g, hgd, hgsq⟩ := exists_sqrt_of_simplyConnected hΩ
    (f := fun z => z - a) (differentiableOn_id.sub_const a) hza
  have hginj : InjOn g Ω := fun z hz w hw h => by
    have := hgsq z hz; rw [h, hgsq w hw] at this; linear_combination -this
  have hgneg (z : ℂ) (hz : z ∈ Ω) (w : ℂ) (hw : w ∈ Ω) : g z ≠ -g w := fun h => by
    have h1 := hgsq z hz; rw [h, neg_sq, hgsq w hw] at h1
    have hzw : w = z := by linear_combination h1
    subst hzw
    have : g w = 0 := by linear_combination h / 2
    exact hza w hw (by rw [← hgsq w hw, this]; ring)
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1
    (isOpen_image_of_injOn hΩ hUc hgd hginj subset_rfl hΩ) (g z₀) ⟨z₀, hz₀, rfl⟩
  have hfar (z : ℂ) (hz : z ∈ Ω) : ρ ≤ ‖g z + g z₀‖ := by
    by_contra hlt; push_neg at hlt
    obtain ⟨w, hw, hgw⟩ := hρsub (show -g z ∈ ball (g z₀) ρ by
      rw [mem_ball, dist_eq_norm, ← norm_neg]; convert hlt using 2; ring)
    exact hgneg w hw z hz hgw
  have hne0 (z : ℂ) (hz : z ∈ Ω) : g z + g z₀ ≠ 0 := fun h => by
    have := hfar z hz; rw [h, norm_zero] at this; linarith
  have hinvle (z : ℂ) (hz : z ∈ Ω) : ‖(g z + g z₀)⁻¹‖ ≤ 1 / ρ := by
    rw [norm_inv, one_div]; exact inv_anti₀ hρ (hfar z hz)
  refine ⟨fun z => ((ρ / 4 : ℝ) : ℂ) * ((g z + g z₀)⁻¹ - (g z₀ + g z₀)⁻¹),
    fun z hz => ((((hgd z hz).add_const _).inv (hne0 z hz)).sub_const _).const_mul _,
    fun z hz w hw h => ?_, fun z hz => ?_, by simp⟩
  · have hρ4 : ((ρ / 4 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : ρ / 4 ≠ 0)
    have h2 : (g z + g z₀)⁻¹ = (g w + g z₀)⁻¹ := by linear_combination mul_left_cancel₀ hρ4 h
    rw [inv_inj] at h2; exact hginj hz hw (by linear_combination h2)
  · rw [mem_ball_zero_iff, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc ρ / 4 * ‖(g z + g z₀)⁻¹ - (g z₀ + g z₀)⁻¹‖
        ≤ ρ / 4 * (‖(g z + g z₀)⁻¹‖ + ‖(g z₀ + g z₀)⁻¹‖) := by gcongr; exact norm_sub_le _ _
      _ ≤ ρ / 4 * (1 / ρ + 1 / ρ) := by gcongr; exacts [hinvle z hz, hinvle z₀ hz₀]
      _ = 1 / 2 := by field_simp; ring
      _ < 1 := by norm_num

private lemma exists_extremal {Ω : Set ℂ} (hΩ : IsOpen Ω) [SimplyConnectedSpace Ω]
    (hne : Ω ≠ univ) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ f, Admissible Ω z₀ f ∧ ∀ g, Admissible Ω z₀ g → ‖deriv g z₀‖ ≤ ‖deriv f z₀‖ := by
  have hUc : IsPreconnected Ω := isPreconnected_iff_preconnectedSpace.2 inferInstance
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 hΩ z₀ hz₀
  have hr : 0 < ε / 2 := by positivity
  have hrsub : closedBall z₀ (ε / 2) ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hεsub
  set S : Set ℝ := {t | ∃ g, Admissible Ω z₀ g ∧ ‖deriv g z₀‖ = t}
  obtain ⟨f₁, hf₁⟩ := exists_admissible hΩ hne hz₀
  have hSne : S.Nonempty := ⟨_, f₁, hf₁, rfl⟩
  have hSbdd : BddAbove S := ⟨1 / (ε / 2), by
    rintro t ⟨g, hg, rfl⟩
    refine norm_deriv_le_of_forall_mem_sphere_norm_le hr ?_
      fun w hw => (mem_ball_zero_iff.1 (hg.2.2.1 (hrsub (sphere_subset_closedBall hw)))).le
    apply DifferentiableOn.diffContOnCl; rw [closure_ball z₀ hr.ne']; exact hg.1.mono hrsub⟩
  have hMpos : 0 < sSup S := lt_of_lt_of_le
    (norm_pos_iff.2 (deriv_ne_zero_of_injOn hΩ hf₁.1 hf₁.2.1 hz₀)) (le_csSup hSbdd ⟨f₁, hf₁, rfl⟩)
  obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sSup hSne hSbdd
  choose F hF hFu using huS
  set l : Ultrafilter ℕ := Ultrafilter.of atTop
  obtain ⟨f, hconv⟩ := montel l hΩ (fun n => (hF n).1)
    fun n z hz => (mem_ball_zero_iff.1 ((hF n).2.2.1 hz)).le
  have hfd : DifferentiableOn ℂ f Ω := hconv.differentiableOn (Eventually.of_forall fun n => (hF n).1) hΩ
  have hnorm : ‖deriv f z₀‖ = sSup S := tendsto_nhds_unique
    ((hconv.deriv (Eventually.of_forall fun n => (hF n).1) hΩ).tendsto_at hz₀).norm
    ((hu.mono_left (Ultrafilter.of_le _)).congr' (Eventually.of_forall fun n => (hFu n).symm))
  have hd0 : deriv f z₀ ≠ 0 := fun h => by rw [h, norm_zero] at hnorm; linarith
  have hfinj : InjOn f Ω := hurwitz_injOn hΩ hUc (fun n => (hF n).1) (fun n => (hF n).2.1) hconv hz₀ hd0
  have hfz₀ : f z₀ = 0 := tendsto_nhds_unique (hconv.tendsto_at hz₀)
    (tendsto_const_nhds.congr' (Eventually.of_forall fun n => ((hF n).2.2.2).symm))
  have hmaps : MapsTo f Ω (ball 0 1) := by
    have hsub : f '' Ω ⊆ closedBall 0 1 := by
      rintro _ ⟨z, hz, rfl⟩
      exact mem_closedBall_zero_iff.2 (le_of_tendsto' (hconv.tendsto_at hz).norm
        fun n => (mem_ball_zero_iff.1 ((hF n).2.2.1 hz)).le)
    have := (isOpen_image_of_injOn hΩ hUc hfd hfinj subset_rfl hΩ).subset_interior_iff.2 hsub
    rw [interior_closedBall (0 : ℂ) one_ne_zero] at this
    exact fun z hz => this ⟨z, hz, rfl⟩
  exact ⟨f, ⟨hfd, hfinj, hmaps, hfz₀⟩, fun g hg => hnorm ▸ le_csSup hSbdd ⟨g, hg, rfl⟩⟩

private lemma hasDerivAt_psi {c : ℂ} (hc : ‖c‖ < 1) :
    HasDerivAt (fun ζ => mob (-(-c ^ 2)) (mob (-c) ζ ^ 2))
      (2 * c / (1 + (starRingEnd ℂ) c * c)) 0 := by
  have hc' : ‖-c‖ < 1 := by rwa [norm_neg]
  have hw : ‖-(-c ^ 2)‖ < 1 := by rw [neg_neg, norm_pow]; nlinarith [norm_nonneg c]
  have h1 := hasDerivAt_mob hc' (z := 0) (by simp)
  have h2 : HasDerivAt (fun ζ => ζ ^ 2) (2 * mob (-c) 0) (mob (-c) 0) := by
    simpa using hasDerivAt_pow 2 (mob (-c) 0)
  have h3 := hasDerivAt_mob hw (z := mob (-c) 0 ^ 2) (by simpa [neg_neg] using hw)
  have := h3.comp (0 : ℂ) (h2.comp (0 : ℂ) h1)
  simp only [Function.comp_def] at this
  convert this using 1
  simp only [mob_zero, neg_neg, map_neg, map_pow, mul_zero, sub_zero]
  have hden : 1 + (starRingEnd ℂ) c * c ≠ 0 := by
    rw [conj_mul']; intro h
    have : (1 + ‖c‖ ^ 2 : ℝ) = 0 := by exact_mod_cast (show ((1 + ‖c‖ ^ 2 : ℝ) : ℂ) = 0 by push_cast; exact h)
    nlinarith [sq_nonneg ‖c‖]
  have hden2 : 1 - (starRingEnd ℂ) c * c ≠ 0 := mob_denom_ne_zero hc hc
  have hden4 : 1 - -(starRingEnd ℂ) c ^ 2 * -c ^ 2 ≠ 0 := by
    rw [show 1 - -(starRingEnd ℂ) c ^ 2 * -c ^ 2 =
      (1 - (starRingEnd ℂ) c * c) * (1 + (starRingEnd ℂ) c * c) by ring]
    exact mul_ne_zero hden2 hden
  generalize (starRingEnd ℂ) c = d at *
  have hden' : 1 + c * d ≠ 0 := by rwa [mul_comm]
  have hden3 : 1 - c ^ 2 * d ^ 2 ≠ 0 := by
    rw [show 1 - c ^ 2 * d ^ 2 = (1 - d * c) * (1 + d * c) by ring]; exact mul_ne_zero hden2 hden
  field_simp [hden, hden2, hden', hden3]; ring

private lemma surjOn_of_extremal {Ω : Set ℂ} (hΩ : IsOpen Ω) [SimplyConnectedSpace Ω] {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) {f : ℂ → ℂ} (hf : Admissible Ω z₀ f)
    (hmax : ∀ g, Admissible Ω z₀ g → ‖deriv g z₀‖ ≤ ‖deriv f z₀‖) :
    SurjOn f Ω (ball 0 1) := by
  intro w hw
  by_contra hnot
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
  obtain ⟨hfd, hfinj, hfmaps, hfz₀⟩ := hf
  have hfn (z : ℂ) (hz : z ∈ Ω) : ‖f z‖ < 1 := mem_ball_zero_iff.1 (hfmaps hz)
  set h : ℂ → ℂ := fun z => mob w (f z) with hh
  have hhd : DifferentiableOn ℂ h Ω := fun z hz =>
    (hasDerivAt_mob hw1 (hfn z hz)).differentiableAt.comp_differentiableWithinAt z (hfd z hz)
  have hh0 (z : ℂ) (hz : z ∈ Ω) : h z ≠ 0 := fun h0 =>
    hnot ⟨z, hz, (mob_eq_zero_iff hw1 (hfn z hz)).1 h0⟩
  obtain ⟨s, hsd, hssq⟩ := exists_sqrt_of_simplyConnected hΩ hhd hh0
  have hsn (z : ℂ) (hz : z ∈ Ω) : ‖s z‖ < 1 := by
    have h1 : ‖s z‖ ^ 2 < 1 := by rw [← norm_pow, hssq z hz]; exact norm_mob_lt_one hw1 (hfn z hz)
    nlinarith [norm_nonneg (s z)]
  have hsinj : InjOn s Ω := fun z hz z' hz' hzz =>
    hfinj hz hz' (mob_injOn hw1 (mem_ball_zero_iff.2 (hfn z hz)) (mem_ball_zero_iff.2 (hfn z' hz'))
      (by change h z = h z'; rw [← hssq z hz, ← hssq z' hz', hzz]))
  set c := s z₀ with hc
  have hcn : ‖c‖ < 1 := hsn z₀ hz₀
  have hwc : w = -c ^ 2 := by
    have hc2 : c ^ 2 = -w := by rw [hc, hssq z₀ hz₀, hh]; simp [hfz₀]
    rw [hc2, neg_neg]
  set F : ℂ → ℂ := fun z => mob c (s z) with hF
  have hFadm : Admissible Ω z₀ F :=
    ⟨fun z hz => (hasDerivAt_mob hcn (hsn z hz)).differentiableAt.comp_differentiableWithinAt z (hsd z hz),
     fun z hz z' hz' hzz => hsinj hz hz'
       (mob_injOn hcn (mem_ball_zero_iff.2 (hsn z hz)) (mem_ball_zero_iff.2 (hsn z' hz')) hzz),
     fun z hz => mem_ball_zero_iff.2 (norm_mob_lt_one hcn (hsn z hz)),
     by simp [hF, hc]⟩
  set Ψ : ℂ → ℂ := fun ζ => mob (-(-c ^ 2)) (mob (-c) ζ ^ 2) with hΨ
  have hfeq : f =ᶠ[𝓝 z₀] Ψ ∘ F := by
    filter_upwards [hΩ.mem_nhds hz₀] with z hz
    simp only [Function.comp_apply, hΨ, hF]
    rw [mob_neg_mob hcn (hsn z hz), hssq z hz, hh, ← hwc, mob_neg_mob hw1 (hfn z hz)]
  have hFd : HasDerivAt F (deriv F z₀) z₀ := (hFadm.1.differentiableAt (hΩ.mem_nhds hz₀)).hasDerivAt
  have hΨd := hasDerivAt_psi hcn
  rw [← hFadm.2.2.2] at hΨd
  have hdf : deriv f z₀ = 2 * c / (1 + (starRingEnd ℂ) c * c) * deriv F z₀ := by
    rw [hfeq.deriv_eq, (hΨd.comp z₀ hFd).deriv]
  have hfd0 : deriv f z₀ ≠ 0 := deriv_ne_zero_of_injOn hΩ hfd hfinj hz₀
  have hFd0 : deriv F z₀ ≠ 0 := fun h0 => hfd0 (by rw [hdf, h0, mul_zero])
  have hpsi_lt : ‖2 * c / (1 + (starRingEnd ℂ) c * c)‖ < 1 := by
    rw [conj_mul', show (1 + (‖c‖ : ℂ) ^ 2) = ((1 + ‖c‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
      norm_div, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
      div_lt_one (by positivity), norm_ofNat]
    nlinarith [sq_nonneg (1 - ‖c‖), norm_nonneg c]
  have hlt : ‖deriv f z₀‖ < ‖deriv F z₀‖ := by
    rw [hdf, norm_mul]; nlinarith [norm_pos_iff.2 hFd0]
  linarith [hmax F hFadm]

theorem riemann_mapping_theorem (Ω : Set ℂ) (hopen : IsOpen Ω) [SimplyConnectedSpace Ω]
    (hne : Ω ≠ univ) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball 0 1) ∧ InjOn G (ball 0 1) ∧ G '' ball 0 1 = Ω := by
  have hUc : IsPreconnected Ω := isPreconnected_iff_preconnectedSpace.2 inferInstance
  obtain ⟨⟨z₀, hz₀⟩⟩ : Nonempty Ω := inferInstance
  obtain ⟨f, hf, hmax⟩ := exists_extremal hopen hne hz₀
  have him : f '' Ω = ball 0 1 := Subset.antisymm hf.2.2.1.image_subset (surjOn_of_extremal hopen hz₀ hf hmax)
  obtain ⟨G, hGd, hGm, hGf, hfG⟩ := exists_holomorphic_inverse hopen hUc hf.1 hf.2.1
  rw [him] at hGd hGm hfG
  exact ⟨G, hGd, fun w hw w' hw' h => by rw [← hfG w hw, ← hfG w' hw', h],
    Subset.antisymm hGm.image_subset fun z hz => ⟨f z, hf.2.2.1 hz, hGf z hz⟩⟩

end

end PolyaNeumann.RiemannInterior

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ENNReal

theorem exists_interior_conformal_map (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hsc : SimplyConnectedSpace Ω) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball 0 1) ∧
      Set.InjOn F (Metric.ball 0 1) ∧ F '' Metric.ball 0 1 = Ω := by
  letI : SimplyConnectedSpace Ω := hsc
  exact RiemannInterior.riemann_mapping_theorem Ω hopen fun h =>
    NormedSpace.unbounded_univ ℝ ℂ (h ▸ hb)

/-! ### Finite-energy circular caps, boundary crosscut & arclength reparametrization -/

def riemannInteriorDerivative (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (ball (0 : ℂ) 1).indicator (deriv F) z

private theorem riemannInteriorDerivative_sq_integrable (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1)) :
    Integrable (fun z => ‖riemannInteriorDerivative F z‖ ^ 2) := by
  have h0 : IntegrableOn (fun z => ‖deriv F z‖ ^ 2) (ball (0 : ℂ) 1) := by
    have hconst : IntegrableOn (fun _ : ℂ => (1 : ℝ)) (F '' ball (0 : ℂ) 1) volume :=
      integrableOn_const hb.measure_lt_top.ne
    simpa only [mul_one] using localConformal_integrable_weight isOpen_ball hF hinj hconst
  refine (h0.integrable_indicator measurableSet_ball).congr (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ ball (0 : ℂ) 1
  · simp only [riemannInteriorDerivative, indicator_of_mem hz]
  · simp only [riemannInteriorDerivative, indicator_of_notMem hz, norm_zero, zero_pow two_ne_zero]

def riemannCapDerivative (F : ℂ → ℂ) (c : ℂ) (r θ : ℝ) : ℂ :=
  riemannInteriorDerivative F (circleMap c r θ) * (circleMap 0 r θ * Complex.I)

private theorem riemannCapDerivative_measurable (F : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    Measurable (riemannCapDerivative F c r) :=
  (((measurable_deriv F).indicator measurableSet_ball).comp (continuous_circleMap c r).measurable).mul
    ((continuous_circleMap 0 r).measurable.mul_const Complex.I)

private theorem norm_riemannCapDerivative (F : ℂ → ℂ) (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    ‖riemannCapDerivative F c r θ‖ = r * ‖riemannInteriorDerivative F (circleMap c r θ)‖ := by
  simp only [riemannCapDerivative, norm_mul, norm_circleMap_zero, abs_of_nonneg hr,
    Complex.norm_I, mul_one, mul_comm]

theorem riemannCapDerivative_hasDerivAt (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (c : ℂ) (r θ : ℝ) (hθ : circleMap c r θ ∈ ball (0 : ℂ) 1) :
    HasDerivAt (fun t => F (circleMap c r t)) (riemannCapDerivative F c r θ) θ := by
  simpa only [riemannCapDerivative, riemannInteriorDerivative, indicator_of_mem hθ, Function.comp_def]
    using ((hF.differentiableAt (isOpen_ball.mem_nhds hθ)).hasDerivAt).comp θ (hasDerivAt_circleMap c r θ)

theorem riemannCapDerivative_continuousAt_interior (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (c : ℂ) (r θ : ℝ)
    (hθ : circleMap c r θ ∈ ball (0 : ℂ) 1) :
    ContinuousAt (riemannCapDerivative F c r) θ := by
  refine ((((hF.deriv isOpen_ball).continuousOn.continuousAt (isOpen_ball.mem_nhds hθ)).comp
    (continuous_circleMap c r).continuousAt).mul
    ((continuous_circleMap 0 r).continuousAt.mul_const Complex.I)).congr ?_
  filter_upwards [(continuous_circleMap c r).continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hθ)] with t ht
  have htDisk : circleMap c r t ∈ ball (0 : ℂ) 1 := ht
  simp only [Pi.mul_apply, Function.comp_apply, riemannCapDerivative, riemannInteriorDerivative, indicator_of_mem htDisk]

theorem riemannCapDerivative_ne_zero_interior (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (c : ℂ) {r : ℝ} (hr : 0 < r) (θ : ℝ)
    (hθ : circleMap c r θ ∈ ball (0 : ℂ) 1) :
    riemannCapDerivative F c r θ ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_riemannCapDerivative F c hr.le θ]
  simp only [riemannInteriorDerivative, indicator_of_mem hθ]
  exact mul_pos hr (norm_pos_iff.mpr (RiemannInterior.deriv_ne_zero_of_injOn isOpen_ball hF hinj hθ))

private theorem riemannMapping_exists_small_cap_length (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (c : ℂ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ r ∈ Ioo (0 : ℝ) δ,
      IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi) ∧
      (∫ θ in Ioo (-Real.pi) Real.pi, ‖riemannCapDerivative F c r θ‖) < ε := by
  let g : ℂ → ℝ := fun z => ‖riemannInteriorDerivative F z‖ ^ 2
  have hg := riemannInteriorDerivative_sq_integrable F hF hinj hb
  have hgp : IntegrableOn (fun p : ℝ × ℝ => p.1 * g (c + Complex.polarCoord.symm p))
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) := by
    have hm : Measurable (fun p : ℝ × ℝ => p.1 * g (c + Complex.polarCoord.symm p)) :=
      measurable_fst.mul ((((measurable_deriv F).indicator measurableSet_ball).norm.pow_const 2).comp
        (measurable_const.add measurable_complexPolarCoord_symm))
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have heq : (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        ‖p.1 * g (c + Complex.polarCoord.symm p)‖ₑ) = ∫⁻ z : ℂ, ‖g (c + z)‖ₑ := by
      rw [← Complex.lintegral_comp_polarCoord_symm]
      refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
      change ‖p.1 * g (c + Complex.polarCoord.symm p)‖ₑ = ENNReal.ofReal p.1 • ‖g (c + Complex.polarCoord.symm p)‖ₑ
      rw [enorm_mul, Real.enorm_eq_ofReal hp.1.le]; rfl
    rw [heq]; exact (hg.comp_add_left c).hasFiniteIntegral
  have heq_cm (p : ℝ × ℝ) : c + Complex.polarCoord.symm p = circleMap c p.1 p.2 := by
    rw [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [heq_cm] at hgp
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hgp
  let R : ℝ → ℝ := fun r => ∫ θ in Ioo (-Real.pi) Real.pi, r * g (circleMap c r θ)
  have hR : IntegrableOn R (Ioi (0 : ℝ)) := hgp.integral_prod_left
  have hslice : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      IntegrableOn (fun θ => g (circleMap c r θ)) (Ioo (-Real.pi) Real.pi) := by
    filter_upwards [hgp.prod_right_ae, ae_restrict_mem measurableSet_Ioi] with r hr (hr0 : 0 < r)
    simpa only [IntegrableOn, ← mul_assoc, inv_mul_cancel₀ hr0.ne', one_mul] using hr.const_mul r⁻¹
  let a : ℝ := ε / (4 * Real.pi)
  have ha : 0 < a := div_pos hε (by positivity)
  have hrad : ∃ r ∈ Ioo (0 : ℝ) δ,
      IntegrableOn (fun θ => g (circleMap c r θ)) (Ioo (-Real.pi) Real.pi) ∧ r * R r < 2 * a * ε := by
    by_contra hn
    have hi : IntegrableOn (fun r : ℝ => (2 * a * ε) * r⁻¹) (Ioo 0 δ) := by
      refine (hR.mono_set Ioo_subset_Ioi_self).mono'
        (measurable_const.mul measurable_inv).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo,
        ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self hslice] with r hr hp
      have hge : 2 * a * ε ≤ r * R r := le_of_not_gt fun hh => hn ⟨r, hr, hp, hh⟩
      rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (inv_nonneg.mpr hr.1.le))]
      simpa only [div_eq_mul_inv] using (div_le_iff₀ hr.1).2 (by simpa only [mul_comm] using hge)
    have hp : IntegrableOn (fun r : ℝ => r ^ (-1 : ℝ)) (Ioo 0 δ) := by
      simpa only [Real.rpow_neg_one, IntegrableOn, ← mul_assoc,
        inv_mul_cancel₀ (show (2 * a * ε) ≠ 0 by positivity), one_mul] using hi.const_mul (2 * a * ε)⁻¹
    linarith [(intervalIntegral.integrableOn_Ioo_rpow_iff hδ).1 hp]
  obtain ⟨r, hr, hs, hsmall⟩ := hrad
  have hsq : IntegrableOn (fun θ => ‖riemannCapDerivative F c r θ‖ ^ 2) (Ioo (-Real.pi) Real.pi) := by
    simpa only [IntegrableOn, norm_riemannCapDerivative F c hr.1.le, mul_pow, g] using hs.const_mul (r ^ 2)
  have hconst1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo (-Real.pi) Real.pi) :=
    integrableOn_const (by simp [Real.volume_Ioo])
  have hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi) :=
    (hconst1.add hsq).mono' (riemannCapDerivative_measurable F c r).aestronglyMeasurable
      (Eventually.of_forall fun θ => by dsimp; nlinarith [sq_nonneg (‖riemannCapDerivative F c r θ‖ - 1)])
  have hsqsmall : (∫ θ in Ioo (-Real.pi) Real.pi, ‖riemannCapDerivative F c r θ‖ ^ 2) < 2 * a * ε := by
    simpa only [R, integral_const_mul, ← mul_assoc, ← pow_two,
      norm_riemannCapDerivative F c hr.1.le, mul_pow, g] using hsmall
  have hconst : IntegrableOn (fun _ : ℝ => a) (Ioo (-Real.pi) Real.pi) :=
    integrableOn_const (by simp [Real.volume_Ioo])
  have hle := integral_mono hi.norm (hconst.add (hsq.div_const (4 * a))) fun θ => by
    dsimp only [Pi.add_apply]
    have h : (‖riemannCapDerivative F c r θ‖ - a) * (4 * a) ≤ ‖riemannCapDerivative F c r θ‖ ^ 2 := by
      nlinarith [sq_nonneg (‖riemannCapDerivative F c r θ‖ - 2 * a)]
    linarith [(le_div_iff₀ (show 0 < 4 * a by positivity)).2 h]
  change (∫ θ in Ioo (-Real.pi) Real.pi, ‖riemannCapDerivative F c r θ‖) ≤
    ∫ θ in Ioo (-Real.pi) Real.pi, a + ‖riemannCapDerivative F c r θ‖ ^ 2 / (4 * a) at hle
  rw [integral_add hconst (hsq.div_const (4 * a)), setIntegral_const,
    Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]), smul_eq_mul, integral_div] at hle
  have hdiv : (∫ θ in Ioo (-Real.pi) Real.pi, ‖riemannCapDerivative F c r θ‖ ^ 2) / (4 * a) < ε / 2 :=
    (div_lt_iff₀ (by positivity)).2 (by nlinarith [hsqsmall])
  have hhalf : (Real.pi - -Real.pi) * a = ε / 2 := by dsimp [a]; field_simp [Real.pi_pos.ne']; ring
  exact ⟨r, hr, hi, hle.trans_lt (by linarith)⟩

private theorem riemannCapDerivative_periodic (F : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    Function.Periodic (riemannCapDerivative F c r) (2 * Real.pi) := fun θ => by
  simp only [riemannCapDerivative, periodic_circleMap c r θ, periodic_circleMap 0 r θ]

private theorem riemannCapDerivative_intervalIntegrable (F : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi))
    (a b : ℝ) : IntervalIntegrable (riemannCapDerivative F c r) volume a b :=
  (riemannCapDerivative_periodic F c r).intervalIntegrable Real.two_pi_pos.ne'
    (by rw [show -Real.pi + 2 * Real.pi = Real.pi by ring,
          intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [Real.pi_pos])]; exact hi) a b

private theorem riemannMapping_cap_continuous_extension (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (c : ℂ) (r : ℝ)
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi))
    {a b : ℝ} (hab : a < b) (harc : MapsTo (circleMap c r) (Ioo a b) (ball (0 : ℂ) 1)) :
    ∃ G : ℝ → ℂ, Continuous G ∧ EqOn G (fun θ => F (circleMap c r θ)) (Ioo a b) ∧
      Tendsto (fun θ => F (circleMap c r θ)) (𝓝[Ioo a b] a) (𝓝 (G a)) ∧
      Tendsto (fun θ => F (circleMap c r θ)) (𝓝[Ioo a b] b) (𝓝 (G b)) := by
  let t : ℝ := (a + b) / 2
  have ht : t ∈ Ioo a b := ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩
  let V : ℝ → ℂ := riemannCapDerivative F c r
  have hVi := riemannCapDerivative_intervalIntegrable F c r hi
  let G : ℝ → ℂ := fun θ => F (circleMap c r t) + ∫ s in t..θ, V s
  have hGc : Continuous G := continuous_const.add (intervalIntegral.continuous_primitive hVi t)
  have hGd (θ : ℝ) (hθ : θ ∈ Ioo a b) : HasDerivAt G (V θ) θ := by
    simpa only [G, zero_add] using
      (intervalIntegral.integral_hasDerivAt_right (hVi t θ)
        (riemannCapDerivative_measurable F c r).aestronglyMeasurable.stronglyMeasurableAtFilter
        (riemannCapDerivative_continuousAt_interior F hF c r θ (harc hθ))).const_add (F (circleMap c r t))
  have heq : EqOn G (fun θ => F (circleMap c r θ)) (Ioo a b) :=
    isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo a b).isPreconnected
      (fun θ hθ => (hGd θ hθ).differentiableAt.differentiableWithinAt)
      (fun θ hθ => (riemannCapDerivative_hasDerivAt F hF c r θ (harc hθ)).differentiableAt.differentiableWithinAt)
      (fun θ hθ => by rw [(hGd θ hθ).deriv, (riemannCapDerivative_hasDerivAt F hF c r θ (harc hθ)).deriv])
      ht (by simp only [G, intervalIntegral.integral_same, add_zero])
  refine ⟨G, hGc, heq, ?_, ?_⟩
  · exact ((hGc.tendsto a).mono_left nhdsWithin_le_nhds).congr' (by filter_upwards [self_mem_nhdsWithin] with θ hθ using heq hθ)
  · exact ((hGc.tendsto b).mono_left nhdsWithin_le_nhds).congr' (by filter_upwards [self_mem_nhdsWithin] with θ hθ using heq hθ)

private theorem riemannMapping_cap_extension_subarc_displacement (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (c : ℂ) (r : ℝ)
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi))
    {a b : ℝ} (harc : MapsTo (circleMap c r) (Ioo a b) (ball (0 : ℂ) 1))
    {G : ℝ → ℂ} (hGc : Continuous G) (hGeq : EqOn G (fun θ => F (circleMap c r θ)) (Ioo a b))
    {θ τ : ℝ} (hθ : θ ∈ Icc a b) (hτ : τ ∈ Icc a b) (hθτ : θ ≤ τ) :
    ‖G τ - G θ‖ ≤ ∫ s in θ..τ, ‖riemannCapDerivative F c r s‖ := by
  have hsub : Ioo θ τ ⊆ Ioo a b := fun s hs => ⟨hθ.1.trans_lt hs.1, hs.2.trans_le hτ.2⟩
  have hGd (s : ℝ) (hs : s ∈ Ioo a b) : HasDerivAt G (riemannCapDerivative F c r s) s :=
    (riemannCapDerivative_hasDerivAt F hF c r s (harc hs)).congr_of_eventuallyEq
      (by filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu using hGeq hu)
  exact norm_sub_le_integral_of_norm_deriv_le_of_le hθτ hGc.continuousOn
    (fun s hs => (hGd s (hsub hs)).differentiableAt.differentiableWithinAt)
    (Eventually.of_forall fun s hs => by rw [(hGd s (hsub hs)).deriv])
    (riemannCapDerivative_intervalIntegrable F c r hi θ τ).norm

theorem riemannMapping_limit_mem_frontier {A : Type*} {l : Filter A} [NeBot l]
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (hinj : InjOn F (ball (0 : ℂ) 1))
    {z : A → ℂ} {ζ w : ℂ} (hζ : ‖ζ‖ = 1) (hzin : ∀ᶠ x in l, z x ∈ ball (0 : ℂ) 1)
    (hz : Tendsto z l (𝓝 ζ)) (hw : Tendsto (fun x => F (z x)) l (𝓝 w)) :
    w ∈ frontier (F '' ball (0 : ℂ) 1) := by
  have hopen := RiemannInterior.isOpen_image_of_injOn isOpen_ball
    (convex_ball (0 : ℂ) 1).isPreconnected hF hinj subset_rfl isOpen_ball
  rw [hopen.frontier_eq]
  refine ⟨mem_closure_of_tendsto hw (hzin.mono fun x hx => mem_image_of_mem F hx), fun hwin => ?_⟩
  obtain ⟨J, hJ, hJmap, hJF, _⟩ := RiemannInterior.exists_holomorphic_inverse
    isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected hF hinj
  have hJlim : Tendsto (fun x => J (F (z x))) l (𝓝 (J w)) :=
    (hJ.continuousOn w hwin).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hw, hzin.mono fun x hx => mem_image_of_mem F hx⟩)
  have heq : ζ = J w := tendsto_nhds_unique hz (hJlim.congr' (hzin.mono fun x hx => hJF _ hx))
  have hmem := hJmap hwin
  rw [mem_ball_zero_iff, ← heq, hζ] at hmem; linarith

def riemannCapCenterAngle (ζ : ℂ) : ℝ := Complex.arg (-ζ)
def riemannCapHalfAngle (r : ℝ) : ℝ := Real.arccos (r / 2)

private theorem riemannCap_circle_norm_sq {ζ : ℂ} (hζ : ‖ζ‖ = 1) (r θ : ℝ) :
    ‖circleMap ζ r (riemannCapCenterAngle ζ + θ)‖ ^ 2 = 1 + r ^ 2 - 2 * r * Real.cos θ := by
  have he : Complex.exp ((riemannCapCenterAngle ζ : ℂ) * Complex.I) = -ζ := by
    simpa only [riemannCapCenterAngle, norm_neg, hζ, Complex.ofReal_one, one_mul]
      using Complex.norm_mul_exp_arg_mul_I (-ζ)
  have hcm : circleMap ζ r (riemannCapCenterAngle ζ + θ) = ζ * (1 - circleMap 0 r θ) := by
    simp only [circleMap, zero_add, Complex.ofReal_add, add_mul, Complex.exp_add, he]; ring
  rw [hcm, norm_mul, hζ, one_mul, ← Complex.normSq_eq_norm_sq]
  calc Complex.normSq (1 - circleMap 0 r θ)
      = (1 - r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 := by simp [circleMap, Complex.normSq_apply, pow_two]
    _ = 1 + r ^ 2 - 2 * r * Real.cos θ := by linear_combination r ^ 2 * Real.sin_sq_add_cos_sq θ

theorem riemannCap_geometry {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
    let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
    a < b ∧ b ≤ a + 2 * Real.pi ∧
      MapsTo (circleMap ζ r) (Ioo a b) (ball (0 : ℂ) 1) ∧
      ‖circleMap ζ r a‖ = 1 ∧ ‖circleMap ζ r b‖ = 1 := by
  let α := riemannCapHalfAngle r
  have hα : 0 < α := Real.arccos_pos.2 (by linarith)
  have hαπ : α ≤ Real.pi := Real.arccos_le_pi _
  have hc : Real.cos α = r / 2 := Real.cos_arccos (by linarith) (by linarith)
  dsimp
  refine ⟨by dsimp [α] at hα; linarith, by dsimp [α] at hαπ; linarith, fun θ hθ => ?_, ?_, ?_⟩
  · let u := θ - riemannCapCenterAngle ζ
    have hu : |u| < α := abs_lt.2 ⟨by dsimp [u, α]; linarith [hθ.1], by dsimp [u, α]; linarith [hθ.2]⟩
    have hcos : r / 2 < Real.cos u := by
      rw [← hc, ← Real.cos_abs u]; exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) hαπ hu
    rw [mem_ball_zero_iff]
    refine (sq_lt_one_iff₀ (norm_nonneg _)).1 ?_
    rw [show θ = riemannCapCenterAngle ζ + u by dsimp [u]; ring, riemannCap_circle_norm_sq hζ]; nlinarith
  · have hsq : ‖circleMap ζ r (riemannCapCenterAngle ζ - riemannCapHalfAngle r)‖ ^ 2 = 1 := by
      rw [show riemannCapCenterAngle ζ - riemannCapHalfAngle r = riemannCapCenterAngle ζ + -α by dsimp [α]; ring,
        riemannCap_circle_norm_sq hζ, Real.cos_neg, hc]; ring
    nlinarith [norm_nonneg (circleMap ζ r (riemannCapCenterAngle ζ - riemannCapHalfAngle r))]
  · have hsq : ‖circleMap ζ r (riemannCapCenterAngle ζ + riemannCapHalfAngle r)‖ ^ 2 = 1 := by
      rw [riemannCap_circle_norm_sq hζ, hc]; ring
    nlinarith [norm_nonneg (circleMap ζ r (riemannCapCenterAngle ζ + riemannCapHalfAngle r))]

theorem jordanParam_eq_of_eq_of_abs_sub_lt {γ : ℝ → ℂ}
    (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : InjOn γ (Ico 0 (2 * Real.pi))) {x y : ℝ}
    (hxy : γ x = γ y) (hlt : |x - y| < 2 * Real.pi) : x = y := by
  have hmem (z : ℝ) : toIcoMod Real.two_pi_pos 0 z ∈ Ico 0 (2 * Real.pi) := by
    simpa only [zero_add] using toIcoMod_mem_Ico Real.two_pi_pos 0 z
  have hval (z : ℝ) : γ (toIcoMod Real.two_pi_pos 0 z) = γ z := by rw [toIcoMod, hper.sub_zsmul_eq]
  have h := hinj (hmem x) (hmem y) (by rw [hval, hval, hxy])
  simp only [toIcoMod] at h
  let n := toIcoDiv Real.two_pi_pos 0 x
  let m := toIcoDiv Real.two_pi_pos 0 y
  have hd : x - y = ((n - m : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [zsmul_eq_mul, zsmul_eq_mul] at h; push_cast; dsimp [n, m]; linarith
  have hk : n - m = 0 := by
    rw [hd, abs_mul, abs_of_pos Real.two_pi_pos] at hlt
    have h1 : |((n - m : ℤ) : ℝ)| < 1 := lt_of_not_ge fun hc => by nlinarith [Real.two_pi_pos]
    rw [← Int.cast_abs] at h1
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast h1)
  rw [hk] at hd; simp only [Int.cast_zero, zero_mul] at hd; linarith

theorem jordanParam_exists_short_arc {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : InjOn γ (Ico 0 (2 * Real.pi))) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ γ '' Icc 0 (2 * Real.pi), ∀ q ∈ γ '' Icc 0 (2 * Real.pi),
      ‖p - q‖ < δ → ∃ (A : ℝ → ℂ) (C : NNReal), LipschitzWith C A ∧
        A 0 = p ∧ A 1 = q ∧ MapsTo A (Icc 0 1) (γ '' Icc 0 (2 * Real.pi)) ∧
        (∀ u ∈ Icc 0 1, ∀ v ∈ Icc 0 1, ‖A u - A v‖ < ε) ∧
        (p ≠ q → InjOn A (Icc 0 1)) := by
  let η : ℝ := min Real.pi (ε / ((K : ℝ) + 1))
  have hη : 0 < η := lt_min Real.pi_pos (div_pos hε (by positivity))
  have hηπ : η < 2 * Real.pi := (min_le_left _ _).trans_lt (by linarith [Real.pi_pos])
  let S : Set (ℝ × ℝ) := (Icc 0 (2 * Real.pi) ×ˢ Icc 0 (2 * Real.pi)) ∩
    {p | η ≤ |p.1 - p.2| ∧ |p.1 - p.2| ≤ 2 * Real.pi - η}
  have hSc : IsCompact S := (isCompact_Icc.prod isCompact_Icc).inter_right
    ((isClosed_le continuous_const (continuous_fst.sub continuous_snd).abs).inter
      (isClosed_le (continuous_fst.sub continuous_snd).abs continuous_const))
  have hn : Continuous (fun p : ℝ × ℝ => ‖γ p.1 - γ p.2‖) :=
    ((hK.continuous.comp continuous_fst).sub (hK.continuous.comp continuous_snd)).norm
  have hpos (p : ℝ × ℝ) (hp : p ∈ S) : 0 < ‖γ p.1 - γ p.2‖ := norm_pos_iff.mpr fun he => by
    have heq := jordanParam_eq_of_eq_of_abs_sub_lt hper hinj (sub_eq_zero.mp he) (hp.2.2.trans_lt (by linarith))
    have ha := hp.2.1; rw [heq, sub_self, abs_zero] at ha; linarith
  obtain ⟨δ, hδ, hbound⟩ : ∃ δ > 0, ∀ p ∈ S, δ ≤ ‖γ p.1 - γ p.2‖ := by
    rcases S.eq_empty_or_nonempty with he | hne
    · exact ⟨1, zero_lt_one, by simp [he]⟩
    · obtain ⟨p, hp, hmin⟩ := hSc.exists_isMinOn hne hn.continuousOn
      exact ⟨_, hpos p hp, fun q hq => hmin hq⟩
  refine ⟨δ, hδ, ?_⟩
  rintro p ⟨s, hs, hsp⟩ q ⟨t, ht, htq⟩ hpq
  have hmod : ∃ d : ℝ, |d| < η ∧ γ (s + d) = γ t := by
    have hst : ‖γ s - γ t‖ < δ := by simpa only [hsp, htq] using hpq
    have hshort : |s - t| < η ∨ 2 * Real.pi - |s - t| < η := by
      by_contra h; push_neg at h
      exact (not_lt_of_ge (hbound (s, t) ⟨⟨hs, ht⟩, h.1, by linarith [h.2]⟩)) hst
    rcases hshort with h | h
    · exact ⟨t - s, by simpa only [abs_sub_comm] using h, by congr 1; ring⟩
    · by_cases hst' : s ≤ t
      · refine ⟨t - s - 2 * Real.pi, ?_, by rw [show s + (t - s - 2 * Real.pi) = t - 2 * Real.pi by ring]; exact hper.sub_eq t⟩
        rw [abs_sub_comm s t, abs_of_nonneg (sub_nonneg.mpr hst')] at h
        rw [abs_of_nonpos (by linarith [ht.2, hs.1])]; linarith
      · refine ⟨t - s + 2 * Real.pi, ?_, by rw [show s + (t - s + 2 * Real.pi) = t + 2 * Real.pi by ring]; exact hper t⟩
        rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hst'))] at h
        rw [abs_of_nonneg (by linarith [hs.2, ht.1])]; linarith
  obtain ⟨d, hd, hend⟩ := hmod
  let A : ℝ → ℂ := fun u => γ (s + d * u)
  let C : NNReal := K * Real.toNNReal |d|
  have hAC : LipschitzWith C A := LipschitzWith.of_dist_le_mul fun u v => by
    simpa only [A, C, NNReal.coe_mul, Real.coe_toNNReal _ (abs_nonneg d),
      Real.dist_eq, show s + d * u - (s + d * v) = d * (u - v) by ring, abs_mul, mul_assoc]
      using hK.dist_le_mul (s + d * u) (s + d * v)
  have hsmall : (K : ℝ) * |d| < ε := by
    have h1 : ((K : ℝ) + 1) * |d| < ((K : ℝ) + 1) * η := mul_lt_mul_of_pos_left hd (by positivity)
    have h2 : ((K : ℝ) + 1) * η ≤ ε := by
      simpa only [mul_comm] using (le_div_iff₀ (by positivity)).mp (min_le_right Real.pi (ε / ((K : ℝ) + 1)))
    exact (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg d)).trans_lt (h1.trans_le h2)
  have huv (u : ℝ) (hu : u ∈ Icc 0 1) (v : ℝ) (hv : v ∈ Icc 0 1) : |u - v| ≤ 1 :=
    abs_le.2 ⟨by linarith [hu.1, hv.2], by linarith [hu.2, hv.1]⟩
  refine ⟨A, C, hAC, by simpa only [A, mul_zero, add_zero] using hsp,
    by simpa only [A, mul_one] using hend.trans htq,
    fun u _ => ⟨toIcoMod Real.two_pi_pos 0 _, Ico_subset_Icc_self (by simpa using toIcoMod_mem_Ico Real.two_pi_pos 0 _),
      by rw [toIcoMod, hper.sub_zsmul_eq]⟩,
    fun u hu v hv => ?_, fun hpq u hu v hv heq => ?_⟩
  · have h := hAC.dist_le_mul u v
    rw [dist_eq_norm, Real.dist_eq, show (C : ℝ) = (K : ℝ) * |d| by
      simp only [C, NNReal.coe_mul, Real.coe_toNNReal _ (abs_nonneg d)]] at h
    exact (h.trans (mul_le_of_le_one_right (by positivity) (huv u hu v hv))).trans_lt hsmall
  · have hd0 : d ≠ 0 := fun he => hpq (by rw [he, add_zero, hsp, htq] at hend; exact hend)
    have hdist : |(s + d * u) - (s + d * v)| < 2 * Real.pi := by
      rw [show (s + d * u) - (s + d * v) = d * (u - v) by ring, abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg d) (huv u hu v hv)).trans_lt (hd.trans hηπ)
    exact mul_left_cancel₀ hd0 (add_left_cancel (jordanParam_eq_of_eq_of_abs_sub_lt hper hinj heq hdist))

theorem riemannMapping_cap_injOn_Ico (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (hinj : InjOn F (ball (0 : ℂ) 1))
    {ζ : ℂ} {r a b : ℝ} (hr : r ≠ 0) (hwidth : b - a ≤ 2 * Real.pi)
    (harc : MapsTo (circleMap ζ r) (Ioo a b) (ball (0 : ℂ) 1))
    {G : ℝ → ℂ} (hGeq : EqOn G (fun θ => F (circleMap ζ r θ)) (Ioo a b))
    (hGa : G a ∈ frontier (F '' ball (0 : ℂ) 1)) : InjOn G (Ico a b) := by
  have hopen := RiemannInterior.isOpen_image_of_injOn isOpen_ball
    (convex_ball (0 : ℂ) 1).isPreconnected hF hinj Subset.rfl isOpen_ball
  have hnot : G a ∉ F '' ball (0 : ℂ) 1 := by rw [hopen.frontier_eq] at hGa; exact hGa.2
  intro x hx y hy heq
  rcases eq_or_lt_of_le hx.1 with hxa | hxa <;> rcases eq_or_lt_of_le hy.1 with hya | hya
  · exact hxa.symm.trans hya
  · exact False.elim (hnot ⟨circleMap ζ r y, harc ⟨hya, hy.2⟩,
      (hGeq ⟨hya, hy.2⟩).symm.trans (heq.symm.trans (congrArg G hxa.symm))⟩)
  · exact False.elim (hnot ⟨circleMap ζ r x, harc ⟨hxa, hx.2⟩,
      (hGeq ⟨hxa, hx.2⟩).symm.trans (heq.trans (congrArg G hya.symm))⟩)
  · exact injOn_circleMap_of_abs_sub_le' hr hwidth hx hy
      (hinj (harc ⟨hxa, hx.2⟩) (harc ⟨hya, hy.2⟩) ((hGeq ⟨hxa, hx.2⟩).symm.trans (heq.trans (hGeq ⟨hya, hy.2⟩))))

theorem riemannMapping_cap_injOn_Icc (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (hinj : InjOn F (ball (0 : ℂ) 1))
    {ζ : ℂ} {r a b : ℝ} (hr : r ≠ 0) (hwidth : b - a ≤ 2 * Real.pi)
    (harc : MapsTo (circleMap ζ r) (Ioo a b) (ball (0 : ℂ) 1))
    {G : ℝ → ℂ} (hGeq : EqOn G (fun θ => F (circleMap ζ r θ)) (Ioo a b))
    (hGa : G a ∈ frontier (F '' ball (0 : ℂ) 1))
    (hGb : G b ∈ frontier (F '' ball (0 : ℂ) 1)) (hab : G a ≠ G b) :
    InjOn G (Icc a b) := by
  have hopen := RiemannInterior.isOpen_image_of_injOn isOpen_ball
    (convex_ball (0 : ℂ) 1).isPreconnected hF hinj Subset.rfl isOpen_ball
  have hnot : G b ∉ F '' ball (0 : ℂ) 1 := by rw [hopen.frontier_eq] at hGb; exact hGb.2
  have hi := riemannMapping_cap_injOn_Ico F hF hinj hr hwidth harc hGeq hGa
  intro x hx y hy heq
  rcases lt_or_eq_of_le hx.2 with hxb | hxb <;> rcases lt_or_eq_of_le hy.2 with hyb | hyb
  · exact hi ⟨hx.1, hxb⟩ ⟨hy.1, hyb⟩ heq
  · rcases eq_or_lt_of_le hx.1 with hxa | hxa
    · exact False.elim (hab (by simpa only [← hxa, hyb] using heq))
    · exact False.elim (hnot ⟨circleMap ζ r x, harc ⟨hxa, hxb⟩,
        (hGeq ⟨hxa, hxb⟩).symm.trans (heq.trans (congrArg G hyb))⟩)
  · rcases eq_or_lt_of_le hy.1 with hya | hya
    · exact False.elim (hab (by simpa only [hxb, ← hya] using heq.symm))
    · exact False.elim (hnot ⟨circleMap ζ r y, harc ⟨hya, hyb⟩,
        (hGeq ⟨hya, hyb⟩).symm.trans (heq.symm.trans (congrArg G hxb))⟩)
  · exact hxb.trans hyb.symm

theorem windingNumber_eq_zero_of_image_ball {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ (2 * Real.pi) = γ 0)
    {p z : ℂ} {R : ℝ} (hball : ∀ θ ∈ Icc 0 (2 * Real.pi), ‖γ θ - p‖ < R)
    (hfar : R ≤ ‖p - z‖) : windingNumber γ z = 0 := by
  have hdpos : 0 < ‖p - z‖ := ((norm_nonneg _).trans_lt (hball 0 ⟨le_rfl, Real.two_pi_pos.le⟩)).trans_le hfar
  have hd : p - z ≠ 0 := norm_pos_iff.mp hdpos
  have hslit (θ : ℝ) (hθ : θ ∈ Icc 0 (2 * Real.pi)) : (p - z)⁻¹ * (γ θ - z) ∈ Complex.slitPlane := by
    rw [show (p - z)⁻¹ * (γ θ - z) = 1 + (γ θ - p) / (p - z) by field_simp [hd]; ring]
    exact Complex.mem_slitPlane_of_norm_lt_one (by rw [norm_div]; exact (div_lt_one hdpos).mpr ((hball θ hθ).trans_le hfar))
  have hi := integral_deriv_div_eq_log_sub hK Real.two_pi_pos.le (inv_ne_zero hd) hslit
  rw [hclosed, sub_self] at hi; simp only [windingNumber, hi, mul_zero]

def riemannCapArcLength (F : ℂ → ℂ) (c : ℂ) (r a θ : ℝ) : ℝ :=
  ∫ s in a..θ, ‖riemannCapDerivative F c r s‖

private theorem riemannCapArcLength_strictMonoOn (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (hinj : InjOn F (ball (0 : ℂ) 1))
    (c : ℂ) {r a b : ℝ} (hr : r ≠ 0) (hwidth : b - a ≤ 2 * Real.pi)
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi))
    (harc : MapsTo (circleMap c r) (Ioo a b) (ball (0 : ℂ) 1))
    {G : ℝ → ℂ} (hGc : Continuous G) (hGeq : EqOn G (fun θ => F (circleMap c r θ)) (Ioo a b)) :
    StrictMonoOn (riemannCapArcLength F c r a) (Icc a b) := by
  let ℓ := riemannCapArcLength F c r a
  have hsub_int (θ ψ : ℝ) : ℓ ψ - ℓ θ = ∫ s in θ..ψ, ‖riemannCapDerivative F c r s‖ :=
    intervalIntegral.integral_interval_sub_left
      (riemannCapDerivative_intervalIntegrable F c r hi a ψ).norm
      (riemannCapDerivative_intervalIntegrable F c r hi a θ).norm
  have hm : Monotone ℓ := fun θ ψ hθψ => sub_nonneg.mp <| by
    rw [hsub_int]; exact intervalIntegral.integral_nonneg_of_forall hθψ fun _ => norm_nonneg _
  intro θ hθ ψ hψ hθψ
  by_contra h
  have he : ℓ θ = ℓ ψ := le_antisymm (hm hθψ.le) (le_of_not_gt h)
  let v := (2 * θ + ψ) / 3
  let w := (θ + 2 * ψ) / 3
  have hvθ : θ < v := by dsimp [v]; linarith
  have hvw : v < w := by dsimp [v, w]; linarith
  have hwψ : w < ψ := by dsimp [w]; linarith
  have hv : v ∈ Ioo a b := ⟨hθ.1.trans_lt hvθ, (hvw.trans hwψ).trans_le hψ.2⟩
  have hw : w ∈ Ioo a b := ⟨hθ.1.trans_lt (hvθ.trans hvw), hwψ.trans_le hψ.2⟩
  have hd := riemannMapping_cap_extension_subarc_displacement F hF c r hi harc hGc hGeq
    (Ioo_subset_Icc_self hv) (Ioo_subset_Icc_self hw) hvw.le
  rw [← hsub_int] at hd
  have hGwv := sub_eq_zero.mp (norm_le_zero_iff.mp (by linarith [hm hvθ.le, hm hwψ.le] : ‖G w - G v‖ ≤ 0))
  exact hvw.ne (injOn_circleMap_of_abs_sub_le' hr hwidth (Ioo_subset_Ico_self hw) (Ioo_subset_Ico_self hv)
    (hinj (harc hw) (harc hv) ((hGeq hw).symm.trans (hGwv.trans (hGeq hv))))).symm

theorem riemannMapping_exists_small_lipschitz_cap (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ (r : ℝ) (G : ℝ → ℂ) (τ : ℝ → ℝ) (H : ℝ → ℂ),
      0 < r ∧ r < δ ∧ r < 1 ∧ Continuous G ∧ LipschitzWith 1 H ∧
      let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
      let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
      let ℓ := riemannCapArcLength F ζ r a
      0 < ℓ b ∧ ℓ b < ε ∧
      EqOn G (fun θ => F (circleMap ζ r θ)) (Ioo a b) ∧
      G a ∈ frontier (F '' ball (0 : ℂ) 1) ∧
      G b ∈ frontier (F '' ball (0 : ℂ) 1) ∧
      (∀ u, τ u ∈ Icc a b) ∧
      (∀ u ∈ Icc 0 (ℓ b), ℓ (τ u) = u) ∧
      (∀ u, H u = G (τ u)) ∧ H 0 = G a ∧ H (ℓ b) = G b ∧
      H '' Icc 0 (ℓ b) = G '' Icc a b ∧ InjOn H (Ico 0 (ℓ b)) := by
  obtain ⟨r, hr, hi, hlength⟩ := riemannMapping_exists_small_cap_length F hF hinj hb ζ
    (lt_min hδ zero_lt_one) hε
  have hrδ := hr.2.trans_le (min_le_left δ 1)
  have hr1 := hr.2.trans_le (min_le_right δ 1)
  let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
  let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
  let ℓ := riemannCapArcLength F ζ r a
  obtain ⟨hab, hwidth, harc, hza, hzb⟩ := riemannCap_geometry hζ hr.1 hr1
  have hwidth' : b - a ≤ 2 * Real.pi := by linarith
  obtain ⟨G, hGc, hGeq, hGaLim, hGbLim⟩ :=
    riemannMapping_cap_continuous_extension F hF ζ r hi hab harc
  have hGa : G a ∈ frontier (F '' ball (0 : ℂ) 1) := by
    letI := left_nhdsWithin_Ioo_neBot hab
    exact riemannMapping_limit_mem_frontier F hF hinj hza
      (by filter_upwards [self_mem_nhdsWithin] with θ hθ; exact harc hθ)
      (((continuous_circleMap ζ r).tendsto a).mono_left nhdsWithin_le_nhds) hGaLim
  have hGb : G b ∈ frontier (F '' ball (0 : ℂ) 1) := by
    letI := right_nhdsWithin_Ioo_neBot hab
    exact riemannMapping_limit_mem_frontier F hF hinj hzb
      (by filter_upwards [self_mem_nhdsWithin] with θ hθ; exact harc hθ)
      (((continuous_circleMap ζ r).tendsto b).mono_left nhdsWithin_le_nhds) hGbLim
  have hℓc : Continuous ℓ := intervalIntegral.continuous_primitive
    (fun s t => (riemannCapDerivative_intervalIntegrable F ζ r hi s t).norm) a
  have hℓs : StrictMonoOn ℓ (Icc a b) :=
    riemannCapArcLength_strictMonoOn F hF hinj ζ hr.1.ne' hwidth' hi harc hGc hGeq
  have hℓa : ℓ a = 0 := by simp only [ℓ, riemannCapArcLength, intervalIntegral.integral_same]
  have hL : 0 < ℓ b := by rw [← hℓa]; exact hℓs ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
  have hLε : ℓ b < ε := by
    let V := riemannCapDerivative F ζ r
    have hp : Function.Periodic (fun s => ‖V s‖) (2 * Real.pi) :=
      (riemannCapDerivative_periodic F ζ r).comp norm
    have hle : ℓ b ≤ ∫ s in Ioo (-Real.pi) Real.pi, ‖V s‖ :=
      calc ℓ b ≤ ∫ s in a..a + 2 * Real.pi, ‖V s‖ :=
              intervalIntegral.integral_mono_interval le_rfl hab.le hwidth
                (Eventually.of_forall fun _ => norm_nonneg _)
                (riemannCapDerivative_intervalIntegrable F ζ r hi a _).norm
        _ = ∫ s in (-Real.pi)..Real.pi, ‖V s‖ := by
              simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring] using hp.intervalIntegral_add_eq a (-Real.pi)
        _ = _ := by rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
    exact hle.trans_lt hlength
  let f : Icc a b → Icc 0 (ℓ b) := fun θ =>
    ⟨ℓ θ, ⟨hℓa ▸ hℓs.monotoneOn ⟨le_rfl, hab.le⟩ θ.property θ.property.1,
      hℓs.monotoneOn θ.property ⟨hab.le, le_rfl⟩ θ.property.2⟩⟩
  have hfo : Function.Surjective f := fun u => by
    obtain ⟨θ, hθ, heq⟩ := intermediate_value_Icc hab.le hℓc.continuousOn
      (by simpa only [hℓa] using u.property : (u : ℝ) ∈ Icc (ℓ a) (ℓ b))
    exact ⟨⟨θ, hθ⟩, Subtype.ext heq⟩
  let e : Icc a b ≃o Icc 0 (ℓ b) := StrictMono.orderIsoOfSurjective f (fun θ ψ h => hℓs θ.property ψ.property h) hfo
  let τ : ℝ → ℝ := fun u => (e.symm (projIcc 0 (ℓ b) hL.le u) : ℝ)
  let H : ℝ → ℂ := fun u => G (τ u)
  have hτmem (u : ℝ) : τ u ∈ Icc a b := (e.symm _).property
  have hτℓ (u : ℝ) : ℓ (τ u) = (projIcc 0 (ℓ b) hL.le u : ℝ) :=
    congrArg Subtype.val (e.apply_symm_apply (projIcc 0 (ℓ b) hL.le u))
  have hτr (u : ℝ) (hu : u ∈ Icc 0 (ℓ b)) : ℓ (τ u) = u := by rw [hτℓ, projIcc_of_mem _ hu]
  have hτl (θ : ℝ) (hθ : θ ∈ Icc a b) : τ (ℓ θ) = θ := by
    have hp : projIcc 0 (ℓ b) hL.le (ℓ θ) = e ⟨θ, hθ⟩ := by rw [projIcc_of_mem _ (f ⟨θ, hθ⟩).property]; rfl
    change (e.symm (projIcc 0 (ℓ b) hL.le (ℓ θ)) : ℝ) = θ; rw [hp, e.symm_apply_apply]
  have hdom (θ : ℝ) (hθ : θ ∈ Icc a b) (ψ : ℝ) (hψ : ψ ∈ Icc a b) (hθψ : θ ≤ ψ) :
      ‖G ψ - G θ‖ ≤ ℓ ψ - ℓ θ := by
    rw [show ℓ ψ - ℓ θ = ∫ s in θ..ψ, ‖riemannCapDerivative F ζ r s‖ from
      intervalIntegral.integral_interval_sub_left
        (riemannCapDerivative_intervalIntegrable F ζ r hi a ψ).norm
        (riemannCapDerivative_intervalIntegrable F ζ r hi a θ).norm]
    exact riemannMapping_cap_extension_subarc_displacement F hF ζ r hi harc hGc hGeq hθ hψ hθψ
  have habs (θ : ℝ) (hθ : θ ∈ Icc a b) (ψ : ℝ) (hψ : ψ ∈ Icc a b) : ‖G θ - G ψ‖ ≤ |ℓ θ - ℓ ψ| := by
    rcases le_total θ ψ with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr (hℓs.monotoneOn hθ hψ h)), norm_sub_rev]
      linarith [hdom θ hθ ψ hψ h]
    · rw [abs_of_nonneg (sub_nonneg.mpr (hℓs.monotoneOn hψ hθ h))]; exact hdom ψ hψ θ hθ h
  have hHlip : LipschitzWith 1 H := LipschitzWith.of_dist_le_mul fun u v => by
    have h := habs (τ u) (hτmem u) (τ v) (hτmem v)
    rw [hτℓ, hτℓ] at h
    have hc := (LipschitzWith.projIcc hL.le).dist_le_mul u v
    rw [Subtype.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at hc
    simpa only [H, dist_eq_norm, NNReal.coe_one, one_mul, Real.dist_eq] using h.trans hc
  have hHim : H '' Icc 0 (ℓ b) = G '' Icc a b := by
    ext z; constructor
    · rintro ⟨u, _, rfl⟩; exact ⟨τ u, hτmem u, rfl⟩
    · rintro ⟨θ, hθ, rfl⟩; exact ⟨ℓ θ, (f ⟨θ, hθ⟩).property, by simp only [H, hτl θ hθ]⟩
  have hGi := riemannMapping_cap_injOn_Ico F hF hinj hr.1.ne' hwidth' harc hGeq hGa
  have hHi : InjOn H (Ico 0 (ℓ b)) := fun u hu v hv heq => by
    have hτi (s : ℝ) (hs : s ∈ Ico 0 (ℓ b)) : τ s ∈ Ico a b :=
      ⟨(hτmem s).1, lt_of_le_of_ne (hτmem s).2 fun hsb => by
        have h := hτr s (Ico_subset_Icc_self hs); rw [hsb] at h; linarith [hs.2]⟩
    have hτuv : τ u = τ v := hGi (hτi u hu) (hτi v hv) heq
    have hru := hτr u (Ico_subset_Icc_self hu); rw [hτuv] at hru
    exact hru.symm.trans (hτr v (Ico_subset_Icc_self hv))
  exact ⟨r, G, τ, H, hr.1, hrδ, hr1, hGc, hHlip, hL, hLε, hGeq, hGa, hGb, hτmem, hτr,
    fun _ => rfl, congrArg G (by simpa only [hℓa] using hτl a ⟨le_rfl, hab.le⟩),
    congrArg G (hτl b ⟨hab.le, le_rfl⟩), hHim, hHi⟩

end PolyaNeumann
end
