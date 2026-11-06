module

public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.Order.IsLUB
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Tactic

/-!
# The interior Riemann mapping theorem

This file contains the local proof dependencies of the interior Riemann
mapping theorem: injective holomorphic maps have nonzero derivative,
disk automorphisms, holomorphic square roots, Montel compactness, Hurwitz
injectivity, and the extremal-map argument. The proof is adapted from the
reference Dirichlet formalization.

The resulting map is holomorphic and injective on the open disk. No claim
about smooth extension to its boundary is part of this theorem.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann.RiemannInterior

section

/-! ## Injective holomorphic maps have nonvanishing derivative -/

open Complex Metric Filter Topology Set

/-- **Injective holomorphic functions have nonzero derivative.** -/
theorem deriv_ne_zero_of_injOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) {a : ℂ} (ha : a ∈ U) :
    deriv f a ≠ 0 := by
  intro h0
  have hUa  := hU.mem_nhds ha
  set g : ℂ → ℂ := fun z => f z - f a with hg
  have hgan : AnalyticAt ℂ g a := ((hf.analyticOnNhd hU) a ha).sub analyticAt_const
  -- `g` is not identically zero near `a`
  obtain ⟨n, h, hhan, hha, hgeq⟩ := hgan.exists_eventuallyEq_pow_smul_nonzero_iff.2 (by
    intro hev
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1 (inter_mem hev hUa)
    have hmem : a + (ε / 2 : ℝ) ∈ ball a ε := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith
    have h1 := hεsub hmem
    have := hinj h1.2 ha (sub_eq_zero.1 h1.1)
    simp_all)
  simp  at hgeq
  -- `n ≥ 2`
  have hderg : deriv g a = 0 := by
    simp_all
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · have := hgeq.self_of_nhds
        simp_all 
      · have hd : HasDerivAt (fun z => (z - a) ^ 1 * h z)
            (1 * h a + (a - a) ^ 1 * deriv h a) a := by
          have h1 : HasDerivAt (fun z => (z - a) ^ 1) 1 a := by
            simpa using (hasDerivAt_id a).sub_const a
          exact h1.mul hhan.differentiableAt.hasDerivAt
        have := hd.deriv
        rw [← Filter.EventuallyEq.deriv_eq hgeq] at this
        simp_all 
    grind
  have hn0 : n ≠ 0 := by omega
  -- an `n`-th root of `h` near `a`
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c ^ n = h a := IsAlgClosed.exists_pow_nat_eq _ (by omega)
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp_all 
  set q : ℂ → ℂ := fun z => h z / h a with hq
  have hqa : q a = 1 := div_self hha
  have hqan : AnalyticAt ℂ q a := hhan.div analyticAt_const hha
  have hslit : q a ∈ slitPlane := by simp_all
  set ψ : ℂ → ℂ := fun z => c * exp (log (q z) / n) with hψ
  have hψan : AnalyticAt ℂ ψ a := by
    fun_prop
  have hψpow : ∀ᶠ z in 𝓝 a, ψ z ^ n = h z := by
    filter_upwards [hqan.continuousAt.preimage_mem_nhds (isOpen_slitPlane.mem_nhds hslit)] with z hz
    rw [mul_pow, hc, ← exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hn0),
      exp_log (slitPlane_ne_zero hz), hq]
    field_simp
  set φ : ℂ → ℂ := fun z => (z - a) * ψ z with hφ
  have hφan : AnalyticAt ℂ φ a := (analyticAt_id.sub analyticAt_const).mul hψan
  have hφa : φ a = 0 := by grind
  have hφd : HasDerivAt φ c a := by
    have := ((hasDerivAt_id a).sub_const a).mul hψan.differentiableAt.hasDerivAt
    simp_all [Pi.mul_def]
  have himg : φ '' {z | z ∈ U ∧ g z = φ z ^ n} ∈ 𝓝 0 := by
    rw [← hφa]
    exact hφan.eventually_constant_or_nhds_le_map_nhds.resolve_left (by
    intro hev
    have : deriv φ a = 0 := by
      have hev' : φ =ᶠ[𝓝 a] fun _ => φ a := hev
      simp [hev'.deriv_eq]
    rw [hφd.deriv] at this
    grind) (image_mem_map (by
    filter_upwards [hUa, hgeq, hψpow] with z hz h1 h2
    simp_all [mul_pow]))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 himg
  set ε : ℂ := ((δ / 2 : ℝ) : ℂ) with hε
  set ζ : ℂ := exp (2 * Real.pi * I / n) with hζ
  have hζprim  := Complex.isPrimitiveRoot_exp n hn0
  have hεnorm : ‖ε‖ = δ / 2 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hε0 : ε ≠ 0 := by
    intro h; rw [h, norm_zero] at hεnorm; linarith
  have hm2 : ε * ζ ∈ ball 0 δ := by
    rw [mem_ball_zero_iff, norm_mul, hζprim.norm'_eq_one hn0]; linarith
  obtain ⟨z1, ⟨hz1U, hz1g⟩, hz1⟩ := hδsub (by
    rw [mem_ball_zero_iff]; linarith)
  obtain ⟨z2, ⟨hz2U, hz2g⟩, hz2⟩ := hδsub hm2
  have hgz : g z1 = g z2 := by
    rw [hz1g, hz2g, hz1, hz2, mul_pow, hζprim.pow_eq_one, mul_one]
  simp_all [hinj hz1U hz2U (by
    grind)]

end

section

/-! ## Disk automorphisms `z ↦ (z - a) / (1 - ā z)` -/

open Complex Metric

/-- The disk automorphism `mob a z = (z - a) / (1 - ā z)`. -/
def mob (a z : ℂ) : ℂ := (z - a) / (1 - (starRingEnd ℂ) a * z)

variable (a : ℂ)

lemma mob_denom_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 - (starRingEnd ℂ) a * z ≠ 0 := by
  intro h
  have h1 : (starRingEnd ℂ) a * z = 1 := by grind
  have : ‖(starRingEnd ℂ) a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖a‖ * ‖z‖ ≤ ‖a‖ * 1 := by gcongr
      _ < 1 := by linarith
  simp_all 

/-- The key identity `|1 - ā z|² - |z - a|² = (1 - |a|²)(1 - |z|²)`. -/
lemma normSq_identity (a z : ℂ) :
    normSq (1 - (starRingEnd ℂ) a * z) - normSq (z - a) =
      (1 - normSq a) * (1 - normSq z) := by
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, conj_re, conj_im, one_re, one_im]
  ring

lemma norm_mob_lt_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : ‖mob a z‖ < 1 := by
  unfold mob
  rw [norm_div, div_lt_one (norm_pos_iff.2 (mob_denom_ne_zero ha hz))]
  have hid := normSq_identity a z
  have ha2 : normSq a < 1 := by
    simp_all [normSq_eq_norm_sq]
  have hz2 : normSq z < 1 := by
    simp_all [normSq_eq_norm_sq]
  have : normSq (z - a) < normSq (1 - (starRingEnd ℂ) a * z) := by
    nlinarith 
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at this
  nlinarith [norm_nonneg (1 - (starRingEnd ℂ) a * z)]

lemma mob_mem_ball {a z : ℂ} (ha : a ∈ ball 0 1) (hz : z ∈ ball 0 1) :
    mob a z ∈ ball 0 1 := by
  rw [mem_ball_zero_iff] at *
  exact norm_mob_lt_one ha hz

@[simp] lemma mob_self (a : ℂ) : mob a a = 0 := by simp [mob]

@[simp] lemma mob_zero : mob a 0 = -a := by simp [mob]

lemma mob_neg_mob {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : mob (-a) (mob a z) = z := by
  have hd := mob_denom_ne_zero ha hz
  unfold mob
  rw [map_neg]
  have h2 : 1 - -(starRingEnd ℂ) a * ((z - a) / (1 - (starRingEnd ℂ) a * z)) =
      (1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z) := by
    field_simp; ring
  rw [h2, div_eq_iff (div_ne_zero (mob_denom_ne_zero ha ha) hd)]
  grind

lemma mob_injOn {a : ℂ} (ha : ‖a‖ < 1) : Set.InjOn (mob a) (ball 0 1) := by
  intro z hz w hw h
  rw [mem_ball_zero_iff] at hz hw
  rw [← mob_neg_mob ha hz, ← mob_neg_mob ha hw, h]

lemma hasDerivAt_mob {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    HasDerivAt (mob a) ((1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z) ^ 2) z := by
  have h1 : HasDerivAt (fun w => w - a) 1 z := (hasDerivAt_id z).sub_const a
  have := h1.div (by
    simpa using ((hasDerivAt_id z).const_mul ((starRingEnd ℂ) a)).const_sub 1) (mob_denom_ne_zero ha hz)
  convert this using 1
  · rfl
  ring

lemma differentiableAt_mob {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (mob a) z := (hasDerivAt_mob ha hz).differentiableAt

lemma mob_eq_zero_iff {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : mob a z = 0 ↔ z = a := by
  constructor
  · intro h
    unfold mob at h
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · grind
    · exact absurd h (mob_denom_ne_zero ha hz)
  simp_all

end

section

/-! ## Holomorphic square roots on simply connected domains -/

open Complex Metric Filter Topology Set

/-- A continuous square root of a differentiable function is differentiable where it does
not vanish. -/
lemma hasDerivAt_of_sq_eq {g f : ℂ → ℂ} {z : ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 z)
    (hg : ContinuousAt g z) (hsq : ∀ w ∈ U, g w ^ 2 = f w) (hf : DifferentiableAt ℂ f z)
    (hgz : g z ≠ 0) : HasDerivAt g (deriv f z / (2 * g z)) z := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hsum : Tendsto (fun w => g w + g z) (𝓝[≠] z) (𝓝 (2 * g z)) := by
    have : Tendsto (fun w => g w + g z) (𝓝 z) (𝓝 (g z + g z)) := hg.add tendsto_const_nhds
    rw [two_mul]
    exact this.mono_left nhdsWithin_le_nhds
  have h2  := mul_ne_zero two_ne_zero hgz
  refine (hf.hasDerivAt.tendsto_slope.div hsum h2).congr' ?_
  filter_upwards [hsum.eventually_ne h2, nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with w hw1 hw2 hw3
  rw [Pi.div_apply, slope_def_field, slope_def_field, ← hsq w hw2, ← hsq z (mem_of_mem_nhds hU)]
  field_simp
  ring

open Classical in
/-- **Holomorphic square roots.** A nonvanishing holomorphic function on a simply connected
open subset of `ℂ` has a holomorphic square root. -/
theorem exists_sqrt_of_simplyConnected {Ω : Set ℂ} (hΩ : IsOpen Ω) [SimplyConnectedSpace Ω]
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) (hf0 : ∀ z ∈ Ω, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ Ω, g z ^ 2 = f z := by
  haveI := hΩ.locPathConnectedSpace
  obtain ⟨z0⟩ : Nonempty Ω := inferInstance
  let F : C(Ω, {x : ℂ // x ≠ 0}) :=
    ⟨fun z => ⟨f z, hf0 z z.2⟩, by
      refine Continuous.subtype_mk ?_ _
      exact hf.continuousOn.restrict⟩
  obtain ⟨e0, he0⟩ : ∃ e : ℂ, e ^ 2 = f z0 := IsAlgClosed.exists_pow_nat_eq _ two_pos
  obtain ⟨G, ⟨-, hGp⟩, -⟩ :=
    (isCoveringMap_npow  2 (by norm_num)).existsUnique_continuousMap_lifts F z0 ⟨e0, by
    grind⟩ (Subtype.ext he0)
  set g : ℂ → ℂ := fun z => if h : z ∈ Ω then G ⟨z, h⟩ else 0
    with hg_def
  have hsq : ∀ z ∈ Ω, g z ^ 2 = f z := by
    intro z hz
    have := congrArg Subtype.val (congrFun hGp ⟨z, hz⟩)
    simp_all [F]
  have hne : ∀ z ∈ Ω, g z ≠ 0 := by
    grind
  have hcont : ContinuousOn g Ω := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : Ω.domRestrict g = fun z  => (G z : ℂ) := by
      grind
    rw [this]
    fun_prop
  refine ⟨g, ?_, hsq⟩
  intro z hz
  have hU  := hΩ.mem_nhds hz
  exact (hasDerivAt_of_sq_eq hU (hcont.continuousAt hU) hsq
    (hf.differentiableAt hU) (hne z hz)).differentiableAt.differentiableWithinAt

end

section

/-! ## Montel's theorem -/

open Complex Metric Filter Topology Set

variable {ι : Type*} {F : ι → ℂ → ℂ} {U : Set ℂ}

/-- Cauchy estimate: a holomorphic family bounded by `1` on `U` is equicontinuous at every
point of `U`. -/
lemma equicontinuousAt_of_norm_le_one (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hb : ∀ i, ∀ z ∈ U, ‖F i z‖ ≤ 1) {z : ℂ}
    (hz : z ∈ U) : EquicontinuousAt F z := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z hz
  set r := ε / 3 with hr
  have hr0 : 0 < r := by positivity
  have hsub : ∀ y ∈ ball z r, closedBall y r ⊆ U := by
    intro y hy w hw
    apply hεU
    rw [mem_ball] at hy ⊢
    rw [mem_closedBall] at hw
    calc dist w z ≤ dist w y + dist y z := dist_triangle _ _ _
      _ < r + r := by linarith
      _ < ε := by linarith
  have hderiv : ∀ i, ∀ y ∈ ball z r, ‖deriv (F i) y‖ ≤ 1 / r := by
    intro i y hy
    apply norm_deriv_le_of_forall_mem_sphere_norm_le hr0
    · apply DifferentiableOn.diffContOnCl
      rw [closure_ball y hr0.ne']
      exact (hF i).mono (hsub y hy)
    · intro w hw
      exact hb i w (hsub y hy (sphere_subset_closedBall hw))
  have hdiff : ∀ i, ∀ y ∈ ball z r, DifferentiableAt ℂ (F i) y := by
    intro i y hy
    exact (hF i).differentiableAt (hU.mem_nhds (hsub y hy (mem_closedBall_self hr0.le)))
  rw [Metric.equicontinuousAt_iff]
  intro e he
  refine ⟨min r (e * r / 2), by positivity, fun y hy i => ?_⟩
  rw [dist_comm, dist_eq_norm]
  calc ‖F i y - F i z‖ ≤ 1 / r * ‖y - z‖ := (fun i y hy =>
    (convex_ball z r).norm_image_sub_le_of_norm_deriv_le (hdiff i) (hderiv i)
      (mem_ball_self hr0) hy) i y (mem_ball.2 (lt_of_lt_of_le hy (min_le_left _ _)))
    _ ≤ 1 / r * (e * r / 2) := by
        gcongr; rw [← dist_eq_norm]; grind
    _ = e / 2 := by field_simp
    _ < e := by linarith

/-- **Montel's theorem.** A family of holomorphic functions on an open set `U`, bounded by `1`
on `U`, converges locally uniformly on `U` along any ultrafilter. -/
theorem montel (l : Ultrafilter ι) {F : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hb : ∀ i, ∀ z ∈ U, ‖F i z‖ ≤ 1) :
    ∃ f : ℂ → ℂ, TendstoLocallyUniformlyOn F f l U := by
  have hpt : ∀ z, ∃ w, z ∈ U → Tendsto (fun i => F i z) l (𝓝 w) := by
    intro z
    by_cases hz : z ∈ U
    · obtain ⟨w, -, hw⟩ := (isCompact_closedBall 0 1).ultrafilter_le_nhds
        (l.map (fun i => F i z)) (by
          refine tendsto_principal.2 (Eventually.of_forall fun i => ?_)
          simp_all )
      exact ⟨w, fun _ => by assumption⟩
    simp_all
  choose f hf using hpt
  refine ⟨f, ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  have heq : ∀ K' ∈ ({K} : Set (Set ℂ)), EquicontinuousOn F K' := by
    rintro K' rfl x hx
    exact (equicontinuousAt_of_norm_le_one hU hF hb (hKU hx)).equicontinuousWithinAt _
  have key := (EquicontinuousOn.tendsto_uniformOnFun_iff_pi' 
    (by grind) heq l f).2 (by
      rw [tendsto_pi_nhds]
      grind)
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at key
  exact key K rfl

end

section

/-! ## Hurwitz's theorem -/

open Complex Metric Filter Topology Set

variable {ι : Type*} {l : Filter ι}

/-- Local Hurwitz theorem for nonvanishing functions. -/
theorem hurwitz_ne_zero [l.NeBot] {F : ι → ℂ → ℂ} {g : ℂ → ℂ}
    {a : ℂ} {r : ℝ} (hr : 0 < r) (hF : ∀ i, DifferentiableOn ℂ (F i) (closedBall a r))
    (hF0 : ∀ i, ∀ z ∈ closedBall a r, F i z ≠ 0)
    (hconv : TendstoUniformlyOn F g l (closedBall a r))
    (hg : ContinuousOn g (sphere a r)) (hg0 : ∀ z ∈ sphere a r, g z ≠ 0) : g a ≠ 0 := by
  obtain ⟨z1, hz1, hmin⟩ := (isCompact_sphere a r).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 hr.le) hg.norm
  set m := ‖g z1‖ with hm
  have hm0  := norm_pos_iff.2 (hg0 z1 hz1)
  rw [Metric.tendstoUniformlyOn_iff] at hconv
  obtain ⟨i, hi⟩ := (hconv (m / 2) (by positivity)).exists
  have hd : DiffContOnCl ℂ (fun z => (F i z)⁻¹) (ball a r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball a hr.ne']
    exact (hF i).inv (hF0 i)
  have hFa  :=
    norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd
      (by rw [frontier_ball a hr.ne']; exact (by
    intro z hz
    have h1  := hmin hz
    have h2 : ‖g z - F i z‖ < m / 2 := by
      simp_all [← dist_eq_norm]
    rw [norm_inv]
    calc ‖F i z‖⁻¹ ≤ (m / 2)⁻¹ := inv_anti₀ (by positivity) (by
      have := norm_sub_norm_le (g z) (g z - F i z)
      grind)
      _ = 2 / m := by grind)) (subset_closure (mem_ball_self hr))
  have hFa' : m / 2 ≤ ‖F i a‖ := by
    rw [norm_inv] at hFa
    rw [inv_le_comm₀ (norm_pos_iff.2 (hF0 i a (mem_closedBall_self hr.le))) (by positivity), inv_div] at hFa
    exact hFa
  have hga : ‖g a - F i a‖ < m / 2 := by
    rw [← dist_eq_norm]; exact hi a (mem_closedBall_self hr.le)
  intro h0
  rw [h0, zero_sub, norm_neg] at hga
  linarith

/-- **Hurwitz's theorem.** A locally uniform limit of injective holomorphic functions on a
connected open set, whose derivative does not vanish at some point, is injective. -/
theorem hurwitz_injOn [l.NeBot] {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hinj : ∀ i, InjOn (F i) U)
    (hconv : TendstoLocallyUniformlyOn F f l U) {z0 : ℂ} (hz0 : z0 ∈ U)
    (hd : deriv f z0 ≠ 0) : InjOn f U := by
  intro a ha b hb hab
  by_contra hne
  have hfd  :=
    hconv.differentiableOn (Eventually.of_forall hF) hU
  set g : ℂ → ℂ := fun z => f z - f b with hg
  have hgan : AnalyticOnNhd ℂ g U := fun z hz => (hfd.analyticOnNhd hU z hz).sub analyticAt_const
  have hev  :=
    ((hgan a ha).eventually_eq_zero_or_eventually_ne_zero).resolve_left (by
    intro hev
    have hloc : f =ᶠ[𝓝 z0] fun _ => f b := by
      filter_upwards [hU.mem_nhds hz0] with z hz
      have := hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc ha hev hz
      simp_all [sub_eq_zero]
    simp_all [hloc.deriv_eq])
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1
    (inter_mem (inter_mem hev (hU.mem_nhds ha)) (isOpen_compl_singleton.mem_nhds hne))
  set r := ε / 2 with hr
  have hr0 : 0 < r := by positivity
  have hcb : closedBall a r ⊆ ball a ε := closedBall_subset_ball (by linarith)
  have hcbU : closedBall a r ⊆ U := fun z hz => (hεsub (hcb hz)).1.2
  exact hurwitz_ne_zero hr0  
    (fun i => ((hF i).mono hcbU).sub_const _)
    (fun i z hz h => (fun z hz => (hεsub (hcb hz)).2) z hz (hinj i (hcbU hz) hb (sub_eq_zero.1 h)))
    (((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv _ hcbU (isCompact_closedBall a r)).sub ((hconv.tendsto_at hb).tendstoUniformlyOn_const _)) ((hfd.mono hcbU).continuousOn.sub continuousOn_const |>.mono
      sphere_subset_closedBall)
    (fun z hz => (fun z hz => (hεsub (hcb hz)).1.1) z (sphere_subset_closedBall hz) (by
      rintro rfl
      rw [mem_sphere, dist_self] at hz
      grind)) (by simp_all)

end

section

/-! ## The Riemann mapping theorem -/

open Complex Metric Filter Topology Set

variable {Ω : Set ℂ} {c : ℂ}

/-- Open mapping theorem for injective holomorphic maps on a connected open set. -/
lemma isOpen_image_of_injOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) {s : Set ℂ} (hs : s ⊆ U)
    (hso : IsOpen s) : IsOpen (f '' s) := by
  rcases (hf.analyticOnNhd hU).is_constant_or_isOpen hUc with ⟨w, hw⟩ | h
  · rcases s.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
    · simp
    · obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z (hs hz)
      have hmem : z + (ε / 2 : ℝ) ∈ ball z ε := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
        linarith
      have := hinj (hεU hmem) (hs hz) ((hw _ (hεU hmem)).trans (hw z (hs hz)).symm)
      simp_all
  grind

/-- The admissible family: injective holomorphic maps `Ω → 𝔻` sending `z₀` to `0`. -/
def Admissible (Ω : Set ℂ) (z₀ : ℂ) (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f Ω ∧ InjOn f Ω ∧ MapsTo f Ω (ball 0 1) ∧ f z₀ = 0

/-- The admissible family is nonempty (square-root trick). -/
lemma exists_admissible (hΩ : IsOpen Ω) [SimplyConnectedSpace Ω]
    (hne : Ω ≠ univ) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) : ∃ f, Admissible Ω z₀ f := by
  obtain ⟨a, ha⟩ : ∃ a, a ∉ Ω := by
    grind
  obtain ⟨g, hgd, hgsq⟩ := exists_sqrt_of_simplyConnected hΩ
     (differentiableOn_id.sub_const a) fun z hz h => ha (sub_eq_zero.1 h ▸ hz)
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 (isOpen_image_of_injOn hΩ (isPreconnected_iff_preconnectedSpace.2 inferInstance) hgd (by
    intro z hz w hw h
    grind) subset_rfl hΩ) (g z₀) ⟨z₀, hz₀, rfl⟩
  have hfar : ∀ z ∈ Ω, ρ ≤ ‖g z + g z₀‖ := by
    intro z hz
    by_contra hlt
    have : -g z ∈ ball (g z₀) ρ := by
      rw [mem_ball, dist_eq_norm, ← norm_neg]
      grind
    grind
  have hne0 : ∀ z ∈ Ω, g z + g z₀ ≠ 0 := fun z hz h => by
    grind
  have hinvle : ∀ z ∈ Ω, ‖(g z + g z₀)⁻¹‖ ≤ 1 / ρ := by
    intro z hz
    rw [norm_inv, one_div]
    exact inv_anti₀ hρ (hfar z hz)
  refine ⟨fun z => (ρ / 4 : ℝ) * ((g z + g z₀)⁻¹ - (g z₀ + g z₀)⁻¹), ?_, ?_, ?_, ?_⟩
  · fun_prop
  · intro z hz w hw h
    have hρ4 : ((ρ / 4 : ℝ) : ℂ) ≠ 0 := by
      have : ρ / 4 ≠ 0 := by positivity
      exact_mod_cast this
    grind
  · intro z hz
    rw [mem_ball_zero_iff, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc ρ / 4 * ‖(g z + g z₀)⁻¹ - (g z₀ + g z₀)⁻¹‖
        ≤ ρ / 4 * (‖(g z + g z₀)⁻¹‖ + ‖(g z₀ + g z₀)⁻¹‖) := by
          gcongr; exact norm_sub_le _ _
      _ ≤ ρ / 4 * (1 / ρ + 1 / ρ) := by
          gcongr
          all_goals grind
      _ = 1 / 2 := by field_simp; ring
      _ < 1 := by norm_num
  · simp

/-- Cauchy estimate for admissible maps. -/
lemma norm_deriv_le_of_admissible {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : closedBall z₀ r ⊆ Ω) {f : ℂ → ℂ} (hf : Admissible Ω z₀ f) :
    ‖deriv f z₀‖ ≤ 1 / r := by
  apply norm_deriv_le_of_forall_mem_sphere_norm_le hr
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball z₀ hr.ne']
    exact hf.1.mono hsub
  · intro w hw
    exact (mem_ball_zero_iff.1 (hf.2.2.1 (hsub (sphere_subset_closedBall hw)))).le

/-- Existence of an extremal admissible map (Montel + Hurwitz). -/
lemma exists_extremal (hΩ : IsOpen Ω) [SimplyConnectedSpace Ω]
    (hne : Ω ≠ univ) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ f, Admissible Ω z₀ f ∧ ∀ g, Admissible Ω z₀ g → ‖deriv g z₀‖ ≤ ‖deriv f z₀‖ := by
  have hUc : IsPreconnected Ω := isPreconnected_iff_preconnectedSpace.2 inferInstance
  obtain ⟨r, hr, hrsub⟩ : ∃ r > 0, closedBall z₀ r ⊆ Ω := by
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 hΩ z₀ hz₀
    exact ⟨ε / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hεsub⟩
  set S : Set ℝ := {t | ∃ g, Admissible Ω z₀ g ∧ ‖deriv g z₀‖ = t} with hS
  obtain ⟨f₁, hf₁⟩ := exists_admissible hΩ hne hz₀
  have hSne : S.Nonempty := ⟨_, f₁, hf₁, rfl⟩
  have hSbdd : BddAbove S := ⟨1 / r, by
    rintro t ⟨g, hg, rfl⟩
    exact norm_deriv_le_of_admissible hr hrsub hg⟩
  have hMpos : 0 < sSup S := by
    have h1  := le_csSup hSbdd ⟨f₁, hf₁, rfl⟩
    have h2  :=
      norm_pos_iff.2 (deriv_ne_zero_of_injOn hΩ hf₁.1 hf₁.2.1 hz₀)
    linarith
  obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sSup hSne hSbdd
  choose F hF hFu using huS
  set l : Ultrafilter ℕ := Ultrafilter.of atTop
  obtain ⟨f, hconv⟩ := montel l hΩ (fun n => (hF n).1)
    (fun n z hz => (mem_ball_zero_iff.1 ((hF n).2.2.1 hz)).le)
  have hfd  :=
    hconv.differentiableOn (Eventually.of_forall fun n => (hF n).1) hΩ
  have hnorm : ‖deriv f z₀‖ = sSup S := by
    have h2 : Tendsto (fun n => ‖deriv (F n) z₀‖) l (𝓝 (sSup S)) := by
      simp_rw [hFu]; exact hu.mono_left (Ultrafilter.of_le _)
    exact tendsto_nhds_unique ((hconv.deriv (Eventually.of_forall fun n => (hF n).1) hΩ).tendsto_at hz₀).norm h2
  have hfinj  :=
    hurwitz_injOn hΩ hUc (fun n => (hF n).1) (fun n => (hF n).2.1) hconv hz₀ (by
    intro h; simp_all )
  have hfle : ∀ z ∈ Ω, ‖f z‖ ≤ 1 := by
    intro z hz
    exact le_of_tendsto' (hconv.tendsto_at hz).norm fun n => (mem_ball_zero_iff.1 ((hF n).2.2.1 hz)).le
  refine ⟨f, ⟨hfd, hfinj, by
    have := (isOpen_image_of_injOn hΩ hUc hfd hfinj subset_rfl hΩ).subset_interior_iff.2 (by
      rintro _ ⟨z, hz, rfl⟩; exact mem_closedBall_zero_iff.2 (hfle z hz))
    rw [interior_closedBall 0 one_ne_zero] at this
    exact fun z hz => this ⟨z, hz, rfl⟩, by
    have h1  := hconv.tendsto_at hz₀
    simp_all [(hF _).2.2.2]⟩, fun g hg => ?_⟩
  rw [hnorm]
  exact le_csSup hSbdd ⟨g, hg, rfl⟩

/-- The derivative at `0` of `ζ ↦ mob (-w) ((mob (-c) ζ)²)` when `w = -c²`. -/
lemma hasDerivAt_psi (hc : ‖c‖ < 1) :
    HasDerivAt (fun ζ => mob (-(-c ^ 2)) (mob (-c) ζ ^ 2))
      (2 * c / (1 + (starRingEnd ℂ) c * c)) 0 := by
  have hw : ‖-(-c ^ 2)‖ < 1 := by
    simp_all 
  have h2 : HasDerivAt (fun ζ => ζ ^ 2) (2 * mob (-c) 0) (mob (-c) 0) := by
    simpa using hasDerivAt_pow 2 (mob (-c) 0)
  have := (hasDerivAt_mob hw  (by simp_all )).comp 0 (h2.comp 0 (hasDerivAt_mob (by simp_all)  (by simp)))
  simp only [Function.comp_def] at this
  convert this using 1
  simp 
  have hden3 : 1 - (starRingEnd ℂ) c ^ 2 * c ^ 2 ≠ 0 := by
    have : 1 - (starRingEnd ℂ) c ^ 2 * c ^ 2 =
        (1 - (starRingEnd ℂ) c * c) * (1 + (starRingEnd ℂ) c * c) := by ring
    rw [this]; exact mul_ne_zero (by
    have := mob_denom_ne_zero hc hc
    exact this) (by
    rw [conj_mul']
    have : 0 ≤ ‖c‖ ^ 2 := by positivity
    intro h
    have : 1 + ‖c‖ ^ 2 = 0 := by exact_mod_cast h
    linarith)
  grind

/-- `|2c / (1 + |c|²)| < 1` for `|c| < 1`. -/
lemma norm_psi_deriv_lt_one (hc : ‖c‖ < 1) :
    ‖2 * c / (1 + (starRingEnd ℂ) c * c)‖ < 1 := by
  rw [conj_mul']
  have h1 : (1 + (‖c‖ : ℂ) ^ 2) = (1 + ‖c‖ ^ 2 : ℝ) := by push_cast; ring
  rw [h1, norm_div, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
    div_lt_one (by positivity)]
  simp 
  nlinarith 

/-- An extremal admissible map is onto the unit disk. -/
lemma surjOn_of_extremal (hΩ : IsOpen Ω) [SimplyConnectedSpace Ω] {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) {f : ℂ → ℂ} (hf : Admissible Ω z₀ f)
    (hmax : ∀ g, Admissible Ω z₀ g → ‖deriv g z₀‖ ≤ ‖deriv f z₀‖) :
    SurjOn f Ω (ball 0 1) := by
  intro w hw
  by_contra hnot
  have hw1  := mem_ball_zero_iff.1 hw
  obtain ⟨hfd, hfinj, hfmaps, hfz₀⟩ := hf
  have hfn : ∀ z ∈ Ω, ‖f z‖ < 1 := fun z hz => mem_ball_zero_iff.1 (hfmaps hz)
  -- `h = mob w ∘ f` does not vanish
  set h : ℂ → ℂ := fun z => mob w (f z) with hh
  have hhd : DifferentiableOn ℂ h Ω := fun z hz =>
    (differentiableAt_mob hw1 (hfn z hz)).comp_differentiableWithinAt z (hfd z hz)
  obtain ⟨s, hsd, hssq⟩ := exists_sqrt_of_simplyConnected hΩ hhd (by
    intro z hz h0
    simp_all [mob_eq_zero_iff hw1 (hfn z hz)])
  have hsn : ∀ z ∈ Ω, ‖s z‖ < 1 := by
    intro z hz
    have h1 : ‖s z‖ ^ 2 < 1 := by
      rw [← norm_pow, hssq z hz]; exact norm_mob_lt_one hw1 (hfn z hz)
    nlinarith 
  have hsinj : InjOn s Ω := by
    intro z hz z' hz' hzz
    have : h z = h z' := by grind
    exact hfinj hz hz' (mob_injOn hw1 (mem_ball_zero_iff.2 (hfn z hz))
      (mem_ball_zero_iff.2 (hfn z' hz')) this)
  set c := s z₀ with hc
  have hcn  := hsn z₀ hz₀
  have hc2 : c ^ 2 = -w := by
    simp_all 
  have hwc : w = -c ^ 2 := by grind
  -- the competitor `F = mob c ∘ s`
  set F : ℂ → ℂ := fun z => mob c (s z) with hF
  have hFadm : Admissible Ω z₀ F := by
    refine ⟨fun z hz => (differentiableAt_mob hcn (hsn z hz)).comp_differentiableWithinAt z
      (hsd z hz), ?_, fun z hz => mob_mem_ball (mem_ball_zero_iff.2 hcn)
      (mem_ball_zero_iff.2 (hsn z hz)), by simp [hF, hc]⟩
    intro z hz z' hz' hzz
    exact hsinj hz hz' (mob_injOn hcn (mem_ball_zero_iff.2 (hsn z hz))
      (mem_ball_zero_iff.2 (hsn z' hz')) hzz)
  -- `f = Ψ ∘ F` on `Ω`
  set Ψ : ℂ → ℂ := fun ζ => mob (-(-c ^ 2)) (mob (-c) ζ ^ 2) with hΨ
  have hfΨ : ∀ z ∈ Ω, f z = Ψ (F z) := by
    intro z hz
    simp only [hΨ]
    rw [mob_neg_mob hcn (hsn z hz), hssq z hz, ← hwc, mob_neg_mob hw1 (hfn z hz)]
  have hΨd := hasDerivAt_psi hcn
  rw [← hFadm.2.2.2] at hΨd
  have hfeq : f =ᶠ[𝓝 z₀] Ψ ∘ F := by
    filter_upwards [hΩ.mem_nhds hz₀] with z hz using hfΨ z hz
  have hdf : deriv f z₀ = 2 * c / (1 + (starRingEnd ℂ) c * c) * deriv F z₀ := by
    rw [hfeq.deriv_eq, (hΨd.comp z₀ (hFadm.1.differentiableAt (hΩ.mem_nhds hz₀)).hasDerivAt).deriv]
  have hFd0 : deriv F z₀ ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hdf; exact deriv_ne_zero_of_injOn hΩ hfd hfinj hz₀ hdf
  have hlt : ‖deriv f z₀‖ < ‖deriv F z₀‖ := by
    rw [hdf, norm_mul]
    have := norm_psi_deriv_lt_one hcn
    have hpos  := norm_pos_iff.2 hFd0
    nlinarith
  grind

/-- Inverse of a bijective holomorphic map onto the disk. -/
lemma exists_inverse (hΩ : IsOpen Ω) (hUc : IsPreconnected Ω) {f : ℂ → ℂ}
    (hfd : DifferentiableOn ℂ f Ω) (hfinj : InjOn f Ω) (hmaps : MapsTo f Ω (ball 0 1))
    (hsurj : SurjOn f Ω (ball 0 1)) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball 0 1) ∧ InjOn G (ball 0 1) ∧
      G '' ball 0 1 = Ω := by
  classical
  set G := Function.invFunOn f Ω with hG
  have hGmem : ∀ w ∈ ball 0 1, G w ∈ Ω ∧ f (G w) = w := fun w hw =>
    Function.invFunOn_pos (hsurj hw)
  have hGf : ∀ z ∈ Ω, G (f z) = z := fun z hz =>
    hfinj (hGmem _ (hmaps hz)).1 hz (hGmem _ (hmaps hz)).2
  refine ⟨G, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨hGw, hfGw⟩ := hGmem w hw
    exact ((hfd.differentiableAt (hΩ.mem_nhds hGw)).hasDerivAt.of_local_left_inverse (by
      rw [ContinuousAt, (nhds_basis_opens (G w)).tendsto_right_iff]
      rintro V ⟨hV, hVo⟩
      filter_upwards [(isOpen_image_of_injOn hΩ hUc hfd hfinj inter_subset_right (hVo.inter hΩ)).mem_nhds ⟨G w, ⟨hV, hGw⟩, hfGw⟩] with y hy
      grind) (deriv_ne_zero_of_injOn hΩ hfd hfinj hGw) (by
      filter_upwards [isOpen_ball.mem_nhds hw] with y hy using (hGmem y hy).2)).differentiableAt.differentiableWithinAt
  · intro w hw w' hw' h
    grind
  · ext z
    constructor
    · grind
    · intro hz; exact ⟨f z, hmaps hz, hGf z hz⟩

/-- **Riemann mapping theorem.** Every simply connected open subset `Ω ≠ ℂ` of the plane is
the image of the open unit disk under an injective holomorphic map. (Simple connectivity
includes nonemptiness.) -/
theorem riemann_mapping_theorem (Ω : Set ℂ) (hopen : IsOpen Ω) [SimplyConnectedSpace Ω]
    (hne : Ω ≠ univ) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball 0 1) ∧ InjOn G (ball 0 1) ∧
      G '' ball 0 1 = Ω := by
  obtain ⟨⟨z₀, hz₀⟩⟩ : Nonempty Ω := inferInstance
  obtain ⟨f, hf, hmax⟩ := exists_extremal hopen hne hz₀
  exact exists_inverse hopen (isPreconnected_iff_preconnectedSpace.2 inferInstance) hf.1 hf.2.1 hf.2.2.1 (surjOn_of_extremal hopen hz₀ hf hmax)

end

section

open Complex Metric Filter Topology Set

/-- An injective holomorphic map on a connected open set has a holomorphic inverse on its
(open) image. -/
lemma exists_holomorphic_inverse {D : Set ℂ} (hD : IsOpen D) (hDc : IsPreconnected D)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) (hinj : InjOn f D) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (f '' D) ∧ MapsTo g (f '' D) D ∧
      (∀ z ∈ D, g (f z) = z) ∧ ∀ w ∈ f '' D, f (g w) = w := by
  classical
  set g := Function.invFunOn f D with hg
  have hgmem : ∀ w ∈ f '' D, g w ∈ D ∧ f (g w) = w := fun w hw => Function.invFunOn_pos hw
  have hgf : ∀ z ∈ D, g (f z) = z := fun z hz =>
    hinj (hgmem _ (mem_image_of_mem f hz)).1 hz (hgmem _ (mem_image_of_mem f hz)).2
  refine ⟨g, ?_, fun w hw => (hgmem w hw).1, hgf, fun w hw => (hgmem w hw).2⟩
  intro w hw
  obtain ⟨hgw, hfgw⟩ := hgmem w hw
  exact ((hf.differentiableAt (hD.mem_nhds hgw)).hasDerivAt.of_local_left_inverse (by
    rw [ContinuousAt, (nhds_basis_opens (g w)).tendsto_right_iff]
    rintro V ⟨hV, hVo⟩
    filter_upwards [(isOpen_image_of_injOn hD hDc hf hinj inter_subset_right (hVo.inter hD)).mem_nhds ⟨g w, ⟨hV, hgw⟩, hfgw⟩] with y hy
    grind) (deriv_ne_zero_of_injOn hD hf hinj hgw) (by
    filter_upwards [(isOpen_image_of_injOn hD hDc hf hinj subset_rfl hD).mem_nhds hw] with y hy using (hgmem y hy).2)).differentiableAt.differentiableWithinAt

end

end PolyaNeumann.RiemannInterior

namespace PolyaNeumann

open Set Metric

/-- Every bounded simply connected open planar domain has an actual
injective holomorphic parametrization by the open unit disk. -/
theorem exists_interior_conformal_map (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hsc : SimplyConnectedSpace Ω) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball 0 1) ∧
      Set.InjOn F (Metric.ball 0 1) ∧ F '' Metric.ball 0 1 = Ω := RiemannInterior.riemann_mapping_theorem Ω hopen (by
    rintro rfl
    exact (NormedSpace.unbounded_univ ℝ ℂ) hb)

end PolyaNeumann
