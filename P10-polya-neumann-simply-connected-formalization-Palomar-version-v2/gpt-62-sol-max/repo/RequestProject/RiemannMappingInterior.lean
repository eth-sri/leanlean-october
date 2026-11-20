module

public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.RemovableSingularity
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

open Complex Metric Filter Topology Set Function

private theorem not_eventually_constant_of_injOn {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hU : U ∈ 𝓝 z) (hinj : InjOn f U) : ¬ (∀ᶠ w in 𝓝 z, f w = f z) := by
  intro h
  have he : ∀ᶠ w in 𝓝[≠] z, False := by
    filter_upwards [nhdsWithin_le_nhds hU, nhdsWithin_le_nhds h, self_mem_nhdsWithin] with w hw heq hne
    exact hne (hinj hw (mem_of_mem_nhds hU) heq)
  exact he.exists.choose_spec

private theorem map_nhds_eq_of_injOn {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) (hz : z ∈ U) :
    map f (𝓝 z) = 𝓝 (f z) := by
  have han := hf.analyticOnNhd hU z hz
  exact le_antisymm han.continuousAt
    (han.eventually_constant_or_nhds_le_map_nhds.resolve_left
      (not_eventually_constant_of_injOn (hU.mem_nhds hz) hinj))

/-- An injective holomorphic map on an open set is open. -/
lemma isOpen_image_of_injOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) {s : Set ℂ} (hs : s ⊆ U)
    (hso : IsOpen s) : IsOpen (f '' s) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, hz, rfl⟩
  rw [← map_nhds_eq_of_injOn hU hf hinj (hs hz)]
  exact image_mem_map (hso.mem_nhds hz)

/-- The inverse is holomorphic off the isolated critical values, which are removable. -/
lemma exists_holomorphic_inverse {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) (hinj : InjOn f D) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (f '' D) ∧ MapsTo g (f '' D) D ∧
      (∀ z ∈ D, g (f z) = z) ∧ ∀ w ∈ f '' D, f (g w) = w := by
  let g := invFunOn f D
  have hm : MapsTo g (f '' D) D := fun _ => invFunOn_mem
  have hr : RightInvOn g f (f '' D) := fun _ => invFunOn_eq
  have hl := hinj.leftInvOn_invFunOn
  have ho := isOpen_image_of_injOn hD hf hinj subset_rfl hD
  have hc (w : ℂ) (hw : w ∈ f '' D) : ContinuousAt g w := by
    have he := eventually_of_mem (hD.mem_nhds (hm hw)) fun _ hz => hl hz
    refine le_of_eq ?_
    calc
      map g (𝓝 w) = map (g ∘ f) (𝓝 (g w)) := by
        rw [← map_map, map_nhds_eq_of_injOn hD hf hinj (hm hw), hr hw]
      _ = 𝓝 (g w) := (map_congr he).trans map_id
  have hd (w : ℂ) (hw : w ∈ f '' D) (hn : deriv f (g w) ≠ 0) :=
    (HasDerivAt.of_local_left_inverse (hc w hw)
      (hf.differentiableAt (hD.mem_nhds (hm hw))).hasDerivAt hn
      (eventually_of_mem (ho.mem_nhds hw) fun _ hy => hr hy)).differentiableAt
  refine ⟨g, fun w hw => DifferentiableAt.differentiableWithinAt ?_, hm, fun _ hz => hl hz, fun _ hw => hr hw⟩
  have hn : ¬ (∀ᶠ z in 𝓝 (g w), deriv f z = 0) := by
    intro he
    obtain ⟨r, hr₀, hs⟩ := Metric.mem_nhds_iff.1 (inter_mem (hD.mem_nhds (hm hw)) he)
    have hd' : ball (g w) r ⊆ D := fun _ hz => (hs hz).1
    apply not_eventually_constant_of_injOn (hD.mem_nhds (hm hw)) hinj
    filter_upwards [ball_mem_nhds (g w) hr₀] with z hz
    exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected
      (hf.mono hd') (fun _ hz' => (hs hz').2) hz (mem_ball_self hr₀)
  have he := ((hf.analyticOnNhd hD _ (hm hw)).deriv.eventually_eq_zero_or_eventually_ne_zero).resolve_left hn
  refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ (hc w hw)).differentiableAt
  rw [eventually_nhdsWithin_iff] at he ⊢
  filter_upwards [(hc w hw).eventually he, ho.mem_nhds hw] with y hy hyD hyw
  exact hd y hyD (hy fun h => hyw ((hr hyD).symm.trans ((congrArg f h).trans (hr hw))))

/-- An injective holomorphic map has a nonzero derivative. -/
theorem deriv_ne_zero_of_injOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) {a : ℂ} (ha : a ∈ U) :
    deriv f a ≠ 0 := by
  obtain ⟨g, hg, -, hl, hr⟩ := exists_holomorphic_inverse hU hf hinj
  have hn := (isOpen_image_of_injOn hU hf hinj subset_rfl hU).mem_nhds (mem_image_of_mem f ha)
  intro h
  have hd : HasDerivAt f 0 (g (f a)) := by
    rw [hl a ha, ← h]
    exact (hf.differentiableAt (hU.mem_nhds ha)).hasDerivAt
  exact not_differentiableAt_of_local_left_inverse_hasDerivAt_zero hd (eventually_of_mem hn hr)
    (hg.differentiableAt hn)

end

section

/-! ## Disk automorphisms `z ↦ (z - a) / (1 - ā z)` -/

open Complex Metric

/-- The disk automorphism `mob a z = (z - a) / (1 - ā z)`. -/
def mob (a z : ℂ) : ℂ := (z - a) / (1 - (starRingEnd ℂ) a * z)

lemma mob_denom_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 - (starRingEnd ℂ) a * z ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have hn : ‖(starRingEnd ℂ) a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg a) ha hz.le
  simpa [← h] using hn

/-- The key identity `|1 - ā z|² - |z - a|² = (1 - |a|²)(1 - |z|²)`. -/
lemma normSq_identity (a z : ℂ) :
    normSq (1 - (starRingEnd ℂ) a * z) - normSq (z - a) =
      (1 - normSq a) * (1 - normSq z) := by grind [normSq_apply, sub_re, sub_im, mul_re, mul_im, conj_re, conj_im, one_re, one_im]

lemma norm_mob_lt_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : ‖mob a z‖ < 1 := by
  have hd := mob_denom_ne_zero ha hz
  unfold mob
  rw [norm_div, div_lt_one (norm_pos_iff.2 hd)]
  have hid := normSq_identity a z
  have ha2 : normSq a < 1 := by
    simp_all [normSq_eq_norm_sq]
  have hz2 : normSq z < 1 := by
    simp_all [normSq_eq_norm_sq]
  have : normSq (z - a) < normSq (1 - (starRingEnd ℂ) a * z) := by
    nlinarith
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at this
  nlinarith [norm_nonneg (z - a), norm_nonneg (1 - (starRingEnd ℂ) a * z)]

lemma mob_mem_ball {a z : ℂ} (ha : a ∈ ball (0 : ℂ) 1) (hz : z ∈ ball (0 : ℂ) 1) :
    mob a z ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff] at *
  exact norm_mob_lt_one ha hz

@[simp] lemma mob_self (a : ℂ) : mob a a = 0 := by simp [mob]

@[simp] lemma mob_zero (a : ℂ) : mob a 0 = -a := by simp [mob]

lemma mob_neg_mob {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : mob (-a) (mob a z) = z := by
  have hd := mob_denom_ne_zero ha hz
  have hna := mob_denom_ne_zero ha ha
  unfold mob
  grind

lemma mob_injOn {a : ℂ} (ha : ‖a‖ < 1) : Set.InjOn (mob a) (ball 0 1) := by
  intro z hz w hw h
  rw [mem_ball_zero_iff] at hz hw
  rw [← mob_neg_mob ha hz, ← mob_neg_mob ha hw, h]

section

variable {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1)
include a z ha hz

lemma hasDerivAt_mob  :
    HasDerivAt (mob a) ((1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z) ^ 2) z := by
  have hd := mob_denom_ne_zero ha hz
  have h1 : HasDerivAt (fun w => w - a) 1 z := (hasDerivAt_id z).sub_const a
  have h2 : HasDerivAt (fun w => 1 - (starRingEnd ℂ) a * w) (-(starRingEnd ℂ) a) z := by
    simpa using ((hasDerivAt_id z).const_mul ((starRingEnd ℂ) a)).const_sub 1
  have := h1.div h2 hd
  simp only [Pi.div_def] at this
  convert this using 1
  rfl
  ring

lemma differentiableAt_mob  :
    DifferentiableAt ℂ (mob a) z := (hasDerivAt_mob ha hz).differentiableAt

lemma mob_eq_zero_iff  : mob a z = 0 ↔ z = a := by
  simp [mob, mob_denom_ne_zero ha hz, sub_eq_zero]

end

end

section

/-! ## Holomorphic square roots on simply connected domains -/

open Complex Metric Filter Topology Set

/-- A nonvanishing holomorphic function on a simply connected open set has a holomorphic
square root. -/
theorem exists_sqrt_of_simplyConnected {Ω : Set ℂ} (hΩ : IsOpen Ω) [SimplyConnectedSpace Ω]
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) (hf0 : ∀ z ∈ Ω, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ Ω, g z ^ 2 = f z := by
  obtain ⟨g, hc, hs⟩ := exists_continuousOn_pow_eq (show IsSimplyConnected Ω from ‹SimplyConnectedSpace Ω›)
    hΩ hf.continuousOn (show 0 ∉ f '' Ω from by grind) two_ne_zero
  refine ⟨g, ?_, fun z _ => hs z⟩
  intro z hz
  have hn := hΩ.mem_nhds hz
  have hg : g z ≠ 0 := by grind
  have hd : HasDerivAt (· ^ 2) (2 * g z) (g z) := by
    simpa using hasDerivAt_pow 2 (g z)
  exact (HasDerivAt.of_comp_left (hc.continuousAt hn) hd (hf.differentiableAt hn).hasDerivAt
    (mul_ne_zero two_ne_zero hg) (.of_forall hs)).differentiableAt.differentiableWithinAt

end

section

/-! ## Montel's theorem -/

open Complex Metric Filter Topology Set

private lemma diffContOnCl_ball {f : ℂ → ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (closedBall z r)) : DiffContOnCl ℂ f (ball z r) :=
  (closure_ball z hr.ne' ▸ hf).diffContOnCl

private lemma norm_deriv_le_of_bounded {f : ℂ → ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (closedBall z r)) (hb : ∀ w ∈ closedBall z r, ‖f w‖ ≤ 1) :
    ‖deriv f z‖ ≤ 1 / r :=
  norm_deriv_le_of_forall_mem_sphere_norm_le hr (diffContOnCl_ball hr hf)
    (fun w hw => hb w (sphere_subset_closedBall hw))

/-- Cauchy estimate: a holomorphic family bounded by `1` on `U` is equicontinuous at every
point of `U`. -/
lemma equicontinuousAt_of_norm_le_one {ι : Type*} {F : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hb : ∀ i, ∀ z ∈ U, ‖F i z‖ ≤ 1) {z : ℂ}
    (hz : z ∈ U) : EquicontinuousAt F z := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z hz
  set r := ε / 3 with hr
  have hr0 : 0 < r := by positivity
  have hsub (y) (hy : y ∈ ball z r) : closedBall y r ⊆ U := by
    intro w hw
    apply hεU
    rw [mem_ball] at hy ⊢
    rw [mem_closedBall] at hw
    linarith [dist_triangle w y z]
  have hdiff (i y) (hy : y ∈ ball z r) :=
    (hF i).differentiableAt (hU.mem_nhds (hsub y hy (mem_closedBall_self hr0.le)))
  have hderiv (i y) (hy : y ∈ ball z r) :=
    norm_deriv_le_of_bounded hr0 ((hF i).mono (hsub y hy)) (fun w hw => hb i w (hsub y hy hw))
  refine equicontinuousAt_of_continuity_modulus (fun y => (1 / r) * dist y z) ?_ F ?_
  · simpa using (continuous_id.dist (continuous_const (y := z)) |>.const_mul (1 / r)).tendsto z
  · filter_upwards [ball_mem_nhds z hr0] with y hy i
    simpa only [dist_comm (F i z) _, dist_eq_norm] using
      (convex_ball z r).norm_image_sub_le_of_norm_deriv_le (hdiff i) (hderiv i) (mem_ball_self hr0) hy

/-- **Montel's theorem.** A family of holomorphic functions on an open set `U`, bounded by `1`
on `U`, converges locally uniformly on `U` along any ultrafilter. -/
theorem montel {ι : Type*} (l : Ultrafilter ι) {F : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hb : ∀ i, ∀ z ∈ U, ‖F i z‖ ≤ 1) :
    ∃ f : ℂ → ℂ, TendstoLocallyUniformlyOn F f (l : Filter ι) U := by
  have hpt : ∀ z, ∃ w, z ∈ U → Tendsto (fun i => F i z) (l : Filter ι) (𝓝 w) := by
    intro z
    by_cases hz : z ∈ U
    · obtain ⟨w, -, hw⟩ := (isCompact_closedBall (0 : ℂ) 1).ultrafilter_le_nhds
        (l.map (fun i => F i z)) (by
          rw [Ultrafilter.coe_map]
          refine tendsto_principal.2 (Eventually.of_forall fun i => ?_)
          simp_all)
      tauto
    simp_all
  choose f hf using hpt
  refine ⟨f, ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  have heq : ∀ K' ∈ ({K} : Set (Set ℂ)), EquicontinuousOn F K' := by
    rintro K' rfl x hx
    exact (equicontinuousAt_of_norm_le_one hU hF hb (hKU hx)).equicontinuousWithinAt _
  have key := (EquicontinuousOn.tendsto_uniformOnFun_iff_pi' (𝔖 := {K})
    (by simp_all) heq (l : Filter ι) f).2 (by grind [tendsto_pi_nhds, sUnion_singleton])
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at key
  tauto

end

section

/-! ## Hurwitz's theorem -/

open Complex Metric Filter Topology Set

/-- Local Hurwitz theorem for nonvanishing functions. -/
theorem hurwitz_ne_zero {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → ℂ → ℂ} {g : ℂ → ℂ}
    {a : ℂ} {r : ℝ} (hr : 0 < r) (hF : ∀ i, DifferentiableOn ℂ (F i) (closedBall a r))
    (hF0 : ∀ i, ∀ z ∈ closedBall a r, F i z ≠ 0)
    (hconv : TendstoUniformlyOn F g l (closedBall a r))
    (hg : ContinuousOn g (sphere a r)) (hg0 : ∀ z ∈ sphere a r, g z ≠ 0) : g a ≠ 0 := by
  obtain ⟨z1, hz1, hmin⟩ := (isCompact_sphere a r).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 hr.le) hg.norm
  let m := ‖g z1‖ / 2
  have hm : 0 < m := half_pos (norm_pos_iff.mpr (hg0 z1 hz1))
  obtain ⟨i, hi⟩ := (Metric.tendstoUniformlyOn_iff.mp hconv m hm).exists
  have hbd (z) (hz : z ∈ sphere a r) : ‖(F i z)⁻¹‖ ≤ m⁻¹ := by
    have hzi := hi z (sphere_subset_closedBall hz)
    have hzg : ‖g z1‖ ≤ ‖g z‖ := hmin hz
    rw [dist_eq_norm] at hzi
    have htriangle := norm_sub_norm_le (g z) (g z - F i z)
    rw [sub_sub_cancel] at htriangle
    rw [norm_inv]
    exact inv_anti₀ hm (by linarith [show m = ‖g z1‖ / 2 from rfl])
  have hFa := norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    (diffContOnCl_ball hr ((hF i).inv (hF0 i)))
    (by rwa [frontier_ball a hr.ne']) (subset_closure (mem_ball_self hr))
  have hFa' : m ≤ ‖F i a‖ := (inv_le_inv₀ (norm_pos_iff.mpr (hF0 i a (mem_closedBall_self hr.le)))
    hm).mp (by simpa using hFa)
  intro h0
  exact hFa'.not_gt (by simpa [dist_eq_norm, h0] using hi a (mem_closedBall_self hr.le))

/-- **Hurwitz's theorem.** A locally uniform limit of injective holomorphic functions on a
connected open set, whose derivative does not vanish at some point, is injective. -/
theorem hurwitz_injOn {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hinj : ∀ i, InjOn (F i) U)
    (hconv : TendstoLocallyUniformlyOn F f l U) {z0 : ℂ} (hz0 : z0 ∈ U)
    (hd : deriv f z0 ≠ 0) : InjOn f U := by
  intro a ha b hb hab
  by_contra hne
  have hfd :=
    hconv.differentiableOn (Eventually.of_forall hF) hU
  have han := hfd.analyticOnNhd hU
  set g : ℂ → ℂ := fun z => f z - f b with hg
  have hgan : AnalyticOnNhd ℂ g U := fun z hz => (han z hz).sub analyticAt_const
  have hnz : ¬ ∀ᶠ z in 𝓝 a, g z = 0 := by
    intro hev
    have hEq := hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc ha hev
    have hloc : f =ᶠ[𝓝 z0] fun _ => f b := by
      filter_upwards [hU.mem_nhds hz0] with z hz
      have := hEq hz
      simp  [hg, sub_eq_zero] at this
      assumption
    apply hd
    rw [hloc.deriv_eq]
    simp
  have hev :=
    ((hgan a ha).eventually_eq_zero_or_eventually_ne_zero).resolve_left hnz
  rw [eventually_nhdsWithin_iff] at hev
  have hbU := isOpen_compl_singleton.mem_nhds hne
  obtain ⟨r, hr0, hεsub⟩ := nhds_basis_closedBall.mem_iff.mp
    (inter_mem (inter_mem hev (hU.mem_nhds ha)) hbU)
  have hcbU : closedBall a r ⊆ U := fun z hz => (hεsub hz).1.2
  have hcbb : ∀ z ∈ closedBall a r, z ≠ b := fun z hz => (hεsub hz).2
  have hcbg : ∀ z ∈ closedBall a r, z ≠ a → g z ≠ 0 := fun z hz => (hεsub hz).1.1
  have hunif :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv _ hcbU (isCompact_closedBall a r)
  have hptb := hconv.tendsto_at hb
  have hconv' :=
    hunif.sub (hptb.tendstoUniformlyOn_const _)
  have key := hurwitz_ne_zero hr0 (F := fun i z => F i z - F i b) (g := g)
    (fun i => ((hF i).mono hcbU).sub_const _)
    (fun i z hz h => hcbb z hz (hinj i (hcbU hz) hb (sub_eq_zero.1 h)))
    hconv' ((hfd.mono hcbU).continuousOn.sub continuousOn_const |>.mono
      sphere_subset_closedBall)
    (fun z hz => hcbg z (sphere_subset_closedBall hz) (ne_of_mem_sphere hz hr0.ne'))
  exact key (by simp [hg, hab])

end

section

/-! ## The Riemann mapping theorem -/

open Complex Metric Filter Topology Set

/-- The admissible family: injective holomorphic maps `Ω → 𝔻` sending `z₀` to `0`. -/
def Admissible (Ω : Set ℂ) (z₀ : ℂ) (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f Ω ∧ InjOn f Ω ∧ MapsTo f Ω (ball 0 1) ∧ f z₀ = 0

/-- A sufficiently small affine map makes the admissible family nonempty. -/
lemma exists_admissible {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (z₀ : ℂ) :
    ∃ f, Admissible Ω z₀ f := by
  obtain ⟨C, hC, hbd⟩ := hb.exists_pos_norm_lt
  let M := C + ‖z₀‖
  have hM : 0 < M := by positivity
  have hm : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  refine ⟨fun z => (z - z₀) / (M : ℂ), (differentiableOn_id.sub_const _).div_const _,
    ?_, ?_, by simp⟩
  simp_all
  · intro z hz
    rw [mem_ball_zero_iff, norm_div, norm_real, Real.norm_of_nonneg hM.le, div_lt_one₀ hM]
    exact (norm_sub_le _ _).trans_lt (add_lt_add_left (hbd z hz) _)

/-- Existence of an extremal admissible map (Montel + Hurwitz). -/
lemma exists_extremal {Ω : Set ℂ} (hΩ : IsOpen Ω) [SimplyConnectedSpace Ω]
    (hb : Bornology.IsBounded Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ f, Admissible Ω z₀ f ∧ ∀ g, Admissible Ω z₀ g → ‖deriv g z₀‖ ≤ ‖deriv f z₀‖ := by
  have hUc : IsPreconnected Ω := isPreconnected_iff_preconnectedSpace.2 inferInstance
  obtain ⟨r, hr, hrsub⟩ := nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hz₀)
  set S : Set ℝ := {t | ∃ g, Admissible Ω z₀ g ∧ ‖deriv g z₀‖ = t} with hS
  obtain ⟨f₁, hf₁⟩ := exists_admissible hb z₀
  have hSne : S.Nonempty := ⟨_, f₁, hf₁, rfl⟩
  have hSbdd : BddAbove S := ⟨1 / r, by
    rintro t ⟨g, hg, rfl⟩
    exact norm_deriv_le_of_bounded hr (hg.1.mono hrsub)
      (fun w hw => (mem_ball_zero_iff.mp (hg.2.2.1 (hrsub hw))).le)⟩
  have hMpos := (norm_pos_iff.mpr (deriv_ne_zero_of_injOn hΩ hf₁.1 hf₁.2.1 hz₀)).trans_le
    (le_csSup hSbdd ⟨f₁, hf₁, rfl⟩)
  obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sSup hSne hSbdd
  choose F hF hFu using huS
  set l : Ultrafilter ℕ := Ultrafilter.of atTop
  have hl : (l : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨f, hconv⟩ := montel l hΩ (fun n => (hF n).1)
    (fun n z hz => (mem_ball_zero_iff.1 ((hF n).2.2.1 hz)).le)
  have hfd :=
    hconv.differentiableOn (Eventually.of_forall fun n => (hF n).1) hΩ
  have hderiv :=
    (hconv.deriv (Eventually.of_forall fun n => (hF n).1) hΩ).tendsto_at hz₀
  have hnorm : ‖deriv f z₀‖ = sSup S := by
    have h1 :=
      hderiv.norm
    have h2 : Tendsto (fun n => ‖deriv (F n) z₀‖) (l : Filter ℕ) (𝓝 (sSup S)) := by
      simp_rw [hFu]; tauto
    exact tendsto_nhds_unique h1 h2
  have hd0 : deriv f z₀ ≠ 0 := by
    aesop
  have hfinj :=
    hurwitz_injOn hΩ hUc (fun n => (hF n).1) (fun n => (hF n).2.1) hconv hz₀ hd0
  have hfz₀ : f z₀ = 0 := by
    have h1 := hconv.tendsto_at hz₀
    have h2 : Tendsto (fun n => F n z₀) (l : Filter ℕ) (𝓝 0) := by
      simp_rw [(hF _).2.2.2]; simp
    exact tendsto_nhds_unique h1 h2
  have hfle : ∀ z ∈ Ω, ‖f z‖ ≤ 1 := by
    intro z hz
    have h1 :=
      (hconv.tendsto_at hz).norm
    exact le_of_tendsto' h1 fun n => (mem_ball_zero_iff.1 ((hF n).2.2.1 hz)).le
  have hmaps : MapsTo f Ω (ball 0 1) := by
    have hopen := isOpen_image_of_injOn hΩ hfd hfinj subset_rfl hΩ
    have hsub : f '' Ω ⊆ closedBall 0 1 := by
      rintro _ ⟨z, hz, rfl⟩; simp_all
    have := hopen.subset_interior_iff.2 hsub
    rw [interior_closedBall (0 : ℂ) one_ne_zero] at this
    exact fun z hz => this ⟨z, hz, rfl⟩
  refine ⟨f, ⟨hfd, hfinj, hmaps, hfz₀⟩, fun g hg => ?_⟩
  rw [hnorm]
  exact le_csSup hSbdd ⟨g, hg, rfl⟩

private lemma norm_one_sub_conj_mul {a : ℂ} (ha : ‖a‖ < 1) :
    ‖1 - (starRingEnd ℂ) a * a‖ = 1 - ‖a‖ ^ 2 := by
  have h : 1 - (starRingEnd ℂ) a * a = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by
    simp [mul_comm, mul_conj, normSq_eq_norm_sq]
  rw [h, norm_real, Real.norm_of_nonneg (by nlinarith [norm_nonneg a])]

/-- An extremal admissible map is onto the unit disk. -/
lemma surjOn_of_extremal {Ω : Set ℂ} (hΩ : IsOpen Ω) [SimplyConnectedSpace Ω] {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) {f : ℂ → ℂ} (hf : Admissible Ω z₀ f)
    (hmax : ∀ g, Admissible Ω z₀ g → ‖deriv g z₀‖ ≤ ‖deriv f z₀‖) :
    SurjOn f Ω (ball 0 1) := by
  intro w hw
  by_contra hnot
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
  obtain ⟨hfd, hfinj, hfmaps, hfz₀⟩ := hf
  have hfn : ∀ z ∈ Ω, ‖f z‖ < 1 := fun z hz => mem_ball_zero_iff.1 (hfmaps hz)
  -- `h = mob w ∘ f` does not vanish
  set h : ℂ → ℂ := fun z => mob w (f z) with hh
  have hhd : DifferentiableOn ℂ h Ω := fun z hz =>
    (differentiableAt_mob hw1 (hfn z hz)).comp_differentiableWithinAt z (hfd z hz)
  have hh0 : ∀ z ∈ Ω, h z ≠ 0 := by
    intro z hz h0
    rw [hh, mob_eq_zero_iff hw1 (hfn z hz)] at h0
    exact hnot ⟨z, hz, h0⟩
  obtain ⟨s, hsd, hssq⟩ := exists_sqrt_of_simplyConnected hΩ hhd hh0
  have hsn : ∀ z ∈ Ω, ‖s z‖ < 1 := by
    intro z hz
    have h1 : ‖s z‖ ^ 2 < 1 := by
      rw [← norm_pow, hssq z hz]; exact norm_mob_lt_one hw1 (hfn z hz)
    nlinarith [norm_nonneg (s z)]
  have hsinj : InjOn s Ω := by
    intro z hz z' hz' hzz
    have : h z = h z' := by grind
    exact hfinj hz hz' (mob_injOn hw1 (mem_ball_zero_iff.2 (hfn z hz))
      (mem_ball_zero_iff.2 (hfn z' hz')) this)
  set c := s z₀ with hc
  have hcn : ‖c‖ < 1 := hsn z₀ hz₀
  have hc2 : c ^ 2 = -w := by
    rw [hc, hssq z₀ hz₀, hh]; simp [hfz₀]
  have hwc : w = -c ^ 2 := by rw [hc2, neg_neg]
  -- the competitor `F = mob c ∘ s`
  set F : ℂ → ℂ := fun z => mob c (s z) with hF
  have hFadm : Admissible Ω z₀ F := by
    refine ⟨fun z hz => (differentiableAt_mob hcn (hsn z hz)).comp_differentiableWithinAt z
      (hsd z hz), ?_, fun z hz => mob_mem_ball (mem_ball_zero_iff.2 hcn)
      (mem_ball_zero_iff.2 (hsn z hz)), by simp [hF, hc]⟩
    intro z hz z' hz' hzz
    exact hsinj hz hz' (mob_injOn hcn (mem_ball_zero_iff.2 (hsn z hz))
      (mem_ball_zero_iff.2 (hsn z' hz')) hzz)
  have hn : ∀ᶠ z in 𝓝 z₀, z ∈ Ω := hΩ.mem_nhds hz₀
  have hfd' := (hfd.differentiableAt hn).hasDerivAt
  have hsd' := (hsd.differentiableAt hn).hasDerivAt
  have hsq : (fun z => s z ^ 2) =ᶠ[𝓝 z₀] mob w ∘ f := hn.mono fun z hz => hssq z hz
  have hA := ((hasDerivAt_mob hw1 (hfn z₀ hz₀)).comp z₀ hfd').congr_of_eventuallyEq hsq
  have hB := (hasDerivAt_pow 2 (s z₀)).comp z₀ hsd'
  have he := congrArg norm (hA.unique hB)
  have hw' : ‖w‖ = ‖c‖ ^ 2 := by rw [hwc, norm_neg, norm_pow]
  simp only [hfz₀, mul_zero, sub_zero, one_pow, div_one, Nat.cast_ofNat, norm_mul, ← hc] at he
  norm_num [norm_ofNat] at he
  rw [norm_one_sub_conj_mul hw1, hw'] at he
  have hFc := (hasDerivAt_mob hcn (hsn z₀ hz₀)).comp z₀ hsd'
  have hr : 0 < 1 - ‖c‖ ^ 2 := by nlinarith [norm_nonneg c]
  have hFm : ‖deriv F z₀‖ = ‖deriv s z₀‖ / (1 - ‖c‖ ^ 2) := by
    change ‖deriv (mob c ∘ s) z₀‖ = _
    rw [hFc.deriv, norm_mul, norm_div, ← hc, norm_pow, norm_one_sub_conj_mul hcn]
    field_simp [hr.ne']
  have hm := mul_le_mul_of_nonneg_left ((div_le_iff₀ hr).mp (hFm ▸ hmax F hFadm))
    (show 0 ≤ 2 * ‖c‖ by positivity)
  have hp := mul_pos (mul_pos hr (sq_pos_of_ne_zero (sub_ne_zero.mpr hcn.ne)))
    (norm_pos_iff.mpr (deriv_ne_zero_of_injOn hΩ hfd hfinj hz₀))
  nlinarith

/-- The Riemann mapping theorem for bounded simply connected open sets. -/
theorem riemann_mapping_theorem (Ω : Set ℂ) (hopen : IsOpen Ω) [SimplyConnectedSpace Ω]
    (hb : Bornology.IsBounded Ω) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball 0 1) ∧ InjOn G (ball 0 1) ∧ G '' ball 0 1 = Ω := by
  obtain ⟨⟨z₀, hz₀⟩⟩ : Nonempty Ω := inferInstance
  obtain ⟨f, hf, hmax⟩ := exists_extremal hopen hb hz₀
  have himg :=
    hf.2.2.1.image_subset.antisymm (surjOn_of_extremal hopen hz₀ hf hmax)
  obtain ⟨g, hg, hm, hl, hr⟩ := exists_holomorphic_inverse hopen hf.1 hf.2.1
  rw [himg] at hg hm hr
  exact ⟨g, hg, (show RightInvOn g f _ from fun _ => hr _).injOn,
    hm.image_subset.antisymm (fun z hz => ⟨f z, hf.2.2.1 hz, hl z hz⟩)⟩

end

end PolyaNeumann.RiemannInterior

namespace PolyaNeumann

open Set Metric

/-- Every bounded simply connected open planar domain has an actual
injective holomorphic parametrization by the open unit disk. -/
theorem exists_interior_conformal_map (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hsc : SimplyConnectedSpace Ω) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball 0 1) ∧
      Set.InjOn F (Metric.ball 0 1) ∧ F '' Metric.ball 0 1 = Ω := RiemannInterior.riemann_mapping_theorem Ω hopen hb

end PolyaNeumann
