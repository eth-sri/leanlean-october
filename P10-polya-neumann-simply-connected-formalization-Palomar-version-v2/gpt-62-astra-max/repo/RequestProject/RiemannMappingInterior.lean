module

public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.Order.IsLUB
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Tactic
public import RequestProject.PlanarNotation

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
  let g := Function.invFunOn f U
  have hUa := hU.mem_nhds ha
  have left : g ∘ f =ᶠ[𝓝 a] id := eventually_of_mem hUa fun _ hz => hinj.leftInvOn_invFunOn hz
  have han := hf.analyticOnNhd hU
  have hnc : ¬ ∀ᶠ z in 𝓝 a, f z = f a := by
    intro he
    have hn : ∀ᶠ z in 𝓝[≠] a, z ≠ a := self_mem_nhdsWithin
    obtain ⟨z, hn, hz, heq⟩ := (hn.and (nhdsWithin_le_nhds (inter_mem hUa he))).exists
    exact hn (hinj hz ha heq)
  have hopen := (han a ha).eventually_constant_or_nhds_le_map_nhds.resolve_left hnc
  have hc : ContinuousAt g (f a) := by
    rw [ContinuousAt, show g (f a) = a from left.self_of_nhds]
    exact (tendsto_map'_iff.mpr (tendsto_id.congr' left.symm)).mono_left hopen
  have right : f ∘ g =ᶠ[𝓝 (f a)] id := eventually_of_mem (hopen (image_mem_map hUa))
    (fun _ hy => Function.invFunOn_eq hy)
  have hcrit : ∀ᶠ z in 𝓝[≠] a, deriv f z ≠ 0 := by
    refine (han a ha).deriv.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun he => hnc ?_
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hUa he)
    filter_upwards [ball_mem_nhds a hr] with x hx
    exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball a r).isPreconnected
      (hf.mono fun z hz => (hsub hz).1) (fun _ hz => (hsub hz).2) hx (mem_ball_self hr)
  have hg : AnalyticAt ℂ g (f a) := by
    refine analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt (eventually_nhdsWithin_iff.mpr ?_) hc
    apply hopen
    change ∀ᶠ x in 𝓝 a, f x ≠ f a → DifferentiableAt ℂ g (f x)
    filter_upwards [hUa, eventually_nhdsWithin_iff.mp hcrit] with x hx hd hne
    apply HasDerivAt.differentiableAt
    apply HasStrictDerivAt.hasDerivAt
    exact (han x hx).hasStrictDerivAt.to_local_left_inverse (hd fun h => hne (h ▸ rfl))
      (eventually_of_mem (hU.mem_nhds hx) fun _ hy => hinj.leftInvOn_invFunOn hy)
  intro h0
  have hf₀ := (han a ha).differentiableAt.hasDerivAt
  rw [h0, ← show g (f a) = a from left.self_of_nhds] at hf₀
  exact not_differentiableAt_of_local_left_inverse_hasDerivAt_zero hf₀ right hg.differentiableAt

end

section

/-! ## Disk automorphisms `z ↦ (z - a) / (1 - ā z)` -/

open Complex Metric

section

variable (a z : ℂ)

include a z in
/-- The disk automorphism `mob a z = (z - a) / (1 - ā z)`. -/
def mob : ℂ := (z - a) / (1 - (starRingEnd ℂ) a * z)

lemma mob_denom_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 - (starRingEnd ℂ) a * z ≠ 0 := by
  intro h
  have h1 : (starRingEnd ℂ) a * z = 1 := by linear_combination -h
  have : ‖(starRingEnd ℂ) a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc _ ≤ ‖a‖ * 1 := by gcongr
      _ < 1 := by linarith
  rw [h1] at this
  simp at this

/-- The key identity `|1 - ā z|² - |z - a|² = (1 - |a|²)(1 - |z|²)`. -/
lemma normSq_identity :
    normSq (1 - (starRingEnd ℂ) a * z) - normSq (z - a) =
      (1 - normSq a) * (1 - normSq z) := by
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, conj_re, conj_im, one_re, one_im]
  ring

lemma norm_mob_lt_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : ‖mob a z‖ < 1 := by
  
  unfold mob
  rw [norm_div, div_lt_one (norm_pos_iff.2 (mob_denom_ne_zero ha hz))]
  have hid := normSq_identity a z
  have ha2 : normSq a < 1 := by
    rw [normSq_eq_norm_sq]; simp [*]
  have hz2 : normSq z < 1 := by
    rw [normSq_eq_norm_sq]; simp [*]
  have : normSq (z - a) < normSq (1 - (starRingEnd ℂ) a * z) := by
    nlinarith
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at this
  nlinarith [norm_nonneg (z - a), norm_nonneg (1 - (starRingEnd ℂ) a * z)]

lemma mob_mem_ball {a z : ℂ} (ha : a ∈ unitDisk) (hz : z ∈ unitDisk) :
    mob a z ∈ unitDisk := by
  rw [mem_ball_zero_iff] at *
  exact norm_mob_lt_one ha hz

@[simp] lemma mob_self : mob a a = 0 := by simp [mob]

@[simp] lemma mob_zero : mob a 0 = -a := by simp [mob]

end

lemma mob_neg_mob {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : mob (-a) (mob a z) = z := by
  have hd := mob_denom_ne_zero ha hz
  
  unfold mob
  rw [map_neg]
  have h2 : 1 - -(starRingEnd ℂ) a * ((z - a) / (1 - (starRingEnd ℂ) a * z)) =
      (1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z) := by
    field_simp; ring
  rw [h2, div_eq_iff (div_ne_zero (mob_denom_ne_zero ha ha) hd)]
  generalize (starRingEnd ℂ) a = c at *
  rw [div_sub' hd, mul_div_assoc', div_left_inj' hd]
  ring

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
  field_simp
  ring

lemma differentiableAt_mob {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (mob a) z := (hasDerivAt_mob ha hz).differentiableAt

lemma mob_eq_zero_iff {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : mob a z = 0 ↔ z = a := by
  constructor
  · intro h
    have hd := mob_denom_ne_zero ha hz
    unfold mob at h
    grind
  · rintro rfl; simp

end

section

/-! ## Holomorphic square roots on simply connected domains -/

open Complex Metric Filter Topology Set

/-- **Holomorphic square roots.** A nonvanishing holomorphic function on a simply connected
open subset of `ℂ` has a holomorphic square root. -/
theorem exists_sqrt_of_simplyConnected {Ω : Set ℂ} (hΩ : IsOpen Ω) [SimplyConnectedSpace Ω]
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) (hf0 : ∀ z ∈ Ω, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ Ω, g z ^ 2 = f z := by
  obtain ⟨g, hg, hsq⟩ := Complex.exists_continuousOn_pow_eq (inferInstanceAs (SimplyConnectedSpace Ω))
    hΩ hf.continuousOn (by grind) two_ne_zero
  refine ⟨g, fun z hz => ?_, fun z _ => hsq z⟩
  have hU := hΩ.mem_nhds hz
  have hgz : g z ≠ 0 := fun h => hf0 z hz (by simp [← hsq z, h])
  exact (HasDerivAt.of_comp_left (hg.continuousAt hU) (hasDerivAt_pow 2 (g z))
    (hf.differentiableAt hU).hasDerivAt (by simp [hgz]) (Eventually.of_forall hsq)).differentiableAt.differentiableWithinAt

end

section

/-! ## Montel's theorem -/

open Complex Metric Filter Topology Set

/-- Cauchy estimate: a holomorphic family bounded by `1` on `U` is equicontinuous at every
point of `U`. -/
lemma equicontinuousAt_of_norm_le_one {ι : Type*} {F : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
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
    calc _ ≤ _ := dist_triangle _ _ _
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
  have hdiff : ∀ i, ∀ y ∈ ball z r, DifferentiableAt ℂ (F i) y := fun i y hy => (hF i).differentiableAt (hU.mem_nhds (hsub y hy (mem_closedBall_self hr0.le)))
  
  rw [Metric.equicontinuousAt_iff]
  intro e he
  refine ⟨min r (e * r / 2), by positivity, fun y hy i => ?_⟩
  
  
  rw [dist_comm, dist_eq_norm]
  calc _ ≤ _ := (fun i y hy =>
    (convex_ball z r).norm_image_sub_le_of_norm_deriv_le (hdiff i) (hderiv i)
      (mem_ball_self hr0) hy) i y (mem_ball.2 (lt_of_lt_of_le hy (min_le_left _ _)))
    _ ≤ 1 / r * (e * r / 2) := by
        gcongr; rw [← dist_eq_norm]; grind
    _ = e / 2 := by field_simp
    _ < e := by linarith

/-- **Montel's theorem.** A family of holomorphic functions on an open set `U`, bounded by `1`
on `U`, converges locally uniformly on `U` along any ultrafilter. -/
theorem montel {ι : Type*} (l : Ultrafilter ι) {F : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hb : ∀ i, ∀ z ∈ U, ‖F i z‖ ≤ 1) :
    ∃ f : ℂ → ℂ, TendstoLocallyUniformlyOn F f (l : Filter ι) U := by
  have hpt : ∀ z, ∃ w, z ∈ U → Tendsto (fun i => F i z) l (𝓝 w) := by
    intro z
    by_cases hz : z ∈ U
    · obtain ⟨w, -, hw⟩ := (isCompact_closedBall 0 1).ultrafilter_le_nhds
        (l.map (fun i => F i z)) (by
          rw [Ultrafilter.coe_map]
          refine tendsto_principal.2 (Eventually.of_forall fun i => ?_)
          simp [*])
      solve_by_elim
    · simp [*]
  choose f hf using hpt
  refine ⟨f, ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  have heq : ∀ K' ∈ ({K} : Set (Set ℂ)), EquicontinuousOn F K' := by
    rintro K' rfl x hx
    exact (equicontinuousAt_of_norm_le_one hU hF hb (hKU hx)).equicontinuousWithinAt _
  have key := (EquicontinuousOn.tendsto_uniformOnFun_iff_pi' 
    (by simpa using hK) heq l f).2 (by
      rw [tendsto_pi_nhds]
      grind)
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at key
  exact key K rfl

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
  set m := ‖g z1‖ 
  have hm0  := norm_pos_iff.2 (hg0 z1 hz1)
  rw [Metric.tendstoUniformlyOn_iff] at hconv
  obtain ⟨i, hi⟩ := (hconv (m / 2) (by positivity)).exists
  have hbd : ∀ z ∈ sphere a r, ‖(F i z)⁻¹‖ ≤ 2 / m := by
    intro z hz
    have h1  := hmin hz
    have h2 : ‖g z - F i z‖ < m / 2 := by
      rw [← dist_eq_norm]; exact hi z (sphere_subset_closedBall hz)
    
    rw [norm_inv]
    calc _ ≤ (m / 2)⁻¹ := inv_anti₀ (by positivity) (by
      grind [norm_sub_norm_le])
      _ = _ := by rw [inv_div]
  have hd : DiffContOnCl ℂ (fun z => (F i z)⁻¹) (ball a r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball a hr.ne']
    exact (hF i).inv (hF0 i)
  have hFa  :=
    norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd
      (by rw [frontier_ball a hr.ne']; exact hbd) (subset_closure (mem_ball_self hr))
  have hFa' : m / 2 ≤ ‖F i a‖ := by
    have hne  := hF0 i a (mem_closedBall_self hr.le)
    rw [norm_inv] at hFa
    
    rw [inv_le_comm₀ (norm_pos_iff.2 hne) (by positivity), inv_div] at hFa
    exact hFa
  have hga : ‖g a - F i a‖ < m / 2 := by
    rw [← dist_eq_norm]; exact hi a (mem_closedBall_self hr.le)
  intro h0
  rw [h0, zero_sub, norm_neg] at hga
  linarith

/-- **Hurwitz's theorem.** A locally uniform limit of injective holomorphic functions on a
connected open set, whose derivative does not vanish at some point, is injective. -/
theorem hurwitz_injOn {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hinj : ∀ i, InjOn (F i) U)
    (hconv : TendstoLocallyUniformlyOn F f l U) {z0 : ℂ} (hz0 : z0 ∈ U)
    (hd : deriv f z0 ≠ 0) : InjOn f U := by
  intro a ha b hb hab
  by_contra hne
  have hfd  :=
    hconv.differentiableOn (Eventually.of_forall hF) hU
  
  set g  := fun z => f z - f b with hg
  have hgan : AnalyticOnNhd ℂ g U := fun z hz => ((hfd.analyticOnNhd hU) z hz).sub analyticAt_const
  
  have hev  :=
    ((hgan a ha).eventually_eq_zero_or_eventually_ne_zero).resolve_left (by
        intro hev

        have hloc : f =ᶠ[𝓝 z0] fun _ => f b := by
          filter_upwards [hU.mem_nhds hz0] with z hz
          have := (hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc ha hev) hz
          simp [hg, sub_eq_zero] at this
          exact this
        apply hd
        simp [hloc.deriv_eq])
  rw [eventually_nhdsWithin_iff] at hev
  
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1
    (inter_mem (inter_mem hev (hU.mem_nhds ha)) (isOpen_compl_singleton.mem_nhds hne))
  set r := ε / 2 with hr
  have hr0 : 0 < r := by positivity
  have hcb : closedBall a r ⊆ ball a ε := closedBall_subset_ball (by linarith)
  have hcbU : closedBall a r ⊆ U := fun z hz => (hεsub (hcb hz)).1.2
  
  
  
  
  
  have key := hurwitz_ne_zero hr0  (g := g)
    (fun i => ((hF i).mono hcbU).sub_const _)
    (fun i z hz h => (fun z hz => (hεsub (hcb hz)).2) z hz (hinj i (hcbU hz) hb (sub_eq_zero.1 h)))
    (((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv _ hcbU (isCompact_closedBall a r)).sub ((hconv.tendsto_at hb).tendstoUniformlyOn_const _)) ((hfd.mono hcbU).continuousOn.sub continuousOn_const |>.mono
      sphere_subset_closedBall)
    (fun z hz => (fun z hz => (hεsub (hcb hz)).1.1) z (sphere_subset_closedBall hz) (by
      rintro rfl
      rw [mem_sphere, dist_self] at hz
      exact hr0.ne hz))
  exact key (by simp [*])

end

section

/-! ## The Riemann mapping theorem -/

open Complex Metric Filter Topology Set

/-- Open mapping theorem for injective holomorphic maps on a connected open set. -/
lemma isOpen_image_of_injOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) : IsOpen (f '' U) := by
  apply isOpen_iff_mem_nhds.2
  rintro _ ⟨z, hz, rfl⟩
  rw [← ((hf.analyticOnNhd hU z hz).hasStrictDerivAt.map_nhds_eq
    (deriv_ne_zero_of_injOn hU hf hinj hz))]
  exact Filter.image_mem_map (hU.mem_nhds hz)

/-- The admissible family: injective holomorphic maps `Ω → 𝔻` sending `z₀` to `0`. -/
def Admissible (Ω : Set ℂ) (z₀ : ℂ) (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f Ω ∧ InjOn f Ω ∧ MapsTo f Ω (ball 0 1) ∧ f z₀ = 0

/-- The admissible family is nonempty (square-root trick). -/
lemma exists_admissible {Ω : Set ℂ} (hΩ : IsOpen Ω) [SimplyConnectedSpace Ω]
    (hne : Ω ≠ univ) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) : ∃ f, Admissible Ω z₀ f := by
  obtain ⟨a, ha⟩ := (ne_univ_iff_exists_notMem Ω).mp hne
  have hza : ∀ z ∈ Ω, z - a ≠ 0 := fun z hz h => ha (sub_eq_zero.1 h ▸ hz)
  obtain ⟨g, hgd, hgsq⟩ := exists_sqrt_of_simplyConnected hΩ
    (f := fun z => z - a) (differentiableOn_id.sub_const a) (fun z hz h => ha (sub_eq_zero.1 h ▸ hz))
  have hginj : InjOn g Ω := by
    intro z hz w hw h
    grind [hgsq z hz]
  have hgneg : ∀ z ∈ Ω, ∀ w ∈ Ω, g z ≠ -g w := by
    grind
  have hopen  := isOpen_image_of_injOn hΩ hgd hginj
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 hopen (g z₀) ⟨z₀, hz₀, rfl⟩
  have hfar : ∀ z ∈ Ω, ρ ≤ ‖g z + g z₀‖ := by
    intro z hz
    by_contra hlt
    push_neg at hlt
    have : -g z ∈ ball (g z₀) ρ := by
      rw [mem_ball, dist_eq_norm, ← norm_neg]
      convert hlt using 2; ring
    obtain ⟨w, hw, hgw⟩ := hρsub this
    exact hgneg w hw z hz hgw
  have hne0 : ∀ z ∈ Ω, g z + g z₀ ≠ 0 := fun z hz h => by
    have := hfar z hz; rw [h, norm_zero] at this; linarith
  have hinvle : ∀ z ∈ Ω, ‖(g z + g z₀)⁻¹‖ ≤ 1 / ρ := by
    intro z hz
    rw [norm_inv, one_div]
    exact inv_anti₀ hρ (hfar z hz)
  refine ⟨fun z => ((ρ / 4 : ℝ) : ℂ) * ((g z + g z₀)⁻¹ - (g z₀ + g z₀)⁻¹), ?_, ?_, ?_, ?_⟩
  · fun_prop
  · intro z hz w hw h
    
    have hρ4 : ((ρ / 4 : ℝ) : ℂ) ≠ 0 := by
      have : ρ / 4 ≠ 0 := by positivity
      exact_mod_cast this
    grind [mul_left_cancel₀ hρ4 h]
  · intro z hz
    rw [mem_ball_zero_iff, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc _
        ≤ ρ / 4 * (‖(g z + g z₀)⁻¹‖ + ‖(g z₀ + g z₀)⁻¹‖) := by
          bound
      _ ≤ ρ / 4 * (1 / ρ + 1 / ρ) := by
          bound
      _ = 1 / 2 := by field_simp; ring
      _ < 1 := by norm_num
  · simp

/-- Cauchy estimate for admissible maps. -/
lemma norm_deriv_le_of_admissible {Ω : Set ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : closedBall z₀ r ⊆ Ω) {f : ℂ → ℂ} (hf : Admissible Ω z₀ f) :
    ‖deriv f z₀‖ ≤ 1 / r := by
  apply norm_deriv_le_of_forall_mem_sphere_norm_le hr
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball z₀ hr.ne']
    exact hf.1.mono hsub
  · intro w hw
    exact (mem_ball_zero_iff.1 (hf.2.2.1 (hsub (sphere_subset_closedBall hw)))).le

/-- Existence of an extremal admissible map (Montel + Hurwitz). -/
lemma exists_extremal {Ω : Set ℂ} (hΩ : IsOpen Ω) [SimplyConnectedSpace Ω]
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
    have h1 : ‖deriv f₁ z₀‖ ≤ sSup S := le_csSup hSbdd ⟨f₁, hf₁, rfl⟩
    have h2 : 0 < ‖deriv f₁ z₀‖ :=
      norm_pos_iff.2 (deriv_ne_zero_of_injOn hΩ hf₁.1 hf₁.2.1 hz₀)
    linarith
  obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sSup hSne hSbdd
  choose F hF hFu using huS
  set l : Ultrafilter ℕ := Ultrafilter.of atTop
  have hl : (l : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨f, hconv⟩ := montel l hΩ (fun n => (hF n).1)
    (fun n z hz => (mem_ball_zero_iff.1 ((hF n).2.2.1 hz)).le)
  have hfd  :=
    hconv.differentiableOn (Eventually.of_forall fun n => (hF n).1) hΩ
  have hderiv  :=
    (hconv.deriv (Eventually.of_forall fun n => (hF n).1) hΩ).tendsto_at hz₀
  have hnorm : ‖deriv f z₀‖ = sSup S := by
    have h1  :=
      hderiv.norm
    have h2 : Tendsto (fun n => ‖deriv (F n) z₀‖) (l : Filter ℕ) (𝓝 (sSup S)) := by
      simp_rw [hFu]; exact hu.mono_left hl
    exact tendsto_nhds_unique h1 h2
  have hd0 : deriv f z₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm; linarith
  have hfinj  :=
    hurwitz_injOn hΩ hUc (fun n => (hF n).1) (fun n => (hF n).2.1) hconv hz₀ hd0
  have hfz₀ : f z₀ = 0 := by
    have h1  := hconv.tendsto_at hz₀
    have h2 : Tendsto (fun n => F n z₀) (l : Filter ℕ) (𝓝 0) := by
      simp_rw [(hF _).2.2.2]; exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  have hfle : ∀ z ∈ Ω, ‖f z‖ ≤ 1 := by
    intro z hz
    have h1  :=
      (hconv.tendsto_at hz).norm
    exact le_of_tendsto' h1 fun n => (mem_ball_zero_iff.1 ((hF n).2.2.1 hz)).le
  have hmaps : MapsTo f Ω (ball 0 1) := by
    have hopen  := isOpen_image_of_injOn hΩ hfd hfinj
    have hsub : f '' Ω ⊆ closedBall 0 1 := by
      rintro _ ⟨z, hz, rfl⟩; simp [*]
    have := hopen.subset_interior_iff.2 hsub
    rw [interior_closedBall (0 : ℂ) one_ne_zero] at this
    exact fun z hz => this ⟨z, hz, rfl⟩
  refine ⟨f, ⟨hfd, hfinj, hmaps, hfz₀⟩, fun g hg => ?_⟩
  rw [hnorm]
  exact le_csSup hSbdd ⟨g, hg, rfl⟩

/-- The derivative at `0` of `ζ ↦ mob (-w) ((mob (-c) ζ)²)` when `w = -c²`. -/
lemma hasDerivAt_psi {c : ℂ} (hc : ‖c‖ < 1) :
    HasDerivAt (fun ζ => mob (-(-c ^ 2)) (mob (-c) ζ ^ 2))
      (2 * c / (1 + (starRingEnd ℂ) c * c)) 0 := by
  have hc' : ‖-c‖ < 1 := by rwa [norm_neg]
  have hw : ‖-(-c ^ 2)‖ < 1 := by
    simp [*]
  
  have h1 := hasDerivAt_mob hc' (z := 0) (by simp)
  have h2 : HasDerivAt (fun ζ => ζ ^ 2) (2 * mob (-c) 0) (mob (-c) 0) := by
    simpa using hasDerivAt_pow 2 (mob (-c) 0)
  have h3 := hasDerivAt_mob hw (z := mob (-c) 0 ^ 2) (by simpa using (by simp [*]))
  have := h3.comp 0 (h2.comp 0 h1)
  simp only [Function.comp_def] at this
  convert this using 1
  simp only [mob_zero, neg_neg, map_neg, map_pow, mul_zero, sub_zero]
  have hden : 1 + (starRingEnd ℂ) c * c ≠ 0 := by
    rw [conj_mul']
    have : 0 ≤ ‖c‖ ^ 2 := by positivity
    intro h
    have h' : ((1 + ‖c‖ ^ 2 : ℝ) : ℂ) = 0 := by push_cast; exact h
    have : (1 + ‖c‖ ^ 2) = 0 := by exact_mod_cast h'
    linarith
  have hden2 : 1 - (starRingEnd ℂ) c * c ≠ 0 := by
    have := mob_denom_ne_zero hc hc
    exact this
  have hden3 : 1 - (starRingEnd ℂ) c ^ 2 * c ^ 2 ≠ 0 := by
    have : 1 - (starRingEnd ℂ) c ^ 2 * c ^ 2 =
        (1 - (starRingEnd ℂ) c * c) * (1 + (starRingEnd ℂ) c * c) := by ring
    simp [*]
  
  generalize (starRingEnd ℂ) c = d at *
  have hden' : 1 + c * d ≠ 0 := by rwa [mul_comm]
  have hden3' : 1 - c ^ 2 * d ^ 2 ≠ 0 := by rwa [mul_comm]
  have hfac : 1 - c ^ 2 * d ^ 2 = (1 - d * c) * (1 + c * d) := by ring
  field_simp
  rw [hfac]
  field_simp

/-- `|2c / (1 + |c|²)| < 1` for `|c| < 1`. -/
lemma norm_psi_deriv_lt_one {c : ℂ} (hc : ‖c‖ < 1) :
    ‖2 * c / (1 + (starRingEnd ℂ) c * c)‖ < 1 := by
  rw [conj_mul']
  have h1 : (1 + ‖c‖ ^ 2) = ((1 + ‖c‖ ^ 2 : ℝ) : ℂ) := by simp
  rw [h1, norm_div, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
    div_lt_one (by positivity)]
  simp
  nlinarith

/-- An extremal admissible map is onto the unit disk. -/
lemma surjOn_of_extremal {Ω : Set ℂ} (hΩ : IsOpen Ω) [SimplyConnectedSpace Ω] {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) {f : ℂ → ℂ} (hf : Admissible Ω z₀ f)
    (hmax : ∀ g, Admissible Ω z₀ g → ‖deriv g z₀‖ ≤ ‖deriv f z₀‖) :
    SurjOn f Ω (ball 0 1) := by
  intro w hw
  by_contra hnot
  have hw1  := mem_ball_zero_iff.1 hw
  obtain ⟨hfd, hfinj, hfmaps, hfz₀⟩ := hf
  have hfn : ∀ z ∈ Ω, ‖f z‖ < 1 := fun z hz => mem_ball_zero_iff.1 (hfmaps hz)
  -- `h = mob w ∘ f` does not vanish
  set h  := fun z => mob w (f z) with hh
  have hhd : DifferentiableOn ℂ h Ω := fun z hz =>
    (differentiableAt_mob hw1 (hfn z hz)).comp_differentiableWithinAt z (hfd z hz)
  
  obtain ⟨s, hsd, hssq⟩ := exists_sqrt_of_simplyConnected hΩ hhd (by
    intro z hz h0
    rw [hh, mob_eq_zero_iff hw1 (hfn z hz)] at h0
    exact hnot ⟨z, hz, h0⟩)
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
    simp [*]
  have hwc : w = -c ^ 2 := by simp [hc2]
  -- the competitor `F = mob c ∘ s`
  set F  := fun z => mob c (s z) with hF
  have hFadm : Admissible Ω z₀ F := by
    refine ⟨fun z hz => (differentiableAt_mob hcn (hsn z hz)).comp_differentiableWithinAt z
      (hsd z hz), ?_, fun z hz => mob_mem_ball (mem_ball_zero_iff.2 hcn)
      (mem_ball_zero_iff.2 (hsn z hz)), by simp [*]⟩
    intro z hz z' hz' hzz
    exact hsinj hz hz' (mob_injOn hcn (mem_ball_zero_iff.2 (hsn z hz))
      (mem_ball_zero_iff.2 (hsn z' hz')) hzz)
  -- `f = Ψ ∘ F` on `Ω`
  set Ψ  := fun ζ => mob (-(-c ^ 2)) (mob (-c) ζ ^ 2) with hΨ
  have hfΨ : ∀ z ∈ Ω, f z = Ψ (F z) := by
    intro z hz
    simp only [hΨ, hF]
    rw [mob_neg_mob hcn (hsn z hz), hssq z hz, hh, ← hwc, mob_neg_mob hw1 (hfn z hz)]
  
  have hΨd := hasDerivAt_psi hcn
  
  rw [← hFadm.2.2.2] at hΨd
  
  have hfeq : f =ᶠ[𝓝 z₀] Ψ ∘ F := by
    filter_upwards [hΩ.mem_nhds hz₀] with z hz using hfΨ z hz
  have hdf : deriv f z₀ = 2 * c / (1 + (starRingEnd ℂ) c * c) * deriv F z₀ := by
    rw [hfeq.deriv_eq, (hΨd.comp z₀ ((hFadm.1.differentiableAt (hΩ.mem_nhds hz₀)).hasDerivAt)).deriv]
  have hfd0  := deriv_ne_zero_of_injOn hΩ hfd hfinj hz₀
  have hFd0 : deriv F z₀ ≠ 0 := by
    grind
  have hlt : ‖deriv f z₀‖ < ‖deriv F z₀‖ := by
    rw [hdf, norm_mul]
    have := norm_psi_deriv_lt_one hcn
    have hpos  := norm_pos_iff.2 hFd0
    nlinarith
  linarith [hmax F hFadm]

/-- On the image of an open set, the set-theoretic inverse of an injective
holomorphic map is locally its analytic inverse. -/
private lemma differentiableOn_invFunOn {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D) (hinj : InjOn f D) :
    DifferentiableOn ℂ (Function.invFunOn f D) (f '' D) := by
  rintro _ ⟨z, hz, rfl⟩
  exact ((hf.analyticOnNhd hD z hz).hasStrictDerivAt.to_local_left_inverse
    (deriv_ne_zero_of_injOn hD hf hinj hz)
    (Filter.mem_of_superset (hD.mem_nhds hz) fun _ hx => hinj.leftInvOn_invFunOn hx)).hasDerivAt.differentiableAt.differentiableWithinAt

/-- **Riemann mapping theorem.** Every simply connected open subset `Ω ≠ ℂ` of the plane is
the image of the open unit disk under an injective holomorphic map. (Simple connectivity
includes nonemptiness.) -/
theorem riemann_mapping_theorem (Ω : Set ℂ) (hopen : IsOpen Ω) [SimplyConnectedSpace Ω]
    (hne : Ω ≠ univ) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball 0 1) ∧ InjOn G (ball 0 1) ∧
      G '' ball 0 1 = Ω := by
  obtain ⟨⟨z₀, hz₀⟩⟩ : Nonempty Ω := inferInstance
  obtain ⟨f, hf, hmax⟩ := exists_extremal hopen hne hz₀
  rw [← (surjOn_of_extremal hopen hz₀ hf hmax).image_eq_of_mapsTo hf.2.2.1]
  exact ⟨_, differentiableOn_invFunOn hopen hf.1 hf.2.1, Function.invFunOn_injOn_image f Ω,
    hf.2.1.invFunOn_image Subset.rfl⟩

end

section

open Complex Metric Filter Topology Set

/-- An injective holomorphic map on a connected open set has a holomorphic inverse on its
(open) image. -/
lemma exists_holomorphic_inverse {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) (hinj : InjOn f D) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (f '' D) ∧ MapsTo g (f '' D) D ∧
      (∀ z ∈ D, g (f z) = z) ∧ ∀ w ∈ f '' D, f (g w) = w :=
  ⟨_, differentiableOn_invFunOn hD hf hinj, fun _ hw => Function.invFunOn_mem hw,
    fun _ hz => hinj.leftInvOn_invFunOn hz, fun _ hw => Function.invFunOn_eq hw⟩

end

end PolyaNeumann.RiemannInterior

namespace PolyaNeumann

open Set Metric

/-- Every bounded simply connected open planar domain has an actual
injective holomorphic parametrization by the open unit disk. -/
theorem exists_interior_conformal_map (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hsc : SimplyConnectedSpace Ω) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball 0 1) ∧
      Set.InjOn F (Metric.ball 0 1) ∧ F '' Metric.ball 0 1 = Ω := by
  letI  := hsc
  
  apply RiemannInterior.riemann_mapping_theorem Ω hopen
  rintro rfl
  exact (NormedSpace.unbounded_univ ℝ ℂ) hb

end PolyaNeumann
