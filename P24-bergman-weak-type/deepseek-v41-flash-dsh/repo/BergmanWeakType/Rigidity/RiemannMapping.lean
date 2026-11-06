/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

Adapted from mathlib pull request 33505, commit
d43061d911b1aeae0788591da437a3b115098962, for Lean v4.35.0-rc2.
Upstream source: Mathlib/Analysis/Complex/RiemannMapping.lean
-/
module

public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Complex.RiemannMapping
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import BergmanWeakType.Rigidity.UnitDiscShift
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Riemann mapping theorem (draft)
-/

open Set Metric Function Filter
open scoped Pointwise Topology ComplexConjugate Real BigOperators Uniformity

public section

theorem TendstoUniformly.fun_const_of_tendsto {ι α X : Type*} [UniformSpace X] {f : ι → X}
    {l : Filter ι} {x : X} (h : Tendsto f l (𝓝 x)) :
    TendstoUniformly (fun i (_ : α) ↦ f i) (fun _ : α ↦ x) l := by
  intro U hU
  filter_upwards [(tendsto_left_nhds_uniformity (a := x)).comp h hU] with i hi y using hi

alias Filter.Tendsto.tendstoUniformly_fun_const := TendstoUniformly.fun_const_of_tendsto

theorem Metric.isPreconnected_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} {r : ℝ} : IsPreconnected (ball x r) :=
  (convex_ball _ _).isPreconnected

namespace Complex

theorem le_norm_of_forall_mem_sphere_le_norm {g : ℂ → ℂ} {c : ℂ} {ρ m : ℝ}
    (hρ : 0 < ρ) (hm : 0 < m)
    (hg : ∀ z ∈ Metric.closedBall c ρ, g z ≠ 0)
    (hd : DifferentiableOn ℂ g (Metric.closedBall c ρ))
    (h : ∀ z ∈ Metric.sphere c ρ, m ≤ ‖g z‖) :
    ∀ z ∈ Metric.closedBall c ρ, m ≤ ‖g z‖ := by
  have hcb : closure (Metric.ball c ρ) = Metric.closedBall c ρ := closure_ball c hρ.ne'
  have hfront : frontier (Metric.ball c ρ) = Metric.sphere c ρ := frontier_ball c hρ.ne'
  have hgdiff : DiffContOnCl ℂ (fun z => (g z)⁻¹) (Metric.ball c ρ) := by
    refine ⟨fun z hz => ?_, ?_⟩
    · exact (hd.differentiableAt (Metric.closedBall_mem_nhds_of_mem hz)).inv
        (hg z (ball_subset_closedBall hz)) |>.differentiableWithinAt
    · refine ContinuousOn.inv₀ (hd.continuousOn.mono ?_) ?_
      · rw [hcb]
      · intro z hz
        rw [hcb] at hz
        exact hg z hz
  intro z hz
  have hle : ‖(g z)⁻¹‖ ≤ m⁻¹ := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x := c) (r := ρ)) hgdiff ?_ ?_
    · intro ζ hζ
      rw [hfront] at hζ
      rw [norm_inv]
      exact (inv_le_inv₀ (norm_pos_iff.mpr (hg ζ (sphere_subset_closedBall hζ))) hm).mpr
        (h ζ hζ)
    · rw [hcb]
      exact hz
  rw [norm_inv] at hle
  exact (inv_le_inv₀ (norm_pos_iff.mpr (hg z hz)) hm).mp hle


theorem eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn {ι : Type*} {U : Set ℂ}
    {l : Filter ι} [l.NeBot] {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hFN : ∀ᶠ i in l, ∀ x ∈ U, F i x ≠ 0)
    (hFd : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U) (hf : TendstoLocallyUniformlyOn F f l U) :
    EqOn f 0 U ∨ ∀ x ∈ U, f x ≠ 0 := by
  have hfd : DifferentiableOn ℂ f U := hf.differentiableOn hFd hUo
  rw [or_iff_not_imp_left]
  intro hf₀ c hc hfc
  rcases (hfd.analyticAt (hUo.mem_nhds hc)).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
  · exact hf₀ (hfd.analyticOnNhd hUo |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hc h0)
  · rw [eventually_nhdsWithin_iff] at hne
    obtain ⟨ε, hε, hεU, hεne⟩ : ∃ ε > 0, Metric.closedBall c ε ⊆ U ∧
        ∀ z ∈ Metric.closedBall c ε, z ≠ c → f z ≠ 0 := by
      obtain ⟨ε, hε, hε'⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp
        (hne.and (hUo.eventually_mem hc))
      exact ⟨ε, hε, fun z hz => (hε' hz).2, fun z hz hzc => (hε' hz).1 hzc⟩
    have hcont : ContinuousOn f (Metric.closedBall c ε) := hfd.continuousOn.mono hεU
    have hsne : (Metric.sphere c ε).Nonempty :=
      ⟨c + (ε : ℂ), by simp [Metric.mem_sphere, hε.le]⟩
    obtain ⟨m, hm0, hm⟩ : ∃ m > 0, ∀ z ∈ Metric.sphere c ε, m ≤ ‖f z‖ := by
      obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_sphere c ε).exists_isMinOn hsne (hcont.norm.mono sphere_subset_closedBall)
      exact ⟨‖f z₀‖, norm_pos_iff.mpr (hεne z₀ (sphere_subset_closedBall hz₀)
        (ne_of_mem_sphere hz₀ hε.ne')), fun z hz => hmin hz⟩
    have hunif : TendstoUniformlyOn F f l (Metric.sphere c ε) :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere c ε)).mp
        (hf.mono (sphere_subset_closedBall.trans hεU))
    have hgood : ∀ᶠ i in l, ∀ z ∈ Metric.closedBall c ε, m / 2 ≤ ‖F i z‖ := by
      filter_upwards [hFN, hFd, hunif _ (Metric.dist_mem_uniformity (by linarith : 0 < m / 2))]
        with i hi hdi huni
      refine le_norm_of_forall_mem_sphere_le_norm hε (by linarith)
        (fun z hz => hi z (hεU hz)) (hdi.mono hεU) ?_
      intro z hz
      have h1 := huni z hz
      have h2 := hm z hz
      rw [dist_eq_norm] at h1
      have h3 := norm_sub_norm_le (f z) (F i z)
      linarith
    have hb := hgood.mono fun i hi => hi c (mem_closedBall_self hε.le)
    have hconst : Tendsto (fun _ : ι => m / 2) l (𝓝 (m / 2)) := tendsto_const_nhds
    have := le_of_tendsto_of_tendsto hconst (hf.tendsto_at hc).norm hb
    rw [hfc, norm_zero] at this
    linarith



theorem eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn {ι : Type*} {U : Set ℂ}
    {l : Filter ι} [l.NeBot] {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hF : ∀ᶠ i in l, InjOn (F i) U)
    (hFd : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U) (hf : TendstoLocallyUniformlyOn F f l U) :
    (∃ C, ∀ x ∈ U, f x = C) ∨ InjOn f U := by
  rw [or_iff_not_imp_left]
  intro hfU x hx y hy hxy
  by_contra! hne
  obtain ⟨r, hr₀, hrU, hry⟩ : ∃ r > 0, ball x r ⊆ U ∧ y ∉ ball x r := by
    simp_rw [← subset_compl_singleton_iff, ← subset_inter_iff, ← Metric.mem_nhds_iff]
    simp [hUo.mem_nhds hx, hne]
  have hf_sub : TendstoLocallyUniformlyOn (fun i z ↦ F i z - F i y) (f · - f y) l (ball x r) := by
    refine (hf.mono hrU).fun_sub <|
      (Tendsto.tendstoUniformly_fun_const ?_).tendstoUniformlyOn.tendstoLocallyUniformlyOn
    exact hf.tendsto_at hy
  refine eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn isOpen_ball isPreconnected_ball
    (hF.mono fun i hi z hz ↦ ?_) ?_ hf_sub |>.resolve_left ?_ x (by simpa) (by rwa [sub_eq_zero])
  · rw [sub_ne_zero, hi.ne_iff (hrU hz) hy]
    exact ne_of_mem_of_not_mem hz hry
  · exact hFd.mono fun i hi ↦ hi.mono hrU |>.sub_const _
  · intro heq
    refine hfU ⟨f y, ?_⟩
    refine hf.differentiableOn hFd hUo |>.analyticOnNhd hUo
      |>.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hUc hx ?_
    exact heq.eventuallyEq_of_mem (ball_mem_nhds _ hr₀) |>.mono fun z hz ↦ sub_eq_zero.mp hz

namespace UnitDisc

@[fun_prop]
theorem continuous_shift (z : 𝔻) : Continuous z.shift := by
  simp only [isEmbedding_coe.continuous_iff, Function.comp_def, coe_shift]
  exact .div (by fun_prop) (by fun_prop) fun _ ↦ shift_den_ne_zero _ _

end UnitDisc

theorem exists_mapsTo_unitBall_injOn_deriv_ne_zero_at {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) {x : ℂ} (hx : x ∈ U) :
    ∃ f : ℂ → ℂ, MapsTo f U (ball 0 1) ∧ InjOn f U ∧ ∀ z ∈ U, deriv f z ≠ 0 := by
  wlog hU₀ : 0 ∉ U
  · rw [ne_univ_iff_exists_notMem] at hU
    rcases hU with ⟨a, ha⟩
    specialize this (hUo.vadd (-a)) (by simpa) (by simp [hU]) (x := -a + x)
      (by simpa [mem_vadd_set_iff_neg_vadd_mem]) (by simpa [mem_vadd_set_iff_neg_vadd_mem])
    rcases this with ⟨f, hf₁, hf_inj, hdf⟩
    refine ⟨f ∘ (-a + ·), hf₁.comp (mapsTo_image _ _),
      hf_inj.comp (by simp [InjOn]) (mapsTo_image _ _), fun z hz ↦ ?_⟩
    simpa [Function.comp_def, deriv_comp_const_add] using hdf (-a + z) (mapsTo_image _ _ hz)
  rcases Complex.exists_continuousOn_pow_eq hUc hUo continuousOn_id (by rwa [image_id]) two_ne_zero
    with ⟨f, hfc, hf_inv⟩
  replace hf_inv : LeftInverse (· ^ 2) f := hf_inv
  have hf₀ : ∀ z ∈ U, f z ≠ 0 := by
    intro z hz hfz
    simpa [hfz, (ne_of_mem_of_not_mem hz hU₀).symm] using hf_inv z
  have hdf : ∀ z ∈ U, HasStrictDerivAt f (2 * f z)⁻¹ z := by
    intro z hz
    apply HasStrictDerivAt.of_local_left_inverse
    · exact hfc.continuousAt <| hUo.mem_nhds hz
    · simpa using hasStrictDerivAt_pow 2 (f z)
    · simpa using hf₀ z hz
    · exact .of_forall hf_inv
  have hdf' : DifferentiableOn ℂ f U := fun z hz ↦
    (hdf z hz).hasDerivAt.differentiableAt.differentiableWithinAt
  have hfUx : f '' U ∈ 𝓝 (f x) := by
    rw [← (hdf x hx).map_nhds_eq (by simpa using hf₀ x hx)]
    exact Filter.image_mem_map <| hUo.mem_nhds hx
  have hdisj : ∀ a ∈ U, ∀ b ∈ U, f a + f b ≠ 0 := by
    intro a ha b hb hfab
    obtain rfl : b = a := by
      rw [← hf_inv a, ← hf_inv b]
      simp [eq_neg_iff_add_eq_zero.mpr hfab]
    have : f b = 0 := by linear_combination hfab / 2
    exact hf₀ b hb this
  have hfUxc : (f '' U)ᶜ ∈ 𝓝 (-f x) := by
    rw [nhds_neg, Filter.mem_neg]
    filter_upwards [hfUx]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    exact hdisj a ha b hb (by linear_combination hab)
  rcases Metric.nhds_basis_closedBall.mem_iff.mp hfUxc with ⟨ε, hε₀, hε⟩
  use fun z ↦ ε / (f x + f z)
  refine ⟨?mapsTo, ?injOn, ?deriv⟩
  case mapsTo =>
    intro z hz
    rw [mem_ball_zero_iff, norm_div, norm_real, Real.norm_of_nonneg hε₀.le, div_lt_one₀]
    · by_contra! hle
      refine @hε (f z) ?_ (mem_image_of_mem f hz)
      simpa [dist_eq_norm, add_comm] using hle
    · simpa using hdisj x hx z hz
  case injOn =>
    intro z hz w hw heq
    simpa [div_eq_mul_inv, hε₀.ne', hf_inv.injective.eq_iff] using heq
  case deriv =>
    intro z hz
    rw [(hasDerivAt_const _ _).fun_div ((hdf z hz).hasDerivAt.const_add _) _ |>.deriv]
    · simp [hε₀.ne', hf₀ z hz, hdisj x hx z hz]
    · exact hdisj x hx z hz

theorem UnitDisc.hasDerivWithinAt_shift_comp {f : ℂ → UnitDisc} {z f' : ℂ} {s : Set ℂ}
    (w : UnitDisc) (hf : HasDerivWithinAt (fun x ↦ ↑(f x)) f' s z) :
    HasDerivWithinAt (fun x ↦ w.shift (f x) : ℂ → ℂ)
      ((1 - ‖(w : ℂ)‖ ^ 2) / (1 + conj ↑w * f z) ^ 2 * f') s z := by
  simp only [coe_shift]
  convert (hf.const_add _).fun_div ((hf.const_mul _).const_add _) _ using 1
  · rw [← mul_conj']
    ring
  · apply UnitDisc.shift_den_ne_zero

theorem UnitDisc.hasDerivAt_shift_comp {f : ℂ → UnitDisc} {z f' : ℂ} (w : UnitDisc)
    (hf : HasDerivAt (fun x ↦ ↑(f x)) f' z) :
    HasDerivAt (fun x ↦ w.shift (f x) : ℂ → ℂ)
      ((1 - ‖(w : ℂ)‖ ^ 2) / (1 + conj ↑w * f z) ^ 2 * f') z :=
  (hasDerivWithinAt_shift_comp w hf.hasDerivWithinAt).hasDerivAt univ_mem

@[simp]
theorem UnitDisc.differentiableWithinAt_shift_comp_iff {f : ℂ → UnitDisc} {z : ℂ} {s : Set ℂ}
    (w : UnitDisc) :
    DifferentiableWithinAt ℂ (fun x ↦ w.shift (f x) : ℂ → ℂ) s z ↔
      DifferentiableWithinAt ℂ (f · : ℂ → ℂ) s z := by
  refine ⟨fun h ↦ ?_, fun h ↦
    (hasDerivWithinAt_shift_comp w h.hasDerivWithinAt).differentiableWithinAt⟩
  simpa using (hasDerivWithinAt_shift_comp (-w) h.hasDerivWithinAt).differentiableWithinAt

@[simp]
theorem UnitDisc.differentiableOn_shift_comp_iff {f : ℂ → UnitDisc} {s : Set ℂ} (w : UnitDisc) :
    DifferentiableOn ℂ (fun x ↦ w.shift (f x) : ℂ → ℂ) s ↔
      DifferentiableOn ℂ (f · : ℂ → ℂ) s := by
  simp [DifferentiableOn]

@[simp]
theorem UnitDisc.differentiableAt_shift_comp_iff {f : ℂ → UnitDisc} {z : ℂ} (w : UnitDisc) :
    DifferentiableAt ℂ (fun x ↦ w.shift (f x) : ℂ → ℂ) z ↔
      DifferentiableAt ℂ (f · : ℂ → ℂ) z := by
  refine ⟨fun h ↦ ?_, fun h ↦ (hasDerivAt_shift_comp w h.hasDerivAt).differentiableAt⟩
  simpa using (hasDerivAt_shift_comp (-w) h.hasDerivAt).differentiableAt

@[simp]
theorem UnitDisc.deriv_shift_comp (f : ℂ → UnitDisc) (z : ℂ) (w : UnitDisc) :
    deriv (fun x ↦ w.shift (f x) : ℂ → ℂ) z =
      (1 - ‖(w : ℂ)‖ ^ 2) / (1 + conj ↑w * f z) ^ 2 * deriv (f · : ℂ → ℂ) z := by
  by_cases hfd : DifferentiableAt ℂ (f · : ℂ → ℂ) z
  · exact (hasDerivAt_shift_comp w hfd.hasDerivAt).deriv
  · rw [deriv_zero_of_not_differentiableAt hfd, deriv_zero_of_not_differentiableAt, mul_zero]
    simpa using hfd

theorem UnitDisc.deriv_shift_comp_eq_zero (f : ℂ → UnitDisc) (z : ℂ) (w : UnitDisc) :
    deriv (fun x ↦ w.shift (f x) : ℂ → ℂ) z = 0 ↔ deriv (f · : ℂ → ℂ) z = 0 := by
  simp only [deriv_shift_comp, mul_eq_zero, div_eq_zero_iff, pow_eq_zero_iff two_ne_zero,
    shift_den_ne_zero, or_false]
  apply or_iff_right
  exact mod_cast sub_ne_zero.mpr w.sq_norm_lt_one.ne'

theorem exists_map_unitDisc_injOn_deriv_ne_zero₀ {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) {x : ℂ} (hx : x ∈ U) :
    ∃ f : ℂ → UnitDisc, f x = 0 ∧ InjOn f U ∧ (∀ z ∈ U, deriv (UnitDisc.coe ∘ f) z ≠ 0) := by
  classical
  obtain ⟨f, hf_inj, hf_deriv⟩ :
      ∃ f : ℂ → UnitDisc, InjOn f U ∧ ∀ z ∈ U, deriv (UnitDisc.coe ∘ f) z ≠ 0 := by
    rcases exists_mapsTo_unitBall_injOn_deriv_ne_zero_at hUo hUc hU hx with ⟨f, hfU, hf_inj, hdf⟩
    use fun z ↦ if hz : z ∈ U then .mk (f z) (by simpa using hfU hz) else 0
    constructor
    · simp +contextual [InjOn, UnitDisc.mk_inj, hf_inj.eq_iff]
    · intro z hz
      convert hdf z hz using 1
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hUo.mem_nhds hz] with w hw
      simp [hw]
  use fun z ↦ (-f x).shift (f z)
  refine ⟨?map_x, (-f x).shift.injective.comp_injOn hf_inj, ?deriv⟩
  case map_x => simp
  case deriv =>
    simpa only [Function.comp_def, ne_eq, UnitDisc.deriv_shift_comp_eq_zero]

theorem exist_map_unitDisc_injOn_norm_deriv_gt {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) {x : ℂ} (hx : x ∈ U) {f : ℂ → UnitDisc}
    (hdf : DifferentiableOn ℂ (UnitDisc.coe ∘ f) U) (hf₀ : f x = 0) (hf_inj : InjOn f U)
    (hsurj : ¬SurjOn f U univ) :
    ∃ g : ℂ → UnitDisc, g x = 0 ∧ InjOn g U ∧ DifferentiableOn ℂ (UnitDisc.coe ∘ g) U ∧
      ‖deriv (UnitDisc.coe ∘ f) x‖ < ‖deriv (UnitDisc.coe ∘ g) x‖ := by
  by_cases hdf₀ : deriv (UnitDisc.coe ∘ f) x = 0
  · rcases exists_map_unitDisc_injOn_deriv_ne_zero₀ hUo hUc hU hx with ⟨g, hg₀, hg_inj, hdg⟩
    refine ⟨g, hg₀, hg_inj, fun z hz ↦ ?_, ?_⟩
    · exact (differentiableAt_of_deriv_ne_zero (hdg z hz)).differentiableWithinAt
    · simpa [hdf₀] using hdg x hx
  obtain ⟨c, hc⟩ : ∃ c, ∀ z ∈ U, f z ≠ c := by simpa [SurjOn, eq_univ_iff_forall] using hsurj
  have hcf : ContinuousOn f U := by
    rw [UnitDisc.isEmbedding_coe.continuousOn_iff]
    exact hdf.continuousOn
  rcases UnitDisc.exists_continuousOn_pow_eq hUc hUo ((-c).continuous_shift.comp_continuousOn hcf)
    (by simpa) 2 with ⟨g, hgc, hgf⟩
  have hg₀ : ∀ z ∈ U, g z ≠ 0 := by
    intro z hz
    suffices g z ^ (2 : ℕ+) ≠ 0 by simpa using this
    simp [hgf, hc z hz]
  have hdg : ∀ z ∈ U, HasDerivAt (g · : ℂ → ℂ)
      ((1 - ‖(c : ℂ)‖ ^ 2) / (2 * g z * (1 - conj ↑c * f z) ^ 2) * deriv (f · : ℂ → ℂ) z) z := by
    intro z hz
    convert (hasDerivAt_pow 2 _).of_comp_left
      (UnitDisc.continuous_coe.continuousAt.comp <| hgc.continuousAt <| hUo.mem_nhds hz)
      (UnitDisc.hasDerivAt_shift_comp _ <| (hdf.hasDerivAt <| hUo.mem_nhds hz)) _
      (.of_forall fun x ↦ congr(UnitDisc.coe $(hgf x))) using 1
    · rfl
    · simp [Function.comp_def, field]
      ring
    · simp [hg₀ z hz]
  have hg_sq_norm (z : ℂ) : ‖(g z : ℂ)‖ ^ 2 = ‖((-c).shift (f z) : ℂ)‖ := by
    rw [← norm_pow, ← PNat.val_ofNat, ← UnitDisc.coe_pow, hgf, Function.comp_apply]
  have hg_norm (z : ℂ) : ‖(g z : ℂ)‖ = √‖((-c).shift (f z) : ℂ)‖ := by
    rw [← Real.sqrt_sq (norm_nonneg _), hg_sq_norm]
  refine ⟨(-g x).shift ∘ g, ?map_x, ?injOn, ?deriv, ?norm_deriv⟩
  case map_x => simp
  case injOn =>
    refine (-g x).shift.injective.comp_injOn fun z hz w hw hzw ↦ ?_
    simpa [hgf, hf_inj.eq_iff hz hw] using congr($hzw ^ (2 : ℕ+))
  case deriv =>
    exact (-g x).differentiableOn_shift_comp_iff.mpr fun z hz ↦
      (hdg z hz).differentiableAt.differentiableWithinAt
  case norm_deriv =>
    have hkey : ‖deriv (UnitDisc.coe ∘ ⇑(-g x).shift ∘ g) x‖ =
        ‖deriv (f · : ℂ → ℂ) x‖ * (√‖(c : ℂ)‖ + √‖(c⁻¹ : ℂ)‖) / 2 := by
      have hgx : ‖(g x : ℂ)‖ = √‖(c : ℂ)‖ := by simp [hg_norm, hf₀]
      simp only [Function.comp_def, UnitDisc.deriv_shift_comp, (hdg x hx).deriv, norm_mul, norm_div,
        ← mul_assoc, conj_mul', UnitDisc.coe_neg, map_neg, neg_mul]
      conv_rhs => rw [mul_comm, mul_div_right_comm]
      congr 1
      norm_cast
      have hpos₁ : 0 < 1 - ‖(c : ℂ)‖ := sub_pos.2 c.norm_lt_one
      have hpos₂ : 0 < 1 - ‖(c : ℂ)‖ ^ 2 := sub_pos.2 c.sq_norm_lt_one
      simp [field, hgx, hf₀, ← sub_eq_add_neg, abs_of_pos, hpos₁, hpos₂]
      ring
    rw [hkey, mul_div_assoc]
    apply lt_mul_of_one_lt_right
    · simpa using hdf₀
    · have hc₀ : 0 < ‖(c : ℂ)‖ := by simpa [hf₀] using (hc x hx).symm
      suffices √‖(c : ℂ)‖ * 2 < ‖(c : ℂ)‖ + 1 by simpa [field] using this
      have : √‖(c : ℂ)‖ ≠ 1 := by simp [c.norm_ne_one]
      rw [← sub_ne_zero, ← sq_pos_iff, sub_sq, Real.sq_sqrt] at this
      · linear_combination this
      · apply norm_nonneg

theorem uniformEquicontinuousOn_of_thickening_subset_of_forall_norm_le {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ι → E → F} {s U : Set E} {r : ℝ} (hr₀ : 0 < r) (hU : thickening r s ⊆ U)
    (hfd : ∀ i, DifferentiableOn ℂ (f i) U) (hf : ∃ C, ∀ i, ∀ z ∈ U, ‖f i z‖ ≤ C) :
    UniformEquicontinuousOn f s := by
  have hsU : s ⊆ U := (self_subset_thickening hr₀ _).trans hU
  rw [(uniformity_basis_dist.inf_principal _).uniformEquicontinuousOn_iff uniformity_basis_dist_le]
  intro ε hε
  rcases hf with ⟨C, hC⟩
  rcases exists_pos_mul_lt hε (2 * C / r) with ⟨δ, hδ₀, hδ⟩
  use min δ r, by positivity
  simp only [mem_ofPred, mem_inter_iff, prodMk_mem_set_prod_eq]
  rintro x y ⟨hdist, hx, hy⟩ i
  rw [lt_min_iff] at hdist
  rw [thickening_eq_biUnion_ball, iUnion₂_subset_iff] at hU
  calc
    dist (f i x) (f i y) ≤ (2 * C / r) * dist x y := by
      apply dist_le_div_mul_dist_of_mapsTo_ball
      · exact (hfd i).mono (hU _ hy)
      · intro z hz
        rw [mem_closedBall, two_mul]
        exact dist_le_norm_add_norm _ _ |>.trans <|
          add_le_add (hC _ _ <| hU y hy hz) (hC _ _ <| hsU hy)
      · exact hdist.2
    _ ≤ _ := by
      grw [hdist.1]
      · exact hδ.le
      · have := (norm_nonneg _).trans (hC i x (hsU hx))
        positivity

theorem equicontinuousAt_of_forall_norm_le {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ι → E → F} {U : Set E} {x : E} (hU : U ∈ 𝓝 x)
    (hfd : ∀ i, DifferentiableOn ℂ (f i) U) (hf : ∃ C, ∀ i, ∀ z ∈ U, ‖f i z‖ ≤ C) :
    EquicontinuousAt f x := by
  rcases nhds_basis_ball.mem_iff.mp hU with ⟨r, hr₀, hr⟩
  have : thickening (r / 2) (ball x (r / 2)) ⊆ U := by
    grw [Metric.thickening_ball]
    rwa [add_halves]
  have := uniformEquicontinuousOn_of_thickening_subset_of_forall_norm_le (by positivity) this
    hfd hf |>.equicontinuousOn x (by simpa)
  rwa [EquicontinuousWithinAt, nhdsWithin_eq_nhds.mpr (ball_mem_nhds _ (by positivity))] at this

open scoped UniformConvergence in
theorem exists_bijOn_unitBall_map_eq_zero {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hU : U ≠ univ) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ BijOn f U (ball 0 1) ∧ f x₀ = 0 := by
  set 𝔖 : Set (Set ℂ) := {K | K ⊆ U ∧ IsCompact K}
  set F : (ℂ →ᵤ[𝔖] ℂ) → (ℂ → ℂ) := fun f ↦ UniformOnFun.toFun _ f
  have hF : ∀ {f : ℂ →ᵤ[𝔖] ℂ} {s}, TendstoLocallyUniformlyOn F (F f) (𝓝[s] f) U := by
    intro f s
    have : Tendsto id (𝓝[s] f) (𝓝 f) := tendsto_id'.mpr nhdsWithin_le_nhds
    simpa [tendstoLocallyUniformlyOn_iff_forall_isCompact hUo,
      UniformOnFun.tendsto_iff_tendstoUniformlyOn, 𝔖] using this
  set s : Set (ℂ →ᵤ[𝔖] ℂ) :=
    {f : ℂ →ᵤ[𝔖] ℂ |
      MapsTo (F f) U (ball 0 1) ∧
      InjOn (F f) U ∧
      DifferentiableOn ℂ (F f) U ∧
      deriv (F f) x₀ ≠ 0 ∧
      F f x₀ = 0}
  have hsd : ∀ f ∈ s, DifferentiableOn ℂ (F f) U := fun f hf ↦ hf.2.2.1
  have hs_ne : s.Nonempty := by
    rcases exists_map_unitDisc_injOn_deriv_ne_zero₀ hUo hUc hU hx₀ with ⟨f, hf₀, hf_inj, hfd⟩
    exact ⟨UniformOnFun.ofFun 𝔖 (f ·), fun x hx ↦ (f x).2,
      by simpa [F, InjOn] using hf_inj, fun z hz ↦
        differentiableAt_of_deriv_ne_zero (hfd z hz) |>.differentiableWithinAt,
      hfd x₀ hx₀, by simp [F, hf₀]⟩
  have hcmpct := ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun _ ↦ And.right)
    (α := ℂ) (s := s) (F := F) .id ?eqcont ?bdd
  case eqcont =>
    rintro K ⟨hKU, -⟩ z hz
    refine equicontinuousAt_of_forall_norm_le (hUo.mem_nhds <| hKU hz) (fun i ↦ hsd _ i.2)
      ⟨1, fun i z hz ↦ le_of_lt ?_⟩ |>.equicontinuousWithinAt _
    simpa using i.2.1 hz
  case bdd =>
    intro K hK x hx
    exact ⟨closedBall 0 1, isCompact_closedBall _ _, fun i hi ↦
      ball_subset_closedBall <| hi.1 (hK.1 hx)⟩
  have hcl : closure s ⊆
      {f | MapsTo (F f) U (ball 0 1) ∧
           ((∃ C, EqOn (F f) (const ℂ C) U) ∨ InjOn (F f) U) ∧
           DifferentiableOn ℂ (F f) U ∧
           F f x₀ = 0} := by
    intro f hf
    rw [mem_closure_iff_nhdsWithin_neBot] at hf
    have htendsto : TendstoLocallyUniformlyOn F (F f) (𝓝[s] f) U := hF
    have hdf : DifferentiableOn ℂ (F f) U := htendsto.differentiableOn
      (eventually_mem_nhdsWithin.mono hsd) hUo
    have hf_le : ∀ z ∈ U, ‖F f z‖ ≤ 1 := by
      intro z hz
      refine le_of_tendsto (htendsto.tendsto_at hz).norm <| eventually_mem_nhdsWithin.mono ?_
      intro g hg
      apply le_of_lt
      simpa using hg.1 hz
    have hfx₀ : F f x₀ = 0 := by
      refine tendsto_nhds_unique (htendsto.tendsto_at hx₀) ?_
      refine tendsto_const_nhds.congr' <| eventually_mem_nhdsWithin.mono fun g hg ↦ ?_
      exact hg.2.2.2.2.symm
    refine ⟨?_, ?_, hdf, hfx₀⟩
    · by_contra hf_ball
      obtain ⟨z, hzU, hz⟩ : ∃ z ∈ U, 1 ≤ ‖F f z‖ := by simpa [MapsTo] using hf_ball
      have : IsMaxOn (‖F f ·‖) U z := by
        intro y hy
        simpa using (hf_le y hy).trans hz
      have : F f x₀ = F f z := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
        hUc.isPathConnected.isConnected.isPreconnected hUo hdf hzU this hx₀
      norm_num [← this, hfx₀] at hz
    · exact eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn hUo
        hUc.isPathConnected.isConnected.isPreconnected
        (eventually_mem_nhdsWithin.mono fun g hg ↦ hg.2.1)
        (eventually_mem_nhdsWithin.mono hsd)
        htendsto
  have hcont : ContinuousOn (fun f ↦ ‖deriv (F f) x₀‖) (closure s) := by
    refine .mono (.norm fun f hf ↦ ?_) hcl
    refine TendstoLocallyUniformlyOn.tendsto_at (.deriv hF ?_ hUo) hx₀
    refine eventually_mem_nhdsWithin.mono fun g hg ↦ ?_
    exact hg.2.2.1
  rcases hcmpct.exists_isMaxOn hs_ne.closure hcont with ⟨f₀, hf₀_mem, hf₀_max⟩
  have hdf₀_x₀ : 0 < ‖deriv (F f₀) x₀‖ := by
    rcases hs_ne with ⟨f', hf'⟩
    refine lt_of_lt_of_le ?_ (hf₀_max <| subset_closure hf')
    simpa using hf'.2.2.2.1
  rcases hcl hf₀_mem with ⟨hf₀_mapsTo, hf₀_inj, hf₀_diff, hf₀_x₀⟩
  replace hf₀_inj : InjOn (F f₀) U := by
    refine hf₀_inj.resolve_left ?_
    rintro ⟨C, hC⟩
    rw [hC.eventuallyEq_of_mem (hUo.mem_nhds hx₀) |>.deriv_eq] at hdf₀_x₀
    unfold const at hdf₀_x₀
    simp at hdf₀_x₀
  refine ⟨F f₀, hf₀_diff, ⟨hf₀_mapsTo, hf₀_inj, ?_⟩, hf₀_x₀⟩
  by_contra! hsurj
  clear hf₀_mem hdf₀_x₀
  rw [isMaxOn_iff] at hf₀_max
  wlog hf₀_lt : ∀ z, ‖F f₀ z‖ < 1 generalizing f₀
  · classical
    apply this (UniformOnFun.ofFun _ <| U.indicator (F f₀))
    · have : deriv (U.indicator (F f₀)) x₀ = deriv (F f₀) x₀ :=
        U.eqOn_indicator.eventuallyEq_of_mem (hUo.mem_nhds hx₀) |>.deriv_eq
      simpa [this, F] using hf₀_max
    · simpa [F, U.eqOn_indicator.mapsTo_iff]
    · simpa [F, differentiableOn_congr U.eqOn_indicator]
    · simp [F, hf₀_x₀]
    · simpa [F, U.eqOn_indicator.injOn_iff]
    · simpa [F, U.eqOn_indicator.surjOn_iff]
    · intro z
      by_cases hz : z ∈ U <;> simp [F, hz, mem_ball_zero_iff.mp (hf₀_mapsTo _)]
  lift F f₀ to ℂ → UnitDisc using hf₀_lt with f hf
  replace hsurj : ¬SurjOn f U univ := by
    simpa [SurjOn, eq_univ_iff_forall, subset_def, UnitDisc.exists, ← UnitDisc.coe_inj] using hsurj
  rcases exist_map_unitDisc_injOn_norm_deriv_gt hUo hUc hU hx₀ hf₀_diff (by simpa using hf₀_x₀)
    (by simpa [InjOn] using hf₀_inj) hsurj with ⟨g, hg₀, hg_inj, hdg, hg_lt⟩
  refine hf₀_max (UniformOnFun.ofFun _ (g · : ℂ → ℂ)) (subset_closure ?_) |>.not_gt hg_lt
  refine ⟨fun z _ ↦ (g z).2, by simpa [F, InjOn] using hg_inj, hdg, ?_, by simpa [F] using hg₀⟩
  rw [← norm_pos_iff]
  exact (norm_nonneg _).trans_lt hg_lt

end Complex
