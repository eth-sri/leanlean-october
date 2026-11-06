/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

Adapted from mathlib pull request 33505, commit
d43061d911b1aeae0788591da437a3b115098962, for Lean v4.35.0-rc2.
Upstream source: Mathlib/Analysis/Complex/RiemannMapping.lean
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Complex.UnitDisc.Basic
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

noncomputable section

@[expose] public section

namespace Complex

namespace UnitDisc

lemma shift_den_ne_zero (z w : 𝔻) : 1 + conj (z : ℂ) * w ≠ 0 :=
  (star z * w).one_add_coe_ne_zero

def shiftFun (z w : 𝔻) : 𝔻 :=
  mk ((z + w : ℂ) / (1 + conj ↑z * w)) <| by
    rw [norm_div, div_lt_one (norm_pos_iff.2 (shift_den_ne_zero z w)),
      ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
    have h : normSq (1 + conj (z : ℂ) * w) - normSq (z + w : ℂ) =
        (1 - normSq (z : ℂ)) * (1 - normSq (w : ℂ)) := by simp [normSq_apply]; ring
    linarith [mul_pos (sub_pos.2 z.normSq_lt_one) (sub_pos.2 w.normSq_lt_one)]

theorem shiftFun_eq_iff {z w u : 𝔻} : shiftFun z w = u ↔ (z + w : ℂ) = u + u * conj ↑z * w := by
  rw [← coe_inj, shiftFun, coe_mk, div_eq_iff (shift_den_ne_zero _ _)]; ring_nf

theorem shiftFun_neg_apply_shiftFun (z w : 𝔻) : shiftFun (-z) (shiftFun z w) = w := by
  rw [shiftFun_eq_iff, shiftFun, coe_mk, add_div_eq_mul_add_div, ← mul_div_assoc,
    add_div_eq_mul_add_div]
  · simp; ring
  all_goals exact shift_den_ne_zero z w

/-- The automorphism of the unit disc that sends zero to `z`. -/
def shift (z : 𝔻) : 𝔻 ≃ 𝔻 where
  toFun := shiftFun z
  invFun := shiftFun (-z)
  left_inv := shiftFun_neg_apply_shiftFun _
  right_inv w := by simpa using shiftFun_neg_apply_shiftFun (-z) w

theorem coe_shift (z w : 𝔻) : (shift z w : ℂ) = (z + w) / (1 + conj ↑z * w) := rfl

@[simp]
theorem shift_apply_zero (z : 𝔻) : shift z 0 = z := by simp [shift, shiftFun_eq_iff]

@[simp]
theorem shift_eq_zero_iff {z w : 𝔻} : shift z w = 0 ↔ w = -z := by
  rw [← Equiv.eq_symm_apply]; change w = shift (-z) 0 ↔ w = -z; simp

@[simp]
theorem shift_neg_apply_self (z : 𝔻) : shift (-z) z = 0 := by simp

@[fun_prop]
theorem continuous_shift (z : 𝔻) : Continuous z.shift := by
  simp only [isEmbedding_coe.continuous_iff, Function.comp_def, coe_shift]
  exact .div (by fun_prop) (by fun_prop) fun _ ↦ shift_den_ne_zero _ _

theorem hasDerivAt_shift_comp {f : ℂ → UnitDisc} {z f' : ℂ} (w : UnitDisc)
    (hf : HasDerivAt (fun x ↦ ↑(f x)) f' z) :
    HasDerivAt (fun x ↦ w.shift (f x) : ℂ → ℂ)
      ((1 - ‖(w : ℂ)‖ ^ 2) / (1 + conj ↑w * f z) ^ 2 * f') z := by
  simp only [coe_shift]
  convert (hf.const_add _).fun_div ((hf.const_mul _).const_add _)
    (shift_den_ne_zero _ _) using 1
  rw [← mul_conj']; ring

end UnitDisc

theorem exists_branch_sqrt {U : Set ℂ}
    (hUc : IsSimplyConnected U) (hUo : IsOpen U) {g : ℂ → ℂ} (hgc : ContinuousOn g U)
    (hU₀ : 0 ∉ g '' U) :
    ∃ f : ℂ → ℂ, ContinuousOn f U ∧ ∀ x, f x ^ 2 = g x := by
  classical
  have := hUc.simplyConnectedSpace
  have := hUo.locallyPathConnectedSpace
  rcases hUc.nonempty with ⟨x₀, hx₀U⟩
  have hx₀ : g x₀ ≠ 0 := ne_of_mem_of_not_mem (mem_image_of_mem g hx₀U) hU₀
  lift x₀ to U using hx₀U
  rcases isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    ⟨U.domRestrict g, continuousOn_iff_continuous_domRestrict.mp hgc⟩ (exp_log hx₀)
    (fun x ↦ ne_of_mem_of_not_mem (mem_image_of_mem g x.2) hU₀) with ⟨L, ⟨-, hL⟩, -⟩
  let f : ℂ → ℂ := fun z ↦ if hz : z ∈ U then L ⟨z, hz⟩ else 0
  have hfc : ContinuousOn f U := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert map_continuous L; ext z; simp [f]
  have hf (x : ℂ) (hx : x ∈ U) : exp (f x) = g x := by
    lift x to U using hx
    simpa [f, ContinuousMap.coe_mk, Set.domRestrict] using congr($hL x)
  refine ⟨U.piecewise (exp <| f · / 2) (g · ^ (1 / 2 : ℂ)), ?_, fun z ↦ ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict, domRestrict_piecewise,
      ← continuousOn_iff_continuous_domRestrict]
    fun_prop
  · by_cases hz : z ∈ U
    · simp [hz, ← exp_nat_mul, mul_div_cancel₀ (f z) two_ne_zero, ← hf z hz]
    · simp [hz, ← cpow_mul_nat]

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
  rcases exists_branch_sqrt hUc hUo continuousOn_id (by rwa [image_id])
    with ⟨f, hfc, hf_inv⟩
  replace hf_inv : LeftInverse (· ^ 2) f := hf_inv
  have hf₀ : ∀ z ∈ U, f z ≠ 0 := fun z hz hfz ↦ by
    simpa [hfz, (ne_of_mem_of_not_mem hz hU₀).symm] using hf_inv z
  have hdf : ∀ z ∈ U, HasStrictDerivAt f (2 * f z)⁻¹ z := fun z hz ↦
    HasStrictDerivAt.of_local_left_inverse (hfc.continuousAt <| hUo.mem_nhds hz)
      (by simpa using hasStrictDerivAt_pow 2 (f z)) (by simpa using hf₀ z hz)
      (.of_forall fun w ↦ hf_inv w)
  have hfUx : f '' U ∈ 𝓝 (f x) := by
    rw [← (hdf x hx).map_nhds_eq (by simpa using hf₀ x hx)]
    exact Filter.image_mem_map <| hUo.mem_nhds hx
  have hdisj : ∀ a ∈ U, ∀ b ∈ U, f a + f b ≠ 0 := fun a ha b hb hfab ↦ by
    obtain rfl : b = a := by
      rw [← hf_inv a, ← hf_inv b]; simp [eq_neg_iff_add_eq_zero.mpr hfab]
    exact hf₀ b hb (by linear_combination hfab / 2)
  have hfUxc : (f '' U)ᶜ ∈ 𝓝 (-f x) := by
    rw [nhds_neg, Filter.mem_neg]
    filter_upwards [hfUx]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    exact hdisj a ha b hb (by linear_combination hab)
  rcases Metric.nhds_basis_closedBall.mem_iff.mp hfUxc with ⟨ε, hε₀, hε⟩
  refine ⟨fun z ↦ ε / (f x + f z), fun z hz ↦ ?_, fun z hz w hw heq ↦ ?_, fun z hz ↦ ?_⟩
  · rw [mem_ball_zero_iff, norm_div, norm_real, Real.norm_of_nonneg hε₀.le,
      div_lt_one₀ (by simpa using hdisj x hx z hz)]
    by_contra! hle
    exact hε (by simpa [dist_eq_norm, add_comm] using hle) (mem_image_of_mem f hz)
  · simpa [div_eq_mul_inv, hε₀.ne', hf_inv.injective.eq_iff] using heq
  · rw [(hasDerivAt_const _ _).fun_div ((hdf z hz).hasDerivAt.const_add _) (hdisj x hx z hz) |>.deriv]
    simp [hε₀.ne', hf₀ z hz, hdisj x hx z hz]

open scoped UniformConvergence in
theorem exists_bijOn_unitBall_map_eq_zero {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hU : U ≠ univ) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ BijOn f U (ball 0 1) ∧ f x₀ = 0 := by
  set 𝔖 : Set (Set ℂ) := {K | K ⊆ U ∧ IsCompact K}
  have h𝔖K : ∀ K ∈ 𝔖, IsCompact K := fun _ ↦ And.right
  have hcnt : (𝓤 (ℂ →ᵤ[𝔖] ℂ)).IsCountablyGenerated := by
    have := hUo.locallyCompactSpace
    have : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
    set φ : CompactExhaustion U := default
    apply UniformOnFun.isCountablyGenerated_uniformity (t := fun n ↦ (↑) '' φ n)
    · exact fun n ↦ ⟨image_val_subset, φ.isCompact n |>.image continuous_subtype_val⟩
    · exact monotone_image.comp φ.subset
    · rintro K ⟨hKU, hKc⟩
      lift K to Set U using hKU
      rw [← Subtype.isCompact_iff] at hKc
      exact (φ.exists_superset_of_isCompact hKc).imp fun n hn ↦ by gcongr
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
    classical
    rcases exists_mapsTo_unitBall_injOn_deriv_ne_zero_at hUo hUc hU hx₀ with ⟨f₁, hfU, hf_inj, hdf⟩
    let f₂ : ℂ → UnitDisc := fun z ↦ if hz : z ∈ U then .mk (f₁ z) (by simpa using hfU hz) else 0
    have hf₂_inj : InjOn f₂ U := by simp +contextual [f₂, InjOn, UnitDisc.mk_inj, hf_inj.eq_iff]
    have hf₂_deriv (z : ℂ) (hz : z ∈ U) : deriv (UnitDisc.coe ∘ f₂) z ≠ 0 := by
      convert hdf z hz using 1
      exact Filter.EventuallyEq.deriv_eq <| (hUo.eventually_mem hz).mono fun w hw ↦ by simp [f₂, hw]
    let f : ℂ → UnitDisc := fun z ↦ (-f₂ x₀).shift (f₂ z)
    have hfd (z : ℂ) (hz : z ∈ U) : deriv (UnitDisc.coe ∘ f) z ≠ 0 := by
      have hd := (-f₂ x₀).hasDerivAt_shift_comp
        (differentiableAt_of_deriv_ne_zero (hf₂_deriv z hz)).hasDerivAt
      rw [Function.comp_def, hd.deriv]
      exact mul_ne_zero (div_ne_zero (mod_cast sub_ne_zero.mpr (-f₂ x₀).sq_norm_lt_one.ne')
        (pow_ne_zero 2 (UnitDisc.shift_den_ne_zero _ _))) (hf₂_deriv z hz)
    exact ⟨UniformOnFun.ofFun 𝔖 (f ·), fun x hx ↦ (f x).2,
      by simpa [F, f, InjOn] using (-f₂ x₀).shift.injective.comp_injOn hf₂_inj, fun z hz ↦
        differentiableAt_of_deriv_ne_zero (hfd z hz) |>.differentiableWithinAt,
      hfd x₀ hx₀, by simp [F, f]⟩
  have hcmpct := ArzelaAscoli.isCompact_closure_of_isClosedEmbedding h𝔖K (α := ℂ) (s := s) (F := F)
    .id ?eqcont ?bdd
  case eqcont =>
    rintro K ⟨hKU, -⟩ x hx
    refine EquicontinuousAt.equicontinuousWithinAt ?_ _
    rcases nhds_basis_ball.mem_iff.mp (hUo.mem_nhds <| hKU hx) with ⟨r, hr₀, hr⟩
    rw [nhds_basis_ball.equicontinuousAt_iff uniformity_basis_dist_le]
    intro ε hε
    rcases exists_pos_mul_lt hε (2 * 1 / r) with ⟨δ, hδ₀, hδ⟩
    refine ⟨min δ r, lt_min hδ₀ hr₀, fun y hy i ↦ ?_⟩
    rw [mem_ball, lt_min_iff] at hy
    have hC (z : ℂ) (hz : z ∈ U) : ‖F i z‖ ≤ 1 := le_of_lt (by simpa using i.2.1 hz)
    change dist (F i x) (F i y) ≤ ε
    rw [dist_comm]
    refine (dist_le_div_mul_dist_of_mapsTo_ball (R₂ := 2 * 1) ((hsd _ i.2).mono hr)
      (fun z hz ↦ ?_) hy.2).trans ?_
    · rw [mem_closedBall, two_mul]
      exact (dist_le_norm_add_norm _ _).trans (add_le_add (hC z (hr hz)) (hC x (hKU hx)))
    · grw [hy.1]; exact hδ.le
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
    have hf_le : ∀ z ∈ U, ‖F f z‖ ≤ 1 := fun z hz ↦
      le_of_tendsto (htendsto.tendsto_at hz).norm <|
        eventually_mem_nhdsWithin.mono fun g hg ↦ le_of_lt (by simpa using hg.1 hz)
    have hfx₀ : F f x₀ = 0 :=
      tendsto_nhds_unique (htendsto.tendsto_at hx₀) <|
        tendsto_const_nhds.congr' <| eventually_mem_nhdsWithin.mono fun g hg ↦ hg.2.2.2.2.symm
    have hUconn := hUc.isPathConnected.isConnected.isPreconnected
    refine ⟨?_, ?_, hdf, hfx₀⟩
    · by_contra hf_ball
      obtain ⟨z, hzU, hz⟩ : ∃ z ∈ U, 1 ≤ ‖F f z‖ := by simpa [MapsTo] using hf_ball
      have : IsMaxOn (‖F f ·‖) U z := fun y hy ↦ by simpa using (hf_le y hy).trans hz
      have : F f x₀ = F f z := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
        hUconn hUo hdf hzU this hx₀
      norm_num [← this, hfx₀] at hz
    · rw [or_iff_not_imp_left]
      intro hfU x hx y hy hxy
      by_contra! hne
      let f' : ℂ → ℂ := fun z ↦ F f z - F f y
      let F' : (ℂ →ᵤ[𝔖] ℂ) → ℂ → ℂ := fun i z ↦ F i z - F i y
      have hf_sub : TendstoLocallyUniformlyOn F' f' (𝓝[s] f) U :=
        htendsto.fun_sub <| TendstoUniformlyOn.tendstoLocallyUniformlyOn fun V hV ↦ by
          filter_upwards [(tendsto_left_nhds_uniformity (a := F f y)).comp
            (htendsto.tendsto_at hy) hV] with i hi z _ using hi
      have hFd : ∀ᶠ i in 𝓝[s] f, DifferentiableOn ℂ (F' i) U :=
        eventually_mem_nhdsWithin.mono fun i hi ↦ (hsd i hi).sub_const _
      have hfd : DifferentiableOn ℂ f' U := hdf.sub_const _
      have hfa : AnalyticAt ℂ f' x := hfd.analyticAt (hUo.mem_nhds hx)
      have hne_top : analyticOrderAt f' x ≠ ⊤ := fun h ↦
        hfU ⟨F f y, (hdf.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
          analyticOnNhd_const hUconn hx
          ((analyticOrderAt_eq_top.mp h).mono fun z hz ↦ sub_eq_zero.mp hz)⟩
      obtain ⟨g, hga, hgc, hfg⟩ := hfa.analyticOrderAt_ne_top.mp hne_top
      set n := analyticOrderNatAt f' x
      have hn : n ≠ 0 := by
        simp [n, f', analyticOrderNatAt, ENat.toNat_eq_zero, hne_top,
          hfa.analyticOrderAt_eq_zero, sub_eq_zero.mpr hxy]
      obtain ⟨r, hr₀, hr⟩ := Metric.nhds_basis_ball.eventually_iff.mp <|
        hga.eventually_analyticAt.and <| (hga.continuousAt.eventually_ne hgc).and <|
          hfg.and ((hUo.sdiff isClosed_singleton).eventually_mem ⟨hx, hne⟩)
      set R := r / 2
      have hR₀ : 0 < R := half_pos hr₀
      have hRr : closedBall x R ⊆ ball x r := closedBall_subset_ball (half_lt_self hr₀)
      have hRU : closedBall x R ⊆ U := fun z hz ↦ (hr (hRr hz)).2.2.2.1
      have hRU' : sphere x R ⊆ U := sphere_subset_closedBall.trans hRU
      have hgR : AnalyticOnNhd ℂ g (closedBall x R) := fun z hz ↦ (hr (hRr hz)).1
      have hg₀ : ∀ z ∈ closedBall x R, g z ≠ 0 := fun z hz ↦ (hr (hRr hz)).2.1
      have hzne : ∀ z ∈ sphere x R, z - x ≠ 0 := fun z hz ↦
        sub_ne_zero.mpr (ne_of_mem_sphere hz hR₀.ne')
      have hfR : ∀ z ∈ sphere x R, f' z ≠ 0 := fun z hz ↦ by
        rw [(hr (hRr (sphere_subset_closedBall hz))).2.2.1]
        exact mul_ne_zero (pow_ne_zero n (hzne z hz)) (hg₀ z (sphere_subset_closedBall hz))
      have hleft : EqOn (logDeriv f') (fun z ↦ (n : ℂ) / (z - x) + logDeriv g z) (sphere x R) := by
        intro z hz
        have hzr : z ∈ ball x r := hRr (sphere_subset_closedBall hz)
        have heq : f' =ᶠ[𝓝 z] fun w ↦ (w - x) ^ n * g w :=
          (isOpen_ball.eventually_mem hzr).mono fun w hw ↦ (hr hw).2.2.1
        rw [logDeriv_apply, heq.deriv_eq, heq.self_of_nhds, ← logDeriv_apply,
          logDeriv_fun_mul, logDeriv_fun_pow (by fun_prop), logDeriv, Pi.div_apply,
          deriv_sub_const, deriv_id'']
        · simp [div_eq_mul_inv]
        · exact pow_ne_zero n (hzne z hz)
        · exact hg₀ z (sphere_subset_closedBall hz)
        · fun_prop
        · exact (hgR z (sphere_subset_closedBall hz)).differentiableAt
      have hdg : AnalyticOnNhd ℂ (logDeriv g) (closedBall x R) := hgR.deriv.div hgR hg₀
      have hi : CircleIntegrable (fun z ↦ (n : ℂ) / (z - x)) x R := by
        simp only [div_eq_mul_inv]
        refine .const_mul (circleIntegrable_sub_inv_iff.mpr <| .inr fun hc' ↦ ?_) _
        exact hR₀.ne (by simpa [abs_of_pos hR₀] using hc')
      have hint : ∮ z in C(x, R), logDeriv f' z = (2 * π * I) * n := by
        rw [circleIntegral.integral_congr hR₀.le hleft,
          circleIntegral.integral_add hi
            (hdg.continuousOn.mono sphere_subset_closedBall |>.circleIntegrable hR₀.le),
          DiffContOnCl.circleIntegral_eq_zero hR₀.le
            (hdg.differentiableOn.diffContOnCl_ball subset_rfl),
          add_zero, circleIntegral_div_sub_of_differentiable_on_off_countable countable_empty
            (mem_ball_self hR₀) (by fun_prop) (fun _ _ ↦ by fun_prop)]
      have hlogDeriv : TendstoUniformlyOn (fun i ↦ logDeriv (F' i)) (logDeriv f')
          (𝓝[s] f) (sphere x R) := by
        rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere x R)]
        exact ((hf_sub.deriv hFd hUo).mono hRU').fun_div₀ (hf_sub.mono hRU')
          (hfd.analyticOnNhd hUo |>.deriv |>.continuousOn |>.mono hRU')
          (hfd.continuousOn.mono hRU') hfR
      have hcirc : Tendsto (fun i ↦ ∮ z in C(x, R), logDeriv (F' i) z) (𝓝[s] f)
          (𝓝 (∮ z in C(x, R), logDeriv f' z)) := by
        apply hlogDeriv.tendsto_circleIntegral_of_continuousOn hR₀.le
        filter_upwards [eventually_mem_nhdsWithin, hFd] with i hi hiD
        exact (hiD.analyticOnNhd hUo |>.deriv |>.continuousOn |>.mono hRU').div
          (hiD.continuousOn.mono hRU') fun z hz ↦ sub_ne_zero.mpr <|
            (hi.2.1.ne_iff (hRU' hz) hy).mpr (hr (hRr (sphere_subset_closedBall hz))).2.2.2.2
      have H₀ : ∀ᶠ i in 𝓝[s] f, ∮ z in C(x, R), logDeriv (F' i) z = 0 := by
        filter_upwards [eventually_mem_nhdsWithin, hFd] with i hi hid
        exact DiffContOnCl.circleIntegral_eq_zero hR₀.le
          (((hid.deriv hUo).mono hRU).div (hid.mono hRU)
            (fun z hz ↦ sub_ne_zero.mpr <|
              (hi.2.1.ne_iff (hRU hz) hy).mpr (hr (hRr hz)).2.2.2.2)
            |>.diffContOnCl_ball subset_rfl)
      have hzero := tendsto_const_nhds_iff.mp (hcirc.congr' H₀)
      rw [hint] at hzero
      exact mul_ne_zero (by simp [Real.pi_ne_zero]) (Nat.cast_ne_zero.mpr hn) hzero.symm
  have hcont : ContinuousOn (fun f ↦ ‖deriv (F f) x₀‖) (closure s) :=
    .mono (.norm fun f _ ↦ TendstoLocallyUniformlyOn.tendsto_at
      (.deriv hF (eventually_mem_nhdsWithin.mono fun _ hg ↦ hg.2.2.1) hUo) hx₀) hcl
  rcases hcmpct.exists_isMaxOn hs_ne.closure hcont with ⟨f₀, hf₀_mem, hf₀_max⟩
  have hdf₀_x₀ : 0 < ‖deriv (F f₀) x₀‖ := by
    rcases hs_ne with ⟨f', hf'⟩
    exact lt_of_lt_of_le (by simpa using hf'.2.2.2.1) (hf₀_max <| subset_closure hf')
  rcases hcl hf₀_mem with ⟨hf₀_mapsTo, hf₀_inj, hf₀_diff, hf₀_x₀⟩
  replace hf₀_inj : InjOn (F f₀) U := by
    refine hf₀_inj.resolve_left ?_
    rintro ⟨C, hC⟩
    rw [hC.eventuallyEq_of_mem (hUo.mem_nhds hx₀) |>.deriv_eq] at hdf₀_x₀
    unfold const at hdf₀_x₀; simp at hdf₀_x₀
  refine ⟨F f₀, hf₀_diff, ⟨hf₀_mapsTo, hf₀_inj, ?_⟩, hf₀_x₀⟩
  by_contra! hsurj
  clear hf₀_mem
  rw [isMaxOn_iff] at hf₀_max
  wlog hf₀_lt : ∀ z, ‖F f₀ z‖ < 1 generalizing f₀
  · classical
    have hderiv_eq : deriv (U.indicator (F f₀)) x₀ = deriv (F f₀) x₀ :=
      U.eqOn_indicator.eventuallyEq_of_mem (hUo.mem_nhds hx₀) |>.deriv_eq
    apply this (UniformOnFun.ofFun _ <| U.indicator (F f₀))
    · simpa [hderiv_eq, F] using hf₀_max
    · simpa [hderiv_eq, F] using hdf₀_x₀
    · simpa [F, U.eqOn_indicator.mapsTo_iff]
    · simpa [F, differentiableOn_congr U.eqOn_indicator]
    · simp [F, hf₀_x₀]
    · simpa [F, U.eqOn_indicator.injOn_iff]
    · simpa [F, U.eqOn_indicator.surjOn_iff]
    · intro z
      by_cases hz : z ∈ U <;> simp [F, hz, mem_ball_zero_iff.mp (hf₀_mapsTo _)]
  lift F f₀ to ℂ → UnitDisc using hf₀_lt with f hf
  obtain ⟨c, hc⟩ : ∃ c, ∀ z ∈ U, f z ≠ c := by
    simpa [SurjOn, eq_univ_iff_forall, subset_def, UnitDisc.exists, ← UnitDisc.coe_inj] using hsurj
  have hcf : ContinuousOn f U := UnitDisc.isEmbedding_coe.continuousOn_iff.mpr hf₀_diff.continuousOn
  rcases exists_branch_sqrt hUc hUo
    (UnitDisc.continuous_coe.comp_continuousOn ((-c).continuous_shift.comp_continuousOn hcf))
    (by simpa [Function.comp_def]) with ⟨g₀, hg₀c, hg₀f⟩
  have hg₀_lt (z : ℂ) : ‖g₀ z‖ < 1 := by
    rw [← sq_lt_one_iff₀ (norm_nonneg _), ← norm_pow, hg₀f]
    exact ((-c).shift (f z)).norm_lt_one
  lift g₀ to ℂ → UnitDisc using hg₀_lt with g
  have hgc : ContinuousOn g U := UnitDisc.isEmbedding_coe.continuousOn_iff.mpr hg₀c
  have hg₀ : ∀ z ∈ U, (g z : ℂ) ≠ 0 := fun z hz h ↦ by
    simpa [h, hc z hz] using (hg₀f z).symm
  have hdg : ∀ z ∈ U, HasDerivAt (g · : ℂ → ℂ)
      ((1 - ‖(c : ℂ)‖ ^ 2) / (2 * g z * (1 - conj ↑c * f z) ^ 2) * deriv (f · : ℂ → ℂ) z) z := by
    intro z hz
    convert (hasDerivAt_pow 2 _).of_comp_left
      (UnitDisc.continuous_coe.continuousAt.comp <| hgc.continuousAt <| hUo.mem_nhds hz)
      (UnitDisc.hasDerivAt_shift_comp _ <| (hf₀_diff.hasDerivAt <| hUo.mem_nhds hz)) _
      (.of_forall hg₀f) using 1
    · rfl
    · simp [field]; ring
    · simp [hg₀ z hz]
  have hg_norm (z : ℂ) : ‖(g z : ℂ)‖ = √‖((-c).shift (f z) : ℂ)‖ := by
    rw [← Real.sqrt_sq (norm_nonneg _), ← norm_pow, hg₀f]
    rfl
  have hf_zero : f x₀ = 0 := UnitDisc.coe_injective hf₀_x₀
  have hg_lt : ‖deriv (UnitDisc.coe ∘ f) x₀‖ < ‖deriv (UnitDisc.coe ∘ ((-g x₀).shift ∘ g)) x₀‖ := by
    have hkey : ‖deriv (UnitDisc.coe ∘ ⇑(-g x₀).shift ∘ g) x₀‖ =
        ‖deriv (f · : ℂ → ℂ) x₀‖ * (√‖(c : ℂ)‖ + √‖(c⁻¹ : ℂ)‖) / 2 := by
      have hgx : ‖(g x₀ : ℂ)‖ = √‖(c : ℂ)‖ := by simp [hg_norm, hf_zero]
      have hd_comp := ((-g x₀).hasDerivAt_shift_comp (hdg x₀ hx₀)).deriv
      simp only [Function.comp_def] at hd_comp ⊢
      rw [hd_comp]
      simp only [norm_mul, norm_div, ← mul_assoc, conj_mul', UnitDisc.coe_neg, map_neg, neg_mul]
      conv_rhs => rw [mul_comm, mul_div_right_comm]
      congr 1
      norm_cast
      have hpos₁ : 0 < 1 - ‖(c : ℂ)‖ := sub_pos.2 c.norm_lt_one
      have hpos₂ : 0 < 1 - ‖(c : ℂ)‖ ^ 2 := sub_pos.2 c.sq_norm_lt_one
      simp [field, hgx, hf_zero, ← sub_eq_add_neg, abs_of_pos, hpos₁, hpos₂]; ring
    rw [hkey, mul_div_assoc]
    apply lt_mul_of_one_lt_right hdf₀_x₀
    have hc₀ : 0 < ‖(c : ℂ)‖ := by simpa [hf_zero] using (hc x₀ hx₀).symm
    suffices √‖(c : ℂ)‖ * 2 < ‖(c : ℂ)‖ + 1 by simpa [field] using this
    have : √‖(c : ℂ)‖ ≠ 1 := by simp [c.norm_ne_one]
    rw [← sub_ne_zero, ← sq_pos_iff, sub_sq, Real.sq_sqrt (norm_nonneg _)] at this
    linear_combination this
  refine hf₀_max (UniformOnFun.ofFun _ (fun z ↦ ((-g x₀).shift (g z) : ℂ))) (subset_closure ?_) |>.not_gt hg_lt
  refine ⟨fun z _ ↦ ((-g x₀).shift (g z)).2, ?_, fun z hz ↦
    ((-g x₀).hasDerivAt_shift_comp (hdg z hz)).differentiableAt.differentiableWithinAt,
    norm_pos_iff.mp (hdf₀_x₀.trans hg_lt), by simp [F]⟩
  refine UnitDisc.coe_injective.comp_injOn <| (-g x₀).shift.injective.comp_injOn fun z hz w hw hzw ↦ ?_
  have hsq : ((-c).shift (f z) : ℂ) = (-c).shift (f w) := by
    have := (hg₀f z).symm.trans (by rw [hzw, hg₀f w])
    exact this
  exact hf₀_inj hz hw (congrArg UnitDisc.coe ((-c).shift.injective (UnitDisc.coe_injective hsq)))

end Complex

end
