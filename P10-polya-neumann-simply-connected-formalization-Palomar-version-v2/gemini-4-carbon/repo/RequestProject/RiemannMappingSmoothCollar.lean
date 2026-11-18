module

public import RequestProject.RiemannMappingSmoothBoundary
public import RequestProject.LocalDirichletNormalBootstrap
public import RequestProject.PhysicalHardySupport
public import RequestProject.CutFourier
public import RequestProject.ArcLength
public import RequestProject.LocalConformalArcFactorization
public import RequestProject.LocalConformalBoundaryGeometry
public import RequestProject.DiskHarmonicModes
public import RequestProject.LocalConformalH1
public import RequestProject.RiemannMappingInterior
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Calculus.Monotone
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PolyaNeumann

open Set Metric Filter Complex MeasureTheory
open scoped Topology ContDiff Real ComplexConjugate InnerProductSpace

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-! ### Boundary parametrization shifts and uniqueness up to shift -/

private def boundaryParamCircleMap (γ : ℝ → ℂ) : AddCircle (2 * Real.pi) → ℂ :=
  AddCircle.liftIco (2 * Real.pi) 0 γ

private theorem boundaryParamCircleMap_coe {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (θ : ℝ) :
    boundaryParamCircleMap γ (θ : AddCircle (2 * Real.pi)) = γ θ := by
  change γ (toIcoMod Real.two_pi_pos 0 θ) = γ θ
  rw [toIcoMod, hγ.periodic.sub_zsmul_eq]

private theorem boundaryParamCircleMap_injective {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) : Function.Injective (boundaryParamCircleMap γ) := fun q r hqr =>
  (AddCircle.equivIco (2 * Real.pi) 0).injective <| Subtype.ext <| hγ.injOn
    (by simpa only [zero_add] using (AddCircle.equivIco (2 * Real.pi) 0 q).property)
    (by simpa only [zero_add] using (AddCircle.equivIco (2 * Real.pi) 0 r).property) hqr

private theorem boundaryParam_eq_iff_circle_coe_eq {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (x y : ℝ) :
    γ x = γ y ↔ (x : AddCircle (2 * Real.pi)) = (y : AddCircle (2 * Real.pi)) :=
  ⟨fun hxy => boundaryParamCircleMap_injective hγ
    (by rwa [boundaryParamCircleMap_coe hγ x, boundaryParamCircleMap_coe hγ y]),
   fun hxy => by rw [← boundaryParamCircleMap_coe hγ x, ← boundaryParamCircleMap_coe hγ y, hxy]⟩

/-- A cyclic change of the starting point is again a positively oriented,
constant-speed parametrization of the boundary. -/
theorem IsBoundaryParam.shift {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (t : ℝ) :
    IsBoundaryParam Ω (fun θ => γ (θ + t)) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hper : Function.Periodic (fun θ => γ (θ + t)) (2 * Real.pi) := fun θ => by
    change γ ((θ + 2 * Real.pi) + t) = γ (θ + t)
    rw [show (θ + 2 * Real.pi) + t = (θ + t) + 2 * Real.pi by ring, hγ.periodic]
  refine ⟨⟨K, LipschitzWith.of_dist_le_mul fun x y => by simpa using hK.dist_le_mul (x + t) (y + t)⟩,
    hper, fun x hx y hy hxy => ?_, Subset.antisymm ?_ ?_, ?_, ?_⟩
  · refine hγ.injOn hx hy ((boundaryParam_eq_iff_circle_coe_eq hγ x y).mpr ?_)
    have h := (boundaryParam_eq_iff_circle_coe_eq hγ (x + t) (y + t)).mp hxy
    rwa [AddCircle.coe_add, AddCircle.coe_add, add_right_cancel_iff] at h
  · rintro _ ⟨θ, _, rfl⟩
    rw [← hγ.image]
    exact ⟨(AddCircle.equivIco (2 * Real.pi) 0 ((θ + t : ℝ) : AddCircle (2 * Real.pi)) : ℝ),
      Ico_subset_Icc_self (by simpa only [zero_add] using
        (AddCircle.equivIco (2 * Real.pi) 0 ((θ + t : ℝ) : AddCircle (2 * Real.pi))).property),
      boundaryParamCircleMap_coe hγ (θ + t)⟩
  · intro z hz
    rw [← hγ.image] at hz
    obtain ⟨s, _, rfl⟩ := hz
    let q : AddCircle (2 * Real.pi) := ((s - t : ℝ) : AddCircle (2 * Real.pi))
    refine ⟨(AddCircle.equivIco (2 * Real.pi) 0 q : ℝ),
      Ico_subset_Icc_self (by simpa only [zero_add] using
        (AddCircle.equivIco (2 * Real.pi) 0 q).property), ?_⟩
    dsimp only
    have hqcoe : ((AddCircle.equivIco (2 * Real.pi) 0 q : ℝ) : AddCircle (2 * Real.pi)) = q :=
      (AddCircle.equivIco (2 * Real.pi) 0).symm_apply_apply q
    refine (boundaryParam_eq_iff_circle_coe_eq hγ _ s).mpr ?_
    rw [AddCircle.coe_add, hqcoe, ← AddCircle.coe_add, sub_add_cancel]
  · obtain ⟨c, hc, hspeed⟩ := hγ.const_speed
    exact ⟨c, hc, by simpa only [deriv_comp_add_const] using
      (measurePreserving_add_right volume t).quasiMeasurePreserving.ae hspeed⟩
  · calc (∫ θ in (0 : ℝ)..(2 * Real.pi), signedAreaDensity (fun θ => γ (θ + t)) θ)
        = ∫ θ in (0 : ℝ)..(2 * Real.pi), signedAreaDensity γ (θ + t) :=
          intervalIntegral.integral_congr fun _ _ => by simp [signedAreaDensity, deriv_comp_add_const]
      _ = ∫ θ in t..t + 2 * Real.pi, signedAreaDensity γ θ := by
          rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm (2 * Real.pi) t]
      _ = 2 * (volume Ω).toReal := (integral_signedAreaDensity_shift hγ.periodic t).trans hγ.area

private def boundaryParamCircleHomeomorph {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) : AddCircle (2 * Real.pi) ≃ₜ frontier Ω :=
  let g : AddCircle (2 * Real.pi) → frontier Ω := fun q =>
    ⟨boundaryParamCircleMap γ q, by
      rw [← hγ.image]
      exact ⟨(AddCircle.equivIco (2 * Real.pi) 0 q : ℝ),
        Ico_subset_Icc_self (by simpa only [zero_add] using (AddCircle.equivIco (2 * Real.pi) 0 q).property),
        rfl⟩⟩
  have hfc : Continuous g :=
    let ⟨_, hK⟩ := hγ.lipschitz
    (AddCircle.liftIco_zero_continuous
      (by simpa only [zero_add] using (hγ.periodic 0).symm) hK.continuous.continuousOn).subtype_mk _
  (Equiv.ofBijective g ⟨fun q r hqr =>
    boundaryParamCircleMap_injective hγ (congrArg Subtype.val hqr), fun z => by
      obtain ⟨θ, _, hθz⟩ : (z : ℂ) ∈ γ '' Icc 0 (2 * Real.pi) := by rw [hγ.image]; exact z.property
      exact ⟨(θ : AddCircle (2 * Real.pi)),
        Subtype.ext ((boundaryParamCircleMap_coe hγ θ).trans hθz)⟩⟩).toHomeomorphOfContinuousClosed
    hfc hfc.isClosedMap

private theorem exists_boundaryParam_realHomeomorph {Ω : Set ℂ} {β γ : ℝ → ℂ}
    (hβ : IsBoundaryParam Ω β) (hγ : IsBoundaryParam Ω γ) :
    ∃ t ∈ Ico 0 (2 * Real.pi), ∃ T : ℝ ≃ₜ ℝ,
      T 0 = t ∧ ∀ θ : ℝ, γ θ = β (T θ) := by
  let e := (boundaryParamCircleHomeomorph hγ).trans (boundaryParamCircleHomeomorph hβ).symm
  letI : LocPathConnectedSpace ℝ := LocPathConnectedSpace.of_bases nhds_basis_Ioo
    fun x b hx => (convex_Ioo (𝕜 := ℝ) b.1 b.2).isPathConnected ⟨x, hx⟩
  let t : ℝ := AddCircle.equivIco (2 * Real.pi) 0 (e 0)
  have ht : t ∈ Ico 0 (2 * Real.pi) := by
    simpa only [zero_add] using (AddCircle.equivIco (2 * Real.pi) 0 (e 0)).property
  have htcoe : (t : AddCircle (2 * Real.pi)) = e 0 :=
    (AddCircle.equivIco (2 * Real.pi) 0).symm_apply_apply (e 0)
  let f : C(ℝ, AddCircle (2 * Real.pi)) :=
    ⟨fun θ => e (θ : AddCircle (2 * Real.pi)),
      e.continuous.comp (AddCircle.continuous_mk' (2 * Real.pi))⟩
  obtain ⟨T, hT, _⟩ := (AddCircle.isCoveringMap_coe (2 * Real.pi)).existsUnique_continuousMap_lifts
    f 0 t (by simpa only [f, ContinuousMap.coe_mk, QuotientAddGroup.mk_zero] using htcoe)
  have hTcoe (θ : ℝ) : (T θ : AddCircle (2 * Real.pi)) = e (θ : AddCircle (2 * Real.pi)) :=
    congrFun hT.2 θ
  let f' : C(ℝ, AddCircle (2 * Real.pi)) :=
    ⟨fun θ => e.symm (θ : AddCircle (2 * Real.pi)),
      e.symm.continuous.comp (AddCircle.continuous_mk' (2 * Real.pi))⟩
  obtain ⟨S, hS, _⟩ := (AddCircle.isCoveringMap_coe (2 * Real.pi)).existsUnique_continuousMap_lifts
    f' t 0 (by change (0 : AddCircle (2 * Real.pi)) = e.symm _; rw [htcoe, e.symm_apply_apply])
  have hScoe (θ : ℝ) : (S θ : AddCircle (2 * Real.pi)) = e.symm (θ : AddCircle (2 * Real.pi)) :=
    congrFun hS.2 θ
  have hST := (AddCircle.isCoveringMap_coe (2 * Real.pi)).eq_of_comp_eq
    (S.continuous.comp T.continuous) continuous_id
    (funext fun θ => by
      change (S (T θ) : AddCircle (2 * Real.pi)) = (θ : AddCircle (2 * Real.pi))
      rw [hScoe, hTcoe, e.symm_apply_apply])
    0 (by change S (T 0) = 0; rw [hT.1, hS.1])
  have hTS := (AddCircle.isCoveringMap_coe (2 * Real.pi)).eq_of_comp_eq
    (T.continuous.comp S.continuous) continuous_id
    (funext fun θ => by
      change (T (S θ) : AddCircle (2 * Real.pi)) = (θ : AddCircle (2 * Real.pi))
      rw [hTcoe, hScoe, e.apply_symm_apply])
    t (by change T (S t) = t; rw [hS.1, hT.1])
  refine ⟨t, ht, ⟨⟨T, S, congrFun hST, congrFun hTS⟩, T.continuous, S.continuous⟩, hT.1, fun θ => ?_⟩
  have hce : boundaryParamCircleMap β (e (θ : AddCircle (2 * Real.pi))) =
      boundaryParamCircleMap γ (θ : AddCircle (2 * Real.pi)) :=
    congrArg Subtype.val ((boundaryParamCircleHomeomorph hβ).apply_symm_apply
      (boundaryParamCircleHomeomorph hγ (θ : AddCircle (2 * Real.pi))))
  change γ θ = β (T θ)
  rw [← boundaryParamCircleMap_coe hγ θ, ← hce, ← hTcoe, boundaryParamCircleMap_coe hβ]

private theorem boundaryParamLift_locallyLipschitz {Ω : Set ℂ} {β γ : ℝ → ℂ}
    (hβ : ContDiff ℝ 1 β) (hnz : ∀ t, deriv β t ≠ 0)
    (hγ : IsBoundaryParam Ω γ) (T : ℝ ≃ₜ ℝ)
    (hcomp : ∀ θ : ℝ, γ θ = β (T θ)) : LocallyLipschitz (T : ℝ → ℝ) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  intro θ
  let t := T θ
  let c : ℂ := conj (deriv β t)
  let D : ℝ := Complex.normSq (deriv β t)
  let f : ℝ → ℝ := fun x => (c * β x).re
  have hD : 0 < D := Complex.normSq_pos.mpr (hnz t)
  have hc : 0 < ‖c‖ := by simpa only [c, Complex.norm_conj] using norm_pos_iff.mpr (hnz t)
  have hdf (x : ℝ) : HasDerivAt f (c * deriv β x).re x := by
    simpa only [f, Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (((hβ.differentiable_one x).hasDerivAt).const_mul c)
  have hopen : IsOpen {x : ℝ | D / 2 < (c * deriv β x).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_const.mul hβ.continuous_deriv_one))
  have htmem : t ∈ {x : ℝ | D / 2 < (c * deriv β x).re} := by
    show D / 2 < (c * deriv β t).re
    rw [show c * deriv β t = (D : ℂ) from Complex.normSq_eq_conj_mul_self.symm, Complex.ofReal_re]
    linarith
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds htmem)
  have hfc : Continuous f := Complex.continuous_re.comp (continuous_const.mul hβ.continuous)
  have hgrowth := (convex_Ioo (𝕜 := ℝ) (t - r) (t + r)).mul_sub_le_image_sub_of_le_deriv
    hfc.continuousOn (fun x _ => (hdf x).differentiableAt.differentiableWithinAt)
    fun x hx => by
      rw [(hdf x).deriv]
      have hx' := interior_subset hx
      exact (hball (Metric.mem_ball.mpr (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx'.1, hx'.2]))).le
  refine ⟨Real.toNNReal ((‖c‖ / (D / 2)) * (K : ℝ)), T ⁻¹' Ioo (t - r) (t + r),
    T.continuous.continuousAt.preimage_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)),
    LipschitzOnWith.of_dist_le' fun x hx y hy => ?_⟩
  have hp : D / 2 * |T x - T y| ≤ |f (T x) - f (T y)| := by
    rcases le_total (T x) (T y) with hxy | hyx
    · rw [abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub, abs_sub_comm]
      exact (hgrowth (T x) hx (T y) hy hxy).trans (le_abs_self _)
    · rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
      exact (hgrowth (T y) hy (T x) hx hyx).trans (le_abs_self _)
  have hpn : D / 2 * |T x - T y| ≤ ‖c‖ * ‖β (T x) - β (T y)‖ :=
    hp.trans <| by
      rw [show f (T x) - f (T y) = (c * (β (T x) - β (T y))).re by simp [f, mul_sub]]
      exact (Complex.abs_re_le_norm _).trans_eq (norm_mul _ _)
  have hbound : |T x - T y| ≤ (‖c‖ / (D / 2)) * ‖β (T x) - β (T y)‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (half_pos hD)]; linarith
  rw [Real.dist_eq]
  calc |T x - T y| ≤ (‖c‖ / (D / 2)) * ‖β (T x) - β (T y)‖ := hbound
    _ = (‖c‖ / (D / 2)) * dist (γ x) (γ y) := by rw [← hcomp x, ← hcomp y, dist_eq_norm]
    _ ≤ (‖c‖ / (D / 2)) * ((K : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left (hK.dist_le_mul x y) (div_nonneg hc.le (half_pos hD).le)
    _ = (‖c‖ / (D / 2) * (K : ℝ)) * dist x y := by ring

private theorem locallyLipschitz_eq_affine_of_ae_deriv {f : ℝ → ℝ} {a : ℝ}
    (hf : LocallyLipschitz f) (hd : ∀ᵐ θ : ℝ ∂volume, deriv f θ = a) (θ : ℝ) :
    f θ = a * θ + f 0 := by
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (s := uIcc 0 θ) isCompact_uIcc hf.locallyLipschitzOn
  have hFTC := hK.absolutelyContinuousOnInterval.integral_deriv_eq_sub
  rw [intervalIntegral.integral_congr_ae (hd.mono fun _ hs _ => hs),
    intervalIntegral.integral_const] at hFTC
  simp only [sub_zero, smul_eq_mul] at hFTC
  linarith

private theorem exists_boundaryParam_shift_of_bounded_domain {Ω : Set ℂ} {β γ : ℝ → ℂ}
    (hb : Bornology.IsBounded Ω) (hΩ : IsDomain Ω)
    (hβ : IsBoundaryParam Ω β) (hβC1 : ContDiff ℝ 1 β)
    (hnz : ∀ θ, deriv β θ ≠ 0) (hγ : IsBoundaryParam Ω γ) :
    ∃ t ∈ Icc 0 (2 * Real.pi), ∀ θ : ℝ, γ θ = β (θ + t) := by
  obtain ⟨t, ht, T, hT0, hcomp⟩ := exists_boundaryParam_realHomeomorph hβ hγ
  obtain ⟨cβ, hcβ, hβs0⟩ := hβ.const_speed
  have hβspeed : ∀ θ, ‖deriv β θ‖ = cβ :=
    congrFun (Measure.eq_of_ae_eq hβs0 hβC1.continuous_deriv_one.norm continuous_const)
  obtain ⟨cγ, hcγ, hγspeed⟩ := hγ.const_speed
  have haediff : ∀ᵐ θ : ℝ ∂volume, DifferentiableAt ℝ (T : ℝ → ℝ) θ := by
    obtain hT | hT := T.continuous.strictMono_of_inj T.injective
    · exact hT.monotone.ae_differentiableAt
    · exact (Monotone.ae_differentiableAt fun _ _ hxy => neg_le_neg (hT.antitone hxy)).mono
        fun θ hθ => by
          have hθ' := hθ.neg
          change DifferentiableAt ℝ (fun x => -(-T x)) θ at hθ'
          simpa only [neg_neg] using hθ'
  have habs : ∀ᵐ θ : ℝ ∂volume, |deriv (T : ℝ → ℝ) θ| = cγ / cβ := by
    filter_upwards [hγspeed, haediff] with θ hθ hTd
    have hchain : deriv γ θ = deriv (T : ℝ → ℝ) θ • deriv β (T θ) := by
      rw [funext hcomp]
      exact ((hβC1.differentiable_one (T θ)).hasDerivAt.scomp θ hTd.hasDerivAt).deriv
    refine (eq_div_iff hcβ.ne').mpr ?_
    calc |deriv (T : ℝ → ℝ) θ| * cβ = ‖deriv (T : ℝ → ℝ) θ • deriv β (T θ)‖ := by
          rw [norm_smul, Real.norm_eq_abs, hβspeed]
      _ = cγ := (congrArg norm hchain.symm).trans hθ
  have hLip := boundaryParamLift_locallyLipschitz hβC1 hnz hγ T hcomp
  obtain ⟨a, ha⟩ : ∃ a : ℝ, ∀ θ : ℝ, T θ = a * θ + T 0 := by
    obtain hmono | hanti := T.continuous.strictMono_of_inj T.injective
    · exact ⟨cγ / cβ, locallyLipschitz_eq_affine_of_ae_deriv hLip
        (habs.mono fun _ hθ => by rwa [abs_of_nonneg hmono.monotone.deriv_nonneg] at hθ)⟩
    · exact ⟨-(cγ / cβ), locallyLipschitz_eq_affine_of_ae_deriv hLip
        (habs.mono fun _ hθ => by rw [abs_of_nonpos hanti.antitone.deriv_nonpos] at hθ; linarith)⟩
  have hperne : 2 * Real.pi ≠ 0 := Real.two_pi_pos.ne'
  have hco := (boundaryParam_eq_iff_circle_coe_eq hβ (T (2 * Real.pi)) (T 0)).mp
    ((hcomp (2 * Real.pi)).symm.trans ((show γ (2 * Real.pi) = γ 0 by simpa using hγ.periodic 0).trans (hcomp 0)))
  have hzero : ((a * (2 * Real.pi) : ℝ) : AddCircle (2 * Real.pi)) = 0 := by
    have hsub : ((T (2 * Real.pi) - T 0 : ℝ) : AddCircle (2 * Real.pi)) = 0 := by
      rw [AddCircle.coe_sub, hco, sub_self]
    simpa only [ha (2 * Real.pi), add_sub_cancel_right] using hsub
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (2 * Real.pi)).mp hzero
  have hmR : (m : ℝ) = a := mul_right_cancel₀ hperne (by rwa [zsmul_eq_mul] at hm)
  let x : ℝ := T.symm (T 0 + 2 * Real.pi)
  have hTx : T x = T 0 + 2 * Real.pi := T.apply_symm_apply _
  have hxzero : (x : AddCircle (2 * Real.pi)) = 0 := by
    simpa using (boundaryParam_eq_iff_circle_coe_eq hγ x 0).mp
      (by rw [hcomp x, hTx, hβ.periodic (T 0), ← hcomp 0])
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (2 * Real.pi)).mp hxzero
  have hx : a * x = 2 * Real.pi := by linarith [ha x]
  have hmn : m * n = 1 := by
    exact_mod_cast (mul_right_cancel₀ hperne (calc
      ((m : ℝ) * (n : ℝ)) * (2 * Real.pi) = a * x := by rw [hmR, ← hn, zsmul_eq_mul]; ring
      _ = 1 * (2 * Real.pi) := by rw [hx, one_mul]))
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hmn with hm1 | hm1
  · have ha1 : a = 1 := by rw [← hmR, hm1, Int.cast_one]
    exact ⟨t, Ico_subset_Icc_self ht, fun θ => by rw [hcomp θ, ha θ, ha1, one_mul, hT0]⟩
  · exfalso
    have ha1 : a = -1 := by rw [← hmR, hm1, Int.cast_neg, Int.cast_one]
    have hfun : γ = fun θ => β (-θ + t) := funext fun θ => by
      rw [hcomp θ, ha θ, ha1, neg_one_mul, hT0]
    have hδ := hβ.shift t
    let δ : ℝ → ℂ := fun θ => β (θ + t)
    have hδa : (∫ θ in (0 : ℝ)..(2 * Real.pi), signedAreaDensity δ θ) = 2 * (volume Ω).toReal := hδ.area
    have hγa : (∫ θ in (0 : ℝ)..(2 * Real.pi), signedAreaDensity γ θ) = 2 * (volume Ω).toReal := hγ.area
    have hd : ∀ θ, signedAreaDensity (fun θ => β (-θ + t)) θ = -signedAreaDensity δ (-θ) :=
      fun θ => by change signedAreaDensity (fun θ => δ (-θ)) θ = _; simp [signedAreaDensity, deriv_comp_neg]
    have hrev : (∫ θ in (0 : ℝ)..(2 * Real.pi), signedAreaDensity γ θ) = -2 * (volume Ω).toReal := by
      rw [hfun]; simp_rw [hd]
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg (signedAreaDensity δ),
        neg_zero]
      have hs := integral_signedAreaDensity_shift hδ.periodic (-(2 * Real.pi))
      rw [neg_add_cancel] at hs
      rw [hs, hδa]; ring
    have hvolpos : 0 < (volume Ω).toReal :=
      ENNReal.toReal_pos (hΩ.1.measure_pos volume hΩ.2.nonempty).ne' hb.measure_lt_top.ne
    linarith

/-! ### Smooth Fourier collar extension from smooth circle trace -/

private def fourierCollarCutoff (t : ℝ) : ℝ := 1 - Real.smoothTransition t

private theorem fourierCollarCutoff_contDiff (N : ℕ∞) : ContDiff ℝ N fourierCollarCutoff :=
  contDiff_const.sub Real.smoothTransition.contDiff

private theorem fourierCollarCutoff_exists_finite_derivative_bound (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i ≤ k, ∀ t : ℝ, ‖iteratedFDeriv ℝ i fourierCollarCutoff t‖ ≤ C := by
  have h1 (i : ℕ) : ∃ B : ℝ, 1 ≤ B ∧ ∀ t : ℝ, ‖iteratedFDeriv ℝ i fourierCollarCutoff t‖ ≤ B := by
    obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
      (ContDiff.continuous_iteratedFDeriv' (fourierCollarCutoff_contDiff (i : ℕ∞))).continuousOn
    refine ⟨max 1 B, le_max_left _ _, fun t => ?_⟩
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · exact (hB t ht).trans (le_max_right _ _)
    · rcases lt_or_ge t 0 with ht0 | ht0
      · have heq : fourierCollarCutoff =ᶠ[𝓝 t] (fun _ : ℝ => (1 : ℝ)) :=
          (eventually_lt_nhds ht0).mono fun s hs => by
            simp [fourierCollarCutoff, Real.smoothTransition.zero_of_nonpos hs.le]
        rw [(heq.iteratedFDeriv ℝ i).eq_of_nhds]
        cases i with
        | zero => simpa only [norm_iteratedFDeriv_zero, norm_one] using le_max_left (1 : ℝ) B
        | succ i => simpa only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero] using (by positivity)
      · have heq : fourierCollarCutoff =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) :=
          (eventually_gt_nhds (lt_of_not_ge fun h => ht ⟨ht0, h⟩)).mono fun s hs => by
            simp [fourierCollarCutoff, Real.smoothTransition.one_of_one_le hs.le]
        rw [(heq.iteratedFDeriv ℝ i).eq_of_nhds]
        simpa only [iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero] using (by positivity)
  choose B hB hbound using h1
  exact ⟨max 1 (∑ i ∈ Finset.range (k + 1), B i), le_max_left _ _, fun i hi t =>
    (hbound i t).trans ((Finset.single_le_sum (fun j _ => by linarith [hB j])
      (Finset.mem_range.mpr (by omega))).trans (le_max_right _ _))⟩

private def fourierCollarRadialDefect (z : ℂ) : ℝ := ‖z‖ ^ 2 - 1

private def fourierCollarScaledDefect (n : ℕ) (z : ℂ) : ℝ := (n : ℝ) * fourierCollarRadialDefect z

private def fourierCollarTerm (n : ℕ) (z : ℂ) : ℂ :=
  z ^ n * (fourierCollarCutoff (fourierCollarScaledDefect n z) : ℂ)

private theorem fourierCollarTerm_contDiff (N : ℕ∞) (n : ℕ) : ContDiff ℝ N (fourierCollarTerm n) :=
  (contDiff_id.pow n).mul (Complex.ofRealCLM.contDiff.comp
    ((fourierCollarCutoff_contDiff N).comp
      (contDiff_const.mul ((contDiff_norm_sq ℂ).sub contDiff_const))))

private theorem fourierCollarTerm_exists_iteratedFDeriv_bound (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n → ∀ z : ℂ,
      ‖iteratedFDeriv ℝ k (fourierCollarTerm n) z‖ ≤ B * (n : ℝ) ^ k := by
  obtain ⟨C, hC, hχ⟩ := fourierCollarCutoff_exists_finite_derivative_bound k
  have hrad_cd (N : ℕ∞) : ContDiff ℝ N fourierCollarRadialDefect :=
    (contDiff_norm_sq ℂ).sub contDiff_const
  have hrad_bd (i : ℕ) : ∃ B : ℝ, 1 ≤ B ∧ ∀ z ∈ closedBall (0 : ℂ) 2,
      ‖iteratedFDeriv ℝ i fourierCollarRadialDefect z‖ ≤ B := by
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) 2).exists_bound_of_continuousOn
      (ContDiff.continuous_iteratedFDeriv' (hrad_cd (i : ℕ∞))).continuousOn
    exact ⟨max 1 B, le_max_left _ _, fun z hz => (hB z hz).trans (le_max_right _ _)⟩
  choose Br hBr hrad using hrad_bd
  let D := max 1 (∑ i ∈ Finset.range (k + 1), Br i)
  have hD : 1 ≤ D := le_max_left _ _
  have hq (i : ℕ) (hi : i ≤ k) (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 2) :
      ‖iteratedFDeriv ℝ i fourierCollarRadialDefect z‖ ≤ D :=
    (hrad i z hz).trans ((Finset.single_le_sum (fun j _ => by linarith [hBr j])
      (Finset.mem_range.mpr (by omega))).trans (le_max_right _ _))
  let B := ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * Real.exp (1 / 2 : ℝ) * ((k - i).factorial : ℝ) * C * D ^ (k - i)
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => by positivity
  refine ⟨B, hB, fun n hn z => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  by_cases hz : fourierCollarScaledDefect n z ≤ 1
  · have hr : ‖z‖ ^ 2 - 1 ≤ 1 / (n : ℝ) :=
      (le_div_iff₀ hn0).mpr (by dsimp [fourierCollarScaledDefect, fourierCollarRadialDefect] at hz; linarith)
    have hsup : ‖z‖ ^ 2 ≤ 1 + 1 / (n : ℝ) := by linarith
    have hz2 : z ∈ closedBall (0 : ℂ) 2 := by
      have : 1 / (n : ℝ) ≤ 1 := (div_le_one hn0).mpr hn1
      rw [mem_closedBall, dist_zero_right]; nlinarith [norm_nonneg z]
    have hpow_le (m : ℕ) (hm : m ≤ n) : ‖z‖ ^ m ≤ Real.exp (1 / 2 : ℝ) := by
      rcases le_or_gt ‖z‖ 1 with hr1 | hr1
      · exact (pow_le_one₀ (norm_nonneg z) hr1).trans (by linarith [Real.add_one_le_exp (1 / 2 : ℝ)])
      · have hl : (2 : ℝ) * Real.log ‖z‖ ≤ ‖z‖ ^ 2 - 1 := by
          simpa only [Real.log_pow, Nat.cast_ofNat] using
            Real.log_le_sub_one_of_pos (sq_pos_of_pos (lt_trans zero_lt_one hr1))
        have hmul := mul_le_mul_of_nonneg_right (hl.trans hr) hn0.le
        rw [show (1 / (n : ℝ)) * (n : ℝ) = 1 by field_simp [hn0.ne']] at hmul
        refine (pow_le_pow_right₀ hr1.le hm).trans ?_
        rw [show ‖z‖ ^ n = Real.exp ((n : ℝ) * Real.log ‖z‖) by
          rw [Real.exp_nat_mul, Real.exp_log (lt_trans zero_lt_one hr1)]]
        exact Real.exp_le_exp.mpr (by nlinarith)
    have hmon (i : ℕ) : ‖iteratedFDeriv ℝ i (fun w : ℂ => w ^ n) z‖ ≤
        (n : ℝ) ^ i * Real.exp (1 / 2 : ℝ) := by
      have hp : ContDiffAt ℂ i (fun w : ℂ => w ^ n) z := (contDiff_id.pow n).contDiffAt
      rw [← hp.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
      simp only [Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
        norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_pow, norm_mul,
        Complex.norm_natCast, norm_pow]
      exact mul_le_mul (by exact_mod_cast Nat.descFactorial_le_pow n i)
        (hpow_le _ (Nat.sub_le _ _)) (by positivity) (by positivity)
    have hsc_cd (N : ℕ∞) : ContDiff ℝ N (fourierCollarScaledDefect n) :=
      contDiff_const.mul (hrad_cd N)
    have hscaled (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ k) :
        ‖iteratedFDeriv ℝ i (fourierCollarScaledDefect n) z‖ ≤ ((n : ℝ) * D) ^ i := by
      change ‖iteratedFDeriv ℝ i (fun w => (n : ℝ) • fourierCollarRadialDefect w) z‖ ≤ _
      rw [iteratedFDeriv_const_smul_apply' (hrad_cd (i : ℕ∞)).contDiffAt, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hn0.le]
      exact (mul_le_mul_of_nonneg_left (hq i hi z hz2) hn0.le).trans
        (by simpa only [pow_one] using pow_le_pow_right₀ (by nlinarith : 1 ≤ (n : ℝ) * D) hi1)
    have hcut (j : ℕ) (hj : j ≤ k) :
        ‖iteratedFDeriv ℝ j
          (fun w : ℂ => (fourierCollarCutoff (fourierCollarScaledDefect n w) : ℂ)) z‖ ≤
          (j.factorial : ℝ) * C * ((n : ℝ) * D) ^ j := by
      have hc := norm_iteratedFDeriv_comp_le (fourierCollarCutoff_contDiff (j : ℕ∞))
        (hsc_cd (j : ℕ∞)) le_rfl z
        (fun i hi => hχ i (hi.trans hj) _) (fun i hi1 hi => hscaled i hi1 (hi.trans hj))
      have hnrm := Complex.ofRealLI.norm_iteratedFDeriv_comp_left (x := z)
        (((fourierCollarCutoff_contDiff (j : ℕ∞)).comp (hsc_cd (j : ℕ∞))).contDiffAt) le_rfl
      simpa only [Function.comp_def, Complex.ofRealLI_apply] using hnrm.le.trans hc
    have hprod := norm_iteratedFDeriv_mul_le
      (show ContDiff ℝ (k : ℕ∞) (fun w : ℂ => w ^ n) from contDiff_id.pow n)
      (Complex.ofRealCLM.contDiff.comp ((fourierCollarCutoff_contDiff (k : ℕ∞)).comp
        (hsc_cd (k : ℕ∞)))) z le_rfl
    change ‖iteratedFDeriv ℝ k (fun w : ℂ => w ^ n *
      (fourierCollarCutoff (fourierCollarScaledDefect n w) : ℂ)) z‖ ≤ _
    refine hprod.trans ?_
    dsimp [B]; rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hmul := mul_le_mul (hmon i) (hcut (k - i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun w : ℂ => w ^ n) z‖ *
          ‖iteratedFDeriv ℝ (k - i)
            (fun w : ℂ => (fourierCollarCutoff (fourierCollarScaledDefect n w) : ℂ)) z‖
        ≤ (k.choose i : ℝ) * ((n : ℝ) ^ i * Real.exp (1 / 2 : ℝ)) *
            (((k - i).factorial : ℝ) * C * ((n : ℝ) * D) ^ (k - i)) := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg _)
      _ = ((k.choose i : ℝ) * Real.exp (1 / 2 : ℝ) * ((k - i).factorial : ℝ) * C * D ^ (k - i)) *
          ((n : ℝ) ^ i * (n : ℝ) ^ (k - i)) := by rw [mul_pow]; ring
      _ = ((k.choose i : ℝ) * Real.exp (1 / 2 : ℝ) * ((k - i).factorial : ℝ) * C * D ^ (k - i)) *
          (n : ℝ) ^ k := by rw [← pow_add, Nat.add_sub_of_le hik]
  · have hgt : 1 < fourierCollarScaledDefect n z := lt_of_not_ge hz
    have heq : fourierCollarTerm n =ᶠ[𝓝 z] (fun _ : ℂ => (0 : ℂ)) := by
      filter_upwards [(isOpen_lt continuous_const
        ((contDiff_const.mul ((contDiff_norm_sq ℂ).sub contDiff_const) :
          ContDiff ℝ (0 : ℕ∞) (fourierCollarScaledDefect n)).continuous)).mem_nhds hgt] with w hw
      have hw' : 1 ≤ fourierCollarScaledDefect n w := hw.le
      simp only [fourierCollarTerm, fourierCollarCutoff,
        Real.smoothTransition.one_of_one_le hw', sub_self, Complex.ofReal_zero, mul_zero]
    rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
    simp only [iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero]
    exact mul_nonneg hB (pow_nonneg hn0.le _)

private def fourierCollarExtension (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  a 0 + ∑' n : ℕ, a (n + 1) • fourierCollarTerm (n + 1) z

private theorem exists_smooth_holomorphic_fourier_collar_of_circleTrace
    (F : ℂ → ℂ) (hF : DiffContOnCl ℂ F (ball (0 : ℂ) 1))
    (hΓ : ContDiff ℝ (⊤ : ℕ∞) (physicalCircleTrace F)) :
    ∃ G : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) G ∧
      EqOn G F (closedBall (0 : ℂ) 1) ∧ DifferentiableOn ℂ G (ball (0 : ℂ) 1) := by
  let f := physicalCircleTrace F
  have hp : Function.Periodic f (2 * Real.pi) := physicalCircleTrace_periodic F
  let a : ℕ → ℂ := fun n => fourierCoeffOn Real.two_pi_pos f (n : ℤ)
  have hper_it (k : ℕ) : Function.Periodic (iteratedDeriv k f) (2 * Real.pi) := by
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hp
    | succ k ih => simpa only [iteratedDeriv_succ] using deriv_periodic ih
  have hcd_it (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv k f) := by
    rw [iteratedDeriv_eq_iterate]; exact ContDiff.iterate_deriv k hΓ
  have hd_it (k : ℕ) (θ : ℝ) : HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f θ) θ := by
    have hk : ContDiff ℝ 1 (iteratedDeriv k f) := (hcd_it k).of_le (WithTop.coe_le_coe.mpr le_top)
    simpa only [iteratedDeriv_succ] using (hk.differentiable_one θ).hasDerivAt
  have hfour_it (k : ℕ) (n : ℤ) :
      fourierCoeffOn Real.two_pi_pos (iteratedDeriv k f) n =
        (Complex.I * (n : ℂ)) ^ k * fourierCoeffOn Real.two_pi_pos f n := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [fourierCoeffOn_deriv (hd_it k) (hcd_it (k + 1)).continuous
        (by simpa only [zero_add] using (hper_it k 0).symm), ih, pow_succ']; ring
  have hdecay (k : ℕ) : Summable (fun n : ℕ => ‖a (n + 1)‖ * ((n + 1 : ℕ) : ℝ) ^ k) := by
    have hinj_nat : Function.Injective (fun n : ℕ => ((n + 1 : ℕ) : ℤ)) :=
      fun _ _ h => Nat.add_right_cancel (Int.ofNat_injective h)
    have hs := (summable_norm_fourierCoeffOn_deriv (hd_it k) (hd_it (k + 1)) (hd_it (k + 1 + 1))
      (hcd_it (k + 1 + 1 + 1)).continuous
      (by simpa only [zero_add] using (hper_it k 0).symm)
      (by simpa only [zero_add] using (hper_it (k + 1) 0).symm)
      (by simpa only [zero_add] using (hper_it (k + 1 + 1) 0).symm)).comp_injective hinj_nat
    have hs' : Summable (fun n : ℕ => ‖a (n + 1)‖ * ((n + 1 : ℕ) : ℝ) ^ (k + 1)) :=
      hs.congr fun n => by
        change ‖fourierCoeffOn Real.two_pi_pos (iteratedDeriv (k + 1) f) ((n + 1 : ℕ) : ℤ)‖ = _
        rw [hfour_it (k + 1), norm_mul, norm_pow, norm_mul, Complex.norm_I, Complex.norm_intCast,
          one_mul, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]; dsimp [a]; ring
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) hs'
    have hb1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    simpa only [mul_one, pow_succ, mul_assoc] using
      mul_le_mul_of_nonneg_left hb1 (mul_nonneg (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
  choose B _ hbound using fourierCollarTerm_exists_iteratedFDeriv_bound
  have hGs : ContDiff ℝ (⊤ : ℕ∞) (fourierCollarExtension a) :=
    contDiff_const.add <| contDiff_tsum
      (v := fun k n => B k * (‖a (n + 1)‖ * ((n + 1 : ℕ) : ℝ) ^ k))
      (fun n => (fourierCollarTerm_contDiff (⊤ : ℕ∞) (n + 1)).const_smul (a (n + 1)))
      (fun k _ => (hdecay k).mul_left (B k))
      (fun k n z _ => by
        rw [iteratedFDeriv_const_smul_apply'
          (fourierCollarTerm_contDiff (k : ℕ∞) (n + 1)).contDiffAt, norm_smul]
        calc ‖a (n + 1)‖ * ‖iteratedFDeriv ℝ k (fourierCollarTerm (n + 1)) z‖
            ≤ ‖a (n + 1)‖ * (B k * ((n + 1 : ℕ) : ℝ) ^ k) :=
              mul_le_mul_of_nonneg_left (hbound k (n + 1) (by omega) z) (norm_nonneg _)
          _ = B k * (‖a (n + 1)‖ * ((n + 1 : ℕ) : ℝ) ^ k) := by ring)
  have hcauchy (n : ℕ) (z : ℂ) : cauchyPowerSeries F 0 1 n (fun _ => z) = a n * z ^ n := by
    have h1 : cauchyPowerSeries F 0 1 n (fun _ => (1 : ℂ)) = a n := by
      have hcirc : circleIntegral (fun w : ℂ => w⁻¹ ^ n * (w⁻¹ * F w)) 0 1 =
          Complex.I * ∫ θ in (0 : ℝ)..(2 * Real.pi),
            fourier (T := 2 * Real.pi) (-(n : ℤ)) (θ : AddCircle (2 * Real.pi)) * f θ := by
        rw [circleIntegral, ← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun θ _ => ?_
        have hz0 : circleMap 0 1 θ ≠ 0 := fun h => by
          have hh := norm_circleMap_zero 1 θ; simp [h] at hh
        have hfn : fourier (T := 2 * Real.pi) (-(n : ℤ)) (θ : AddCircle (2 * Real.pi)) =
            (circleMap 0 1 θ)⁻¹ ^ n := by
          have hp_pos : fourier (T := 2 * Real.pi) (n : ℤ) (θ : AddCircle (2 * Real.pi)) =
              (circleMap 0 1 θ) ^ n := by
            rw [fourier_coe_apply, circleMap_zero_pow]
            simp only [one_pow, circleMap_zero, Complex.ofReal_one, one_mul]
            congr 1; push_cast; field_simp [Real.pi_ne_zero]
          rw [fourier_neg, hp_pos, map_pow,
            ← Complex.inv_eq_conj (z := circleMap 0 1 θ) (by simp [norm_circleMap_zero])]
        change deriv (circleMap 0 1) θ •
          ((circleMap 0 1 θ)⁻¹ ^ n * ((circleMap 0 1 θ)⁻¹ * F (circleMap 0 1 θ))) =
          Complex.I * (fourier (T := 2 * Real.pi) (-(n : ℤ)) (θ : AddCircle (2 * Real.pi)) * f θ)
        rw [hfn]; simp only [deriv_circleMap, smul_eq_mul, f, physicalCircleTrace]; field_simp [hz0]
      simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_const,
        one_pow, sub_zero, smul_eq_mul]
      rw [hcirc, show a n = fourierCoeffOn Real.two_pi_pos f (n : ℤ) from rfl, fourierCoeffOn_eq_integral]
      simp only [sub_zero, smul_eq_mul, Complex.real_smul]
      rw [sub_zero]
      have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      push_cast; field_simp [hπ, Complex.I_ne_zero]
    simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_const,
      one_pow, smul_eq_mul, one_mul] at h1 ⊢
    rw [h1, mul_comm]
  have hEq : EqOn (fourierCollarExtension a) F (ball (0 : ℂ) 1) := fun w hw => by
    have hterm (m : ℕ) : fourierCollarTerm m w = w ^ m := by
      have hr : ‖w‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using ball_subset_closedBall hw
      have hq : fourierCollarScaledDefect m w ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
          (by dsimp [fourierCollarRadialDefect]; nlinarith [norm_nonneg w])
      simp [fourierCollarTerm, fourierCollarCutoff, Real.smoothTransition.zero_of_nonpos hq]
    have hs : HasSum (fun n : ℕ => a n * w ^ n) (F w) := by
      have hp_ser := hF.hasFPowerSeriesOnBall (R := (1 : NNReal)) (by norm_num)
      simpa only [sub_zero, NNReal.coe_one, hcauchy] using
        hp_ser.hasSum_sub (by simpa only [Metric.eball_coe, NNReal.coe_one] using hw)
    calc fourierCollarExtension a w
        = a 0 + ∑' n : ℕ, a (n + 1) * w ^ (n + 1) := by
          unfold fourierCollarExtension; congr 1; refine tsum_congr fun n => ?_
          rw [hterm (n + 1)]; rfl
      _ = ∑' n : ℕ, a n * w ^ n := by
          simpa only [pow_zero, mul_one] using hs.summable.tsum_eq_zero_add.symm
      _ = F w := hs.tsum_eq
  have hEqCl : EqOn (fourierCollarExtension a) F (closedBall (0 : ℂ) 1) :=
    hEq.of_subset_closure hGs.continuous.continuousOn hF.continuousOn_ball ball_subset_closedBall
      (by simpa only [closure_ball (0 : ℂ) one_ne_zero] using Subset.rfl)
  exact ⟨fourierCollarExtension a, hGs, hEqCl,
    hF.differentiableOn.congr fun z hz => hEqCl (ball_subset_closedBall hz)⟩

/-! ### Rectangular mixed-derivative boundary extension & inverse Riemann smoothness -/

private theorem rectangular_norm_add_sq_le (z w : ℂ) :
    ‖z + w‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
  have hs : ‖z + w‖ ^ 2 ≤ (‖z‖ + ‖w‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (norm_add_le z w)
  nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

private theorem rectangular_interval_sub_norm_sq_le {a b : ℝ} {v dv : ℝ → ℂ}
    (hv : ContinuousOn v (Ioo a b)) (hdv : ContinuousOn dv (Ioo a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt v (dv t) t)
    (hm : IntegrableOn (fun t => ‖dv t‖ ^ 2) (Ioo a b))
    {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    ‖v t - v s‖ ^ 2 ≤ |t - s| * ∫ r in Ioo a b, ‖dv r‖ ^ 2 := by
  have hord {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) (hst : s ≤ t) :
      ‖v t - v s‖ ^ 2 ≤ (t - s) * ∫ r in Ioo a b, ‖dv r‖ ^ 2 := by
    let μ := volume.restrict (Ioc s t)
    have hsub : Ioc s t ⊆ Ioo a b := fun r hr => ⟨hs.1.trans hr.1, hr.2.trans_lt ht.2⟩
    have hdL : MemLp dv 2 μ :=
      (memLp_two_iff_integrable_sq_norm
        ((hdv.mono hsub).aestronglyMeasurable measurableSet_Ioc)).mpr (hm.mono_set hsub)
    have hi : IntervalIntegrable dv volume s t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mpr (hdL.integrable (by norm_num))
    have hcc : Icc s t ⊆ Ioo a b := fun r hr => ⟨hs.1.trans_le hr.1, hr.2.trans_lt ht.2⟩
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst (hv.mono hcc)
      (fun r hr => hd r (hcc ⟨hr.1.le, hr.2.le⟩)) hi
    have h1 : MemLp (fun _ : ℝ => (1 : ℂ)) 2 μ := memLp_const 1
    have hinner : (∫ r in s..t, dv r) = inner ℂ (h1.toLp _) (hdL.toLp _) := by
      rw [intervalIntegral.integral_of_le hst, L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [h1.coeFn_toLp, hdL.coeFn_toLp] with r hr₁ hr₂
      simp only [hr₁, hr₂, RCLike.inner_apply, map_one, mul_one]
    have hn₂ := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      (hinner ▸ norm_inner_le_norm (h1.toLp _) (hdL.toLp _))
    have hconst : ‖h1.toLp _‖ ^ 2 = t - s := by
      rw [norm_sq_toLp_eq_integral]; simp [μ, Measure.real, hst]
    rw [mul_pow, hconst, norm_sq_toLp_eq_integral hdL, hFTC] at hn₂
    exact hn₂.trans (mul_le_mul_of_nonneg_left
      (integral_mono_measure (Measure.restrict_mono_set volume hsub)
        (Eventually.of_forall fun _ => sq_nonneg _) hm) (sub_nonneg.mpr hst))
  rcases le_total s t with hst | hts
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using hord hs ht hst
  · have h := hord ht hs hts
    rw [norm_sub_rev] at h
    simpa only [abs_of_nonpos (sub_nonpos.mpr hts), neg_sub] using h

private theorem rectangular_interval_point_norm_sq_le {a b : ℝ} (hab : a < b)
    {v dv : ℝ → ℂ} (hv : ContinuousOn v (Ioo a b)) (hdv : ContinuousOn dv (Ioo a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt v (dv t) t)
    (hmv : IntegrableOn (fun t => ‖v t‖ ^ 2) (Ioo a b))
    (hmd : IntegrableOn (fun t => ‖dv t‖ ^ 2) (Ioo a b))
    {t : ℝ} (ht : t ∈ Ioo a b) :
    ‖v t‖ ^ 2 ≤ (2 / (b - a)) * (∫ s in Ioo a b, ‖v s‖ ^ 2) +
      2 * (b - a) * (∫ s in Ioo a b, ‖dv s‖ ^ 2) := by
  have hE : 0 ≤ ∫ s in Ioo a b, ‖dv s‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hp (s : ℝ) (hs : s ∈ Ioo a b) :
      ‖v t‖ ^ 2 ≤ 2 * ‖v s‖ ^ 2 + 2 * (b - a) * (∫ r in Ioo a b, ‖dv r‖ ^ 2) := by
    have habs : |t - s| ≤ b - a := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [hs.1, ht.2]⟩
    have hdiff := (rectangular_interval_sub_norm_sq_le hv hdv hd hmd hs ht).trans
      (mul_le_mul_of_nonneg_right habs hE)
    have hsum := rectangular_norm_add_sq_le (v s) (v t - v s)
    rw [show v s + (v t - v s) = v t by abel] at hsum
    nlinarith
  have hi : Integrable (fun s => 2 * ‖v s‖ ^ 2 +
      2 * (b - a) * (∫ r in Ioo a b, ‖dv r‖ ^ 2)) (volume.restrict (Ioo a b)) :=
    (hmv.const_mul 2).add (integrable_const _)
  have hmean := integral_mono_ae (integrable_const (‖v t‖ ^ 2)) hi
    (ae_restrict_of_forall_mem measurableSet_Ioo hp)
  rw [integral_add (hmv.const_mul 2) (integrable_const _), integral_const_mul] at hmean
  simp only [integral_const, smul_eq_mul,
    show (volume.restrict (Ioo a b)).real univ = b - a by simp [Measure.real, hab.le]] at hmean
  refine (mul_le_mul_iff_of_pos_right (sub_pos.mpr hab)).mp ?_
  calc ‖v t‖ ^ 2 * (b - a)
      ≤ 2 * (∫ s in Ioo a b, ‖v s‖ ^ 2) + (b - a) * (2 * (b - a) * (∫ s in Ioo a b, ‖dv s‖ ^ 2)) := by
        nlinarith [hmean]
    _ = ((2 / (b - a)) * (∫ s in Ioo a b, ‖v s‖ ^ 2) +
        2 * (b - a) * (∫ s in Ioo a b, ‖dv s‖ ^ 2)) * (b - a) := by
        field_simp [(sub_pos.mpr hab).ne']

private def rectangularL2Energy (a b c d : ℝ) (f : ℝ × ℝ → ℂ) : ℝ :=
  ∫ p, ‖f p‖ ^ 2 ∂(volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))

private theorem rectangular_vertical_slice_energy {a b c d : ℝ} (hab : a < b)
    {f g : ℝ × ℝ → ℂ}
    (hf : ContinuousOn f (Ioo a b ×ˢ Ioo c d))
    (hg : ContinuousOn g (Ioo a b ×ˢ Ioo c d))
    (hd : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d, HasDerivAt (fun s => f (s, y)) (g (x, y)) x)
    (hfm : Integrable (fun p => ‖f p‖ ^ 2)
      ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))))
    (hgm : Integrable (fun p => ‖g p‖ ^ 2)
      ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))))
    {x : ℝ} (hx : x ∈ Ioo a b) :
    IntegrableOn (fun y => ‖f (x, y)‖ ^ 2) (Ioo c d) ∧
      (∫ y in Ioo c d, ‖f (x, y)‖ ^ 2) ≤
        (2 / (b - a)) * rectangularL2Energy a b c d f +
          2 * (b - a) * rectangularL2Energy a b c d g := by
  have hfvert : ContinuousOn (fun y => f (x, y)) (Ioo c d) :=
    hf.comp (continuous_const.prodMk continuous_id).continuousOn fun y hy => ⟨hx, hy⟩
  have hR : Integrable (fun y => (2 / (b - a)) * (∫ s in Ioo a b, ‖f (s, y)‖ ^ 2) +
      2 * (b - a) * (∫ s in Ioo a b, ‖g (s, y)‖ ^ 2)) (volume.restrict (Ioo c d)) :=
    (hfm.integral_prod_right.const_mul _).add (hgm.integral_prod_right.const_mul _)
  have hbound : ∀ᵐ y ∂volume.restrict (Ioo c d),
      ‖f (x, y)‖ ^ 2 ≤ (2 / (b - a)) * (∫ s in Ioo a b, ‖f (s, y)‖ ^ 2) +
        2 * (b - a) * (∫ s in Ioo a b, ‖g (s, y)‖ ^ 2) := by
    filter_upwards [hfm.prod_left_ae, hgm.prod_left_ae, ae_restrict_mem measurableSet_Ioo]
      with y hyf hyg hy
    exact rectangular_interval_point_norm_sq_le hab
      (hf.comp (continuous_id.prodMk continuous_const).continuousOn fun s hs => ⟨hs, hy⟩)
      (hg.comp (continuous_id.prodMk continuous_const).continuousOn fun s hs => ⟨hs, hy⟩)
      (fun s hs => hd s hs y hy) hyf hyg hx
  have hslice : IntegrableOn (fun y => ‖f (x, y)‖ ^ 2) (Ioo c d) :=
    hR.mono' ((hfvert.norm.pow 2).aestronglyMeasurable measurableSet_Ioo)
      (hbound.mono fun y hy => by
        change |‖f (x, y)‖ ^ 2| ≤ _; rw [abs_of_nonneg (sq_nonneg _)]; exact hy)
  refine ⟨hslice, ?_⟩
  have hi := integral_mono_ae hslice hR hbound
  rw [integral_add (hfm.integral_prod_right.const_mul _)
    (hgm.integral_prod_right.const_mul _), integral_const_mul, integral_const_mul] at hi
  simpa only [rectangularL2Energy, ← integral_prod_symm _ hfm, ← integral_prod_symm _ hgm] using hi

private def rectangularComplexCoord (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I

private theorem continuous_rectangularComplexCoord : Continuous rectangularComplexCoord :=
  (Complex.ofRealCLM.continuous.comp continuous_fst).add
    ((Complex.ofRealCLM.continuous.comp continuous_snd).mul continuous_const)

private theorem rectangularComplexCoord_mem_halfBox {a b : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Ioo (-a) a ×ˢ Ioo (0 : ℝ) b) :
    rectangularComplexCoord p ∈ smoothDirichletHalfBox a b := by
  simpa [smoothDirichletHalfBox, rectangularComplexCoord, abs_lt] using hp

private theorem rectangular_halfBox_horizontal_hasDerivAt {a b : ℝ} {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox a b))
    {x y : ℝ} (hx : x ∈ Ioo (-a) a) (hy : y ∈ Ioo (0 : ℝ) b) :
    HasDerivAt (fun s : ℝ => u (rectangularComplexCoord (s, y)))
      (dirD u 1 (rectangularComplexCoord (x, y))) x := by
  have hz := rectangularComplexCoord_mem_halfBox (show (x, y) ∈ Ioo (-a) a ×ˢ Ioo (0 : ℝ) b from ⟨hx, hy⟩)
  have hd := (hu.differentiableOn (by simp)).differentiableAt
    ((isOpen_smoothDirichletHalfBox a b).mem_nhds hz)
  exact hd.hasFDerivAt.comp_hasDerivAt x
    (by simpa only [rectangularComplexCoord, Complex.ofReal_one, id] using
      ((hasDerivAt_id x).ofReal_comp).add_const ((y : ℂ) * Complex.I))

private theorem dirichlet_halfBox_exists_continuous_extension {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {u : ℂ → ℂ} (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox a b))
    (hx : MemLp (dirD u 1) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hy : MemLp (dirD u Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hxy : MemLp (dirD (dirD u 1) Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    ∃ v : ℂ → ℂ, ContinuousOn v (smoothDirichletClosedHalfBox a b) ∧
      EqOn v u (smoothDirichletHalfBox a b) := by
  classical
  have hU := isOpen_smoothDirichletHalfBox a b
  have hx_cd := dirichlet_contDiffOn_dirD hU hs 1
  have hy_cd := dirichlet_contDiffOn_dirD hU hs Complex.I
  have hxy_cd := dirichlet_contDiffOn_dirD hU hx_cd Complex.I
  let R := Ioo (-a) a ×ˢ Ioo (0 : ℝ) b
  have hmap : MapsTo rectangularComplexCoord R (smoothDirichletHalfBox a b) :=
    fun _ hp => rectangularComplexCoord_mem_halfBox hp
  let U₀ := u ∘ rectangularComplexCoord
  let Ux := (dirD u 1) ∘ rectangularComplexCoord
  let Uy := (dirD u Complex.I) ∘ rectangularComplexCoord
  let Uxy := (dirD (dirD u 1) Complex.I) ∘ rectangularComplexCoord
  have hU₀c : ContinuousOn U₀ R := hs.continuousOn.comp continuous_rectangularComplexCoord.continuousOn hmap
  have hUxc : ContinuousOn Ux R := hx_cd.continuousOn.comp continuous_rectangularComplexCoord.continuousOn hmap
  have hUyc : ContinuousOn Uy R := hy_cd.continuousOn.comp continuous_rectangularComplexCoord.continuousOn hmap
  have hUxyc : ContinuousOn Uxy R := hxy_cd.continuousOn.comp continuous_rectangularComplexCoord.continuousOn hmap
  have hIx := dirichlet_halfBox_sq_integrable_real_prod hx
  have hIy := dirichlet_halfBox_sq_integrable_real_prod hy
  have hIxy := dirichlet_halfBox_sq_integrable_real_prod hxy
  have hab : -a < a := by linarith
  have hd_uy : ∀ x ∈ Ioo (-a) a, ∀ y ∈ Ioo (0 : ℝ) b, HasDerivAt (fun s => Uy (s, y)) (Uxy (x, y)) x := by
    intro x hx₀ y hy₀
    have hd := rectangular_halfBox_horizontal_hasDerivAt hy_cd hx₀ hy₀
    have hz := rectangularComplexCoord_mem_halfBox (show (x, y) ∈ R from ⟨hx₀, hy₀⟩)
    change HasDerivAt (fun s => dirD u Complex.I (rectangularComplexCoord (s, y)))
      (dirD (dirD u 1) Complex.I (rectangularComplexCoord (x, y))) x
    rwa [← dirichlet_dirD_comm hU hs hz Complex.I 1]
  have huc : UniformContinuousOn U₀ R := by
    let Bx := (2 / (b - 0)) * rectangularL2Energy (-a) a 0 b Ux +
      2 * (b - 0) * rectangularL2Energy (-a) a 0 b Uxy
    let By := (2 / (a - -a)) * rectangularL2Energy (-a) a 0 b Uy +
      2 * (a - -a) * rectangularL2Energy (-a) a 0 b Uxy
    have hEx : 0 ≤ rectangularL2Energy (-a) a 0 b Ux := integral_nonneg fun _ => sq_nonneg _
    have hEy : 0 ≤ rectangularL2Energy (-a) a 0 b Uy := integral_nonneg fun _ => sq_nonneg _
    have hExy : 0 ≤ rectangularL2Energy (-a) a 0 b Uxy := integral_nonneg fun _ => sq_nonneg _
    have hBx : 0 ≤ Bx := by dsimp [Bx]; positivity
    have hBy : 0 ≤ By := by dsimp [By]; positivity
    let C := 2 * Bx + 2 * By
    have hC : 0 ≤ C := by dsimp [C]; positivity
    rw [Metric.uniformContinuousOn_iff]
    intro ε hε
    refine ⟨ε ^ 2 / (C + 1), div_pos (sq_pos_of_pos hε) (by positivity), fun p hp q hq hpq => ?_⟩
    have hx_sl : IntegrableOn (fun x => ‖Ux (x, p.2)‖ ^ 2) (Ioo (-a) a) ∧
        (∫ x in Ioo (-a) a, ‖Ux (x, p.2)‖ ^ 2) ≤ Bx := by
      have h := rectangular_vertical_slice_energy hb
        (f := fun r : ℝ × ℝ => Ux (r.2, r.1)) (g := fun r : ℝ × ℝ => Uxy (r.2, r.1))
        (hUxc.comp continuous_swap.continuousOn fun _ hp' => ⟨hp'.2, hp'.1⟩)
        (hUxyc.comp continuous_swap.continuousOn fun _ hp' => ⟨hp'.2, hp'.1⟩)
        (fun t ht s hs' => dirichlet_halfBox_vertical_hasDerivAt hx_cd (abs_lt.mpr hs') ht)
        hIx.swap hIxy.swap hp.2
      rwa [show rectangularL2Energy 0 b (-a) a (fun r => Ux (r.2, r.1)) =
            rectangularL2Energy (-a) a 0 b Ux from integral_prod_swap (fun r => ‖Ux r‖ ^ 2),
          show rectangularL2Energy 0 b (-a) a (fun r => Uxy (r.2, r.1)) =
            rectangularL2Energy (-a) a 0 b Uxy from integral_prod_swap (fun r => ‖Uxy r‖ ^ 2)] at h
    obtain ⟨hyv, hby⟩ := rectangular_vertical_slice_energy hab hUyc hUxyc hd_uy hIy hIxy hq.1
    have hxsub : ‖U₀ p - U₀ (q.1, p.2)‖ ^ 2 ≤ |p.1 - q.1| * Bx := (rectangular_interval_sub_norm_sq_le
      (hU₀c.comp (continuous_id.prodMk continuous_const).continuousOn fun _ hs' => ⟨hs', hp.2⟩)
      (hUxc.comp (continuous_id.prodMk continuous_const).continuousOn fun _ hs' => ⟨hs', hp.2⟩)
      (fun s hs' => rectangular_halfBox_horizontal_hasDerivAt hs hs' hp.2)
      hx_sl.1 hq.1 hp.1).trans (mul_le_mul_of_nonneg_left hx_sl.2 (abs_nonneg _))
    have hysub : ‖U₀ (q.1, p.2) - U₀ q‖ ^ 2 ≤ |p.2 - q.2| * By := (rectangular_interval_sub_norm_sq_le
      (hU₀c.comp (continuous_const.prodMk continuous_id).continuousOn fun _ ht => ⟨hq.1, ht⟩)
      (hUyc.comp (continuous_const.prodMk continuous_id).continuousOn fun _ ht => ⟨hq.1, ht⟩)
      (fun t ht => dirichlet_halfBox_vertical_hasDerivAt hs (abs_lt.mpr hq.1) ht)
      hyv hq.2 hp.2).trans (mul_le_mul_of_nonneg_left hby (abs_nonneg _))
    have hsum := rectangular_norm_add_sq_le (U₀ p - U₀ (q.1, p.2)) (U₀ (q.1, p.2) - U₀ q)
    rw [show (U₀ p - U₀ (q.1, p.2)) + (U₀ (q.1, p.2) - U₀ q) = U₀ p - U₀ q by abel] at hsum
    have hfst : |p.1 - q.1| ≤ dist p q := by rw [Prod.dist_eq, ← Real.dist_eq]; exact le_max_left _ _
    have hsnd : |p.2 - q.2| ≤ dist p q := by rw [Prod.dist_eq, ← Real.dist_eq]; exact le_max_right _ _
    have hquad : ‖U₀ p - U₀ q‖ ^ 2 ≤ C * dist p q := by
      change ‖U₀ p - U₀ q‖ ^ 2 ≤ (2 * Bx + 2 * By) * dist p q
      nlinarith [hsum, hxsub, hysub,
        mul_le_mul_of_nonneg_right hfst hBx, mul_le_mul_of_nonneg_right hsnd hBy]
    have hsmall : dist p q * (C + 1) < ε ^ 2 := (lt_div_iff₀ (by positivity)).mp hpq
    rw [dist_eq_norm]
    nlinarith [(dist_nonneg : 0 ≤ dist p q), norm_nonneg (U₀ p - U₀ q)]
  let e : R → closure R := inclusion subset_closure
  have he : IsUniformInducing e := (isUniformEmbedding_set_inclusion subset_closure).isUniformInducing
  have hdense : DenseRange e := (denseRange_inclusion_iff subset_closure).mpr subset_rfl
  have huc' : UniformContinuous (fun p : R => U₀ p) := uniformContinuousOn_iff_restrict.mp huc
  let V : closure R → ℂ := (he.isDenseInducing hdense).extend (fun p : R => U₀ p)
  have hV : Continuous V := (uniformContinuous_uniformly_extend he hdense huc').continuous
  have hVe (p : R) : V (e p) = U₀ p := uniformly_extend_of_ind he hdense huc' p
  have hclosed : closure R = Icc (-a) a ×ˢ Icc (0 : ℝ) b := by
    dsimp [R]; rw [closure_prod_eq, closure_Ioo hab.ne, closure_Ioo hb.ne]
  let vR : ℝ × ℝ → ℂ := fun p => if hp : p ∈ closure R then V ⟨p, hp⟩ else 0
  have hvR : ContinuousOn vR (Icc (-a) a ×ˢ Icc (0 : ℝ) b) := by
    rw [← hclosed, continuousOn_iff_continuous_domRestrict]
    change Continuous (fun p : closure R => vR p)
    rw [show (fun p : closure R => vR p) = V from funext fun p => dif_pos p.property]
    exact hV
  refine ⟨fun z => vR (z.re, z.im),
    hvR.comp (Complex.continuous_re.prodMk Complex.continuous_im).continuousOn
      (fun z hz => ⟨abs_le.mp hz.1, hz.2⟩), fun z hz => ?_⟩
  have hzP : (z.re, z.im) ∈ R := ⟨abs_lt.mp hz.1, hz.2⟩
  have hpc : (z.re, z.im) ∈ closure R := subset_closure hzP
  have hzcoord : rectangularComplexCoord (z.re, z.im) = z := by
    apply Complex.ext <;> simp [rectangularComplexCoord]
  simpa only [vR, dif_pos hpc, U₀, Function.comp_apply, hzcoord] using hVe ⟨(z.re, z.im), hzP⟩

private theorem dirichlet_closed_halfBox_horizontal_mem {a b x y : ℝ}
    (hx : x ∈ Icc (-a) a) (hy : y ∈ Icc (0 : ℝ) b) :
    rectangularComplexCoord (x, y) ∈ smoothDirichletClosedHalfBox a b := by
  simpa only [rectangularComplexCoord, smoothDirichletClosedHalfBox, mem_setOf_eq,
    Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, zero_add,
    Complex.add_im, Complex.mul_im, mul_one] using
    (show |x| ≤ a ∧ 0 ≤ y ∧ y ≤ b from ⟨abs_le.mpr hx, hy⟩)

private theorem dirichlet_closed_halfBox_vertical_limit {a b : ℝ} (hb : 0 < b)
    {U : ℂ → ℂ} (hU : ContinuousOn U (smoothDirichletClosedHalfBox a b))
    {x : ℝ} (hx : |x| ≤ a) :
    Tendsto (fun y : ℝ => U (rectangularComplexCoord (x, y))) (𝓝[>] (0 : ℝ)) (𝓝 (U (x : ℂ))) := by
  have hx0 : (x : ℂ) ∈ smoothDirichletClosedHalfBox a b := by
    simpa only [rectangularComplexCoord, Complex.ofReal_zero, zero_mul, add_zero] using
      dirichlet_closed_halfBox_horizontal_mem (abs_le.mp hx) ⟨le_rfl, hb.le⟩
  have ht : Tendsto (fun y : ℝ => rectangularComplexCoord (x, y)) (𝓝[>] (0 : ℝ)) (𝓝 (x : ℂ)) := by
    have hc : Continuous (fun y : ℝ => rectangularComplexCoord (x, y)) :=
      continuous_rectangularComplexCoord.comp ((continuous_const : Continuous fun _ : ℝ => x).prodMk continuous_id)
    simpa only [rectangularComplexCoord, Complex.ofReal_zero, zero_mul, add_zero] using
      (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hm : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), rectangularComplexCoord (x, y) ∈ smoothDirichletClosedHalfBox a b := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with y hy hyb
    exact dirichlet_closed_halfBox_horizontal_mem (abs_le.mp hx) ⟨hy.le, hyb.le⟩
  exact (hU.continuousWithinAt hx0).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨ht, hm⟩)

private theorem dirichlet_boundary_horizontal_hasDerivAt {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {U Q : ℂ → ℂ}
    (hU : ContinuousOn U (smoothDirichletClosedHalfBox a b))
    (hQ : ContinuousOn Q (smoothDirichletClosedHalfBox a b))
    (hd : ∀ x ∈ Ioo (-a) a, ∀ y ∈ Ioo (0 : ℝ) b,
      HasDerivAt (fun s : ℝ => U (rectangularComplexCoord (s, y)))
        (Q (rectangularComplexCoord (x, y))) x)
    {x : ℝ} (hx : x ∈ Ioo (-a) a) :
    HasDerivAt (fun s : ℝ => U (s : ℂ)) (Q (x : ℂ)) x := by
  have hftc_le {s t : ℝ} (hs : s ∈ Ioo (-a) a) (ht : t ∈ Ioo (-a) a) (hst : s ≤ t) :
      (∫ u in s..t, Q (u : ℂ)) = U (t : ℂ) - U (s : ℂ) := by
    let μ := volume.restrict (Ioc s t)
    have hI : Icc s t ⊆ Ioo (-a) a := fun u hu => ⟨hs.1.trans_le hu.1, hu.2.trans_lt ht.2⟩
    have hrow (V : ℂ → ℂ) (hV : ContinuousOn V (smoothDirichletClosedHalfBox a b))
        (y : ℝ) (hy : y ∈ Icc (0 : ℝ) b) :
        ContinuousOn (fun u : ℝ => V (rectangularComplexCoord (u, y))) (Icc s t) :=
      hV.comp (continuous_rectangularComplexCoord.comp
        (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => y))).continuousOn
        fun u hu => dirichlet_closed_halfBox_horizontal_mem ⟨(hI hu).1.le, (hI hu).2.le⟩ hy
    obtain ⟨B, hB⟩ := (isCompact_smoothDirichletClosedHalfBox a b).exists_bound_of_continuousOn hQ
    have hmeas : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ),
        AEStronglyMeasurable (fun u : ℝ => Q (rectangularComplexCoord (u, y))) μ := by
      filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with y hy hyb
      exact ((hrow Q hQ y ⟨hy.le, hyb.le⟩).aestronglyMeasurable measurableSet_Icc).mono_measure
        (Measure.restrict_mono_set volume Ioc_subset_Icc_self)
    have hbound : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), ∀ᵐ u ∂μ, ‖Q (rectangularComplexCoord (u, y))‖ ≤ B := by
      filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with y hy hyb
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact hB _ (dirichlet_closed_halfBox_horizontal_mem
        ⟨(hI ⟨hu.1.le, hu.2⟩).1.le, (hI ⟨hu.1.le, hu.2⟩).2.le⟩ ⟨hy.le, hyb.le⟩)
    have hlim : ∀ᵐ u ∂μ, Tendsto (fun y : ℝ => Q (rectangularComplexCoord (u, y)))
        (𝓝[>] (0 : ℝ)) (𝓝 (Q (u : ℂ))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact dirichlet_closed_halfBox_vertical_limit hb hQ
        (abs_le.mpr ⟨(hI ⟨hu.1.le, hu.2⟩).1.le, (hI ⟨hu.1.le, hu.2⟩).2.le⟩)
    have hint : Tendsto (fun y : ℝ => ∫ u in s..t, Q (rectangularComplexCoord (u, y)))
        (𝓝[>] (0 : ℝ)) (𝓝 (∫ u in s..t, Q (u : ℂ))) := by
      simpa only [intervalIntegral.integral_of_le hst] using
        tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => B) hmeas hbound
          (integrable_const B) hlim
    have hvalues := (dirichlet_closed_halfBox_vertical_limit hb hU (abs_lt.mpr ht).le).sub
      (dirichlet_closed_halfBox_vertical_limit hb hU (abs_lt.mpr hs).le)
    refine tendsto_nhds_unique_of_eventuallyEq hint hvalues ?_
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with y hy hyb
    have hyy : y ∈ Icc (0 : ℝ) b := ⟨hy.le, hyb.le⟩
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst (hrow U hU y hyy)
      (fun u hu => hd u (hI ⟨hu.1.le, hu.2.le⟩) y ⟨hy, hyb⟩)
      ((hrow Q hQ y hyy).intervalIntegrable_of_Icc hst)
  let clamp : ℝ → ℝ := fun s => max (-a) (min a s)
  let q : ℝ → ℂ := fun s => Q ((clamp s : ℝ) : ℂ)
  have hqc : Continuous q := continuousOn_univ.mp <|
    hQ.comp (Complex.continuous_ofReal.comp (continuous_const.max (continuous_const.min continuous_id))).continuousOn
      fun s _ => by
        simpa only [rectangularComplexCoord, Complex.ofReal_zero, zero_mul, add_zero, Function.comp_apply] using
          dirichlet_closed_halfBox_horizontal_mem
            ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩ ⟨le_rfl, hb.le⟩
  let P : ℝ → ℂ := fun s => U (0 : ℂ) + ∫ t in (0 : ℝ)..s, q t
  have hP : HasDerivAt P (Q (x : ℂ)) x := by
    rw [show Q (x : ℂ) = q x by dsimp [q, clamp]; rw [min_eq_right hx.2.le, max_eq_right hx.1.le]]
    exact (intervalIntegral.integral_hasDerivAt_right (hqc.intervalIntegrable 0 x)
      hqc.aestronglyMeasurable.stronglyMeasurableAtFilter hqc.continuousAt).const_add (U 0)
  refine hP.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hx] with s hs
  have h0 : (0 : ℝ) ∈ Ioo (-a) a := ⟨by linarith, ha⟩
  have hinterval : uIcc (0 : ℝ) s ⊆ Icc (-a) a := uIcc_subset_Icc ⟨by linarith, ha.le⟩ ⟨hs.1.le, hs.2.le⟩
  have hi : (∫ t in (0 : ℝ)..s, q t) = ∫ t in (0 : ℝ)..s, Q (t : ℂ) :=
    intervalIntegral.integral_congr fun t ht => by
      dsimp [q, clamp]; rw [min_eq_right (hinterval ht).2, max_eq_right (hinterval ht).1]
  have hftc : (∫ t in (0 : ℝ)..s, Q (t : ℂ)) = U (s : ℂ) - U ((0 : ℝ) : ℂ) := by
    by_cases h0s : 0 ≤ s
    · exact hftc_le h0 hs h0s
    · rw [intervalIntegral.integral_symm, hftc_le hs h0 (le_of_not_ge h0s), neg_sub]
  dsimp only [P]; rw [hi, hftc, Complex.ofReal_zero]; abel

private theorem dirichlet_boundary_extension_hasDerivAt {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {u U Q : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox a b))
    (hU : ContinuousOn U (smoothDirichletClosedHalfBox a b))
    (hUu : EqOn U u (smoothDirichletHalfBox a b))
    (hQ : ContinuousOn Q (smoothDirichletClosedHalfBox a b))
    (hQu : EqOn Q (dirD u 1) (smoothDirichletHalfBox a b))
    {x : ℝ} (hx : x ∈ Ioo (-a) a) :
    HasDerivAt (fun s : ℝ => U (s : ℂ)) (Q (x : ℂ)) x := by
  refine dirichlet_boundary_horizontal_hasDerivAt ha hb hU hQ (fun t ht y hy => ?_) hx
  have hd := rectangular_halfBox_horizontal_hasDerivAt hs ht hy
  have heq : (fun s : ℝ => U (rectangularComplexCoord (s, y))) =ᶠ[𝓝 t]
      (fun s => u (rectangularComplexCoord (s, y))) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs'
    exact hUu (rectangularComplexCoord_mem_halfBox
      (show (s, y) ∈ Ioo (-a) a ×ˢ Ioo (0 : ℝ) b from ⟨hs', hy⟩))
  rw [hQu (rectangularComplexCoord_mem_halfBox (show (t, y) ∈ Ioo (-a) a ×ˢ Ioo (0 : ℝ) b from ⟨ht, hy⟩))]
  exact hd.congr_of_eventuallyEq heq

private theorem dirichlet_boundary_derivative_chain_contDiffOn {s : Set ℝ} (hs : IsOpen s)
    (n : ℕ) (v : ℕ → ℝ → ℂ)
    (hc : ∀ j ≤ n, ContinuousOn (v j) s)
    (hd : ∀ j < n, ∀ x ∈ s, HasDerivAt (v j) (v (j + 1) x) x) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (v 0) s := by
  induction n generalizing v with
  | zero => exact contDiffOn_zero.mpr (hc 0 (by omega))
  | succ n ih =>
    have hnext := ih (fun j => v (j + 1)) (fun j hj => hc (j + 1) (by omega))
      (fun j hj x hx => hd (j + 1) (by omega) x hx)
    have hsucc : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) (v 0) s :=
      (contDiffOn_succ_iff_deriv_of_isOpen hs).mpr
        ⟨fun x hx => (hd 0 (by omega) x hx).differentiableAt.differentiableWithinAt,
          by simp, hnext.congr fun x hx => (hd 0 (by omega) x hx).deriv⟩
    simpa only [Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hsucc

private theorem dirichlet_mixed_exists_continuous_extension {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) {u : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox a b)) (N p q : ℕ)
    (hm : ∀ j k : ℕ, j + k ≤ N → MemLp (dirichletMixedDerivative j k u) 2
      (volume.restrict (smoothDirichletHalfBox a b)))
    (horder : p + q + 2 ≤ N) :
    ∃ U : ℂ → ℂ, ContinuousOn U (smoothDirichletClosedHalfBox a b) ∧
      EqOn U (dirichletMixedDerivative p q u) (smoothDirichletHalfBox a b) := by
  have hW := isOpen_smoothDirichletHalfBox a b
  have hy (j k : ℕ) (hjk : j + k + 1 ≤ N) :
      MemLp (dirD (dirichletMixedDerivative j k u) Complex.I) 2
        (volume.restrict (smoothDirichletHalfBox a b)) :=
    (hm j (k + 1) (by omega)).ae_eq <|
      (ae_restrict_mem hW.measurableSet).mono fun z hz =>
        (dirD_dirichletMixedDerivative_I_eqOn hW hs j k hz).symm
  have hx : MemLp (dirD (dirichletMixedDerivative p q u) 1) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
    rw [dirD_dirichletMixedDerivative_one]; exact hm (p + 1) q (by omega)
  have hxy : MemLp (dirD (dirD (dirichletMixedDerivative p q u) 1) Complex.I) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
    rw [dirD_dirichletMixedDerivative_one]; exact hy (p + 1) q (by omega)
  exact dirichlet_halfBox_exists_continuous_extension ha hb
    (dirichletMixedDerivative_contDiffOn hW hs p q) hx (hy p q (by omega)) hxy

private theorem dirichlet_mixed_boundary_contDiffAt_of_finite_energy {A b a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) {u U : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    (p q : ℕ)
    (hhigh : ∀ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
      ∀ j k : ℕ, j + k ≤ N → MemLp (dirichletMixedDerivative j k u) 2
        (volume.restrict (smoothDirichletHalfBox ρ ρ)))
    (hU : ContinuousOn U (smoothDirichletClosedHalfBox a β))
    (hUu : EqOn U (dirichletMixedDerivative p q u) (smoothDirichletHalfBox a β)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => U (x : ℂ)) 0 := by
  refine contDiffAt_infty.mpr fun n => ?_
  obtain ⟨ρ, hρ, hρA, hρb, hm⟩ := hhigh (p + q + n + 2)
  have hsρ : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox ρ ρ) :=
    hs.mono fun z hz => ⟨hz.1.trans (by linarith), hz.2.1, hz.2.2.trans hρb⟩
  have hex : ∀ j : ℕ, ∃ W : ℂ → ℂ, j ≤ n →
      ContinuousOn W (smoothDirichletClosedHalfBox ρ ρ) ∧
        EqOn W (dirichletMixedDerivative (p + j) q u) (smoothDirichletHalfBox ρ ρ) := fun j => by
    by_cases hj : j ≤ n
    · obtain ⟨W, hWc, hWu⟩ := dirichlet_mixed_exists_continuous_extension
        hρ hρ hsρ (p + q + n + 2) (p + j) q hm (by omega)
      exact ⟨W, fun _ => ⟨hWc, hWu⟩⟩
    · exact ⟨0, fun hj' => False.elim (hj hj')⟩
  choose V hV using hex
  have hd : ∀ j < n, ∀ x ∈ Ioo (-ρ) ρ,
      HasDerivAt (fun s : ℝ => V j (s : ℂ)) (V (j + 1) (x : ℂ)) x := fun j hj x hx => by
    have hVu : EqOn (V (j + 1)) (dirD (dirichletMixedDerivative (p + j) q u) 1)
        (smoothDirichletHalfBox ρ ρ) := by
      rw [dirD_dirichletMixedDerivative_one]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (hV (j + 1) (by omega)).2
    exact dirichlet_boundary_extension_hasDerivAt hρ hρ
      (dirichletMixedDerivative_contDiffOn (isOpen_smoothDirichletHalfBox ρ ρ) hsρ (p + j) q)
      (hV j (by omega)).1 (hV j (by omega)).2 (hV (j + 1) (by omega)).1 hVu hx
  have hVc := dirichlet_boundary_derivative_chain_contDiffOn isOpen_Ioo n
    (fun j x => V j (x : ℂ))
    (fun j hj => (hV j hj).1.comp Complex.continuous_ofReal.continuousOn fun x hx => by
      simpa only [rectangularComplexCoord, Complex.ofReal_zero, zero_mul, add_zero] using
        dirichlet_closed_halfBox_horizontal_mem ⟨hx.1.le, hx.2.le⟩ ⟨le_rfl, hρ.le⟩) hd
  have hV₀ : EqOn (V 0) (dirichletMixedDerivative p q u) (smoothDirichletHalfBox ρ ρ) := by
    simpa only [Nat.add_zero] using (hV 0 (by omega)).2
  have heq : (fun x : ℝ => U (x : ℂ)) =ᶠ[𝓝 (0 : ℝ)] (fun x => V 0 (x : ℂ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-a) a from ⟨by linarith, ha⟩),
      isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-ρ) ρ from ⟨by linarith, hρ⟩)] with x hx hxρ
    refine tendsto_nhds_unique_of_eventuallyEq
      (dirichlet_closed_halfBox_vertical_limit hβ hU (abs_lt.mpr hx).le)
      (dirichlet_closed_halfBox_vertical_limit hρ (hV 0 (by omega)).1 (abs_lt.mpr hxρ).le) ?_
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hβ).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds hρ).filter_mono nhdsWithin_le_nhds] with y hy hyβ hyρ
    rw [hUu (rectangularComplexCoord_mem_halfBox (show (x, y) ∈ Ioo (-a) a ×ˢ Ioo (0 : ℝ) β from ⟨hx, hy, hyβ⟩)),
      hV₀ (rectangularComplexCoord_mem_halfBox (show (x, y) ∈ Ioo (-ρ) ρ ×ˢ Ioo (0 : ℝ) ρ from ⟨hxρ, hy, hyρ⟩))]
  exact (hVc.contDiffAt (isOpen_Ioo.mem_nhds
    (show (0 : ℝ) ∈ Ioo (-ρ) ρ from ⟨by linarith, hρ⟩))).congr_of_eventuallyEq heq

private def riemannMappingFlattenedGreen (F : ℂ → ℂ) (Ψ : ℂ → ℂ) (z : ℂ) : ℂ :=
  (riemannMappingGreen F (Ψ z) : ℂ)

private def riemannMappingGreenBoundaryCoefficient (f : ℝ → ℝ) (P Q : ℂ → ℂ) (z : ℂ) : ℂ :=
  (-(P z - ((deriv f z.re : ℝ) : ℂ) * Q z) + Complex.I * Q z) *
    (1 + Complex.I * ((deriv f z.re : ℝ) : ℂ))

private def riemannMappingGreenLogDatum (F : ℂ → ℂ) (d : smoothTraceTests)
    (Ψ : ℂ → ℂ) (z : ℂ) : ℂ :=
  d (Ψ z) - (((1 / 2 : ℝ) * Real.log (‖Ψ z - F 0‖ ^ 2) : ℝ) : ℂ)

private theorem complex_eq_mul_log_gradient (j D : ℂ) (hj : j ≠ 0) :
    D = j * (-((-⟪j, D⟫_ℝ / ‖j‖ ^ 2 : ℝ) : ℂ) +
      Complex.I * ((-⟪j, D * Complex.I⟫_ℝ / ‖j‖ ^ 2 : ℝ) : ℂ)) := by
  have hn : j.re * j.re + j.im * j.im ≠ 0 := by
    simpa only [← Complex.normSq_apply, Complex.normSq_eq_norm_sq] using
      pow_ne_zero 2 (norm_ne_zero_iff.mpr hj)
  have hn₂ : j.re ^ 2 + j.im ^ 2 ≠ 0 := by simpa only [pow_two] using hn
  apply Complex.ext <;>
    simp only [Complex.inner, Complex.sq_norm, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, mul_one, one_mul, add_zero, zero_add, sub_zero] <;>
    field_simp [hn, hn₂] <;> ring

private theorem contDiffAt_of_eventually_hasDerivAt_mul {α B : ℝ → ℂ} {x₀ : ℝ}
    (hB : ContDiffAt ℝ (⊤ : ℕ∞) B x₀)
    (hd : ∀ᶠ x in 𝓝 x₀, HasDerivAt α (α x * B x) x) :
    ContDiffAt ℝ (⊤ : ℕ∞) α x₀ := by
  refine contDiffAt_infty.mpr fun n => ?_
  induction n with
  | zero =>
    exact contDiffAt_zero.mpr ⟨{x | HasDerivAt α (α x * B x) x}, hd,
      fun _ hx => hx.continuousAt.continuousWithinAt⟩
  | succ n ih =>
    refine contDiffAt_succ_iff_hasFDerivAt.mpr
      ⟨fun x => ContinuousLinearMap.toSpanSingleton ℝ (α x * B x),
        ⟨{x | HasDerivAt α (α x * B x) x}, hd, fun _ hx => hx.hasFDerivAt⟩, ?_⟩
    exact (ContinuousLinearMap.toSpanSingletonCLE : ℂ ≃L[ℝ] (ℝ →L[ℝ] ℂ)).contDiff.contDiffAt.comp x₀
      (ih.mul (hB.of_le (WithTop.coe_le_coe.mpr le_top)))

/-! ### Smoothness and nonstationarity of the forward Riemann circle trace -/

private def riemannMappingBoundaryPhase (α : ℝ → ℂ) (t₀ t : ℝ) : ℝ :=
  (Complex.log (α t / α t₀)).im

private theorem riemannMappingBoundaryPhase_circle_eventually {α : ℝ → ℂ} {t₀ : ℝ}
    (hcircle : ∀ᶠ t in 𝓝 t₀, ‖α t‖ = 1) :
    ∀ᶠ t in 𝓝 t₀, α t = α t₀ * circleMap 0 1 (riemannMappingBoundaryPhase α t₀ t) := by
  have h₀ : ‖α t₀‖ = 1 := hcircle.self_of_nhds
  have hn₀ : α t₀ ≠ 0 := fun h => by simp [h] at h₀
  refine hcircle.mono fun t ht => ?_
  have hratio : ‖α t / α t₀‖ = 1 := by rw [norm_div, ht, h₀]; norm_num
  have hn : α t / α t₀ ≠ 0 := fun h => by simp [h] at hratio
  have hre : (Complex.log (α t / α t₀)).re = 0 := by rw [Complex.log_re, hratio, Real.log_one]
  have hlog : Complex.log (α t / α t₀) =
      (riemannMappingBoundaryPhase α t₀ t : ℂ) * Complex.I := by
    simpa only [riemannMappingBoundaryPhase, hre, Complex.ofReal_zero, zero_add] using
      (Complex.re_add_im (Complex.log (α t / α t₀))).symm
  have hexp : circleMap 0 1 (riemannMappingBoundaryPhase α t₀ t) = α t / α t₀ := by
    simp only [circleMap_zero, Complex.ofReal_one, one_mul, ← hlog, Complex.exp_log hn]
  rw [hexp]; field_simp [hn₀]

private theorem exists_riemannMappingBoundaryAngularInverse {α : ℝ → ℂ} {t₀ θ₀ : ℝ}
    (hα : ContDiffAt ℝ (⊤ : ℕ∞) α t₀)
    (hcircle : ∀ᶠ t in 𝓝 t₀, ‖α t‖ = 1) (hd : deriv α t₀ ≠ 0)
    (hcenter : α t₀ = circleMap 0 1 θ₀) :
    ∃ g : ℝ → ℝ, g θ₀ = t₀ ∧ ContDiffAt ℝ (⊤ : ℕ∞) g θ₀ ∧
      deriv (riemannMappingBoundaryPhase α t₀) t₀ ≠ 0 ∧
      HasDerivAt g (deriv (riemannMappingBoundaryPhase α t₀) t₀)⁻¹ θ₀ ∧
      ∀ᶠ θ in 𝓝 θ₀, α (g θ) = circleMap 0 1 θ := by
  let φ := riemannMappingBoundaryPhase α t₀
  have hn₀ : α t₀ ≠ 0 := fun h => by simpa [h] using hcircle.self_of_nhds
  have hφ : ContDiffAt ℝ (⊤ : ℕ∞) φ t₀ :=
    Complex.imCLM.contDiff.contDiffAt.comp t₀ <|
      ((Complex.contDiffAt_log (by simp [hn₀] : α t₀ / α t₀ ∈ Complex.slitPlane)).restrict_scalars ℝ).comp
        (f := fun t : ℝ => α t / α t₀) (g := Complex.log) t₀ (hα.div_const _)
  have hdφ : HasDerivAt φ (deriv φ t₀) t₀ := (hφ.differentiableAt (by simp)).hasDerivAt
  have hc : deriv φ t₀ ≠ 0 := fun hz => hd <| by
    have ha : HasDerivAt α (α t₀ * (deriv φ t₀ • (circleMap 0 1 (φ t₀) * Complex.I))) t₀ :=
      (((hasDerivAt_circleMap 0 1 _).scomp t₀ hdφ).const_mul (α t₀)).congr_of_eventuallyEq
        (riemannMappingBoundaryPhase_circle_eventually hcircle)
    rw [ha.deriv, hz, zero_smul, mul_zero]
  have hfd := hdφ.hasFDerivAt_equiv hc
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  let e := hφ.toOpenPartialHomeomorph φ hfd htop
  have he : (e : ℝ → ℝ) = φ := rfl
  have hs : t₀ ∈ e.source := hφ.mem_toOpenPartialHomeomorph_source hfd htop
  have hφ₀ : φ t₀ = 0 := by simp [φ, riemannMappingBoundaryPhase, hn₀]
  have ht : (0 : ℝ) ∈ e.target := by
    simpa only [hφ₀] using hφ.image_mem_toOpenPartialHomeomorph_target hfd htop
  have he₀ : e.symm 0 = t₀ := by simpa only [he, hφ₀] using e.left_inv hs
  have hid : HasDerivAt (e : ℝ → ℝ) (deriv φ t₀) (e.symm 0) := by simpa only [he₀, he] using hdφ
  have hi : ContDiffAt ℝ (⊤ : ℕ∞) (e.symm : ℝ → ℝ) 0 :=
    e.contDiffAt_symm_deriv hc ht hid (by simpa only [he₀, he] using hφ)
  have hdi : HasDerivAt (e.symm : ℝ → ℝ) (deriv φ t₀)⁻¹ 0 := e.hasDerivAt_symm ht hc hid
  let g : ℝ → ℝ := fun θ => e.symm (θ - θ₀)
  have hg₀ : g θ₀ = t₀ := by simp [g, he₀]
  have hgs : ContDiffAt ℝ (⊤ : ℕ∞) g θ₀ :=
    (show ContDiffAt ℝ (⊤ : ℕ∞) (e.symm : ℝ → ℝ) (θ₀ - θ₀) by simpa only [sub_self] using hi).comp
      (f := fun θ : ℝ => θ - θ₀) (g := (e.symm : ℝ → ℝ)) θ₀ (contDiffAt_id.sub contDiffAt_const)
  have hgd : HasDerivAt g (deriv φ t₀)⁻¹ θ₀ := by
    simpa only [g, one_mul, mul_one, Function.comp_def, id] using
      hdi.comp_of_eq θ₀ ((hasDerivAt_id θ₀).sub_const θ₀) (by simp)
  have hshift : Tendsto (fun θ : ℝ => θ - θ₀) (𝓝 θ₀) (𝓝 0) :=
    sub_self θ₀ ▸ (tendsto_id.sub tendsto_const_nhds)
  have hgt : Tendsto g (𝓝 θ₀) (𝓝 t₀) := by simpa only [hg₀] using hgs.continuousAt.tendsto
  refine ⟨g, hg₀, hgs, hc, hgd, ?_⟩
  filter_upwards [hshift.eventually (e.eventually_right_inverse ht),
    hgt.eventually (riemannMappingBoundaryPhase_circle_eventually hcircle)] with θ hθ hrec
  change α (g θ) = α t₀ * circleMap 0 1 (φ (g θ)) at hrec
  have hθ' : φ (g θ) = θ - θ₀ := hθ
  rw [hrec, hcenter, hθ', circleMap_zero_mul, one_mul]
  congr 1; ring

section SmoothBoundaryMap

open scoped RealInnerProductSpace

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
include hb hS hsc hF hinj himage

private theorem riemannMappingBoundaryTrace_hasDerivAt_of_green_fields
    (p c : ℂ) (hc : c ≠ 0) {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {a b : ℝ} (ha : 0 < a) (hb_pos : 0 < b)
    (hmap : MapsTo (smoothDirichletGraphChart p c hc f hf.continuous)
      (smoothDirichletHalfBox a b) Ω)
    (hpole : ∀ z ∈ smoothDirichletHalfBox a b,
      smoothDirichletGraphChart p c hc f hf.continuous z ≠ F 0)
    (hJ : ContinuousOn (riemannMappingClosedInverse F ∘
      smoothDirichletGraphChart p c hc f hf.continuous) (smoothDirichletClosedHalfBox a b))
    {P Q : ℂ → ℂ}
    (hPc : ContinuousOn P (smoothDirichletClosedHalfBox a b))
    (hQc : ContinuousOn Q (smoothDirichletClosedHalfBox a b))
    (hP : EqOn P (dirD (riemannMappingFlattenedGreen F
      (smoothDirichletGraphChart p c hc f hf.continuous)) 1) (smoothDirichletHalfBox a b))
    (hQ : EqOn Q (dirD (riemannMappingFlattenedGreen F
      (smoothDirichletGraphChart p c hc f hf.continuous)) Complex.I) (smoothDirichletHalfBox a b))
    {x : ℝ} (hx : x ∈ Ioo (-a) a) :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     HasDerivAt (fun s : ℝ => riemannMappingClosedInverse F (Ψ (s : ℂ)))
       (riemannMappingClosedInverse F (Ψ (x : ℂ)) *
         riemannMappingGreenBoundaryCoefficient f P Q (x : ℂ)) x) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let J := riemannMappingClosedInverse F
  let G := riemannMappingFlattenedGreen F Ψ
  have hd_f : Continuous (fun z : ℂ => ((deriv f z.re : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((contDiff_infty_iff_deriv.mp hf).2.continuous.comp Complex.continuous_re)
  have hB_cont : ContinuousOn (riemannMappingGreenBoundaryCoefficient f P Q)
      (smoothDirichletClosedHalfBox a b) :=
    ((hPc.sub (hd_f.continuousOn.mul hQc)).neg.add (continuousOn_const.mul hQc)).mul
      (continuousOn_const.add (continuousOn_const.mul hd_f.continuousOn))
  refine dirichlet_boundary_horizontal_hasDerivAt ha hb_pos hJ (hJ.mul hB_cont) (fun s hs y hy => ?_) hx
  let z := rectangularComplexCoord (s, y)
  have hz : z ∈ smoothDirichletHalfBox a b := rectangularComplexCoord_mem_halfBox ⟨hs, hy⟩
  have hzΩ := hmap hz
  have hzne := hpole z hz
  have hdJ : DifferentiableAt ℂ J (Ψ z) :=
    (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage).differentiableAt
      (hS.1.1.mem_nhds hzΩ)
  have hdcomp : DifferentiableAt ℝ (J ∘ Ψ) z :=
    (hdJ.restrictScalars ℝ).comp z (smoothDirichletGraphChart_hasFDerivAt p c hc hf z).differentiableAt
  have hrow := hdcomp.hasFDerivAt.comp_hasDerivAt s
    ((Complex.ofRealCLM.hasDerivAt (x := s)).add_const ((y : ℂ) * Complex.I))
  change HasDerivAt (fun t : ℝ => J (Ψ (rectangularComplexCoord (t, y)))) (dirD (J ∘ Ψ) 1 z) s at hrow
  have hdir1 : dirD (J ∘ Ψ) 1 z = (deriv J (Ψ z) / c) * (1 + Complex.I * ((deriv f z.re : ℝ) : ℂ)) := by
    change fderiv ℝ (J ∘ Ψ) z 1 = _
    rw [fderiv_comp z (hdJ.restrictScalars ℝ) (smoothDirichletGraphChart_hasFDerivAt p c hc hf z).differentiableAt,
      ContinuousLinearMap.comp_apply, hdJ.fderiv_restrictScalars ℝ]
    change fderiv ℂ J (Ψ z) (fderiv ℝ Ψ z 1) = _
    rw [fderiv_eq_deriv_mul, smoothDirichletGraphChart_fderiv_apply p c hc hf z 1]
    simp only [Complex.one_re, mul_one, Complex.real_smul, div_eq_mul_inv]; ring
  have hdGr_re : DifferentiableAt ℝ (riemannMappingGreen F) (Ψ z) :=
    (riemannMappingGreen_harmonicOnNhd hb hS hsc F hF hinj himage (Ψ z) ⟨hzΩ, hzne⟩).1.differentiableAt
      (by norm_num)
  have hdGr : DifferentiableAt ℝ (fun w : ℂ => (riemannMappingGreen F w : ℂ)) (Ψ z) :=
    Complex.ofRealCLM.differentiableAt.comp _ hdGr_re
  have hGr_fd (v : ℂ) : fderiv ℝ (fun w : ℂ => (riemannMappingGreen F w : ℂ)) (Ψ z) v =
      ((-⟪J (Ψ z), deriv J (Ψ z) * v⟫_ℝ / ‖J (Ψ z)‖ ^ 2 : ℝ) : ℂ) := by
    change fderiv ℝ (Complex.ofRealCLM ∘ riemannMappingGreen F) (Ψ z) v = _
    rw [fderiv_comp (Ψ z) Complex.ofRealCLM.differentiableAt hdGr_re,
      ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
      riemannMappingGreen_fderiv hb hS hsc F hF hinj himage hzΩ hzne]
  obtain ⟨hX, hY⟩ := smoothDirichletGraphChart_pullback_gradient p c hc hf hdGr
  change dirD G 1 z - ((deriv f z.re : ℝ) : ℂ) * dirD G Complex.I z = fderiv ℝ _ (Ψ z) (1 / c) at hX
  change dirD G Complex.I z = fderiv ℝ _ (Ψ z) (Complex.I / c) at hY
  rw [hGr_fd, show deriv J (Ψ z) * (1 / c) = deriv J (Ψ z) / c by ring] at hX
  rw [hGr_fd, show deriv J (Ψ z) * (Complex.I / c) = (deriv J (Ψ z) / c) * Complex.I by ring] at hY
  have hlog : deriv J (Ψ z) / c = J (Ψ z) *
      (-(dirD G 1 z - ((deriv f z.re : ℝ) : ℂ) * dirD G Complex.I z) + Complex.I * dirD G Complex.I z) := by
    rw [hX, hY]
    exact complex_eq_mul_log_gradient (J (Ψ z)) (deriv J (Ψ z) / c)
      (riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage (subset_closure hzΩ) hzne)
  have hode : dirD (J ∘ Ψ) 1 z = J (Ψ z) * riemannMappingGreenBoundaryCoefficient f P Q z := by
    rw [hdir1, hlog, ← hP hz, ← hQ hz]
    unfold riemannMappingGreenBoundaryCoefficient; ring
  rwa [hode] at hrow

private theorem exists_riemannMapping_genuine_regular_inverse_graph {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (r : ℝ),
      f 0 = 0 ∧ 0 < r ∧
      (∀ z : ℂ, |z.re| < r → |z.im| < r →
        (smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω ↔ 0 < z.im)) ∧
      ContDiffAt ℝ (⊤ : ℕ∞)
        (fun x : ℝ => riemannMappingClosedInverse F
          (smoothDirichletGraphChart p c hc f hf.continuous (x : ℂ))) 0 ∧
      deriv (fun x : ℝ => riemannMappingClosedInverse F
        (smoothDirichletGraphChart p c hc f hf.continuous (x : ℂ))) 0 ≠ 0 := by
  obtain ⟨d, hvcont, hvsmooth, hvzero, hvm, hgm, hΔ⟩ :=
    exists_riemannMapping_zero_boundary_poisson_problem hb hS hsc F hF hinj himage
  obtain ⟨c, hc, f, hf, K, a₀, b₀, hc₁, hLip, hf₀, ha₀, hb₀, hchart₀⟩ :=
    exists_smoothDomain_flattening_rectangle hS hp
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let A := a₀ / 2
  let b := b₀ / 2
  have hA : 0 < A := by positivity
  have hb_pos : 0 < b := by positivity
  let U₀ := smoothDirichletHalfBox A b
  let u := riemannMappingDirichletRemainder F d ∘ Ψ
  have hU₀ : IsOpen U₀ := isOpen_smoothDirichletHalfBox _ _
  have hmap₀ : MapsTo Ψ U₀ Ω := fun z hz =>
    (hchart₀ z (hz.1.trans (by dsimp [A]; linarith))
      (by rw [abs_of_pos hz.2.1]; exact hz.2.2.trans (by dsimp [b]; linarith))).mpr hz.2.1
  have hclosed₀ : MapsTo Ψ (smoothDirichletClosedHalfBox A b) (closure Ω) := fun z hz => by
    have hzr : |z.re| < a₀ := hz.1.trans_lt (by dsimp [A]; linarith)
    have hzi : |z.im| < b₀ := by rw [abs_of_nonneg hz.2.1]; dsimp [b] at hz; linarith [hz.2.2]
    rcases eq_or_lt_of_le hz.2.1 with heq | hpos
    · rw [show z = (z.re : ℂ) by apply Complex.ext <;> simp [← heq]]
      exact frontier_subset_closure
        (smoothDirichletGraphChart_mem_frontier hS.1.1 p c hc f hf.continuous hb₀ hchart₀ hzr)
    · exact subset_closure ((hchart₀ z hzr hzi).mpr hpos)
  have huc : ContinuousOn u (smoothDirichletClosedHalfBox A b) :=
    hvcont.comp Ψ.continuous.continuousOn hclosed₀
  have hus : ContDiffOn ℝ (⊤ : ℕ∞) u U₀ :=
    hvsmooth.comp (smoothDirichletGraphChart_contDiff p c hc hf).contDiffOn hmap₀
  have huz (x : ℝ) (hx : |x| < A) : u (x : ℂ) = 0 :=
    smoothDirichletGraphChart_zero_boundary hS.1.1 p c hc f hf.continuous hb₀ hchart₀ _ hvzero
      (hx.trans (by dsimp [A]; linarith))
  obtain ⟨hvm', hgm'⟩ := smoothDirichletGraphChart_pullback_memLp
    hS.1.1 hU₀ p c hc hc₁ hf hLip (mapsTo_iff_image_subset.mp hmap₀) hvsmooth hvm hgm
  have hstrong (z : ℂ) (hzU : z ∈ U₀) : dirichletFlattenedDivergence f u z = -(lap (d : ℂ → ℂ) ∘ Ψ) z := by
    rw [dirichletFlattenedDivergence_pullback hS.1.1 p c hc hc₁ hf hvsmooth (hmap₀ hzU)]
    exact hΔ _ (hmap₀ hzU)
  have hhigh (N : ℕ) := exists_dirichlet_halfBox_mixed_derivative_memLp hA hb_pos hf hLip
    huc hus huz hvm' hgm' hstrong
    (d.property.lap.1.comp (smoothDirichletGraphChart_contDiff p c hc hf)) N
  obtain ⟨ρ, hρ, hρA, hρb, hm3⟩ := hhigh 3
  have hWU : smoothDirichletHalfBox ρ ρ ⊆ U₀ :=
    fun z hz => ⟨hz.1.trans (by linarith), hz.2.1, hz.2.2.trans hρb⟩
  obtain ⟨X, hXc, hXu⟩ := dirichlet_mixed_exists_continuous_extension hρ hρ (hus.mono hWU) 3 1 0 hm3 (by omega)
  obtain ⟨Y, hYc, hYu⟩ := dirichlet_mixed_exists_continuous_extension hρ hρ (hus.mono hWU) 3 0 1 hm3 (by omega)
  have hXsmooth := dirichlet_mixed_boundary_contDiffAt_of_finite_energy hρ hρ hus 1 0 hhigh hXc hXu
  have hYsmooth := dirichlet_mixed_boundary_contDiffAt_of_finite_energy hρ hρ hus 0 1 hhigh hYc hYu
  let L := riemannMappingGreenLogDatum F d Ψ
  have hΨ : ContDiff ℝ (⊤ : ℕ∞) (Ψ : ℂ → ℂ) := smoothDirichletGraphChart_contDiff p c hc hf
  have hΨ₀ : Ψ 0 = p := by simp [Ψ, smoothDirichletGraphShear, hf₀]
  have hpne : p ≠ F 0 := fun he => by
    rw [he, hS.1.1.frontier_eq] at hp; exact hp.2 (riemannMapping_pole_mem F himage)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (Ψ.continuous.continuousAt.eventually (eventually_ne_nhds (by rw [hΨ₀]; exact hpne)))
  let r := min ρ (ε / 4)
  have hr : 0 < r := lt_min hρ (by positivity)
  have hrρ : r ≤ ρ := min_le_left _ _
  have hrε : r ≤ ε / 4 := min_le_right _ _
  let U := smoothDirichletHalfBox r r
  let V := smoothDirichletClosedHalfBox r r
  have hne : ∀ z ∈ V, Ψ z ≠ F 0 := fun z hz => hball <| by
    rw [mem_ball_zero_iff]
    have hzI : |z.im| ≤ r := by rw [abs_of_nonneg hz.2.1]; exact hz.2.2
    exact ((Complex.norm_le_abs_re_add_abs_im z).trans
      (by linarith [hz.1] : |z.re| + |z.im| ≤ 2 * r)).trans_lt (by linarith)
  have hrA : r < A := hrρ.trans_lt (hρA.trans (by linarith))
  have hrb : r < b := hrρ.trans_lt hρb
  have hUρ : U ⊆ smoothDirichletHalfBox ρ ρ := fun z hz => ⟨hz.1.trans_le hrρ, hz.2.1, hz.2.2.trans_le hrρ⟩
  have hVρ : V ⊆ smoothDirichletClosedHalfBox ρ ρ := fun z hz => ⟨hz.1.trans hrρ, hz.2.1, hz.2.2.trans hrρ⟩
  have hUA : U ⊆ U₀ := fun z hz => ⟨hz.1.trans hrA, hz.2.1, hz.2.2.trans hrb⟩
  have hVA : V ⊆ smoothDirichletClosedHalfBox A b := fun z hz => ⟨hz.1.trans hrA.le, hz.2.1, hz.2.2.trans hrb.le⟩
  have hUV : U ⊆ V := fun z hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩
  have hclosed' : MapsTo Ψ V (closure Ω) := fun z hz => hclosed₀ (hVA hz)
  have hmap' : MapsTo Ψ U Ω := fun z hz => hmap₀ (hUA hz)
  have hchart' (z : ℂ) (hzre : |z.re| < r) (hzim : |z.im| < r) : Ψ z ∈ Ω ↔ 0 < z.im :=
    hchart₀ z (hzre.trans (hrA.trans (by dsimp [A]; linarith)))
      (hzim.trans (hrb.trans (by dsimp [b]; linarith)))
  have hLs (z : ℂ) (hz : z ∈ V) : ContDiffAt ℝ (⊤ : ℕ∞) L z := by
    have hnorm : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ => ‖Ψ w - F 0‖ ^ 2) z :=
      (hΨ.contDiffAt.sub contDiffAt_const).norm_sq ℂ
    have hlog := hnorm.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hne z hz))))
    exact (d.property.1.contDiffAt.comp z hΨ.contDiffAt).sub
      (Complex.ofRealCLM.contDiff.contDiffAt.comp z (contDiffAt_const.mul hlog))
  have hLc : ContinuousOn L V := fun z hz => (hLs z hz).continuousAt.continuousWithinAt
  have hDs (w z : ℂ) (hz : z ∈ V) : ContDiffAt ℝ (⊤ : ℕ∞) (dirD L w) z :=
    ((hLs z hz).fderiv_right (m := (⊤ : ℕ∞)) le_rfl).clm_apply contDiffAt_const
  have hDc (w : ℂ) : ContinuousOn (dirD L w) V :=
    fun z hz => (hDs w z hz).continuousAt.continuousWithinAt
  have hV₀ : (0 : ℂ) ∈ V := by
    change |(0 : ℂ).re| ≤ r ∧ 0 ≤ (0 : ℂ).im ∧ (0 : ℂ).im ≤ r; simp [hr.le]
  have hLsmooth (w : ℂ) : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => dirD L w (x : ℂ)) 0 :=
    (hDs w 0 hV₀).comp (f := fun x : ℝ => (x : ℂ)) (g := dirD L w) 0
      Complex.ofRealCLM.contDiff.contDiffAt
  let P : ℂ → ℂ := fun z => X z + dirD L 1 z
  let Q : ℂ → ℂ := fun z => Y z + dirD L Complex.I z
  let G := riemannMappingFlattenedGreen F Ψ
  have hsum : EqOn G (fun z => u z + L z) V := fun z hz => by
    dsimp only [G, u, L, Function.comp_apply]
    rw [riemannMappingFlattenedGreen, riemannMappingDirichletRemainder, riemannMappingGreenLogDatum,
      riemannMappingGreenCorrection_eq hb hS hsc F hF hinj himage (hclosed' hz) (hne z hz), Real.log_pow]
    push_cast; ring
  have hGc : ContinuousOn G V := ((huc.mono hVA).add hLc).congr hsum
  have hus' : ContDiffOn ℝ (⊤ : ℕ∞) u U := hus.mono hUA
  have hGs : ContDiffOn ℝ (⊤ : ℕ∞) G U :=
    (hus'.add fun z hz => (hLs z (hUV hz)).contDiffWithinAt).congr (hsum.mono hUV)
  have hU : IsOpen U := isOpen_smoothDirichletHalfBox r r
  have hd (w : ℂ) : EqOn (dirD G w) (fun z => dirD u w z + dirD L w z) U := fun z hz => by
    rw [dirichlet_bootstrap_dirD_eqOn hU (hsum.mono hUV) w hz]
    exact dirichlet_normal_dirD_add
      ((hus'.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
      ((hLs z (hUV hz)).differentiableAt (by simp)) w
  have hP : EqOn P (dirD G 1) U := fun z hz => by
    rw [hd 1 hz]; change X z + dirD L 1 z = _; rw [hXu (hUρ hz)]; rfl
  have hQ : EqOn Q (dirD G Complex.I) U := fun z hz => by
    rw [hd Complex.I hz]; change Y z + dirD L Complex.I z = _; rw [hYu (hUρ hz)]; rfl
  have hJ : ContinuousOn (riemannMappingClosedInverse F ∘ Ψ) V :=
    (riemannMappingClosedInverse_continuousOn hb hS hsc F hF hinj himage).comp
      Ψ.continuous.continuousOn hclosed'
  have hpole : ∀ z ∈ U, Ψ z ≠ F 0 := fun z hz => hne z (hUV hz)
  have hPc : ContinuousOn P V := (hXc.mono hVρ).add (hDc 1)
  have hQc : ContinuousOn Q V := (hYc.mono hVρ).add (hDc Complex.I)
  have hPs : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => P (x : ℂ)) 0 := hXsmooth.add (hLsmooth 1)
  have hQs : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => Q (x : ℂ)) 0 := hYsmooth.add (hLsmooth Complex.I)
  have hz₀_I : (0 : ℝ) ∈ Ioo (-r) r := ⟨by linarith, hr⟩
  have hα : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => riemannMappingClosedInverse F (Ψ (x : ℂ))) 0 := by
    have hd_f : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => ((deriv f x : ℝ) : ℂ)) 0 :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp 0 (contDiff_infty_iff_deriv.mp hf).2.contDiffAt
    have hBs : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun x : ℝ => riemannMappingGreenBoundaryCoefficient f P Q (x : ℂ)) 0 := by
      simpa only [riemannMappingGreenBoundaryCoefficient, Complex.ofReal_re] using
        ((hPs.sub (hd_f.mul hQs)).neg.add (contDiffAt_const.mul hQs)).mul
          (contDiffAt_const.add (contDiffAt_const.mul hd_f))
    refine contDiffAt_of_eventually_hasDerivAt_mul hBs ?_
    filter_upwards [isOpen_Ioo.mem_nhds hz₀_I] with x hx
    exact riemannMappingBoundaryTrace_hasDerivAt_of_green_fields hb hS hsc F hF hinj himage
      p c hc hf hr hr hmap' hpole hJ hPc hQc hP hQ hx
  refine ⟨c, hc, f, hf, r, hf₀, hr, hchart', hα, ?_⟩
  have hP₀ : P 0 = 0 := by
    have hd0 := dirichlet_boundary_extension_hasDerivAt hr hr hGs hGc (fun _ _ => rfl) hPc hP hz₀_I
    have heq0 : (fun s : ℝ => riemannMappingFlattenedGreen F Ψ (s : ℂ)) =ᶠ[𝓝 (0 : ℝ)]
        (fun _ => (0 : ℂ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hz₀_I] with x hx
      have hp' := smoothDirichletGraphChart_mem_frontier hS.1.1 p c hc f hf.continuous hr hchart' (abs_lt.mpr hx)
      dsimp only [riemannMappingFlattenedGreen, Ψ]
      rw [riemannMappingGreen_frontier hb hS hsc F hF hinj himage hp', Complex.ofReal_zero]
    simpa only [Complex.ofReal_zero] using
      hd0.unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq heq0)
  have hQ₀ : Q 0 ≠ 0 := fun hQ₀ => by
    have hpin : p ∈ closure Ω := frontier_subset_closure hp
    obtain ⟨v, δ, A_bar, _, hδ, hA_bar, hray⟩ :=
      exists_riemannMappingGreen_inward_ray_lower hb hS hsc F hF hinj himage hp
    let w : ℝ → ℂ := fun t => p + (t : ℂ) * v
    let ζ : ℝ → ℂ := fun t => Ψ.symm (w t)
    let R : ℝ → ℂ := fun t => (riemannMappingGreen F (w t) : ℂ)
    have hw : Continuous w := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hw₀ : w 0 = p := by simp [w]
    have hζ₀ : ζ 0 = 0 := by change Ψ.symm (w 0) = 0; rw [hw₀, ← hΨ₀, Ψ.symm_apply_apply]
    have hζlim : Tendsto ζ (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
      hζ₀ ▸ ((Ψ.symm.continuous.comp hw).continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    have hrelim : Tendsto (fun t : ℝ => |(ζ t).re|) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa only [Complex.zero_re, abs_zero, Function.comp_def] using
        continuous_abs.continuousAt.tendsto.comp (Complex.continuous_re.continuousAt.tendsto.comp hζlim)
    have himlim : Tendsto (fun t : ℝ => |(ζ t).im|) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa only [Complex.zero_im, abs_zero, Function.comp_def] using
        continuous_abs.continuousAt.tendsto.comp (Complex.continuous_im.continuousAt.tendsto.comp hζlim)
    have hζbox : ∀ᶠ t in 𝓝[>] (0 : ℝ), ζ t ∈ U := by
      filter_upwards [self_mem_nhdsWithin, hrelim.eventually_lt_const hr,
        himlim.eventually_lt_const hr, (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds]
        with t ht htr hti htδ
      have hpos : 0 < (ζ t).im := (hchart' (ζ t) htr hti).mp (by
        change Ψ (ζ t) ∈ Ω; rw [Ψ.apply_symm_apply]; exact (hray t ht htδ).1)
      exact ⟨htr, hpos, lt_of_le_of_lt (le_abs_self _) hti⟩
    have hzclosed : ∀ᶠ t in 𝓝[>] (0 : ℝ), ζ t ∈ V := hζbox.mono fun _ ht => hUV ht
    have hζwithin := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within ζ hζlim hzclosed
    have hpLim := (hPc 0 hV₀).tendsto.comp hζwithin
    have hqLim := (hQc 0 hV₀).tendsto.comp hζwithin
    have hcoef : Continuous (fun z : ℂ => (((c * v).im - deriv f z.re * (c * v).re : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp
        (continuous_const.sub (((contDiff_infty_iff_deriv.mp hf).2.continuous.comp Complex.continuous_re).mul
          continuous_const))
    have hder : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        HasDerivAt R (((c * v).re : ℂ) * P (ζ t) +
          (((c * v).im - deriv f (ζ t).re * (c * v).re : ℝ) : ℂ) * Q (ζ t)) t := by
      filter_upwards [hζbox, self_mem_nhdsWithin,
        (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t hzt ht htδ
      obtain ⟨hwt, hwne, _⟩ := hray t ht htδ
      have he : Ψ (ζ t) = w t := Ψ.apply_symm_apply (w t)
      have hdG : DifferentiableAt ℝ (fun z : ℂ => (riemannMappingGreen F z : ℂ)) (Ψ (ζ t)) := by
        rw [he]
        exact Complex.ofRealCLM.differentiableAt.comp _
          ((riemannMappingGreen_harmonicOnNhd hb hS hsc F hF hinj himage (w t)
            ⟨hwt, hwne⟩).1.differentiableAt (by norm_num))
      obtain ⟨hX, hY⟩ := smoothDirichletGraphChart_pullback_gradient p c hc hf hdG
      let T := fderiv ℝ (fun z : ℂ => (riemannMappingGreen F z : ℂ)) (Ψ (ζ t))
      change dirD G 1 (ζ t) - ((deriv f (ζ t).re : ℝ) : ℂ) * dirD G Complex.I (ζ t) = T (1 / c) at hX
      change dirD G Complex.I (ζ t) = T (Complex.I / c) at hY
      have hv_split : v = (c * v).re • (1 / c : ℂ) + (c * v).im • (Complex.I / c) := by
        calc v = (c * v) / c := (mul_div_cancel_left₀ v hc).symm
          _ = (((c * v).re : ℂ) + ((c * v).im : ℂ) * Complex.I) / c := by rw [Complex.re_add_im]
          _ = _ := by simp only [Complex.real_smul, div_eq_mul_inv]; ring
      have hTv : T v = ((c * v).re : ℂ) * P (ζ t) +
          (((c * v).im - deriv f (ζ t).re * (c * v).re : ℝ) : ℂ) * Q (ζ t) := by
        calc T v = T ((c * v).re • (1 / c : ℂ) + (c * v).im • (Complex.I / c)) := congrArg T hv_split
          _ = ((c * v).re : ℂ) * (dirD G 1 (ζ t) - ((deriv f (ζ t).re : ℝ) : ℂ) * dirD G Complex.I (ζ t)) +
              ((c * v).im : ℂ) * dirD G Complex.I (ζ t) := by
                rw [map_add, map_smul, map_smul, ← hX, ← hY, Complex.real_smul, Complex.real_smul]
          _ = _ := by rw [← hP hzt, ← hQ hzt]; push_cast; ring
      have hdw : HasDerivAt w v t := by
        simpa only [one_mul] using
          (((by simpa only [id, Complex.ofReal_one] using (hasDerivAt_id t).ofReal_comp :
            HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t)).mul_const v).const_add p
      have hdR := (he ▸ hdG).hasFDerivAt.comp_hasDerivAt t hdw
      change HasDerivAt R (fderiv ℝ (fun z : ℂ => (riemannMappingGreen F z : ℂ)) (w t) v) t at hdR
      rw [← he] at hdR
      exact hTv ▸ hdR
    obtain ⟨ε₁, hε₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hder
    have hGreenC : ContinuousOn (fun z : ℂ => (riemannMappingGreen F z : ℂ)) (closure Ω \ {F 0}) :=
      Complex.continuous_ofReal.comp_continuousOn
        (riemannMappingGreen_continuousOn hb hS hsc F hF hinj himage)
    have hRayDom : ∀ᶠ t in 𝓝[>] (0 : ℝ), w t ∈ closure Ω \ {F 0} := by
      filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t ht htδ
      exact ⟨subset_closure (hray t ht htδ).1, (hray t ht htδ).2.1⟩
    have hwlim : Tendsto w (𝓝[>] (0 : ℝ)) (𝓝 p) := by
      simpa only [hw₀] using (hw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds : Tendsto w _ (𝓝 (w 0)))
    have hRlim : Tendsto R (𝓝[>] (0 : ℝ)) (𝓝 (R 0)) := by
      simpa only [R, hw₀, Function.comp_def] using (hGreenC p ⟨hpin, hpne⟩).tendsto.comp
        (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within w hwlim hRayDom)
    have hDlim : Tendsto (fun t : ℝ => deriv R t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
      have hpLim' : Tendsto (fun t : ℝ => P (ζ t)) (𝓝[>] (0 : ℝ)) (𝓝 (P 0)) := hpLim
      have hqLim' : Tendsto (fun t : ℝ => Q (ζ t)) (𝓝[>] (0 : ℝ)) (𝓝 (Q 0)) := hqLim
      have hcoeflim : Tendsto (fun t : ℝ => (((c * v).im - deriv f (ζ t).re * (c * v).re : ℝ) : ℂ))
          (𝓝[>] (0 : ℝ)) (𝓝 (((c * v).im - deriv f 0 * (c * v).re : ℝ) : ℂ)) := by
        simpa only [Complex.zero_re, Function.comp_def] using hcoef.continuousAt.tendsto.comp hζlim
      have hh : Tendsto (fun t : ℝ => ((c * v).re : ℂ) * P (ζ t) +
          (((c * v).im - deriv f (ζ t).re * (c * v).re : ℝ) : ℂ) * Q (ζ t))
          (𝓝[>] (0 : ℝ))
          (𝓝 (((c * v).re : ℂ) * P 0 +
            (((c * v).im - deriv f 0 * (c * v).re : ℝ) : ℂ) * Q 0)) :=
        (tendsto_const_nhds.mul hpLim').add (hcoeflim.mul hqLim')
      rw [hP₀, hQ₀, mul_zero, mul_zero, add_zero] at hh
      exact hh.congr' (hder.mono fun _ ht => ht.deriv.symm)
    have hd₀ := hasDerivWithinAt_Ici_of_tendsto_deriv
      (fun t ht => (hsub ht).differentiableAt.differentiableWithinAt)
      (hRlim.mono_left (nhdsWithin_mono _ Ioo_subset_Ioi_self)) (Ioo_mem_nhdsGT hε₁) hDlim
    have hsl := (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Ioi (0 : ℝ) by simp)).mp
      (hd₀.mono Ioi_subset_Ici_self)
    have hR₀ : R 0 = 0 := by
      simp [R, hw₀, riemannMappingGreen_frontier hb hS hsc F hF hinj himage hp]
    have hlower : ∀ᶠ t in 𝓝[>] (0 : ℝ), A_bar ≤ (slope R 0 t).re := by
      filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t ht htδ
      simp only [slope_def_module, hR₀, sub_zero, Complex.smul_re, smul_eq_mul, R, Complex.ofReal_re]
      simpa only [w, div_eq_mul_inv, mul_comm] using (le_div_iff₀ ht).mpr (hray t ht htδ).2.2
    exact (not_le_of_gt hA_bar) (ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hsl) hlower)
  have hd_tr := riemannMappingBoundaryTrace_hasDerivAt_of_green_fields hb hS hsc F hF hinj himage
    p c hc hf hr hr hmap' hpole hJ hPc hQc hP hQ hz₀_I
  dsimp only at hd_tr
  have hj : riemannMappingClosedInverse F (Ψ 0) ≠ 0 := by
    rw [hΨ₀]
    exact norm_ne_zero_iff.mp (by
      rw [riemannMappingClosedInverse_norm_frontier hb hS hsc F hF hinj himage hp]; exact one_ne_zero)
  have hleft : ((deriv f 0 : ℝ) : ℂ) + Complex.I ≠ 0 := fun he =>
    (one_ne_zero : (1 : ℝ) ≠ 0) (by simpa using congrArg Complex.im he)
  have hright : 1 + Complex.I * ((deriv f 0 : ℝ) : ℂ) ≠ 0 := fun he =>
    (one_ne_zero : (1 : ℝ) ≠ 0) (by simpa using congrArg Complex.re he)
  have hB : riemannMappingGreenBoundaryCoefficient f P Q 0 =
      Q 0 * (((deriv f 0 : ℝ) : ℂ) + Complex.I) * (1 + Complex.I * ((deriv f 0 : ℝ) : ℂ)) := by
    simp only [riemannMappingGreenBoundaryCoefficient, Complex.zero_re, hP₀]; ring
  rw [hd_tr.deriv, Complex.ofReal_zero, hB]
  exact mul_ne_zero hj (mul_ne_zero (mul_ne_zero hQ₀ hleft) hright)

private theorem riemannMapping_circleTrace_contDiff_and_deriv_ne_zero :
    ContDiff ℝ (⊤ : ℕ∞) (physicalCircleTrace (riemannMappingClosedExtension F)) ∧
      ∀ θ : ℝ, deriv (physicalCircleTrace (riemannMappingClosedExtension F)) θ ≠ 0 := by
  have hall (θ : ℝ) :
      ContDiffAt ℝ (⊤ : ℕ∞) (physicalCircleTrace (riemannMappingClosedExtension F)) θ ∧
        deriv (physicalCircleTrace (riemannMappingClosedExtension F)) θ ≠ 0 := by
    let p := riemannMappingClosedExtension F (circleMap 0 1 θ)
    have hp : p ∈ frontier Ω :=
      riemannMappingClosedExtension_mem_frontier hb hS.isLipschitzDomain hsc F hF hinj himage
        (by simp only [norm_circleMap_zero, abs_one])
    obtain ⟨c, hc, f, hf, r, hf₀, hr, hchart', hα, hdα⟩ :=
      exists_riemannMapping_genuine_regular_inverse_graph hb hS hsc F hF hinj himage hp
    let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
    have hΨ : ContDiff ℝ (⊤ : ℕ∞) (Ψ : ℂ → ℂ) := smoothDirichletGraphChart_contDiff p c hc hf
    have hΨ₀ : Ψ 0 = p := by simp [Ψ, smoothDirichletGraphShear, hf₀]
    let β : ℝ → ℂ := fun x => Ψ (x : ℂ)
    let α : ℝ → ℂ := fun x => riemannMappingClosedInverse F (β x)
    have hfront : ∀ᶠ x : ℝ in 𝓝 0, β x ∈ frontier Ω := by
      filter_upwards [Ioo_mem_nhds (by linarith : -r < 0) hr] with x hx
      exact smoothDirichletGraphChart_mem_frontier hS.1.1 p c hc f hf.continuous hr hchart'
        (abs_lt.mpr hx)
    have hcircle : ∀ᶠ x in 𝓝 (0 : ℝ), ‖α x‖ = 1 :=
      hfront.mono fun _ hx => riemannMappingClosedInverse_norm_frontier hb hS hsc F hF hinj himage hx
    have hcenter : α 0 = circleMap 0 1 θ := by
      change riemannMappingClosedInverse F (Ψ (0 : ℝ)) = _
      rw [Complex.ofReal_zero, hΨ₀]
      exact riemannMappingClosedInverse_left hb hS hsc F hF hinj himage
        (circleMap_mem_closedBall 0 zero_le_one θ)
    have hforward : ∀ᶠ x in 𝓝 (0 : ℝ), riemannMappingClosedExtension F (α x) = β x :=
      hfront.mono fun _ hx =>
        (riemannMappingClosedInverse_mem_right hb hS hsc F hF hinj himage (frontier_subset_closure hx)).2
    have hβ : ContDiffAt ℝ (⊤ : ℕ∞) β 0 := (hΨ.comp Complex.ofRealCLM.contDiff).contDiffAt
    have hdβ : deriv β 0 ≠ 0 := by
      have hdβ₀ : HasDerivAt β (c⁻¹ * (1 + ((deriv f 0 : ℝ) : ℂ) * Complex.I)) 0 := by
        simpa only [β, Ψ, Function.comp_def, Complex.ofRealCLM_apply, ContinuousLinearMap.smul_apply,
          smoothDirichletGraphDifferential_apply, Complex.ofReal_re, Complex.ofReal_one,
          Complex.one_re, mul_one, Complex.real_smul, smul_eq_mul] using
          (smoothDirichletGraphChart_hasFDerivAt p c hc hf (0 : ℝ)).comp_hasDerivAt 0
            (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ)))
      rw [hdβ₀.deriv]
      refine mul_ne_zero (inv_ne_zero hc) fun hz => ?_
      have hre := congrArg Complex.re hz; norm_num [Complex.mul_re] at hre
    obtain ⟨g, hg₀, hgs, hc_ph, hgd, hcircleG⟩ :=
      exists_riemannMappingBoundaryAngularInverse hα hcircle hdα hcenter
    have hgt : Tendsto g (𝓝 θ) (𝓝 0) := by simpa only [hg₀] using hgs.continuousAt.tendsto
    have heq : physicalCircleTrace (riemannMappingClosedExtension F) =ᶠ[𝓝 θ] β ∘ g := by
      filter_upwards [hcircleG, hgt.eventually hforward] with s hs hforw
      have hforw' : riemannMappingClosedExtension F (α (g s)) = β (g s) := hforw
      simpa only [physicalCircleTrace, Function.comp_apply, ← hs] using hforw'
    have hβg : ContDiffAt ℝ (⊤ : ℕ∞) (β ∘ g) θ :=
      (show ContDiffAt ℝ (⊤ : ℕ∞) β (g θ) by rw [hg₀]; exact hβ).comp θ hgs
    have hdβg : HasDerivAt (β ∘ g)
        ((deriv (riemannMappingBoundaryPhase α 0) 0)⁻¹ • deriv β 0) θ :=
      ((hβ.differentiableAt (by simp)).hasDerivAt).scomp_of_eq θ hgd hg₀.symm
    refine ⟨hβg.congr_of_eventuallyEq heq, ?_⟩
    rw [(hdβg.congr_of_eventuallyEq heq).deriv]
    exact smul_ne_zero (inv_ne_zero hc_ph) hdβ
  exact ⟨contDiff_iff_contDiffAt.mpr fun θ => (hall θ).1, fun θ => (hall θ).2⟩

end SmoothBoundaryMap

/-! ### Area orientation, boundary shift sync, and smooth conformal coordinates -/

private theorem localConformal_circleTrace_signedArea {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (conj (physicalCircleTrace F θ) * deriv (physicalCircleTrace F) θ).im) =
        2 * (volume (F '' ball (0 : ℂ) 1)).toReal := by
  have hφ := smoothDiskCutoff_testFunction hR hFs
  have hφs := contDiff_smoothDiskCutoff hR hFs
  have hV := hφ.conj
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hV.2.1 hV.1 (by simp)
  have hdirD {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (v : ℂ) :
      dirD (smoothDiskCutoff R hR F) v z = deriv F z * v := by
    unfold dirD
    rw [fderiv_smoothDiskCutoff_eq hR F (ball_subset_closedBall hz),
      (hhol.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
    exact fderiv_eq_deriv_mul
  have hlap {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : lap (smoothDiskCutoff R hR F) z = 0 := by
    have heq : dirD (smoothDiskCutoff R hR F) Complex.I =ᶠ[𝓝 z]
        fun w => Complex.I * dirD (smoothDiskCutoff R hR F) 1 w := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      rw [hdirD hw Complex.I, hdirD hw 1, mul_one, mul_comm]
    have hd : DifferentiableAt ℝ (dirD (smoothDiskCutoff R hR F) 1) z :=
      ((hφs.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).clm_apply contDiff_const).differentiable (by simp) z
    have hD (v : ℂ) : dirD (dirD (smoothDiskCutoff R hR F) Complex.I) v z =
        Complex.I * dirD (dirD (smoothDiskCutoff R hR F) 1) v z := by
      simpa only [dirD, ContinuousLinearMap.smul_apply, smul_eq_mul] using
        congrArg (fun A : ℂ →L[ℝ] ℂ => A v) (heq.fderiv_eq.trans (fderiv_const_mul hd Complex.I))
    have hcomm : dirD (dirD (smoothDiskCutoff R hR F) 1) Complex.I z =
        dirD (dirD (smoothDiskCutoff R hR F) Complex.I) 1 z :=
      dirichlet_dirD_comm isOpen_ball hφs.contDiffOn hz 1 Complex.I
    rw [lap, hD Complex.I, hcomm, hD 1]
    ring_nf; simp only [Complex.I_sq]; ring
  have hgreen := doubleLayer_eq_integral unitDisk_bounded isLipschitzDomain_unitDisk
    unitCircle_isBoundaryParam hK hV.2.1
    (fun θ _ => show conj (smoothDiskCutoff R hR F (circleMap 0 1 θ)) =
      conj (physicalCircleTrace F θ) from congrArg conj (smoothDiskCutoff_eq_closedDisk hR F
        (circleMap_mem_closedBall (0 : ℂ) (by norm_num) θ))) hφ.1
  have hjac : (∫ z in ball (0 : ℂ) 1, ‖deriv F z‖ ^ 2) = (volume (F '' ball (0 : ℂ) 1)).toReal := by
    simpa only [setIntegral_const, measureReal_def, smul_eq_mul, mul_one] using
      (localConformal_integral_image isOpen_ball hhol hinj fun _ => (1 : ℝ)).symm
  have hdl : doubleLayer (circleMap 0 1) (fun θ => conj (physicalCircleTrace F θ))
      (smoothDiskCutoff R hR F) = ((2 * (volume (F '' ball (0 : ℂ) 1)).toReal : ℝ) : ℂ) := by
    rw [hgreen, ← hjac, ← integral_const_mul, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_ball fun z hz => ?_
    change conj (smoothDiskCutoff R hR F z) * lap (smoothDiskCutoff R hR F) z +
      (∑ i : Fin 2, dirD (fun w => conj (smoothDiskCutoff R hR F w)) (coordDir i) z *
        dirD (smoothDiskCutoff R hR F) (coordDir i) z) = ((2 * ‖deriv F z‖ ^ 2 : ℝ) : ℂ)
    rw [hlap hz, mul_zero, zero_add]
    simp only [Fin.sum_univ_two, show coordDir 0 = 1 from rfl,
      show coordDir 1 = Complex.I from rfl, dirD_conj (hφs.of_le (by simp)),
      ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hdirD hz 1, hdirD hz Complex.I,
      mul_one, norm_mul, Complex.norm_I]
    push_cast; ring
  have hγ := contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (by simp))
  let G : ℝ → ℂ := fun θ => conj (physicalCircleTrace F θ) * (-(Complex.I * deriv (physicalCircleTrace F) θ))
  have hi : IntervalIntegrable G volume 0 (2 * Real.pi) :=
    ((Complex.continuous_conj.comp hγ.continuous).mul
      ((continuous_const.mul hγ.continuous_deriv_one).neg)).intervalIntegrable _ _
  have hbd : doubleLayer (circleMap 0 1) (fun θ => conj (physicalCircleTrace F θ))
      (smoothDiskCutoff R hR F) = ∫ θ in (0 : ℝ)..(2 * Real.pi), G θ := by
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hz := circleMap_mem_closedBall (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ
    change conj (physicalCircleTrace F θ) *
      fderiv ℝ (smoothDiskCutoff R hR F) (circleMap 0 1 θ) (-(Complex.I * deriv (circleMap 0 1) θ)) = G θ
    dsimp only [G]
    rw [unitCircle_conormalDirection, fderiv_smoothDiskCutoff_eq hR F hz,
      localConformal_fderiv_closedDisk hR F hFs hhol hz, localConformal_circleTrace_deriv hR F hFs hhol]
    ring_nf; simp only [Complex.I_sq]; ring
  have he := congrArg Complex.re hdl
  rw [hbd, Complex.ofReal_re] at he
  rw [← he]
  change _ = Complex.reCLM (∫ θ in (0 : ℝ)..(2 * Real.pi), G θ)
  rw [← Complex.reCLM.intervalIntegral_comp_comm hi]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  dsimp [G]
  rw [show conj (physicalCircleTrace F θ) * (-(Complex.I * deriv (physicalCircleTrace F) θ)) =
    -(Complex.I * (conj (physicalCircleTrace F θ) * deriv (physicalCircleTrace F) θ)) by ring]
  simp

private theorem exists_localConformal_isBoundaryParam {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (closedBall (0 : ℂ) 1))
    (hnz : ∀ z ∈ sphere (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0)
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1)) :
    let hγ := contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
    let hp := physicalCircleTrace_periodic F
    let hv := localConformal_circleTrace_deriv_ne_zero hR F hFs hhol hnz
    IsBoundaryParam (F '' ball (0 : ℂ) 1) (normalizedArcCurve hγ hp hv) := by
  dsimp only
  let hγ := contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  let hp := physicalCircleTrace_periodic F
  let hv := localConformal_circleTrace_deriv_ne_zero hR F hFs hhol hnz
  obtain ⟨c, hτ, _, _⟩ := exists_isC1TraceReparam_normalizedArc hγ hp hv
  obtain ⟨K, hK⟩ := hτ.lipschitz
  let e := normalizedArcOrderIso hγ hp hv
  have he : LipschitzWith K e := hK
  have hcomp : normalizedArcCurve hγ hp hv ∘ e = physicalCircleTrace F :=
    funext fun θ => (normalizedArcCurve_factorization hγ hp hv θ).symm
  have hchain := ae_deriv_comp (normalizedArcCurve_lipschitz hγ hp hv) e.monotone he
  rw [hcomp] at hchain
  have harea : (∫ θ in (0 : ℝ)..(2 * Real.pi), signedAreaDensity (normalizedArcCurve hγ hp hv) θ) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), signedAreaDensity (physicalCircleTrace F) θ := by
    rw [integral_comp_orderIso he (normalizedArcOrderIso_zero hγ hp hv)
      (normalizedArcOrderIso_endpoint hγ hp hv) (signedAreaDensity (normalizedArcCurve hγ hp hv))]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hchain] with θ hθ _
    have hpoint : normalizedArcCurve hγ hp hv (e θ) = physicalCircleTrace F θ := congrFun hcomp θ
    simp only [signedAreaDensity]
    rw [hpoint, hθ, mul_left_comm, Complex.im_ofReal_mul]
  exact
    { lipschitz := ⟨_, normalizedArcCurve_lipschitz hγ hp hv⟩
      periodic := normalizedArcCurve_periodic hγ hp hv
      injOn := normalizedArcCurve_injOn hγ hp hv (physicalCircleTrace_injOn_of_closedDisk_inj F hinj)
      image := normalizedArcCurve_image_frontier hγ hp hv
        (localConformal_circleTrace_image_frontier hR F hFs hinj hL.1.1)
      const_speed := ⟨arcLen (physicalCircleTrace F) (2 * Real.pi) / (2 * Real.pi),
        div_pos (arcLen_period_pos_of_regular hγ hv) Real.two_pi_pos,
        Filter.Eventually.of_forall (normalizedArcCurve_speed hγ hp hv)⟩
      area := harea.trans
        (localConformal_circleTrace_signedArea hR F hFs hhol (hinj.mono ball_subset_closedBall)) }

private def rotateTraceReparam (τ : ℝ → ℝ) (t θ : ℝ) : ℝ := τ (θ + t) - τ t

private theorem rotateTraceReparam_isC1 {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (hlow : ∀ θ, c ≤ deriv τ θ)
    (hper : ∀ θ, τ (θ + 2 * Real.pi) = τ θ + 2 * Real.pi) (t : ℝ) :
    IsC1TraceReparam (rotateTraceReparam τ t) c := by
  obtain ⟨K, hK⟩ := hτ.lipschitz
  refine ⟨fun x y hxy => sub_le_sub_right (hτ.monotone (add_le_add hxy le_rfl)) (τ t),
    ⟨K, LipschitzWith.of_dist_le_mul fun x y => by
      simpa [rotateTraceReparam, Real.dist_eq] using hK.dist_le_mul (x + t) (y + t)⟩,
    (hτ.contDiff.comp (contDiff_id.add contDiff_const)).sub contDiff_const,
    by simp [rotateTraceReparam],
    by dsimp [rotateTraceReparam]; rw [add_comm (2 * Real.pi) t, hper]; ring,
    hτ.lower_pos, Eventually.of_forall fun θ => ?_⟩
  have hd : deriv (rotateTraceReparam τ t) θ = deriv τ (θ + t) :=
    ((((hτ.contDiff.differentiable_one (θ + t)).hasDerivAt.comp θ
      ((hasDerivAt_id θ).add_const t)).sub_const (τ t)).congr_deriv (by simp)).deriv
  rw [hd]; exact hlow (θ + t)

private theorem exists_smoothConformal_collar_of_regular_circleTrace
    (F : ℂ → ℂ) (hF : DiffContOnCl ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (closedBall (0 : ℂ) 1))
    (hΓ : ContDiff ℝ (⊤ : ℕ∞) (physicalCircleTrace F))
    (hΓnz : ∀ θ : ℝ, deriv (physicalCircleTrace F) θ ≠ 0) :
    ∃ (G : ℂ → ℂ) (R C K : ℝ) (e : OpenPartialHomeomorph ℂ ℂ),
      1 < R ∧ ContDiffOn ℝ (⊤ : ℕ∞) G (ball (0 : ℂ) R) ∧
      EqOn G F (closedBall (0 : ℂ) 1) ∧
      DifferentiableOn ℂ G (ball (0 : ℂ) 1) ∧
      InjOn G (closedBall (0 : ℂ) 1) ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ G z 1 ≠ 0) ∧
      (∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv G z‖ ^ 2) ∧
      (∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ G z 1‖ ≤ K) ∧
      (e : ℂ → ℂ) = G ∧ closedBall (0 : ℂ) 1 ⊆ e.source ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target := by
  obtain ⟨G, hGs, hGF, hhol⟩ := exists_smooth_holomorphic_fourier_collar_of_circleTrace F hF hΓ
  have hGinj : InjOn G (closedBall (0 : ℂ) 1) := fun z hz w hw he =>
    hinj hz hw ((hGF hz).symm.trans (he.trans (hGF hw)))
  have hR : (1 : ℝ) < 2 := by norm_num
  have hG₂ : ContDiffOn ℝ (⊤ : ℕ∞) G (ball (0 : ℂ) 2) := hGs.contDiffOn
  have hfd_eq {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : fderiv ℝ G z 1 = deriv G z := by
    rw [(hhol.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
    change fderiv ℂ G z 1 = _; rw [fderiv_eq_deriv_mul, mul_one]
  have htr : physicalCircleTrace G = physicalCircleTrace F :=
    funext fun θ => hGF (circleMap_mem_closedBall 0 (by norm_num) θ)
  have hnz : ∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ G z 1 ≠ 0 := fun z hz => by
    have hzNorm : ‖z‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hz
    rcases lt_or_eq_of_le hzNorm with hzlt | hzeq
    · have hzD : z ∈ ball (0 : ℂ) 1 := by simpa only [mem_ball, dist_zero_right] using hzlt
      rw [hfd_eq hzD]
      exact RiemannInterior.deriv_ne_zero_of_injOn isOpen_ball hhol
        (hGinj.mono ball_subset_closedBall) hzD
    · have hθ : circleMap 0 1 z.arg = z := by
        simpa only [circleMap_zero, hzeq, Complex.ofReal_one, one_mul] using
          Complex.norm_mul_exp_arg_mul_I z
      have hd : deriv (physicalCircleTrace F) z.arg = fderiv ℝ G z 1 * (z * Complex.I) := by
        simpa only [htr, hθ] using localConformal_circleTrace_deriv hR G hG₂ hhol z.arg
      exact fun hn => hΓnz z.arg (by rw [hd, hn, zero_mul])
  have hcont : ContinuousOn (fun z : ℂ => ‖fderiv ℝ G z 1‖) (closedBall (0 : ℂ) 1) :=
    ((hGs.continuous_fderiv (by simp)).clm_apply continuous_const).norm.continuousOn
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_isMinOn ⟨0, by simp⟩ hcont
  have hp : 0 < ‖fderiv ℝ G z₀ 1‖ := norm_pos_iff.mpr (hnz z₀ hz₀)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hcont
  obtain ⟨e, he, hsource, _, hes⟩ := exists_localConformalInverse hR G hG₂ hhol hGinj hnz
  refine ⟨G, 2, (‖fderiv ℝ G z₀ 1‖ ^ 2)⁻¹, max B 1, e, hR, hG₂, hGF, hhol, hGinj, hnz, ?_, ?_,
    he, hsource, hes⟩
  · intro z hz
    rw [← hfd_eq hz]
    calc 1 = (‖fderiv ℝ G z₀ 1‖ ^ 2)⁻¹ * ‖fderiv ℝ G z₀ 1‖ ^ 2 := (inv_mul_cancel₀ (by positivity)).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hmin (ball_subset_closedBall hz)) 2)
        (inv_nonneg.mpr (sq_nonneg _))
  · intro z hz
    have hb := hB z (ball_subset_closedBall hz)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hb
    exact hb.trans (le_max_left _ _)

theorem exists_synced_smoothConformal_coordinates {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) :
    ∃ (R C K : ℝ) (F : ℂ → ℂ) (e : OpenPartialHomeomorph ℂ ℂ) (c : ℝ) (τ : ℝ → ℝ) (L : NNReal),
      1 < R ∧ ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R) ∧
      DifferentiableOn ℂ F (ball (0 : ℂ) 1) ∧ InjOn F (ball (0 : ℂ) 1) ∧
      F '' ball (0 : ℂ) 1 = Ω ∧
      (∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2) ∧
      (∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K) ∧
      (e : ℂ → ℂ) = F ∧ closedBall (0 : ℂ) 1 ⊆ e.source ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target ∧
      IsC1TraceReparam τ c ∧ (∀ θ, F (circleMap 0 1 θ) = γ (τ θ)) ∧
      LipschitzWith L (physicalCircleTrace F) := by
  obtain ⟨G₀, hG₀, hG₀inj, hG₀image⟩ := exists_interior_conformal_map Ω hS.1.1 hb hsc
  let H := riemannMappingClosedExtension G₀
  have hHF : EqOn H G₀ (ball (0 : ℂ) 1) := riemannMappingClosedExtension_eqOn G₀ hG₀
  have hHs : DiffContOnCl ℂ H (ball (0 : ℂ) 1) :=
    DiffContOnCl.mk_ball (hG₀.congr fun z hz => hHF hz)
      (riemannMappingClosedExtension_continuousOn hb hS.isLipschitzDomain hsc G₀ hG₀ hG₀inj hG₀image)
  have hHinj : InjOn H (closedBall (0 : ℂ) 1) :=
    riemannMappingClosedExtension_injOn hb hS.isLipschitzDomain hsc G₀ hG₀ hG₀inj hG₀image
  have hHimage : H '' ball (0 : ℂ) 1 = Ω := hHF.image_eq.trans hG₀image
  obtain ⟨hΓ, hΓnz⟩ := riemannMapping_circleTrace_contDiff_and_deriv_ne_zero
    hb hS hsc G₀ hG₀ hG₀inj hG₀image
  obtain ⟨F₀, R₀, _, _, _, hR₀, hF₀s, hF₀H, hF₀hol, hF₀inj, hF₀nz, _, _, _, _, _⟩ :=
    exists_smoothConformal_collar_of_regular_circleTrace H hHs hHinj hΓ hΓnz
  have hF₀im : F₀ '' ball (0 : ℂ) 1 = Ω := (hF₀H.mono ball_subset_closedBall).image_eq.trans hHimage
  have hF₀tr : physicalCircleTrace F₀ = physicalCircleTrace H :=
    funext fun θ => hF₀H (circleMap_mem_closedBall 0 (by norm_num) θ)
  let hΓ₁ := contDiff_physicalCircleTrace_of_neighborhood hR₀ F₀ (hF₀s.of_le (WithTop.coe_le_coe.mpr le_top))
  let hp₀ := physicalCircleTrace_periodic F₀
  let hv₀ := localConformal_circleTrace_deriv_ne_zero hR₀ F₀ hF₀s hF₀hol
    (fun z hz => hF₀nz z (sphere_subset_closedBall hz))
  have hβ : IsBoundaryParam Ω (normalizedArcCurve hΓ₁ hp₀ hv₀) :=
    hF₀im ▸ exists_localConformal_isBoundaryParam hR₀ F₀ hF₀s hF₀hol hF₀inj
      (fun z hz => hF₀nz z (sphere_subset_closedBall hz)) (hF₀im.symm ▸ hS.isLipschitzDomain)
  have hβC1 : ContDiff ℝ 1 (normalizedArcCurve hΓ₁ hp₀ hv₀) := by
    let σ : ℝ → ℝ := (normalizedArcOrderIso hΓ₁ hp₀ hv₀).symm
    let a : ℝ := 2 * Real.pi / arcLen (physicalCircleTrace F₀) (2 * Real.pi)
    have ha : 0 < a := div_pos Real.two_pi_pos (arcLen_period_pos_of_regular hΓ₁ hv₀)
    have hv : Continuous fun t => deriv (physicalCircleTrace F₀) (σ t) :=
      hΓ₁.continuous_deriv_one.comp (normalizedArcOrderIso hΓ₁ hp₀ hv₀).symm.continuous
    refine contDiff_one_iff_deriv.mpr ⟨fun t => (normalizedArcCurve_hasDerivAt hΓ₁ hp₀ hv₀ t).differentiableAt, ?_⟩
    rw [funext fun t => (normalizedArcCurve_hasDerivAt hΓ₁ hp₀ hv₀ t).deriv]
    exact ((continuous_const.mul hv.norm).inv₀ fun t =>
      (mul_pos ha (norm_pos_iff.mpr (hv₀ (σ t)))).ne').smul hv
  have hβnz : ∀ t, deriv (normalizedArcCurve hΓ₁ hp₀ hv₀) t ≠ 0 := fun t => by
    apply norm_pos_iff.mp
    rw [normalizedArcCurve_speed hΓ₁ hp₀ hv₀]
    exact div_pos (arcLen_period_pos_of_regular hΓ₁ hv₀) Real.two_pi_pos
  obtain ⟨t, _, hshift⟩ := exists_boundaryParam_shift_of_bounded_domain hb hS.1 hβ hβC1 hβnz hγ
  let φ : ℝ := (normalizedArcOrderIso hΓ₁ hp₀ hv₀).symm t
  have hφval : normalizedArcReparam (physicalCircleTrace F₀) φ = t :=
    (normalizedArcOrderIso hΓ₁ hp₀ hv₀).apply_symm_apply t
  obtain ⟨c, hτ0, hτlow, hτper⟩ := exists_isC1TraceReparam_normalizedArc hΓ₁ hp₀ hv₀
  let τ : ℝ → ℝ := rotateTraceReparam (normalizedArcReparam (physicalCircleTrace F₀)) φ
  have hτ : IsC1TraceReparam τ c := rotateTraceReparam_isC1 hτ0 hτlow hτper φ
  let Hφ : ℂ → ℂ := fun z => H (circleMap 0 1 φ * z)
  have hHφs : DiffContOnCl ℂ Hφ (ball (0 : ℂ) 1) := by
    refine DiffContOnCl.mk_ball
      (hHs.differentiableOn.comp ((differentiable_const _).mul differentiable_id).differentiableOn
        fun z hz => by simpa [mem_ball, dist_zero_right] using hz) ?_
    have hcl : ContinuousOn H (closedBall (0 : ℂ) 1) := by
      simpa only [closure_ball (0 : ℂ) one_ne_zero] using hHs.continuousOn
    exact hcl.comp (continuous_const.mul continuous_id).continuousOn
      fun z hz => by simpa [mem_closedBall, dist_zero_right] using hz
  have hHφinj : InjOn Hφ (closedBall (0 : ℂ) 1) := fun z hz w hw he =>
    mul_left_cancel₀ (norm_ne_zero_iff.mp (by simp))
      (hHinj (by simpa [mem_closedBall, dist_zero_right] using hz)
        (by simpa [mem_closedBall, dist_zero_right] using hw) he)
  have hHφtr : physicalCircleTrace Hφ = fun θ => physicalCircleTrace H (θ + φ) :=
    funext fun θ => by simp [Hφ, physicalCircleTrace, circleMap_zero_mul, add_comm φ θ]
  have hΓφ : ContDiff ℝ (⊤ : ℕ∞) (physicalCircleTrace Hφ) :=
    hHφtr ▸ hΓ.comp (contDiff_id.add contDiff_const)
  have hΓφnz : ∀ θ, deriv (physicalCircleTrace Hφ) θ ≠ 0 := fun θ => by
    rw [hHφtr, deriv_comp_add_const]; exact hΓnz (θ + φ)
  obtain ⟨F, R, C, K, e, hR, hFs, hFHφ, hhol, hFinj, _, hC, hK, he, hsource, hes⟩ :=
    exists_smoothConformal_collar_of_regular_circleTrace Hφ hHφs hHφinj hΓφ hΓφnz
  have hrot_ball : (fun z : ℂ => circleMap 0 1 φ * z) '' ball (0 : ℂ) 1 = ball (0 : ℂ) 1 := by
    refine Subset.antisymm (by rintro _ ⟨z, hz, rfl⟩; simpa [mem_ball, dist_zero_right] using hz)
      fun z hz => ⟨circleMap 0 1 (-φ) * z, by simpa [mem_ball, dist_zero_right] using hz, ?_⟩
    dsimp only; rw [← mul_assoc, circleMap_zero_mul, one_mul, add_neg_cancel]; simp [circleMap]
  have hFim : F '' ball (0 : ℂ) 1 = Ω := by
    calc F '' ball (0 : ℂ) 1 = Hφ '' ball (0 : ℂ) 1 := (hFHφ.mono ball_subset_closedBall).image_eq
      _ = H '' ((fun z => circleMap 0 1 φ * z) '' ball (0 : ℂ) 1) := (image_image H _ _).symm
      _ = Ω := by rw [hrot_ball, hHimage]
  have hFtr : physicalCircleTrace F = physicalCircleTrace Hφ :=
    funext fun θ => hFHφ (circleMap_mem_closedBall 0 (by norm_num) θ)
  have hΓF₁ : ContDiff ℝ 1 (physicalCircleTrace F) :=
    hFtr ▸ hΓφ.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨_, M, _, hM0, hbounds⟩ := exists_regular_periodic_speed_bounds hΓF₁
    (physicalCircleTrace_periodic F) (fun θ => by rw [hFtr]; exact hΓφnz θ)
  have hLip : LipschitzWith (Real.toNNReal M) (physicalCircleTrace F) := by
    refine lipschitzWith_of_nnnorm_deriv_le hΓF₁.differentiable_one fun θ => NNReal.coe_le_coe.mp ?_
    change ‖deriv (physicalCircleTrace F) θ‖ ≤ (Real.toNNReal M : ℝ)
    rw [Real.coe_toNNReal _ hM0]; exact (hbounds θ).2
  refine ⟨R, C, K, F, e, c, τ, Real.toNNReal M, hR, hFs, hhol,
    hFinj.mono ball_subset_closedBall, hFim, hC, hK, he, hsource, hes, hτ, fun θ => ?_, hLip⟩
  calc F (circleMap 0 1 θ) = physicalCircleTrace F₀ (θ + φ) :=
        (congrFun hFtr θ).trans ((congrFun hHφtr θ).trans (congrFun hF₀tr (θ + φ)).symm)
    _ = normalizedArcCurve hΓ₁ hp₀ hv₀ (normalizedArcReparam (physicalCircleTrace F₀) (θ + φ)) :=
        normalizedArcCurve_factorization hΓ₁ hp₀ hv₀ (θ + φ)
    _ = normalizedArcCurve hΓ₁ hp₀ hv₀ (τ θ + t) := by
        congr 1; simp [τ, rotateTraceReparam, hφval]
    _ = γ (τ θ) := (hshift (τ θ)).symm

end PolyaNeumann
end
