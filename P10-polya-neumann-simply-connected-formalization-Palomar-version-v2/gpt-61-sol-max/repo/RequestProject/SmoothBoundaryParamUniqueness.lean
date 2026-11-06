module

public import RequestProject.PlanarTypes

public import RequestProject.CirclePeriod

public import RequestProject.PlanarGeometry

public import RequestProject.ArcLength
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

/-!
# Actual lifts between physical boundary parametrizations

The six physical `IsBoundaryParam` fields give an actual homeomorphism from
the additive circle onto the physical frontier.  Lifting the resulting circle
homeomorphism and its inverse gives a genuine real homeomorphism, rather than
an assumed reparametrization.  A regular C¹ reference curve then gives actual
local Lipschitz bounds and an almost-everywhere chain rule for this lift.

Absolute continuity and the two actual constant speeds make the lift affine.
Single traversal forces its slope to be `1` or `-1`; the signed-area fields
select `1` whenever the physical area is nonzero.  In particular this gives
exact shift synchronization for an actual bounded domain, without a new
hypothesis in the original bounded-domain theorem.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter
open scoped ComplexConjugate Topology



/-- The actual periodic curve descended to the additive circle. -/
def boundaryParamCircleMap (γ : ComplexCurve)  :=
  AddCircle.liftIco circlePeriod 0 γ

section
variable {Ω } {γ } (hγ : IsBoundaryParam Ω γ)
include Ω γ hγ

/-- The circle map agrees with the original curve at every real parameter. -/
theorem boundaryParamCircleMap_coe (θ : ℝ) :
    boundaryParamCircleMap γ (θ : AddCircle circlePeriod) = γ θ := by
  change γ (toIcoMod Real.two_pi_pos 0 θ) = γ θ
  rw [toIcoMod, hγ.periodic.sub_zsmul_eq]

theorem boundaryParamCircleMap_continuous : Continuous (boundaryParamCircleMap γ) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  exact AddCircle.liftIco_zero_continuous
    (by simpa   using (hγ.periodic 0).symm) hK.continuous.continuousOn

theorem boundaryParamCircleMap_mem_frontier q :
    boundaryParamCircleMap γ q ∈ frontier Ω := by
  rw [← hγ.image]
  refine ⟨(AddCircle.equivIco circlePeriod 0 q), ?_, rfl⟩
  grind

theorem boundaryParamCircleMap_injective : Function.Injective (boundaryParamCircleMap γ) := by
  intro q r hqr
  apply (AddCircle.equivIco circlePeriod 0).injective
  apply Subtype.ext
  exact hγ.injOn
    (by grind)
    (by grind) hqr

theorem boundaryParam_eq_iff_circle_coe_eq x y :
    γ x = γ y ↔ (x : AddCircle circlePeriod) = (y : AddCircle circlePeriod) := by
  constructor
  · intro hxy
    apply boundaryParamCircleMap_injective hγ
    grind only [boundaryParamCircleMap_coe]
  · intro hxy
    rw [← boundaryParamCircleMap_coe hγ x, ← boundaryParamCircleMap_coe hγ y, hxy]

end


/-- The actual map with codomain the physical frontier.  Its membership proof
is public because it is part of this computational definition. -/
def boundaryParamFrontierMap {Ω : PlanarSet} {γ : ComplexCurve}
    (hγ : IsBoundaryParam Ω γ) : AddCircle circlePeriod → frontier Ω :=
  fun q => ⟨boundaryParamCircleMap γ q, boundaryParamCircleMap_mem_frontier hγ q⟩

section
variable {Ω } {γ } (hγ : IsBoundaryParam Ω γ)
include Ω γ hγ

theorem boundaryParamFrontierMap_continuous : Continuous (boundaryParamFrontierMap hγ) :=
  (boundaryParamCircleMap_continuous hγ).subtype_mk _

theorem boundaryParamFrontierMap_bijective : Function.Bijective (boundaryParamFrontierMap hγ) := by
  constructor
  · intro q r hqr
    exact boundaryParamCircleMap_injective hγ (congrArg Subtype.val hqr)
  · intro z
    have hz : (z : ℂ) ∈ γ '' boundaryInterval := by
      rw [hγ.image]
      exact z.property
    obtain ⟨θ, hθ, hθz⟩ := hz
    refine ⟨θ, Subtype.ext ?_⟩
    exact (boundaryParamCircleMap_coe hγ θ).trans hθz

end


/-- The genuine compact-to-Hausdorff boundary homeomorphism. -/
def boundaryParamCircleHomeomorph {Ω } {γ }
    (hγ : IsBoundaryParam Ω γ)  :=
  (Equiv.ofBijective (boundaryParamFrontierMap hγ)
    (boundaryParamFrontierMap_bijective hγ)).toHomeomorphOfContinuousClosed
      (boundaryParamFrontierMap_continuous hγ)
      (boundaryParamFrontierMap_continuous hγ).isClosedMap

/-- Two actual parametrizations induce an actual homeomorphism of the circle. -/
def boundaryParamCircleChange {Ω } {β γ }
    (hβ : IsBoundaryParam Ω β) (hγ : IsBoundaryParam Ω γ)  :=
  (boundaryParamCircleHomeomorph hγ).trans (boundaryParamCircleHomeomorph hβ).symm

section
variable {Ω } {β γ : ComplexCurve} (hβ : IsBoundaryParam Ω β)

include Ω β γ hβ in
theorem boundaryParamCircleChange_apply (hγ : IsBoundaryParam Ω γ)
    q :
    boundaryParamCircleMap β (boundaryParamCircleChange hβ hγ q) =
      boundaryParamCircleMap γ q := congrArg Subtype.val
    ((boundaryParamCircleHomeomorph hβ).apply_symm_apply
      (boundaryParamCircleHomeomorph hγ q))

/-- A homeomorphism of the genuine additive circle has a genuine real
homeomorphic lift.  The inverse lift is constructed independently and proved
to be an inverse by uniqueness of covering lifts. -/
theorem exists_realHomeomorph_lift_of_addCircleHomeomorph
    (e : AddCircle circlePeriod ≃ₜ AddCircle circlePeriod) :
    ∃ t ∈ Ico 0 circlePeriod, ∃ T : ℝ ≃ₜ ℝ,
      T 0 = t ∧ ∀ θ : ℝ,
        (T θ : AddCircle circlePeriod) = e (θ : AddCircle circlePeriod) := by
  letI  := LocPathConnectedSpace.of_bases
    (fun x : ℝ => nhds_basis_Ioo x)
    (fun x b hx => (convex_Ioo (𝕜 := ℝ) b.1 b.2).isPathConnected ⟨x, hx⟩)
  let t : ℝ := AddCircle.equivIco circlePeriod 0 (e 0)
  have ht : t ∈ Ico 0 circlePeriod := by
    grind
  have htcoe : (t : AddCircle circlePeriod) = e 0 :=
    (AddCircle.equivIco circlePeriod 0).symm_apply_apply (e 0)
  let f : C(ℝ, AddCircle circlePeriod) :=
    ⟨fun θ => e θ,
      e.continuous.comp (AddCircle.continuous_mk' circlePeriod)⟩
  have hf0 : (t : AddCircle circlePeriod) = f 0 := by
    assumption
  obtain ⟨T, hT, _⟩ :=
    (AddCircle.isCoveringMap_coe circlePeriod).existsUnique_continuousMap_lifts f 0 t hf0
  have hTcoe θ :
      (T θ : AddCircle circlePeriod) = e (θ : AddCircle circlePeriod) :=
    congrFun hT.2 θ
  let f' : C(ℝ, AddCircle circlePeriod) :=
    ⟨fun θ => e.symm θ,
      e.symm.continuous.comp (AddCircle.continuous_mk' circlePeriod)⟩
  have hf't : ((0 : ℝ) : AddCircle circlePeriod) = f' t := by
    change 0 = e.symm t
    rw [htcoe, e.symm_apply_apply]
  obtain ⟨S, hS, _⟩ :=
    (AddCircle.isCoveringMap_coe circlePeriod).existsUnique_continuousMap_lifts f' t 0 hf't
  have hScoe (θ : ℝ) :
      (S θ : AddCircle circlePeriod) = e.symm (θ : AddCircle circlePeriod) :=
    congrFun hS.2 θ
  have hST : (fun θ : ℝ => S (T θ)) = id := by
    refine (AddCircle.isCoveringMap_coe circlePeriod).eq_of_comp_eq
      (S.continuous.comp T.continuous) continuous_id ?_ 0 ?_
    · funext θ
      change (S (T θ)) = (θ : AddCircle circlePeriod)
      rw [hScoe, hTcoe, e.symm_apply_apply]
    grind
  have hTS : (fun θ : ℝ => T (S θ)) = id := by
    refine (AddCircle.isCoveringMap_coe circlePeriod).eq_of_comp_eq
      (T.continuous.comp S.continuous) continuous_id ?_ t ?_
    · funext θ
      change (T (S θ)) = (θ : AddCircle circlePeriod)
      rw [hTcoe, hScoe, e.apply_symm_apply]
    grind
  let H : ℝ ≃ₜ ℝ :=
    { toFun := T
      invFun := S
      left_inv := (congrFun hST)
      right_inv := (congrFun hTS)
      continuous_toFun := T.continuous
      continuous_invFun := S.continuous }
  exact ⟨t, ht, H, hT.1, hTcoe⟩

include Ω β γ hβ in
/-- Actual real synchronization up to a homeomorphic lift, with no assumed
reparametrization, orientation, or equality of speeds. -/
theorem exists_boundaryParam_realHomeomorph (hγ : IsBoundaryParam Ω γ) :
    ∃ t ∈ Ico 0 circlePeriod, ∃ T : ℝ ≃ₜ ℝ,
      T 0 = t ∧ (∀ θ : ℝ, γ θ = β (T θ)) ∧ (StrictMono T ∨ StrictAnti T) := by
  obtain ⟨t, ht, T, hT0, hTcoe⟩ :=
    exists_realHomeomorph_lift_of_addCircleHomeomorph (boundaryParamCircleChange hβ hγ)
  refine ⟨t, ht, T, hT0, ?_, T.continuous.strictMono_of_inj T.injective⟩
  grind only [boundaryParamCircleMap, boundaryParamCircleMap_coe, boundaryParamCircleChange, boundaryParamCircleChange_apply]

/-- Nonzero C¹ velocity gives a genuine local inverse chord bound between
any two parameters, by the real tangent projection and the mean value theorem. -/
theorem exists_regularCurve_local_inverse_bound (β : ComplexCurve)
    (hβ : ContDiff ℝ 1 β) t (ht : deriv β t ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x ∈ Ioo (t - r) (t + r), ∀ y ∈ Ioo (t - r) (t + r),
        |x - y| ≤ C * ‖β x - β y‖ := by
  let c  := conj (deriv β t)
  let D  := Complex.normSq (deriv β t)
  let f  := fun x => (c * β x).re
  have hD : 0 < D := Complex.normSq_pos.mpr ht
  have hc : 0 < ‖c‖ := by
    aesop
  have hdt : (c * deriv β t).re = D := by
    aesop
  have hdf x : HasDerivAt f (c * deriv β x).re x := by
    have hd := ((hβ.differentiable_one x).hasDerivAt).const_mul c
    simpa only [Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd
  have hfc : Continuous f :=
    Complex.continuous_re.comp (continuous_const.mul hβ.continuous)
  have hfd : Differentiable ℝ f := fun x => (hdf x).differentiableAt
  have hdc : Continuous (fun x : ℝ => (c * deriv β x).re) :=
    Complex.continuous_re.comp (continuous_const.mul hβ.continuous_deriv_one)
  have hopen : IsOpen {x : ℝ | D / 2 < (c * deriv β x).re} :=
    isOpen_lt continuous_const hdc
  have htmem : t ∈ {x : ℝ | D / 2 < (c * deriv β x).re} := by
    simp_all
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds htmem)
  have hlower (x : ℝ) (hx : x ∈ Ioo (t - r) (t + r)) : D / 2 ≤ deriv f x := by
    rw [(hdf x).deriv]
    have hxball : x ∈ Metric.ball t r := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    exact le_of_lt (hball hxball)
  have hgrowth := (convex_Ioo (𝕜 := ℝ) (t - r) (t + r)).mul_sub_le_image_sub_of_le_deriv
    hfc.continuousOn hfd.differentiableOn
    (fun x hx => hlower x (interior_subset hx))
  refine ⟨r, hr, ‖c‖ / (D / 2), div_pos hc (half_pos hD), ?_⟩
  intro x hx y hy
  have hp : D / 2 * |x - y| ≤ |f x - f y| := by
    by_cases hxy : x ≤ y
    · calc
        _ = D / 2 * (y - x) := by rw [abs_of_nonpos (sub_nonpos.mpr hxy)]; ring
        _ ≤ f y - f x := hgrowth x hx y hy hxy
        _ ≤ |f y - f x| := le_abs_self _
        _ = |f x - f y| := abs_sub_comm _ _
    · have hyx  := (not_le.mp hxy).le
      calc
        _ = D / 2 * (x - y) := by rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
        _ ≤ f x - f y := hgrowth y hy x hx hyx
        _ ≤ |f x - f y| := le_abs_self _
  have hproj : f x - f y = (c * (β x - β y)).re := by
    simp only [f, mul_sub, Complex.sub_re]
  have hpn : D / 2 * |x - y| ≤ ‖c‖ * ‖β x - β y‖ := by
    calc
      _ ≤ |f x - f y| := hp
      _ = |(c * (β x - β y)).re| := by rw [hproj]
      _ ≤ ‖c * (β x - β y)‖ := Complex.abs_re_le_norm _
      _ = _ := norm_mul _ _
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (half_pos hD)).mpr (by simpa only [mul_comm] using hpn)

/-- The actual lift is locally Lipschitz because its reference curve has a
genuine local inverse bound and the arbitrary physical curve is Lipschitz. -/
theorem boundaryParamLift_locallyLipschitz  
    (hβ : ContDiff ℝ 1 β) (hnz : ∀ t, deriv β t ≠ 0)
    (hγ : IsBoundaryParam Ω γ) (T : ℝ ≃ₜ ℝ)
    (hcomp : ∀ θ : ℝ, γ θ = β (T θ)) : LocallyLipschitz (T : RealMap) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  intro θ
  obtain ⟨r, hr, C, hC, hbound⟩ :=
    exists_regularCurve_local_inverse_bound β hβ (T θ) (hnz (T θ))
  let U  := T ⁻¹' Ioo (T θ - r) (T θ + r)
  have hU : U ∈ 𝓝 θ :=
    T.continuous.continuousAt.preimage_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith))
  refine ⟨Real.toNNReal (C * K), U, hU, ?_⟩
  apply LipschitzOnWith.of_dist_le'
  intro x hx y hy
  calc
    dist (T x) (T y) = |T x - T y| := Real.dist_eq _ _
    _ ≤ C * ‖β (T x) - β (T y)‖ := hbound (T x) hx (T y) hy
    _ = C * dist (γ x) (γ y) := by rw [← hcomp x, ← hcomp y, dist_eq_norm]
    _ ≤ C * (K * dist x y) :=
      mul_le_mul_of_nonneg_left (hK.dist_le_mul x y) hC.le
    _ = (C * K) * dist x y := by ring

/-- A genuine real homeomorphism is differentiable almost everywhere; no
differentiability or absolute-continuity premise is imposed on its lift. -/
theorem realHomeomorph_ae_differentiable (T : ℝ ≃ₜ ℝ) :
    ∀ᵐ θ : ℝ ∂volume, DifferentiableAt ℝ (T : RealMap) θ := by
  obtain hT | hT := T.continuous.strictMono_of_inj T.injective
  · exact hT.monotone.ae_differentiableAt
  · have hn : Monotone (fun θ : ℝ => -T θ) :=
      fun x y hxy => neg_le_neg (hT.antitone hxy)
    filter_upwards [hn.ae_differentiableAt] with θ hθ
    simp_all

/-- The actual almost-everywhere derivative chain for the homeomorphic lift. -/
theorem boundaryParamLift_ae_deriv_chain {β γ : ComplexCurve}
    (hβ : ContDiff ℝ 1 β) (T : ℝ ≃ₜ ℝ)
    (hcomp : ∀ θ : ℝ, γ θ = β (T θ)) :
    ∀ᵐ θ : ℝ ∂volume, deriv γ θ = deriv (T : RealMap) θ • deriv β (T θ) := by
  have hfun  := funext hcomp
  filter_upwards [realHomeomorph_ae_differentiable T] with θ hθ
  rw [hfun]
  exact ((hβ.differentiable_one (T θ)).hasDerivAt.scomp θ hθ.hasDerivAt).deriv

/-- The real speed of a C¹ physical boundary parametrization is constant
everywhere, because its genuine almost-everywhere speed is continuous. -/
theorem boundaryParam_contDiff_constant_speed  
    (hβ : IsBoundaryParam Ω β) (hβC1 : ContDiff ℝ 1 β) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ : ℝ, ‖deriv β θ‖ = c := by
  obtain ⟨c, hc, hspeed⟩ := hβ.const_speed
  have heq  :=
    Measure.eq_of_ae_eq hspeed hβC1.continuous_deriv_one.norm continuous_const
  tauto

include Ω β γ hβ in
/-- The actual constant-speed fields determine the absolute derivative of
the constructed lift.  Neither equality of the two speeds nor its orientation
is assumed. -/
theorem boundaryParamLift_ae_abs_deriv (hβC1 : ContDiff ℝ 1 β)
    (hγ : IsBoundaryParam Ω γ) (T : ℝ ≃ₜ ℝ)
    (hcomp : ∀ θ : ℝ, γ θ = β (T θ)) :
    ∃ cβ : ℝ, 0 < cβ ∧ ∃ cγ : ℝ, 0 < cγ ∧
      (∀ θ : ℝ, ‖deriv β θ‖ = cβ) ∧
      (∀ᵐ θ : ℝ ∂volume, |deriv (T : RealMap) θ| = cγ / cβ) := by
  obtain ⟨cβ, hcβ, hβspeed⟩ := boundaryParam_contDiff_constant_speed hβ hβC1
  obtain ⟨cγ, hcγ, hγspeed⟩ := hγ.const_speed
  refine ⟨cβ, hcβ, cγ, hcγ, hβspeed, ?_⟩
  filter_upwards [hγspeed, boundaryParamLift_ae_deriv_chain hβC1 T hcomp] with θ hθ hchain
  have heq : |deriv (T : RealMap) θ| * cβ = cγ := by
    simp_all
  exact (eq_div_iff hcβ.ne').mpr heq

end


/-- Genuine real absolute continuity makes a locally Lipschitz function with
constant a.e. derivative affine.  This uses the actual AC fundamental theorem. -/
theorem locallyLipschitz_eq_affine_of_ae_deriv  
    (hf : LocallyLipschitz f) (hd : ∀ᵐ θ : ℝ ∂volume, deriv f θ = a) :
    ∀ θ : ℝ, f θ = a * θ + f 0 := by
  intro θ
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (s := uIcc 0 θ) isCompact_uIcc hf.locallyLipschitzOn
  have hi : ∫ s in (0 : ℝ)..θ, deriv f s = ∫ s in (0 : ℝ)..θ, a := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hd] with s hs _ using hs
  have hFTC := hK.absolutelyContinuousOnInterval.integral_deriv_eq_sub
  rw [hi, intervalIntegral.integral_const] at hFTC
  simp   at hFTC
  linarith

section
variable {Ω } {β γ } (hβ : IsBoundaryParam Ω β) (hβC1 : ContDiff ℝ 1 β) (hnz : ∀ θ, deriv β θ ≠ 0) (hγ : IsBoundaryParam Ω γ)

include Ω β γ hβ hβC1 hnz hγ in
/-- Constant-speed physical curves force the actual real lift to be affine;
the slope is derived from their two genuine speeds. -/
theorem boundaryParamLift_affine
    (T : ℝ ≃ₜ ℝ) (hcomp : ∀ θ : ℝ, γ θ = β (T θ)) :
    ∃ a : ℝ, a ≠ 0 ∧ ∀ θ : ℝ, T θ = a * θ + T 0 := by
  obtain ⟨cβ, hcβ, cγ, hcγ, _, habs⟩ :=
    boundaryParamLift_ae_abs_deriv hβ hβC1 hγ T hcomp
  have hc  := div_pos hcγ hcβ
  have hLip := boundaryParamLift_locallyLipschitz hβC1 hnz hγ T hcomp
  obtain hmono | hanti := T.continuous.strictMono_of_inj T.injective
  · refine ⟨cγ / cβ, hc.ne', locallyLipschitz_eq_affine_of_ae_deriv hLip ?_⟩
    filter_upwards [habs] with θ hθ
    rwa [abs_of_nonneg hmono.monotone.deriv_nonneg] at hθ
  · refine ⟨-(cγ / cβ), neg_ne_zero.mpr hc.ne',
      locallyLipschitz_eq_affine_of_ae_deriv hLip ?_⟩
    filter_upwards [habs] with θ hθ
    rw [abs_of_nonpos hanti.antitone.deriv_nonpos] at hθ
    linarith

/-- The same boundary image and single traversal force an affine lift's
slope to be an integer unit.  Thus its slope is exactly `1` or `-1`. -/
theorem boundaryParamLift_affine_unit  
    (hβ : IsBoundaryParam Ω β) (hγ : IsBoundaryParam Ω γ)
    (T : ℝ ≃ₜ ℝ) (hcomp : ∀ θ : ℝ, γ θ = β (T θ))
    a (ha : ∀ θ : ℝ, T θ = a * θ + T 0) : a = 1 ∨ a = -1 := by
  have hperne  := Real.two_pi_pos.ne'
  have hβsame : β (T circlePeriod) = β (T 0) := by
    calc
      β (T circlePeriod) = γ circlePeriod := (hcomp circlePeriod).symm
      _ = γ 0 := by simpa only [zero_add] using hγ.periodic 0
      _ = β (T 0) := hcomp 0
  have hco := (boundaryParam_eq_iff_circle_coe_eq hβ _ _).mp hβsame
  have hzero : ((a * circlePeriod : ℝ) : AddCircle circlePeriod) = 0 := by
    have hsub : ((T circlePeriod - T 0 : ℝ) : AddCircle circlePeriod) = 0 := by
      rw [AddCircle.coe_sub, hco, sub_self]
    grind
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff circlePeriod).mp hzero
  have hmR : (m : ℝ) = a := by
    grind
  let x  := T.symm (T 0 + 2 * Real.pi)
  have hTx : T x = T 0 + 2 * Real.pi := T.apply_symm_apply _
  have hγsame : γ x = γ 0 := by
    rw [hcomp x, hTx, hβ.periodic (T 0), ← hcomp 0]
  have hxzero : (x : AddCircle circlePeriod) = 0 := by
    simpa only [AddCircle.coe_zero] using
      (boundaryParam_eq_iff_circle_coe_eq hγ x 0).mp hγsame
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff circlePeriod).mp hxzero
  have hmnR : (m : ℝ) * (n : ℝ) = 1 := by
    grind
  have hmn : m * n = 1 := by exact_mod_cast hmnR
  obtain hmone | hmneg := Int.eq_one_or_neg_one_of_mul_eq_one hmn
  · grind
  grind

include Ω β γ hβ hβC1 hnz hγ in
/-- Actual synchronization has only the two possible unit-speed orientations.
No speed equality, lift, or orientation is supplied as a premise. -/
theorem exists_boundaryParam_shift_or_reverse :
    ∃ t ∈ Ico 0 circlePeriod,
      (∀ θ : ℝ, γ θ = β (θ + t)) ∨ (∀ θ : ℝ, γ θ = β (-θ + t)) := by
  obtain ⟨t, ht, T, hT0, hcomp, _⟩ := exists_boundaryParam_realHomeomorph hβ hγ
  obtain ⟨a, _, ha⟩ := boundaryParamLift_affine hβ hβC1 hnz hγ T hcomp
  refine ⟨t, ht, ?_⟩
  obtain haone | haneg := boundaryParamLift_affine_unit hβ hγ T hcomp a ha
  · grind
  grind

theorem integral_signedAreaDensity_add_shift 
    (hper : Function.Periodic β circlePeriod) t :
    (∫ θ in (0 : ℝ)..circlePeriod, signedAreaDensity (fun θ => β (θ + t)) θ) =
      ∫ θ in (0 : ℝ)..circlePeriod, signedAreaDensity β θ := by
  calc
    _ = ∫ θ in (0)..circlePeriod, signedAreaDensity β (θ + t) := by
      simp  [signedAreaDensity, deriv_comp_add_const]
    _ = ∫ θ in t..t + 2 * Real.pi, signedAreaDensity β θ := by
      rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm circlePeriod t]
    _ = _ := integral_signedAreaDensity_shift hper t

/-- The reverse lift reverses the actual signed area, even with a shifted
origin.  This is the orientation test, not an assumed orientation. -/
theorem integral_signedAreaDensity_reverse_shift 
    (hper : Function.Periodic β circlePeriod) t :
    (∫ θ in (0 : ℝ)..circlePeriod, signedAreaDensity (fun θ => β (-θ + t)) θ) =
      -(∫ θ in (0 : ℝ)..circlePeriod, signedAreaDensity β θ) := by
  let δ  := fun θ => β (θ + t)
  have hδper : Function.Periodic δ circlePeriod := by
    intro θ
    change β ((θ + 2 * Real.pi) + t) = β (θ + t)
    rw [show (θ + 2 * Real.pi) + t = (θ + t) + 2 * Real.pi by ring, hper]
  have hd θ :
      signedAreaDensity (fun θ => β (-θ + t)) θ = -signedAreaDensity δ (-θ) := by
    change signedAreaDensity (fun θ => δ (-θ)) θ = -signedAreaDensity δ (-θ)
    simp  [signedAreaDensity, deriv_comp_neg]
  simp_rw [hd]
  rw [intervalIntegral.integral_neg,
    intervalIntegral.integral_comp_neg ((signedAreaDensity δ)), neg_zero]
  have hshift := integral_signedAreaDensity_shift hδper (-circlePeriod)
  rw [neg_add_cancel] at hshift
  rw [hshift]
  exact congrArg Neg.neg (integral_signedAreaDensity_add_shift hper t)

include Ω β γ hβ hβC1 hnz hγ in
/-- The physical signed-area fields exclude the reverse lift at nonzero
physical area, and give the exact shift requested by boundary synchronization. -/
theorem exists_boundaryParam_shift_of_area_ne_zero
    (harea : (volume Ω).toReal ≠ 0) :
    ∃ t ∈ boundaryInterval, ∀ θ : ℝ, γ θ = β (θ + t) := by
  obtain ⟨t, ht, hshift | hreverse⟩ := exists_boundaryParam_shift_or_reverse hβ hβC1 hnz hγ
  · exact ⟨t, Ico_subset_Icc_self ht, hshift⟩
  · have hfun  := funext hreverse
    have hγarea : (∫ θ in (0 : ℝ)..circlePeriod, signedAreaDensity γ θ) =
        2 * (volume Ω).toReal := hγ.area
    have hβarea : (∫ θ in (0 : ℝ)..circlePeriod, signedAreaDensity β θ) =
        2 * (volume Ω).toReal := hβ.area
    rw [hfun, integral_signedAreaDensity_reverse_shift hβ.periodic t, hβarea] at hγarea
    exact (harea (by linarith)).elim

end


/-- The original bounded-domain geometry itself supplies positive finite
area.  Thus a smooth regular physical boundary parameter synchronizes with
every original physical boundary parameter by an actual cyclic shift. -/
theorem exists_boundaryParam_shift_of_bounded_domain  
    (hb : Bornology.IsBounded Ω) (hΩ : IsDomain Ω)
    (hβ : IsBoundaryParam Ω β) (hβC1 : ContDiff ℝ 1 β)
    (hnz : ∀ θ, deriv β θ ≠ 0) (hγ : IsBoundaryParam Ω γ) :
    ∃ t ∈ boundaryInterval, ∀ θ : ℝ, γ θ = β (θ + t) := by
  have hvolpos  :=
    ENNReal.toReal_pos (hΩ.1.measure_pos volume hΩ.2.nonempty).ne' hb.measure_lt_top.ne
  grind only [exists_boundaryParam_shift_of_area_ne_zero]

end PolyaNeumann

end
