module

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
open scoped Real ComplexConjugate Topology

variable {γ : ℝ → ℂ}

local instance boundaryParamPeriod_pos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The actual periodic curve descended to the additive circle. -/
def boundaryParamCircleMap (γ : ℝ → ℂ) : AddCircle (2 * Real.pi) → ℂ :=
  AddCircle.liftIco (2 * Real.pi) 0 γ

/-- The circle map agrees with the original curve at every real parameter. -/
theorem boundaryParamCircleMap_coe  
    (hγ : IsBoundaryParam Ω γ) (θ : ℝ) :
    boundaryParamCircleMap γ (θ : AddCircle (2 * Real.pi)) = γ θ := by
  change γ (toIcoMod Real.two_pi_pos 0 θ) = _
  rw [toIcoMod, hγ.periodic.sub_zsmul_eq]

theorem boundaryParamCircleMap_injective  
    (hγ : IsBoundaryParam Ω γ) : Function.Injective (boundaryParamCircleMap γ) := by
  intro q r hqr
  apply (AddCircle.equivIco (2 * Real.pi) 0).injective
  apply Subtype.ext
  exact hγ.injOn
    (by simpa using (AddCircle.equivIco (2 * Real.pi) 0 q).property)
    (by simpa using (AddCircle.equivIco (2 * Real.pi) 0 r).property) hqr

theorem boundaryParam_eq_iff_circle_coe_eq  
    (hγ : IsBoundaryParam Ω γ) x y :
    γ x = γ y ↔ (x : AddCircle (2 * Real.pi)) = (y : AddCircle (2 * Real.pi)) := by
  constructor
  · intro hxy
    apply boundaryParamCircleMap_injective hγ
    rwa [boundaryParamCircleMap_coe hγ x, boundaryParamCircleMap_coe hγ y]
  · intro hxy
    rw [← boundaryParamCircleMap_coe hγ x, ← boundaryParamCircleMap_coe hγ y, hxy]

/-- The actual map with codomain the physical frontier.  Its membership proof
is public because it is part of this computational definition. -/
def boundaryParamFrontierMap  
    (hγ : IsBoundaryParam Ω γ) : AddCircle (2 * Real.pi) → frontier Ω :=
  fun q => ⟨boundaryParamCircleMap γ q, (show boundaryParamCircleMap γ q ∈ frontier Ω by
    rw [← hγ.image]
    refine ⟨(AddCircle.equivIco (2 * Real.pi) 0 q : ℝ), ?_, rfl⟩
    exact Ico_subset_Icc_self (by
      simpa using (AddCircle.equivIco (2 * Real.pi) 0 q).property))⟩

theorem boundaryParamFrontierMap_continuous {Ω : Set ℂ} 
    (hγ : IsBoundaryParam Ω γ) : Continuous (boundaryParamFrontierMap hγ) :=
  (show Continuous (boundaryParamCircleMap γ) by
    obtain ⟨K, hK⟩ := hγ.lipschitz
    exact AddCircle.liftIco_zero_continuous
      (by simpa using (hγ.periodic 0).symm) hK.continuous.continuousOn).subtype_mk _

/-- The genuine compact-to-Hausdorff boundary homeomorphism. -/
def boundaryParamCircleHomeomorph  
    (hγ : IsBoundaryParam Ω γ) : AddCircle (2 * Real.pi) ≃ₜ frontier Ω :=
  (Equiv.ofBijective (boundaryParamFrontierMap hγ)
    (show Function.Bijective (boundaryParamFrontierMap hγ) by
      constructor
      · intro q r hqr
        exact boundaryParamCircleMap_injective hγ (congrArg Subtype.val hqr)
      · intro z
        have hz : (z : ℂ) ∈ γ '' Icc 0 (2 * Real.pi) := by
          rw [hγ.image]
          exact z.property
        obtain ⟨θ, hθ, hθz⟩ := hz
        refine ⟨(θ : AddCircle (2 * Real.pi)), Subtype.ext ?_⟩
        exact (boundaryParamCircleMap_coe hγ θ).trans hθz)).toHomeomorphOfContinuousClosed
      (boundaryParamFrontierMap_continuous hγ)
      (boundaryParamFrontierMap_continuous hγ).isClosedMap

/-- Two actual parametrizations induce an actual homeomorphism of the circle. -/
def boundaryParamCircleChange  
    (hβ : IsBoundaryParam Ω β) (hγ : IsBoundaryParam Ω γ) :
    AddCircle (2 * Real.pi) ≃ₜ AddCircle (2 * Real.pi) :=
  (boundaryParamCircleHomeomorph hγ).trans (boundaryParamCircleHomeomorph hβ).symm

/-- A homeomorphism of the genuine additive circle has a genuine real
homeomorphic lift.  The inverse lift is constructed independently and proved
to be an inverse by uniqueness of covering lifts. -/
theorem exists_realHomeomorph_lift_of_addCircleHomeomorph
    (e : AddCircle (2 * Real.pi) ≃ₜ AddCircle (2 * Real.pi)) :
    ∃ t ∈ Ico 0 (2 * Real.pi), ∃ T : ℝ ≃ₜ ℝ,
      T 0 = t ∧ ∀ θ : ℝ,
        (T θ : AddCircle (2 * Real.pi)) = e (θ : AddCircle (2 * Real.pi)) := by
  letI : LocPathConnectedSpace ℝ := LocPathConnectedSpace.of_bases
    nhds_basis_Ioo
    (fun x b hx => (convex_Ioo (𝕜 := ℝ) b.1 b.2).isPathConnected ⟨x, hx⟩)
  let t := AddCircle.equivIco (2 * Real.pi) 0 (e 0)
  have htcoe : (t : AddCircle (2 * Real.pi)) = e 0 :=
    (AddCircle.equivIco (2 * Real.pi) 0).symm_apply_apply (e 0)
  let f : C(ℝ, AddCircle (2 * Real.pi)) :=
    ⟨fun θ => e (θ : AddCircle (2 * Real.pi)),
      e.continuous.comp (AddCircle.continuous_mk' (2 * Real.pi))⟩
  obtain ⟨T, hT, _⟩ :=
    (AddCircle.isCoveringMap_coe (2 * Real.pi)).existsUnique_continuousMap_lifts f 0 t (by
      simpa [f] using htcoe)
  have hTcoe θ :
      T θ = e (θ : AddCircle (2 * Real.pi)) :=
    congrFun hT.2 θ
  let f' : C(ℝ, AddCircle (2 * Real.pi)) :=
    ⟨fun θ => e.symm (θ : AddCircle (2 * Real.pi)),
      e.symm.continuous.comp (AddCircle.continuous_mk' (2 * Real.pi))⟩
  obtain ⟨S, hS, _⟩ :=
    (AddCircle.isCoveringMap_coe (2 * Real.pi)).existsUnique_continuousMap_lifts f' t 0 (by
      change (0 : AddCircle (2 * Real.pi)) = e.symm (t : AddCircle (2 * Real.pi))
      rw [htcoe, e.symm_apply_apply])
  have hScoe θ :
      S θ = e.symm (θ : AddCircle (2 * Real.pi)) :=
    congrFun hS.2 θ
  let H : ℝ ≃ₜ ℝ :=
    { toFun := T
      invFun := S
      left_inv := fun θ => congrFun (by
        refine (AddCircle.isCoveringMap_coe (2 * Real.pi)).eq_of_comp_eq
          (S.continuous.comp T.continuous) continuous_id ?_ 0 ?_
        · funext θ
          change S (T θ) = (θ : AddCircle (2 * Real.pi))
          rw [hScoe, hTcoe, e.symm_apply_apply]
        · change S (T 0) = 0
          rw [hT.1, hS.1]) θ
      right_inv := fun θ => congrFun (by
        refine (AddCircle.isCoveringMap_coe (2 * Real.pi)).eq_of_comp_eq
          (T.continuous.comp S.continuous) continuous_id ?_ t ?_
        · funext θ
          change T (S θ) = (θ : AddCircle (2 * Real.pi))
          rw [hTcoe, hScoe, e.apply_symm_apply]
        · change T (S t) = t
          rw [hS.1, hT.1]) θ
      continuous_toFun := T.continuous
      continuous_invFun := S.continuous }
  exact ⟨t, (by
    simpa using (AddCircle.equivIco (2 * Real.pi) 0 (e 0)).property), H, hT.1, hTcoe⟩

/-- Nonzero C¹ velocity gives a genuine local inverse chord bound between
any two parameters, by the real tangent projection and the mean value theorem. -/
theorem exists_regularCurve_local_inverse_bound (β : ℝ → ℂ)
    (hβ : ContDiff ℝ 1 β) t (ht : deriv β t ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x ∈ Ioo (t - r) (t + r), ∀ y ∈ Ioo (t - r) (t + r),
        |x - y| ≤ C * ‖β x - β y‖ := by
  let c := conj (deriv β t)
  let D := Complex.normSq (deriv β t)
  let f : ℝ → ℝ := fun x => (c * β x).re
  have hD := Complex.normSq_pos.mpr ht
  have hdf x : HasDerivAt f (c * deriv β x).re x := by
    simpa [f, Function.comp_def] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (((hβ.differentiable_one x).hasDerivAt).const_mul c)
  have hfc : Continuous f :=
    Complex.continuous_re.comp (continuous_const.mul hβ.continuous)
  have hfd : Differentiable ℝ f := fun x => (hdf x).differentiableAt
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp ((isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_const.mul hβ.continuous_deriv_one))).mem_nhds (by
    change D / 2 < (c * deriv β t).re
    rw [show (c * deriv β t).re = D by
      dsimp only [c, D]
      rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]]
    linarith))
  have hlower x (hx : x ∈ Ioo (t - r) (t + r)) : D / 2 ≤ deriv f x := by
    rw [(hdf x).deriv]
    exact le_of_lt (hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]))
  have hgrowth := (convex_Ioo (𝕜 := ℝ) (t - r) (t + r)).mul_sub_le_image_sub_of_le_deriv
    hfc.continuousOn hfd.differentiableOn
    (fun x hx => hlower x (interior_subset hx))
  refine ⟨r, hr, ‖c‖ / (D / 2), div_pos (by
    simpa [c, Complex.norm_conj] using norm_pos_iff.mpr ht) (half_pos hD), ?_⟩
  intro x hx y hy
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (half_pos hD)).mpr (by simpa [mul_comm] using (show D / 2 * |x - y| ≤ ‖c‖ * ‖β x - β y‖ by
    calc
      _ ≤ _ := show D / 2 * |x - y| ≤ |f x - f y| by
        by_cases hxy : x ≤ y
        · calc
            _ = D / 2 * (y - x) := by rw [abs_of_nonpos (sub_nonpos.mpr hxy)]; ring
            _ ≤ f y - f x := hgrowth x hx y hy hxy
            _ ≤ |f y - f x| := le_abs_self _
            _ = |f x - f y| := abs_sub_comm _ _
        · have hyx := (not_le.mp hxy).le
          calc
            _ = _ := by rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
            _ ≤ _ := hgrowth y hy x hx hyx
            _ ≤ _ := le_abs_self _
      _ = _ := by rw [show f x - f y = (c * (β x - β y)).re by
        simp [f, mul_sub]]
      _ ≤ _ := Complex.abs_re_le_norm _
      _ = _ := norm_mul _ _))

/-- The actual lift is locally Lipschitz because its reference curve has a
genuine local inverse bound and the arbitrary physical curve is Lipschitz. -/
theorem locallyLipschitz_eq_affine_of_ae_deriv  
    (hf : LocallyLipschitz f) (hd : ∀ᵐ θ : ℝ ∂volume, deriv f θ = a) :
    ∀ θ : ℝ, f θ = a * θ + f 0 := by
  intro θ
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (s := uIcc 0 θ) isCompact_uIcc hf.locallyLipschitzOn
  have hFTC := hK.absolutelyContinuousOnInterval.integral_deriv_eq_sub
  rw [show ∫ s in 0..θ, deriv f s = ∫ s in 0..θ, a by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hd] with s hs _ using hs, intervalIntegral.integral_const] at hFTC
  simp at hFTC
  linarith

/-- The original bounded-domain geometry itself supplies positive finite
area.  Thus a smooth regular physical boundary parameter synchronizes with
every original physical boundary parameter by an actual cyclic shift. -/
theorem exists_boundaryParam_shift_of_bounded_domain  
    (hb : Bornology.IsBounded Ω) (hΩ : IsDomain Ω)
    (hβ : IsBoundaryParam Ω β) (hβC1 : ContDiff ℝ 1 β)
    (hnz : ∀ θ, deriv β θ ≠ 0) (hγ : IsBoundaryParam Ω γ) :
    ∃ t ∈ Icc 0 (2 * Real.pi), ∀ θ : ℝ, γ θ = β (θ + t) := by
  exact (by
    obtain ⟨t, ht, hshift | hreverse⟩ : ∃ t ∈ Ico 0 (2 * Real.pi), (∀ θ : ℝ, γ θ = β (θ + t)) ∨ (∀ θ : ℝ, γ θ = β (-θ + t)) := by
      obtain ⟨t, ht, T, hT0, hcomp, _⟩ : ∃ t ∈ Ico 0 (2 * Real.pi), ∃ T : ℝ ≃ₜ ℝ, T 0 = t ∧ (∀ θ : ℝ, γ θ = β (T θ)) ∧ (StrictMono T ∨ StrictAnti T) := by
        obtain ⟨t, ht, T, hT0, hTcoe⟩ :=
          exists_realHomeomorph_lift_of_addCircleHomeomorph (boundaryParamCircleChange hβ hγ)
        refine ⟨t, ht, T, hT0, ?_, T.continuous.strictMono_of_inj T.injective⟩
        intro θ
        calc
          _ = _ :=
            (boundaryParamCircleMap_coe hγ θ).symm
          _ = _ := (show boundaryParamCircleMap β (boundaryParamCircleChange hβ hγ _) = boundaryParamCircleMap γ _ by
                exact congrArg Subtype.val
                  ((boundaryParamCircleHomeomorph hβ).apply_symm_apply
                    (boundaryParamCircleHomeomorph hγ _))).symm
          _ = _ := by rw [hTcoe]
          _ = _ := boundaryParamCircleMap_coe hβ (T θ)
      obtain ⟨a, _, ha⟩ : ∃ a : ℝ, a ≠ 0 ∧ ∀ θ : ℝ, T θ = a * θ + T 0 := by
        obtain ⟨cβ, hcβ, cγ, hcγ, _, habs⟩ : ∃ cβ : ℝ, 0 < cβ ∧ ∃ cγ : ℝ, 0 < cγ ∧ (∀ θ : ℝ, ‖deriv β θ‖ = cβ) ∧ (∀ᵐ θ : ℝ ∂volume, |deriv (T : ℝ → ℝ) θ| = cγ / cβ) := by
          obtain ⟨c, hc, hspeed⟩ := hβ.const_speed
          let cβ := c
          let hcβ := hc
          let hβspeed := fun θ => congrFun (Measure.eq_of_ae_eq hspeed hβC1.continuous_deriv_one.norm continuous_const) θ
          obtain ⟨cγ, hcγ, hγspeed⟩ := hγ.const_speed
          refine ⟨cβ, hcβ, cγ, hcγ, hβspeed, ?_⟩
          filter_upwards [hγspeed, show ∀ᵐ θ : ℝ ∂volume, deriv γ θ = deriv (T : ℝ → ℝ) θ • deriv β (T θ) by
            filter_upwards [(show ∀ᵐ θ : ℝ ∂volume, DifferentiableAt ℝ (T : ℝ → ℝ) θ by
              obtain hT | hT := T.continuous.strictMono_of_inj T.injective
              · exact hT.monotone.ae_differentiableAt
              · have hn : Monotone (fun θ => -T θ) :=
                  fun x y hxy => neg_le_neg (hT.antitone hxy)
                filter_upwards [hn.ae_differentiableAt] with θ hθ
                have hθ' := hθ.neg
                change DifferentiableAt ℝ (fun x => -(-T x)) θ at hθ'
                simpa using hθ')] with θ hθ
            rw [funext hcomp]
            exact ((hβC1.differentiable_one (T θ)).hasDerivAt.scomp θ hθ.hasDerivAt).deriv] with θ hθ hchain
          exact (eq_div_iff hcβ.ne').mpr (by
            calc
              _ = _ := by
                rw [norm_smul, Real.norm_eq_abs, hβspeed]
              _ = _ := congrArg norm hchain.symm
              _ = cγ := hθ)
        have hc := div_pos hcγ hcβ
        have hLip : LocallyLipschitz (T : ℝ → ℝ) := by
          obtain ⟨K, hK⟩ := hγ.lipschitz
          intro θ
          obtain ⟨r, hr, C, hC, hbound⟩ :=
            exists_regularCurve_local_inverse_bound β hβC1 (T θ) (hnz (T θ))
          refine ⟨Real.toNNReal (C * K), T ⁻¹' Ioo (T θ - r) (T θ + r), T.continuous.continuousAt.preimage_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)), ?_⟩
          apply LipschitzOnWith.of_dist_le'
          intro x hx y hy
          calc
            _ = _ := Real.dist_eq _ _
            _ ≤ _ := hbound (T x) hx (T y) hy
            _ = _ := by rw [← hcomp x, ← hcomp y, dist_eq_norm]
            _ ≤ _ :=
              mul_le_mul_of_nonneg_left (hK.dist_le_mul x y) hC.le
            _ = _ := by ring
        obtain hmono | hanti := T.continuous.strictMono_of_inj T.injective
        · refine ⟨cγ / cβ, hc.ne', locallyLipschitz_eq_affine_of_ae_deriv hLip ?_⟩
          filter_upwards [habs] with θ hθ
          rwa [abs_of_nonneg hmono.monotone.deriv_nonneg] at hθ
        · refine ⟨-(cγ / cβ), neg_ne_zero.mpr hc.ne',
            locallyLipschitz_eq_affine_of_ae_deriv hLip ?_⟩
          filter_upwards [habs] with θ hθ
          rw [abs_of_nonpos hanti.antitone.deriv_nonpos] at hθ
          linarith
      refine ⟨t, ht, ?_⟩
      obtain haone | haneg := (show a = 1 ∨ a = -1 by
        have hperne := Real.two_pi_pos.ne'
        obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (2 * Real.pi)).mp (by
          have hsub : ((T (2 * Real.pi) - T 0 : ℝ) : AddCircle (2 * Real.pi)) = 0 := by
            rw [AddCircle.coe_sub, ((boundaryParam_eq_iff_circle_coe_eq hβ _ _).mp (by
              calc
                _ = _ := (hcomp (2 * Real.pi)).symm
                _ = _ := by simpa using hγ.periodic 0
                _ = _ := hcomp 0)), sub_self]
          simpa [ha (2 * Real.pi)] using hsub)
        have hmR : m = a := by
          rw [zsmul_eq_mul] at hm
          exact mul_right_cancel₀ hperne hm
        let x := T.symm (T 0 + 2 * Real.pi)
        have hTx : T x = T 0 + 2 * Real.pi := T.apply_symm_apply _
        obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (2 * Real.pi)).mp (by
          simpa [AddCircle.coe_zero] using
            (boundaryParam_eq_iff_circle_coe_eq hγ x 0).mp (by
              rw [hcomp x, hTx, hβ.periodic (T 0), ← hcomp 0]))
        obtain hmone | hmneg := Int.eq_one_or_neg_one_of_mul_eq_one (show m * n = 1 by exact_mod_cast (show (m : ℝ) * n = 1 by
          apply mul_right_cancel₀ hperne
          calc
            _ = a * x := by
              rw [hmR, ← hn, zsmul_eq_mul]
              ring
            _ = _ := show a * x = 2 * Real.pi by
              rw [ha x] at hTx
              linarith
            _ = _ := by ring))
        · left
          rw [← hmR, hmone, Int.cast_one]
        · right
          rw [← hmR, hmneg, Int.cast_neg, Int.cast_one])
      · left
        intro θ
        rw [hcomp θ, ha θ, haone, one_mul, hT0]
      · right
        intro θ
        rw [hcomp θ, ha θ, haneg, neg_one_mul, hT0]
    · exact ⟨t, Ico_subset_Icc_self ht, hshift⟩
    · have hfun : γ = fun θ => β (-θ + t) := funext hreverse
      have hγarea : (∫ θ in 0..(2 * Real.pi), signedAreaDensity γ θ) =
          2 * (volume Ω).toReal := hγ.area
      have hβarea : (∫ θ in 0..(2 * Real.pi), signedAreaDensity β θ) =
          2 * (volume Ω).toReal := hβ.area
      rw [hfun, show (∫ θ in 0..(2 * Real.pi), signedAreaDensity (fun θ => β (-θ + t)) θ) = -(∫ θ in 0..(2 * Real.pi), signedAreaDensity β θ) by
        let δ : ℝ → ℂ := fun θ => β (θ + t)
        have hd θ :
            signedAreaDensity (fun θ => β (-θ + t)) θ = -signedAreaDensity δ (-θ) := by
          change signedAreaDensity (fun θ => δ (-θ)) θ = _
          simp [signedAreaDensity, deriv_comp_neg]
        simp_rw [hd]
        rw [intervalIntegral.integral_neg,
          intervalIntegral.integral_comp_neg (signedAreaDensity δ), neg_zero]
        have hshift := integral_signedAreaDensity_shift (show Function.Periodic δ (2 * Real.pi) by
          intro θ
          change β ((θ + 2 * Real.pi) + t) = _
          rw [show θ + 2 * Real.pi + t = θ + t + 2 * Real.pi by ring, hβ.periodic]) (-(2 * Real.pi))
        rw [neg_add_cancel] at hshift
        rw [hshift]
        exact congrArg Neg.neg (show (∫ θ in 0..(2 * Real.pi), signedAreaDensity (fun θ => β (θ + t)) θ) = ∫ θ in 0..(2 * Real.pi), signedAreaDensity β θ by
          calc
            _ = ∫ θ in 0..(2 * Real.pi), signedAreaDensity β (θ + t) := by
              apply intervalIntegral.integral_congr
              intro θ _
              simp [signedAreaDensity, deriv_comp_add_const]
            _ = _ := by
              rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm (2 * Real.pi) t]
            _ = _ := integral_signedAreaDensity_shift hβ.periodic t), hβarea] at hγarea
      exact (((ENNReal.toReal_pos (hΩ.1.measure_pos volume hΩ.2.nonempty).ne' hb.measure_lt_top.ne).ne') (by linarith)).elim)

end PolyaNeumann

end
