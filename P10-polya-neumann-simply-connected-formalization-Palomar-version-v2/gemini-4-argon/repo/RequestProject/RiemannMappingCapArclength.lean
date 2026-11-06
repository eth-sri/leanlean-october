module

public import RequestProject.RiemannMappingBoundaryCrosscut
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Genuine arclength parametrization of conformal caps

The length is the integral of the actual cut-off angular derivative.
Its strict increase follows from the true subarc displacement estimate
and interior injectivity, including when the two physical endpoint
limits coincide. The intermediate value theorem and interval projection
construct a genuine global Lipschitz parametrization and its continuous
inverse parameter. No regularity at the two endpoint limits is assumed.
-/

@[expose] public section


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology

variable {r a b : ℝ}

/-- A proved length coordinate with the actual displacement inequality
gives a genuine Lipschitz parametrization. The inverse is constructed
from its strict order and the intermediate value theorem. -/
theorem exists_lipschitz_reparam_of_length  {ℓ : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hℓc : ContinuousOn ℓ (Icc a b))
    (hℓs : StrictMonoOn ℓ (Icc a b)) (hℓa : ℓ a = 0)
    (hdom : ∀ θ ∈ Icc a b, ∀ τ ∈ Icc a b, θ ≤ τ →
      ‖G τ - G θ‖ ≤ ℓ τ - ℓ θ) :
    ∃ (τ : ℝ → ℝ) (H : ℝ → ℂ), Continuous τ ∧ LipschitzWith 1 H ∧
      (∀ u, τ u ∈ Icc a b) ∧
      (∀ u ∈ Icc 0 (ℓ b), ℓ (τ u) = u) ∧
      (∀ θ ∈ Icc a b, τ (ℓ θ) = θ) ∧
      (∀ u, H u = G (τ u)) ∧ H '' Icc 0 (ℓ b) = G '' Icc a b := by
  have hL : 0 < ℓ b := by
    rw [← hℓa]
    exact hℓs ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
  let f : Icc a b → Icc 0 (ℓ b) := fun θ =>
    ⟨ℓ θ, ⟨by rw [← hℓa]; exact hℓs.monotoneOn ⟨le_rfl, hab.le⟩ θ.property θ.property.1,
      hℓs.monotoneOn θ.property ⟨hab.le, le_rfl⟩ θ.property.2⟩⟩
  let e : Icc a b ≃o Icc 0 (ℓ b) := StrictMono.orderIsoOfSurjective f (fun θ ψ hθψ => hℓs θ.property ψ.property hθψ) (by
    intro u
    have hu : (u : ℝ) ∈ Icc (ℓ a) (ℓ b) := by simpa [hℓa] using u.property
    obtain ⟨θ, hθ, heq⟩ := intermediate_value_Icc hab.le hℓc hu
    exact ⟨⟨θ, hθ⟩, Subtype.ext heq⟩)
  let τ : ℝ → ℝ := fun u => e.symm (projIcc 0 (ℓ b) hL.le u)
  let H : ℝ → ℂ := fun u => G (τ u)
  have hτmem u : τ u ∈ Icc a b := (e.symm _).property
  have hτℓ u : ℓ (τ u) = projIcc 0 (ℓ b) hL.le u := by
    exact congrArg (fun x : Icc 0 (ℓ b) => (x : ℝ))
      (e.apply_symm_apply (projIcc 0 (ℓ b) hL.le u))
  have hτright u (hu : u ∈ Icc 0 (ℓ b)) : ℓ (τ u) = u := by
    rw [hτℓ, projIcc_of_mem _ hu]
  have hτleft θ (hθ : θ ∈ Icc a b) : τ (ℓ θ) = θ := by
    have hℓθ : ℓ θ ∈ Icc 0 (ℓ b) := (f ⟨θ, hθ⟩).property
    change e.symm (projIcc 0 (ℓ b) hL.le (ℓ θ)) = θ
    rw [show projIcc 0 (ℓ b) hL.le (ℓ θ) = e ⟨θ, hθ⟩ by
      rw [projIcc_of_mem _ hℓθ]
      rfl, e.symm_apply_apply]
  have hH : LipschitzWith 1 H := by
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    have h := (show ∀ θ ∈ Icc a b, ∀ ψ ∈ Icc a b, ‖G θ - G ψ‖ ≤ |ℓ θ - ℓ ψ| by
      intro θ hθ ψ hψ
      rcases le_total θ ψ with h | h
      · have hm := hℓs.monotoneOn hθ hψ h
        rw [abs_of_nonpos (sub_nonpos.mpr hm), norm_sub_rev]
        have hd := hdom θ hθ ψ hψ h
        linarith
      · rw [abs_of_nonneg (sub_nonneg.mpr (hℓs.monotoneOn hψ hθ h))]
        exact hdom ψ hψ θ hθ h) (τ u) (hτmem u) (τ v) (hτmem v)
    rw [hτℓ, hτℓ] at h
    have hc := (LipschitzWith.projIcc hL.le).dist_le_mul u v
    rw [Subtype.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at hc
    simpa [H, dist_eq_norm, Real.dist_eq]
      using h.trans hc
  refine ⟨τ, H, continuous_subtype_val.comp (e.symm.continuous.comp (LipschitzWith.projIcc hL.le).continuous), hH, hτmem, hτright, hτleft, fun _ => rfl, ?_⟩
  ext z
  constructor
  · rintro ⟨u, _, rfl⟩
    exact ⟨τ u, hτmem u, rfl⟩
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨ℓ θ, (f ⟨θ, hθ⟩).property, ?_⟩
    simp [H, hτleft θ hθ]

/-- The actual angular arclength, with its prescribed starting point. -/
def riemannCapArcLength (F : ℂ → ℂ) (c : ℂ) (r a θ : ℝ) : ℝ :=
  ∫ s in a..θ, ‖riemannCapDerivative F c r s‖

theorem riemannCapArcLength_sub F c r a θ ψ
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi)) :
    riemannCapArcLength F c r a ψ - riemannCapArcLength F c r a θ =
      ∫ s in θ..ψ, ‖riemannCapDerivative F c r s‖ :=
  intervalIntegral.integral_interval_sub_left
    (riemannCapDerivative_intervalIntegrable F c r hi a ψ).norm
    (riemannCapDerivative_intervalIntegrable F c r hi a θ).norm

/-- Actual interior injectivity prevents the genuine length from being
constant on any nontrivial subinterval, including the entire closed cap
when its two endpoint limits happen to agree. -/
theorem riemannCapArcLength_strictMonoOn F
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) c 
    (hr : r ≠ 0) (hwidth : b - a ≤ 2 * Real.pi)
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi))
    (harc : MapsTo (circleMap c r) (Ioo a b) (ball 0 1))
     (hGc : Continuous G)
    (hGeq : EqOn G (fun θ => F (circleMap c r θ)) (Ioo a b)) :
    StrictMonoOn (riemannCapArcLength F c r a) (Icc a b) := by
  let ℓ := riemannCapArcLength F c r a
  have hm : Monotone (riemannCapArcLength F c r a) := by
    intro θ ψ hθψ
    apply sub_nonneg.mp
    rw [riemannCapArcLength_sub F c r a θ ψ hi]
    exact intervalIntegral.integral_nonneg_of_forall hθψ (fun _ => norm_nonneg _)
  intro θ hθ ψ hψ hθψ
  by_contra h
  let v := (2 * θ + ψ) / 3
  let w := (θ + 2 * ψ) / 3
  have hvθ : θ < v := by dsimp [v]; linarith
  have hvw : v < w := by dsimp [v, w]; linarith
  have hwψ : w < ψ := by dsimp [w]; linarith
  have hv : v ∈ Ioo a b := ⟨hθ.1.trans_lt hvθ, (hvw.trans hwψ).trans_le hψ.2⟩
  have hw : w ∈ Ioo a b := ⟨hθ.1.trans_lt (hvθ.trans hvw), hwψ.trans_le hψ.2⟩
  have hd := riemannMapping_cap_extension_subarc_displacement F hF c r hi harc hGc hGeq
    (Ioo_subset_Icc_self hv) (Ioo_subset_Icc_self hw) hvw.le
  rw [← riemannCapArcLength_sub F c r a v w hi] at hd
  have hGwv := sub_eq_zero.mp (norm_le_zero_iff.mp (by
    have h1 := hm hvθ.le
    have h2 := hm hwψ.le
    change ℓ w - ℓ v ≥ ‖G w - G v‖ at hd
    linarith))
  have hwv := (show InjOn G (Ioo a b) by
    intro θ hθ ψ hψ he
    apply injOn_circleMap_of_abs_sub_le' hr hwidth
      (Ioo_subset_Ico_self hθ) (Ioo_subset_Ico_self hψ)
    exact hinj (harc hθ) (harc hψ) ((hGeq hθ).symm.trans (he.trans (hGeq hψ)))) hw hv hGwv
  exact hvw.ne hwv.symm

/-- Genuine cap arclength produces a continuous inverse parameter and
an actual global `1`-Lipschitz physical curve with exactly the same
closed image. No endpoint distinction is required. -/
theorem riemannMapping_cap_arclength_reparam F
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) c 
    (hr : r ≠ 0) (hab : a < b) (hwidth : b - a ≤ 2 * Real.pi)
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi))
    (harc : MapsTo (circleMap c r) (Ioo a b) (ball 0 1))
    {G : ℝ → ℂ} (hGc : Continuous G)
    (hGeq : EqOn G (fun θ => F (circleMap c r θ)) (Ioo a b)) :
    let ℓ := riemannCapArcLength F c r a
    ∃ (τ : ℝ → ℝ) (H : ℝ → ℂ), Continuous τ ∧ LipschitzWith 1 H ∧
      (∀ u, τ u ∈ Icc a b) ∧
      (∀ u ∈ Icc 0 (ℓ b), ℓ (τ u) = u) ∧
      (∀ θ ∈ Icc a b, τ (ℓ θ) = θ) ∧
      (∀ u, H u = G (τ u)) ∧ H '' Icc 0 (ℓ b) = G '' Icc a b := by
  refine exists_lipschitz_reparam_of_length hab
    (intervalIntegral.continuous_primitive (fun s t => (riemannCapDerivative_intervalIntegrable F c r hi s t).norm) a).continuousOn
    (riemannCapArcLength_strictMonoOn F hF hinj c hr hwidth hi harc hGc hGeq)
    (by simp [riemannCapArcLength]) ?_
  intro θ hθ ψ hψ hθψ
  rw [riemannCapArcLength_sub F c r a θ ψ hi]
  exact riemannMapping_cap_extension_subarc_displacement F hF c r hi harc hGc hGeq
    hθ hψ hθψ

/-- The actual cap derivative is continuous at every genuinely interior
source parameter, even though no derivative is required at the two
endpoint limits. -/
theorem riemannCapDerivative_continuousAt_interior F
    (hF : DifferentiableOn ℂ F (ball 0 1)) c r θ
    (hθ : circleMap c r θ ∈ ball 0 1) :
    ContinuousAt (riemannCapDerivative F c r) θ := by
  have hc : ContinuousAt (fun t =>
      deriv F (circleMap c r t) * (circleMap 0 r t * Complex.I)) θ :=
    (((hF.deriv isOpen_ball).continuousOn.continuousAt
      (isOpen_ball.mem_nhds hθ)).comp (continuous_circleMap c r).continuousAt).mul
        ((continuous_circleMap 0 r).continuousAt.mul_const Complex.I)
  apply hc.congr
  filter_upwards [(continuous_circleMap c r).continuousAt.preimage_mem_nhds
    (isOpen_ball.mem_nhds hθ)] with t ht
  have htDisk : circleMap c r t ∈ ball 0 1 := ht
  simp [riemannCapDerivative, riemannInteriorDerivative, indicator_of_mem htDisk]

theorem riemannCapDerivative_ne_zero_interior F
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) c  (hr : 0 < r) θ
    (hθ : circleMap c r θ ∈ ball 0 1) :
    riemannCapDerivative F c r θ ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_riemannCapDerivative F c hr.le θ]
  simp [riemannInteriorDerivative, indicator_of_mem hθ]
  exact mul_pos hr (norm_pos_iff.mpr
    (RiemannInterior.deriv_ne_zero_of_injOn isOpen_ball hF hinj hθ))

/-- Arbitrarily short genuine conformal caps admit actual global
Lipschitz arclength parametrizations, with finite physical frontier
endpoints. All length and inverse hypotheses are derived from the true
finite conformal energy and interior injectivity. -/
theorem riemannMapping_exists_small_lipschitz_cap F
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1))
    (hb : Bornology.IsBounded (F '' ball 0 1))
     (hζ : ‖ζ‖ = 1) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ (r : ℝ) (G : ℝ → ℂ) (τ : ℝ → ℝ) (H : ℝ → ℂ),
      0 < r ∧ r < δ ∧ r < 1 ∧ Continuous G ∧ Continuous τ ∧ LipschitzWith 1 H ∧
      let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
      let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
      let ℓ := riemannCapArcLength F ζ r a
      IntegrableOn (riemannCapDerivative F ζ r) (Ioo (-Real.pi) Real.pi) ∧
      0 < ℓ b ∧ ℓ b < ε ∧
      EqOn G (fun θ => F (circleMap ζ r θ)) (Ioo a b) ∧
      G a ∈ frontier (F '' ball 0 1) ∧
      G b ∈ frontier (F '' ball 0 1) ∧
      (∀ u, τ u ∈ Icc a b) ∧
      (∀ u ∈ Icc 0 (ℓ b), ℓ (τ u) = u) ∧
      (∀ θ ∈ Icc a b, τ (ℓ θ) = θ ∧ H (ℓ θ) = G θ) ∧
      (∀ u, H u = G (τ u)) ∧ H 0 = G a ∧ H (ℓ b) = G b ∧
      H '' Icc 0 (ℓ b) = G '' Icc a b ∧ InjOn H (Ico 0 (ℓ b)) := by
  obtain ⟨r, hr, hi, hlength⟩ := riemannMapping_exists_small_cap_length F hF hinj hb ζ
    (lt_min hδ zero_lt_one) hε
  have hr1 := hr.2.trans_le (min_le_right δ 1)
  let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
  let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
  let ℓ := riemannCapArcLength F ζ r a
  obtain ⟨hab, hwidth, harc, hza, hzb⟩ := riemannCap_geometry hζ hr.1 hr1
  have hwidth' : b - a ≤ 2 * Real.pi := by linarith
  obtain ⟨G, hGc, hGeq, hGaLim, hGbLim⟩ :=
    riemannMapping_cap_continuous_extension F hF ζ r hi hab harc
  have hGa : G a ∈ frontier (F '' ball 0 1) := by
    letI := left_nhdsWithin_Ioo_neBot hab
    exact riemannMapping_limit_mem_frontier F hF hinj hza
      (by filter_upwards [self_mem_nhdsWithin] with θ hθ; exact harc hθ)
      (((continuous_circleMap ζ r).tendsto a).mono_left nhdsWithin_le_nhds) hGaLim
  have hℓs : StrictMonoOn ℓ (Icc a b) :=
    riemannCapArcLength_strictMonoOn F hF hinj ζ hr.1.ne' hwidth' hi harc hGc hGeq
  have hℓa : ℓ a = 0 := by simp [ℓ, riemannCapArcLength]
  obtain ⟨τ, H, hτc, hHlip, hτm, hτr, hτl, hH, hHim⟩ :=
    riemannMapping_cap_arclength_reparam F hF hinj ζ hr.1.ne' hab hwidth' hi harc hGc hGeq
  refine ⟨r, G, τ, H, hr.1, hr.2.trans_le (min_le_left δ 1), hr1, hGc, hτc, hHlip, hi, (by
    rw [← hℓa]
    exact hℓs ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab), ((show riemannCapArcLength F ζ r a b ≤ ∫ s in Ioo (-Real.pi) Real.pi, ‖riemannCapDerivative F ζ r s‖ by
      calc
        _ ≤ _ :=
          intervalIntegral.integral_mono_interval le_rfl hab.le hwidth
            (Eventually.of_forall fun _ => norm_nonneg _)
            (riemannCapDerivative_intervalIntegrable F ζ r hi a _).norm
        _ = _ := by
          simpa [show -Real.pi + 2 * Real.pi = Real.pi by ring]
            using ((riemannCapDerivative_periodic F ζ r).comp norm).intervalIntegral_add_eq a (-Real.pi)
        _ = _ := by
          rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
            integral_Ioc_eq_integral_Ioo]).trans_lt hlength),
    hGeq, hGa, (by
      letI := right_nhdsWithin_Ioo_neBot hab
      exact riemannMapping_limit_mem_frontier F hF hinj hzb
        (by filter_upwards [self_mem_nhdsWithin] with θ hθ; exact harc hθ)
        (((continuous_circleMap ζ r).tendsto b).mono_left nhdsWithin_le_nhds) hGbLim), hτm, hτr, ?_, hH, ((hH 0).trans (congrArg G (by
      have h := hτl a ⟨le_rfl, hab.le⟩
      change τ (ℓ a) = a at h
      simpa [hℓa] using h))), (hH _).trans (congrArg G (hτl b ⟨hab.le, le_rfl⟩)), hHim, (by
      intro u hu v hv heq
      have hτi s (hs : s ∈ Ico 0 (ℓ b)) : τ s ∈ Ico a b := by
        refine ⟨(hτm s).1, ?_⟩
        apply lt_of_le_of_ne (hτm s).2
        intro hsb
        have h := hτr s (Ico_subset_Icc_self hs)
        rw [hsb] at h
        linarith [hs.2]
      have hru := hτr u (Ico_subset_Icc_self hu)
      rw [(riemannMapping_cap_injOn_Ico F hF hinj hr.1.ne' hwidth' harc hGeq hGa) (hτi u hu) (hτi v hv) ((hH u).symm.trans (heq.trans (hH v)))] at hru
      exact hru.symm.trans (hτr v (Ico_subset_Icc_self hv)))⟩
  intro θ hθ
  exact ⟨hτl θ hθ, (hH _).trans (congrArg G (hτl θ hθ))⟩

end PolyaNeumann

end
