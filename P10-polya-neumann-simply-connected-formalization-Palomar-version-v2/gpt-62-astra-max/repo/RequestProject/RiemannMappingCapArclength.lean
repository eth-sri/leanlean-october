module

public import RequestProject.RiemannMappingBoundaryCrosscut
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import RequestProject.PlanarNotation

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

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology

/-- A proved length coordinate with the actual displacement inequality
gives a genuine Lipschitz parametrization. The inverse is constructed
from its strict order and the intermediate value theorem. -/
theorem exists_lipschitz_reparam_of_length {G : ℝ → ℂ} {ℓ : ℝ → ℝ} {a b : ℝ}
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
    exact hℓs (by grind) (by grind) hab
  let f : Icc a b → Icc 0 (ℓ b) := fun θ =>
    ⟨ℓ θ, ⟨by rw [← hℓa]; exact hℓs.monotoneOn (by grind) θ.property θ.property.1,
      hℓs.monotoneOn θ.property (by grind) θ.property.2⟩⟩
  
  have hfo : Function.Surjective f := by
    intro u
    have hu : (u : ℝ) ∈ Icc (ℓ a) (ℓ b) := by simpa only [hℓa] using u.property
    obtain ⟨θ, hθ, heq⟩ := intermediate_value_Icc hab.le hℓc hu
    exact ⟨⟨θ, hθ⟩, Subtype.ext heq⟩
  let e  := StrictMono.orderIsoOfSurjective f (fun θ ψ hθψ => hℓs θ.property ψ.property hθψ) hfo
  let τ  := fun u => (e.symm (projIcc 0 (ℓ b) hL.le u) : ℝ)
  let H  := fun u => G (τ u)
  have hτc  := continuous_subtype_val.comp
    (e.symm.continuous.comp (LipschitzWith.projIcc hL.le).continuous)
  have hτmem (u : ℝ) : τ u ∈ Icc a b := (e.symm _).property
  have hτℓ (u : ℝ) : ℓ (τ u) = (projIcc 0 (ℓ b) hL.le u) := by
    exact congrArg (fun x : Icc 0 (ℓ b) => (x : ℝ))
      (e.apply_symm_apply (projIcc 0 (ℓ b) hL.le u))
  have hτright (u : ℝ) (hu : u ∈ Icc 0 (ℓ b)) : ℓ (τ u) = u := by
    rw [hτℓ, projIcc_of_mem _ hu]
  have hτleft (θ : ℝ) (hθ : θ ∈ Icc a b) : τ (ℓ θ) = θ := by
    have hℓθ  := (f ⟨θ, hθ⟩).property
    have hp : projIcc 0 (ℓ b) hL.le (ℓ θ) = e ⟨θ, hθ⟩ := by
      rw [projIcc_of_mem _ hℓθ]
      rfl
    change (e.symm (projIcc 0 (ℓ b) hL.le (ℓ θ)) : ℝ) = θ
    simp [hp]
  have habs : ∀ θ ∈ Icc a b, ∀ ψ ∈ Icc a b,
      ‖G θ - G ψ‖ ≤ |ℓ θ - ℓ ψ| := by
    intro θ hθ ψ hψ
    rcases le_total θ ψ with h | h
    · 
      rw [abs_of_nonpos (sub_nonpos.mpr (hℓs.monotoneOn hθ hψ h)), norm_sub_rev]
      have hd := hdom θ hθ ψ hψ h
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr (hℓs.monotoneOn hψ hθ h))]
      simp [*]
  have hH : LipschitzWith 1 H := by
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    have h := habs (τ u) (hτmem u) (τ v) (hτmem v)
    rw [hτℓ, hτℓ] at h
    have hc := (LipschitzWith.projIcc hL.le).dist_le_mul u v
    simpa [dist_eq_norm] using h.trans hc
  refine ⟨τ, H, hτc, hH, hτmem, hτright, hτleft, fun _ => rfl, ?_⟩
  ext z
  constructor
  · rintro ⟨u, _, rfl⟩
    grind
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨ℓ θ, (f ⟨θ, hθ⟩).property, ?_⟩
    simp [H, hτleft θ hθ]

section

variable (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F unitDisk) (hinj : InjOn F unitDisk) (c : ℂ)
    (r a θ ψ : ℝ) (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi))
include F

include a c r θ in
/-- The actual angular arclength, with its prescribed starting point. -/
def riemannCapArcLength : ℝ :=
  ∫ s in a..θ, ‖riemannCapDerivative F c r s‖

include hi in
theorem riemannCapArcLength_continuous :
    Continuous (riemannCapArcLength F c r a) :=
  intervalIntegral.continuous_primitive
    (fun s t => (riemannCapDerivative_intervalIntegrable F c r hi s t).norm) a

include hi in
theorem riemannCapArcLength_sub :
    riemannCapArcLength F c r a ψ - riemannCapArcLength F c r a θ =
      ∫ s in θ..ψ, ‖riemannCapDerivative F c r s‖ :=
  intervalIntegral.integral_interval_sub_left
    (riemannCapDerivative_intervalIntegrable F c r hi a ψ).norm
    (riemannCapDerivative_intervalIntegrable F c r hi a θ).norm

include hi in
theorem riemannCapArcLength_monotone :
    Monotone (riemannCapArcLength F c r a) := by
  intro θ ψ hθψ
  apply sub_nonneg.mp
  rw [riemannCapArcLength_sub F c r a θ ψ hi]
  grind [intervalIntegral.integral_nonneg_of_forall]

include hF hinj in
/-- Actual interior injectivity prevents the genuine length from being
constant on any nontrivial subinterval, including the entire closed cap
when its two endpoint limits happen to agree. -/
theorem riemannCapArcLength_strictMonoOn {r a b : ℝ}
    (hr : r ≠ 0) (hwidth : b - a ≤ anglePeriod)
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi))
    (harc : MapsTo (circleMap c r) (Ioo a b) unitDisk)
    {G : ℝ → ℂ} (hGc : Continuous G)
    (hGeq : EqOn G (fun θ => F (circleMap c r θ)) (Ioo a b)) :
    StrictMonoOn (riemannCapArcLength F c r a) (Icc a b) := by
  
  have hm  := riemannCapArcLength_monotone F c r a hi
  have hGi : InjOn G (Ioo a b) := by
    intro θ hθ ψ hψ he
    apply injOn_circleMap_of_abs_sub_le' hr hwidth
      (Ioo_subset_Ico_self hθ) (Ioo_subset_Ico_self hψ)
    exact hinj (harc hθ) (harc hψ) ((by grind))
  intro θ hθ ψ hψ hθψ
  by_contra h
  
  let v := (2 * θ + ψ) / 3
  let w := (θ + 2 * ψ) / 3
  have hvθ : θ < v := by dsimp [v]; linarith
  have hvw : v < w := by dsimp [v, w]; linarith
  have hwψ : w < ψ := by dsimp [w]; linarith
  have hv : v ∈ Ioo a b := (by grind)
  have hw : w ∈ Ioo a b := (by grind)
  have hd := riemannMapping_cap_extension_subarc_displacement F hF c r hi harc hGc hGeq
    (Ioo_subset_Icc_self hv) (Ioo_subset_Icc_self hw) hvw.le
  rw [← riemannCapArcLength_sub F c r a v w hi] at hd
  
  have hGwv := sub_eq_zero.mp (norm_le_zero_iff.mp (by
    have h1 := hm hvθ.le
    have h2 := hm hwψ.le
    linarith))
  grind [hGi hw hv hGwv]

include hF hinj in
/-- Genuine cap arclength produces a continuous inverse parameter and
an actual global `1`-Lipschitz physical curve with exactly the same
closed image. No endpoint distinction is required. -/
theorem riemannMapping_cap_arclength_reparam {r a b : ℝ}
    (hr : r ≠ 0) (hab : a < b) (hwidth : b - a ≤ anglePeriod)
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi))
    (harc : MapsTo (circleMap c r) (Ioo a b) unitDisk)
    {G : ℝ → ℂ} (hGc : Continuous G)
    (hGeq : EqOn G (fun θ => F (circleMap c r θ)) (Ioo a b)) :
    let ℓ := riemannCapArcLength F c r a
    ∃ (τ : ℝ → ℝ) (H : ℝ → ℂ), Continuous τ ∧ LipschitzWith 1 H ∧
      (∀ u, τ u ∈ Icc a b) ∧
      (∀ u ∈ Icc 0 (ℓ b), ℓ (τ u) = u) ∧
      (∀ θ ∈ Icc a b, τ (ℓ θ) = θ) ∧
      (∀ u, H u = G (τ u)) ∧ H '' Icc 0 (ℓ b) = G '' Icc a b := by
  refine exists_lipschitz_reparam_of_length hab
    (riemannCapArcLength_continuous F c r a hi).continuousOn
    (riemannCapArcLength_strictMonoOn F hF hinj c hr hwidth hi harc hGc hGeq)
    (by simp [riemannCapArcLength]) ?_
  intro θ hθ ψ hψ hθψ
  rw [riemannCapArcLength_sub F c r a θ ψ hi]
  grind [riemannMapping_cap_extension_subarc_displacement]

theorem riemannCapArcLength_le_full_length {r a b : ℝ}
    (hab : a ≤ b) (hwidth : b ≤ a + anglePeriod)
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi)) :
    riemannCapArcLength F c r a b ≤
      ∫ s in Ioo (-Real.pi) Real.pi, ‖riemannCapDerivative F c r s‖ := by
  let V := riemannCapDerivative F c r
  have hp : Function.Periodic (fun s => ‖V s‖) anglePeriod :=
    (riemannCapDerivative_periodic F c r).comp norm
  calc
    _ ≤ _ :=
      intervalIntegral.integral_mono_interval le_rfl hab hwidth
        (Eventually.of_forall fun _ => norm_nonneg _)
        (riemannCapDerivative_intervalIntegrable F c r hi a _).norm
    _ = ∫ s in (-Real.pi)..Real.pi, ‖V s‖ := by
      simpa only [show -Real.pi + anglePeriod = Real.pi by ring]
        using hp.intervalIntegral_add_eq a (-Real.pi)
    _ = _ := by
      rw [intervalIntegral.integral_of_le (by linarith),
        integral_Ioc_eq_integral_Ioo]

include hF hinj in
theorem riemannCapDerivative_ne_zero_interior {r : ℝ} (hr : 0 < r) (θ : ℝ)
    (hθ : circleMap c r θ ∈ unitDisk) :
    riemannCapDerivative F c r θ ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_riemannCapDerivative F c hr.le θ]
  simp [riemannInteriorDerivative, indicator_of_mem hθ]
  exact mul_pos hr (norm_pos_iff.mpr
    (RiemannInterior.deriv_ne_zero_of_injOn isOpen_ball hF hinj hθ))

include hF hinj in
/-- Arbitrarily short genuine conformal caps admit actual global
Lipschitz arclength parametrizations, with finite physical frontier
endpoints. All length and inverse hypotheses are derived from the true
finite conformal energy and interior injectivity. -/
theorem riemannMapping_exists_small_lipschitz_cap
    (hb : Bornology.IsBounded (F '' unitDisk))
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ (r : ℝ) (G : ℝ → ℂ) (τ : ℝ → ℝ) (H : ℝ → ℂ),
      0 < r ∧ r < δ ∧ r < 1 ∧ Continuous G ∧ Continuous τ ∧ LipschitzWith 1 H ∧
      let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
      let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
      let ℓ := riemannCapArcLength F ζ r a
      IntegrableOn (riemannCapDerivative F ζ r) (Ioo (-Real.pi) Real.pi) ∧
      0 < ℓ b ∧ ℓ b < ε ∧
      EqOn G (fun θ => F (circleMap ζ r θ)) (Ioo a b) ∧
      G a ∈ frontier (F '' unitDisk) ∧
      G b ∈ frontier (F '' unitDisk) ∧
      (∀ u, τ u ∈ Icc a b) ∧
      (∀ u ∈ Icc 0 (ℓ b), ℓ (τ u) = u) ∧
      (∀ θ ∈ Icc a b, τ (ℓ θ) = θ ∧ H (ℓ θ) = G θ) ∧
      (∀ u, H u = G (τ u)) ∧ H 0 = G a ∧ H (ℓ b) = G b ∧
      H '' Icc 0 (ℓ b) = G '' Icc a b ∧ InjOn H (Ico 0 (ℓ b)) := by
  obtain ⟨r, hr, hi, hlength⟩ := riemannMapping_exists_small_cap_length F hF hinj hb ζ
    (show 0 < min δ 1 from lt_min hδ zero_lt_one) hε
  have hrδ := hr.2.trans_le (min_le_left δ 1)
  have hr1 := hr.2.trans_le (min_le_right δ 1)
  let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
  let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
  let ℓ := riemannCapArcLength F ζ r a
  obtain ⟨hab, hwidth, harc, hza, hzb⟩ := riemannCap_geometry hζ hr.1 hr1
  have hwidth' : b - a ≤ anglePeriod := by linarith
  obtain ⟨G, hGc, hGeq, hGaLim, hGbLim⟩ :=
    riemannMapping_cap_continuous_extension F hF ζ r hi hab harc
  have hGa : G a ∈ frontier (F '' unitDisk) := by
    letI := left_nhdsWithin_Ioo_neBot hab
    exact riemannMapping_limit_mem_frontier F hF hinj hza
      (by filter_upwards [self_mem_nhdsWithin] with θ hθ; exact harc hθ)
      (((continuous_circleMap ζ r).tendsto a).mono_left nhdsWithin_le_nhds) hGaLim
  
  have hℓs  :=
    riemannCapArcLength_strictMonoOn F hF hinj ζ hr.1.ne' hwidth' hi harc hGc hGeq
  have hℓa : ℓ a = 0 := by simp [ℓ, riemannCapArcLength]
  
  
  obtain ⟨τ, H, hτc, hHlip, hτm, hτr, hτl, hH, hHim⟩ :=
    riemannMapping_cap_arclength_reparam F hF hinj ζ hr.1.ne' hab hwidth' hi harc hGc hGeq
  have hτ0 : τ 0 = a := by
    grind [hτl a ⟨le_rfl, hab.le⟩]
  
  
  have hHL  := (hH _).trans (congrArg G (hτl b ⟨hab.le, le_rfl⟩))
  
  have hHi : InjOn H (Ico 0 (ℓ b)) := by
    intro u hu v hv heq
    have huc  := Ico_subset_Icc_self hu
    have hvc  := Ico_subset_Icc_self hv
    have hτi (s : ℝ) (hs : s ∈ Ico 0 (ℓ b)) : τ s ∈ Ico a b := by
      refine ⟨(hτm s).1, ?_⟩
      apply lt_of_le_of_ne (hτm s).2
      intro hsb
      have h := hτr s (Ico_subset_Icc_self hs)
      rw [hsb] at h
      linarith [hs.2]
    have hτuv  := (riemannMapping_cap_injOn_Ico F hF hinj hr.1.ne' hwidth' harc hGeq hGa) (hτi u hu) (hτi v hv)
      ((hH u).symm.trans (heq.trans (hH v)))
    grind [hτr u huc]
  refine ⟨r, G, τ, H, hr.1, hrδ, hr1, hGc, hτc, hHlip, hi, (by
    rw [← hℓa]
    exact hℓs ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab), ((riemannCapArcLength_le_full_length F ζ hab.le hwidth hi).trans_lt hlength),
    hGeq, hGa, (by
      letI := right_nhdsWithin_Ioo_neBot hab
      exact riemannMapping_limit_mem_frontier F hF hinj hzb
        (by filter_upwards [self_mem_nhdsWithin] with θ hθ; exact harc hθ)
        (((continuous_circleMap ζ r).tendsto b).mono_left nhdsWithin_le_nhds) hGbLim), hτm, hτr, ?_, hH, ((hH 0).trans (congrArg G hτ0)), hHL, hHim, hHi⟩
  grind

end

end PolyaNeumann

end
