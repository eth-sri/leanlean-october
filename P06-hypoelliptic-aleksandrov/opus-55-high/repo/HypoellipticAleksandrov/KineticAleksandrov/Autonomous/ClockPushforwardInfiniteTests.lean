module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforwardValue

/-! # The weighted clock identity for the actual infinite physical Green measure -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)

/-- The advancing-clock cone holds on the actual infinite physical Green measure. -/
theorem clock_forward_cone_infinite
     (c : Clock) (e : StripPole c.activeInterval ⊤) :
    ∀ᵐ p ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤ e,
      p.time - e.1.time ≤ 2 * c.r ^ 2 * (c.map e.1 p).time := by
  apply stripGreen_infinite_ae_of_finite hH hLE hlam hLam A c.activeInterval e
  intro T ht
  exact (clock_forward_cone_finite hH hLE hlam hLam A c T
    _).2

/-- Compact nonnegative normalized interior tests satisfy the genuine infinite weighted identity. -/
theorem clock_weighted_test_infinite
     (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active)
    (f : exitProbeSubmodule) (hfn : ∀ p, 0 ≤ exitProbePhysical f p)
    (hs : tsupport (exitProbePhysical f) ⊆
      {p | 0 < p.time ∧ p.velocity 0 ∈ normalizedActive}) :
    (∫ p, clockWeightedProbe c e f p ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      ⟨e, WithTop.coe_lt_top _, he⟩) =
      (|c.vbar| * c.r ^ 2) * ∫ p, exitProbePhysical f p
        ∂clockGreen hH hLE hlam hLam A c e he := by
  obtain ⟨R, hR, htimes, hz⟩ := clock_probe_cutoff f
  let ei : StripPole c.activeInterval ⊤ := ⟨e, WithTop.coe_lt_top _, he⟩
  let U := e.time + 2 * c.r ^ 2 * R + 1
  have hU : e.time < U := by
    have hpositive : 0 < 2 * c.r ^ 2 * R :=
      mul_pos (mul_pos (by norm_num) (sq_pos_of_pos c.positive)) hR
    linarith
  let ep := stripPoleFinite c.activeInterval ei U hU
  have hs' : tsupport (exitProbePhysical f) ⊆
      {p | p.time < R + 1 ∧ p.velocity 0 ∈ clockNormalizedInterval.carrier} := by
    intro p hp
    exact ⟨by grind, (hs hp).2⟩
  have hf := clock_weighted_test_finite hH hLE hlam hLam A c e R _ U
    (by linarith) (by linarith) ep rfl f hfn hs' hz
  have hv := clockSourcePotential_eq_infinite_green hH hLE hlam hLam A c e he R (R + 1)
    (by linarith) (by linarith) f hz
  have hr := stripGreen_finite_restrict_infinite hH hLE hlam hLam A c.activeInterval ei U hU
  have hstab : (∫ p, clockWeightedProbe c e f p
      ∂(stripGreen hH hLE hlam hLam A c.activeInterval ⊤ ei).restrict {p | p.time < U}) =
      ∫ p, clockWeightedProbe c e f p ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤ ei := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [clock_forward_cone_infinite hH hLE hlam hLam A c ei] with p hp hlate
    have hclock : R ≤ (c.map e p).time := by
      nlinarith
    change |p.velocity 0| * exitProbePhysical f _ = 0
    simp_all
  grind

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
