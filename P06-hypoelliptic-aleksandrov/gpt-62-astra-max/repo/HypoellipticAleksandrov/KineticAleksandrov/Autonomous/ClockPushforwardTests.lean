module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTestBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforwardGreen

/-! # The actual finite physical Green test at a sufficiently late physical horizon -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (c : Clock) (e : Point) (R T U : ℝ) (hRT : R < T) (hU : e.time + 2 * c.r ^ 2 * R ≤ U)
    (ep : StripPole c.activeInterval (U : WithTop ℝ)) (hep : ep.1 = e) (f : exitProbeSubmodule)
    (hfn : ∀ p, 0 ≤ exitProbePhysical f p)
    (hs : tsupport (exitProbePhysical f) ⊆
      {p | p.time < T ∧ p.velocity 0 ∈ clockNormalizedInterval.carrier})
    (hz : ∀ p, R ≤ p.time → exitProbePhysical f p = 0)

include c e f in
/-- A weighted compact normalized probe expressed in physical coordinates. -/
def clockWeightedProbe : Point → ℝ :=
  fun p => |p.velocity 0| * exitProbePhysical f (c.map e p)

include hRT hU hep hfn hs hz in
/-- The genuine test has zero exit integral at every physical horizon past the clock cutoff. -/
theorem clock_test_exit_zero :
    (∫ p, clockSourcePotential hlam hLam A c e T f
      (sectionTwoPoint (c.map e p)) ∂stripExit hlam hLam A c.activeInterval U ep) = 0 := by
  have hex : ∀ᵐ p ∂stripExit hlam hLam A c.activeInterval U ep,
      p ∈ reconstructionExit c.activeInterval (ep.1.time - 1) U := by
    exact (strip_exit_probability hlam hLam A c.activeInterval
      (ep.1.time - 1) U ep (by linarith)).2.1
  apply integral_eq_zero_of_ae
  filter_upwards [((clock_forward_cone_finite hlam hLam A c U ep).1), hex] with p hp hx
  rcases hx with hx | hx
  · have ht : R ≤ (c.map e p).time := by
      have hp' : p.time - e.time ≤ 2 * c.r ^ 2 * (c.map e p).time := by
        simpa [hep] using hp
      have hsqr := sq_pos_of_pos c.positive
      rw [hx.1] at hp'
      nlinarith
    exact (clockSourcePotential_regular hlam hLam A c e R T hRT
      f hfn hs hz).2.2.1 _ ht
  · exact clockSourcePotential_pullback_zero_faces hlam hLam A c e R T hRT
      f hfn hs hz p hx.2.2

include hRT hU hep hfn hs hz in
/-- The literal full-test strip identity gives the weighted compact-probe integral.
All regularity, boundedness and the zero exit term are proved from the actual normalized solver. -/
theorem clock_weighted_test_finite :
    (∫ p, clockWeightedProbe c e f p ∂stripGreen hlam hLam A c.activeInterval U ep) =
      (|c.vbar| * c.r ^ 2) * clockSourcePotential hlam hLam A c e T f
        (sectionTwoPoint (c.map e e)) := by
  let u := (clockSourcePotential hlam hLam A c e T f ∘ sectionTwoPoint) ∘ c.map e
  have hreg := clock_C112_mono (clock_pullback_C112 c e _ (clockSourcePotential_regular hlam hLam A c e R T hRT f hfn hs hz).2.1)
    (show reconstructionStrip c.activeInterval (ep.1.time - 1) U ⊆
      {p | p.velocity 0 ∈ c.active} from fun _ hp => hp.2.2)
  have hcont := clockSourcePotential_pullback_continuous hlam hLam A c e R T hRT
    f hfn hs hz
  obtain ⟨M, hM⟩ := clockSourcePotential_pullback_bounded hlam hLam A c e R T hRT
    f hfn hs hz
  have heU := WithTop.coe_lt_coe.mp ep.2.1
  have hi := strip_identity_C112 hlam hLam A c.activeInterval (ep.1.time - 1) U
    (by linarith) ep (by linarith) u hreg
    (hcont.mono (fun p hp => (nested_strip_union_exit_subset_closed c.activeInterval
      c.activeInterval subset_rfl (ep.1.time - 1) U hp).2))
    ⟨M, fun p hp => hM p hp.2.2⟩
  have hzero := clock_test_exit_zero hlam hLam A c e R T U hRT hU ep hep
    f hfn hs hz
  have hsource : (fun p => forwardScalarOperator A.a u p) =ᵐ[
      stripGreen hlam hLam A c.activeInterval U ep]
      fun p => -(1 / (|c.vbar| * c.r ^ 2)) * clockWeightedProbe c e f p := by
    filter_upwards [stripGreenOfKernel_ae_mem_stripPast c.activeInterval
      (stripEvolution hlam hLam A c.activeInterval).2 U ep] with p hp
    exact (clockSourcePotential_physical_equation hlam hLam A c e R T hRT
      f hfn hs hz p hp.2).trans (by dsimp [clockWeightedProbe]; ring)
  rw [integral_congr_ae hsource, integral_const_mul] at hi
  change u ep.1 = _ - _ at hi
  change (∫ p, u p ∂stripExit hlam hLam A c.activeInterval U ep) = 0 at hzero
  rw [hzero] at hi
  rw [(congrArg u hep)] at hi
  exact ((eq_div_iff (ne_of_gt (mul_pos (abs_pos.mpr c.nonzero) (sq_pos_of_pos c.positive)))).mp (hi.trans (by ring))).symm.trans (mul_comm _ _)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
