module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTestBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforwardGreen

/-! # The actual finite physical Green test at a sufficiently late physical horizon -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution

/-- A weighted compact normalized probe expressed in physical coordinates. -/
def clockWeightedProbe (c : Clock) (e : Point) (f : exitProbeSubmodule) : Point → ℝ :=
  fun p => |p.velocity 0| * exitProbePhysical f (c.map e p)

/-- The genuine test has zero exit integral at every physical horizon past the clock cutoff. -/
private theorem clock_test_exit_zero
    {lam Lam : ℝ} {A : SmoothAutonomous lam Lam} {c : Clock} {e : Point}
    {R T : ℝ} {f : exitProbeSubmodule} (h : ClockSourcePotentialSpec A c e R T f)
    (U : ℝ) (hU : e.time + 2 * c.r ^ 2 * R ≤ U)
    (ep : StripPole c.activeInterval (U : WithTop ℝ)) (hep : ep.1 = e) :
    (∫ p, clockSourcePotential A c e T f
      (sectionTwoPoint (c.map e p)) ∂stripExit A c.activeInterval U ep) = 0 := by
  have hc := (clock_forward_cone_finite A c U ep).1
  have hex : ∀ᵐ p ∂stripExit A c.activeInterval U ep,
      p ∈ reconstructionExit c.activeInterval (ep.1.time - 1) U := by
    rw [ae_iff]
    exact (strip_exit_probability A c.activeInterval
      (ep.1.time - 1) U ep (by linarith)).2.1
  apply integral_eq_zero_of_ae
  filter_upwards [hc, hex] with p hp hx
  rcases hx with hx | hx
  · have ht : R ≤ (c.map e p).time := by
      have hp' : p.time - e.time ≤ 2 * c.r ^ 2 * (c.map e p).time := by
        simpa only [hep] using hp
      have hsqr := sq_pos_of_pos c.positive
      rw [hx.1] at hp'
      nlinarith
    exact h.zero_after _ ht
  · exact h.pullback_zero_faces p hx.2.2

/-- The literal full-test strip identity gives the weighted compact-probe integral.
All regularity, boundedness and the zero exit term are proved from the actual normalized solver. -/
theorem clock_weighted_test_finite
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
    (R T U : ℝ) (hRT : R < T) (hU : e.time + 2 * c.r ^ 2 * R ≤ U)
    (ep : StripPole c.activeInterval (U : WithTop ℝ)) (hep : ep.1 = e)
    (f : exitProbeSubmodule) (hfn : ∀ p, 0 ≤ exitProbePhysical f p)
    (hs : tsupport (exitProbePhysical f) ⊆
      {p | p.time < T ∧ p.velocity 0 ∈ clockNormalizedInterval.carrier})
    (hz : ∀ p, R ≤ p.time → exitProbePhysical f p = 0) :
    (∫ p, clockWeightedProbe c e f p ∂stripGreen A c.activeInterval U ep) =
      (|c.vbar| * c.r ^ 2) * clockSourcePotential A c e T f
        (sectionTwoPoint (c.map e e)) := by
  let u := (clockSourcePotential A c e T f ∘ sectionTwoPoint) ∘ c.map e
  have hspec := clockSourcePotential_regular A c e R T hRT f hfn hs hz
  have hreg := (clock_pullback_C112 c e _ hspec.smooth).mono
    (show reconstructionStrip c.activeInterval (ep.1.time - 1) U ⊆
      {p | p.velocity 0 ∈ c.active} from fun _ hp => hp.2.2)
  obtain ⟨M, hM⟩ := hspec.pullback_bounded
  have heU : ep.1.time < U := WithTop.coe_lt_coe.mp ep.2.1
  have hi := strip_identity_C112 A c.activeInterval (ep.1.time - 1) U
    (by linarith) ep (by linarith) u hreg
    (hspec.pullback_continuous.mono (fun p hp => (nested_strip_union_exit_subset_closed c.activeInterval
      c.activeInterval subset_rfl (ep.1.time - 1) U hp).2))
    ⟨M, fun p hp => hM p hp.2.2⟩
  have hzero := clock_test_exit_zero hspec U hU ep hep
  have hsource : (fun p => forwardScalarOperator A.a u p) =ᵐ[
      stripGreen A c.activeInterval U ep]
      fun p => -(1 / (|c.vbar| * c.r ^ 2)) * clockWeightedProbe c e f p := by
    filter_upwards [stripGreenOfKernel_ae_mem_stripPast c.activeInterval
      (stripEvolution A c.activeInterval).2 U ep] with p hp
    exact (hspec.physical_equation p hp.2).trans (by dsimp [clockWeightedProbe]; ring)
  rw [integral_congr_ae hsource, integral_const_mul] at hi
  change u ep.1 = _ - _ at hi
  change (∫ p, u p ∂stripExit A c.activeInterval U ep) = 0 at hzero
  rw [hzero] at hi
  have hv : |c.vbar| * c.r ^ 2 ≠ 0 :=
    ne_of_gt (mul_pos (abs_pos.mpr c.nonzero) (sq_pos_of_pos c.positive))
  have heval : u ep.1 = clockSourcePotential A c e T f
      (sectionTwoPoint (c.map e e)) := congrArg u hep
  rw [heval] at hi
  have hi' : clockSourcePotential A c e T f
      (sectionTwoPoint (c.map e e)) =
      (∫ p, clockWeightedProbe c e f p ∂stripGreen A
        c.activeInterval U ep) / (|c.vbar| * c.r ^ 2) := hi.trans (by ring)
  exact ((eq_div_iff hv).mp hi').symm.trans (mul_comm _ _)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
