module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforwardSupport
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforwardValue
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTest
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforwardMass
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforwardTests
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreenSupport

/-! # The exact weighted pushforward identity for the actual killed Green measures -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution
open scoped ENNReal NNReal

/- The literal position clock pushes velocity-weighted physical Green to the actual normalized
Green with factor exactly `|vbar| r²`. No density or analytic bridge is a premise. -/
theorem clock_green_pushforward
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    Measure.map (c.map e) ((stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      ⟨e, WithTop.coe_lt_top _, he⟩).withDensity (fun p => ENNReal.ofReal |p.velocity 0|)) =
      ENNReal.ofReal (|c.vbar| * c.r ^ 2) • clockGreen hH hLE hlam hLam A c e he := by
  have hD : 0 < |c.vbar| * c.r ^ 2 :=
    mul_pos (abs_pos.mpr c.nonzero) (sq_pos_of_pos c.positive)
  have : IsFiniteMeasure ((stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      ⟨e, WithTop.coe_lt_top _, he⟩).withDensity
      (fun p => ENNReal.ofReal |p.velocity 0|)) :=
    clockWeightedGreen_isFiniteMeasure hH hLE hlam hLam A c e he
  have := Measure.isFiniteMeasure_map
    ((stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      ⟨e, WithTop.coe_lt_top _, he⟩).withDensity
      (fun p => ENNReal.ofReal |p.velocity 0|)) (c.map e)
  have := Measure.smul_finite (clockGreen hH hLE hlam hLam A c e he)
    (ENNReal.ofReal_ne_top : ENNReal.ofReal (|c.vbar| * c.r ^ 2) ≠ ⊤)
  have _h_xinl_0 : ∀ᵐ p ∂clockGreen hH hLE hlam hLam A c e he, p ∈ clockGreenSupport := by
    rw [ae_iff]
    have hz := (reconstruction_green_infinite_zero_of_finite clockNormalizedInterval (clockEvolution hH hLE hlam hLam A c e) (clockPhysicalPole c e he) clockGreenSupportᶜ isOpen_clockGreenSupport.measurableSet.compl) (fun T ht => by
      apply (ae_iff (p := fun p : Point => p ∈ clockGreenSupport)).mp
      filter_upwards [reconstruction_green_ae_time_gt clockNormalizedInterval
        (clockEvolution hH hLE hlam hLam A c e).2 T
        ⟨(clockPhysicalPole c e he).1, WithTop.coe_lt_coe.mpr ht,
          (clockPhysicalPole c e he).2.2⟩,
        stripGreenOfKernel_ae_mem_stripPast clockNormalizedInterval
          (clockEvolution hH hLE hlam hLam A c e).2 T
          ⟨(clockPhysicalPole c e he).1, WithTop.coe_lt_coe.mpr ht,
            (clockPhysicalPole c e he).2.2⟩] with p hp hq
      exact ⟨hp, hq.2⟩)
    exact (congrArg (fun μ : Measure Point => μ clockGreenSupportᶜ)
      (clockGreen_eq_stripGreenOfKernel hH hLE hlam hLam A c e he)).trans hz
  apply nested_physical_measure_eq clockGreenSupport isOpen_clockGreenSupport
    (clock_weighted_pushforward_ae_support hH hLE hlam hLam A c e he)
    (Measure.ae_smul_measure _h_xinl_0 _)
  intro f hs hn
  have hmap := integral_map
    (μ := (stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      ⟨e, WithTop.coe_lt_top _, he⟩).withDensity
      (fun p => ENNReal.ofReal |p.velocity 0|)) (c.continuous_map e).measurable.aemeasurable
    (exitProbePhysical_continuous_compact f).1.measurable.aestronglyMeasurable
  have hweight := integral_withDensity_eq_integral_toReal_smul
    (μ := stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      ⟨e, WithTop.coe_lt_top _, he⟩)
    clock_velocity_weight_measurable
    (Filter.Eventually.of_forall (fun p : Point => ENNReal.ofReal_lt_top))
    (fun p => exitProbePhysical f (c.map e p))
  have hweight' : (∫ p, exitProbePhysical f (c.map e p)
      ∂(stripGreen hH hLE hlam hLam A c.activeInterval ⊤
        ⟨e, WithTop.coe_lt_top _, he⟩).withDensity
        (fun p => ENNReal.ofReal |p.velocity 0|)) =
      ∫ p, clockWeightedProbe c e f p ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤
        ⟨e, WithTop.coe_lt_top _, he⟩ := by
    simpa only [ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul, clockWeightedProbe]
      using hweight
  have _h_xinl_0 : (∫ p, clockWeightedProbe c e f p ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      ⟨e, WithTop.coe_lt_top _, he⟩) =
      (|c.vbar| * c.r ^ 2) * ∫ p, exitProbePhysical f p
        ∂clockGreen hH hLE hlam hLam A c e he := by
    obtain ⟨R, hR, htimes, hz⟩ : ∃ R : ℝ, 0 < R ∧
      (∀ p ∈ tsupport (exitProbePhysical f), p.time < R) ∧
      (∀ p, R ≤ p.time → exitProbePhysical f p = 0) := by
      have hc := (exitProbePhysical_continuous_compact f).2
      obtain ⟨b, hb⟩ := (hc.image continuous_time).bddAbove
      refine ⟨max b 0 + 1, by have := le_max_right b 0; linarith, ?_, ?_⟩
      · intro p hp
        have ht := hb (show p.time ∈ KineticPoint.time '' tsupport (exitProbePhysical f)
          from ⟨p, hp, rfl⟩)
        have := le_max_left b 0
        linarith
      · intro p hp
        apply image_eq_zero_of_notMem_tsupport
        intro hs
        have ht := hb (show p.time ∈ KineticPoint.time '' tsupport (exitProbePhysical f)
          from ⟨p, hs, rfl⟩)
        have := le_max_left b 0
        linarith
    let ei : StripPole c.activeInterval ⊤ := ⟨e, WithTop.coe_lt_top _, he⟩
    let U := e.time + 2 * c.r ^ 2 * R + 1
    have hU : e.time < U := by
      dsimp [U]
      have hpositive : 0 < 2 * c.r ^ 2 * R :=
        mul_pos (mul_pos (by norm_num) (sq_pos_of_pos c.positive)) hR
      linarith
    let ep := stripPoleFinite c.activeInterval ei U hU
    have hs' : tsupport (exitProbePhysical f) ⊆
        {p | p.time < R + 1 ∧ p.velocity 0 ∈ clockNormalizedInterval.carrier} := by
      intro p hp
      exact ⟨by linarith [htimes p hp], (hs hp).2⟩
    have hf := clock_weighted_test_finite hH hLE hlam hLam A c e R (R + 1) U
      (by linarith) (by dsimp [U]; linarith) ep rfl f hn hs' hz
    have hv : clockSourcePotential hH hLE hlam hLam A c e (R + 1) f (sectionTwoPoint (c.map e e)) = ∫ p, exitProbePhysical f p ∂clockGreen hH hLE hlam hLam A c e he := by
      let T := (R + 1)
      have hT : 0 < (R + 1) := by
        linarith
      have hRT : R < (R + 1) := by
        linarith
      let ep := stripPoleFinite clockNormalizedInterval (clockPhysicalPole c e he) T hT
      have hv := nestedSourcePotential_eq_green A clockNormalizedInterval
        (clockEvolution hH hLE hlam hLam A c e) T f ep
      have hleft : clockSourcePotential hH hLE hlam hLam A c e T f
          (sectionTwoPoint (c.map e e)) = nestedSourcePotential clockNormalizedInterval
            (clockEvolution hH hLE hlam hLam A c e) T f ep.1 := by
        have _h_inl_9 : c.map e e = (clockPhysicalPole c e he).1 := by
            ext i <;> simp [Clock.map, clockPhysicalPole]


        rw [_h_inl_9]
        rfl
      have hr := stripGreenOfKernel_horizonRestriction clockNormalizedInterval
        (clockEvolution hH hLE hlam hLam A c e).2 T ep
      have hep : stripPoleInfinite clockNormalizedInterval T ep = clockPhysicalPole c e he :=
        Subtype.ext rfl
      have hm := (congrArg (fun μ : Measure Point => μ.restrict {p | p.time < T}) (congrArg (stripGreenOfKernel clockNormalizedInterval (clockEvolution hH hLE hlam hLam A c e).2 ⊤) hep)).trans
        (congrArg (fun μ : Measure Point => μ.restrict {p | p.time < T})
          (clockGreen_eq_stripGreenOfKernel hH hLE hlam hLam A c e he).symm)
      have hrestricted := hr.trans hm
      exact hleft.trans (hv.trans ((congrArg (fun μ : Measure Point =>
        ∫ p, exitProbePhysical f p ∂μ) hrestricted).trans
        (setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp =>
          hz p (hRT.le.trans (not_lt.mp hp))))))
    have hr := stripGreen_finite_restrict_infinite hH hLE hlam hLam A c.activeInterval ei U hU
    have hstab : (∫ p, clockWeightedProbe c e f p
        ∂(stripGreen hH hLE hlam hLam A c.activeInterval ⊤ ei).restrict {p | p.time < U}) =
        ∫ p, clockWeightedProbe c e f p ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤ ei := by
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      filter_upwards [clock_forward_cone_infinite hH hLE hlam hLam A c ei] with p hp hlate
      have hclock : R ≤ (c.map e p).time := by
        have hp' := hp
        have ht : U ≤ p.time := not_lt.mp hlate
        have hsqr := sq_pos_of_pos c.positive
        dsimp [U] at ht
        nlinarith
      change |p.velocity 0| * exitProbePhysical f (c.map e p) = 0
      rw [hz _ hclock, mul_zero]
    exact hstab.symm.trans ((congrArg (fun μ : Measure Point =>
      ∫ p, clockWeightedProbe c e f p ∂μ) hr.symm).trans
        (hf.trans (congrArg (fun x : ℝ => (|c.vbar| * c.r ^ 2) * x) hv)))
  exact hmap.trans (hweight'.trans (_h_xinl_0.trans (by rw [integral_smul_measure, ENNReal.toReal_ofReal hD.le]; rfl)))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
