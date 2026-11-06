module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforwardMass

/-! # Genuine support properties of both measures in the weighted clock identity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution
open scoped ENNReal NNReal

/-- The normalized physical support is the open positive-time active strip. -/
def clockGreenSupport : Set Point := {p | 0 < p.time ∧ p.velocity 0 ∈ normalizedActive}

/-- The support used for determining the clock Green measure is open. -/
theorem isOpen_clockGreenSupport : IsOpen clockGreenSupport :=
  (isOpen_lt continuous_const continuous_time).inter
    (isOpen_Ioo.preimage ((continuous_apply 0).comp continuous_velocity))

variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)

/-- The actual normalized Green is supported inside its positive-time active strip. -/
theorem clockGreen_ae_support
     (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    ∀ᵐ p ∂clockGreen hH hLE hlam hLam A c e he, p ∈ clockGreenSupport := by
  have hh := reconstruction_green_infinite_zero_of_finite clockNormalizedInterval
    (clockEvolution hH hLE hlam hLam A c e) (clockPhysicalPole c e he)
    clockGreenSupportᶜ isOpen_clockGreenSupport.measurableSet.compl
  have hz := hh (fun T ht => by
    apply (ae_iff (p := fun p : Point => p ∈ clockGreenSupport)).mp
    filter_upwards [reconstruction_green_ae_time_gt clockNormalizedInterval
      _ T
      _,
      stripGreenOfKernel_ae_mem_stripPast clockNormalizedInterval
        _ T
        _] with p hp hq
    exact ⟨hp, hq.2⟩)
  aesop

/-- The weighted physical measure, pushed through the literal clock, has the same open support. -/
theorem clock_weighted_pushforward_ae_support
     (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    ∀ᵐ p ∂Measure.map (c.map e)
      ((stripGreen hH hLE hlam hLam A c.activeInterval ⊤
        ⟨e, WithTop.coe_lt_top _, he⟩).withDensity
        (fun p => ENNReal.ofReal |p.velocity 0|)), p ∈ clockGreenSupport := by
  apply (c.homeomorph e).measurableEmbedding.ae_map_iff.mpr
  apply (ae_withDensity_iff clock_velocity_weight_measurable).mpr
  filter_upwards [stripGreen_infinite_ae_future_carrier hH hLE hlam hLam A c.activeInterval
    ⟨e, WithTop.coe_lt_top _, he⟩,
    clock_forward_cone_infinite hH hLE hlam hLam A c
      ⟨e, WithTop.coe_lt_top _, he⟩] with p hp hc _
  refine ⟨?_, (c.mem_active_iff _).mp hp.2⟩
  change 0 < (c.map e p).time
  nlinarith

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
