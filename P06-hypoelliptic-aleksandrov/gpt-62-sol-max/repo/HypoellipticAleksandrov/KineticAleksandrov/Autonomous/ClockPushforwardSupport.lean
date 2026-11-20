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

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
  (he : e.velocity 0 ∈ c.active)

/-- The actual normalized Green is supported inside its positive-time active strip. -/
theorem clockGreen_ae_support :
    ∀ᵐ p ∂clockGreen A c e he, p ∈ clockGreenSupport := by
  rw [ae_iff]
  have hh := reconstruction_green_infinite_zero_of_finite clockNormalizedInterval
    (clockEvolution A c e) (clockPhysicalPole c e he)
    clockGreenSupportᶜ isOpen_clockGreenSupport.measurableSet.compl
  have hz := hh (fun T ht => by
    apply (ae_iff (p := fun p : Point => p ∈ clockGreenSupport)).mp
    filter_upwards [reconstruction_green_ae_time_gt clockNormalizedInterval
      (clockEvolution A c e).2 T
      ⟨(clockPhysicalPole c e he).1, WithTop.coe_lt_coe.mpr ht,
        (clockPhysicalPole c e he).2.2⟩,
      stripGreenOfKernel_ae_mem_stripPast clockNormalizedInterval
        (clockEvolution A c e).2 T
        ⟨(clockPhysicalPole c e he).1, WithTop.coe_lt_coe.mpr ht,
          (clockPhysicalPole c e he).2.2⟩] with p hp hq
    exact ⟨hp, hq.2⟩)
  assumption

/-- The weighted physical measure, pushed through the literal clock, has the same open support. -/
theorem clock_weighted_pushforward_ae_support :
    ∀ᵐ p ∂Measure.map (c.map e)
      ((stripGreen A c.activeInterval ⊤
        ⟨e, WithTop.coe_lt_top _, he⟩).withDensity
        (fun p => ENNReal.ofReal |p.velocity 0|)), p ∈ clockGreenSupport := by
  apply (c.homeomorph e).measurableEmbedding.ae_map_iff.mpr
  apply (ae_withDensity_iff clock_velocity_weight_measurable).mpr
  filter_upwards [stripGreen_infinite_ae_future_carrier A c.activeInterval
    ⟨e, WithTop.coe_lt_top _, he⟩,
    clock_forward_cone_infinite A c
      ⟨e, WithTop.coe_lt_top _, he⟩] with p hp hc _
  refine ⟨?_, (c.mem_active_iff (p.velocity 0)).mp hp.2⟩
  change 0 < (c.map e p).time
  nlinarith

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
