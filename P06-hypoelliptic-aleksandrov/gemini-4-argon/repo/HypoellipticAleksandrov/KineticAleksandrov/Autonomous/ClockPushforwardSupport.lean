module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforwardMass

/-! # Genuine support properties of both measures in the weighted clock identity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution
open scoped ENNReal NNReal

/- The normalized physical support is the open positive-time active strip. -/
def clockGreenSupport : Set Point := {p | 0 < p.time ∧ p.velocity 0 ∈ normalizedActive}

/- The support used for determining the clock Green measure is open. -/
theorem isOpen_clockGreenSupport : IsOpen clockGreenSupport :=
  (isOpen_lt continuous_const continuous_time).inter
    (isOpen_Ioo.preimage ((continuous_apply 0).comp continuous_velocity))

/- The actual normalized Green is supported inside its positive-time active strip. -/
theorem clock_weighted_pushforward_ae_support
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
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
  refine ⟨?_, (c.mem_active_iff (p.velocity 0)).mp hp.2⟩
  change 0 < (c.map e p).time
  have hs := sq_pos_of_pos c.positive
  have ht := hp.1
  have hc' := hc
  nlinarith

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
