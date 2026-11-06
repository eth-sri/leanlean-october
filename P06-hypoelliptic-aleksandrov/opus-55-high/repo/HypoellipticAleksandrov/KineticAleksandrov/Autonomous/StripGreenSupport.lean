module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenCharacterization

/-! # Open-domain support of the physical killed Green measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

/-- The physical open past strip, without an artificial lower time endpoint. -/
def stripPast (H : Interval) (T : ℝ) : Set Point :=
  {p | p.time < T ∧ p.velocity 0 ∈ H.carrier}

variable (H : Interval) (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ) (e : StripPole H (T : WithTop ℝ))

/-- The physical past strip is open in the native topology. -/
theorem isOpen_stripPast  : IsOpen (stripPast H T) :=
  (isOpen_Iio.preimage continuous_time).inter
    (isOpen_Ioo.preimage ((continuous_apply 0).comp continuous_velocity))

private theorem elapsedPhysicalPoint_mem_stripPast  (τ : ElapsedTime (stripHorizon T e.1.time))
    (w : EvolutionAmbientState 1)
    (hw : w ∈ evolutionStateSet (intervalDomain H) (fun _ => 0) (e.1.time + τ.1)) :
    elapsedPhysicalPoint e.1.time (τ, w) ∈ stripPast H T := by
  refine ⟨?_, ?_⟩
  · have hR : 0 < T - e.1.time := sub_pos.mpr (WithTop.coe_lt_coe.mp e.2.1)
    have hτ : τ.1 < T - e.1.time := (ENNReal.ofReal_lt_ofReal_iff hR).mp τ.2.2
    change e.1.time + τ.1 < T
    linarith
  · have hv : w.1 ∈ intervalDomain H := by
      simpa only [movingDomain, PDE.mem_translateSet_iff_sub_mem, sub_zero] using hw.1
    aesop

/-- Killing and elapsed-time truncation support the actual measure on the open past strip. -/
theorem stripGreenOfKernel_compl_stripPast  :
    stripGreenOfKernel H K T e (stripPast H T)ᶜ = 0 := by
  have hD := (isOpen_stripPast H T).measurableSet
  rw [← lintegral_indicator_one hD.compl]
  rw [stripGreenOfKernel_spec H K T e _ (measurable_one.indicator hD.compl)]
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Eventually.of_forall
  intro τ
  dsimp only
  rw [← K.terminal_support]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem
    (measurableSet_evolutionStateSet (intervalDomain_measurable H) _)]
    with w hw
  have hn : elapsedPhysicalPoint e.1.time (τ, w) ∉ (stripPast H T)ᶜ := not_not.mpr (elapsedPhysicalPoint_mem_stripPast H T e τ w hw)
  simp_all

/-- Green almost every physical point lies in the open past strip. -/
theorem stripGreenOfKernel_ae_mem_stripPast  :
    ∀ᵐ p ∂stripGreenOfKernel H K T e, p ∈ stripPast H T := stripGreenOfKernel_compl_stripPast H K T e

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
