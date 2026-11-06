module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernels
import Mathlib.MeasureTheory.Measure.Map

/-! # Translation independence of displacement Fourier measures -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d} (hΩ : MeasurableSet Ω) (K : MovingFiberKernel Ω γ)

/-- Ambient position translation is Borel. -/
theorem measurable_evolutionAmbientStateShift  (h : PDE.Vec d) :
    Measurable (evolutionAmbientStateShift h) := measurable_fst.prodMk (measurable_snd.add_const h)

/-- Translation on the terminal state subtype is Borel. -/
theorem measurable_evolutionStateShift  (Ω : Set (PDE.Vec d))
    (γ : ℝ → PDE.Vec d) (σ : ℝ) (h : PDE.Vec d) :
    Measurable (evolutionStateShift Ω γ σ h) :=
  ((measurable_evolutionAmbientStateShift h).comp measurable_subtype_coe).subtype_mk

/-- Fiber covariance pushes forward to the ambient master measures. -/
theorem master_translation 
    (hcov : IsTranslationCovariantEvolution Ω γ hΩ K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ) (h : PDE.Vec d) :
    Measure.map (evolutionAmbientStateShift h)
        (K.master (evolutionQueryOfState Ω γ σ τ hστ p)) =
      K.master (evolutionQueryOfState Ω γ σ τ hστ (evolutionStateShift Ω γ σ h p)) := by
  rw [← K.map_fiberKernel_eq_master hΩ,
    Measure.map_map (measurable_evolutionAmbientStateShift h) measurable_subtype_coe]
  have hc := congrArg
    (Measure.map Subtype.val)
    (hcov σ τ hστ h p)
  rw [Measure.map_map measurable_subtype_coe
    (measurable_evolutionStateShift Ω γ τ h), K.map_fiberKernel_eq_master] at hc
  exact hc

/-- Translating both positions leaves the displacement Fourier phase unchanged. -/
theorem fourierPhase_shift  (ξ z h : PDE.Vec d) (w : EvolutionAmbientState d) :
    fourierPhase ξ (z + h) (evolutionAmbientStateShift h w) = fourierPhase ξ z w := by
  simp only [fourierPhase, evolutionAmbientStateShift, add_sub_add_right_eq_sub]

/-- The Fourier projection is independent of simultaneous starting-position translation. -/
theorem fourierProjection_translation 
    (hcov : IsTranslationCovariantEvolution Ω γ hΩ K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ) (h ξ : PDE.Vec d) :
    fourierProjection K
      (evolutionQueryOfState Ω γ σ τ hστ (evolutionStateShift Ω γ σ h p)) ξ =
    fourierProjection K (evolutionQueryOfState Ω γ σ τ hστ p) ξ := by
  apply VectorMeasure.ext
  intro E hE
  rw [fourierProjection_spec K _ ξ E hE, fourierProjection_spec K _ ξ E hE,
    ← master_translation hΩ K hcov]
  rw [← integral_indicator (hE.prod MeasurableSet.univ),
    ← integral_indicator (hE.prod MeasurableSet.univ)]
  rw [integral_map (measurable_evolutionAmbientStateShift h).aemeasurable
    (((continuous_fourierPhase ξ _).measurable.indicator
      (hE.prod MeasurableSet.univ)).aestronglyMeasurable)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w
  change (E ×ˢ univ).indicator (fourierPhase ξ (p.1.2 + h))
    _ = (E ×ˢ univ).indicator (fourierPhase ξ p.1.2) w
  by_cases hw : w.1 ∈ E
  · rw [indicator_of_mem (by aesop),
      indicator_of_mem (by simp_all), fourierPhase_shift]
  · rw [indicator_of_notMem (by aesop),
      indicator_of_notMem (by simp_all)]

/-- Starting position does not affect the whole-space Fourier kernel. -/
theorem fourierKernel_eq_startingPosition 
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0)
      MeasurableSet.univ K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v z : PDE.Vec d) :
    fourierProjection K (wholeSpaceQuery σ τ hστ v z) ξ =
      fourierKernel K σ τ hστ ξ v := by
  let p : EvolutionState _ _ σ :=
    ⟨(v, 0), (wholeSpaceQuery σ τ hστ v 0).property.2⟩
  have hq : evolutionQueryOfState _ _ σ τ hστ
      (evolutionStateShift _ _ σ z p) =
      wholeSpaceQuery σ τ hστ v z := by
    apply Subtype.ext
    simp only [evolutionQueryOfState, evolutionStateShift, evolutionAmbientStateShift,
      wholeSpaceQuery, p, zero_add]
  have hp : evolutionQueryOfState _ _ σ τ hστ p =
      wholeSpaceQuery σ τ hστ v 0 := rfl
  have ht := fourierProjection_translation MeasurableSet.univ K hcov σ τ hστ p z ξ
  exact (congrArg (fun q => fourierProjection K q ξ) hq).symm.trans
    (ht.trans (congrArg (fun q => fourierProjection K q ξ) hp))

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
