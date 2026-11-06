module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Duhamel

/-! # Identification of Duhamel source slices with the supplied evolution operators -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set

variable {d : ℕ}

/-- A bounded Borel spacetime source restricted to one absolute-time state slice. -/
def duhamelSlice  (g : BoundedBorel (KineticPoint d)) (r : ℝ) :
    BoundedBorel (EvolutionAmbientState d) := by
  refine ⟨fun w => g ⟨r, w.1, w.2⟩, ?_, ?_⟩
  · convert g.measurable.comp ((KineticPoint.measurable_equivProd_symm d).comp
      (measurable_const.prodMk measurable_id)) using 1
    rfl
  · obtain ⟨C, hC, hg⟩ := g.exists_bound
    exact ⟨C, hC, fun w => hg ⟨r, w.1, w.2⟩⟩

/-- Each source-time kernel integral equals the supplied terminal evolution action. -/
theorem duhamelSourceIntegral_eq_evolution  {Ω : PDE.VelocityRegion d}
    {γ : ℝ → PDE.Vec d} (hΩ : MeasurableSet Ω)
    (B : FullKineticCoefficient d) (b : PDE.VectorField d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (g : BoundedBorel (KineticPoint d)) (σ r : ℝ) (hσr : σ ≤ r)
    (p : EvolutionState Ω γ σ) :
    duhamelSourceIntegral K g (evolutionQueryOfState Ω γ σ r hσr p) =
      S σ r hσr (terminalStateDatum (duhamelSlice g r)) p := by
  rw [hreal.2.1 σ r hσr p (terminalStateDatum (duhamelSlice g r))]
  unfold duhamelSourceIntegral
  rw [← K.map_fiberKernel_eq_master hΩ σ r hσr p]
  exact integral_map measurable_subtype_coe.aemeasurable
    (duhamelSlice g r).measurable.aestronglyMeasurable

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
