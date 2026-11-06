module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Duhamel

/-! # Identification of Duhamel source slices with the supplied evolution operators -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set

/- A bounded Borel spacetime source restricted to one absolute-time state slice. -/
def duhamelSlice {d } (g : BoundedBorel (KineticPoint d)) (r : ℝ) :
    BoundedBorel (EvolutionAmbientState d) := by
  refine ⟨fun w => g ⟨r, w.1, w.2⟩, ?_, ?_⟩
  · convert g.measurable.comp ((KineticPoint.measurable_equivProd_symm d).comp
      (measurable_const.prodMk measurable_id)) using 1
    rfl
  · obtain ⟨C, hC, hg⟩ := g.exists_bound
    exact ⟨C, hC, fun w => hg ⟨r, w.1, w.2⟩⟩

/- Each source-time kernel integral equals the supplied terminal evolution action. -/
end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
