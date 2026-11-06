module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionHorizonLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRepresentation

/-! # Closed early-time exit domination at an intermediate observation time -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo TheoremA Evolution
open scoped Topology

/- Nonnegative compact smooth physical probes determine order of finite measures. -/
theorem enlarged_physical_measure_le {mu nu : Measure Point}
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (h : ∀ f : exitProbeSubmodule, (∀ p, 0 ≤ exitProbePhysical f p) →
      (∫ p, exitProbePhysical f p ∂mu) ≤ ∫ p, exitProbePhysical f p ∂nu) : mu ≤ nu := by
  let e := reconstructionPhysicalHomeomorph
  have hm : mu.map e.symm ≤ nu.map e.symm := by
    apply measure_le_of_smooth_integral_le isOpen_univ (by simp)
    intro f hf hc _ hn
    let F : exitProbeSubmodule := ⟨f, hf, hc⟩
    have hh := h F (fun p => hn _)
    have hi (rho : Measure Point) : (∫ x, f x ∂rho.map e.symm) =
        ∫ p, exitProbePhysical F p ∂rho :=
      integral_map e.symm.measurable.aemeasurable hf.continuous.measurable.aestronglyMeasurable
    rw [hi mu, hi nu]
    exact hh
  have hb (rho : Measure Point) : (rho.map e.symm).map e = rho := by
    rw [Measure.map_map e.measurable e.symm.measurable]
    have he : e ∘ e.symm = (id : Point → Point) := funext e.apply_symm_apply
    rw [he, Measure.map_id]
  have hmap := Measure.map_mono hm e.measurable
  rwa [hb mu, hb nu] at hmap

/- Later-horizon exits up to a closed intermediate time are dominated by its stopped exit.
This retains possible endpoint mass rather than assuming temporal atomlessness. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
