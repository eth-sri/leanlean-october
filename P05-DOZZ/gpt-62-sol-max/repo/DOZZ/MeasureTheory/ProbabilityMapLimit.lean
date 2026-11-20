/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Almost-sure convergence of random variables implies weak convergence of their laws. -/

@[expose] public section
open MeasureTheory Filter Topology
namespace DOZZ.Proofs

theorem probabilityMap_tendsto_of_ae
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [MeasurableSpace E]
    [BorelSpace E] (Q : ProbabilityMeasure Ω) (f : ℕ → Ω → E) (g : Ω → E)
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hlim : ∀ᵐ ω ∂(Q : Measure Ω), Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    Tendsto (fun n => Q.map (f n)) atTop (𝓝 (Q.map g)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro test
  have hmap (n : ℕ) : (∫ x, test x ∂(Q.map (f n) : Measure E)) =
      ∫ ω, test (f n ω) ∂(Q : Measure Ω) := integral_map (hf n).aemeasurable test.continuous.measurable.aestronglyMeasurable
  have hmapg : (∫ x, test x ∂(Q.map g : Measure E)) =
      ∫ ω, test (g ω) ∂(Q : Measure Ω) := integral_map hg.aemeasurable test.continuous.measurable.aestronglyMeasurable
  simp_rw [hmap, hmapg]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖test‖)
  · intro n
    exact (test.continuous.measurable.comp (hf n)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ fun ω => test.norm_coe_le_norm (f n ω)
  · exact hlim.mono fun ω hω => test.continuous.continuousAt.tendsto.comp hω

end DOZZ.Proofs
