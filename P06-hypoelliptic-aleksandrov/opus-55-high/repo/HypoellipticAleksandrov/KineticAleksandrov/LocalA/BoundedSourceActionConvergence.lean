module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeakMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Actual source-action convergence of bounded potentials

Almost-everywhere approximation for the literal occupation measure is disintegrated back
through the master kernel. Two dominated-convergence steps recover the potential itself.
-/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter
open scoped Topology ProbabilityTheory
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- Approximation for the actual finite source-action measure yields almost-everywhere
convergence of the literal bounded potentials for the supplied starting measure. -/
theorem ae_tendsto_duhamelPotential_of_action_ae
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (ν : Measure (KineticPoint d)) [IsFiniteMeasure ν] (a T : ℝ)
    (hfloor : ∀ᵐ p ∂ν, a ≤ p.time)
    (f : ℕ → KineticPoint d → ℝ) (hf : ∀ n, Measurable (f n))
    (F : KineticPoint d → ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n p, |f n p| ≤ C)
    (hae : ∀ᵐ q ∂boundedSourceActionMeasure K ν a T,
      Tendsto (fun n => f n ⟨q.1, q.2.1, q.2.2⟩) atTop
        (𝓝 (F ⟨q.1, q.2.1, q.2.2⟩))) :
    ∀ᵐ p ∂ν, Tendsto (fun n => duhamelPotential K T (f n) p) atTop
      (𝓝 (duhamelPotential K T F p)) := by
  classical
  let ρ := ν.prod (volume.restrict (Ioo a T))
  let η := ρ.comap ((↑) : BoundedSourcePair Ω γ → KineticPoint d × ℝ)
  let κ := boundedSourcePairKernel K
  have : ProbabilityTheory.IsFiniteKernel κ := by
    dsimp only [κ, boundedSourcePairKernel]
    infer_instance
  have hD := measurableSet_boundedSourcePairSet hΩ hγ
  have hout : ∀ᵐ q ∂η.compProd κ,
      Tendsto (fun n => f n ⟨q.1.1.2, q.2.1, q.2.2⟩) atTop
        (𝓝 (F ⟨q.1.1.2, q.2.1, q.2.2⟩)) := ae_of_ae_map measurable_boundedSourceOutput.aemeasurable hae
  have hdis := Measure.ae_ae_of_ae_compProd hout
  have hvalid : ∀ᵐ q ∂η,
      Tendsto (fun n => duhamelIntegrand K (f n) q.1.1 q.1.2) atTop
        (𝓝 (duhamelIntegrand K F q.1.1 q.1.2)) := by
    filter_upwards [hdis] with q hq
    have hi := tendsto_integral_of_dominated_convergence _
      (fun n => (hf n).aestronglyMeasurable.comp_measurable
        ((KineticPoint.measurable_equivProd_symm d).comp
          (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))))
      (integrable_const C) (fun n => Eventually.of_forall fun w => by
        simp_all) hq
    have he (g : KineticPoint d → ℝ) :
        duhamelIntegrand K g q.1.1 q.1.2 = ∫ w, g ⟨q.1.2, w.1, w.2⟩ ∂κ q := by
      unfold duhamelIntegrand
      have hqvalid : q.1.1.time ≤ q.1.2 ∧
          q.1.1.position ∈ movingDomain Ω γ q.1.1.time := q.2
      aesop
    aesop
  have hmap : ∀ᵐ q ∂Measure.map Subtype.val η,
      Tendsto (fun n => duhamelIntegrand K (f n) q.1 q.2) atTop
        (𝓝 (duhamelIntegrand K F q.1 q.2)) := (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_tendsto_fun (fun n =>
        measurable_duhamelIntegrand K hΩ hγ _ (hf n))
        (measurable_duhamelIntegrand K hΩ hγ F hF))).2 hvalid
  have hrestricted : ∀ᵐ q ∂ρ.restrict (boundedSourcePairSet Ω γ),
      Tendsto (fun n => duhamelIntegrand K (f n) q.1 q.2) atTop
        (𝓝 (duhamelIntegrand K F q.1 q.2)) := by
    simpa only [η, map_comap_subtype_coe hD] using hmap
  have hpairs : ∀ᵐ q ∂ρ,
      Tendsto (fun n => duhamelIntegrand K (f n) q.1 q.2) atTop
        (𝓝 (duhamelIntegrand K F q.1 q.2)) := by
    filter_upwards [(ae_restrict_iff' hD).mp hrestricted] with q hq
    by_cases hqm : q ∈ boundedSourcePairSet Ω γ
    · simp_all
    · have hz (g : KineticPoint d → ℝ) : duhamelIntegrand K g q.1 q.2 = 0 := dite_eq_right hqm
      simp_all
  have hstarts := Measure.ae_ae_of_ae_prod hpairs
  filter_upwards [hstarts, hfloor] with p hp hpa
  have hi := tendsto_integral_of_dominated_convergence _
    (fun n => ((measurable_duhamelIntegrand K hΩ hγ _ (hf n)).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable.restrict)
    (integrable_const C) (fun n => Eventually.of_forall fun r => by
      exact abs_duhamelIntegrand_le K _ C hC (hb n) p r) hp
  have he (g : KineticPoint d → ℝ) := duhamelPotential_eq_integral_window K g p (T := T) hpa
  simp_all

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
