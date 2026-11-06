module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyApproximateIdentity

/-! # Essential bounds suffice for normalized spatial convolution -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory
open scoped Convolution

/-- The normalized mollifier respects an essential bound, without changing the selected
representative on its exceptional null set. -/
theorem construction_spatialMollify_norm_le_ae {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasureSpace G] [BorelSpace G]
    [FiniteDimensional ℝ G] [Measure.IsAddHaarMeasure (volume : Measure G)]
    (phi : ContDiffBump (0 : G)) (g : G → ℝ) (hg : AEStronglyMeasurable g volume)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ x ∂volume, |g x| ≤ C) (q : G) :
    ‖spatialMollify phi g q‖ ≤ C := by
  let f := fun x => max (-C) (min (g x) C)
  have hf : AEStronglyMeasurable f volume :=
    (aemeasurable_const.max (hg.aemeasurable.min aemeasurable_const)).aestronglyMeasurable
  have he : f =ᵐ[volume] g := by
    filter_upwards [hb] with x hx
    grind
  have hfB : ∀ x, ‖f x‖ ≤ C := by
    intro x
    rw [Real.norm_eq_abs, abs_le]
    grind
  have hc : spatialMollify phi f = spatialMollify phi g := convolution_congr _
      (Filter.Eventually.of_forall (fun _ => rfl)) he
  rw [← hc]
  exact spatialMollify_norm_le phi f hf C hC hfB q

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
