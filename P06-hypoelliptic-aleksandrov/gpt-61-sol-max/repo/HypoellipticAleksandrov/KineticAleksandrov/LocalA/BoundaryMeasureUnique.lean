module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundarySolution
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
public import PDEFoundation.Calculus.RegularityOrder


/-! # Uniqueness from all stipulated ambient smooth compact tests -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo

/-- Finite physical measures are determined by the stipulated smooth product-coordinate tests. -/
theorem boundary_measure_ext {d : ℕ} (μ ν : Measure (KineticPoint d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ φ : HypoellipticAleksandrov.KineticScalarField d,
      ContDiff ℝ PDE.smoothOrder (φ ∘ (KineticPoint.equivProd d).symm) →
      HasCompactSupport φ → (∫ P, φ P ∂μ) = ∫ P, φ P ∂ν) : μ = ν := by
  let H := KineticPoint.homeomorphProd d

  exact H.measurableEmbedding.map_injective (by
      apply measure_eq_of_smooth_integral_eq isOpen_univ
      · simp
      · simp
      intro ψ hψ hc _ _
      rw [integral_map H.measurable.aemeasurable hψ.continuous.measurable.aestronglyMeasurable,
        integral_map H.measurable.aemeasurable hψ.continuous.measurable.aestronglyMeasurable]
      apply h (ψ ∘ H)
      · assumption
      · exact hc.comp_homeomorph H)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
