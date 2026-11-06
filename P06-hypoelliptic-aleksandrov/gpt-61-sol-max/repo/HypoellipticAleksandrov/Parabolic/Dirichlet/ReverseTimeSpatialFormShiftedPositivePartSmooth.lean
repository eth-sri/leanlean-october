module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormShiftedPositivePart

/-!
# Smooth-data shifted positive-part spatial-form inequality

This file derives the scalar-product integrability required by the literal
fixed-slice theorem from closed-cylinder smoothness and boundedness of the
spatial domain.
-/

 public section

open MeasureTheory Set
open scoped NNReal



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Smoothness of the scalar coefficient on a bounded closed cylinder supplies
the fixed-slice shifted positive-part spatial-form inequality. -/
theorem reverseTimeSpatialForm_apply_shiftedPositivePart_ge_of_smoothOnNeighborhood
    {d : ℕ} {Ω : PDE.VelocityRegion d}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : PDE.TimeVectorField d)
    (c : PDE.TimeScalarField d)
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (u : H10HilbertGraph hΩ) (k : ℝ≥0) :
    reverseTimeSpatialForm hΩ r₁ τ a b c u (h10ShiftedPositivePart hΩ u k) ≥
      reverseTimeSpatialForm hΩ r₁ τ a b c
        (h10ShiftedPositivePart hΩ u k) (h10ShiftedPositivePart hΩ u k) := by
  let q := fun y  => reverseTimeScalarCoefficient r₁ c τ y
  let U := valueCLM hΩ u
  let W := valueCLM hΩ (h10ShiftedPositivePart hΩ u k)
  obtain ⟨C, hC, hCbound⟩ :=
    exists_reverseTimeScalarCoefficient_bound_of_smoothOnNeighborhood
      r₀ r₁ hΩbounded c hcSmooth
  have hqMeas : AEStronglyMeasurable q (PDE.volumeOn Ω) := by
    exact (continuousOn_reverseTimeScalarCoefficient_slice_of_smoothOnNeighborhood
      r₀ r₁ τ c hcSmooth hτ).aestronglyMeasurable hΩ.measurableSet
  have hqBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y‖ ≤ C := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
    exact hCbound τ hτ y hy



  exact reverseTimeSpatialForm_apply_shiftedPositivePart_ge hΩ r₁ τ a b c u k
    (by

        filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
        simpa only [q, reverseTimeScalarCoefficient_apply] using
          hcNonpos (r₁ - τ, y) ⟨(by
              constructor <;> linarith [h₀₁, hτ.1, hτ.2]), subset_closure hy⟩) ((by
        refine (L2.integrable_inner (𝕜 := ℝ)
          (scalarL2Multiplier q hqMeas C hC hqBound W) W).congr ?_
        filter_upwards [scalarL2Multiplier_apply_ae q hqMeas C hC hqBound W] with y hy
        rw [hy]
        simp only [RCLike.inner_apply, conj_trivial]
        ring))
    ((by
        refine (L2.integrable_inner (𝕜 := ℝ)
          (scalarL2Multiplier q hqMeas C hC hqBound U) W).congr ?_
        filter_upwards [scalarL2Multiplier_apply_ae q hqMeas C hC hqBound U] with y hy
        rw [hy]
        simp only [RCLike.inner_apply, conj_trivial]
        ring))

end HypoellipticAleksandrov.Parabolic.Dirichlet
