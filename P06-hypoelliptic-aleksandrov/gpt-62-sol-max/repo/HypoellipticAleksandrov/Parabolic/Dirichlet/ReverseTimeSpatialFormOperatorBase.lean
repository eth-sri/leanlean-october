module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds

/-! # The reverse-time spatial operator -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The reverse-time spatial form as a continuous operator at a local time. -/
noncomputable def reverseTimeSpatialFormOperator
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
    (τ : Set.Icc 0 (r₁ - r₀)) :
    H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ :=
  (ReverseTimeSpatialFormEvidence.ofSmooth hΩ hΩbounded haSmooth hbSmooth hcSmooth).operator hΩ τ

/-- The local operator evaluates to the literal reverse-time spatial form. -/
theorem reverseTimeSpatialFormOperator_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
    (τ : Set.Icc 0 (r₁ - r₀)) (u v : H10HilbertGraph hΩ) :
    reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ u v =
      reverseTimeSpatialForm hΩ r₁ τ.1 a b c u v :=
  (ReverseTimeSpatialFormEvidence.ofSmooth hΩ hΩbounded haSmooth hbSmooth hcSmooth).operator_apply hΩ τ u v

/-- The local operator curve has one time-uniform application bound. -/
theorem exists_reverseTimeSpatialFormOperator_bound
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ u : H10HilbertGraph hΩ,
        ‖reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth τ u‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC, hForm⟩ :=
    reverseTimeSpatialForm_bounded_of_smoothOnNeighborhood r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth
  refine ⟨C, hC, ?_⟩
  intro τ u
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg _))
  intro v
  rw [Real.norm_eq_abs, reverseTimeSpatialFormOperator_apply]
  exact hForm τ.1 τ.2 u v


end HypoellipticAleksandrov.Parabolic.Dirichlet
