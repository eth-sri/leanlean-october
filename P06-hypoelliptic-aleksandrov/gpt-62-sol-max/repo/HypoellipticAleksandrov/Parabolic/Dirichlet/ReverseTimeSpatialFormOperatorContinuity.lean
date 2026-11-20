module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperatorBase

/-! # Operator-norm continuity of the reverse-time spatial form -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The local reverse-time spatial operator is continuous in operator norm. -/
theorem continuous_reverseTimeSpatialFormOperator
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c) :
    Continuous (reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth) :=
  (ReverseTimeSpatialFormEvidence.ofSmooth hΩ hΩbounded haSmooth hbSmooth hcSmooth).continuous_operator hΩ
    hΩbounded haSmooth hbSmooth hcSmooth

end HypoellipticAleksandrov.Parabolic.Dirichlet
