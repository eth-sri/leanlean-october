module

public import HypoellipticAleksandrov.Parabolic.ScalarZeroOrderMaximum
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonCalculus
public import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter Set Matrix
open scoped MatrixOrder Topology
open LocalHolder

/-- Ordered source, terminal, and lateral data order supplied classical backward solutions. -/
theorem le_on_closedCylinder_of_isClassicalBackwardDirichletSolution
    {n : ℕ} {Ω : Set (PDE.Vec n)} {r₀ r₁ : ℝ}
    (hΩOpen : IsOpen Ω)
    (hΩBounded : Bornology.IsBounded Ω)
    (hr : r₀ < r₁)
    (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n)
    (c : ℝ → PDE.Vec n → ℝ)
    (haContinuous : IsContinuousCoefficient a)
    (hbContinuous : Continuous (fun z : TimeVelocity n => b z.1 z.2))
    (haPsd : ∀ r y, (a r y).PosSemidef)
    (hc : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω, c z.1 z.2 ≤ 0)
    (F_u F_v : ℝ → PDE.Vec n → ℝ)
    (phi_u phi_v : PDE.Vec n → ℝ)
    (h_u h_v u v : TimeVelocity n → ℝ)
    (hu : IsClassicalBackwardDirichletSolution r₀ r₁ Ω a b c F_u phi_u h_u u)
    (hv : IsClassicalBackwardDirichletSolution r₀ r₁ Ω a b c F_v phi_v h_v v)
    (hF : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω, F_v z.1 z.2 ≤ F_u z.1 z.2)
    (hPhi : ∀ y ∈ closure Ω, phi_u y ≤ phi_v y)
    (hLat : ∀ z ∈ scalarParabolicLateralFace r₀ r₁ Ω, h_u z ≤ h_v z) :
    ∀ z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω, u z ≤ v z := by
  have hzero : ∀ z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω, u z - v z ≤ 0 := by
    apply scalar_le_zero_on_closedCylinder_of_zeroOrderOperator_nonneg
      hΩOpen hΩBounded hr a b c haContinuous hbContinuous haPsd hc (fun q => u q - v q)
    · exact hu.1.sub hv.1
    · exact isScalarC12On_sub hu.2.1 hv.2.1
    · intro z hz
      rw [scalarParabolicZeroOrderOperator_sub a b c hu.2.1 hv.2.1 hz,
        hu.2.2.1 z hz, hv.2.2.1 z hz]
      exact sub_nonneg.mpr (hF z hz)
    · rintro ⟨r, y⟩ ⟨hr, hy⟩
      simp only [mem_singleton_iff] at hr
      subst r
      rw [hu.2.2.2.1 y hy, hv.2.2.2.1 y hy]
      exact sub_nonpos.mpr (hPhi y hy)
    · intro z hz
      rw [hu.2.2.2.2 z hz, hv.2.2.2.2 z hz]
      exact sub_nonpos.mpr (hLat z hz)
  intro z hz
  exact sub_nonpos.mp (hzero z hz)

/-- Classical backward Dirichlet solutions with identical data agree on the closed cylinder. -/
theorem eqOn_closedCylinder_of_isClassicalBackwardDirichletSolution
    {n : ℕ} {Ω : Set (PDE.Vec n)} {r₀ r₁ : ℝ}
    (hΩOpen : IsOpen Ω)
    (hΩBounded : Bornology.IsBounded Ω)
    (hr : r₀ < r₁)
    (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n)
    (c F : ℝ → PDE.Vec n → ℝ)
    (phi : PDE.Vec n → ℝ) (h u v : TimeVelocity n → ℝ)
    (haContinuous : IsContinuousCoefficient a)
    (hbContinuous : Continuous (fun z : TimeVelocity n => b z.1 z.2))
    (haPsd : ∀ r y, (a r y).PosSemidef)
    (hc : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω, c z.1 z.2 ≤ 0)
    (hu : IsClassicalBackwardDirichletSolution r₀ r₁ Ω a b c F phi h u)
    (hv : IsClassicalBackwardDirichletSolution r₀ r₁ Ω a b c F phi h v) :
    Set.EqOn u v (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
  intro z hz
  apply le_antisymm
  · exact le_on_closedCylinder_of_isClassicalBackwardDirichletSolution
      hΩOpen hΩBounded hr a b c haContinuous hbContinuous haPsd hc F F phi phi h h u v
      hu hv (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) z hz
  · exact le_on_closedCylinder_of_isClassicalBackwardDirichletSolution
      hΩOpen hΩBounded hr a b c haContinuous hbContinuous haPsd hc F F phi phi h h v u
      hv hu (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) z hz

end HypoellipticAleksandrov.Parabolic
