module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinCoordinatesBase
import Batteries.Tactic.Alias



/-!
# Reverse-time finite Galerkin coordinate equation

This module proves the exact finite-coordinate reverse-time Galerkin equation.
It does not assert existence, uniqueness, differentiability, or an energy estimate.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open scoped BigOperators ENNReal Matrix Matrix.Norms.Elementwise

private theorem bilinear_mulVec_eq_coe_submodule_sum
    {I E : Type} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Submodule ℝ E) (L : E →L[ℝ] E →L[ℝ] ℝ)
    (e : I → p) (x : I → ℝ) (i : I) :
    ((fun i j => L (e j : E) (e i : E)) *ᵥ x) i =
      L (↑(∑ j, x j • e j) ) (e i : E) := by
  let sharedTerm_b7dbbfb723 := ((∑ j, x j • (e j : E)))

  change (∑ j, L (e j : E) (e i : E) * x j) =
    L (↑(∑ j, x j • e j) ) (e i : E)
  calc
    _ = ∑ j, L (x j • (e j : E)) (e i : E) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [L.map_smul, ContinuousLinearMap.smul_apply]
      exact mul_comm _ _
    _ = (∑ j, L (x j • (e j : E))) (e i : E) := (map_sum (ContinuousLinearMap.apply ℝ ℝ (e i : E))
        (fun j => L (x j • (e j : E))) Finset.univ).symm
    _ = L sharedTerm_b7dbbfb723 (e i : E) := by rw [← map_sum]
    _ = _ := congrArg (fun u => L u (e i : E)) (show (↑(∑ j, x j • e j) : E) = sharedTerm_b7dbbfb723 by
        exact (Submodule.coe_sum (p := p) (fun j => x j • e j) Finset.univ)).symm

variable {d : ℕ} {Ω : PDE.VelocityRegion d}

private theorem coe_galerkinReconstruct_eq_sum

    (hΩ : IsOpen Ω) (N : ℕ)
    (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) : type_of% (congrArg (fun u : galerkinSpace hΩ N => (u : H10HilbertGraph hΩ))
    (galerkinReconstruct_apply hΩ N x)) := congrArg (fun u : galerkinSpace hΩ N => (u : H10HilbertGraph hΩ))
    (galerkinReconstruct_apply hΩ N x)

section
variable (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d) (b : PDE.TimeVectorField d) (c : PDE.TimeScalarField d) (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω)) (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀)) (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (i : Fin (Module.finrank ℝ (galerkinSpace hΩ N)))

private theorem stiffness_mulVec_eq_operator_sum

     :
    (reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ *ᵥ
      x) i =
      reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ
        (↑(∑ j, x j • galerkinSpaceBasis hΩ N j) )
        (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := by
  solve_by_elim (maxDepth := 4) [H10HilbertGraph, reverseTimeSpatialFormOperator, galerkinSpace, galerkinSpaceBasis, bilinear_mulVec_eq_coe_submodule_sum]

private theorem operator_sum_eq_operator_reconstruct

     :
    reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ
        (↑(∑ j, x j • galerkinSpaceBasis hΩ N j) )
        (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
      reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ
        (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
        (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := (congrArg
  (fun u =>
    ((reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ) u)
      ↑((galerkinSpaceBasis hΩ N) i))
  (Eq.symm (coe_galerkinReconstruct_eq_sum hΩ N x)))

private theorem operator_reconstruct_eq_raw_form

     :
    reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ
        (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
        (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
      reverseTimeSpatialForm hΩ r₁ τ.1 a b c
        (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
        (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := reverseTimeSpatialFormOperator_apply r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
    τ _ _

private theorem stiffness_mulVec_eq_form

     :
    (reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ *ᵥ
      x) i = reverseTimeSpatialForm hΩ r₁ τ.1 a b c
        (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
        (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := (Trans.trans
  (Trans.trans (stiffness_mulVec_eq_operator_sum r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ x i)
    (operator_sum_eq_operator_reconstruct r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ x i))
  (operator_reconstruct_eq_raw_form r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ x i))
end


private theorem map_galerkinBasis_sum

    (hΩ : IsOpen Ω) (N : ℕ) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : H10HilbertGraph hΩ →L[ℝ] W)
    (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
    L (↑(∑ j, x j • galerkinSpaceBasis hΩ N j) ) =
      ∑ j, x j • L (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ) := by

  calc
    L (↑(∑ j, x j • galerkinSpaceBasis hΩ N j) ) =
        L (∑ j, x j • (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ)) := congrArg L (by
            simpa only [Submodule.coe_smul] using
              (Submodule.coe_sum (p := galerkinSpace hΩ N)
                (fun j => x j • galerkinSpaceBasis hΩ N j) Finset.univ))
    _ = ∑ j, L (x j • (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ)) :=
      map_sum L (fun j => x j • (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ)) Finset.univ
    _ = ∑ j, x j • L (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ) := by
      apply Finset.sum_congr rfl
      intro j _
      exact L.map_smul (x j) _

private theorem gram_mulVec_eq_inner_sum
    {I E : Type} [Fintype I] [DecidableEq I] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (v : I → E) (x : I → ℝ) (i : I) :
    (Matrix.gram ℝ v *ᵥ x) i = inner ℝ (∑ j, x j • v j) (v i) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.gram_apply, sum_inner, inner_smul_left,
    starRingEnd_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm]
  exact mul_comm _ _

variable {d : ℕ} {Ω : PDE.VelocityRegion d}

private theorem galerkinMass_mulVec_eq_inner_reconstruct

    (hΩ : IsOpen Ω) (N : ℕ)
    (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (i : Fin (Module.finrank ℝ (galerkinSpace hΩ N))) :
    (galerkinMassGram hΩ N *ᵥ x) i =
      inner ℝ
        (valueCLM hΩ (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ))
        (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) := by
  rw [galerkinReconstruct_apply]
  let v : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → PDE.ScalarLp Ω (2 ) :=
    fun j => valueCLM hΩ (galerkinSpaceBasis hΩ N j : H10HilbertGraph hΩ)
  calc
    (galerkinMassGram hΩ N *ᵥ x) i = (Matrix.gram ℝ v *ᵥ x) i := rfl
    _ = inner ℝ (∑ j, x j • v j) (v i) := gram_mulVec_eq_inner_sum v x i
    _ = inner ℝ
        (valueCLM hΩ (↑(∑ j, x j • galerkinSpaceBasis hΩ N j) ))
        (v i) := congrArg (fun z => inner ℝ z (v i))
          (map_galerkinBasis_sum hΩ N (valueCLM hΩ) x).symm

private theorem weak_rows_iff_matrix_rows

    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : PDE.TimeVectorField d) (c F : PDE.TimeScalarField d)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀))
    (x xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
    (∀ i,
      inner ℝ
          (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))
          (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
        reverseTimeSpatialForm hΩ r₁ τ.1 a b c
          (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
          (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) ↔
      ∀ i, (galerkinMassGram hΩ N *ᵥ xdot) i +
        (reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ *ᵥ
          x) i =
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i := by
  constructor <;> intro h i
  · simpa only [galerkinMass_mulVec_eq_inner_reconstruct, stiffness_mulVec_eq_form] using h i
  · simpa only [galerkinMass_mulVec_eq_inner_reconstruct, stiffness_mulVec_eq_form] using h i

variable {I : Type}

private theorem matrix_coordinateEquation_iff
     [Fintype I] [DecidableEq I]
    (M K : Matrix I I ℝ) (q x xdot : I → ℝ) (hdet : IsUnit M.det) :
    (∀ i, (M *ᵥ xdot) i + (K *ᵥ x) i = q i) ↔
      xdot = -(M⁻¹ *ᵥ (K *ᵥ x)) + M⁻¹ *ᵥ q := by
  constructor
  · intro h


    calc
      xdot = (1 : Matrix I I ℝ) *ᵥ xdot := (Matrix.one_mulVec _).symm
      _ = (M⁻¹ * M) *ᵥ xdot := by rw [Matrix.nonsing_inv_mul M hdet]
      _ = M⁻¹ *ᵥ (M *ᵥ xdot) := (Matrix.mulVec_mulVec xdot M⁻¹ M).symm
      _ = M⁻¹ *ᵥ (q - K *ᵥ x) := by rw [((eq_sub_iff_add_eq).2 (show M *ᵥ xdot + K *ᵥ x = q by
          ext i
          exact h i))]
      _ = -(M⁻¹ *ᵥ (K *ᵥ x)) + M⁻¹ *ᵥ q := by
        rw [Matrix.mulVec_sub]
        abel
  · intro h

    intro i
    exact congrFun (show M *ᵥ xdot + K *ᵥ x = q by
        have hstiff : M *ᵥ (M⁻¹ *ᵥ (K *ᵥ x)) = K *ᵥ x := by
          rw [Matrix.mulVec_mulVec (K *ᵥ x) M M⁻¹, Matrix.mul_nonsing_inv M hdet,
            Matrix.one_mulVec]
        have hsource : M *ᵥ (M⁻¹ *ᵥ q) = q := by
          rw [Matrix.mulVec_mulVec q M M⁻¹, Matrix.mul_nonsing_inv M hdet,
            Matrix.one_mulVec]
        rw [h, Matrix.mulVec_add, Matrix.mulVec_neg, hstiff, hsource]
        abel) i

private theorem matrix_solution_eq_continuousMulVec_rhs
     [Fintype I] [DecidableEq I]
    (M K : Matrix I I ℝ) (q x : I → ℝ) :
    -(M *ᵥ (K *ᵥ x)) + M *ᵥ q =
      (- LinearMap.toContinuousLinearMap (Matrix.mulVecLin (M * K))) x + M *ᵥ q := by
  simp_all

private theorem matrix_solution_eq_reverseTimeGalerkin_rhs
    {d : ℕ} {Ω : PDE.VelocityRegion d}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : PDE.TimeVectorField d) (c F : PDE.TimeScalarField d)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀))
    (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
    -((galerkinMassGram hΩ N)⁻¹ *ᵥ
      (reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ *ᵥ
        x)) +
      (galerkinMassGram hΩ N)⁻¹ *ᵥ
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ =
      reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ x +
        reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ := by
  solve_by_elim (maxDepth := 4) [galerkinMassGram, reverseTimeGalerkinStiffness, reverseTimeGalerkinSource, matrix_solution_eq_continuousMulVec_rhs]

private theorem eq_iff_eq_of_eq_right {E : Type} (x y z : E) (hyz : y = z) :
    (x = y ↔ x = z) := by
  rw [hyz]

variable {d : ℕ} {Ω : PDE.VelocityRegion d} (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d) (b : PDE.TimeVectorField d) (c F : PDE.TimeScalarField d) (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω)) (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀)) (x xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)

private theorem matrix_rows_iff_reverseTimeGalerkin_rhs
     :
    (∀ i, (galerkinMassGram hΩ N *ᵥ xdot) i +
        (reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth N τ *ᵥ x) i =
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) ↔
      xdot =
        reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth N τ x +
        reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ := by
  let sharedTerm_f14ef75461 := ((Fin (Module.finrank ℝ (galerkinSpace hΩ N))))
  let M : Matrix sharedTerm_f14ef75461
      sharedTerm_f14ef75461 ℝ := galerkinMassGram hΩ N



  have hrhs := matrix_solution_eq_reverseTimeGalerkin_rhs r₀ r₁ h₀₁ hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth N τ x
  exact (matrix_coordinateEquation_iff M (reverseTimeGalerkinStiffness r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ) (reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ) x xdot ((M.isUnit_iff_isUnit_det).mp (isUnit_galerkinMassGram hΩ N))).trans
    (eq_iff_eq_of_eq_right xdot _
      _ hrhs)

private theorem reverseTimeGalerkin_coordinateEquation_iff_aux
     :
    (∀ i,
      inner ℝ
          (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))
          (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
        reverseTimeSpatialForm hΩ r₁ τ.1 a b c
          (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
          (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) ↔
      xdot =
        reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N τ
          x +
        reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ := (weak_rows_iff_matrix_rows r₀ r₁ h₀₁ hΩ hΩbounded a b c F haSmooth hbSmooth hcSmooth
    hFSmooth N τ x xdot).trans
    (matrix_rows_iff_reverseTimeGalerkin_rhs r₀ r₁ h₀₁ hΩ hΩbounded a b c F haSmooth hbSmooth
      hcSmooth hFSmooth N τ x xdot)

/-- The finite weak-coordinate equation is exactly the mass-inverted local linear ODE.
This theorem neither constructs nor solves a curve. -/
alias reverseTimeGalerkin_coordinateEquation_iff := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTimeGalerkin_coordinateEquation_iff_aux


end HypoellipticAleksandrov.Parabolic.Dirichlet
