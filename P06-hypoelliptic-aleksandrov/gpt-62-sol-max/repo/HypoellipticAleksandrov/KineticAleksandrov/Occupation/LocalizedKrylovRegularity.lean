module

public import HypoellipticAleksandrov.KineticAleksandrov.ClassicalInputs
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovGeometry
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletComparison
public import HypoellipticAleksandrov.Parabolic.AffineScalarCalculus
public import HypoellipticAleksandrov.Parabolic.ScalarJetPointGermCongruence

/-!
# Closure regularity and nonnegativity of the localized source solution

For the classical solution `V` of `∂_r V + B : D_v² V = -F` on `(α, 1) × B_R(v_*)`
with zero terminal and lateral data (proof of the companion paper, Proposition 4.2), the weak
maximum principle proves `V ≥ 0`. 
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology MatrixOrder Matrix.Norms.Elementwise

variable {d : ℕ}

section Solution

variable {lam Lam : ℝ} {B : CoefficientField d} {F : TimeVelocity d → ℝ}
  {α : ℝ} {vStar : PDE.Vec d} {R : ℝ}

/-- Positive lower Loewner bound makes the coefficient positive semidefinite. -/
theorem posSemidef_of_lower_loewner (hlam : 0 < lam)
    (hlow : ∀ r v, lam • (1 : PDE.Mat d) ≤ B r v) (r : ℝ) (v : PDE.Vec d) :
    (B r v).PosSemidef := by
  have h0 : (0 : PDE.Mat d) ≤ lam • (1 : PDE.Mat d) := by
    rw [Matrix.nonneg_iff_posSemidef]
    exact Matrix.PosSemidef.one.smul hlam.le
  exact Matrix.nonneg_iff_posSemidef.mp (h0.trans (hlow r v))

/-- Nonnegativity of the localized source solution (weak maximum principle). -/
theorem classical_solution_nonneg (hlam : 0 < lam) (hF0 : ∀ z, 0 ≤ F z)
    (hα1 : α < 1) (hR : 0 < R)
    (hsmooth : IsSmoothCoefficient B) (hlow : ∀ r v, lam • (1 : PDE.Mat d) ≤ B r v)
    {V : TimeVelocity d → ℝ}
    (hV : IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall vStar R) B
      (fun _ _ => 0) (fun _ _ => 0) (fun r v => -F (r, v)) (fun _ => 0) (fun _ => 0) V) :
    ∀ z ∈ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R), 0 ≤ V z := by
  obtain ⟨hcont, hC12, hpde, hterm, hlat⟩ := hV
  have hw := scalar_le_zero_on_closedCylinder_of_zeroOrderOperator_nonneg
    (PDE.isOpen_euclideanBall vStar R) (isBounded_euclideanBall vStar hR) hα1 B
    (fun _ _ => 0) (fun _ _ => 0) hsmooth.continuous continuous_const
    (posSemidef_of_lower_loewner hlam hlow) (fun _ _ => le_rfl)
    (fun z => -1 * V z + 0)
    ((continuousOn_const.mul hcont).add continuousOn_const)
    (IsScalarC12On.const_mul_add_const hC12 (-1) 0)
    (by
      intro z hz
      rw [scalarParabolicZeroOrderOperator_const_mul_add_const, hpde z hz]
      simpa using hF0 z)
    (by
      rintro ⟨r, y⟩ hz
      rw [mem_scalarParabolicTerminalFace_iff] at hz
      obtain ⟨rfl, hy⟩ := hz
      have h0 : V (1, y) = 0 := hterm y hy
      show -1 * V (1, y) + 0 ≤ 0
      rw [h0]
      norm_num)
    (by
      intro z hz
      have h0 : V z = 0 := hlat z hz
      show -1 * V z + 0 ≤ 0
      rw [h0]
      norm_num)
  intro z hz
  have := hw z hz
  linarith

end Solution

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
