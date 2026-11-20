module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BracketSquares
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSliceWeak

/-! # Integration against the full kinetic adjoint for smooth interior functions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open Evolution

variable {d : ℕ}

/-- Full kinetic integration by parts, with all jets discharged by interior smoothness. -/
theorem integral_transportedAdjoint_contDiffOn {U : Set (EvolutionVec d)} (hU : IsOpen U)
    {B : FullKineticCoefficient d} (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B)
    {b : PDE.Vec d → PDE.Vec d} (hb : IsSmoothDrift b)
    {u : EvolutionVec d → ℝ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (ψ : EvolutionVec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    (∫ x in U, u x * transportedAdjoint B b ψ x) =
      ∫ x in U, transportedOperator B b u x * ψ x := by
  simpa only [regularizedAdjoint, regularizedOperator, zero_mul, add_zero] using
    integral_regularizedAdjoint_contDiffOn_two hU hB hBs hb 0 (hu.of_le (by simp)) ψ hψ hc hs

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
