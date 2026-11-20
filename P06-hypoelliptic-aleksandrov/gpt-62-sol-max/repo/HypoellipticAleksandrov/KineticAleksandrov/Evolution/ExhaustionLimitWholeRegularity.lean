module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitWholeWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitWholeGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitClassical
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyParameters
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Classical regularity of the actual whole-space ball exhaustion -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov Set Filter MeasureTheory
open Evolution
open scoped Topology MatrixOrder

section Data

variable {n : ℕ} {lam Lam Lb : ℝ} {B : FullKineticCoefficient n}
variable {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam)
variable (hB : HasEverywhereLoewnerBounds lam Lam B) (hb : HasEuclideanLipschitzDrift Lb b)
variable {ε τ α S0 C : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
variable (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
variable (r : ℕ → ℝ) (hrlim : Tendsto r atTop atTop) (v : ℕ → KineticPoint n → ℝ)
variable (hv : ∀ j, IsClassicalViscousTerminalSolution (PDE.euclideanBall 0 (r j))
  (fun _ => 0) B b ε τ F (v j))
variable (hBs : IsSmoothFullKineticCoefficient B) (hBsym : IsSymmetricFullKineticCoefficient B)
variable (hbs : IsSmoothDrift b)
include hBs hBsym hbs
include hlam hB hb hε hε1 hC hFC hrlim hv

/-- Relative to the explicit Hörmander input, the actual whole-space ball limit
is smooth and satisfies the pointwise viscous equation on each bounded inner cylinder. -/
theorem classical_wholeSpace_ball_limit :
    ContDiffOn ℝ (⊤ : ℕ∞) ((fun p => limUnder atTop (fun j => v j p)) ∘
      evolutionHomeomorph n) (evolutionHomeomorph n ⁻¹' wholeSpaceInnerCylinder α τ S0) ∧
    ∀ p ∈ wholeSpaceInnerCylinder α τ S0,
      viscousTransportedOperator B b ε (fun p => limUnder atTop (fun j => v j p)) p = 0 := by
  have hcont := (tendstoUniformlyOn_wholeSpace_ball_solutions (α := α) (S0 := S0)
    hlam hB hb hε.le hε1 hC F hFC r hrlim v hv).2.1.mono (wholeSpaceInnerCylinder_subset_closed α τ S0)
  exact classical_kinetic_of_continuous_weak hlam hB hBs hBsym hbs hε
    (isOpen_wholeSpaceInnerCylinder α τ S0) hcont
    (weakRegularized_wholeSpace_ball_limit hlam hB hb hε hε1 hC F hFC r hrlim v hv hBs hBsym hbs)

end Data

end HypoellipticAleksandrov.KineticAleksandrov
