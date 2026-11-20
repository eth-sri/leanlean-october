module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalIntegralOperator

/-! # The master kernel from the characterized terminal measures

The only hypothesis here is the joint measurability of the terminal measures.
Support and mass come from the construction of the terminal measures; the fixed-time fibers
are the same kernels as in `FixedFiberMeasure`.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov Set MeasureTheory
open scoped ProbabilityTheory

section EvolutionData

variable {n : ℕ} {lam Lam m L_b : ℝ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (data : TerminalEvolutionData lam Lam m L_b Ω γ B b)
include data

local notation "μ" => terminalMeasure data
local notation "κ" => terminalFiberKernel data

/-- The ambient master is literally the family of terminal measures, with joint measurability
supplied explicitly. -/
def constructionTerminalKernel (hJoint : Measurable (fun q : EvolutionQuery Ω γ => μ q)) :
    MovingFiberKernel Ω γ where
  master := ⟨μ, hJoint⟩
  terminal_support q := (terminalMeasure_spec data q).2.1
  mass_le_one q := (terminalMeasure_spec data q).1

/-- The fiber identification follows from the identical map/comap constructions. -/
theorem constructionTerminalKernel_fiber_eq
    (hJoint : Measurable (fun q : EvolutionQuery Ω γ => μ q))
    (σ τ : ℝ) (hστ : σ ≤ τ) :
    (constructionTerminalKernel data hJoint).fiberKernel
      (measurableSet_of_isAdmissibleEvolutionDomain data.domain) σ τ hστ = κ σ τ hστ := by
  rfl

end EvolutionData
end HypoellipticAleksandrov.KineticAleksandrov
