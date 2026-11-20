module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelSmoothTest
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelDense

/-! # Joint Borel measurability of the characterized terminal measures -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set
open scoped CompactlySupported

section EvolutionData

variable {n : ℕ} {lam Lam m L_b : ℝ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (data : TerminalEvolutionData lam Lam m L_b Ω γ B b)
include data

local notation "μT" => terminalMeasure data
local notation "κ" => terminalFiberKernel data

local notation "P₀" => terminalOperators data

/-- The terminal measure family is jointly Borel on the actual valid
query subtype, including the equal-time endpoint. -/
theorem measurable_terminalMeasure : Measurable (fun q : EvolutionQuery Ω γ => μT q) := by
  have hmass (q : EvolutionQuery Ω γ) :=
    (terminalMeasure_spec data q).1
  have (q : EvolutionQuery Ω γ) : IsFiniteMeasure (μT q) :=
    ⟨(hmass q).trans_lt ENNReal.one_lt_top⟩
  apply measurable_measure_family_of_smooth_tests μT hmass
  intro f hf
  exact measurable_integral_terminal_smooth data (compactProbeDatum f) hf

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov
