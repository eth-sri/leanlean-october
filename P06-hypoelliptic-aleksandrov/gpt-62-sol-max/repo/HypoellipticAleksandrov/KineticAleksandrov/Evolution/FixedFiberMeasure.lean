module

import Mathlib.Tactic.Linarith
public import Mathlib.Probability.Kernel.Defs
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.FixedFiberMeasureGeneral
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalMeasure

/-!
# The fixed-time fiber kernel

Companion paper, Proposition 2.1.  For fixed times `σ ≤ τ` the fiber measures
`p ↦ comap (↑) (μ (σ, τ, p))` of the terminal measures depend measurably on the source
state, BEFORE any composition or joint-Borel statement.  Measurability is proved from the
integrals against smooth probes: for a probe `F` the integral is the point value
`terminalValue`, which is continuous in `p` (a single classical solution evaluates all of them);
`FixedFiberMeasureGeneral` passes from probes to all measures.

* `measurable_terminalFiberMeasure`: measurable dependence of the fiber measure.
* `terminalFiberKernel`: the kernel `κ σ τ hστ` with `κ σ τ hστ p = comap (↑) (μ q)`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set
open scoped CompactlySupported ENNReal ProbabilityTheory

section EvolutionData

variable {n : ℕ} {lam Lam m L_b : ℝ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (data : TerminalEvolutionData lam Lam m L_b Ω γ B b)
include data

local notation "S" => terminalValue data.exists_solution
local notation "ℓ_" => terminalFunctional data
local notation "ν_" => terminalFiberRieszMeasure data
local notation "μ" => terminalMeasure data

section
variable (σ τ : ℝ) (hστ : σ ≤ τ)
include hστ

/-- For fixed times `σ ≤ τ` the fiber measure of the terminal measure depends
measurably on the source state. -/
theorem measurable_terminalFiberMeasure :
    Measurable (fun p : EvolutionState Ω γ σ =>
      Measure.comap ((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n)
        (μ (evolutionQueryOfState Ω γ σ τ hστ p))) := by
  have hΩo := isOpen_of_isAdmissibleEvolutionDomain data.domain
  have hfun : (fun p : EvolutionState Ω γ σ =>
      Measure.comap ((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n)
        (μ (evolutionQueryOfState Ω γ σ τ hστ p))) = fun p => ν_ σ τ hστ p := by
    funext p
    exact comap_terminalMeasure_eq_rieszMeasure data
      (evolutionQueryOfState Ω γ σ τ hστ p)
  rw [hfun]
  have := locallyCompactSpace_evolutionState (γ := γ) (τ := τ) hΩo
  have hfin : ∀ p, IsFiniteMeasure (ν_ σ τ hστ p) := fun p =>
    isFiniteMeasure_terminalFiberRieszMeasure data σ τ hστ p
  have hmass : ∀ p, ν_ σ τ hστ p univ ≤ 1 := fun p =>
    terminalFiberRieszMeasure_univ_le_one data σ τ hστ p
  refine measurable_of_integral_measurable (fun p => ν_ σ τ hστ p) ?_
  refine measurable_integral_of_dense (terminalProbeCcLinear (Ω := Ω) (γ := γ) (τ := τ))
    (fun p => ν_ σ τ hστ p) hmass
    (fun f ε hε => exists_terminalProbe_close hΩo f ε hε) (fun F => ?_)
  have hint : (fun p : EvolutionState Ω γ σ => ∫ x, terminalProbeCcLinear F x ∂(ν_ σ τ hστ p)) =
      fun p => S σ τ hστ p (terminalProbeDatum F) (terminalProbeDatum_isSmoothCompact F) := by
    funext p
    rw [integral_terminalFiberRieszMeasure data σ τ hστ p]
    exact (terminalFunctional_spec data σ τ hστ p).2
      (terminalProbeDatum F) (terminalProbeDatum_isSmoothCompact F)
      (terminalProbeCcLinear F) fun x => rfl
  rw [hint]
  exact (continuous_terminalValue_source data σ τ hστ
    (terminalProbeDatum F) (terminalProbeDatum_isSmoothCompact F)).measurable

/-- The fixed-time fiber kernel `κ σ τ hστ`, defined literally as the measurable
fiber-measure function of `measurable_terminalFiberMeasure`. -/
def terminalFiberKernel :
    ProbabilityTheory.Kernel (EvolutionState Ω γ σ) (EvolutionState Ω γ τ) :=
  ⟨fun p : EvolutionState Ω γ σ =>
      Measure.comap ((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n)
        (μ (evolutionQueryOfState Ω γ σ τ hστ p)),
    measurable_terminalFiberMeasure data σ τ hστ⟩

end

local notation "κ" => terminalFiberKernel data

section
variable (σ τ : ℝ) (hστ : σ ≤ τ)

/-- The value of the fiber kernel at a source state. -/
theorem terminalFiberKernel_apply (p : EvolutionState Ω γ σ) :
    κ σ τ hστ p =
      Measure.comap ((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n)
        (μ (evolutionQueryOfState Ω γ σ τ hστ p)) :=
  rfl

/-- The fiber kernel has mass at most one. -/
theorem terminalFiberKernel_univ_le_one (p : EvolutionState Ω γ σ) :
    κ σ τ hστ p univ ≤ 1 := by
  have hU := measurableSet_evolutionStateSet_of_isOpen (γ := γ) (τ := τ)
    (isOpen_of_isAdmissibleEvolutionDomain data.domain)
  rw [terminalFiberKernel_apply, (MeasurableEmbedding.subtype_coe hU).comap_apply,
    image_univ, Subtype.range_coe]
  exact (measure_mono (subset_univ _)).trans
    (terminalMeasure_spec data
      (evolutionQueryOfState Ω γ σ τ hστ p)).1

/-- The fiber kernel is a finite kernel. -/
theorem isFiniteKernel_terminalFiberKernel :
    ProbabilityTheory.IsFiniteKernel (κ σ τ hστ) :=
  ⟨⟨1, ENNReal.one_lt_top, fun p =>
    terminalFiberKernel_univ_le_one data σ τ hστ p⟩⟩

end

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov
