module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CompositionTrace
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! # Kernel composition and composition on bounded Borel data

The composed measure is characterized by the terminal measures, using composition on smooth compact
probes. All equalities hold at every source state.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set
open scoped ProbabilityTheory ENNReal

section EvolutionData

variable {n : ℕ} {lam Lam m L_b : ℝ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (data : TerminalEvolutionData lam Lam m L_b Ω γ B b)
include data

local notation "μ" => terminalMeasure data
local notation "κ" => terminalFiberKernel data

local notation "P₀" => terminalOperators data

section
variable (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ)

/-- The terminal fiber kernels satisfy pointwise composition. -/
theorem terminalFiberKernel_comp :
    κ σ τ (hσr.trans hrτ) = κ r τ hrτ ∘ₖ κ σ r hσr := by
  have := isFiniteKernel_terminalFiberKernel data σ r hσr
  have := isFiniteKernel_terminalFiberKernel data r τ hrτ
  apply ProbabilityTheory.Kernel.ext
  intro p
  let q := evolutionQueryOfState Ω γ σ τ (hσr.trans hrτ) p
  let ν := (κ r τ hrτ ∘ₖ κ σ r hσr) p
  let νa := ν.map ((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n)
  have hmass : νa univ ≤ 1 := by
    rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ]
    change (κ r τ hrτ ∘ₖ κ σ r hσr) p univ ≤ 1
    rw [ProbabilityTheory.Kernel.comp_apply' _ _ _ MeasurableSet.univ]
    calc
      (∫⁻ x, κ r τ hrτ x univ ∂(κ σ r hσr p)) ≤ ∫⁻ _x, 1 ∂(κ σ r hσr p) :=
        lintegral_mono fun x => terminalFiberKernel_univ_le_one data r τ hrτ x
      _ = κ σ r hσr p univ := by rw [lintegral_const, one_mul]
      _ ≤ 1 := terminalFiberKernel_univ_le_one data σ r hσr p
  have hsupp :=
    map_subtype_val_restrict (measurableSet_evolutionStateSet_of_isOpen
      (isOpen_of_isAdmissibleEvolutionDomain data.domain)) ν
  have hint (F : BoundedBorel (EvolutionAmbientState n))
      (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
      (∫ x, F x ∂νa) = terminalValue data.exists_solution
        σ τ (hσr.trans hrτ) p F hF := by
    rw [(MeasurableEmbedding.subtype_coe
      (measurableSet_evolutionStateSet_of_isOpen
        (isOpen_of_isAdmissibleEvolutionDomain data.domain))).integral_map]
    change (∫ x, terminalStateDatum F x ∂((κ r τ hrτ ∘ₖ κ σ r hσr) p)) = _
    rw [ProbabilityTheory.Kernel.integral_comp (integrable_boundedBorel (terminalStateDatum F) _)]
    simp_rw [← terminalOperators_apply]
    have hc := congrArg (fun f : BoundedBorel (EvolutionState Ω γ σ) => f p)
      (terminalOperators_comp_smooth data
        σ r τ hσr hrτ F hF)
    rw [← hc]
    exact terminalOperators_apply_smooth data
      σ τ (hσr.trans hrτ) p F hF
  have heq := terminalMeasure_eq_of_spec data
    q νa hmass hsupp hint
  have hm := congrArg (Measure.comap ((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n)) heq
  rw [(MeasurableEmbedding.subtype_coe
    (measurableSet_evolutionStateSet_of_isOpen
      (isOpen_of_isAdmissibleEvolutionDomain data.domain))).comap_map] at hm
  exact hm.symm

/-- The terminal operators compose on every bounded Borel datum. -/
theorem terminalOperators_comp :
    P₀ σ τ (hσr.trans hrτ) = (P₀ σ r hσr).comp (P₀ r τ hrτ) := by
  have := isFiniteKernel_terminalFiberKernel data σ r hσr
  have := isFiniteKernel_terminalFiberKernel data r τ hrτ
  apply LinearMap.ext
  intro f
  apply BoundedBorel.ext
  intro p
  rw [terminalOperators_apply, terminalFiberKernel_comp data σ r τ hσr hrτ,
    ProbabilityTheory.Kernel.integral_comp (integrable_boundedBorel f _)]
  change _ = P₀ σ r hσr (P₀ r τ hrτ f) p
  simp [terminalOperators_apply]

end

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov
