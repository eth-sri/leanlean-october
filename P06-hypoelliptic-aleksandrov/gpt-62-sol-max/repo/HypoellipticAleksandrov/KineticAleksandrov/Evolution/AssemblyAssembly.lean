module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.AssemblyKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.MarginalAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CompositionTraceRepresentation
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TranslationCovariance
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDomination
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.EvolutionConclusion

/-! # Clause-by-clause assembly of the terminal evolution

Every clause is assembled for the same integral operators and the same characterized
master measures. Composition and joint measurability remain explicit premises.
This module performs no analytic limit.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set MeasureTheory SectionTwo
open scoped ProbabilityTheory

section EvolutionData
variable {n : ℕ} {lam Lam m L_b : ℝ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (data : TerminalEvolutionData lam Lam m L_b Ω γ B b)
include data

local notation "μ" => terminalMeasure data
local notation "κ" => terminalFiberKernel data
local notation "P₀" => terminalOperators data

/-- Assemble every conjunct using one operator and one master-kernel witness.
The premises are the composition identity and the joint measurability of the master kernel;
the marginal package is consumed directly. -/
theorem construction_terminalEvolution_assembly
    (hComp : ∀ σ r τ hσr hrτ,
      P₀ σ τ (hσr.trans hrτ) = (P₀ σ r hσr).comp (P₀ r τ hrτ))
    (hKComp : ∀ σ r τ hσr hrτ,
      κ σ τ (hσr.trans hrτ) = κ r τ hrτ ∘ₖ κ σ r hσr)
    (hJoint : Measurable (fun q : EvolutionQuery Ω γ => μ q)) :
    SectionTwo.TerminalEvolutionResult Ω γ B b data.domain := by
  let K := constructionTerminalKernel data hJoint
  have hK (q : EvolutionQuery Ω γ) : K.master q = μ q := rfl
  have hFiber (σ τ : ℝ) (hστ : σ ≤ τ) :
      K.fiberKernel (measurableSet_of_isAdmissibleEvolutionDomain data.domain) σ τ hστ =
        κ σ τ hστ :=
    constructionTerminalKernel_fiber_eq data hJoint σ τ hστ
  have hComposition : K.HasComposition
      (measurableSet_of_isAdmissibleEvolutionDomain data.domain) := by
    intro σ r τ hσr hrτ
    rw [hFiber, hFiber, hFiber]
    exact hKComp σ r τ hσr hrτ
  have hBasic := terminalOperators_basic data
  refine ⟨P₀, K, ?_, hBasic.1, hBasic.2.1, hBasic.2.2.1, ?_, ?_,
    K.terminal_support, K.mass_le_one, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact terminalOperators_classical data
  · exact hComp
  · intro σ τ hστ p f
    rw [hFiber]
    exact terminalOperators_apply data σ τ hστ f p
  · exact K.jointlyMeasurable_apply
  · exact K.fiberKernel_mass_le_one (measurableSet_of_isAdmissibleEvolutionDomain data.domain)
  · intro σ
    rw [hFiber]
    exact hBasic.2.2.2 σ
  · exact hComposition
  · exact terminalKernel_translation_of_master_eq data K hK
  · exact terminalKernel_domain_domination_of_master_eq data K hK
  · exact terminalMarginal_properties_of_master_eq data K hK hComposition

end EvolutionData
end HypoellipticAleksandrov.KineticAleksandrov
