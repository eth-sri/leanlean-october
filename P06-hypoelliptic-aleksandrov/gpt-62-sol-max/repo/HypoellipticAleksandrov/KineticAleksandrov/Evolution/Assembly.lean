module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.AssemblyAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalExistence
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CompositionKernel
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorel

/-! # Construction of the terminal evolution -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set MeasureTheory
open scoped ProbabilityTheory

/-- The terminal evolution, obtained from classical existence, the composition laws,
and joint measurability of the terminal measures. -/
theorem exists_terminalEvolution_of_classical : SectionTwo.TerminalEvolutionConclusion := by
  intro n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive
  let data : TerminalEvolutionData lam Lam m L_b Ω γ B b :=
    ⟨hn, hlam, hlamLam, hm, hmLb, hΩ, hγ, hB_smooth, hB_symm, hB_ell,
      hb_smooth, hb_lipschitz, hb_coercive,
      classicalTerminalExistence_holds n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
        hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive⟩
  exact construction_terminalEvolution_assembly data
    (terminalOperators_comp data) (terminalFiberKernel_comp data) (measurable_terminalMeasure data)

end HypoellipticAleksandrov.KineticAleksandrov
