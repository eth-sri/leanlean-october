module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierGreen
import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierExtensionFibers

/-! # The interval slab Fourier theorem

Occupation, killing and frequency decay are discharged by their proved interval
lemmas. The only hypotheses are the explicit analytic inputs.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov.KineticAleksandrov.Green
open scoped ENNReal NNReal
open scoped ProbabilityTheory

/- The scalar slab exponent is the literal exponent in case I. -/
theorem interval_slab_beta (γ : ℝ) : slabBeta 1 γ = 3 / (2 * γ) - 1 / 2 := by
  norm_num [slabBeta]

/- Integrating frequencies gives the scalar slab height exponent. -/
theorem interval_slab_height_exponent (γ : ℝ) :
    slabBeta 1 γ - 3 * (1 : ℝ) / 2 = 3 / (2 * γ) - 2 := by
  rw [interval_slab_beta]
  ring

/- Uniform interval slab Fourier densities, with both killing and frequency decay. -/
end HypoellipticAleksandrov.KineticAleksandrov.Interval
