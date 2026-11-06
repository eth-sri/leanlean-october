module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalOrder
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitClassical
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeOperator
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Smooth interior representatives of vanishing-viscosity sequences -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov Set Filter MeasureTheory Evolution
open scoped Topology MatrixOrder

/- A smooth representative of the zero-source weak equation satisfies the equation
pointwise in the original kinetic coordinates. -/
theorem transportedForwardOperator_eq_zero_of_smooth_weak {n B} (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B) {b }
    (hb : IsSmoothDrift b) {U } (hU : IsOpen U)
    {u V }
    (hu : IsKineticWeakTransportedSolution B b U u (fun _ => 0))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) (V ∘ evolutionHomeomorph n)
      (evolutionHomeomorph n ⁻¹' U)) (hrep : u =ᵐ[volume.restrict U] V) :
    ∀ p ∈ U, transportedForwardOperator B b V p = 0 := by
  have hw : IsKineticWeakTransportedSolution B b U V (fun _ => 0) := by
    refine ⟨(locallyIntegrableOn_congr hrep).mp hu.1, ?_⟩
    intro ψ hψ hc hs
    have he := hu.2 ψ hψ hc hs
    rw [← he]
    apply integral_congr_ae
    filter_upwards [hrep] with p hp
    rw [hp]
  have hp := (isWeakTransportedSolution_comp_iff B b U V (fun _ => 0)).mpr hw
  have hP := (evolutionHomeomorph n).continuous.isOpen_preimage U hU
  have hreg : IsWeakRegularizedSolution B b 0 (evolutionHomeomorph n ⁻¹' U)
      (V ∘ evolutionHomeomorph n) (fun _ => 0) := by
    simpa only [IsWeakRegularizedSolution, IsWeakTransportedSolution,
      IsDistributionalSolution, regularizedAdjoint, transportedAdjoint,
      Function.comp_def, zero_mul, add_zero, sub_zero] using hp
  have he := regularizedOperator_eq_zero_of_smooth_weak hP hB hBs hb 0 hV hreg
  intro p hpin
  let x := (evolutionHomeomorph n).symm p
  have hx : x ∈ evolutionHomeomorph n ⁻¹' U := by simpa [x] using hpin
  have heq := he x hx
  rw [regularizedOperator_comp 0 ((hV.contDiffAt (hP.mem_nhds hx)).of_le (by simp)),
    zero_mul, add_zero] at heq
  simpa [x] using heq

/- Interior compactness retains all integrable tests as well as a smooth representative.
Boundary extension is handled separately by uniform trace estimates. -/
end HypoellipticAleksandrov.KineticAleksandrov
