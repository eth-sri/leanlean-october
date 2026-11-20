module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EvolutionInstance
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelEquation
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSmooth

/-! # Subtraction of weak solutions and homogeneous smooth representatives

Weak solutions with the same forcing have a homogeneous difference. Hörmander's
theorem then gives a smooth almost-everywhere representative. This module
keeps almost-everywhere regularity separate from the pointwise Green formula.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open Evolution Occupation SectionTwo

/-- The homogeneous weak difference has a smooth almost-everywhere representative. -/
theorem homogeneous_weak_smooth_representative
    {lam Lam : ℝ}
    (A : SmoothAutonomous lam Lam) {U : Set (EvolutionVec 1)} (hU : IsOpen U)
    {u : EvolutionVec 1 → ℝ}
    (hu : IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) U
      u (fun _ => 0)) :
    ∃ f : EvolutionVec 1 → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f U ∧
      u =ᵐ[volume.restrict U] f := by
  exact exists_smooth_representative_transported_source A.positive
    (evolutionCoefficient_smooth A) (evolutionCoefficient_bounds A)
    (identityDrift_smooth 1) zero_lt_one (identityDrift_bounds 1).2 hU hu
    contDiffOn_const

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) {U : Set (EvolutionVec 1)} (hU : IsOpen U)
  {u : EvolutionVec 1 → ℝ}
  (hu : IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) U u (fun _ => 0))
include lam Lam A hU hu

/-- A continuous homogeneous weak solution is pointwise smooth on its open domain. -/
theorem homogeneous_weak_contDiffOn (hc : ContinuousOn u U) :
    ContDiffOn ℝ (⊤ : ℕ∞) u U := by
  obtain ⟨f, hf, hae⟩ := homogeneous_weak_smooth_representative A hU hu
  exact hf.congr (fun x hx => (Measure.eqOn_open_of_ae_eq hae hU hc hf.continuousOn) hx)

/-- The smooth representative of a homogeneous weak solution solves the equation pointwise. -/
theorem homogeneous_weak_smooth_solution :
    ∃ f : EvolutionVec 1 → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f U ∧
      u =ᵐ[volume.restrict U] f ∧
      ∀ x ∈ U, transportedOperator (evolutionCoefficient A.a) (identityDrift 1) f x = 0 := by
  obtain ⟨f, hf, hae⟩ := homogeneous_weak_smooth_representative A hU hu
  have hw : IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) U
      f (fun _ => 0) := by
    refine ⟨hf.continuousOn.locallyIntegrableOn hU.measurableSet, ?_⟩
    intro ψ hψ hc hs
    refine (integral_congr_ae ?_).trans (hu.2 ψ hψ hc hs)
    filter_upwards [hae] with x hx
    rw [hx]
  exact ⟨f, hf, hae, duhamel_operator_eq_of_smooth_weak hU
    (evolutionCoefficient_smooth A) (evolutionCoefficient_symmetric A.a)
    (identityDrift_smooth 1) hf continuousOn_const hw⟩

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
