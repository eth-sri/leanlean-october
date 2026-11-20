module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PhysicalJets
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundarySolutionRegularity

/-! # Actual weak and smooth regularity of source-class homogeneous physical solutions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic Evolution SectionTwo TheoremA Occupation

section
variable {d : ℕ} {lam Lam : ℝ} (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  {D : Set (KineticPoint d)} (hD : IsOpen D) (u : KineticPoint d → ℝ) (hu : IsKineticC112On u D)
  (he : ∀ P ∈ D, forwardKineticOperator (ofTimeVelocityCoefficient B) u P = 0)
include lam Lam B hB hD hu he

/-- A physical C112 homogeneous solution satisfies the actual packed weak equation. -/
theorem mass_classical_homogeneous_weak :
    IsWeakTransportedSolution (zIndependentCoefficient B) (identityDrift d)
      (packedPhysicalPoint ⁻¹' D) (u ∘ packedPhysicalPoint) (fun _ => 0) := by
  obtain ⟨hsm, hsym, _⟩ := sectionTwoCoefficient_fullBounds lam Lam B hB
  exact (packedPhysicalPoint_classical_weak (zIndependentCoefficient B) hsm hsym hD hu).congr_source
    (hD.preimage continuous_packedPhysicalPoint).measurableSet fun _ hx => he _ hx

/-- Hörmander upgrades the exact C112 homogeneous class without a second position premise. -/
theorem mass_classical_homogeneous_smooth :
    ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' D) := by
  have hw := mass_classical_homogeneous_weak B hB hD u hu he
  have hset : packedPhysicalPoint ⁻¹' D =
      evolutionHomeomorph d ⁻¹' (sectionTwoPoint '' D) := by
    ext x
    constructor
    · intro hx
      exact ⟨packedPhysicalPoint x, hx, rfl⟩
    · rintro ⟨P, hP, hEq⟩
      have hp : packedPhysicalPoint x = P := congrArg sectionTwoPoint hEq.symm
      change packedPhysicalPoint x ∈ D
      rw [hp]
      exact hP
  have hc : ContinuousOn (u ∘ packedPhysicalPoint) (packedPhysicalPoint ⁻¹' D) :=
    hu.continuousOn.comp continuous_packedPhysicalPoint.continuousOn (fun _ hx => hx)
  obtain ⟨f, hf, hae⟩ := exists_smooth_representative_transported_source hB.1
    (sectionTwoCoefficient_fullBounds lam Lam B hB).1
    (sectionTwoCoefficient_fullBounds lam Lam B hB).2.2
    (identityDrift_smooth d) zero_lt_one (identityDrift_bounds d).2
    (hD.preimage continuous_packedPhysicalPoint) hw contDiffOn_const
  have hEq := Measure.eqOn_open_of_ae_eq hae (hD.preimage continuous_packedPhysicalPoint)
    hc hf.continuousOn
  have hs := hf.congr (fun x hx => hEq hx)
  apply boundary_native_smooth_to_physical D u
  rw [← hset]
  exact hs

end

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
