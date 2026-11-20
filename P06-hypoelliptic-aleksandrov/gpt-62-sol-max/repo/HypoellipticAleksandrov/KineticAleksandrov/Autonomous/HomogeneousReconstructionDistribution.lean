module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.WeakCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionClassicalWeak

/-! # The actual homogeneous reconstruction in distributions

Both weak equations have the same literal forcing on the finite strip. Their
difference therefore has a homogeneous smooth representative by
Hörmander's theorem. Almost-everywhere equality is not asserted to be pointwise equality.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Evolution SectionTwo MeasureTheory Set

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
  (hE : IsStripEvolution A H E) (sMinus T : ℝ) (phi : Point → ℝ)
  (hphi : IsKineticC112On phi (reconstructionStrip H sMinus T))
include hE hphi

private theorem candidate_weak
    (g : BoundedBorel Point)
    (hg : ∀ p ∈ reconstructionStrip H sMinus T,
      g p = -forwardScalarOperator A.a phi p) :
    IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1)
      (packedPhysicalPoint ⁻¹' reconstructionStrip H sMinus T)
      (stripReconstructionCandidate H E.2 T phi g ∘ packedPhysicalPoint)
      (fun _ => 0) := by
  let U := packedPhysicalPoint ⁻¹' reconstructionStrip H sMinus T
  have hU : IsOpen U := (isOpen_reconstructionStrip H sMinus T).preimage
    continuous_packedPhysicalPoint
  have htest := reconstruction_test_isWeakTransportedSolution A
    (isOpen_reconstructionStrip H sMinus T) hphi
  have hw := (isWeakTransportedSolution_comp_iff (evolutionCoefficient A.a)
    (identityDrift 1) _ _ _).mpr (stripSourcePotential_weak A H E hE T g)
  have hsub : U ⊆ evolutionHomeomorph 1 ⁻¹'
      evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T := by
    intro x hx
    refine ⟨hx.2.1, ?_⟩
    change diffusedCoord 1 x ∈ movingDomain (intervalDomain H) (fun _ => 0) _
    rw [movingDomain, PDE.mem_translateSet_iff_sub_mem, sub_zero, intervalDomain,
      PDE.mem_oneDimensionalAxisBox_iff]
    exact hx.2.2
  have hwr := hw.mono hsub
  have hsource : EqOn
      ((fun p => -nativeStripSource g p) ∘ evolutionHomeomorph 1)
      (forwardScalarOperator A.a phi ∘ packedPhysicalPoint) U := by
    intro x hx
    change -g (packedPhysicalPoint x) = _
    rw [hg _ hx, neg_neg]
    rfl
  have hws := hwr.congr_source hU.measurableSet hsource
  exact htest.sub_same_source hws (evolutionCoefficient_smooth A) (identityDrift_smooth 1)

/-- The literal reconstruction candidate has a homogeneous smooth AE representative.
The bounded Borel source is constructed from the test, rather than assumed. -/
theorem exists_reconstruction_smooth_ae
    (hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H sMinus T,
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    ∃ (g : BoundedBorel Point) (f : EvolutionVec 1 → ℝ),
      (∀ p ∈ reconstructionStrip H sMinus T, g p = -forwardScalarOperator A.a phi p) ∧
      (∀ p ∉ reconstructionStrip H sMinus T, g p = 0) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) f
        (packedPhysicalPoint ⁻¹' reconstructionStrip H sMinus T) ∧
      (stripReconstructionCandidate H E.2 T phi g ∘ packedPhysicalPoint)
        =ᵐ[volume.restrict
          (packedPhysicalPoint ⁻¹' reconstructionStrip H sMinus T)] f ∧
      ∀ x ∈ packedPhysicalPoint ⁻¹' reconstructionStrip H sMinus T,
        transportedOperator (evolutionCoefficient A.a) (identityDrift 1) f x = 0 := by
  obtain ⟨g, hg, hg0⟩ := exists_bounded_reconstruction_source A H sMinus T phi hphi hb
  obtain ⟨f, hf, hae, heq⟩ := homogeneous_weak_smooth_solution A
    ((isOpen_reconstructionStrip H sMinus T).preimage continuous_packedPhysicalPoint)
    (candidate_weak A H E hE sMinus T phi hphi g hg)
  exact ⟨g, f, hg, hg0, hf, hae, heq⟩

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
