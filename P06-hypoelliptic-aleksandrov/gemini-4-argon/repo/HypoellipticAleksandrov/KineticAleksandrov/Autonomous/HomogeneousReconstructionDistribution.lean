module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionClassicalWeak
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceLimitsQuadratic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceWeakGreenSigned
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EvolutionInstance
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeak

/-! # The actual homogeneous reconstruction in distributions

Both weak equations have the same literal forcing on the finite strip. Their
difference therefore has a homogeneous smooth representative by
Hörmander's theorem. Almost-everywhere equality is not asserted to be pointwise equality.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Evolution SectionTwo MeasureTheory Set
open Filter TheoremA
open scoped Topology

private theorem source_congr {lam Lam } (A : SmoothAutonomous lam Lam)
    {U } (hU : IsOpen U) {u g f }
    (hu : IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) U u g)
    (hg : EqOn g f U) :
    IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) U u f := by
  refine ⟨hu.1, ?_⟩
  intro ψ hψ hc hs
  refine (hu.2 ψ hψ hc hs).trans (setIntegral_congr_fun hU.measurableSet ?_)
  intro x hx
  change g x * ψ x = f x * ψ x
  rw [hg hx]

theorem exists_reconstruction_smooth_ae
    (hH : HormanderHypoellipticityStatement) {lam Lam } (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (sMinus T : ℝ) (phi : Point → ℝ)
    (hphi : IsKineticC112On phi (reconstructionStrip H sMinus T))
    (hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H sMinus T,
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    ∃ (g : BoundedBorel Point) (f : EvolutionVec 1 → ℝ),
      (∀ p ∈ reconstructionStrip H sMinus T, g p = -forwardScalarOperator A.a phi p) ∧
      (∀ p ∉ reconstructionStrip H sMinus T, g p = 0) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) f
        (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T) ∧
      (stripReconstructionCandidate H E.2 T phi g ∘ reconstructionPhysicalPoint)
        =ᵐ[volume.restrict
          (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T)] f ∧
      ∀ x ∈ reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T,
        transportedOperator (evolutionCoefficient A.a) (identityDrift 1) f x = 0 := by
  obtain ⟨g, hg, hg0⟩ := exists_bounded_reconstruction_source A H sMinus T phi hphi hb
  have _h_inl_7 : IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T) (stripReconstructionCandidate H E.2 T phi g ∘ reconstructionPhysicalPoint) (fun _ => 0) := by
    let U := reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T
    have hU : IsOpen U := (isOpen_reconstructionStrip H sMinus T).preimage
      continuous_reconstructionPhysicalPoint
    have htest := reconstruction_test_isWeakTransportedSolution A
      (isOpen_reconstructionStrip H sMinus T) hphi
    have _h_xinl_0 : IsKineticWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) (evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T) (stripSourcePotential H E.2 T g ∘ sectionTwoPoint) (fun p => -nativeStripSource g p) := by
      have heq : (stripSourcePotential H E.2 T g ∘ sectionTwoPoint) =
          duhamelPotential E.2 T (nativeStripSource g) := by
        funext p
        change duhamelPotential E.2 T (nativeStripSource g)
          (sectionTwoPoint (sectionTwoPoint p)) = _
        rw [sectionTwoPoint_involutive p]
      rw [heq]
      let g := (nativeStripSource g)
      obtain ⟨C, hC, hg⟩ := g.exists_bound
      exact duhamel_bounded_isKineticWeakTransportedSolution (intervalDomain_admissible H)
        (intervalDomain_measurable H) continuous_const (evolutionCoefficient A.a)
        (identityDrift 1) E.1 E.2 hE (evolutionCoefficient_smooth A)
        (evolutionCoefficient_symmetric A.a) (identityDrift_smooth 1)
        g g.measurable C hC hg T
    have hw := (isWeakTransportedSolution_comp_iff (evolutionCoefficient A.a)
      (identityDrift 1) _ _ _).mpr _h_xinl_0
    have hsub : U ⊆ evolutionHomeomorph 1 ⁻¹'
        evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T := by
      intro x hx
      refine ⟨hx.2.1, ?_⟩
      change diffusedCoord 1 x ∈ movingDomain (intervalDomain H) (fun _ => 0) _
      rw [movingDomain, PDE.mem_translateSet_iff_sub_mem, sub_zero, intervalDomain,
        PDE.mem_oneDimensionalAxisBox_iff]
      exact hx.2.2
    have hwr := weak_solution_restrict A hsub hw
    have hsource : EqOn
        ((fun p => -nativeStripSource g p) ∘ evolutionHomeomorph 1)
        (forwardScalarOperator A.a phi ∘ reconstructionPhysicalPoint) U := by
      intro x hx
      change -g (reconstructionPhysicalPoint x) = _
      rw [hg _ hx, neg_neg]
      rfl
    exact weak_same_source_sub A htest (source_congr A hU hwr hsource)
  obtain ⟨f, hf, hae, heq⟩ := homogeneous_weak_smooth_solution hH hlam A
    ((isOpen_reconstructionStrip H sMinus T).preimage continuous_reconstructionPhysicalPoint)
    _h_inl_7
  exact ⟨g, f, hg, hg0, hf, hae, heq⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
