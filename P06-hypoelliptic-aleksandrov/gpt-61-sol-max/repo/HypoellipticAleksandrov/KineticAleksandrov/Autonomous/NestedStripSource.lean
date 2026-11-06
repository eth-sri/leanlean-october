module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripCoordinates
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionCanonical
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelTheorem
public import PDEFoundation.Calculus.RegularityOrder


/-! # Actual compact physical source potentials for the nested-strip identity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set Parabolic
open SectionTwo TheoremA Evolution

variable (f : exitProbeSubmodule)



/-- The native source has genuine global C-infinity regularity in product coordinates. -/
theorem nested_native_probe_raw_smooth  :
    ContDiff ℝ PDE.smoothOrder (rawLift (exitProbePhysical f ∘ sectionTwoPoint)) := by
  have hs := f.2.1.comp (evolutionProdCLE 1).symm.contDiff
  assumption

variable (H : Interval)

variable (T : ℝ)

/-- Native past membership is exactly physical time and physical velocity membership. -/
theorem nested_mem_native_past   (p : Point) :
    sectionTwoPoint p ∈ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T ↔
      p.time < T ∧ p.velocity 0 ∈ H.carrier := by
  simp only [evolutionPastOpenCylinder, mem_ofPred_eq, mem_movingDomain_iff,
    sub_zero, intervalDomain,
    PDE.mem_oneDimensionalAxisBox_iff, PDE.vecOneCoordinate, Interval.carrier, sectionTwoPoint]

/-- Compact interior physical sources satisfy the hypotheses of the actual native Duhamel
  theorem. -/
theorem nested_native_probe_source_support   (f : exitProbeSubmodule)
    (hs : tsupport (exitProbePhysical f) ⊆ {p | p.time < T ∧ p.velocity 0 ∈ H.carrier}) :
    tsupport (exitProbePhysical f ∘ sectionTwoPoint) ⊆
      evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T := by
  intro p hp

  have heq := nested_mem_native_past H T (sectionTwoPoint p)
  rw [sectionTwoPoint_involutive] at heq
  exact heq.mpr (hs ((tsupport_comp_subset_preimage _ (continuous_sectionTwoPoint 1)) hp))

/-- The physical compact-source potential is the actual native Duhamel integral after exchange. -/
def nestedSourcePotential  (E : StripEvolution H) (T : ℝ)
    (f : exitProbeSubmodule) : Point → ℝ :=
  duhamelPotential E.2 T (exitProbePhysical f ∘ sectionTwoPoint) ∘ sectionTwoPoint

/-- The compact-source potential has boundedness, physical C112 regularity and its true source
operator; none of those analytic conclusions is an input premise. -/
theorem nestedSourcePotential_regular_source
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (f : exitProbeSubmodule)
    (hfn : ∀ p, 0 ≤ exitProbePhysical f p)
    (hs : tsupport (exitProbePhysical f) ⊆ {p | p.time < T ∧ p.velocity 0 ∈ H.carrier}) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ p, |nestedSourcePotential H E T f p| ≤ C) ∧
      IsKineticC112On (nestedSourcePotential H E T f)
        {p | p.time < T ∧ p.velocity 0 ∈ H.carrier} ∧
      (∀ p, p.time < T → p.velocity 0 ∈ H.carrier →
        forwardScalarOperator A.a (nestedSourcePotential H E T f) p = -exitProbePhysical f p) := by
  have hc := (exitProbePhysical_continuous_compact f).2.comp_homeomorph (sectionTwoHomeomorph 1)
  have hg := nested_native_probe_raw_smooth f
  have hu := nested_native_probe_source_support H T f hs
  obtain ⟨⟨-, C, hC, hb⟩, -, hsm, -, hop, -, -, -, -⟩ :=
    kinetic_duhamel hH (by omega) (intervalDomain_admissible H) (zeroCurve_piecewiseC1 1)
      hlam hLam one_pos (evolutionCoefficient A.a) (evolutionCoefficient_smooth A)
      (evolutionCoefficient_symmetric A.a) (evolutionCoefficient_bounds A)
      (identityDrift 1) (identityDrift_smooth 1) (identityDrift_bounds 1)
      E.1 E.2 hE T (exitProbePhysical f ∘ sectionTwoPoint) (fun p => hfn _) hg hc hu
  refine ⟨⟨C, hC, fun p => hb _⟩, ?_, ?_⟩
  · have hD := isOpen_duhamelCylinder
      (isOpen_of_isAdmissibleEvolutionDomain (intervalDomain_admissible H))
      (show Continuous (fun _ : ℝ => (0 : PDE.Vec 1)) from continuous_const) T
    have hh := nested_physical_isKineticC112On hD hsm
    have hset : sectionTwoPoint ⁻¹'
        evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T =
        {p | p.time < T ∧ p.velocity 0 ∈ H.carrier} := by
      ext p
      exact nested_mem_native_past H T p
    rwa [hset] at hh
  · intro p ht hv
    have hp := hop _ ((nested_mem_native_past H T p).mpr ⟨ht, hv⟩)
    have hswap := reconstruction_scalar_operator_swap A.a (nestedSourcePotential H E T f)
      (sectionTwoPoint p)
    rw [sectionTwoPoint_involutive] at hswap
    have heq : nestedSourcePotential H E T f ∘ sectionTwoPoint =
        duhamelPotential E.2 T (exitProbePhysical f ∘ sectionTwoPoint) := by
      funext q
      change duhamelPotential E.2 T (exitProbePhysical f ∘ sectionTwoPoint)
        (sectionTwoPoint (sectionTwoPoint q)) = _
      rw [sectionTwoPoint_involutive q]
    rw [heq] at hswap
    rw [← hswap, hp]
    rfl

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
