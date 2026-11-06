module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstruction
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsRegularity
public import PDEFoundation.Calculus.RegularityOrder


/-! # Physical smoothness after exchanging the native diffused and transported coordinates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution

/-- The coordinate exchange is a smooth linear map on the existing Euclidean packing. -/
def nestedSwapPacked : EvolutionVec 1 → EvolutionVec 1 := fun x =>
  (evolutionProdCLE 1).symm
    ((evolutionProdCLE 1 x).1, (evolutionProdCLE 1 x).2.2, (evolutionProdCLE 1 x).2.1)

/-- The packed exchange is globally C-infinity. -/
theorem nestedSwapPacked_contDiff : ContDiff ℝ PDE.smoothOrder nestedSwapPacked :=
  (evolutionProdCLE 1).symm.contDiff.comp
    ((evolutionProdCLE 1).contDiff.fst.prodMk
      ((evolutionProdCLE 1).contDiff.snd.snd.prodMk (evolutionProdCLE 1).contDiff.snd.fst))

/-- The packed linear exchange is exactly the established physical coordinate exchange. -/
theorem nestedSwapPacked_physical (x : EvolutionVec 1) :
    evolutionHomeomorph 1 (nestedSwapPacked x) = sectionTwoPoint (evolutionHomeomorph 1 x) := by
  simp [nestedSwapPacked, evolutionHomeomorph, sectionTwoPoint, KineticPoint.homeomorphProd,
    KineticPoint.isometryEquivProd, KineticPoint.equivProd]
  rfl

variable {u : Point → ℝ} {D : Set Point}

/-- Native smoothness transfers to physical smoothness on the exchanged open set. -/
theorem nested_physical_contDiffOn
    (hu : ContDiffOn ℝ PDE.smoothOrder (u ∘ evolutionHomeomorph 1)
      (evolutionHomeomorph 1 ⁻¹' D)) :
    ContDiffOn ℝ PDE.smoothOrder ((u ∘ sectionTwoPoint) ∘ evolutionHomeomorph 1)
      (evolutionHomeomorph 1 ⁻¹' (sectionTwoPoint ⁻¹' D)) := by

  have hs := hu.comp nestedSwapPacked_contDiff.contDiffOn (by
      intro x hx
      change evolutionHomeomorph 1 (nestedSwapPacked x) ∈ D
      rw [nestedSwapPacked_physical]
      exact hx)
  have heq : (u ∘ evolutionHomeomorph 1) ∘ nestedSwapPacked =
      (u ∘ sectionTwoPoint) ∘ evolutionHomeomorph 1 := by
    funext x
    change u (evolutionHomeomorph 1 (nestedSwapPacked x)) = _
    rw [nestedSwapPacked_physical]
    rfl
  rwa [heq] at hs

/-- The same physical smoothness supplies the literal anisotropic C112 interface. -/
theorem nested_physical_isKineticC112On
    (hD : IsOpen D)
    (hu : ContDiffOn ℝ PDE.smoothOrder (u ∘ evolutionHomeomorph 1)
      (evolutionHomeomorph 1 ⁻¹' D)) :
    IsKineticC112On (u ∘ sectionTwoPoint) (sectionTwoPoint ⁻¹' D) :=
  isKineticC112On_of_contDiffOn (hD.preimage (continuous_sectionTwoPoint 1))
    (nested_physical_contDiffOn hu)

/-- Raw physical smoothness on an open set supplies the literal C112 interface. -/
theorem nested_raw_isKineticC112On
    (hD : IsOpen D)
    (hu : ContDiffOn ℝ PDE.smoothOrder (u ∘ (KineticPoint.equivProd 1).symm)
      (KineticPoint.equivProd 1 '' D)) : IsKineticC112On u D := by
  apply isKineticC112On_of_contDiffOn hD

  exact hu.comp (evolutionProdCLE 1).contDiff.contDiffOn (by
      intro x hx
      exact ⟨_, hx, rfl⟩)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
