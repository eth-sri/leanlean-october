module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionSlab

/-! # Native slice regularity of the actual smooth physical homogeneous reconstruction -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution

variable (H : Interval) (lower T : ℝ) (u : Point → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ (KineticPoint.equivProd 1).symm)
      (KineticPoint.equivProd 1 '' reconstructionStrip H lower T))
include hu

/-- Smoothness in raw physical coordinates transfers to the fixed packed kinetic coordinates. -/
theorem reconstruction_physical_smooth_to_packed :
    ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ reconstructionPhysicalHomeomorph)
      (reconstructionPhysicalHomeomorph ⁻¹' reconstructionStrip H lower T) := by
  let c := fun x =>
    ((evolutionProdCLE 1 x).1, (evolutionProdCLE 1 x).2.2, (evolutionProdCLE 1 x).2.1)
  have hmaps : MapsTo c (reconstructionPhysicalHomeomorph ⁻¹' reconstructionStrip H lower T)
      (KineticPoint.equivProd 1 '' reconstructionStrip H lower T) := fun x hx => ⟨reconstructionPhysicalHomeomorph x, hx, rfl⟩
  have hh := hu.comp ((evolutionProdCLE 1).contDiff.fst.prodMk ((evolutionProdCLE 1).contDiff.snd.snd.prodMk (evolutionProdCLE 1).contDiff.snd.fst)).contDiffOn hmaps
  exact hh

/-- Actual physical joint smoothness gives native slice regularity at every interior point. -/
theorem reconstruction_physical_slice_regular
    (p : Point) (hp : sectionTwoPoint p ∈ reconstructionStrip H lower T) :
    IsSliceRegularAt (u ∘ sectionTwoPoint) p := by
  let D := sectionTwoPoint ⁻¹' reconstructionStrip H lower T
  have hD : IsOpen D := (isOpen_reconstructionStrip H lower T).preimage
    (continuous_sectionTwoPoint 1)
  exact reconstruction_slice_regular_of_contDiffOn hD
    (reconstruction_physical_smooth_to_packed H lower T u hu) p hp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
