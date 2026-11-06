module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionSlab
public import PDEFoundation.Calculus.RegularityOrder


/-! # Native slice regularity of the actual smooth physical homogeneous reconstruction -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set
open TheoremA Evolution

variable (H : Interval) (lower T : ℝ) (u : Point → ℝ) (hu : ContDiffOn ℝ PDE.smoothOrder (u ∘ (KineticPoint.equivProd 1).symm) (KineticPoint.equivProd 1 '' reconstructionStrip H lower T))

include hu
/-- Smoothness in raw physical coordinates transfers to the fixed packed kinetic coordinates. -/
theorem reconstruction_physical_smooth_to_packed
     :
    ContDiffOn ℝ PDE.smoothOrder (u ∘ reconstructionPhysicalHomeomorph)
      (reconstructionPhysicalHomeomorph ⁻¹' reconstructionStrip H lower T) := by
  let c  := fun x =>
    ((evolutionProdCLE 1 x).1, (evolutionProdCLE 1 x).2.2, (evolutionProdCLE 1 x).2.1)
  have hc : ContDiff ℝ PDE.smoothOrder c :=
    (evolutionProdCLE 1).contDiff.fst.prodMk
      ((evolutionProdCLE 1).contDiff.snd.snd.prodMk (evolutionProdCLE 1).contDiff.snd.fst)
  have hmaps : MapsTo c (reconstructionPhysicalHomeomorph ⁻¹' reconstructionStrip H lower T)
      (KineticPoint.equivProd 1 '' reconstructionStrip H lower T) := by
    intro x hx
    exact ⟨_, hx, rfl⟩
  have hh := hu.comp hc.contDiffOn hmaps
  exact hh

/-- Actual physical joint smoothness gives native slice regularity at every interior point. -/
theorem reconstruction_physical_slice_regular

    (p : Point) (hp : sectionTwoPoint p ∈ reconstructionStrip H lower T) :
    IsSliceRegularAt (u ∘ sectionTwoPoint) p := (reconstruction_slice_regular_of_contDiffOn
  (IsOpen.preimage (continuous_sectionTwoPoint 1) (isOpen_reconstructionStrip H lower T))
  (reconstruction_physical_smooth_to_packed H lower T u hu) p hp)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
