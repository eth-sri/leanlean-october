module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionSlab

/-! # Native slice regularity of the actual smooth physical homogeneous reconstruction -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution

/- Smoothness in raw physical coordinates transfers to the fixed packed kinetic coordinates. -/
theorem reconstruction_physical_slice_regular
    (H : Interval) (lower T : ℝ) (u )
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ (KineticPoint.equivProd 1).symm)
      (KineticPoint.equivProd 1 '' reconstructionStrip H lower T))
    (p ) (hp : sectionTwoPoint p ∈ reconstructionStrip H lower T) :
    IsSliceRegularAt (u ∘ sectionTwoPoint) p := by
  let D := sectionTwoPoint ⁻¹' reconstructionStrip H lower T
  have hD : IsOpen D := (isOpen_reconstructionStrip H lower T).preimage
    (continuous_sectionTwoPoint 1)
  have _h_inl_7 : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ reconstructionPhysicalHomeomorph) (reconstructionPhysicalHomeomorph ⁻¹' reconstructionStrip H lower T) := by
    let c : EvolutionVec 1 → ℝ × PDE.Vec 1 × PDE.Vec 1 := fun x =>
      ((evolutionProdCLE 1 x).1, (evolutionProdCLE 1 x).2.2, (evolutionProdCLE 1 x).2.1)
    have hc : ContDiff ℝ (⊤ : ℕ∞) c :=
      (evolutionProdCLE 1).contDiff.fst.prodMk
        ((evolutionProdCLE 1).contDiff.snd.snd.prodMk (evolutionProdCLE 1).contDiff.snd.fst)
    have hmaps : MapsTo c (reconstructionPhysicalHomeomorph ⁻¹' reconstructionStrip H lower T)
        (KineticPoint.equivProd 1 '' reconstructionStrip H lower T) := by
      intro x hx
      exact ⟨reconstructionPhysicalHomeomorph x, hx, rfl⟩
    exact (hu.comp hc.contDiffOn hmaps)
  exact reconstruction_slice_regular_of_contDiffOn hD
    _h_inl_7 p hp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
