import RequestProject.StabilizedDiskPresentation
import RequestProject.DiskFamilyMap


/-! The filled-circle stabilization is natural for literal disk
inclusions. This includes its actual forward homotopy equivalence,
so stabilization preserves a chain's zero-on-pi2 maps. Unverified. -/

noncomputable section
namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
variable {A B D : Type}

theorem diskRoseMap_comp (f : A → B) (g : B → D) :
    (diskRoseMap g).comp (diskRoseMap f) = diskRoseMap (g ∘ f) := by
  apply hom_ext _ _
  · tauto
  simp

end FiniteChains.ClassicalGraphModel

namespace FiniteChains.RelativeAttachment.StabilizedDiskPresentation
open ClassicalGraphModel
variable {A B J K : Type}

def withDummy (f : A ↪ B) : A ⊕ PUnit ↪ B ⊕ PUnit where
  toFun := Sum.map f id
  inj' := by
    intro a b hab
    grind

variable (f : A ↪ B) (c : J ↪ K)
  (r : C(BoundaryFamily J (Fin 2 → ℝ), Rose A))
  (s : C(BoundaryFamily K (Fin 2 → ℝ), Rose B))
  (h : ∀ z, diskRoseMap f (r z) = s ⟨c z.1, z.2⟩)

include h in
theorem attaching_natural (z : BoundaryFamily (J ⊕ PUnit) (Fin 2 → ℝ)) :
    diskRoseMap (withDummy f) (attaching r z) =
      attaching s ⟨withDummy c z.1, z.2⟩ := by
  rcases z with ⟨j | u, a⟩
  · change diskRoseMap (withDummy f) (diskRoseMap Sum.inl (r ⟨j, a⟩)) =
      diskRoseMap Sum.inl (s ⟨c j, a⟩)
    rw [← h ⟨j, a⟩]
    exact congrArg (· (r ⟨j, a⟩))
      ((diskRoseMap_comp Sum.inl (withDummy f)).trans
        (diskRoseMap_comp f Sum.inl).symm)
  · exact congrArg (· (dummyCircleBoundaryHomeomorph a))
      (diskRoseMap_comp Sum.inr (withDummy f))

def map : C(Model r, Model s) :=
  diskFamilyMap _ _ _
    _ (fun j a => attaching_natural f c r s h _)

theorem homotopyEquiv_natural :
    (map f c r s h).comp (homotopyEquiv r).toFun =
      (homotopyEquiv s).toFun.comp
        (DiskPresentationExtension.sourceMap f c r s h) := by
  apply hom_ext r _
  · intro x
    exact congrArg _
      (congrArg (· x)
      ((diskRoseMap_comp Sum.inl (withDummy f)).trans
        (diskRoseMap_comp f Sum.inl).symm))
  · rintro ⟨j, x⟩
    change map f c r s h (DiskPresentationExtension.sourceMap oldGenerator oldRelator
      r _ (attaching_old r) (cell r _ ⟨j, x⟩)) =
      DiskPresentationExtension.sourceMap oldGenerator oldRelator s _ (attaching_old s)
        (DiskPresentationExtension.sourceMap f c r s h
          (cell r _ ⟨j, x⟩))
    rw [DiskPresentationExtension.sourceMap_cell]
    change diskFamilyMap _ _ _
      _ (fun j a => attaching_natural f c r s h _)
        (cell _ _
          ⟨oldRelator j, x⟩) = _
    rw [diskFamilyMap_cell, DiskPresentationExtension.sourceMap_cell,
      DiskPresentationExtension.sourceMap_cell]
    rfl

theorem map_killsPi2_iff : Whitehead.KillsPi2 (map f c r s h) ↔
    Whitehead.KillsPi2 (DiskPresentationExtension.sourceMap f c r s h) := by
  apply Whitehead.killsPi2_homotopyEquiv_square_iff _ _
  rw [homotopyEquiv_natural]
