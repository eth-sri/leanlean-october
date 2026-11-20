module

public import RequestProject.SigmaHomotopy
public import RequestProject.StabilizedDiskPresentation
public import RequestProject.PresCircleWordParametrization
public import RequestProject.ClassicalRoseWordReduction
public import RequestProject.ClassicalRoseWordNaturality

@[expose] public section

namespace FiniteChains.PresModel
open ClassicalGraphModel RelativeAttachment
open scoped Topology

variable {A J : Type} {w : J → List (A × Bool)} {hw : ∀ j, w j ≠ []}

/-- A boundary map reading a representative of the relator agrees up to homotopy
with the canonical disk model. -/
theorem classicalPresCellBoundary_of_word {f : C(UnitBoundary (Fin 2 → ℝ), ClassicalGraphModel.Rose A)}
    {l : List (A × Bool)} {j : J} (h : f.Homotopic (classicalRoseWordBoundary l))
    (he : FreeGroup.mk l = FreeGroup.mk (w j)) :
    f.Homotopic (classicalPresCellBoundary w j hw) :=
  h.trans ((classicalRoseWordBoundary_homotopic_of_mk_eq he).trans
    (classicalPresWordAttaching_homotopic_read w j hw).symm)

variable (r : C(BoundaryFamily J (Fin 2 → ℝ), ClassicalGraphModel.Rose A))
  (u : J → List (A × Bool)) (w' : J ⊕ PUnit.{1} → List ((A ⊕ PUnit.{1}) × Bool))
  (hw' : ∀ j, w' j ≠ [])
  (hr : ∀ j, (r.comp (ContinuousMap.sigmaMk j)).Homotopic (classicalRoseWordBoundary (u j)))
  (hold : ∀ j, FreeGroup.map Sum.inl (FreeGroup.mk (u j)) = FreeGroup.mk (w' (Sum.inl j)))
  (hfresh : FreeGroup.of (Sum.inr PUnit.unit) = FreeGroup.mk (w' (Sum.inr PUnit.unit)))

include hr hold hfresh in
theorem stabilizedPresCellBoundary_homotopic (j : J ⊕ PUnit) :
    ((StabilizedDiskPresentation.attaching r).comp (ContinuousMap.sigmaMk j)).Homotopic
      (classicalPresCellBoundary w' j hw') := by
  cases j with
  | inl j =>
    have H := (ContinuousMap.Homotopic.refl (diskRoseMap (Sum.inl : A → A ⊕ PUnit))).comp (hr j)
    erw [classicalRoseWordBoundary_map] at H
    exact classicalPresCellBoundary_of_word H (hold j)
  | inr j =>
    cases j
    have H := (ContinuousMap.Homotopic.refl (diskRoseMap (Sum.inr : PUnit → A ⊕ PUnit))).comp
      dummyCircleBoundaryHomeomorph_homotopic_word
    erw [classicalRoseWordBoundary_map] at H
    exact classicalPresCellBoundary_of_word H hfresh

noncomputable def stabilizedPresAttachingHomotopy : (StabilizedDiskPresentation.attaching r).Homotopy
    (classicalPresWordAttaching w' hw') :=
  .sigmaFamily fun j => Classical.choice (stabilizedPresCellBoundary_homotopic r u w' hw' hr hold hfresh j)

end FiniteChains.PresModel
