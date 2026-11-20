module


public import RequestProject.RelatorCircleTraversalWord
public import RequestProject.PresRoseAffineWordReading
public import RequestProject.PresClassicalDiskComparison

@[expose] public section

/-! Match the canonical relator-circle parametrization with the actual
finite edge-word attaching loop. Both sides are maps of the genuine disk
boundary and the comparison is an actual homotopy. Pending verification. -/

noncomputable section
open scoped Classical unitInterval Topology
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.PresModel
open Comb RelativeAttachment ContinuousEdgeWords ClassicalGraphModel

variable {A J : Type} (w : J → List (A × Bool)) (j : J) (hn : 0 < (w j).length)

def presReadTraversal : Path (orderRoseBase A) (orderRoseBase A) where
  toFun t := presCircleWordMap w j _
  continuous_toFun := (presCircleWordMap w j).continuous.comp
    (relatorCircleTraversal w j hn).continuous
  source' := by
    erw [(relatorCircleTraversal w j hn).source]
    apply realizedMap_vertex
  target' := by
    erw [(relatorCircleTraversal w j hn).target]
    apply realizedMap_vertex

theorem presReadTraversal_homotopic_word :
    (presReadTraversal w j hn).Homotopic (orderRoseRead (w j)) := by
  let f :=
    (orderNerveRealizationMap _ (aFun_monotone w)).hom
  have hb :=
    (realizedMap_vertex _ (aFun_monotone w) (circleWordVertex w j hn 0)).symm
  have H := ((circleFullLoop_homotopic_word w j hn).map f).pathCast hb hb
  have hleft : ((circleFullLoop w j hn).map f.continuous).cast hb hb =
      presReadTraversal w j hn := by
    apply Path.ext
    funext t
    change orderNerveRealizationMap _ (aFun_monotone w) _ = _
    erw [← circleTraversal_to_full, orderNerveRealizationMap_comp]
    rfl
  have hright : ((affineOrderWordPath _ (circleWordValid w j hn)).map f.continuous).cast hb hb =
      affineOrderWordPath _ (roseWord_valid (w j)) := by
    apply Path.ext
    funext t
    change orderNerveRealizationMap _ (aFun_monotone w)
      _ = _
    simp_all [affineOrderWordPath_map, mapPath_aFun_circLoop]
  erw [hleft, hright] at H
  exact H.trans (roseWord_homotopic_read (w j))

def classicalPresReadTraversal :=
  ((presReadTraversal w j hn).map (orderRoseRealizationHomeomorph A).continuous).cast
    (orderRoseRealizationHomeomorph_base A).symm (orderRoseRealizationHomeomorph_base A).symm

theorem classicalPresReadTraversal_homotopic_word :
    (classicalPresReadTraversal w j hn).Homotopic (classicalRoseRead (w j)) := by
  have H := ((presReadTraversal_homotopic_word w j hn).map
    (orderRoseRealizationHomeomorph A).toContinuousMap).pathCast
    (orderRoseRealizationHomeomorph_base A).symm (orderRoseRealizationHomeomorph_base A).symm
  have he : ((orderRoseRead (w j)).map (orderRoseRealizationHomeomorph A).continuous).cast
      (orderRoseRealizationHomeomorph_base A).symm (orderRoseRealizationHomeomorph_base A).symm =
        classicalRoseRead (w j) := by
    apply Path.ext
    funext t
    apply orderRoseRead_classical
  aesop

variable (hw : ∀ j, w j ≠ [])

def classicalPresCellBoundary :=
  (classicalPresWordAttaching w hw).comp
    (⟨fun z : UnitBoundary (Fin 2 → ℝ) => ⟨j, z⟩, continuous_sigmaMk («σ» := fun _ : J => UnitBoundary (Fin 2 → ℝ)) (i := j)⟩)

theorem squareLoopDesc_classicalPresReadTraversal :
    squareLoopDesc (classicalPresReadTraversal w j (List.length_pos_of_ne_nil (hw j))) =
      (classicalPresCellBoundary w j hw).comp unitBoundarySquareHomeomorph.symm.toContinuousMap := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, rfl⟩ := squareBoundaryTraversal_surjective z
  erw [squareLoopDesc_traversal]
  change orderRoseRealizationHomeomorph A
    _ =
      classicalPresWordAttaching w hw
        _; erw [← ((relatorCircleCycle w j _).boundaryHomeomorph_traversal t)]; exact (classicalPresWordAttaching_link w hw j _).symm

/-- The actual canonical disk attaching map reads exactly its word,
up to endpoint-preserving reparametrization of the traversal. -/
theorem classicalPresWordAttaching_homotopic_read :
    (classicalPresCellBoundary w j hw).Homotopic
      ((squareLoopDesc (classicalRoseRead (w j))).comp unitBoundarySquareHomeomorph.toContinuousMap) := by
  have H := squareLoopDesc_homotopic
    (classicalPresReadTraversal_homotopic_word w j (List.length_pos_of_ne_nil (hw j)))
  erw [squareLoopDesc_classicalPresReadTraversal w j hw] at H
  have H' := H.comp (ContinuousMap.Homotopic.refl unitBoundarySquareHomeomorph.toContinuousMap)
  simp_all

end FiniteChains.PresModel
