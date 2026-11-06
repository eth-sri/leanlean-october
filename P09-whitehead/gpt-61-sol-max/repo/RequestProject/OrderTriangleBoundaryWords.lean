import Mathlib.Tactic

import RequestProject.HomeomorphContinuousMap
import RequestProject.OrderEdgeSkeletonAttachment
import RequestProject.ClassicalGraphBoundaryWords

/-! The actual triangle attaching circle reads the literal strict
boundary 01,12,02^-1 in the graph model. The trailing constant segment in
the recursive word reader is handled by an endpoint-fixed homotopy on
all four sides.  -/

noncomputable section
open scoped Classical unitInterval Topology
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.OrderTriangleWords
open RelativeAttachment ClassicalGraphModel ContinuousEdgeWords
open OrderTriangleAttachment OrderEdgeAttachment CategoryTheory

variable (P : Type) [PartialOrder P]

  (t : StrictOrdTri P)
def edge01  : StrictOrdEdge P := ⟨(t.val.1, t.val.2.1), t.property.1⟩
def edge12  : StrictOrdEdge P := ⟨(t.val.2.1, t.val.2.2), t.property.2⟩
def edge02  : StrictOrdEdge P :=
  ⟨(t.val.1, t.val.2.2), t.property.1.trans t.property.2⟩

def corner  (z : SquareBoundary)  :=
  vertexEquiv P (if z.val 1 = 0 then t.val.1 else
    if z.val 0 = 0 then t.val.2.1 else t.val.2.2)

def sideWord  (s : SquareSide)  :=
  if s.1 = 0 then
    if s.2 then [(edge02 P t, true)] else [(edge01 P t, true)]
  else if s.2 then [(edge12 P t, true)] else []

def words  : BoundaryWords (graphAttaching P) where
  vertex := corner P t
  word := sideWord P t
  isPath := by
    rintro ⟨i, b⟩
    fin_cases i <;> cases b <;>
      simp [sideWord, corner, squareSideMap, Whitehead.squareEdge, boolEndpoint,
        IsPath, germSrc, germTgt, graphAttaching_source, graphAttaching_target,
        edge01, edge12, edge02]



def graphAttachingTriangles  :=
  (graphHomeomorph P).symm.toContinuousMap.comp (triangleAttaching P)

def graphBoundary   :=
  (graphAttachingTriangles P).comp
    ⟨Sigma.mk (β := fun _ : StrictOrdTri P => UnitBoundary (Fin 2 → ℝ)) t,
      continuous_sigmaMk⟩

def graphSquare   :=
  (graphBoundary P t).comp unitBoundarySquareHomeomorph.symm.toContinuousMap

theorem graphSquare_coordinates  (z : SquareBoundary) (p : P) :
    orderNerveRealizationCoordinates P ((graphHomeomorph P (graphSquare P t z)).val) p =
      (1 - (z.val 1 : ℝ)) * (if t.val.1 = p then 1 else 0) +
      ((z.val 1 : ℝ) * (1 - (z.val 0 : ℝ))) * (if t.val.2.1 = p then 1 else 0) +
      ((z.val 1 : ℝ) * (z.val 0 : ℝ)) * (if t.val.2.2 = p then 1 else 0) := by
  have he : graphHomeomorph P (graphSquare P t z) =
      triangleAttaching P ⟨t, unitBoundarySquareHomeomorph.symm z⟩ :=
    (graphHomeomorph P).apply_symm_apply _
  rw [he, triangleAttaching_val]
  have hd : OrderTriangleDisk.disk
      (unitBoundaryInclusion _ (unitBoundarySquareHomeomorph.symm z)) =
        OrderTriangleDisk.parametrization z.val := by
    change OrderTriangleDisk.parametrization
      (OrderTriangleDisk.squareBallHomeomorph
        (unitBoundaryInclusion _ (unitBoundarySquareHomeomorph.symm z))) = _
    rw [OrderTriangleDisk.squareBallHomeomorph_boundary, Homeomorph.apply_symm_apply]
  change orderNerveRealizationCoordinates P
    (orderNerveRealizationSimplex P (strictTriNerveEquiv P t).val
      (ULift.up ((TopologicalSingular.simplexCoordinates 2).symm (OrderTriangleDisk.disk
        (unitBoundaryInclusion _ (unitBoundarySquareHomeomorph.symm z)))))) p = _
  rw [hd, orderNerveRealizationCoordinates_simplex]
  simp only [orderNerveAffineSimplex, ContinuousMap.coe_mk,
    TopologicalSingular.simplexCoordinates_symm_weights_apply]
  
  rw [Fin.sum_univ_three]
  rfl

variable (u : I)
theorem graphSquare_left   :
    graphSquare P t (squareSideMap (0, false) u) = graphEdgePath (graphAttaching P) (edge01 P t) u := by
  apply (graphHomeomorph P).injective
  apply Subtype.ext
  apply orderNerveRealizationCoordinates_injective P
  ext <;> simp_all [graphSquare_coordinates, graphHomeomorph_edgePath, orderNerveAffineEdgePath_coordinates, squareSideMap, Whitehead.squareEdge, boolEndpoint, edge01]

theorem graphSquare_top   :
    graphSquare P t (squareSideMap (1, true) u) = graphEdgePath (graphAttaching P) (edge12 P t) u := by
  apply (graphHomeomorph P).injective
  apply Subtype.ext
  apply orderNerveRealizationCoordinates_injective P
  ext <;> simp_all [graphSquare_coordinates, graphHomeomorph_edgePath, orderNerveAffineEdgePath_coordinates, squareSideMap, Whitehead.squareEdge, boolEndpoint, edge12]

theorem graphSquare_right   :
    graphSquare P t (squareSideMap (0, true) u) = graphEdgePath (graphAttaching P) (edge02 P t) u := by
  apply (graphHomeomorph P).injective
  apply Subtype.ext
  apply orderNerveRealizationCoordinates_injective P
  ext <;> simp_all [graphSquare_coordinates, graphHomeomorph_edgePath, orderNerveAffineEdgePath_coordinates, squareSideMap, Whitehead.squareEdge, boolEndpoint, edge02]

theorem graphSquare_bottom   :
    graphSquare P t (squareSideMap (1, false) u) =
      old (graphAttaching P) (boundaryFamilyInclusion (StrictOrdEdge P) _) (vertexEquiv P t.val.1) := by
  apply (graphHomeomorph P).injective
  apply Subtype.ext
  apply orderNerveRealizationCoordinates_injective P
  funext p
  rw [graphSquare_coordinates, graphHomeomorph_old, vertexEquiv_val,
    orderNerveRealizationCoordinates_vertex]
  simp [squareSideMap, Whitehead.squareEdge, boolEndpoint]

def intervalPath : Path (0 : I) 1 where
  toFun := id
  continuous_toFun := continuous_id
  source' := rfl
  target' := rfl

def pausedIntervalPath  := intervalPath.trans (Path.refl 1)

theorem single_word_paused {V E X : Type} [TopologicalSpace X]
    (src tgt : E → V) (v : V → X) (edge : ∀ e, Path (v (src e)) (v (tgt e)))
    (g : E × Bool) {a b : V} (h : IsPath src tgt [g] a b) (u : I) :
    realize src tgt v edge [g] h u = germPath src tgt v edge g (pausedIntervalPath u) := by
  classical aesop (add simp [realize, pausedIntervalPath, intervalPath, Path.trans_apply])

theorem words_side_paused  (s : SquareSide) (u : I) :
    (words P t).sidePath s u = graphSquare P t (squareSideMap s (pausedIntervalPath u)) := by
  rcases s with ⟨i, b⟩
  fin_cases i <;> cases b
  · erw [graphSquare_left P t (pausedIntervalPath u)]
    exact single_word_paused _ _ _ _ _ ((words P t).isPath (0, false)) u
  · erw [graphSquare_right P t (pausedIntervalPath u)]
    exact single_word_paused _ _ _ _ _ ((words P t).isPath (0, true)) u
  · erw [graphSquare_bottom P t (pausedIntervalPath u)]
    simp [BoundaryWords.sidePath, words, sideWord, realize, corner,
      squareSideMap, Whitehead.squareEdge, boolEndpoint]
  · erw [graphSquare_top P t (pausedIntervalPath u)]
    exact single_word_paused _ _ _ _ _ ((words P t).isPath (1, true)) u

/-- All side homotopies use the same fixed-endpoint interval homotopy,
so they agree at corners throughout the deformation. -/
theorem graphSquare_homotopic_words  :
    (graphSquare P t).Homotopic (words P t).squareMap := by
  let H := Classical.choice ((Path.Homotopic.trans_refl intervalPath).symm)
  let F (s : SquareSide)  :=
    (graphSquare P t).comp ((squareSideMap s).comp H.toHomotopy.toContinuousMap)
  have hend : ∀ s τ u, u = 0 ∨ u = 1 → F s (τ, u) = graphSquare P t (squareSideMap s u) := by
    aesop
  let G := squareBoundaryHomotopyPasting F (fun _ => graphSquare P t) hend
  exact ⟨{
    toContinuousMap := G
    map_zero_left := by
      intro z
      obtain ⟨⟨s, u⟩, rfl⟩ := squareSideQuotient_surjective z
      change squareBoundaryHomotopyPasting F (fun _ => graphSquare P t) hend
        (0, squareSideMap s u) = graphSquare P t (squareSideMap s u)
      aesop
    map_one_left := by
      intro z
      obtain ⟨⟨s, u⟩, rfl⟩ := squareSideQuotient_surjective z
      change squareBoundaryHomotopyPasting F (fun _ => graphSquare P t) hend
        (1, squareSideMap s u) = (words P t).squareMap (squareSideMap s u)
      aesop (add simp [FiniteChains.Comb.OrderTriangleWords.words_side_paused]) }⟩

theorem graphBoundary_homotopic_words  :
    (graphBoundary P t).Homotopic (words P t).boundaryMap := by
  have H := (graphSquare_homotopic_words P t).comp
    (ContinuousMap.Homotopic.refl unitBoundarySquareHomeomorph.toContinuousMap)
  aesop (add simp [graphSquare])

end FiniteChains.Comb.OrderTriangleWords
