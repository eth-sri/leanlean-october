module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.OrderEdgeSkeletonAttachment
public import RequestProject.ClassicalGraphBoundaryWords

@[expose] public section

noncomputable section
open scoped Classical unitInterval Topology
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb.OrderTriangleWords
open RelativeAttachment ClassicalGraphModel ContinuousEdgeWords
open OrderTriangleAttachment OrderEdgeAttachment CategoryTheory

variable (P : Type) [PartialOrder P]

def edge01 (t : StrictOrdTri P) : StrictOrdEdge P := ⟨(t.val.1, t.val.2.1), t.property.1⟩
def edge12 (t : StrictOrdTri P) : StrictOrdEdge P := ⟨(t.val.2.1, t.val.2.2), t.property.2⟩
def edge02 (t : StrictOrdTri P) : StrictOrdEdge P :=
  ⟨(t.val.1, t.val.2.2), t.property.1.trans t.property.2⟩

def corner (t : StrictOrdTri P) (z : SquareBoundary) : Vertices P :=
  vertexEquiv P (if z.val 1 = 0 then t.val.1 else
    if z.val 0 = 0 then t.val.2.1 else t.val.2.2)

def sideWord (t : StrictOrdTri P) (s : SquareSide) : List (StrictOrdEdge P × Bool) :=
  if s.1 = 0 then
    if s.2 then [(edge02 P t, true)] else [(edge01 P t, true)]
  else if s.2 then [(edge12 P t, true)] else []

def words (t : StrictOrdTri P) : BoundaryWords (graphAttaching P) where
  vertex := corner P t
  word := sideWord P t
  isPath := by
    rintro ⟨i, b⟩
    fin_cases i <;> cases b <;>
      simp [sideWord, corner, squareSideMap, Whitehead.squareEdge, boolEndpoint,
        IsPath, germSrc, germTgt, graphAttaching_source, graphAttaching_target,
        edge01, edge12, edge02]

theorem words_loopWord (t : StrictOrdTri P) :
    (words P t).loopWord = (strictOrderCx P).att t := by
  simp [BoundaryWords.loopWord, words, sideWord, revPath, revGerm,
    edge01, edge12, edge02, strictOrderCx]

def graphAttachingTriangles :
    C(BoundaryFamily (StrictOrdTri P) (Fin 2 → ℝ), DiskAttachment (graphAttaching P)) :=
  (graphHomeomorph P).symm.toContinuousMap.comp (triangleAttaching P)

def graphBoundary (t : StrictOrdTri P) :
    C(UnitBoundary (Fin 2 → ℝ), DiskAttachment (graphAttaching P)) :=
  (graphAttachingTriangles P).comp
    ⟨Sigma.mk (β := fun _ : StrictOrdTri P => UnitBoundary (Fin 2 → ℝ)) t, continuous_sigmaMk⟩

def graphSquare (t : StrictOrdTri P) : C(SquareBoundary, DiskAttachment (graphAttaching P)) :=
  (graphBoundary P t).comp unitBoundarySquareHomeomorph.symm.toContinuousMap

theorem graphSquare_coordinates (t : StrictOrdTri P) (z : SquareBoundary) (p : P) :
    orderNerveRealizationCoordinates P ((graphHomeomorph P (graphSquare P t z)).val) p =
      (1 - (z.val 1 : ℝ)) * (if t.val.1 = p then 1 else 0) +
      ((z.val 1 : ℝ) * (1 - (z.val 0 : ℝ))) * (if t.val.2.1 = p then 1 else 0) +
      ((z.val 1 : ℝ) * (z.val 0 : ℝ)) * (if t.val.2.2 = p then 1 else 0) := by
  rw [show graphHomeomorph P (graphSquare P t z) =
      triangleAttaching P ⟨t, unitBoundarySquareHomeomorph.symm z⟩ from
    (graphHomeomorph P).apply_symm_apply _, triangleAttaching_val]
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
  change (∑ i : Fin 3, (OrderTriangleDisk.parametrization z.val).val i *
    (if (strictTriNerveEquiv P t).val.obj i = p then 1 else 0)) = _
  rw [Fin.sum_univ_three]; rfl

def intervalPath : Path (0 : I) 1 where
  toFun := id
  continuous_toFun := continuous_id
  source' := rfl
  target' := rfl

theorem graphBoundary_homotopic_words (t : StrictOrdTri P) :
    (graphBoundary P t).Homotopic (words P t).boundaryMap := by
  let paused : Path (0 : I) 1 := intervalPath.trans (Path.refl 1)
  have hsingle {V E X : Type} [TopologicalSpace X]
      (src tgt : E → V) (v : V → X) (edge : ∀ e, Path (v (src e)) (v (tgt e)))
      (g : E × Bool) {a b : V} (h : IsPath src tgt [g] a b) (u : I) :
      realize src tgt v edge [g] h u = germPath src tgt v edge g (paused u) := by
    by_cases hu : (u : ℝ) ≤ 2⁻¹ <;>
      simp [realize, paused, intervalPath, Path.trans_apply, hu]
  have hside (s : SquareSide) (u : I) :
      (words P t).sidePath s u = graphSquare P t (squareSideMap s (paused u)) := by
    rcases s with ⟨i, b⟩
    fin_cases i <;> cases b
    · erw [show graphSquare P t (squareSideMap (0, false) (paused u)) =
          graphEdgePath (graphAttaching P) (edge01 P t) (paused u) by
        apply (graphHomeomorph P).injective; apply Subtype.ext
        apply orderNerveRealizationCoordinates_injective P; funext p
        rw [graphSquare_coordinates, graphHomeomorph_edgePath, orderNerveAffineEdgePath_coordinates]
        simp [squareSideMap, Whitehead.squareEdge, boolEndpoint, edge01]]
      exact hsingle _ _ _ _ _ ((words P t).isPath (0, false)) u
    · erw [show graphSquare P t (squareSideMap (0, true) (paused u)) =
          graphEdgePath (graphAttaching P) (edge02 P t) (paused u) by
        apply (graphHomeomorph P).injective; apply Subtype.ext
        apply orderNerveRealizationCoordinates_injective P; funext p
        rw [graphSquare_coordinates, graphHomeomorph_edgePath, orderNerveAffineEdgePath_coordinates]
        simp [squareSideMap, Whitehead.squareEdge, boolEndpoint, edge02]]
      exact hsingle _ _ _ _ _ ((words P t).isPath (0, true)) u
    · erw [show graphSquare P t (squareSideMap (1, false) (paused u)) =
          old (graphAttaching P) (boundaryFamilyInclusion (StrictOrdEdge P) _) (vertexEquiv P t.val.1) by
        apply (graphHomeomorph P).injective; apply Subtype.ext
        apply orderNerveRealizationCoordinates_injective P; funext p
        rw [graphSquare_coordinates, graphHomeomorph_old, vertexEquiv_val,
          orderNerveRealizationCoordinates_vertex]
        simp [squareSideMap, Whitehead.squareEdge, boolEndpoint]]
      simp [BoundaryWords.sidePath, words, sideWord, realize, corner,
        squareSideMap, Whitehead.squareEdge, boolEndpoint]
    · erw [show graphSquare P t (squareSideMap (1, true) (paused u)) =
          graphEdgePath (graphAttaching P) (edge12 P t) (paused u) by
        apply (graphHomeomorph P).injective; apply Subtype.ext
        apply orderNerveRealizationCoordinates_injective P; funext p
        rw [graphSquare_coordinates, graphHomeomorph_edgePath, orderNerveAffineEdgePath_coordinates]
        simp [squareSideMap, Whitehead.squareEdge, boolEndpoint, edge12]]
      exact hsingle _ _ _ _ _ ((words P t).isPath (1, true)) u
  let H := Classical.choice ((Path.Homotopic.trans_refl intervalPath).symm)
  let F (s : SquareSide) : C(I × I, DiskAttachment (graphAttaching P)) :=
    (graphSquare P t).comp ((squareSideMap s).comp H.toHomotopy.toContinuousMap)
  have hend : ∀ s τ u, u = 0 ∨ u = 1 → F s (τ, u) = graphSquare P t (squareSideMap s u) := by
    rintro s τ u (rfl | rfl)
    · exact congrArg (fun u => graphSquare P t (squareSideMap s u)) (H.source τ)
    · exact congrArg (fun u => graphSquare P t (squareSideMap s u)) (H.target τ)
  have hsq : (graphSquare P t).Homotopic (words P t).squareMap := ⟨{
    toContinuousMap := squareBoundaryHomotopyPasting F (fun _ => graphSquare P t) hend
    map_zero_left := fun z => by
      obtain ⟨⟨s, u⟩, rfl⟩ := squareSideQuotient_surjective z
      change squareBoundaryHomotopyPasting F (fun _ => graphSquare P t) hend
        (0, squareSideMap s u) = graphSquare P t (squareSideMap s u)
      rw [squareBoundaryHomotopyPasting_side]
      change graphSquare P t (squareSideMap s (H (0, u))) = _
      rw [H.apply_zero]; rfl
    map_one_left := fun z => by
      obtain ⟨⟨s, u⟩, rfl⟩ := squareSideQuotient_surjective z
      change squareBoundaryHomotopyPasting F (fun _ => graphSquare P t) hend
        (1, squareSideMap s u) = (words P t).squareMap (squareSideMap s u)
      rw [squareBoundaryHomotopyPasting_side, BoundaryWords.squareMap_side]
      change graphSquare P t (squareSideMap s (H (1, u))) = _
      rw [H.apply_one]; exact (hside s u).symm }⟩
  have H' := hsq.comp (ContinuousMap.Homotopic.refl unitBoundarySquareHomeomorph.toContinuousMap)
  rwa [show (graphSquare P t).comp unitBoundarySquareHomeomorph.toContinuousMap =
      graphBoundary P t from ContinuousMap.ext fun z =>
    congrArg (graphBoundary P t) (unitBoundarySquareHomeomorph.symm_apply_apply z)] at H'

end FiniteChains.Comb.OrderTriangleWords
