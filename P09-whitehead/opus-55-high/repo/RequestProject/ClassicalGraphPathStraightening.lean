import RequestProject.ClassicalGraphModel
import RequestProject.ContinuousEdgeWords
import RequestProject.DiskAttachmentVertexStars
import RequestProject.Tac


/-! Every continuous path between vertices of the literal graph attachment
is homotopic relative endpoints to a finite word in its original edges.
No finiteness or local finiteness of the graph is assumed.
Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval
open Set Topology

bwd

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment ContinuousEdgeWords PathReplacement

abbrev GraphBall := ClosedUnitBall (Fin 1 → ℝ)

def graphBallSegment (x y : GraphBall) : Path x y where
  toFun t := ⟨Path.segment x.val y.val t, by
    have h := (convex_closedBall (0 : Fin 1 → ℝ) 1).segment_subset
      (by aesop)
      (by aesop)
      (show Path.segment x.val y.val t ∈ segment ℝ x.val y.val by
        grind [← Path.range_segment])
    simp_all⟩
  continuous_toFun := (Path.segment x.val y.val).continuous.subtype_mk _
  source' := Subtype.ext (Path.segment x.val y.val).source
  target' := Subtype.ext (Path.segment x.val y.val).target

theorem graphBall_simplyConnected : SimplyConnectedSpace GraphBall := by
  letI := Metric.contractibleSpace_closedBall (E := Fin 1 → ℝ) (x := 0) zero_le_one
  let e : Metric.closedBall (0 : Fin 1 → ℝ) 1 ≃ₜ GraphBall := Homeomorph.setCongr (by
    aesop)
  exact e.symm.toHomotopyEquiv.simplyConnectedSpace

def graphSnapBoundary (x : GraphBall) :=
  if h : 0 < ‖x.val‖ then annulusBoundary 0 le_rfl ⟨x, h⟩ else graphBoundaryNeg

variable {V J : Type} [TopologicalSpace V]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V)

def graphCellMap (j : J) : C(GraphBall, DiskAttachment r) :=
  ⟨fun x => cell r _ ⟨j, x⟩,
    (cell_continuous r _).comp continuous_sigmaMk⟩

theorem graphCellMap_interior j (x : OpenNormBall (Fin 1 → ℝ)) :
    graphCellMap r j ⟨x.val, x.property.le⟩ = openDiskMap r j x := by
  exact cell_of_not_mem r _ ⟨j, ⟨x.val, x.property.le⟩⟩
    (fun h => (ne_of_lt x.property)
      ((boundaryFamilyInclusion_range J (Fin 1 → ℝ) _).mp h))

def graphOpenPath j (x y : OpenNormBall (Fin 1 → ℝ))
    (P : Path (⟨x.val, x.property.le⟩ : GraphBall) ⟨y.val, y.property.le⟩) :=
  (P.map (graphCellMap r j).continuous).cast (graphCellMap_interior r j x).symm
    (graphCellMap_interior r j y).symm

def graphSnap : DiskAttachment r → V
  | Sum.inl v => v
  | Sum.inr d => r ⟨d.val.1, graphSnapBoundary d.val.2⟩

def graphConnector (z : DiskAttachment r) :
    Path z (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (graphSnap r z)) :=
  match z with
  | Sum.inl _ => Path.refl _
  | Sum.inr d =>
      ((graphBallSegment d.val.2 _).map
        (graphCellMap r d.val.1).continuous).cast
          (cell_of_not_mem r _ d.val d.property).symm
          (cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J _).injective
            _).symm

omit [TopologicalSpace V] in
theorem graphSnap_of_mem_vertexStar {v : V} {z : DiskAttachment r}
    (hz : z ∈ vertexStar r v) : graphSnap r z = v := by
  cases z with
  | inl w => exact hz
  | inr d =>
    cases' hz with hx hv
    simp_all [graphSnap, graphSnapBoundary]

theorem graphConnector_eq_radial (hr : Continuous r)
    z :
    ∀ t, graphConnector r z.val t = radialCoreHomotopy r hr (t, z) := by
  rcases z with ⟨v | d, hz⟩
  · intro t
    rfl
  · cases' hz with hx _
    intro t
    apply congrArg (cell r (boundaryFamilyInclusion J (Fin 1 → ℝ)))
    apply congrArg _
    apply Subtype.ext
    change Path.segment d.val.2.val (graphSnapBoundary d.val.2).val t =
      ((1 - t) + t / ‖d.val.2.val‖) • d.val.2.val
    rw [Path.segment_apply, AffineMap.lineMap_apply_module]
    rw [graphSnapBoundary, dif_pos hx]
    change (1 - (t : ℝ)) • d.val.2.val +
      (t : ℝ) • (‖d.val.2.val‖⁻¹ • d.val.2.val) = _
    rw [smul_smul, add_smul, div_eq_mul_inv]

theorem graphConnector_range_vertexStar (hr : Continuous r) {v}
    {z} (hz : z ∈ vertexStar r v) :
    Set.range (graphConnector r z) ⊆ vertexStar r v := by
  rintro _ ⟨t, rfl⟩
  rw [graphConnector_eq_radial r hr ⟨z, vertexStar_subset_core r v hz⟩ t]
  exact radialCoreHomotopy_mem_oldCollar r hr t _ _ hz

def graphBoundaryPath j a b
    (p : Path (unitBoundaryInclusion _ a) (unitBoundaryInclusion _ b)) :
    Path (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (r ⟨j, a⟩))
      (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (r ⟨j, b⟩)) :=
  (p.map (graphCellMap r j).continuous).cast
    (cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J _).injective _).symm
    (cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J _).injective _).symm

def graphClosedEdgePath :
    Path (unitBoundaryInclusion _ graphBoundaryNeg) (unitBoundaryInclusion _ graphBoundaryPos) where
  toFun := graphDiskHomeomorph
  continuous_toFun := graphDiskHomeomorph.continuous
  source' := graphDiskHomeomorph_zero
  target' := graphDiskHomeomorph_one

theorem graphBoundaryPath_refl j a :
    graphBoundaryPath r j a a (Path.refl _) =
      Path.refl (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (r ⟨j, a⟩)) := by
  apply Path.ext
  funext t
  exact cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J _).injective ⟨j, a⟩

theorem graphBoundaryPath_isWord j a b
    p :
    IsWord (graphSrc r) (graphTgt r) (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)))
      (graphEdgePath r) (graphBoundaryPath r j a b p) := by
  letI := graphBall_simplyConnected
  rcases graphBoundary_cases a with rfl | rfl <;>
    rcases graphBoundary_cases b with rfl | rfl
  · refine ⟨[], rfl, ?_⟩
    have h := (SimplyConnectedSpace.paths_homotopic p (Path.refl _)).map (graphCellMap r j)
    have h' : Path.Homotopic (graphBoundaryPath r j graphBoundaryNeg graphBoundaryNeg p)
        (graphBoundaryPath r j graphBoundaryNeg graphBoundaryNeg (Path.refl _)) := h.pathCast _ _
    rwa [graphBoundaryPath_refl] at h'
  · refine ⟨[(j, true)], ⟨rfl, rfl⟩, ?_⟩
    have h := (SimplyConnectedSpace.paths_homotopic p graphClosedEdgePath).map (graphCellMap r j)
    have h' : Path.Homotopic (graphBoundaryPath r j graphBoundaryNeg graphBoundaryPos p)
        (graphEdgePath r j) := h.pathCast _ _
    exact h'.trans (Path.Homotopic.trans_refl _).symm
  · refine ⟨[(j, false)], ⟨rfl, rfl⟩, ?_⟩
    have h := (SimplyConnectedSpace.paths_homotopic p graphClosedEdgePath.symm).map (graphCellMap r j)
    have h' : Path.Homotopic (graphBoundaryPath r j graphBoundaryPos graphBoundaryNeg p)
        (graphEdgePath r j).symm := h.pathCast _ _
    exact h'.trans (Path.Homotopic.trans_refl _).symm
  · refine ⟨[], rfl, ?_⟩
    have h := (SimplyConnectedSpace.paths_homotopic p (Path.refl _)).map (graphCellMap r j)
    have h' : Path.Homotopic (graphBoundaryPath r j graphBoundaryPos graphBoundaryPos p)
        (graphBoundaryPath r j graphBoundaryPos graphBoundaryPos (Path.refl _)) := h.pathCast _ _
    rwa [graphBoundaryPath_refl] at h'

theorem lift_openDisk_path j (x y : OpenNormBall (Fin 1 → ℝ))
    (p : Path (openDiskMap r j x) (openDiskMap r j y))
    (hp : Set.range p ⊆ openDisk r j) :
    ∃ P,
      graphOpenPath r j x y P = p := by
  let e := (openDiskMap_isOpenEmbedding r j).isEmbedding.toHomeomorph
  let Q : Path (e x) (e y) := {
    toFun := fun t => ⟨p t, hp ⟨t, rfl⟩⟩
    continuous_toFun := p.continuous.subtype_mk _
    source' := Subtype.ext p.source
    target' := Subtype.ext p.target }
  let incl : C(OpenNormBall (Fin 1 → ℝ), GraphBall) :=
    ⟨fun x => ⟨x.val, x.property.le⟩, continuous_subtype_val.subtype_mk _⟩
  let P := ((Q.map e.symm.continuous).cast (e.symm_apply_apply x).symm
    (e.symm_apply_apply y).symm).map incl.continuous
  refine ⟨P, ?_⟩
  apply Path.ext
  funext t
  change graphCellMap r j ⟨(e.symm (Q t)).val, by grind⟩ = p t
  rw [graphCellMap_interior]
  exact congrArg Subtype.val (e.apply_symm_apply _)

theorem graph_isWord_local_edge j {x y}
    (p : Path x y) (hp : Set.range p ⊆ openDisk r j) :
    IsWord (graphSrc r) (graphTgt r) (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)))
      (graphEdgePath r) (((graphConnector r x).symm.trans p).trans (graphConnector r y)) := by
  obtain ⟨x, rfl⟩ := hp p.source_mem_range
  obtain ⟨y, rfl⟩ := hp p.target_mem_range
  obtain ⟨P, rfl⟩ := lift_openDisk_path r j x y p hp
  let a : GraphBall := ⟨x.val, x.property.le⟩
  let b : GraphBall := ⟨y.val, y.property.le⟩
  let A := graphSnapBoundary a
  let B := graphSnapBoundary b
  let Q := ((graphBallSegment a (unitBoundaryInclusion _ A)).symm.trans P).trans
    (graphBallSegment b (unitBoundaryInclusion _ B))
  have h := graphBoundaryPath_isWord r j A B Q
  have he : graphBoundaryPath r j A B Q =
      (((graphConnector r _).symm.trans (graphOpenPath r j x y P)).trans
        (graphConnector r _)) := by
    apply Path.ext
    funext t
    simp [graphBoundaryPath, Q, graphOpenPath, Path.cast_coe,
      Path.map_coe, Function.comp_apply, Path.trans_apply, Path.symm_apply]
    aesop
  simp_all

theorem graph_isWord_local_vertex (hr : Continuous r) v {x y}
    (p : Path x y) (hp : Set.range p ⊆ vertexStar r v) :
    IsWord (graphSrc r) (graphTgt r) (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)))
      (graphEdgePath r) (((graphConnector r x).symm.trans p).trans (graphConnector r y)) := by
  have hx := hp p.source_mem_range
  have hy := hp p.target_mem_range
  have hxy := (graphSnap_of_mem_vertexStar r hx).trans (graphSnap_of_mem_vertexStar r hy).symm
  refine ⟨[], hxy, ?_⟩
  apply homotopic_of_within_simplyConnected _ (vertexStar_simplyConnected r hr v)
  · exact range_trans_subset _ _
      (range_trans_subset _ _ (range_symm_subset _ (graphConnector_range_vertexStar r hr hx)) hp)
      (graphConnector_range_vertexStar r hr hy)
  · rintro _ ⟨t, rfl⟩
    exact graphSnap_of_mem_vertexStar r hx

/-- Every path between actual vertices is represented by a finite list of
the actual original oriented edges. -/
theorem graph_path_isWord [DiscreteTopology V] (hr : Continuous r) v w
    (p : Path (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) v)
      (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) w)) :
    IsWord (graphSrc r) (graphTgt r) (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)))
      (graphEdgePath r) p := by
  let U := Sum.elim (vertexStar r) (openDisk r)
  have hU : ∀ i, IsOpen (U i) := by
    rintro (v | j)
    · exact vertexStar_isOpen r hr v
    · exact openDisk_isOpen r j
  have hcover : Set.univ ⊆ ⋃ i, U i := by
    rintro (v | d) _
    · aesop
    · have hd := lt_of_le_of_ne d.val.2.property
        (by aesop)
      exact Set.mem_iUnion.mpr ⟨Sum.inr d.val.1, ⟨⟨d.val.2.val, hd⟩, rfl⟩⟩
  have hlocal : ∀ i {x y : DiskAttachment r} (p : Path x y), Set.range p ⊆ U i →
      IsWord _ _ _
        (graphEdgePath r) (((graphConnector r x).symm.trans p).trans (graphConnector r y)) := by
    rintro (v | j) x y p hp
    · exact graph_isWord_local_vertex r hr v p hp
    · exact graph_isWord_local_edge r j p hp
  have h := isWord_of_open_cover _ _
    _ _
    U hU hcover _ _ hlocal p
  apply h.of_homotopic
  exact ((Path.Homotopic.refl_trans p).hcomp (Path.Homotopic.refl _)
    |>.trans (Path.Homotopic.trans_refl p)).symm

theorem graphCx_isConnected [DiscreteTopology V] (hr : Continuous r)
    [PathConnectedSpace (DiskAttachment r)] : Comb.IsConnected (graphCx r) := by
  intro v w
  obtain ⟨p⟩ := PathConnectedSpace.joined
    (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) v)
    _
  obtain ⟨l, hl, _⟩ := graph_path_isWord r hr v w p
  tauto
