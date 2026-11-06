module

public import RequestProject.ClassicalGraphModel
public import RequestProject.ContinuousEdgeWords
public import RequestProject.DiskAttachmentVertexStars

@[expose] public section

noncomputable section
open scoped Classical unitInterval
open Set Topology

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment ContinuousEdgeWords PathReplacement

abbrev GraphBall := ClosedUnitBall (Fin 1 → ℝ)

def graphBallSegment (x y : GraphBall) : Path x y where
  toFun t := ⟨Path.segment x.val y.val t, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (convex_closedBall (0 : Fin 1 → ℝ) 1).segment_subset
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property)
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using y.property)
        (by rw [← Path.range_segment]; exact ⟨t, rfl⟩)⟩
  continuous_toFun := (Path.segment x.val y.val).continuous.subtype_mk _
  source' := Subtype.ext (Path.segment x.val y.val).source
  target' := Subtype.ext (Path.segment x.val y.val).target

theorem graphBall_simplyConnected : SimplyConnectedSpace GraphBall := by
  letI := Metric.contractibleSpace_closedBall (E := Fin 1 → ℝ) (x := 0) zero_le_one
  exact (Homeomorph.setCongr (by ext x; change dist x 0 ≤ 1 ↔ ‖x‖ ≤ 1; rw [dist_zero_right]) :
    Metric.closedBall (0 : Fin 1 → ℝ) 1 ≃ₜ GraphBall).symm.toHomotopyEquiv.simplyConnectedSpace

def graphSnapBoundary (x : GraphBall) : UnitBoundary (Fin 1 → ℝ) :=
  if h : 0 < ‖x.val‖ then annulusBoundary 0 le_rfl ⟨x, h⟩ else graphBoundaryNeg

variable {V J : Type} (r : BoundaryFamily J (Fin 1 → ℝ) → V)

def graphSnap : DiskAttachment r → V
  | .inl v => v
  | .inr d => r ⟨d.val.1, graphSnapBoundary d.val.2⟩

theorem graphSnap_of_mem_vertexStar {v : V} {z : DiskAttachment r}
    (hz : z ∈ vertexStar r v) : graphSnap r z = v := by
  cases z with
  | inl _ => exact hz
  | inr d => simpa only [graphSnap, graphSnapBoundary, dif_pos hz.1] using Set.mem_singleton_iff.mp hz.2

variable [TopologicalSpace V]

def graphCellMap (j : J) : C(GraphBall, DiskAttachment r) :=
  ⟨fun x => cell r (boundaryFamilyInclusion J (Fin 1 → ℝ)) ⟨j, x⟩,
    (cell_continuous r _).comp continuous_sigmaMk⟩

theorem graphCellMap_interior (j : J) (x : OpenNormBall (Fin 1 → ℝ)) :
    graphCellMap r j ⟨x.val, x.property.le⟩ = openDiskMap r j x := by
  exact cell_of_not_mem r _ ⟨j, ⟨x.val, x.property.le⟩⟩ fun h =>
    (ne_of_lt x.property) ((boundaryFamilyInclusion_range J (Fin 1 → ℝ) _).mp h)

def graphOpenPath (j : J) (x y : OpenNormBall (Fin 1 → ℝ))
    (P : Path (⟨x.val, x.property.le⟩ : GraphBall) ⟨y.val, y.property.le⟩) :
    Path (openDiskMap r j x) (openDiskMap r j y) :=
  (P.map (graphCellMap r j).continuous).cast (graphCellMap_interior r j x).symm
    (graphCellMap_interior r j y).symm

def graphConnector (z : DiskAttachment r) :
    Path z (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (graphSnap r z)) :=
  match z with
  | .inl _ => Path.refl _
  | .inr d =>
      ((graphBallSegment d.val.2 (unitBoundaryInclusion _ (graphSnapBoundary d.val.2))).map
        (graphCellMap r d.val.1).continuous).cast
          (cell_of_not_mem r _ d.val d.property).symm
          (cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J _).injective
            ⟨d.val.1, graphSnapBoundary d.val.2⟩).symm

theorem graphConnector_range_vertexStar (hr : Continuous r) {v : V}
    {z : DiskAttachment r} (hz : z ∈ vertexStar r v) :
    Set.range (graphConnector r z) ⊆ vertexStar r v := by
  rintro _ ⟨t, rfl⟩
  have hrad : graphConnector r z t =
      radialCoreHomotopy r hr (t, ⟨z, vertexStar_subset_core r v hz⟩) := by
    cases z with
    | inl _ => rfl
    | inr d =>
      refine congrArg (cell r (boundaryFamilyInclusion J (Fin 1 → ℝ)) ∘ Sigma.mk d.val.1)
        (Subtype.ext ?_)
      change Path.segment d.val.2.val (graphSnapBoundary d.val.2).val t =
        ((1 - (t : ℝ)) + (t : ℝ) / ‖d.val.2.val‖) • d.val.2.val
      rw [Path.segment_apply, AffineMap.lineMap_apply_module, graphSnapBoundary, dif_pos hz.1]
      change (1 - (t : ℝ)) • d.val.2.val + (t : ℝ) • (‖d.val.2.val‖⁻¹ • d.val.2.val) = _
      rw [smul_smul, add_smul, div_eq_mul_inv]
  rw [hrad]
  exact radialCoreHomotopy_mem_oldCollar r hr t _ {v} hz

def graphBoundaryPath (j : J) (a b : UnitBoundary (Fin 1 → ℝ))
    (p : Path (unitBoundaryInclusion _ a) (unitBoundaryInclusion _ b)) :
    Path (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (r ⟨j, a⟩))
      (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (r ⟨j, b⟩)) :=
  (p.map (graphCellMap r j).continuous).cast
    (cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J _).injective ⟨j, a⟩).symm
    (cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J _).injective ⟨j, b⟩).symm

theorem graphBoundaryPath_isWord (j : J) (a b : UnitBoundary (Fin 1 → ℝ))
    (p : Path (unitBoundaryInclusion _ a) (unitBoundaryInclusion _ b)) :
    IsWord (graphSrc r) (graphTgt r) (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)))
      (graphEdgePath r) (graphBoundaryPath r j a b p) := by
  letI := graphBall_simplyConnected
  let ce : Path (unitBoundaryInclusion _ graphBoundaryNeg)
      (unitBoundaryInclusion _ graphBoundaryPos) :=
    ⟨⟨graphDiskHomeomorph, graphDiskHomeomorph.continuous⟩,
      graphDiskHomeomorph_zero, graphDiskHomeomorph_one⟩
  by_cases hab : a = b
  · subst b
    refine ⟨[], rfl, ?_⟩
    have h' : Path.Homotopic (graphBoundaryPath r j a a p)
        (graphBoundaryPath r j a a (Path.refl _)) :=
      ((SimplyConnectedSpace.paths_homotopic p (Path.refl _)).map (graphCellMap r j)).pathCast _ _
    rwa [show graphBoundaryPath r j a a (Path.refl _) = Path.refl _ from
      Path.ext (funext fun _ => cell_boundary r _
        (boundaryFamilyInclusion_isClosedEmbedding J _).injective ⟨j, a⟩)] at h'
  · rcases graphBoundary_cases a with rfl | rfl <;>
      rcases graphBoundary_cases b with rfl | rfl
    · exact absurd rfl hab
    · refine ⟨[(j, true)], ⟨rfl, rfl⟩, ?_⟩
      have h' : Path.Homotopic (graphBoundaryPath r j graphBoundaryNeg graphBoundaryPos p)
          (graphEdgePath r j) :=
        ((SimplyConnectedSpace.paths_homotopic p ce).map (graphCellMap r j)).pathCast _ _
      exact h'.trans (Path.Homotopic.trans_refl (graphEdgePath r j)).symm
    · refine ⟨[(j, false)], ⟨rfl, rfl⟩, ?_⟩
      have h' : Path.Homotopic (graphBoundaryPath r j graphBoundaryPos graphBoundaryNeg p)
          (graphEdgePath r j).symm :=
        ((SimplyConnectedSpace.paths_homotopic p ce.symm).map (graphCellMap r j)).pathCast _ _
      exact h'.trans (Path.Homotopic.trans_refl (graphEdgePath r j).symm).symm
    · exact absurd rfl hab

theorem graph_isWord_local_edge (j : J) {x y : DiskAttachment r}
    (p : Path x y) (hp : Set.range p ⊆ openDisk r j) :
    IsWord (graphSrc r) (graphTgt r) (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)))
      (graphEdgePath r) (((graphConnector r x).symm.trans p).trans (graphConnector r y)) := by
  obtain ⟨x, rfl⟩ := hp p.source_mem_range
  obtain ⟨y, rfl⟩ := hp p.target_mem_range
  let e := (openDiskMap_isOpenEmbedding r j).isEmbedding.toHomeomorph
  let Q : Path (e x) (e y) :=
    ⟨⟨fun t => ⟨p t, hp ⟨t, rfl⟩⟩, p.continuous.subtype_mk _⟩,
      Subtype.ext p.source, Subtype.ext p.target⟩
  let incl : C(OpenNormBall (Fin 1 → ℝ), GraphBall) :=
    ⟨fun z => ⟨z.val, z.property.le⟩, continuous_subtype_val.subtype_mk _⟩
  let P := ((Q.map e.symm.continuous).cast (e.symm_apply_apply x).symm
    (e.symm_apply_apply y).symm).map incl.continuous
  have hP : graphOpenPath r j x y P = p := Path.ext (funext fun t => by
    change graphCellMap r j ⟨(e.symm (Q t)).val, (e.symm (Q t)).property.le⟩ = p t
    rw [graphCellMap_interior]
    exact congrArg Subtype.val (e.apply_symm_apply (Q t)))
  rw [← hP]
  let a : GraphBall := ⟨x.val, x.property.le⟩
  let b : GraphBall := ⟨y.val, y.property.le⟩
  let A := graphSnapBoundary a
  let B := graphSnapBoundary b
  let R := ((graphBallSegment a (unitBoundaryInclusion _ A)).symm.trans P).trans
    (graphBallSegment b (unitBoundaryInclusion _ B))
  have h := graphBoundaryPath_isWord r j A B R
  rwa [show graphBoundaryPath r j A B R =
    (((graphConnector r (openDiskMap r j x)).symm.trans (graphOpenPath r j x y P)).trans
      (graphConnector r (openDiskMap r j y))) from Path.ext (funext fun t => by
    simp only [graphBoundaryPath, R, graphOpenPath, Path.cast_coe,
      Path.map_coe, Function.comp_apply, Path.trans_apply, Path.symm_apply]
    split_ifs <;> rfl)] at h

theorem graph_path_isWord [DiscreteTopology V] (hr : Continuous r) (v w : V)
    (p : Path (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) v)
      (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) w)) :
    IsWord (graphSrc r) (graphTgt r) (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)))
      (graphEdgePath r) p := by
  let U : V ⊕ J → Set (DiskAttachment r) := Sum.elim (vertexStar r) (openDisk r)
  have h := isWord_of_open_cover (graphSrc r) (graphTgt r)
    (old r (boundaryFamilyInclusion J (Fin 1 → ℝ))) (graphEdgePath r) U
    (by rintro (v | j); exact vertexStar_isOpen r hr v; exact openDisk_isOpen r j)
    (by rintro (v | d) _
        · exact Set.mem_iUnion.mpr ⟨.inl v, rfl⟩
        · exact Set.mem_iUnion.mpr ⟨.inr d.val.1, ⟨⟨d.val.2.val, lt_of_le_of_ne d.val.2.property
            fun h => d.property ((boundaryFamilyInclusion_range J _ _).mpr h)⟩, rfl⟩⟩)
    (graphSnap r) (graphConnector r)
    (by rintro (v | j) x y p hp
        · have hx := hp p.source_mem_range; have hy := hp p.target_mem_range
          refine ⟨[], (graphSnap_of_mem_vertexStar r hx).trans
            (graphSnap_of_mem_vertexStar r hy).symm,
            homotopic_of_within_simplyConnected (vertexStar r v) (vertexStar_simplyConnected r hr v)
              _ _ (range_trans_subset _ _ (range_trans_subset _ _
                (range_symm_subset _ (graphConnector_range_vertexStar r hr hx)) hp)
                (graphConnector_range_vertexStar r hr hy)) ?_⟩
          rintro _ ⟨_, rfl⟩; exact graphSnap_of_mem_vertexStar r hx
        · exact graph_isWord_local_edge r j p hp) p
  exact h.of_homotopic (((Path.Homotopic.refl_trans p).hcomp (Path.Homotopic.refl _)
    |>.trans (Path.Homotopic.trans_refl p)).symm)

theorem graphCx_isConnected [DiscreteTopology V] (hr : Continuous r)
    [PathConnectedSpace (DiskAttachment r)] : Comb.IsConnected (graphCx r) := by
  intro v w
  obtain ⟨p⟩ := PathConnectedSpace.joined
    (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) v)
    (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) w)
  obtain ⟨l, hl, _⟩ := graph_path_isWord r hr v w p
  exact ⟨l, hl⟩
