import RequestProject.ClassicalCellAttachmentHausdorff
import RequestProject.OpenCoverCorePaths
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.LinearAlgebra.Dimension.Constructions


/-! Actual path cellularization away from the centers of arbitrary families
of attached disks of dimension at least two. All chart and intersection
hypotheses of the open-cover replacement lemma are proved here.
Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval
open Set Topology Metric

namespace FiniteChains.RelativeAttachment

variable {E X J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X]

abbrev OpenNormBall (E : Type) [Norm E] := {x : E // ‖x‖ < 1}

def normBallHomeomorph : E ≃ₜ OpenNormBall E :=
  Homeomorph.unitBall.trans (Homeomorph.setCongr (by
    aesop))

theorem normBallHomeomorph_zero : (normBallHomeomorph (E := E) 0).val = 0 :=
  Homeomorph.coe_unitBall_apply_zero

theorem puncturedNormBall_pathConnected (hdim : 1 < Module.rank ℝ E) :
    IsPathConnected {x : OpenNormBall E | x.val ≠ 0} := by
  have hp := (isPathConnected_compl_singleton_of_one_lt_rank hdim (0 : E)).image
    (normBallHomeomorph (E := E)).continuous
  have he : normBallHomeomorph (E := E) '' ({0})ᶜ =
      {x : OpenNormBall E | x.val ≠ 0} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ heq
      have hy0 := (normBallHomeomorph (E := E)).injective
        (Subtype.ext (heq.trans normBallHomeomorph_zero.symm))
      simp_all
    · intro hx
      refine ⟨(normBallHomeomorph (E := E)).symm x, ?_,
        by simp⟩
      grind [(normBallHomeomorph (E := E)).apply_symm_apply, normBallHomeomorph_zero]
  simp_all

def openDiskMap (r : BoundaryFamily J E → X) (j : J) : OpenNormBall E → DiskAttachment r :=
  fresh r _ ∘ interiorDiskPoint j

omit [NormedSpace ℝ E] in
theorem openDiskMap_isOpenEmbedding (r : BoundaryFamily J E → X) (j : J) :
    IsOpenEmbedding (openDiskMap r j) :=
  (fresh_isOpenEmbedding r _ (boundaryFamilyInclusion_isClosedEmbedding J E).isClosed_range).comp
    (interiorDiskPoint_isOpenEmbedding j)

def openDisk (r : BoundaryFamily J E → X) (j : J) :=
  Set.range (openDiskMap r j)

def puncturedAttachment (r : BoundaryFamily J E → X) :=
  oldCollar r 0 le_rfl Set.univ

omit [NormedSpace ℝ E] in
theorem openDisk_isOpen (r : BoundaryFamily J E → X) (j : J) : IsOpen (openDisk r j) :=
  (openDiskMap_isOpenEmbedding r j).isOpen_range

omit [NormedSpace ℝ E] [TopologicalSpace X] in
theorem openDisk_pairwiseDisjoint (r : BoundaryFamily J E → X) :
    Pairwise (fun i j => Disjoint (openDisk r i) (openDisk r j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, he⟩
  have h := Sum.inr_injective he
  exact hij (congrArg (·.val.1) h).symm

omit [TopologicalSpace X] in
theorem puncturedAttachment_union_openDisk (r : BoundaryFamily J E → X) :
    puncturedAttachment r ∪ ⋃ j, openDisk r j = Set.univ := by
  apply Set.eq_univ_of_forall
  rintro (x | d)
  · exact Or.inl trivial
  · apply Or.inr
    have hd := lt_of_le_of_ne d.val.2.property
      (by aesop)
    exact Set.mem_iUnion.mpr ⟨d.val.1, ⟨⟨d.val.2.val, hd⟩, rfl⟩⟩

theorem puncturedAttachment_isOpen (r : BoundaryFamily J E → X) (hr : Continuous r) :
    IsOpen (puncturedAttachment r) :=
  oldCollar_isOpen r hr 0 le_rfl zero_lt_one Set.univ isOpen_univ

theorem openDisk_simplyConnected (r : BoundaryFamily J E → X) j :
    IsSimplyConnected (openDisk r j) := by
  letI : ContractibleSpace (Metric.ball (0 : E) 1) := Metric.contractibleSpace_ball zero_lt_one
  let e : Metric.ball (0 : E) 1 ≃ₜ OpenNormBall E := Homeomorph.setCongr (by
    aesop)
  letI : SimplyConnectedSpace (OpenNormBall E) := e.symm.toHomotopyEquiv.simplyConnectedSpace
  exact (openDiskMap_isOpenEmbedding r j).isEmbedding.toHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace

omit [TopologicalSpace X] in
theorem puncturedAttachment_inter_openDisk (r : BoundaryFamily J E → X) (j : J) :
    puncturedAttachment r ∩ openDisk r j =
      openDiskMap r j '' {x : OpenNormBall E | x.val ≠ 0} := by
  ext z
  constructor
  · rintro ⟨hz, ⟨x, rfl⟩⟩
    cases' hz with hx _
    aesop
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨norm_pos_iff.mpr hx, trivial⟩, ⟨x, rfl⟩⟩

theorem puncturedAttachment_inter_pathConnected (r : BoundaryFamily J E → X)
    (hdim : 1 < Module.rank ℝ E) j :
    IsPathConnected (puncturedAttachment r ∩ openDisk r j) := by
  rw [puncturedAttachment_inter_openDisk]
  exact (puncturedNormBall_pathConnected hdim).image (openDiskMap_isOpenEmbedding r j).continuous

/-- The path and its homotopy are built in the actual attachment; neither
an abstract presentation nor a surjectivity premise is used. -/
theorem diskAttachment_path_avoid_centers (r : BoundaryFamily J E → X) (hr : Continuous r)
    (hdim : 1 < Module.rank ℝ E) {x y}
    (hx : x ∈ puncturedAttachment r) (hy : y ∈ puncturedAttachment r) p :
    ∃ q : Path x y, Set.range q ⊆ puncturedAttachment r ∧ Path.Homotopic p q :=
  PathReplacement.path_into_core _ _
    (puncturedAttachment_union_openDisk r) (openDisk_pairwiseDisjoint r)
    (puncturedAttachment_inter_pathConnected r hdim) (openDisk_simplyConnected r)
    (puncturedAttachment_isOpen r hr) (openDisk_isOpen r) hx hy p
