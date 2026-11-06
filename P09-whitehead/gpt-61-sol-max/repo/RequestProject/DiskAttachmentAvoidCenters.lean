import Mathlib.Tactic

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
  have he : normBallHomeomorph (E := E) '' ({0} : Set E)ᶜ =
      {x : OpenNormBall E | x.val ≠ 0} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ heq
      have hy0 : y = 0 := (normBallHomeomorph (E := E)).injective
        (Subtype.ext (heq.trans normBallHomeomorph_zero.symm))
      exact hy (Set.mem_singleton_iff.mpr hy0)
    · intro hx
      refine ⟨(normBallHomeomorph (E := E)).symm x, ?_,
        (normBallHomeomorph (E := E)).apply_symm_apply x⟩
      intro hzero
      have hz : (normBallHomeomorph (E := E)).symm x = 0 := hzero
      have h := congrArg (fun z => (normBallHomeomorph (E := E) z).val) hz
      
      rw [(normBallHomeomorph (E := E)).apply_symm_apply, normBallHomeomorph_zero] at h
      exact hx h
  rwa [he] at hp

variable (r : BoundaryFamily J E → X)
  (j : J)
def openDiskMap    :=
  fresh r (boundaryFamilyInclusion J E) ∘ interiorDiskPoint j

omit [NormedSpace ℝ E] in
abbrev openDiskMap_isOpenEmbedding    :=
  (fresh_isOpenEmbedding r _ (boundaryFamilyInclusion_isClosedEmbedding J E).isClosed_range).comp
    (interiorDiskPoint_isOpenEmbedding j)

def openDisk    :=
  Set.range (openDiskMap r j)

def puncturedAttachment   :=
  oldCollar r 0 le_rfl Set.univ

omit [NormedSpace ℝ E] in
abbrev openDisk_isOpen    :=
  (FiniteChains.RelativeAttachment.openDiskMap_isOpenEmbedding r j).isOpen_range

omit [NormedSpace ℝ E] [TopologicalSpace X] in
theorem openDisk_pairwiseDisjoint  :
    Pairwise (fun i j => Disjoint (openDisk r i) (openDisk r j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, he⟩
  have h  := Sum.inr_injective he
  exact hij (congrArg (fun d => d.val.1) h).symm

omit [TopologicalSpace X] in
theorem puncturedAttachment_union_openDisk  :
    puncturedAttachment r ∪ ⋃ j, openDisk r j = Set.univ := by
  apply Set.eq_univ_of_forall
  rintro (x | d)
  · exact Or.inl trivial
  · apply Or.inr
    have hd  := lt_of_le_of_ne d.val.2.property
      (fun h => d.property ((boundaryFamilyInclusion_range J E _).mpr h))
    exact Set.mem_iUnion.mpr ⟨d.val.1, ⟨⟨d.val.2.val, hd⟩, rfl⟩⟩

abbrev puncturedAttachment_isOpen  (hr : Continuous r)  :=
  FiniteChains.RelativeAttachment.oldCollar_isOpen r hr 0 le_rfl zero_lt_one Set.univ isOpen_univ

theorem openDisk_simplyConnected   :
    IsSimplyConnected (openDisk r j) := by
  letI : ContractibleSpace (Metric.ball (0 : E) 1) := Metric.contractibleSpace_ball zero_lt_one
  let e : Metric.ball (0 : E) 1 ≃ₜ OpenNormBall E := Homeomorph.setCongr (by
    aesop)
  letI  := e.symm.toHomotopyEquiv.simplyConnectedSpace
  exact (openDiskMap_isOpenEmbedding r j).isEmbedding.toHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace

omit [TopologicalSpace X] in
theorem puncturedAttachment_inter_openDisk   :
    puncturedAttachment r ∩ openDisk r j =
      openDiskMap r j '' {x : OpenNormBall E | x.val ≠ 0} := by
  ext z
  constructor
  · rintro ⟨hz, ⟨x, rfl⟩⟩
    obtain ⟨hx, _⟩ := hz
    refine ⟨x, ?_, rfl⟩
    exact norm_pos_iff.mp hx
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨norm_pos_iff.mpr hx, trivial⟩, ⟨x, rfl⟩⟩

theorem puncturedAttachment_inter_pathConnected 
    (hdim : 1 < Module.rank ℝ E) (j : J) :
    IsPathConnected (puncturedAttachment r ∩ openDisk r j) := by
  rw [puncturedAttachment_inter_openDisk]
  exact (puncturedNormBall_pathConnected hdim).image (openDiskMap_isOpenEmbedding r j).continuous

/-- The path and its homotopy are built in the actual attachment; neither
an abstract presentation nor a surjectivity premise is used. -/
abbrev diskAttachment_path_avoid_centers  (hr : Continuous r)
    (hdim : 1 < Module.rank ℝ E) {x y : DiskAttachment r}
    (hx : x ∈ puncturedAttachment r) (hy : y ∈ puncturedAttachment r) (p : Path x y)  :=
  FiniteChains.PathReplacement.path_into_core (FiniteChains.RelativeAttachment.puncturedAttachment r)
    (FiniteChains.RelativeAttachment.openDisk r) (FiniteChains.RelativeAttachment.puncturedAttachment_union_openDisk r)
    (FiniteChains.RelativeAttachment.openDisk_pairwiseDisjoint r)
    (FiniteChains.RelativeAttachment.puncturedAttachment_inter_pathConnected r hdim)
    (FiniteChains.RelativeAttachment.openDisk_simplyConnected r)
    (FiniteChains.RelativeAttachment.puncturedAttachment_isOpen r hr) (FiniteChains.RelativeAttachment.openDisk_isOpen r)
    hx hy p

end FiniteChains.RelativeAttachment
