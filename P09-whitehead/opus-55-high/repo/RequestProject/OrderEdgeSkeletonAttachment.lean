import RequestProject.HomeomorphContinuousMap
import RequestProject.OrderTriangleSkeletonAttachment
import RequestProject.ClassicalCWGraphCoordinates
import RequestProject.OrderNerveAffineEdgePath
import RequestProject.Tac


/-! Explicitly oriented graph disks for the genuine first skeleton of
an order realization. Vertex labels are the actual zero-skeleton points;
edges are the strict order edges. The comparison fixes every vertex and
reads each edge in its prescribed order. Pending final Lean verification. -/

noncomputable section
open scoped Classical unitInterval Topology
bwd

namespace FiniteChains.Comb.OrderEdgeAttachment
open RelativeAttachment ClassicalSkeletonAttachment ClassicalGraphModel
open OrderTriangleAttachment CategoryTheory Topology

def intervalSimplexHomeomorph : I ≃ₜ stdSimplex ℝ (Fin 2) where
  toFun t := ⟨![1 - (t : ℝ), (t : ℝ)], by
    constructor
    · intro i
      fin_cases i <;> aesop
    simp⟩
  invFun z := ⟨z.val 1, z.property.1 1, by
    have hs := (Fin.sum_univ_two z.val).symm.trans z.property.2
    linarith [z.property.1 0]⟩
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext
    funext i
    have hs := (Fin.sum_univ_two z.val).symm.trans z.property.2
    fin_cases i
    · change 1 - z.val 1 = z.val 0
      linarith
    · rfl
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_apply 1).comp continuous_subtype_val

def edgeDiskSimplexHomeomorph :=
  oneBallIntervalHomeomorph.trans intervalSimplexHomeomorph

theorem edgeDiskSimplexHomeomorph_positive_iff x :
    (∀ i, 0 < (edgeDiskSimplexHomeomorph x).val i) ↔ ‖x.val‖ < 1 := by
  rw [finOne_norm, abs_lt]
  constructor
  · intro h
    have h₀ : 0 < 1 - (x.val 0 + 1) / 2 := h 0
    have h₁ : 0 < (x.val 0 + 1) / 2 := h 1
    grind
  · rintro ⟨hl, hu⟩ i
    fin_cases i
    · change 0 < 1 - (x.val 0 + 1) / 2
      linarith
    · change 0 < (x.val 0 + 1) / 2
      linarith

def edgeDiskReparametrization :=
  edgeDiskSimplexHomeomorph.trans (simplexNormDiskHomeomorph 1)

theorem edgeDiskReparametrization_interior x :
    ‖(edgeDiskReparametrization x).val‖ < 1 ↔ ‖x.val‖ < 1 :=
  (simplexNormDiskHomeomorph_positive_iff 1 _).symm.trans
    (edgeDiskSimplexHomeomorph_positive_iff x)

def edgeBoundaryReparametrization : C(UnitBoundary (Fin 1 → ℝ), UnitBoundary (Fin 1 → ℝ)) where
  toFun z := ⟨(edgeDiskReparametrization (unitBoundaryInclusion _ z)).val, by
    apply le_antisymm (edgeDiskReparametrization (unitBoundaryInclusion _ z)).property
    apply le_of_not_gt
    intro h
    have h' := (edgeDiskReparametrization_interior _).mp h
    change ‖z.val‖ < 1 at h'
    grind⟩
  continuous_toFun := by
    fun_prop

variable (P : Type) [PartialOrder P]

abbrev Vertices := SkeletonCarrier (Set.univ : Set (orderNerveRealization P)) 1

def vertexEquiv : P ≃ Vertices P :=
  (vertexNerveEquiv P).trans (ClassicalCW.zeroCellEquiv (X := orderNerveRealization P))

theorem vertexEquiv_val p : (vertexEquiv P p).val = orderNerveRealizationVertex p := by
  change Topology.CWComplex.map (C := (Set.univ : Set (orderNerveRealization P))) 0
    (vertexNerveEquiv P p) ![] = _
  have he : (simplexNormDiskHomeomorph 0 (default : stdSimplex ℝ (Fin 1))).val = ![] :=
    Subsingleton.elim _ _
  rw [← he, characteristicDisk_simplex]
  apply congrArg _
  exact Subsingleton.elim _ _

def edgeDiskMap (e : StrictOrdEdge P) :
    C(ClosedUnitBall (Fin 1 → ℝ), orderNerveRealization P) where
  toFun x := orderNerveRealizationSimplex P (strictEdgeNerveEquiv P e).val
    (ULift.up ((TopologicalSingular.simplexCoordinates 1).symm (edgeDiskSimplexHomeomorph x)))
  continuous_toFun := (orderNerveRealizationSimplex P (strictEdgeNerveEquiv P e).val).hom.continuous.comp
    (continuous_uliftUp.comp
      ((TopologicalSingular.simplexCoordinates 1).symm.continuous.comp edgeDiskSimplexHomeomorph.continuous))

theorem edgeDiskMap_characteristic e x :
    Topology.CWComplex.map (C := Set.univ) 1
      (strictEdgeNerveEquiv P e) (edgeDiskReparametrization x).val = edgeDiskMap P e x :=
  characteristicDisk_simplex P 1 _ _

theorem edgeDiskMap_coordinates e x p :
    orderNerveRealizationCoordinates P (edgeDiskMap P e x) p =
      (1 - (oneBallIntervalHomeomorph x)) * (if e.val.1 = p then 1 else 0) +
      (oneBallIntervalHomeomorph x) * (if e.val.2 = p then 1 else 0) := by
  change orderNerveRealizationCoordinates P
    (orderNerveRealizationSimplex P (strictEdgeNerveEquiv P e).val
      (ULift.up ((TopologicalSingular.simplexCoordinates 1).symm (edgeDiskSimplexHomeomorph x)))) p = _
  rw [orderNerveRealizationCoordinates_simplex]
  simp [orderNerveAffineSimplex, ContinuousMap.coe_mk,
    TopologicalSingular.simplexCoordinates_symm_weights_apply]
  aesop

theorem edgeDiskMap_edgePath e t :
    edgeDiskMap P e (graphDiskHomeomorph t) = orderNerveAffineEdgePath e.property.le t := by
  apply orderNerveRealizationCoordinates_injective P
  funext p
  rw [edgeDiskMap_coordinates, orderNerveAffineEdgePath_coordinates]
  have he : oneBallIntervalHomeomorph (graphDiskHomeomorph t) = t := by
    simp [oneBallIntervalHomeomorph, graphDiskHomeomorph]
  simp_all

def graphAttaching : C(BoundaryFamily (StrictOrdEdge P) (Fin 1 → ℝ), Vertices P) where
  toFun := reparametrizedAttaching
    (skeletonAttachingMap (Set.univ : Set (orderNerveRealization P)) 1)
    (strictEdgeNerveEquiv P) (fun _ => edgeBoundaryReparametrization)
  continuous_toFun := by
    fun_prop

theorem graphAttaching_val e z :
    (graphAttaching P ⟨e, z⟩).val = edgeDiskMap P e (unitBoundaryInclusion _ z) :=
  edgeDiskMap_characteristic P e _

theorem graphAttaching_source e :
    graphSrc (graphAttaching P) e = vertexEquiv P e.val.1 := by
  grind [graphSrc, graphAttaching_val, vertexEquiv_val, ← graphDiskHomeomorph_zero, edgeDiskMap_edgePath]

theorem graphAttaching_target e :
    graphTgt (graphAttaching P) e = vertexEquiv P e.val.2 := by
  grind [graphTgt, graphAttaching_val, vertexEquiv_val, ← graphDiskHomeomorph_one, edgeDiskMap_edgePath]

def edgeReparametrizationHomeomorph :
    DiskAttachment (graphAttaching P) ≃ₜ
      DiskAttachment (skeletonAttachingMap (Set.univ : Set (orderNerveRealization P)) 1) :=
  diskAttachmentQuotientReparametrization
    (skeletonAttachingMap (Set.univ : Set (orderNerveRealization P)) 1)
    (strictEdgeNerveEquiv P) (fun _ => edgeDiskReparametrization.toContinuousMap)
    (fun _ => edgeBoundaryReparametrization) (by aesop)
    (fun _ => edgeDiskReparametrization.isQuotientMap)
    (fun _ => edgeDiskReparametrization_interior)
    (by simp)

def graphHomeomorph : DiskAttachment (graphAttaching P) ≃ₜ OrderTriangleAttachment.OneSkeleton P :=
  (edgeReparametrizationHomeomorph P).trans
    (skeletonAttachmentHomeomorph _ 1)

@[simp] theorem graphHomeomorph_old v :
    (graphHomeomorph P (old (graphAttaching P) (boundaryFamilyInclusion (StrictOrdEdge P) _) v)).val =
      v.val := rfl

@[simp] theorem graphHomeomorph_cell e x :
    (graphHomeomorph P (cell (graphAttaching P) (boundaryFamilyInclusion (StrictOrdEdge P) _) ⟨e, x⟩)).val =
      edgeDiskMap P e x := by
  change (skeletonAttachmentHomeomorph _ 1
    (edgeReparametrizationHomeomorph P (cell _ _ ⟨e, x⟩))).val = _
  erw [diskAttachmentQuotientReparametrization_cell]
  rw [skeletonAttachmentHomeomorph_cell]
  exact edgeDiskMap_characteristic P e x

theorem graphHomeomorph_edgePath e t :
    (graphHomeomorph P (graphEdgePath (graphAttaching P) e t)).val =
      orderNerveAffineEdgePath e.property.le t :=
  (graphHomeomorph_cell P e _).trans (edgeDiskMap_edgePath P e t)
