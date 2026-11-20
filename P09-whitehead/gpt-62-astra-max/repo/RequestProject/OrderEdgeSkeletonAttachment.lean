module


public import RequestProject.OrderTriangleSkeletonAttachment
public import RequestProject.OrderNerveAffineEdgePath

@[expose] public section

/-! Explicitly oriented graph disks for the genuine first skeleton of
an order realization. Vertex labels are the actual zero-skeleton points;
edges are the strict order edges. The comparison fixes every vertex and
reads each edge in its prescribed order. Pending final Lean verification. -/

noncomputable section
open scoped Classical unitInterval Topology
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.OrderEdgeAttachment
open RelativeAttachment ClassicalSkeletonAttachment ClassicalGraphModel
open OrderTriangleAttachment CategoryTheory Topology

def intervalSimplexHomeomorph : I ≃ₜ stdSimplex ℝ (Fin 2) where
  toFun t := ⟨![1 - t, t], by
    constructor
    · intro i
      fin_cases i
      · aesop
      · exact t.property.1
    · simp⟩
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

theorem edgeDiskSimplexHomeomorph_positive_iff (x : ClosedUnitBall (Fin 1 → ℝ)) :
    (∀ i, 0 < (edgeDiskSimplexHomeomorph x).val i) ↔ ‖x.val‖ < 1 := by
  rw [finOne_norm, abs_lt]
  constructor
  · intro h
    have h₀ : 0 < 1 - (x.val 0 + 1) / 2 := h 0
    have h₁ : 0 < (x.val 0 + 1) / 2 := h 1
    constructor <;> linarith
  · rintro ⟨hl, hu⟩ i
    fin_cases i
    · change 0 < 1 - (x.val 0 + 1) / 2
      linarith
    · change 0 < (x.val 0 + 1) / 2
      linarith

def edgeDiskReparametrization :=
  edgeDiskSimplexHomeomorph.trans (simplexNormDiskHomeomorph 1)

theorem edgeDiskReparametrization_interior (x : ClosedUnitBall (Fin 1 → ℝ)) :
    ‖(edgeDiskReparametrization x).val‖ < 1 ↔ ‖x.val‖ < 1 :=
  (simplexNormDiskHomeomorph_positive_iff 1 _).symm.trans
    (edgeDiskSimplexHomeomorph_positive_iff x)

def edgeBoundaryReparametrization : C(UnitBoundary (Fin 1 → ℝ), UnitBoundary (Fin 1 → ℝ)) where
  toFun z := ⟨(edgeDiskReparametrization (unitBoundaryInclusion _ z)).val, by
    apply le_antisymm (edgeDiskReparametrization _).property
    apply le_of_not_gt
    intro h
    have h' := (edgeDiskReparametrization_interior _).mp h
    change ‖z.val‖ < 1 at h'
    simp_all [z.property]⟩
  continuous_toFun := by
    fun_prop

variable (P : Type) [PartialOrder P]

abbrev Vertices := SkeletonCarrier (Set.univ : Set (orderNerveRealization P)) 1

def vertexEquiv :=
  (vertexNerveEquiv P).trans (ClassicalCW.zeroCellEquiv (X := orderNerveRealization P))

theorem vertexEquiv_val (p : P) : (vertexEquiv P p).val = orderNerveRealizationVertex p := by
  change Topology.CWComplex.map (C := (Set.univ : Set _)) 0
    _ ![] = _
  have he : (simplexNormDiskHomeomorph 0 (default : stdSimplex ℝ (Fin 1))).val = ![] :=
    Subsingleton.elim _ _
  rw [← he, characteristicDisk_simplex]
  apply congrArg _
  exact Subsingleton.elim _ _

variable (e : StrictOrdEdge P)

def edgeDiskMap :
    C(ClosedUnitBall (Fin 1 → ℝ), orderNerveRealization P) where
  toFun x := orderNerveRealizationSimplex P _
    _
  continuous_toFun := (orderNerveRealizationSimplex P (strictEdgeNerveEquiv P e).val).hom.continuous.comp
    (continuous_uliftUp.comp
      ((TopologicalSingular.simplexCoordinates 1).symm.continuous.comp edgeDiskSimplexHomeomorph.continuous))

variable (x : ClosedUnitBall (Fin 1 → ℝ))

theorem edgeDiskMap_characteristic :
    Topology.CWComplex.map (C := Set.univ) 1
      (strictEdgeNerveEquiv P e) (edgeDiskReparametrization x).val = edgeDiskMap P e x :=
  by apply characteristicDisk_simplex

theorem edgeDiskMap_coordinates (p : P) :
    orderNerveRealizationCoordinates P (edgeDiskMap P e x) p =
      (1 - (oneBallIntervalHomeomorph x)) * (if e.val.1 = p then 1 else 0) +
      (oneBallIntervalHomeomorph x) * (if e.val.2 = p then 1 else 0) := by
  change orderNerveRealizationCoordinates P
    (orderNerveRealizationSimplex P (strictEdgeNerveEquiv P e).val
      (ULift.up ((TopologicalSingular.simplexCoordinates 1).symm (edgeDiskSimplexHomeomorph x)))) p = _
  rw [orderNerveRealizationCoordinates_simplex]
  simp only [orderNerveAffineSimplex, ContinuousMap.coe_mk,
    TopologicalSingular.simplexCoordinates_symm_weights_apply]
  rw [Fin.sum_univ_two]; rfl

theorem edgeDiskMap_edgePath (t : I) :
    edgeDiskMap P e (graphDiskHomeomorph t) = orderNerveAffineEdgePath e.property.le t := by
  apply orderNerveRealizationCoordinates_injective P
  funext p
  rw [edgeDiskMap_coordinates, orderNerveAffineEdgePath_coordinates]
  have he : oneBallIntervalHomeomorph (graphDiskHomeomorph t) = t := by
    simp [oneBallIntervalHomeomorph, graphDiskHomeomorph]
  simp [he]

def graphAttaching : C(BoundaryFamily (StrictOrdEdge P) (Fin 1 → ℝ), Vertices P) where
  toFun := reparametrizedAttaching
    (skeletonAttachingMap Set.univ 1)
    (strictEdgeNerveEquiv P) (fun _ => edgeBoundaryReparametrization)
  continuous_toFun := by
    fun_prop

variable (e : StrictOrdEdge P)

theorem graphAttaching_val (z : UnitBoundary (Fin 1 → ℝ)) :
    (graphAttaching P ⟨e, z⟩).val = edgeDiskMap P e (unitBoundaryInclusion _ z) :=
  by apply edgeDiskMap_characteristic

theorem graphAttaching_source :
    graphSrc (graphAttaching P) e = vertexEquiv P e.val.1 := by
  apply Subtype.ext
  rw [graphSrc, graphAttaching_val, vertexEquiv_val, ← graphDiskHomeomorph_zero,
    edgeDiskMap_edgePath] <;> simp_all

theorem graphAttaching_target :
    graphTgt (graphAttaching P) e = vertexEquiv P e.val.2 := by
  apply Subtype.ext
  rw [graphTgt, graphAttaching_val, vertexEquiv_val, ← graphDiskHomeomorph_one,
    edgeDiskMap_edgePath] <;> simp_all

def edgeReparametrizationHomeomorph :
    DiskAttachment (graphAttaching P) ≃ₜ
      DiskAttachment (skeletonAttachingMap (Set.univ : Set (orderNerveRealization P)) 1) :=
  diskAttachmentQuotientReparametrization
    _
    _ (fun _ => edgeDiskReparametrization.toContinuousMap)
    (fun _ => edgeBoundaryReparametrization) (fun _ _ => rfl)
    (fun _ => edgeDiskReparametrization.isQuotientMap)
    (fun _ => edgeDiskReparametrization_interior)
    (fun _ _ _ _ _ h => edgeDiskReparametrization.injective h)

def graphHomeomorph :=
  (edgeReparametrizationHomeomorph P).trans
    (skeletonAttachmentHomeomorph Set.univ 1)

@[simp] theorem graphHomeomorph_old (v : Vertices P) :
    (graphHomeomorph P (old (graphAttaching P) (boundaryFamilyInclusion (StrictOrdEdge P) _) v)).val =
      v.val := rfl

variable (e : StrictOrdEdge P)

@[simp] theorem graphHomeomorph_cell (x : ClosedUnitBall (Fin 1 → ℝ)) :
    (graphHomeomorph P (cell (graphAttaching P) (boundaryFamilyInclusion (StrictOrdEdge P) _) ⟨e, x⟩)).val =
      edgeDiskMap P e x := by
  change (skeletonAttachmentHomeomorph Set.univ 1
    (edgeReparametrizationHomeomorph P _)).val = _
  rw [edgeReparametrizationHomeomorph]
  erw [diskAttachmentQuotientReparametrization_cell]
  rw [skeletonAttachmentHomeomorph_cell]
  apply edgeDiskMap_characteristic

theorem graphHomeomorph_edgePath (t : I) :
    (graphHomeomorph P (graphEdgePath (graphAttaching P) e t)).val =
      orderNerveAffineEdgePath e.property.le t :=
  (graphHomeomorph_cell P e _).trans (edgeDiskMap_edgePath P e t)

end FiniteChains.Comb.OrderEdgeAttachment
