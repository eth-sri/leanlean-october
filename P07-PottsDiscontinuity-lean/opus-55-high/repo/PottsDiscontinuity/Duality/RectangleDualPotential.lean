/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.RectangleCurlLinearEquiv
public import PottsDiscontinuity.Duality.RectangleFlowDimension
public import PottsDiscontinuity.Duality.NormalizedPotentialSpace

@[expose] public noncomputable section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

section
variable (a : LatticeVertex) (w h : ℕ) (A : Finset (rectanglePrimalEdgeCarrier a w h))
def rectangleDualConfiguration  :
    Configuration (rectangleDualGraph a w h) :=
  Finset.map (rectangleDualGraphEdgeEquiv a w h).toEmbedding
    (rectangleDualComplementEquiv a w h A)

@[simp] theorem mem_rectangleDualConfiguration (e : RectangleDualEdgeCarrier a w h) :
    rectangleDualGraphEdgeEquiv a w h e ∈ rectangleDualConfiguration a w h A ↔
      e.primalEdge ∉ A := by
  simp [rectangleDualConfiguration,
    mem_rectangleDualComplementEquiv]

theorem mem_rectangleDualConfiguration_iff
    (g : (rectangleDualGraph a w h).edgeSet) :
    g ∈ rectangleDualConfiguration a w h A ↔
      ((rectangleDualGraphEdgeEquiv a w h).symm g).primalEdge ∉ A := by
  constructor
  · intro hg
    rcases Finset.mem_map.mp hg with ⟨e, he, hge⟩
    aesop
  · intro hg
    apply Finset.mem_map.mpr
    refine ⟨(rectangleDualGraphEdgeEquiv a w h).symm g, ?_, ?_⟩
    · simp_all
    simp

theorem rectangleDualOpen_adj_iff
    (u v : RectangleDualVertex a w h) :
    (openGraph (rectangleDualGraph a w h) (rectangleDualConfiguration a w h A)).Adj u v ↔
      ∃ e : RectangleDualEdgeCarrier a w h,
        e.primalEdge ∉ A ∧ s(u,v) = rectangleDualCarrierPair a w h e := by
  rw [openGraph_adj, openEdges]
  constructor
  · intro hv
    rcases hv with ⟨g, hg, hgv⟩
    let e := (rectangleDualGraphEdgeEquiv a w h).symm g
    refine ⟨e, ?_, ?_⟩
    · grind [mem_rectangleDualConfiguration_iff]
    · have he : rectangleDualGraphEdgeEquiv a w h e = g := by grind
      have hpair : (rectangleDualGraphEdgeEquiv a w h e : Sym2 _) =
          rectangleDualCarrierPair a w h e := by
        rfl
      simp_all
  · rintro ⟨e, he, huv⟩
    refine ⟨rectangleDualGraphEdgeEquiv a w h e, ?_, ?_⟩
    · simp_all
    tauto
end

section
variable (a : LatticeVertex) (w h : ℕ)
def rectangleDualBaseVertex  :
    RectangleDualVertex a w h :=
  ⟨(a.1 - 1, a.2 - 1), by
    rw [rectangleDualExpanded, mem_latticeRectangle]
    omega⟩

theorem rectangleDualBaseVertex_boundary  :
    (rectangleDualBaseVertex a w h).1 ∈ rectangleDualBoundary a w h := by
  grind [rectangleDualBaseVertex, rectangleDualBoundary, rectangleDualInterior, rectangleDualExpanded]

def rectanglePrimalEdgeBond_mem (e : rectanglePrimalEdgeCarrier a w h) : RectanglePrimalBond a w h :=
  ⟨rectanglePrimalEdgeBond a w h e,
    rectanglePrimalEdgeBond_endpoints_mem_public a w h e⟩

def rectangleDualPotentialExtended (φ : rectangleExteriorPotentialSubmodule a w h) (z : LatticeVertex) : ℝ :=
  if hz : z ∈ rectangleDualExpanded a w h then φ.1 ⟨z, hz⟩ else 0

/-- Zero-exterior potentials whose curl vanishes on every closed primal edge
(the complement of the open primal configuration A). -/
def rectangleDualPotentialCurlKernel (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    Submodule ℝ (rectangleExteriorPotentialSubmodule a w h) where
  carrier := {φ | ∀ e : rectanglePrimalEdgeCarrier a w h, e ∉ A →
    rectanglePotentialCurlMap a w h φ (rectanglePrimalEdgeBond_mem a w h e) = 0}
  zero_mem' := by
    intro φ
    simp
  add_mem' := by
    intro φ ψ hφ hψ e he
    rw [map_add]
    simp [hφ e he, hψ e he]
  smul_mem' := by
    intro c φ hφ e he
    rw [map_smul]
    simp [hφ e he]

theorem rectanglePotentialCurl_zero_iff_dualEnds_eq
    (φ : rectangleExteriorPotentialSubmodule a w h)
    (e : rectanglePrimalEdgeCarrier a w h) :
    rectanglePotentialCurlMap a w h φ (rectanglePrimalEdgeBond_mem a w h e) = 0 ↔
      φ.1 (rectangleDualEdgeSource a w h
        (rectanglePrimalDualEdgeEquiv a w h e)) =
      φ.1 (rectangleDualEdgeTarget a w h
        (rectanglePrimalDualEdgeEquiv a w h e)) := by
  let d := rectanglePrimalDualEdgeEquiv a w h e
  let b := rectanglePrimalEdgeBond a w h e
  have hsrc : d.primalEdge = e := by rfl
  have hs : (rectangleDualEdgeSource a w h d).val = b.faceBase false := by
    simpa [d, hsrc, b] using rectangleDualEdgeSource_faceBase a w h d
  have ht : (rectangleDualEdgeTarget a w h d).val = b.faceBase true := by
    simpa [d, hsrc, b] using rectangleDualEdgeTarget_faceBase a w h d
  have hsource : rectangleExtendedPotential a w h
      (rectanglePotentialAsExterior a w h φ) (b.faceBase false) =
      rectangleDualPotentialExtended a w h φ (rectangleDualEdgeSource a w h d).val := by
    rw [← hs]
    rfl
  have htarget : rectangleExtendedPotential a w h
      (rectanglePotentialAsExterior a w h φ) (b.faceBase true) =
      rectangleDualPotentialExtended a w h φ (rectangleDualEdgeTarget a w h d).val := by
    rw [← ht]
    rfl
  have hsrcval : rectangleDualPotentialExtended a w h φ
      (rectangleDualEdgeSource a w h d).val = φ.1 (rectangleDualEdgeSource a w h d) := by
    change (if hz : (rectangleDualEdgeSource a w h d).val ∈ rectangleDualExpanded a w h
      then φ.1 ⟨(rectangleDualEdgeSource a w h d).val, hz⟩ else 0) = _
    grind
  have htgtval : rectangleDualPotentialExtended a w h φ
      (rectangleDualEdgeTarget a w h d).val = φ.1 (rectangleDualEdgeTarget a w h d) := by
    change (if hz : (rectangleDualEdgeTarget a w h d).val ∈ rectangleDualExpanded a w h
      then φ.1 ⟨(rectangleDualEdgeTarget a w h d).val, hz⟩ else 0) = _
    grind
  change rectangleCurlFlow a w h (rectanglePotentialAsExterior a w h φ) b = 0 ↔ _
  grind [rectangleCurlFlow]
end

section
variable (a : LatticeVertex) (w h : ℕ) (A : Finset (rectanglePrimalEdgeCarrier a w h))
abbrev RectangleDualNormalizedPotentials  :=
  normalizedComponentPotentials (rectangleDualGraph a w h)
    (rectangleDualBoundaryCondition a w h)
    (rectangleDualConfiguration a w h A) (rectangleDualBaseVertex a w h)

theorem rectangleDualNormalized_boundary_zero
    (f : RectangleDualNormalizedPotentials a w h A) (z : RectangleDualVertex a w h)
    (hz : z.1 ∈ rectangleDualBoundary a w h) : f.1.1 z = 0 := by
  have hrel : (rectangleDualBoundaryCondition a w h).partition.r z
      (rectangleDualBaseVertex a w h) := by
    simp_all [rectangleDualBaseVertex_boundary]
  have hcomp := boundary_component (rectangleDualGraph a w h)
    (rectangleDualBoundaryCondition a w h) (rectangleDualConfiguration a w h A) hrel
  have heq := f.1.2 hcomp
  aesop

 theorem rectangleDualNormalized_mem_exterior
    (f : RectangleDualNormalizedPotentials a w h A) :
    f.1.1 ∈ rectangleExteriorPotentialSubmodule a w h := by
  change ∀ z : RectangleDualVertex a w h, z.1 ∈ rectangleDualBoundary a w h → f.1.1 z = 0
  simp_all [rectangleDualNormalized_boundary_zero]

 theorem rectangleDualNormalized_mem_curlKernel
    (f : RectangleDualNormalizedPotentials a w h A) :
    (⟨f.1.1, rectangleDualNormalized_mem_exterior a w h A f⟩ :
      rectangleExteriorPotentialSubmodule a w h) ∈ rectangleDualPotentialCurlKernel a w h A := by
  intro e he
  let d := rectanglePrimalDualEdgeEquiv a w h e
  have hAdj : (openGraph (rectangleDualGraph a w h)
      (rectangleDualConfiguration a w h A)).Adj
      (rectangleDualEdgeSource a w h d) (rectangleDualEdgeTarget a w h d) := by
    apply (rectangleDualOpen_adj_iff a w h A _ _).2
    tauto
  have hlocal := (componentConstant_iff_local (rectangleDualGraph a w h)
    (rectangleDualBoundaryCondition a w h)
    (rectangleDualConfiguration a w h A) f.1.1).mp f.1.2
  have heq := hlocal.1 hAdj
  grind [rectanglePotentialCurl_zero_iff_dualEnds_eq, rectangleDualNormalized_mem_exterior]

/-- The normalized wired dual potentials embed as zero-exterior potentials
whose curl vanishes on every closed primal edge. -/
def rectangleDualNormalizedToCurlKernel  :
    RectangleDualNormalizedPotentials a w h A →ₗ[ℝ]
      rectangleDualPotentialCurlKernel a w h A where
  toFun f := ⟨⟨f.1.1, rectangleDualNormalized_mem_exterior a w h A f⟩,
    rectangleDualNormalized_mem_curlKernel a w h A f⟩
  map_add' f g := by
    rfl
  map_smul' c f := by
    rfl

theorem rectangleDualCurlKernel_local
    (φ : rectangleDualPotentialCurlKernel a w h A) :
    componentPotentialLocalPredicate (rectangleDualGraph a w h)
      (rectangleDualBoundaryCondition a w h)
      (rectangleDualConfiguration a w h A) φ.1.1 := by
  constructor
  · intro u v hadj
    rcases (rectangleDualOpen_adj_iff a w h A u v).mp hadj with ⟨e, he, huv⟩
    let de := rectanglePrimalDualEdgeEquiv a w h e.primalEdge
    have hde : de = e := by
      grind [rectanglePrimalDualEdgeEquiv]
    have hp := (rectanglePotentialCurl_zero_iff_dualEnds_eq a w h φ.1 e.primalEdge).mp
      (φ.2 e.primalEdge he)
    grind [rectangleDualCarrierPair, rectangleDualEdgeSource, rectangleDualEdgeTarget]
  · intro u v hrel
    rcases ((rectangleDualBoundaryCondition_rel a w h u v).mp hrel) with huv | ⟨hu,hv⟩
    · simp_all
    · have hzu := φ.1.2 ⟨u.1, u.2⟩ hu
      have hzv := φ.1.2 ⟨v.1, v.2⟩ hv
      linarith

 theorem rectangleDualCurlKernel_mem_componentConstant
    (φ : rectangleDualPotentialCurlKernel a w h A) :
    φ.1.1 ∈ componentConstantFunctions (rectangleDualGraph a w h)
      (rectangleDualBoundaryCondition a w h)
      (rectangleDualConfiguration a w h A) :=
  (componentConstant_iff_local _ _ _ _).mpr
    (rectangleDualCurlKernel_local a w h A φ)

 theorem rectangleDualCurlKernel_base_zero
    (φ : rectangleDualPotentialCurlKernel a w h A) :
    φ.1.1 (rectangleDualBaseVertex a w h) = 0 := by
  have hb := rectangleDualBaseVertex_boundary a w h
  aesop

def rectangleDualCurlKernelToNormalized  :
    rectangleDualPotentialCurlKernel a w h A →ₗ[ℝ]
      RectangleDualNormalizedPotentials a w h A where
  toFun φ :=
    ⟨⟨φ.1.1, rectangleDualCurlKernel_mem_componentConstant a w h A φ⟩,
      rectangleDualCurlKernel_base_zero a w h A φ⟩
  map_add' φ ψ := by
    rfl
  map_smul' c φ := by
    rfl

def rectangleDualPotentialNormalizedLinearEquiv
     :
    RectangleDualNormalizedPotentials a w h A ≃ₗ[ℝ]
      rectangleDualPotentialCurlKernel a w h A := by
  let f := rectangleDualNormalizedToCurlKernel a w h A
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : rectangleDualPotentialCurlKernel a w h A => z.1.1) hxy
  · intro φ
    refine ⟨rectangleDualCurlKernelToNormalized a w h A φ, ?_⟩
    rfl

 theorem rectangleDualPotentialCurlKernel_finrank_add_one
     :
    Module.finrank ℝ (rectangleDualPotentialCurlKernel a w h A) + 1 =
      componentCount (rectangleDualGraph a w h)
        (rectangleDualBoundaryCondition a w h)
        (rectangleDualConfiguration a w h A) := by
  rw [← ((rectangleDualPotentialNormalizedLinearEquiv a w h A).finrank_eq)]
  exact normalizedComponentPotentials_finrank_add_one _ _ _ _
end

end PottsDiscontinuity.FK
