/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.RectangleCurlLinearEquiv
public import PottsDiscontinuity.Duality.RectangleFlowDimension
public import PottsDiscontinuity.Duality.NormalizedPotentialSpace

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

noncomputable def rectangleDualConfiguration {a : LatticeVertex} {w h : ℕ}
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    Configuration (rectangleDualGraph a w h) :=
  Finset.map (rectangleDualGraphEdgeEquiv a w h).toEmbedding
    (rectangleDualComplementEquiv a w h A)

@[simp] theorem mem_rectangleDualConfiguration (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (e : RectangleDualEdgeCarrier a w h) :
    rectangleDualGraphEdgeEquiv a w h e ∈ rectangleDualConfiguration A ↔
      e.primalEdge ∉ A := by
  classical
  simp [rectangleDualConfiguration,
    mem_rectangleDualComplementEquiv]

private theorem mem_rectangleDualConfiguration_iff
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (g : (rectangleDualGraph a w h).edgeSet) :
    g ∈ rectangleDualConfiguration A ↔
      ((rectangleDualGraphEdgeEquiv a w h).symm g).primalEdge ∉ A := by
  classical
  constructor
  · intro hg
    rcases Finset.mem_map.mp hg with ⟨e, he, hge⟩
    simp_all [(by simpa using (congrArg (fun x => (rectangleDualGraphEdgeEquiv a w h).symm x) hge).symm)]
  · intro hg
    apply Finset.mem_map.mpr
    refine ⟨(rectangleDualGraphEdgeEquiv a w h).symm g, ?_, ?_⟩ <;> simp_all

private theorem rectangleDualOpen_adj_iff
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (u v : RectangleDualVertex a w h) :
    (openGraph (rectangleDualConfiguration A)).Adj u v ↔
      ∃ e,
        e.primalEdge ∉ A ∧ s(u,v) = rectangleDualCarrierPair a w h e := by
  rw [openGraph_adj, openEdges]
  constructor
  · intro hv
    rcases hv with ⟨g, hg, hgv⟩
    let e := (rectangleDualGraphEdgeEquiv a w h).symm g
    refine ⟨e, ?_, ?_⟩
    · exact (mem_rectangleDualConfiguration_iff a w h A g).mp hg
    · have hpair : (rectangleDualGraphEdgeEquiv a w h e) =
          rectangleDualCarrierPair a w h e := rfl
      grind
  · rintro ⟨e, he, huv⟩
    refine ⟨rectangleDualGraphEdgeEquiv a w h e, ?_, ?_⟩
    · simp_all
    · exact huv.symm

section
variable (a : LatticeVertex) (w h : ℕ)

def rectangleDualBaseVertex :
    RectangleDualVertex a w h :=
  ⟨(a.1 - 1, a.2 - 1), by
    grind [rectangleDualExpanded, mem_latticeRectangle]⟩

theorem rectangleDualBaseVertex_boundary :
    (rectangleDualBaseVertex a w h).1 ∈ rectangleDualBoundary a w h := by
  simp [rectangleDualBaseVertex, rectangleDualBoundary, rectangleDualInterior,
    rectangleDualExpanded, mem_latticeRectangle, Finset.mem_filter]
  omega

noncomputable def rectanglePrimalEdgeBond_mem
    (e : rectanglePrimalEdgeCarrier a w h) : RectanglePrimalBond a w h :=
  ⟨rectanglePrimalEdgeBond e,
    rectanglePrimalEdgeBond_endpoints_mem_public e⟩

end

section
variable {a : LatticeVertex} {w h : ℕ} (A : Finset (rectanglePrimalEdgeCarrier a w h))

def rectangleDualPotentialExtended
    (φ : rectangleExteriorPotentialSubmodule a w h) (z : LatticeVertex) : ℝ :=
  if hz : z ∈ rectangleDualExpanded a w h then φ.1 ⟨z, hz⟩ else 0

include A in
/-- Zero-exterior potentials whose curl vanishes on every closed primal edge
(the complement of the open primal configuration A). -/
def rectangleDualPotentialCurlKernel :
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

private theorem rectanglePotentialCurl_zero_iff_dualEnds_eq
    (a : LatticeVertex) (w h : ℕ)
    (φ : rectangleExteriorPotentialSubmodule a w h)
    (e : rectanglePrimalEdgeCarrier a w h) :
    rectanglePotentialCurlMap a w h φ (rectanglePrimalEdgeBond_mem a w h e) = 0 ↔
      φ.1 (rectangleDualEdgeSource
        (rectanglePrimalDualEdgeEquiv a w h e)) =
      φ.1 (rectangleDualEdgeTarget
        (rectanglePrimalDualEdgeEquiv a w h e)) := by
  let d := rectanglePrimalDualEdgeEquiv a w h e
  let b := rectanglePrimalEdgeBond e
  let source := rectangleDualEdgeSource d
  have hs : source.val = b.faceBase false := rectangleDualEdgeSource_faceBase a w h d
  let target := rectangleDualEdgeTarget d
  have ht : target.val = b.faceBase true := rectangleDualEdgeTarget_faceBase a w h d
  have hsource : rectangleExtendedPotential
      (rectanglePotentialAsExterior a w h φ) (b.faceBase false) =
      rectangleDualPotentialExtended φ source.val := by
    rw [← hs]
    rfl
  have htarget : rectangleExtendedPotential
      (rectanglePotentialAsExterior a w h φ) (b.faceBase true) =
      rectangleDualPotentialExtended φ target.val := by
    rw [← ht]
    rfl
  have hsrcval : rectangleDualPotentialExtended φ
      source.val = φ.1 source := by
    change (if hz : source.val ∈ rectangleDualExpanded a w h
      then φ.1 ⟨source.val, hz⟩ else 0) = _
    grind
  have htgtval : rectangleDualPotentialExtended φ
      target.val = φ.1 target := by
    change (if hz : target.val ∈ rectangleDualExpanded a w h
      then φ.1 ⟨target.val, hz⟩ else 0) = _
    grind
  change rectangleCurlFlow (rectanglePotentialAsExterior a w h φ) b = 0 ↔ _
  cases haxis : b.axis
  · simp only [rectangleCurlFlow, haxis]
    grind
  · simp only [rectangleCurlFlow, haxis]
    grind

noncomputable abbrev RectangleDualNormalizedPotentials :=
  normalizedComponentPotentials _
    (rectangleDualBoundaryCondition a w h)
    (rectangleDualConfiguration A) (rectangleDualBaseVertex a w h)

end

variable (a : LatticeVertex) (w h : ℕ) (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (f : RectangleDualNormalizedPotentials A) (φ : rectangleDualPotentialCurlKernel A)

private theorem rectangleDualNormalized_boundary_zero (z : RectangleDualVertex a w h)
    (hz : z.1 ∈ rectangleDualBoundary a w h) : f.1.1 z = 0 := by
  have hcomp := boundary_component _
    (rectangleDualBoundaryCondition a w h) (rectangleDualConfiguration A) (by exact Or.inr ⟨hz, rectangleDualBaseVertex_boundary a w h⟩)
  exact (f.1.2 hcomp).trans (f.property)

 theorem rectangleDualNormalized_mem_exterior :
    f.1.1 ∈ rectangleExteriorPotentialSubmodule a w h := by
  solve_by_elim [rectangleDualNormalized_boundary_zero]

 theorem rectangleDualNormalized_mem_curlKernel :
    ⟨f.1.1, rectangleDualNormalized_mem_exterior a w h A f⟩ ∈ rectangleDualPotentialCurlKernel A := by
  intro e he
  have heq := ((componentConstant_iff_local _ _ _ f.1.1).mp f.1.2).1 (by
    apply (rectangleDualOpen_adj_iff a w h A _ _).2
    refine ⟨(rectanglePrimalDualEdgeEquiv a w h e), ?_, ?_⟩
    · assumption
    · rfl)
  exact (rectanglePotentialCurl_zero_iff_dualEnds_eq a w h
    ⟨f.1.1, rectangleDualNormalized_mem_exterior a w h A f⟩ e).2 heq

/-- The normalized wired dual potentials embed as zero-exterior potentials
whose curl vanishes on every closed primal edge. -/
def rectangleDualNormalizedToCurlKernel :
    RectangleDualNormalizedPotentials A →ₗ[ℝ]
      rectangleDualPotentialCurlKernel A where
  toFun f := ⟨⟨f.1.1, rectangleDualNormalized_mem_exterior a w h A f⟩,
    rectangleDualNormalized_mem_curlKernel a w h A f⟩
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

private theorem rectangleDualCurlKernel_local :
    componentPotentialLocalPredicate (rectangleDualGraph a w h)
      (rectangleDualBoundaryCondition a w h)
      (rectangleDualConfiguration A) φ.1.1 := by
  constructor
  · intro u v hadj
    rcases (rectangleDualOpen_adj_iff a w h A u v).mp hadj with ⟨e, he, huv⟩
    have hde : (rectanglePrimalDualEdgeEquiv a w h e.primalEdge) = e := (rectanglePrimalDualEdgeEquiv a w h).right_inv e
    have hpair : s(u,v) = rectangleDualCarrierPair a w h e := by
      assumption
    have hp := (rectanglePotentialCurl_zero_iff_dualEnds_eq a w h φ.1 e.primalEdge).mp
      (φ.2 e.primalEdge he)
    rw [rectangleDualCarrierPair, Sym2.eq_iff] at hpair
    grind
  · intro u v hrel
    rcases (by assumption) with huv | ⟨hu,hv⟩
    · cases huv
      rfl
    · exact (φ.1.2 ⟨u.1, u.2⟩ hu).trans (φ.1.2 ⟨v.1, v.2⟩ hv).symm

 theorem rectangleDualCurlKernel_mem_componentConstant :
    φ.1.1 ∈ componentConstantFunctions (rectangleDualGraph a w h)
      (rectangleDualBoundaryCondition a w h)
      (rectangleDualConfiguration A) := (componentConstant_iff_local _ _ _ _).mpr
    (rectangleDualCurlKernel_local a w h A φ)

 theorem rectangleDualCurlKernel_base_zero :
    φ.1.1 (rectangleDualBaseVertex a w h) = 0 := by
  have hb := rectangleDualBaseVertex_boundary a w h
  exact by apply φ.1.2 <;> assumption

def rectangleDualCurlKernelToNormalized :
    rectangleDualPotentialCurlKernel A →ₗ[ℝ]
      RectangleDualNormalizedPotentials A where
  toFun φ :=
    ⟨⟨φ.1.1, rectangleDualCurlKernel_mem_componentConstant a w h A φ⟩,
      rectangleDualCurlKernel_base_zero a w h A φ⟩
  map_add' φ ψ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' c φ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

noncomputable def rectangleDualPotentialNormalizedLinearEquiv :
    RectangleDualNormalizedPotentials A ≃ₗ[ℝ]
      rectangleDualPotentialCurlKernel A := by
  refine LinearEquiv.ofBijective (rectangleDualNormalizedToCurlKernel a w h A) ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : rectangleDualPotentialCurlKernel A => z.1.1) hxy
  · intro φ
    refine ⟨rectangleDualCurlKernelToNormalized a w h A φ, ?_⟩
    rfl

 theorem rectangleDualPotentialCurlKernel_finrank_add_one :
    Module.finrank ℝ (rectangleDualPotentialCurlKernel A) + 1 =
      componentCount
        (rectangleDualBoundaryCondition a w h)
        (rectangleDualConfiguration A) := by
  rw [← (rectangleDualPotentialNormalizedLinearEquiv a w h A).finrank_eq]
  exact normalizedComponentPotentials_finrank_add_one _ _ _ _

end PottsDiscontinuity.FK
