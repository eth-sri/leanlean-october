module

public import PottsDiscontinuity.Duality.RectangleCurlLinearEquiv
public import PottsDiscontinuity.Duality.RectangleFlowDimension
public import PottsDiscontinuity.Duality.NormalizedPotentialSpace

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

noncomputable def rectangleDualConfiguration (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    Configuration (rectangleDualGraph a w h) :=
  Finset.map (rectangleDualGraphEdgeEquiv a w h).toEmbedding
    (rectangleDualComplementEquiv a w h A)

@[simp] theorem mem_rectangleDualConfiguration (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (e : RectangleDualEdgeCarrier a w h) :
    rectangleDualGraphEdgeEquiv a w h e ∈ rectangleDualConfiguration a w h A ↔
      e.primalEdge ∉ A := by
  classical
  simp [rectangleDualConfiguration, mem_rectangleDualComplementEquiv]

private theorem rectangleDualOpen_adj_iff
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (u v : RectangleDualVertex a w h) :
    (openGraph (rectangleDualGraph a w h) (rectangleDualConfiguration a w h A)).Adj u v ↔
      ∃ e : RectangleDualEdgeCarrier a w h,
        e.primalEdge ∉ A ∧ s(u,v) = rectangleDualCarrierPair a w h e := by
  rw [openGraph_adj, openEdges]
  constructor
  · rintro ⟨g, hg, hgv⟩
    have hgA : g ∈ rectangleDualConfiguration a w h A := hg
    let e := (rectangleDualGraphEdgeEquiv a w h).symm g
    have he : rectangleDualGraphEdgeEquiv a w h e = g := Equiv.apply_symm_apply _ _
    rw [← he, mem_rectangleDualConfiguration] at hgA
    exact ⟨e, hgA, hgv.symm.trans (congrArg Subtype.val he).symm⟩
  · rintro ⟨e, he, huv⟩
    exact ⟨rectangleDualGraphEdgeEquiv a w h e,
      (mem_rectangleDualConfiguration a w h A e).mpr he, huv.symm⟩

def rectangleDualBaseVertex (a : LatticeVertex) (w h : ℕ) :
    RectangleDualVertex a w h :=
  ⟨(a.1 - 1, a.2 - 1), by
    rw [rectangleDualExpanded, mem_latticeRectangle]; simp; omega⟩

theorem rectangleDualBaseVertex_boundary (a : LatticeVertex) (w h : ℕ) :
    (rectangleDualBaseVertex a w h).1 ∈ rectangleDualBoundary a w h := by
  simp [rectangleDualBaseVertex, rectangleDualBoundary, rectangleDualInterior,
    rectangleDualExpanded, mem_latticeRectangle, Finset.mem_filter]
  omega

noncomputable def rectanglePrimalEdgeBond_mem (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier a w h) : RectanglePrimalBond a w h :=
  ⟨rectanglePrimalEdgeBond a w h e,
    rectanglePrimalEdgeBond_endpoints_mem_public a w h e⟩

def rectangleDualPotentialCurlKernel (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    Submodule ℝ (rectangleExteriorPotentialSubmodule a w h) where
  carrier := {φ | ∀ e : rectanglePrimalEdgeCarrier a w h, e ∉ A →
    rectanglePotentialCurlMap a w h φ (rectanglePrimalEdgeBond_mem a w h e) = 0}
  zero_mem' := by intro _ _; simp
  add_mem' := by intro φ ψ hφ hψ e he; rw [map_add]; simp [hφ e he, hψ e he]
  smul_mem' := by intro c φ hφ e he; rw [map_smul]; simp [hφ e he]

private theorem rectanglePotentialCurl_zero_iff_dualEnds_eq
    (a : LatticeVertex) (w h : ℕ)
    (φ : rectangleExteriorPotentialSubmodule a w h)
    (e : rectanglePrimalEdgeCarrier a w h) :
    rectanglePotentialCurlMap a w h φ (rectanglePrimalEdgeBond_mem a w h e) = 0 ↔
      φ.1 (rectangleDualEdgeSource a w h
        (rectanglePrimalDualEdgeEquiv a w h e)) =
      φ.1 (rectangleDualEdgeTarget a w h
        (rectanglePrimalDualEdgeEquiv a w h e)) := by
  let d := rectanglePrimalDualEdgeEquiv a w h e
  let b := rectanglePrimalEdgeBond a w h e
  have hs : (rectangleDualEdgeSource a w h d).val = b.faceBase false :=
    rectangleDualEdgeSource_faceBase a w h d
  have ht : (rectangleDualEdgeTarget a w h d).val = b.faceBase true :=
    rectangleDualEdgeTarget_faceBase a w h d
  have hsrcval : rectangleExtendedPotential a w h ⟨φ.1, φ.2⟩ (b.faceBase false) =
      φ.1 (rectangleDualEdgeSource a w h d) := by
    rw [← hs, rectangleExtendedPotential_of_mem a w h _ _ (rectangleDualEdgeSource a w h d).2]
  have htgtval : rectangleExtendedPotential a w h ⟨φ.1, φ.2⟩ (b.faceBase true) =
      φ.1 (rectangleDualEdgeTarget a w h d) := by
    rw [← ht, rectangleExtendedPotential_of_mem a w h _ _ (rectangleDualEdgeTarget a w h d).2]
  change rectangleCurlFlow a w h ⟨φ.1, φ.2⟩ b = 0 ↔ _
  cases haxis : b.axis <;> simp only [rectangleCurlFlow, haxis, hsrcval, htgtval, sub_eq_zero, d]
  exact eq_comm

noncomputable abbrev RectangleDualNormalizedPotentials (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :=
  normalizedComponentPotentials (rectangleDualGraph a w h)
    (rectangleDualBoundaryCondition a w h)
    (rectangleDualConfiguration a w h A) (rectangleDualBaseVertex a w h)

theorem rectangleDualNormalized_mem_exterior
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (f : RectangleDualNormalizedPotentials a w h A) :
    f.1.1 ∈ rectangleExteriorPotentialSubmodule a w h := by
  intro z hz
  have hrel : (rectangleDualBoundaryCondition a w h).partition.r z
      (rectangleDualBaseVertex a w h) := by
    rw [rectangleDualBoundaryCondition_rel]
    exact Or.inr ⟨hz, rectangleDualBaseVertex_boundary a w h⟩
  have heq := f.1.2 (boundary_component (rectangleDualGraph a w h)
    (rectangleDualBoundaryCondition a w h) (rectangleDualConfiguration a w h A) hrel)
  have hnorm : f.1.1 (rectangleDualBaseVertex a w h) = 0 := by
    simpa [componentPotentialEvaluation] using LinearMap.mem_ker.mp f.2
  exact heq.trans hnorm

theorem rectangleDualNormalized_mem_curlKernel
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (f : RectangleDualNormalizedPotentials a w h A) :
    (⟨f.1.1, rectangleDualNormalized_mem_exterior a w h A f⟩ :
      rectangleExteriorPotentialSubmodule a w h) ∈ rectangleDualPotentialCurlKernel a w h A := by
  intro e he
  let d := rectanglePrimalDualEdgeEquiv a w h e
  have hAdj : (openGraph (rectangleDualGraph a w h)
      (rectangleDualConfiguration a w h A)).Adj
      (rectangleDualEdgeSource a w h d) (rectangleDualEdgeTarget a w h d) :=
    (rectangleDualOpen_adj_iff a w h A _ _).2 ⟨d, by simpa [d, rectanglePrimalDualEdgeEquiv] using he, rfl⟩
  have hlocal := (componentConstant_iff_local (rectangleDualGraph a w h)
    (rectangleDualBoundaryCondition a w h)
    (rectangleDualConfiguration a w h A) f.1.1).mp f.1.2
  exact (rectanglePotentialCurl_zero_iff_dualEnds_eq a w h
    ⟨f.1.1, rectangleDualNormalized_mem_exterior a w h A f⟩ e).2 (hlocal.1 hAdj)

theorem rectangleDualCurlKernel_mem_componentConstant
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (φ : rectangleDualPotentialCurlKernel a w h A) :
    φ.1.1 ∈ componentConstantFunctions (rectangleDualGraph a w h)
      (rectangleDualBoundaryCondition a w h)
      (rectangleDualConfiguration a w h A) := by
  rw [componentConstant_iff_local]
  refine ⟨fun {u v} hadj => ?_, fun {u v} hrel => ?_⟩
  · rcases (rectangleDualOpen_adj_iff a w h A u v).mp hadj with ⟨e, he, huv⟩
    have hde : rectanglePrimalDualEdgeEquiv a w h e.primalEdge = e :=
      (rectanglePrimalDualEdgeEquiv a w h).right_inv e
    have hp := (rectanglePotentialCurl_zero_iff_dualEnds_eq a w h φ.1 e.primalEdge).mp
      (φ.2 e.primalEdge he)
    rw [hde] at hp
    rw [rectangleDualCarrierPair, Sym2.eq_iff] at huv
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hp
    · exact hp.symm
  · rcases (rectangleDualBoundaryCondition_rel a w h u v).mp hrel with rfl | ⟨hu, hv⟩
    · rfl
    · exact (φ.1.2 u hu).trans (φ.1.2 v hv).symm

noncomputable def rectangleDualPotentialNormalizedLinearEquiv
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    RectangleDualNormalizedPotentials a w h A ≃ₗ[ℝ]
      rectangleDualPotentialCurlKernel a w h A where
  toFun f := ⟨⟨f.1.1, rectangleDualNormalized_mem_exterior a w h A f⟩,
    rectangleDualNormalized_mem_curlKernel a w h A f⟩
  invFun φ := ⟨⟨φ.1.1, rectangleDualCurlKernel_mem_componentConstant a w h A φ⟩,
    φ.1.2 _ (rectangleDualBaseVertex_boundary a w h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rectangleDualPotentialCurlKernel_finrank_add_one
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    Module.finrank ℝ (rectangleDualPotentialCurlKernel a w h A) + 1 =
      componentCount (rectangleDualGraph a w h)
        (rectangleDualBoundaryCondition a w h)
        (rectangleDualConfiguration a w h A) := by
  rw [← (rectangleDualPotentialNormalizedLinearEquiv a w h A).finrank_eq]
  exact normalizedComponentPotentials_finrank_add_one _ _ _ _

end PottsDiscontinuity.FK
