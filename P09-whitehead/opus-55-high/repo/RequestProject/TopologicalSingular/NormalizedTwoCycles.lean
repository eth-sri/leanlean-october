import RequestProject.TopologicalSingular.CoherentTriangleNormalization
import RequestProject.TopologicalSingular.CoherentPrism
import RequestProject.TopologicalSingular.BasedTriangleHurewicz
noncomputable section


namespace FiniteChains.TopologicalSingular
open scoped Topology
universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

def normalizedTriangleChain (x : X) :=
  simplexFamilyMap 2 (normalizedTriangle x)

theorem normalizedTriangleChain_single x (tau : Simplex X 2) r :
    normalizedTriangleChain x (Finsupp.single tau r) = Finsupp.single (normalizedTriangle x tau) r :=
  simplexFamilyMap_single 2 _ tau r

theorem normalizedTriangleChain_difference_bounds x (c : Chain X 2) (hc : boundary 1 c = 0) :
    normalizedTriangleChain x c - c ∈ LinearMap.range (boundary 2) :=
  coherentPrism_cycle_difference_bounds 1 _
    _ _ _
    (normalizedTriangleHomotopy_face x) c hc

theorem normalizedTriangleChain_cycle x (c : Chain X 2) (hc : boundary 1 c = 0) :
    boundary 1 (normalizedTriangleChain x c) = 0 :=
  coherentPrism_preserves_cycles 1 _
    _ _ _
    (normalizedTriangleHomotopy_face x) c hc

def normalizedCycleMap (x : X) : Chain X 2 →ₗ[ℤ] LinearMap.ker (boundary (X := X) 1) :=
  Finsupp.linearCombination ℤ (fun tau =>
    ⟨basedTriangleCycle (normalizedTriangle x tau) x,
      basedTriangleCycle_boundary _ (normalizedTriangle_face x tau)⟩)

theorem normalizedCycleMap_single x (tau : Simplex X 2) r :
    (normalizedCycleMap x (Finsupp.single tau r)).val =
      r • basedTriangleCycle (normalizedTriangle x tau) x := by
  rw [normalizedCycleMap, Finsupp.linearCombination_single]
  rfl

def constantTriangleFromEdge (x : X) : Chain X 1 →ₗ[ℤ] Chain X 2 :=
  Finsupp.linearCombination ℤ (fun _ => Finsupp.single (ContinuousMap.const _ x) 1)

omit [SimplyConnectedSpace X] in
theorem constantTriangleFromEdge_single (x : X) (tau : Simplex X 1) (r : ℤ) :
    constantTriangleFromEdge x (Finsupp.single tau r) = Finsupp.single (ContinuousMap.const (Domain 2) x) r := by
  simp [constantTriangleFromEdge, Finsupp.smul_single]

theorem boundary_normalizedTriangle_single x (tau : Simplex X 2) r :
    boundary 1 (Finsupp.single (normalizedTriangle x tau) r) =
      Finsupp.single (ContinuousMap.const (Domain 1) x) r := by
  simp [boundary_two_single, normalizedTriangle_face]

/-- For a cycle, the constant-triangle correction has zero total coefficient.
The resulting chain is a linear combination of based triangle cycles. -/
theorem normalizedCycleMap_val x (c : Chain X 2) (hc : boundary 1 c = 0) :
    (normalizedCycleMap x c).val = normalizedTriangleChain x c := by
  have he : (LinearMap.ker (boundary (X := X) 1)).subtype.comp (normalizedCycleMap x) =
      normalizedTriangleChain x - (constantTriangleFromEdge x).comp
        ((boundary 1).comp (normalizedTriangleChain x)) := by
    apply Finsupp.lhom_ext
    simp [normalizedCycleMap_single, normalizedTriangleChain_single, boundary_normalizedTriangle_single, constantTriangleFromEdge_single, basedTriangleCycle, smul_sub, Finsupp.smul_single]
  have hp := DFunLike.congr_fun he c
  change (normalizedCycleMap x c).val = normalizedTriangleChain x c -
    constantTriangleFromEdge x (boundary 1 (normalizedTriangleChain x c)) at hp
  grind [normalizedTriangleChain_cycle x c hc, map_zero, sub_zero]

theorem normalizedCycleMap_class {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    x (c : Chain X 2) hc :
    singularCycleClass 1 (normalizedCycleMap x c).val (normalizedCycleMap x c).property =
      singularCycleClass 1 c hc := by
  apply (singularCycleClass_eq_iff 1 _ _ _ _).mpr
  rw [normalizedCycleMap_val x c hc]
  exact normalizedTriangleChain_difference_bounds x c hc
