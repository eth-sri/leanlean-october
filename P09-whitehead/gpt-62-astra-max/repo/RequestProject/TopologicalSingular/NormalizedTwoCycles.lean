module

public import RequestProject.TopologicalSingular.CoherentTriangleNormalization
public import RequestProject.TopologicalSingular.CoherentPrism
public import RequestProject.TopologicalSingular.BasedTriangleHurewicz

@[expose] public section

noncomputable section

namespace FiniteChains.TopologicalSingular
open scoped Topology
universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

variable (x : X)

def normalizedTriangleChain :=
  simplexFamilyMap 2 (normalizedTriangle x)

theorem normalizedTriangleChain_single (tau : Simplex X 2) (r : ℤ) :
    normalizedTriangleChain x (Finsupp.single tau r) = Finsupp.single (normalizedTriangle x tau) r :=
  by apply simplexFamilyMap_single

section

variable (c : Chain X 2) (hc : boundary 1 c = 0)
include hc

theorem normalizedTriangleChain_difference_bounds :
    normalizedTriangleChain x c - c ∈ LinearMap.range (boundary 2) :=
  coherentPrism_cycle_difference_bounds 1 _
    _ _ _
    (normalizedTriangleHomotopy_face x) c hc

theorem normalizedTriangleChain_cycle :
    boundary 1 (normalizedTriangleChain x c) = 0 :=
  coherentPrism_preserves_cycles 1 _
    _ _ _
    (normalizedTriangleHomotopy_face x) c hc

end

def normalizedCycleMap : Chain X 2 →ₗ[ℤ] LinearMap.ker (boundary (X := X) 1) :=
  Finsupp.linearCombination ℤ (fun tau =>
    ⟨basedTriangleCycle (normalizedTriangle x tau) x,
      basedTriangleCycle_boundary _ (normalizedTriangle_face x tau)⟩)

theorem normalizedCycleMap_single (tau : Simplex X 2) (r : ℤ) :
    (normalizedCycleMap x (Finsupp.single tau r)).val =
      r • basedTriangleCycle (normalizedTriangle x tau) x := by
  simp [normalizedCycleMap, Finsupp.linearCombination_single]

def constantTriangleFromEdge : Chain X 1 →ₗ[ℤ] Chain X 2 :=
  Finsupp.linearCombination ℤ (fun _ => Finsupp.single (ContinuousMap.const (Domain 2) x) 1)

omit [SimplyConnectedSpace X] in
theorem constantTriangleFromEdge_single (tau : Simplex X 1) (r : ℤ) :
    constantTriangleFromEdge x (Finsupp.single tau r) = Finsupp.single (ContinuousMap.const (Domain 2) x) r := by
  simp [constantTriangleFromEdge, Finsupp.smul_single]

theorem boundary_normalizedTriangle_single (tau : Simplex X 2) (r : ℤ) :
    boundary 1 (Finsupp.single (normalizedTriangle x tau) r) =
      Finsupp.single (ContinuousMap.const (Domain 1) x) r := by
  simp [boundary_two_single, normalizedTriangle_face]

/-- For a cycle, the constant-triangle correction has zero total coefficient.
The resulting chain is a linear combination of based triangle cycles. -/
theorem normalizedCycleMap_val (c : Chain X 2) (hc : boundary 1 c = 0) :
    (normalizedCycleMap x c).val = normalizedTriangleChain x c := by
  have he : (LinearMap.ker (boundary 1)).subtype.comp (normalizedCycleMap x) =
      normalizedTriangleChain x - (constantTriangleFromEdge x).comp
        ((boundary 1).comp (normalizedTriangleChain x)) := by
    apply Finsupp.lhom_ext
    simp [normalizedCycleMap_single, normalizedTriangleChain_single, boundary_normalizedTriangle_single, constantTriangleFromEdge_single, basedTriangleCycle, smul_sub, Finsupp.smul_single]
  have hp := DFunLike.congr_fun he c
  change (normalizedCycleMap x c).val = normalizedTriangleChain x c -
    constantTriangleFromEdge x _ at hp
  simp_all [normalizedTriangleChain_cycle]

theorem normalizedCycleMap_class {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) (c : Chain X 2) (hc : boundary 1 c = 0) :
    singularCycleClass 1 _ (normalizedCycleMap x c).property =
      singularCycleClass 1 c hc := by
  apply (singularCycleClass_eq_iff 1 _ _ _ _).mpr
  rw [normalizedCycleMap_val x c hc]
  apply normalizedTriangleChain_difference_bounds <;> assumption

end FiniteChains.TopologicalSingular
