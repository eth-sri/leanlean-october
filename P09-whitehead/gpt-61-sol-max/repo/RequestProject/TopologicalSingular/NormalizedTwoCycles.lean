import Mathlib.Tactic

import RequestProject.TopologicalSingular.CoherentTriangleNormalization
import RequestProject.TopologicalSingular.CoherentPrism
import RequestProject.TopologicalSingular.BasedTriangleHurewicz

namespace FiniteChains.TopologicalSingular

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

  (x : X)
noncomputable def normalizedTriangleChain   :=
  simplexFamilyMap 2 (normalizedTriangle x)

variable (tau : Simplex X 2)
theorem normalizedTriangleChain_single   (r : ℤ) :
    normalizedTriangleChain x (Finsupp.single tau r) = Finsupp.single (normalizedTriangle x tau) r :=
  simplexFamilyMap_single 2 (normalizedTriangle x) tau r

variable (c : Chain X 2)
abbrev normalizedTriangleChain_difference_bounds   (hc : boundary 1 c = 0)  :=
  coherentPrism_cycle_difference_bounds 1 (fun _ => ContinuousMap.const (Domain 1) x)
    (normalizedTriangle x) (normalizedEdgeHomotopy x) (normalizedTriangleHomotopy x)
    (normalizedTriangleHomotopy_face x) c hc

theorem normalizedTriangleChain_cycle   (hc : boundary 1 c = 0) :
    boundary 1 (normalizedTriangleChain x c) = 0 :=
  coherentPrism_preserves_cycles 1 (fun _ => ContinuousMap.const (Domain 1) x)
    (normalizedTriangle x) (normalizedEdgeHomotopy x) (normalizedTriangleHomotopy x)
    (normalizedTriangleHomotopy_face x) c hc

noncomputable def normalizedCycleMap  : Chain X 2 →ₗ[ℤ] LinearMap.ker (boundary (X := X) 1) :=
  Finsupp.linearCombination ℤ (fun tau =>
    ⟨basedTriangleCycle (normalizedTriangle x tau) x,
      basedTriangleCycle_boundary _ (normalizedTriangle_face x tau)⟩)

theorem normalizedCycleMap_single   (r : ℤ) :
    (normalizedCycleMap x (Finsupp.single tau r)).val =
      r • basedTriangleCycle (normalizedTriangle x tau) x := by
  rw [normalizedCycleMap, Finsupp.linearCombination_single]
  rfl

noncomputable def constantTriangleFromEdge  : Chain X 1 →ₗ[ℤ] Chain X 2 :=
  Finsupp.linearCombination ℤ (fun _ => Finsupp.single (ContinuousMap.const (Domain 2) x) 1)

omit [SimplyConnectedSpace X] in
theorem constantTriangleFromEdge_single  (tau : Simplex X 1) (r : ℤ) :
    constantTriangleFromEdge x (Finsupp.single tau r) = Finsupp.single (ContinuousMap.const (Domain 2) x) r := by
  simp [constantTriangleFromEdge]

theorem boundary_normalizedTriangle_single   (r : ℤ) :
    boundary 1 (Finsupp.single (normalizedTriangle x tau) r) =
      Finsupp.single (ContinuousMap.const (Domain 1) x) r := by simp_all [boundary_two_single, normalizedTriangle_face]

/-- For a cycle, the constant-triangle correction has zero total coefficient.
The resulting chain is a linear combination of based triangle cycles. -/
theorem normalizedCycleMap_val   (hc : boundary 1 c = 0) :
    (normalizedCycleMap x c).val = normalizedTriangleChain x c := by
  have he : (LinearMap.ker (boundary (X := X) 1)).subtype.comp (normalizedCycleMap x) =
      normalizedTriangleChain x - (constantTriangleFromEdge x).comp
        ((boundary 1).comp (normalizedTriangleChain x)) := by
    aesop (add simp [normalizedCycleMap_single, normalizedTriangleChain_single, boundary_normalizedTriangle_single, constantTriangleFromEdge_single])
  have hp := DFunLike.congr_fun he c
  change (normalizedCycleMap x c).val = normalizedTriangleChain x c -
    constantTriangleFromEdge x (boundary 1 (normalizedTriangleChain x c)) at hp
  rwa [normalizedTriangleChain_cycle x c hc, map_zero, sub_zero] at hp

theorem normalizedCycleMap_class {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) (c : Chain X 2) (hc : boundary 1 c = 0) :
    singularCycleClass 1 (normalizedCycleMap x c).val (normalizedCycleMap x c).property =
      singularCycleClass 1 c hc := by
  apply (singularCycleClass_eq_iff 1 _ _ _ _).mpr
  rw [normalizedCycleMap_val x c hc]
  exact normalizedTriangleChain_difference_bounds x c hc

end FiniteChains.TopologicalSingular
