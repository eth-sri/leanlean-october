module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.SingularTriangleGeometry

@[expose] public section

/-! # A path homotopy gives an explicit bounding singular two-chain -/

namespace FiniteChains.TopologicalSingular

open Set Topology

universe u
variable {X : Type u} [TopologicalSpace X]

theorem boundary_two_single (σ : Simplex X 2) (r : ℤ) :
    boundary 1 (Finsupp.single σ r) =
      Finsupp.single (face 0 σ) r - Finsupp.single (face 1 σ) r + Finsupp.single (face 2 σ) r := by
  rw [boundary_single, Fin.sum_univ_three]
  change (1 : ℤ) • _ + (-1 : ℤ) • _ + (1 : ℤ) • _ = _
  rw [one_smul, neg_smul, one_smul, one_smul, sub_eq_add_neg]

theorem boundary_constant_two (x : X) (r : ℤ) :
    boundary 1 (Finsupp.single (ContinuousMap.const (Domain 2) x) r) =
      Finsupp.single (ContinuousMap.const (Domain 1) x) r := by
  rw [boundary_two_single]
  change Finsupp.single (ContinuousMap.const (Domain 1) x) r -
    Finsupp.single (ContinuousMap.const (Domain 1) x) r +
    Finsupp.single (ContinuousMap.const (Domain 1) x) r = _
  exact sub_add_cancel _ _
