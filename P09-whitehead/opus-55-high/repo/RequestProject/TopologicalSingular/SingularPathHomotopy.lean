/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.SingularTriangleGeometry


/-! # A path homotopy gives an explicit bounding singular two-chain -/

namespace FiniteChains.TopologicalSingular

open Set Topology

universe u
variable {X : Type u} [TopologicalSpace X]

theorem boundary_two_single (σ : Simplex X 2) r :
    boundary 1 (Finsupp.single σ r) =
      Finsupp.single (face 0 σ) r - Finsupp.single (face 1 σ) r + Finsupp.single (face 2 σ) r := by
  rw [boundary_single, Fin.sum_univ_three]
  aesop

theorem boundary_constant_two (x : X) r :
    boundary 1 (Finsupp.single (ContinuousMap.const (Domain 2) x) r) =
      Finsupp.single (ContinuousMap.const (Domain 1) x) r := by
  rw [boundary_two_single]
  exact sub_add_cancel _ _

variable {a b : X} {p q : Path a b}
