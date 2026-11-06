import Mathlib.Tactic

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.SingularPrism
import Mathlib.Topology.Homotopy.Contractible

/-! # Exact singular chains in all positive degrees for contractible spaces

The proof uses the actual prism and an explicit cone on constant chains.
In particular no higher exactness or homotopy invariance is postulated.
-/

namespace FiniteChains.TopologicalSingular

open Set Topology SingularPrism

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

  (y : Y)
  (n : ℕ)
noncomputable def constantCone   : Chain X n →ₗ[ℤ] Chain Y (n + 1) :=
  Finsupp.lmapDomain ℤ ℤ (fun _ => ContinuousMap.const (Domain (n + 1)) y)

theorem constantCone_single   (σ : Simplex X n) (r : ℤ) :
    constantCone y n (Finsupp.single σ r) = Finsupp.single (ContinuousMap.const (Domain (n + 1)) y) r :=
  Finsupp.mapDomain_single

theorem face_constant {n : ℕ} (y : Y) (i : Fin (n + 2)) :
    face i (ContinuousMap.const (Domain (n + 1)) y) = ContinuousMap.const (Domain n) y := rfl

theorem constantCone_identity_single   (σ : Simplex X (n + 1)) (r : ℤ) :
    boundary (n + 1) (constantCone y (n + 1) (Finsupp.single σ r)) +
      constantCone y n (boundary n (Finsupp.single σ r)) =
        map (ContinuousMap.const X y) (n + 1) (Finsupp.single σ r) := by
  simp only [constantCone_single, boundary_single, face_constant, map_sum, map_zsmul, map_single]
  change altSum (fun _ : Fin (n + 3) => Finsupp.single (ContinuousMap.const (Domain (n + 1)) y) r) +
    altSum (fun _ : Fin (n + 2) => Finsupp.single (ContinuousMap.const (Domain (n + 1)) y) r) =
      Finsupp.single (ContinuousMap.const (Domain (n + 1)) y) r
  rw [altSum_succ]
  exact sub_add_cancel _ _

theorem constantCone_identity   (c : Chain X (n + 1)) :
    boundary (n + 1) (constantCone y (n + 1) c) + constantCone y n (boundary n c) =
      map (ContinuousMap.const X y) (n + 1) c := by
  have he : (boundary (n + 1)).comp (constantCone y (n + 1)) +
      (constantCone y n).comp (boundary n) = map (ContinuousMap.const X y) (n + 1) := by
    apply Finsupp.lhom_ext
    exact constantCone_identity_single y n
  exact DFunLike.congr_fun he c

theorem constantMap_cycle_bounds   (c : Chain X (n + 1)) (hc : boundary n c = 0) :
    map (ContinuousMap.const X y) (n + 1) c ∈ LinearMap.range (boundary (n + 1)) := by
  refine ⟨constantCone y (n + 1) c, ?_⟩
  simpa [hc, map_zero, add_zero] using constantCone_identity y n c

theorem nullhomotopic_cycle_bounds (f : C(X, Y)) (hf : f.Nullhomotopic)
    (n : ℕ) (c : Chain X (n + 1)) (hc : boundary n c = 0) :
    map f (n + 1) c ∈ LinearMap.range (boundary (n + 1)) := by
  obtain ⟨y, ⟨H⟩⟩ := hf
  have h₁ := homotopic_maps_difference_bounds H n c hc
  have h₂ := constantMap_cycle_bounds y n c hc
  have hm := (LinearMap.range (boundary (X := Y) (n + 1))).sub_mem h₂ h₁
  convert hm using 1
  abel

theorem contractible_ker_boundary_eq_range [ContractibleSpace X] (n : ℕ) :
    LinearMap.ker (boundary (X := X) n) = LinearMap.range (boundary (n + 1)) := by
  apply le_antisymm
  · intro c hc
    have hm := nullhomotopic_cycle_bounds (ContinuousMap.id X) (id_nullhomotopic X) n c hc
    simpa [map_id, LinearMap.id_apply] using hm
  · rintro c ⟨b, rfl⟩
    exact boundary_boundary n b

abbrev contractible_cycle_bounds [ContractibleSpace X] (n : ℕ) (c : Chain X (n + 1))
    (hc : boundary n c = 0)  :=
  have hm := hc;
  Eq.mp
    (congrArg (fun (_a : Submodule ℤ (FiniteChains.TopologicalSingular.Chain X (n + 1))) => c ∈ _a)
      (FiniteChains.TopologicalSingular.contractible_ker_boundary_eq_range n))
    hm

end FiniteChains.TopologicalSingular
