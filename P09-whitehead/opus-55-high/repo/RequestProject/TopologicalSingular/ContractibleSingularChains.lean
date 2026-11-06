/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.SingularPrism
import Mathlib.Topology.Homotopy.Contractible


/-! # Exact singular chains in all positive degrees for contractible spaces

The proof uses the actual prism and an explicit cone on constant chains.
In particular no higher exactness or homotopy invariance is postulated.
-/

namespace FiniteChains.TopologicalSingular

open Set Topology SingularPrism

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def constantCone (y : Y) (n : ℕ) : Chain X n →ₗ[ℤ] Chain Y (n + 1) :=
  Finsupp.lmapDomain ℤ ℤ (fun _ => ContinuousMap.const _ y)

theorem constantCone_single (y : Y) n (σ : Simplex X n) r :
    constantCone y n (Finsupp.single σ r) = Finsupp.single (ContinuousMap.const (Domain (n + 1)) y) r :=
  Finsupp.mapDomain_single

theorem face_constant (y : Y) i :
    face i (ContinuousMap.const (Domain (n + 1)) y) = ContinuousMap.const (Domain n) y := rfl

theorem constantCone_identity_single (y : Y) n σ r :
    boundary (n + 1) (constantCone y (n + 1) (Finsupp.single σ r)) +
      constantCone y n (boundary n (Finsupp.single σ r)) =
        map (ContinuousMap.const X y) (n + 1) (Finsupp.single σ r) := by
  simp only [constantCone_single, boundary_single, face_constant, map_sum, map_zsmul, map_single]
  change altSum (fun _ => Finsupp.single (ContinuousMap.const _ y) r) +
    altSum (fun _ => Finsupp.single (ContinuousMap.const _ y) r) =
      Finsupp.single (ContinuousMap.const _ y) r
  simp [altSum_succ]

theorem constantCone_identity (y : Y) n c :
    boundary (n + 1) (constantCone y (n + 1) c) + constantCone y n (boundary n c) =
      map (ContinuousMap.const X y) (n + 1) c := by
  have he : (boundary _).comp (constantCone y _) +
      (constantCone y n).comp (boundary n) = map (ContinuousMap.const X y) _ := by
    apply Finsupp.lhom_ext
    exact constantCone_identity_single y n
  exact DFunLike.congr_fun he c

theorem constantMap_cycle_bounds (y : Y) n c (hc : boundary n c = 0) :
    map (ContinuousMap.const X y) (n + 1) c ∈ LinearMap.range (boundary (n + 1)) := by
  refine ⟨constantCone y _ c, ?_⟩
  simpa [hc, map_zero, add_zero] using constantCone_identity y n c

theorem nullhomotopic_cycle_bounds (f : C(X, Y)) (hf : f.Nullhomotopic)
    n c (hc : boundary n c = 0) :
    map f (n + 1) c ∈ LinearMap.range (boundary (n + 1)) := by
  obtain ⟨y, ⟨H⟩⟩ := hf
  have h₁ := homotopic_maps_difference_bounds H n c hc
  have h₂ := constantMap_cycle_bounds y n c hc
  have hm := (LinearMap.range (boundary (X := Y) _)).sub_mem h₂ h₁
  simp_all

theorem contractible_ker_boundary_eq_range [ContractibleSpace X] n :
    LinearMap.ker (boundary (X := X) n) = LinearMap.range (boundary (n + 1)) := by
  apply le_antisymm
  · intro c hc
    have hm := nullhomotopic_cycle_bounds _ (id_nullhomotopic X) n c hc
    simp_all [map_id, LinearMap.id_apply]
  · rintro c ⟨b, rfl⟩
    exact boundary_boundary n b

theorem contractible_cycle_bounds [ContractibleSpace X] n c
    (hc : boundary n c = 0) : ∃ b : Chain X (n + 2), boundary (n + 1) b = c := by
  have hm : c ∈ LinearMap.ker (boundary (X := X) n) := hc
  simp_all [contractible_ker_boundary_eq_range]
