module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.SingularPrism
public import Mathlib.Topology.Homotopy.Contractible

@[expose] public section

/-! # Exact singular chains in all positive degrees for contractible spaces

The proof uses the actual prism and an explicit cone on constant chains.
In particular no higher exactness or homotopy invariance is postulated.
-/

namespace FiniteChains.TopologicalSingular

open Set Topology SingularPrism

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

variable (y : Y) (n : ℕ)

noncomputable def constantCone : Chain X n →ₗ[ℤ] Chain Y (n + 1) :=
  Finsupp.lmapDomain ℤ ℤ (fun _ => ContinuousMap.const (Domain (n + 1)) y)

theorem constantCone_single (σ : Simplex X n) (r : ℤ) :
    constantCone y n (Finsupp.single σ r) = Finsupp.single (ContinuousMap.const (Domain (n + 1)) y) r :=
  Finsupp.mapDomain_single

theorem face_constant {n : ℕ} (y : Y) (i : Fin _) :
    face i (ContinuousMap.const _ y) = ContinuousMap.const (Domain n) y := rfl

variable (y : Y) (n : ℕ)

theorem constantCone_identity_single (σ : Simplex X _) (r : ℤ) :
    boundary _ (constantCone y _ (Finsupp.single σ r)) +
      constantCone y n (boundary n (Finsupp.single σ r)) =
        map (ContinuousMap.const X y) _ (Finsupp.single σ r) := by
  simp only [constantCone_single, boundary_single, face_constant, map_sum, map_zsmul, map_single]
  change altSum (fun _ : Fin _ => Finsupp.single _ r) +
    altSum (fun _ : Fin _ => Finsupp.single _ r) =
      Finsupp.single (ContinuousMap.const (Domain (n + 1)) y) r
  simp [altSum_succ]

variable (c : Chain X (n + 1))

theorem constantCone_identity :
    boundary _ (constantCone y _ c) + constantCone y n (boundary n c) =
      map (ContinuousMap.const X y) _ c := by
  have he : (boundary (n + 1)).comp (constantCone y _) +
      (constantCone y n).comp (boundary n) = map (ContinuousMap.const X y) _ := by
    apply Finsupp.lhom_ext
    exact constantCone_identity_single y n
  exact DFunLike.congr_fun he c

theorem constantMap_cycle_bounds (hc : boundary n c = 0) :
    map (ContinuousMap.const X y) _ c ∈ LinearMap.range (boundary _) := by
  refine ⟨constantCone y _ c, ?_⟩
  simpa only [hc, map_zero, add_zero] using constantCone_identity y n c

theorem nullhomotopic_cycle_bounds (f : C(X, Y)) (hf : f.Nullhomotopic)
    (n : ℕ) (c : Chain X _) (hc : boundary n c = 0) :
    map f _ c ∈ LinearMap.range (boundary _) := by
  obtain ⟨y, ⟨H⟩⟩ := hf
  have hm := (LinearMap.range (boundary _)).sub_mem (constantMap_cycle_bounds y n c hc) (homotopic_maps_difference_bounds H n c hc)
  simp_all

variable [ContractibleSpace X] (n : ℕ)

theorem contractible_ker_boundary_eq_range :
    LinearMap.ker (boundary (X := X) n) = LinearMap.range (boundary _) := by
  apply le_antisymm
  · intro c hc
    have hm := nullhomotopic_cycle_bounds _ (id_nullhomotopic X) n c hc
    simp_all [map_id, LinearMap.id_apply]
  · rintro c ⟨b, rfl⟩
    exact boundary_boundary n b

theorem contractible_cycle_bounds (c : Chain X _)
    (hc : boundary n c = 0) : ∃ b : Chain X _, boundary _ b = c := by
  have hm : c ∈ LinearMap.ker (boundary n) := hc
  simp_all [contractible_ker_boundary_eq_range]

end FiniteChains.TopologicalSingular
