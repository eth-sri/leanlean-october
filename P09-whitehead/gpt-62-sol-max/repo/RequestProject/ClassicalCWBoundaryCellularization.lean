module

public import RequestProject.SigmaHomotopy
public import RequestProject.HomeomorphContinuousMap
public import RequestProject.IntervalEndpointHomotopyExtension
public import RequestProject.ClassicalCWLoopCellularization

@[expose] public section

/-! Cellular representatives for actual attaching circle maps, including
maps whose chosen starting point is not in the one-skeleton. Four endpoint
motions are extended over the sides, then genuine path cellularization
and corner-compatible homotopy pasting finish the construction. -/

noncomputable section
open scoped Topology unitInterval Classical
open Topology
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.ClassicalCW
open RelativeAttachment

def pointVertexInOneSkeleton (K : Whitehead.TwoComplex) (x : K) : OneSkeleton K :=
  ⟨vertexPoint (pointVertex x), by
    apply CWComplex.skeletonLT_mono (C := Set.univ)
      (show 0 + 1 ≤ 2 by norm_num)
    apply CWComplex.closedCell_subset_skeletonLT 0 (pointVertex x)
    rw [RelCWComplex.closedCell_zero_eq_singleton]
    rfl⟩

/-- Any continuous square-boundary map can be moved into the original
one-skeleton, without any initial condition on its corner values. -/
theorem squareBoundary_into_oneSkeleton (K : Whitehead.TwoComplex)
    (r : C(SquareBoundary, K)) :
    ∃ q : C(SquareBoundary, OneSkeleton K),
      r.Homotopic ((⟨Subtype.val, continuous_subtype_val⟩ : C(OneSkeleton K, K)).comp q) := by
  let v z := pointVertexInOneSkeleton K (r z)
  obtain ⟨l, hl⟩ := homotopic_boundaryOfPaths r (fun z => (v z).val) (fun z => pointVertexPath (r z))
  have hl' (s : SquareSide) := path_into_oneSkeleton K (v (squareSideMap s 0)) (v (squareSideMap s 1)) (l s)
  choose q hq using hl'
  refine ⟨boundaryOfPaths q, hl.trans ?_⟩
  rw [boundaryOfPaths_comp]
  exact boundaryOfPaths_homotopic hq

/-- This is the actual normed circle used by classical CW attachments,
not a replacement of the attaching domain by a combinatorial loop. -/
theorem boundary_into_oneSkeleton (K : Whitehead.TwoComplex)
    (r : C(UnitBoundary (Fin 2 → ℝ), K)) :
    ∃ q : C(UnitBoundary (Fin 2 → ℝ), OneSkeleton K),
      r.Homotopic ((⟨Subtype.val, continuous_subtype_val⟩ : C(OneSkeleton K, K)).comp q) := by
  let e := unitBoundarySquareHomeomorph
  obtain ⟨q, hq⟩ := squareBoundary_into_oneSkeleton K (r.comp e.symm.toContinuousMap)
  refine ⟨q.comp e.toContinuousMap, ?_⟩
  have h := hq.comp (ContinuousMap.Homotopic.refl e.toContinuousMap)
  simp_all

/-- Arbitrary families are cellularized simultaneously. Each new boundary
has finite support in the original lower-dimensional cells; the whole
family and the old CW complex may both be infinite. -/
theorem boundaryFamily_into_oneSkeleton (K : Whitehead.TwoComplex) {J : Type}
    (r : C(BoundaryFamily J (Fin 2 → ℝ), K)) :
    ∃ q : C(BoundaryFamily J (Fin 2 → ℝ), K),
      r.Homotopic q ∧ FiniteLowerBoundary 2 q := by
  let rj (j : J)  :=
    r.comp ⟨fun a : UnitBoundary (Fin 2 → ℝ) => ⟨j, a⟩, continuous_sigmaMk («σ» := fun _ : J => UnitBoundary (Fin 2 → ℝ)) (i := j)⟩
  have hj := fun j => boundary_into_oneSkeleton K (rj j)
  choose q hq using hj
  let ι : C(OneSkeleton K, K) := ⟨Subtype.val, continuous_subtype_val⟩
  let Q : C(BoundaryFamily J (Fin 2 → ℝ), K) :=
    ⟨fun a => (q a.1 a.2).val,
      continuous_sigma (fun j => continuous_subtype_val.comp (q j).continuous)⟩
  let H (j : J) := Classical.choice (hq j)
  refine ⟨Q, ⟨ContinuousMap.Homotopy.sigmaFamily H⟩, ?_⟩
  letI : CompactSpace (UnitBoundary (Fin 2 → ℝ)) := isCompact_iff_compactSpace.mp (by
    convert isCompact_sphere (0 : Fin 2 → ℝ) 1 using 1
    ext x
    simp only [Metric.mem_sphere, dist_zero_right]
    rfl)
  intro j
  obtain ⟨support, hsupport⟩ := IsCompact.finite_lower_support (isCompact_range (ι.comp (q j)).continuous) 2
    (by rintro _ ⟨a, rfl⟩; exact (q j a).property)
  exact ⟨support, fun a => hsupport ⟨a, rfl⟩⟩

end FiniteChains.ClassicalCW
