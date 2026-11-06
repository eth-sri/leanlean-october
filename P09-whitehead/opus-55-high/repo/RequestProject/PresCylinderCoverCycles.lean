import RequestProject.PresCylinderCycles
import RequestProject.PosetCoverUpTransform
import RequestProject.Tac


bwd

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  {f : P → CylBase w} (hf : IsPosetCover f)
include hf

noncomputable def cylinderCoverCollapse : P → P :=
  hf.upTransform _ (le_cylIn_cylRetr _)

theorem cylinderCoverCollapse_monotone : Monotone (cylinderCoverCollapse w hf) :=
  hf.upTransform_monotone _ (cylCollapse_monotone _) _

theorem cylinderCoverCollapse_projection p :
    f (cylinderCoverCollapse w hf p) = cylCollapse (aHom w) (f p) :=
  (hf.upTransform_spec _ _ p).2

theorem cylinderCover_strict_three_flags_empty : IsEmpty (StrictOrdTet P) := by
  refine ⟨fun t => ?_⟩
  exact (cylinder_strict_three_flags_empty w).false ⟨(f t.1.1, f t.1.2.1, f t.1.2.2.1, f t.1.2.2.2),
    hf.strictMono t.2.1, hf.strictMono t.2.2.1, hf.strictMono t.2.2.2⟩

theorem cylinderCover_normalized_collapse_triangle_zero (t : OrdTri P) :
    normalizeOrdTriangle
      ((orderCxMap (cylinderCoverCollapse w hf)
        (cylinderCoverCollapse_monotone w hf)).onF t) = 0 := by
  classical
  unfold normalizeOrdTriangle
  split
  · rename_i h
    have h01 := hf.strictMono h.1
    have h12 := hf.strictMono h.2
    change f (cylinderCoverCollapse w hf t.1.1) <
      f (cylinderCoverCollapse w hf t.1.2.1) at h01
    change f (cylinderCoverCollapse w hf t.1.2.1) <
      f (cylinderCoverCollapse w hf t.1.2.2) at h12
    rw [cylinderCoverCollapse_projection w hf, cylinderCoverCollapse_projection w hf] at h01 h12
    exact False.elim ((rose_strict_triangles_empty (α := α)).false ⟨(cylRetr _ (f t.1.1),
      cylRetr _ (f t.1.2.1), cylRetr _ (f t.1.2.2)), h01, h12⟩)
  · rfl

theorem cylinderCover_normalized_collapse_zero c :
    normalizedStrictChain2 (cylinderCoverCollapse w hf)
      (cylinderCoverCollapse_monotone w hf) c = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => rfl
  | add c d hc hd => simp_all
  | single t n =>
    rw [normalizedStrictChain2_single, cylinderCover_normalized_collapse_triangle_zero,
      smul_zero]

/-- The genuine preimage of the presentation cylinder has no strict two-cycles
in any actual covering poset. -/
theorem cylinderCover_two_cycle_zero (c : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0) : c = 0 := by
  obtain ⟨y, hy⟩ := strict_cycle_comparable_boundary id _
    monotone_id (cylinderCoverCollapse_monotone w hf)
    (hf.le_upTransform _ _) c hc
  haveI := cylinderCover_strict_three_flags_empty w hf
  have hy0 : y = 0 := by
    ext t
    exact isEmptyElim t
  simp_all [hy0, map_zero, cylinderCover_normalized_collapse_zero, normalizedStrictChain2_id, zero_sub]
