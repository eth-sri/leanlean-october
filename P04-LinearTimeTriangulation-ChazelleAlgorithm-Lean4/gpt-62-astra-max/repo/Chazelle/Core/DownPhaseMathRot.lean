module

public import Chazelle.Core.SpecBase
public import Chazelle.Existence.Rotate

/-!
# Down phase, math (H-R1): the chain model depends only on the vertex sequence

A chain model `chainModel C` is built from the vertices `C.vertex k` of the chain, its length
`C.m` and its box radius `coordBound C.P + 1` only (`chainModel_congr`).  So rotating the host
polygon and shifting the start of the chain accordingly gives the same model
(`chainModel_rotate`); the driver's region chains start at index `0` of a rotated host polygon.
-/

namespace Chazelle.Core

namespace DownMath

@[expose] public section

open Set
open Chazelle.Chain (sideE)

/-- The coordinate bound is invariant under rotation. -/
theorem coordBound_rotate (P : Polygon) (s : ℕ) :
    Chazelle.Jordan.coordBound (P.rotate s) = Chazelle.Jordan.coordBound P := by
  unfold Chazelle.Jordan.coordBound
  rw [Existence.n_rotate]
  rw [← Existence.sum_range_rot (fun i => |(P.vtx i).1| + |(P.vtx i).2|) s P.n]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Existence.vtx_rotate _ _ (Finset.mem_range.1 hi)]

section

variable {C C' : Chain} (hm : C.m = C'.m) (hv : ∀ k, C.vertex k = C'.vertex k)
  (hr : Chazelle.Jordan.coordBound C.P = Chazelle.Jordan.coordBound C'.P)
include hm hv hr

omit hr in
theorem set_congr : C.set = C'.set := by
  ext p
  simp only [Chain.set, Set.mem_ofPred_eq, Chain.chainEdge_eq, hv, hm]

omit hr in
theorem topIdx_congr : C.topIdx = C'.topIdx := by
  apply le_antisymm
  · apply C.topIdx_min (by rw [hm]; exact C'.topIdx_le)
    intro i hi
    rw [hv, hv]; exact C'.topIdx_spec.2 i (by rw [← hm]; exact hi)
  · apply C'.topIdx_min (by rw [← hm]; exact C.topIdx_le)
    intro i hi
    rw [← hv, ← hv]; exact C.topIdx_spec.2 i (by rw [hm]; exact hi)

omit hr in
theorem top_congr : C.top = C'.top := by
  unfold Chain.top; rw [hv, topIdx_congr hm hv]

omit hm hv in
theorem radius_congr : C.radius = C'.radius := by
  unfold Chain.radius; rw [hr]

theorem slitTop_congr : C.slitTop = C'.slitTop := by
  unfold Chain.slitTop; rw [top_congr hm hv, radius_congr hr]

theorem dom_congr : C.dom = C'.dom := by
  unfold Chain.dom Chain.obstacle Chain.slit
  rw [set_congr hm hv, slitTop_congr hm hv hr, top_congr hm hv, radius_congr hr]

theorem sideBeta_congr : C.sideBeta = C'.sideBeta := by
  rw [Bool.eq_iff_iff, Chain.sideBeta_eq_true_iff, Chain.sideBeta_eq_true_iff]
  simp only [hv, top_congr hm hv, slitTop_congr hm hv hr, topIdx_congr hm hv]

theorem sideWalk_congr (β : Bool) : C.sideWalk β = C'.sideWalk β := by
  unfold Chain.sideWalk Chain.boxList Chain.sideTour Chain.sideIdx Chain.sideS
  simp only [hv, hm, slitTop_congr hm hv hr, radius_congr hr, topIdx_congr hm hv]

theorem augChords_congr : Merge.augChords C = Merge.augChords C' := by
  unfold Merge.augChords
  rw [dom_congr hm hv hr, top_congr hm hv]

theorem chords_congr : C.chords = C'.chords := by
  unfold Chain.chords Chain.DirFree Chain.chordSet Chain.chordEnd Chain.chordParam
    Chain.hitParam Chain.hitSet
  simp only [hv, hm, dom_congr hm hv hr]

/-- **The chain model depends only on the vertices, the length and the box radius.** -/
theorem chainModel_congr : chainModel C = chainModel C' := by
  unfold chainModel
  rw [dom_congr hm hv hr, sideBeta_congr hm hv hr, sideWalk_congr hm hv hr,
    augChords_congr hm hv hr, chords_congr hm hv hr, hm]

end

end

end DownMath

end Chazelle.Core
