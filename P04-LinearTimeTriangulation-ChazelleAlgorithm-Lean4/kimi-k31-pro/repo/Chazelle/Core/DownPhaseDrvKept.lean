module

public import Chazelle.Core.DownPhaseFrontier
public import Chazelle.Core.DownPhaseHostSimple

/-!
# Down-phase driver, X-R1 (part 1): which chain chords are kept

For a region `R` of a nonempty interior submap `S` of a simple polygon `Q`, with host polygon
`H = hostPoly Q S R` (simple, H1) and host chain `C = hostChain Q S R g`:

* `region_eq_intHost`: `R` is the interior of `H` (`R ⊆ int H`, the frontier of `R` lies on `∂H`,
  and `int H` is connected);
* `kept_iff_intAdm`: a horizontal chord of `C.dom` meets `R` iff it is a chord of the interior of
  `H` (`kept_chord` for `⇒`);
* `kept_iff_attach`: iff its left end is attached (side-aware) to the boundary walk of the interior
  of `H` (the walk axioms `ends` and `clean` of `interiorModel H`).

The last form is what the driver's RAM decides from the chain walk position of the record's left
end (design `docs/design-downphase-driver.md` §4.2 (f)).
-/

namespace Chazelle.Core

namespace DownDrv

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft IsHChordIn)
open Chazelle.Visibility (hseg)
open DownHost

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point} {g : ℕ}
  {h3 : 3 ≤ nk (interiorModel Q) S R}

/-- **The region is the interior of its host polygon.** -/
theorem region_eq_intHost (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S)
    (hne : S.Nonempty) (hR : R ∈ (interiorModel Q).regions S) :
    R = (hostPoly Q S R).filled \ (hostPoly Q S R).boundary := by
  have hH  := hostPts_simple hQ hFam hne hR
  have hMH  := walkAx_interiorModel hH
  have hM  := walkAx_interiorModel hQ
  have hRo  := (hM.sys S hFam.2.1 hFam.1).regionsIn_open subset_rfl hR
  obtain ⟨z, hz⟩ := Chazelle.Chain.regionsIn_nonempty hR
  have hsub := region_sub_intHost hQ hFam hne hR
  refine Subset.antisymm hsub ?_
  have hpre  := hMH.preconn
  refine hpre.subset_of_closure_inter_subset hRo ⟨z, hsub hz, hz⟩ ?_
  rintro w ⟨hwc, hwH⟩
  by_contra hwR
  exact hwH.2 (frontier_sub_hostBd hQ hFam hne hR hwc hwR)

/-- The left endpoint of a horizontal segment written as a segment of two points is one of
them. -/
theorem left_end_of_segment {a' b' : Point} {y a b : ℝ} (hab : a < b) (hy : a'.2 = b'.2)
    (h : hseg y a b = Chazelle.segment a' b') : ((a, y) : Point) = a' ∨ ((a, y) : Point) = b' := by
  rw [Visibility.segment_horizontal_eq_hseg hy] at h
  obtain ⟨h1, h2, -⟩ := Merge.hseg_inj hab.le h
  rcases le_total a'.1 b'.1 with hl | hl
  · left; rw [min_eq_left hl] at h2; exact Prod.ext h2 h1
  · right; rw [min_eq_right hl] at h2; exact Prod.ext h2 (h1.trans hy)

/-- The horizontal direction to the right. -/
def eX : Point := (1, 0)

end

end DownDrv

end Chazelle.Core
