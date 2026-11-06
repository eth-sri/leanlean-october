module

public import Chazelle.Core.SweepLabelJL
public import Chazelle.Core.SweepQuery

/-!
# The sweep (WP-D), mirror part 6: lemma (Q) and the answer for the left side

The mirror of the junction part of `SweepQuery` (sweep with `i = 1`): `left_vtx0`,
`left_split_top`, `left_cover₁`, `query_left` (lemma (Q): a query on `C₂` seeing `C₁`
reads the label of its region of `F₁⁺`) and `answer_of_labelL`.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft sideLeftOf sideCcw
  sideCross sideDot freeIn regionsIn sideLeft_edge sideLeft_zero sideLeft_not_self sideKey_inj
  sideCcw_smul)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext)
open Chazelle.Jordan (offset SectorSide)
open WalkEmbed

namespace Sweep

section Junction

variable (J : Merge.Junction)

/-- In case G, the vertex after the gap is the top of `C₁`. -/
theorem left_split_top (h : 0 < lδ J) :
    (chainModel J.left).W.vtx ((6 + tpos J.left J.m₁ + (lL1 J + lδ J)) %
      (chainModel J.left).W.n) = J.left.top := by
  have hτ := tpos_lt J.left J.m₁
  have e : lL1 J + lδ J = 2 * J.left.m - tpos J.left J.m₁ + 7 := by
    unfold lL1 lδ at *
    split_ifs at h ⊢ <;> omega
  rw [e, show 6 + tpos J.left J.m₁ + (2 * J.left.m - tpos J.left J.m₁ + 7) =
    6 + tpos J.left J.m₁ + (2 * J.left.m - tpos J.left J.m₁) + 7 by omega]
  exact walk_box J.left J.m₁ 7 le_rfl

end Junction
/-! ## Lemma (Q) -/

section Query

variable (J : Merge.Junction)

end Query
section Answer

variable (J : Merge.Junction)

end Answer

end Sweep

end

end Chazelle.Core
