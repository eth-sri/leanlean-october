import Mathlib.Tactic

import RequestProject.StrictTopLinkCoefficients
import RequestProject.RelatorCircleBoundary
import RequestProject.PresConeLinkOrderIso
import RequestProject.PresCoverConeLinks
import RequestProject.CellularChainMapZero

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f) (v : P) (j : J) (hv : f v = apexOf w j)

/-- The actual attaching circle is the lower interval of each lifted relator apex. -/
noncomputable def presCoverConeCircleOrderIso  :=
  (hf.lowerIntervalOrderIso v).trans
    ((strictBelowCongr hv).trans (relatorCircleOrderIso w j).symm)

noncomputable def presCoverConeCircleHom  :=
  strictOrderCxMap (presCoverConeCircleOrderIso w f hf v j hv)
    (presCoverConeCircleOrderIso w f hf v j hv).strictMono

variable (c : StrictOrdTri P →₀ ℤ)
noncomputable def presCoverConeCircleChain  :
    StrictOrdEdge (RelatorCircle w j) →₀ ℤ :=
  chain1 (presCoverConeCircleHom w f hf v j hv) (strictTopLinkChain v c)

/-- Actual presentation-cover two-cycles yield actual finite attaching-circle one-cycles. -/
theorem presCoverConeCircleChain_cycle 
    (hc : Comb.bdry2 (strictOrderCx P) c = 0) :
    Comb.bdry1 (strictOrderCx (RelatorCircle w j))
      (presCoverConeCircleChain w f hf v j hv c) = 0 := by
  change Comb.bdry1 (strictOrderCx (RelatorCircle w j))
    (chain1 (presCoverConeCircleHom w f hf v j hv) (strictTopLinkChain v c)) = 0
  rw [bdry1_chain1, presCover_cone_link_cycle w f hf v j hv c hc, map_zero]

/-- The transported circle coefficient is the coefficient of the genuine lifted triangle. -/
theorem presCoverConeCircleChain_apply 
    (e : StrictOrdEdge (StrictBelow v)) :
    presCoverConeCircleChain w f hf v j hv c
      ((presCoverConeCircleHom w f hf v j hv).onE e) =
        c (strictConeTriangle v e) := (strictOrderCxMap_chain1_apply
    (presCoverConeCircleOrderIso w f hf v j hv)
    (presCoverConeCircleOrderIso w f hf v j hv).strictMono
    (presCoverConeCircleOrderIso w f hf v j hv).injective
    (strictTopLinkChain v c) e).trans (strictTopLinkChain_apply v c e)

/-- One actual coefficient determines all triangles at a lifted relator apex in a two-cycle. -/
theorem presCoverConeTriangles_eq_of_first_coefficient
    (c d : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0)
    (hd : Comb.bdry2 (strictOrderCx P) d = 0)
    (hpos : 0 < (w j).length)
    (he : presCoverConeCircleChain w f hf v j hv c
      (relatorCircleEdge0 w j ⟨0, hpos⟩) =
        presCoverConeCircleChain w f hf v j hv d
          (relatorCircleEdge0 w j ⟨0, hpos⟩))
    (e : StrictOrdEdge (StrictBelow v)) :
    c (strictConeTriangle v e) = d (strictConeTriangle v e) := by
  have hcd := relatorCircle_cycle_ext w j
    (presCoverConeCircleChain w f hf v j hv c)
    (presCoverConeCircleChain w f hf v j hv d)
    (presCoverConeCircleChain_cycle w f hf v j hv c hc)
    (presCoverConeCircleChain_cycle w f hf v j hv d hd) hpos he
  have heq := congrArg
    (fun z => z ((presCoverConeCircleHom w f hf v j hv).onE e)) hcd
  simpa [presCoverConeCircleChain_apply] using heq

end FiniteChains.PresModel
