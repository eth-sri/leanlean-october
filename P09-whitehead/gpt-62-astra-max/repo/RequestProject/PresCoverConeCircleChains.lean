module

public import RequestProject.StrictTopLinkCoefficients
public import RequestProject.RelatorCircleBoundary
public import RequestProject.PresCoverConeLinks


@[expose] public section
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f) (v : P) (j : J) (hv : f v = apexOf w j)

/-- The actual attaching circle is the lower interval of each lifted relator apex. -/
def presCoverConeCircleOrderIso :=
  (hf.lowerIntervalOrderIso v).trans
    ((strictBelowCongr hv).trans (relatorCircleOrderIso w j).symm)

def presCoverConeCircleHom :=
  strictOrderCxMap (presCoverConeCircleOrderIso w f hf v j hv)
    (presCoverConeCircleOrderIso w f hf v j hv).strictMono

/-- Transport the actual link by its circle isomorphism. -/
def presCoverConeCircleChain :=
  (chain1 (presCoverConeCircleHom w f hf v j hv)).comp (strictTopLinkChain v)

variable (c : StrictOrdTri P →₀ ℤ)

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

end FiniteChains.PresModel
