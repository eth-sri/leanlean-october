module

public import RequestProject.StrictOrderChains
public import RequestProject.OrderNerveDictionary

@[expose] public section

/-! Normalization preserves the coefficients of all genuine order simplices. -/

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
variable {P : Type} [PartialOrder P]

theorem normalizeOrdChain2_apply (c : OrdTri P →₀ ℤ) (t : StrictOrdTri P) :
    normalizeOrdChain2 c t = c ((strictOrderIncl P).onF t) := rfl

end FiniteChains.Comb
