module
public import Chazelle.Core.SpecBase

/-! Expose the canonical models as operations of their geometric objects. In particular
`J.whole.chainModel.W` and `P.Qof` use the very same model and shearing definitions as the
functional notation. -/

public section
namespace Chazelle.Chain
export Chazelle.Core (chainModel)
end Chazelle.Chain
namespace Chazelle.Polygon
export Chazelle.Core (Qof interiorModel)
end Chazelle.Polygon
