module

public import RequestProject.PresConeIntervals
public import RequestProject.PresPosetConnected

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
variable {α J : Type u} (w : J → List (α × Bool))

end FiniteChains.PresModel
