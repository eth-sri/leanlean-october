module

public import Erdos821.P4Probe.SharedPairingTask

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Shared

noncomputable section

open Erdos821.P4Probe

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]

end
end Erdos821.P4Shared
