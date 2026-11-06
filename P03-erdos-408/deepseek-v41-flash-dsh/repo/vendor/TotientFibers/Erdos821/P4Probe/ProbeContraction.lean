module

public import Erdos821.P4Probe.ProjectionSelector

@[expose] public section

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe

noncomputable section

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]

end
end Erdos821.P4Probe
