module

public import OAI.NumberTheory.DirichletL.Moments.Primary
public import OAI.NumberTheory.DirichletL.Moments.Mask

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
open scoped ContDiff
local notation "O" => ActualEisensteinCubic.O
end

end OAI
