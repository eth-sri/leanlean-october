module

public import OAI.NumberTheory.DirichletL.RowCompletion.BranchDecoding

@[expose] public section

namespace OAI

noncomputable section

















namespace CanonicalRowCompletion.ActualFiber

local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

end CanonicalRowCompletion.ActualFiber

namespace CanonicalRowCompletion

section

local notation "Eis" => ActualEisensteinCubic.O

end

end CanonicalRowCompletion

namespace ShortDraft

end ShortDraft

end

end OAI
