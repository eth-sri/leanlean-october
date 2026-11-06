module

public import OAI.NumberTheory.DirichletL.Moments.FirstCanonicalAllowance
public import OAI.NumberTheory.DirichletL.Moments.DescentLedger

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstExtractedLedger
open CanonicalQuadraticSieve CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentRankinRadical
open CenteredMomentFirstCanonicalAllowance CenteredMomentDescentLedger
local notation "O" => ActualEisensteinCubic.O

end SevenEighths.CenteredMomentFirstExtractedLedger

end

end OAI
