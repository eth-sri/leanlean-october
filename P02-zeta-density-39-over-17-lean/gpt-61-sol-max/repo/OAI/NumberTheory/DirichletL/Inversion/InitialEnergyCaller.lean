module
public import OAI.NumberTheory.DirichletL.Inversion.InitialQuotientGeometry
public import OAI.NumberTheory.DirichletL.Inversion.InitialClippedColumns

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
open SevenEighths.InverseInitialQuotientGeometry SevenEighths.InverseInitialClippedColumns
namespace SevenEighths.InverseInitialEnergyCaller
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

end SevenEighths.InverseInitialEnergyCaller

end

end OAI
