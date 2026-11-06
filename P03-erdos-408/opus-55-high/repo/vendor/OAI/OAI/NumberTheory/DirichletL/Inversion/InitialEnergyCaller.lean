module

public import OAI.NumberTheory.DirichletL.Inversion.InitialQuotientGeometry
public import OAI.NumberTheory.DirichletL.Inversion.InitialClippedColumns

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical
namespace SevenEighths.InverseInitialEnergyCaller
variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O)
  (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

end SevenEighths.InverseInitialEnergyCaller

end

end OAI
