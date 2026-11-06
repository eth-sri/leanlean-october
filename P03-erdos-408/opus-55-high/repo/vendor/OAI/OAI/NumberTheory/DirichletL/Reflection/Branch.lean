module

public import OAI.NumberTheory.DirichletL.Reflection.Brackets

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
noncomputable section
noncomputable local instance branchFinite (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] : Fintype (ActualEisensteinCubic.O ⧸ P) := Fintype.ofFinite _

end
end SevenEighths.InverseReflectedPhase

end OAI
