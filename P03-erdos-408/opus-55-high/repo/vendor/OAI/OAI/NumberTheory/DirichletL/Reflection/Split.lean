module

public import OAI.NumberTheory.DirichletL.Reflection.Partition

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
noncomputable section
variable {ι : Type*} [Fintype ι] {p : ι → ActualEisensteinCubic.O} {N a0 c0 : ActualEisensteinCubic.O} {mode : Bool}
noncomputable local instance splitPhaseFinite (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] : Fintype (ActualEisensteinCubic.O ⧸ P) := Fintype.ofFinite _

end
end SevenEighths.InverseReflectedPhase

end OAI
