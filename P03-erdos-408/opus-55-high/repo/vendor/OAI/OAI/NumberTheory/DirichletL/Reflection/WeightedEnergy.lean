module

public import OAI.NumberTheory.DirichletL.Reflection.ActualExtractedEnergy

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open CubicEisenstein
noncomputable section
variable {φ ι : Type*} [Fintype φ] [Fintype ι] {N a c : ActualEisensteinCubic.O} {mode : Bool}

lemma actualCuspWeightedColumn_norm_le_one {ι : Type*} [Fintype ι]
    (G0 : PrimeFamily ι) (D0 : ControlledStratumArithmetic G0.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (w : Ideal ActualEisensteinCubic.O → Ideal ActualEisensteinCubic.O → ℂ)
    (hw : ∀ n b, ‖w n b‖ ≤ 1) (n b : Ideal ActualEisensteinCubic.O) :
    ‖actualCuspColumn D0 s hc u m n b*w n b‖ ≤ 1 := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (actualCuspColumn_norm_le_one D0 s hc u m n b)).trans (by grind)

end
end SevenEighths.InverseReflectedPhase

end OAI
