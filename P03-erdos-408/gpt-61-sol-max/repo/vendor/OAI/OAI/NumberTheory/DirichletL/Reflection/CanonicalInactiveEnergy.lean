module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Reflection.CanonicalChoiceEnergy
public import OAI.NumberTheory.DirichletL.Reflection.InactiveSource

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment


universe v
variable {Nlevel : ActualEisensteinCubic.O}

lemma inactiveRows_mem {σ φ : Type*} [Fintype σ] [DecidableEq σ]
    (rows : Finset (Ideal ActualEisensteinCubic.O)) (lists : σ→Finset (Ideal ActualEisensteinCubic.O))  T 
    (FF : φ→Ideal ActualEisensteinCubic.O)  b   K  :
    K∈inactiveRowSet rows lists T FF b ↔ K∈rows ∧
      IsCoprime K (∏ i : {i // i∉T},(b i).val) ∧ ∀ j i,(b i).val≠FF j := Finset.mem_filter


end SevenEighths.InverseReflectedPhase

end OAI
