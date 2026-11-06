module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Reflection.OriginalSlotSupport
public import OAI.NumberTheory.DirichletL.Reflection.OriginalTransport

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m f z : ActualEisensteinCubic.O} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal ActualEisensteinCubic.O) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))

variable (L : σ→Finset (Ideal ActualEisensteinCubic.O))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)



variable {τ : Type*} [Fintype τ] (Frozen : PrimeFamily τ) {N a c : ActualEisensteinCubic.O} {mode : Bool}
variable (T : Finset σ)
    (C : ∀ _b : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ∀ p : supportedSlotChoices (fun i : T => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ControlledStratumArithmetic (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F))
        (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator N a c mode)

def originalSplitControlled (p : originalSlotChoices D Q₀ L) :
    ControlledStratumArithmetic (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F))
      (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
      ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator N a c mode :=
  castControlled ((by rfl))
    (C (originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p).1
      (originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p).2)



end
end SevenEighths.InverseReflectedPhase

end OAI
