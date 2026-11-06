module

public import OAI.NumberTheory.DirichletL.Reflection.OriginalDictionary

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section



def castControlled {ι } [Fintype ι] {p q : ι→ActualEisensteinCubic.O} {N a c } {mode }
    (h : p=q) (D : ControlledStratumArithmetic p N a c mode)  := h ▸ D

lemma mixedReflectedValue_cast {ι : Type*} [Fintype ι] {p q : ι→ActualEisensteinCubic.O} {N a c : ActualEisensteinCubic.O} {mode : Bool}
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (h : p=q) (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
     hp   hq  (hc : c≠0)
    (hgp : ∀ i, ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i}) (hgq : ∀ i, ConcretePrimeRowBridge.goodLambda∉Ideal.span {q i})
     j   S   W   X  :
    mixedReflectedValue (castControlled h D) s hq hc hgq j S W X=
      mixedReflectedValue D s hp hc hgp j S W X := by
  subst q
  rfl

variable {σ : Type*} [Fintype σ] {m f z : ActualEisensteinCubic.O} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal ActualEisensteinCubic.O) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (S : PrimeFamily σ) (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
local notation "E" => D.primeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad
local notation "PS" => PrimeFamily.restrict (PrimeFamily.sum (freePrimeFamily D.movingIdeal Q₀ D.movingSupported) S) (markedActiveSet E B T)
local notation "PF" => PrimeFamily.reflected (PrimeFamily.restrict (poolPrimeFamily R (Ideal.span (Set.singleton m)*F) Q₀) B) K hK (S.restrict T)
local notation "EA" => markedActiveEquiv E B T

lemma original_active_marks_eq_slots :
    reindexMarks EA (activeMarks (markedActiveSet E B T) markedSumSlots)=slotIndices B (PrimeIndex K) T := by
  rw [original_active_marks D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask B T]
  ext x
  cases x with
  | inl b => simp [slotIndices]
  | inr x => cases x with
    | inl a => simp [slotIndices]
    | inr t => simp [slotIndices]

end
end SevenEighths.InverseReflectedPhase

end OAI
