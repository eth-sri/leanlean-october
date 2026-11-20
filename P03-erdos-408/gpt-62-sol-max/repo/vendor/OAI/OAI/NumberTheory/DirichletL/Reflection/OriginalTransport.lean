module

public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalFamily
public import OAI.NumberTheory.DirichletL.Reflection.OriginalDictionary

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def castControlled {ι : Type*} [Fintype ι] {p q : ι→Eis} {N a c : Eis} {mode : Bool}
    (h : p=q) (D : ControlledStratumArithmetic p N a c mode) :
    ControlledStratumArithmetic q N a c mode := h ▸ D

lemma mixedReflectedValue_cast {ι : Type*} [Fintype ι] {p q : ι→Eis} {N a c : Eis} {mode : Bool}
    [OAI.PrincipalFamily.Maximal p] [OAI.PrincipalFamily.Maximal q]
    (h : p=q) (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i≠0) (hq : ∀ i, q i≠0) (hc : c≠0)
    (hgp : OAI.PrincipalFamily.Avoids p λ₀) (hgq : OAI.PrincipalFamily.Avoids q λ₀)
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (castControlled h D) s hq hc hgq j S W X=
      mixedReflectedValue D s hp hc hgp j S W X := by
  subst q
  rfl

variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (S : PrimeFamily σ) (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
local notation "E" => D.primeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad
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
