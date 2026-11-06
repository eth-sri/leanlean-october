module

public import OAI.NumberTheory.DirichletL.Reflection.Transport

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open CubicEisenstein
noncomputable section

lemma sourceRowPhase_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → ActualEisensteinCubic.O} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    {a c : ActualEisensteinCubic.O} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {q i})
    (j j' : κ → ℕ) (R F : Finset κ) (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (he : p=q) (hj : j=j') :
    sourceRowPhase s hp hg j R F u m = sourceRowPhase s hq hqg j' R F u m := by
  simp_all

lemma sourceSlotPhase_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → ActualEisensteinCubic.O} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    {a c : ActualEisensteinCubic.O} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {q i})
    (j j' : κ → ℕ) (S F : Finset κ) (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (he : p=q) (hj : j=j') :
    sourceSlotPhase s hp hg j S F u m = sourceSlotPhase s hq hqg j' S F u m := by
  simp_all

end
end SevenEighths.InverseReflectedPhase

end OAI
