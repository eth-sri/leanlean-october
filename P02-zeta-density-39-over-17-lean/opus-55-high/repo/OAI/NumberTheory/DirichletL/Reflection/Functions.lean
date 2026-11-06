module
public import OAI.NumberTheory.DirichletL.Reflection.Transport

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

section
variable {κ : Type*} [Fintype κ] {p q : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal] {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i}) (j j' : κ → ℕ)
include κ p q a c mode s hp hg hq hqg j j'
lemma sourceRowPhase_congr_functions (R F : Finset κ) (u : Eisˣ) (m : ℕ) (he : p=q) (hj : j=j') :
    sourceRowPhase s hp hg j R F u m = sourceRowPhase s hq hqg j' R F u m := by grind

lemma sourceSlotPhase_congr_functions (S F : Finset κ) (u : Eisˣ) (m : ℕ) (he : p=q) (hj : j=j') :
    sourceSlotPhase s hp hg j S F u m = sourceSlotPhase s hq hqg j' S F u m := by grind
end

end
end SevenEighths.InverseReflectedPhase

end OAI
