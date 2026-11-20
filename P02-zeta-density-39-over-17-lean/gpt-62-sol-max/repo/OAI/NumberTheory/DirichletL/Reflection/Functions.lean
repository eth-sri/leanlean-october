module
public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalIdealFamily
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
variable {κ : Type*} [instShared1 : Fintype κ] {p q : κ → Eis} [instShared3 : OAI.PrincipalIdealFamily.Maximal p] [instShared4 : OAI.PrincipalIdealFamily.Maximal q] {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hp : ∀ i, p i ≠ 0) (hg : OAI.PrincipalIdealFamily.Avoids p λ₀) (hq : ∀ i, q i ≠ 0) (hqg : OAI.PrincipalIdealFamily.Avoids q λ₀) (j j' : κ → ℕ)
include κ instShared1 p q instShared3 instShared4 a c mode s hp hg hq hqg j j'

lemma sourceRowPhase_congr_functions (R F : Finset κ) (u : Eisˣ) (m : ℕ) (he : p=q) (hj : j=j') :
    sourceRowPhase s hp hg j R F u m = sourceRowPhase s hq hqg j' R F u m := by
  subst q
  subst j'
  rfl

lemma sourceSlotPhase_congr_functions (S F : Finset κ) (u : Eisˣ) (m : ℕ) (he : p=q) (hj : j=j') :
    sourceSlotPhase s hp hg j S F u m = sourceSlotPhase s hq hqg j' S F u m := by
  subst q
  subst j'
  rfl

end

end
end SevenEighths.InverseReflectedPhase

end OAI
