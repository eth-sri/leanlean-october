module

public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalFamily
public import OAI.NumberTheory.DirichletL.Reflection.Transport

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open ActualEisensteinCubic CubicEisenstein
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma sourceRowPhase_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [OAI.PrincipalFamily.Maximal p] [OAI.PrincipalFamily.Maximal q]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : OAI.PrincipalFamily.Avoids p λ₀)
    (hq : ∀ i, q i ≠ 0) (hqg : OAI.PrincipalFamily.Avoids q λ₀)
    (j j' : κ → ℕ) (R F : Finset κ) (u : Eisˣ) (m : ℕ) (he : p=q) (hj : j=j') :
    sourceRowPhase s hp hg j R F u m = sourceRowPhase s hq hqg j' R F u m := by
  subst q
  subst j'
  rfl

lemma sourceSlotPhase_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [OAI.PrincipalFamily.Maximal p] [OAI.PrincipalFamily.Maximal q]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : OAI.PrincipalFamily.Avoids p λ₀)
    (hq : ∀ i, q i ≠ 0) (hqg : OAI.PrincipalFamily.Avoids q λ₀)
    (j j' : κ → ℕ) (S F : Finset κ) (u : Eisˣ) (m : ℕ) (he : p=q) (hj : j=j') :
    sourceSlotPhase s hp hg j S F u m = sourceSlotPhase s hq hqg j' S F u m := by
  subst q
  subst j'
  rfl

end
end SevenEighths.InverseReflectedPhase

end OAI
