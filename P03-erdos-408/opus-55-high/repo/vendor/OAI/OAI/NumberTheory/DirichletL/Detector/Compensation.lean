module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeCompensation

def tupleOperation {α : Type*} [CommMonoid α] {K : ℕ}
    (p : Fin K → α) (q : α → ℝ) (η : α → ℂ)
    (F : α → ℝ → ℝ → ℝ → ℂ) (X Y Z : ℝ) : ℂ :=
  ∑ J ∈ (Finset.univ : Finset (Fin K)).powerset,
    (-1 : ℂ) ^ J.card * ((q (∏ i ∈ J, p i) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
      star (η (∏ i ∈ Finset.univ \ J, p i)) *
      F (∏ i ∈ Finset.univ \ J, p i)
        (X / q (∏ i ∈ J, p i)) (Y / q (∏ i ∈ J, p i))
        (Z * q (∏ i ∈ Finset.univ \ J, p i))

end SevenEighths.ProbeCompensation
end

end OAI
