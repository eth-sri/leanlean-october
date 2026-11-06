module

public import OAI.NumberTheory.PrimeGaps.SingularTails

@[expose] public section

namespace OAI

namespace LargePrimeGaps







noncomputable def distinctBox {s h : ℕ} (a : Fin s → ℤ) : Finset (Fin s → Fin h) :=
  Finset.univ.filter fun n => Function.Injective (boxTuple a n)

end LargePrimeGaps

end OAI
