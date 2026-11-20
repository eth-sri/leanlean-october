module

public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

namespace OAI.PrincipalFamily

variable {ι R : Type*} [CommSemiring R]

/-- Every generator gives a maximal ideal. -/
abbrev Maximal (p : ι → R) : Prop := ∀ i, (Ideal.span {p i}).IsMaximal

/-- Distinct members of the family are coprime. -/
abbrev Coprime (p : ι → R) : Prop := Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))

/-- The element `a` is outside each of the principal ideals in the family. -/
abbrev Avoids (p : ι → R) (a : R) : Prop := ∀ i, a ∉ Ideal.span {p i}

end OAI.PrincipalFamily
