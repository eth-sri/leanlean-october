module
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Coprime.Ideal
public import Mathlib.Algebra.CharP.Defs

@[expose] public section

namespace OAI.PrincipalIdealFamily

variable {ι R : Type*} [CommRing R]

/-- The family of principal ideals with specified generators. -/
abbrev ideal (p : ι → R) (i : ι) : Ideal R := Ideal.span {p i}

abbrev PairwiseCoprime (p : ι → R) : Prop := Pairwise (Function.onFun IsCoprime (ideal p))

abbrev Maximal (p : ι → R) : Prop := ∀ i, (ideal p i).IsMaximal

abbrev Avoids (p : ι → R) (t : R) : Prop := ∀ i, t ∉ ideal p i

/-- The generator in each slot is primary relative to `t`. -/
abbrev PrimaryAt (p : ι → R) (t : R) : Prop := ∀ i, t^2 ∣ p i-1

abbrev CharacteristicNe (p : ι → R) (n : ℕ) : Prop := ∀ i, ringChar (R ⧸ ideal p i) ≠ n

abbrev Distinct (p : ι → R) : Prop := Function.Injective (ideal p)

end OAI.PrincipalIdealFamily
