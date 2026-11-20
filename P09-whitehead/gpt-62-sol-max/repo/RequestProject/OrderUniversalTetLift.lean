module

public import RequestProject.OrderUniversalPosetThree

@[expose] public section


namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

/-- Every actual lifted nerve tetrahedron is an actual tetrahedron in the lifted order. -/
theorem uOrderTet_surjective : Function.Surjective (uOrderTet (P := P) (a := a)) := by
  rintro ⟨⟨v, t⟩, hv⟩
  let s := liftOrdTet uOrderEnd_monotone uOrderLiftUp t v hv
  exact ⟨s.1, Subtype.ext (Prod.ext s.2.1 s.2.2)⟩

/-- Genuine finite three-chains lift to genuine finite lifted-order three-chains. -/
theorem exists_uOrder_three_chain (c : UOrdTet P a →₀ ℤ) :
    ∃ d : OrdTet (UOrder P a) →₀ ℤ, Finsupp.mapDomain uOrderTet d = c :=
  Finsupp.mapDomain_surjective uOrderTet_surjective c

end FiniteChains.Comb
