module

public import RequestProject.OrderUniversalPosetThree

@[expose] public section

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

/-- Every actual lifted nerve tetrahedron is an actual tetrahedron in the lifted order. -/
theorem uOrderTet_surjective : Function.Surjective (uOrderTet (P := P) (a := a)) := by
  rintro ⟨⟨v, t⟩, hv⟩
  have hv' : uOrderEnd v = t.1.1 := hv
  let h := hv'.le.trans t.2.1
  let w := uOrderStep v _ h
  let h' := (uOrderStep_end v _ h).le.trans t.2.2.1
  let z := uOrderStep w _ h'
  let h'' := (uOrderStep_end w _ h').le.trans t.2.2.2
  refine ⟨⟨(v, w, z, (uOrderStep z _ h'')), uOrderStep_le v _ h, uOrderStep_le w _ h',
    uOrderStep_le z _ h''⟩, ?_⟩
  exact Subtype.ext (Prod.ext rfl (Subtype.ext
    (Prod.ext hv (Prod.ext (uOrderStep_end v _ h)
      (Prod.ext (uOrderStep_end w _ h') (uOrderStep_end z _ h''))))))

/-- Genuine finite three-chains lift to genuine finite lifted-order three-chains. -/
theorem exists_uOrder_three_chain (c : UOrdTet P a →₀ ℤ) :
    ∃ d : OrdTet (UOrder P a) →₀ ℤ, Finsupp.mapDomain uOrderTet d = c :=
  Finsupp.mapDomain_surjective uOrderTet_surjective c

end FiniteChains.Comb
