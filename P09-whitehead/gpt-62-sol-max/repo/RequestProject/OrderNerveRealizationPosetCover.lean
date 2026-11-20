module

public import RequestProject.OrderNerveRealizationNestedSubcomplex
public import RequestProject.PosetCoverUpTransform

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

namespace IsPosetCover
variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {f : P → Q}

/-- Every actual simplex has an actual simplex lift through a poset cover. -/
theorem exists_simplex_lift (hf : IsPosetCover f) {n : SimplexCategory}
    (s : (nerve Q).obj (Opposite.op n)) :
    ∃ t : (nerve P).obj (Opposite.op n), (nerveMap hf.mono.functor).app _ t = s := by
  obtain ⟨a, ha⟩ := hf.surj (s.obj 0)
  have hs : Monotone s.obj := fun _ _ h => leOfHom (s.map (homOfLE h))
  have hb (i : Fin (n.len + 1)) : f a ≤ s.obj i := ha.symm ▸ hs (Fin.zero_le i)
  exact ⟨(hf.upperMapLift_monotone _ _ monotone_const hs hb).functor,
    CategoryTheory.Functor.ext (fun i => (hf.upperMapLift_spec _ _ hb i).2)⟩

/-- The actual realized map of a poset cover is surjective. -/
theorem realizationMap_surjective (hf : IsPosetCover f) :
    Function.Surjective (orderNerveRealizationMap f hf.mono) := by
  intro x
  obtain ⟨n, s, z, hx⟩ := orderNerveRealizationSimplex_jointly_surjective Q x
  obtain ⟨t, ht⟩ := hf.exists_simplex_lift s
  refine ⟨orderNerveRealizationSimplex P t z, ?_⟩
  rwa [orderNerveRealizationSimplex_natural, ht]

end IsPosetCover
end FiniteChains.Comb
