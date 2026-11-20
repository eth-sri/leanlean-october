module

public import RequestProject.OrderNerveRealizationNestedSubcomplex
public import RequestProject.PosetCoverUpTransform

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

namespace IsPosetCover
variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {f : P → Q}

variable (hf : IsPosetCover f)
include hf

/-- A poset cover reflects order in every common upper interval. -/
theorem le_of_le_above {a b v : P}
    (ha : v ≤ a) (hb : v ≤ b) (h : f a ≤ f b) : a ≤ b := by
  obtain ⟨c, ⟨hac, hfc⟩, _⟩ := hf.up a _ h
  exact hf.up_inj (ha.trans hac) hb hfc ▸ hac

/-- Every actual simplex has an actual simplex lift through a poset cover. -/
theorem exists_simplex_lift {n : SimplexCategory}
    (s : (nerve Q).obj _) :
    ∃ t : (nerve P).obj (Opposite.op n), (nerveMap (Monotone.functor hf.mono)).app _ t = s := by
  obtain ⟨a, ha⟩ := hf.surj _
  have hu : ∀ i, ∃ b, a ≤ b ∧ f b = s.obj i := by
    intro i
    have hi : f a ≤ s.obj i := by
      rw [ha]
      exact leOfHom (s.map (homOfLE (Fin.zero_le i)))
    obtain ⟨b, hb, _⟩ := hf.up a _ hi
    solve_by_elim
  choose b hb hfb using hu
  let t : (nerve P).obj _ :=
    { obj := b
      map := fun h => homOfLE (hf.le_of_le_above (hb _) (hb _) (by
        rw [hfb, hfb]
        exact leOfHom (s.map h))) }
  refine ⟨t, ?_⟩
  exact CategoryTheory.Functor.ext hfb

/-- The actual realized map of a poset cover is surjective. -/
theorem realizationMap_surjective :
    Function.Surjective (orderNerveRealizationMap f hf.mono) := by
  intro x
  obtain ⟨n, s, z, hx⟩ := orderNerveRealizationSimplex_jointly_surjective Q x
  obtain ⟨t, ht⟩ := hf.exists_simplex_lift s
  refine ⟨orderNerveRealizationSimplex P t z, ?_⟩
  have he := congrArg (fun k => k z) (orderNerveRealizationSimplex_natural f hf.mono t)
  simp_all

end IsPosetCover
end FiniteChains.Comb
