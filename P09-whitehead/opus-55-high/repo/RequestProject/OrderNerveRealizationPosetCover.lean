import RequestProject.OrderNerveRealizationNestedSubcomplex
import RequestProject.PosetCoverUpTransform


namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

namespace IsPosetCover
variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {f : P → Q}

/-- A poset cover reflects order in every common upper interval. -/
theorem le_of_le_above (hf : IsPosetCover f) {a b v}
    (ha : v ≤ a) (hb : v ≤ b) (h : f a ≤ f b) : a ≤ b := by
  obtain ⟨c, ⟨hac, hfc⟩, _⟩ := hf.up a _ h
  have hc := hf.up_inj (ha.trans hac) hb hfc
  simp_all

/-- Every actual simplex has an actual simplex lift through a poset cover. -/
theorem exists_simplex_lift (hf : IsPosetCover f) {n}
    (s : (nerve Q).obj (Opposite.op n)) :
    ∃ t : (nerve P).obj (Opposite.op n), (nerveMap hf.mono.functor).app _ t = s := by
  cases' hf.surj _ with a ha
  have hu : ∀ i, ∃ b, a ≤ b ∧ f b = s.obj i := by
    intro i
    have hi : f a ≤ s.obj i := by
      rw [ha]
      exact leOfHom (s.map (homOfLE i.zero_le))
    obtain ⟨b, hb, _⟩ := hf.up a _ hi
    tauto
  choose b hb hfb using hu
  let t : (nerve P).obj (Opposite.op n) :=
    { obj := b
      map := fun h => homOfLE (hf.le_of_le_above (hb _) (hb _) (by
        rw [hfb, hfb]
        exact leOfHom (s.map h))) }
  refine ⟨t, ?_⟩
  exact CategoryTheory.Functor.ext hfb

/-- The actual realized map of a poset cover is surjective. -/
theorem realizationMap_surjective (hf : IsPosetCover f) :
    Function.Surjective (orderNerveRealizationMap f hf.mono) := by
  intro x
  obtain ⟨n, s, z, hx⟩ := orderNerveRealizationSimplex_jointly_surjective Q x
  cases' hf.exists_simplex_lift s with t ht
  refine ⟨orderNerveRealizationSimplex P t z, ?_⟩
  have he := congrArg (· z) (orderNerveRealizationSimplex_natural f hf.mono t)
  simp_all
