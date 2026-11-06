
import Mathlib.Topology.Maps.Strict.Basic



/-!
# Compact equal-fibre maps

This is the topological step following the original manuscript's fibre
calculation. It requires actual compactness and continuity, not just a set
bijection. It asserts a homeomorphism, not differentiability of the image.

-/

namespace GS

/-- Equal fibres give a homeomorphism which also respects the parameter maps.
The compatibility records the image of each distinguished base point. -/
theorem exists_homeomorph_ranges_of_same_fibres
    {K Y Z : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z] [T2Space Z]
    (f : K → Y) (g : K → Z) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ a b, f a = f b ↔ g a = g b) :
    ∃ h : Set.range f ≃ₜ Set.range g,
      ∀ k, h ⟨f k, ⟨k,rfl⟩⟩ = ⟨g k, ⟨k,rfl⟩⟩ := by
  let e := Homeomorph.quotientKerEquivRange (hf.isClosedMap.isStrictMap hf)
  let e' := Homeomorph.quotientKerEquivRange (hg.isClosedMap.isStrictMap hg)
  refine ⟨e.symm.trans ((Homeomorph.Quotient.congrRight hfg).trans e'), ?_⟩
  intro k
  have he : e (Quotient.mk (Setoid.ker f) k) = ⟨f k, ⟨k,rfl⟩⟩ := rfl
  simp only [Homeomorph.trans_apply, ← he, Homeomorph.symm_apply_apply]
  rfl

end GS
