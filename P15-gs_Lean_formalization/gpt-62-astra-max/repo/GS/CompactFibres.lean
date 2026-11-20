module

public import Mathlib.Topology.Homeomorph.Quotient
public import Mathlib.Topology.Maps.Strict.Basic
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Compact equal-fibre maps

This is the topological step following the original manuscript's fibre
calculation. It requires actual compactness and continuity, not just a set
bijection. It asserts a homeomorphism, not differentiability of the image.

-/

noncomputable section
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
  let F := Homeomorph.quotientKerEquivRange (hf.isClosedMap.isStrictMap hf)
  let G := Homeomorph.quotientKerEquivRange (hg.isClosedMap.isStrictMap hg)
  let E : Quotient (Setoid.ker f) ≃ₜ Quotient (Setoid.ker g) := Homeomorph.Quotient.congrRight hfg
  refine ⟨F.symm.trans (E.trans G),fun k => ?_⟩
  change G (E (F.symm (F ⟦k⟧))) = _
  rw [F.symm_apply_apply]; rfl

end GS
