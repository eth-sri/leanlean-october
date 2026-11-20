module

public import RequestProject.NerveRelativeGluing

@[expose] public section

namespace FiniteChains.Nerve
universe u
variable {P Q : Type u} [Preorder P] [Preorder Q]

/-- A prism transfers a filling along either orientation of an order homotopy. -/
theorem filling_of_comparable_maps {f g : P → P} (hf : Monotone f) (hg : Monotone g)
    (hfg : f ≤ g ∨ g ≤ f) {c : Ch P} (hc : c ∈ Inc P) (hcyc : bdry c = 0)
    (hfill : ∃ y ∈ Inc P, bdry y = cmap g c) : ∃ y ∈ Inc P, bdry y = cmap f c := by
  obtain ⟨y, hy, hdy⟩ := hfill
  have hp (a b : P → P) : bdry (prism a b c) = cmap b c - cmap a c := by
    simpa only [hcyc, map_zero, add_zero] using bdry_prism_add_prism_bdry a b c
  rcases hfg with h | h
  · exact ⟨y - prism f g c, (Inc P).sub_mem hy (prism_mem_inc hf hg h hc),
      by rw [map_sub, hdy, hp]; abel⟩
  · exact ⟨y + prism g f c, (Inc P).add_mem hy (prism_mem_inc hg hf h hc),
      by rw [map_add, hdy, hp]; abel⟩

/-- The composite of the section with the retraction is homotopic to the identity,
so fillings pull back from the retraction. -/
theorem boundary_reflection_of_section (r : P → Q) (s : Q → P)
    (hr : Monotone r) (hs : Monotone s) (hle : id ≤ s ∘ r ∨ s ∘ r ≤ id)
    (c : Ch P) (hc : c ∈ Inc P) (hcyc : bdry c = 0)
    (hbound : ∃ y ∈ Inc Q, bdry y = cmap r c) : ∃ y ∈ Inc P, bdry y = c := by
  obtain ⟨y, hy, hdy⟩ := hbound
  simpa only [cmap_id] using filling_of_comparable_maps monotone_id (hs.comp hr) hle hc hcyc
    ⟨cmap s y, cmap_mem_inc_of_monotone hs hy, by rw [← cmap_bdry, hdy, cmap_comp]⟩

end FiniteChains.Nerve
