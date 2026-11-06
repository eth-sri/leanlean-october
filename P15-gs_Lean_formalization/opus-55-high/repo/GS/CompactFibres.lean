module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix

@[expose] public section


/-!
# Compact equal-fibre maps

This is the topological step following the original manuscript's fibre
calculation. It requires actual compactness and continuity, not just a set
bijection. It asserts a homeomorphism, not differentiability of the image.

-/

noncomputable section
attribute [fun_prop] continuous_if_const

@[fun_prop] theorem continuous_val_row {X R α β : Type*} [TopologicalSpace X] [TopologicalSpace R]
    {P : Matrix α β R → Prop} {f : X → {W : Matrix α β R // P W}} (hf : Continuous f) (i : α) :
    Continuous fun x => (f x).val i :=
  continuous_pi fun k => hf.subtype_val.matrix_elem i k

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
  let f' : K → Set.range f := fun k => ⟨f k, ⟨k,rfl⟩⟩
  let g' : K → Set.range g := fun k => ⟨g k, ⟨k,rfl⟩⟩
  have hsf : Function.Surjective f' := by rintro ⟨y,k,rfl⟩; exact ⟨k, rfl⟩
  have hsg : Function.Surjective g' := by rintro ⟨y,k,rfl⟩; exact ⟨k, rfl⟩
  let e : Set.range f ≃ Set.range g :=
    { toFun y := g' (Classical.choose y.property), invFun z := f' (Classical.choose z.property),
      left_inv := by grind, right_inv := by grind }
  have hto : ∀ k, e (f' k) = g' k := by grind
  have hinv : ∀ k, e.symm (g' k) = f' k := by grind
  refine ⟨⟨e, ?_, ?_⟩, hto⟩
  · exact (Topology.IsQuotientMap.of_surjective_continuous hsf (hf.subtype_mk _)).continuous_iff.2
      (by simpa [Function.comp_def, hto] using hg.subtype_mk _)
  · exact (Topology.IsQuotientMap.of_surjective_continuous hsg (hg.subtype_mk _)).continuous_iff.2
      (by simpa [Function.comp_def, hinv] using hf.subtype_mk _)

end GS
