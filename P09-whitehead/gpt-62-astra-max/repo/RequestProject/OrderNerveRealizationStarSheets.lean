module

public import RequestProject.OrderNerveRealizationOpenStars

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical
/-- Viewing a subset inside a containing carrier preserves its actual subspace topology. -/
def orderNerveNestedCarrierHomeomorph {X : Type} [TopologicalSpace X]
    (S C : Set X) (h : S ⊆ C) : S ≃ₜ {x : C // x.val ∈ S} where
  toFun x := ⟨⟨x.val, h x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

namespace IsPosetCover
variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {f : P → Q}

variable (hf : IsPosetCover f) (v : P)

/-- The actual supported closed-star carriers are homeomorphic under a poset cover. -/
noncomputable def vertexStarCarrierHomeomorph :=
  (orderNerveRealizationSubtypeHomeomorph (orderNerveVertexStar P v)).symm.trans
    ((hf.vertexStarRealizationHomeomorph v).trans
      (orderNerveRealizationSubtypeHomeomorph (orderNerveVertexStar Q (f v))))

variable (x : (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v) : Set (orderNerveRealization P)))

/-- The closed-star carrier homeomorphism agrees with the actual realized projection. -/
theorem vertexStarCarrierHomeomorph_coe :
    (hf.vertexStarCarrierHomeomorph v x).val = orderNerveRealizationMap f hf.mono x.val := by
  obtain ⟨y, rfl⟩ := (orderNerveRealizationSubtypeHomeomorph
    (orderNerveVertexStar P v)).surjective x
  change (orderNerveRealizationSubtypeHomeomorph _
    (hf.vertexStarRealizationHomeomorph v
      _)).val = _
  erw [Homeomorph.symm_apply_apply, orderNerveRealizationSubtypeHomeomorph_coe,
    orderNerveRealizationSubtypeHomeomorph_coe]
  erw [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]; rfl

/-- On a lifted closed star, the center coordinate is preserved by the projection. -/
theorem vertexStarCarrier_coordinate :
    orderNerveRealizationCoordinates Q (orderNerveRealizationMap f hf.mono x.val) (f v) =
      orderNerveRealizationCoordinates P x.val v := by
  obtain ⟨y, rfl⟩ := (orderNerveRealizationSubtypeHomeomorph
    (orderNerveVertexStar P v)).surjective x
  change orderNerveAffineRealization _
    (orderNerveRealizationMap f hf.mono
      _) =
    orderNerveAffineRealization _
      (orderNerveRealizationMap Subtype.val _ y)
  erw [orderNerveAffineRealization_natural, orderNerveAffineRealization_natural,
    orderNerveAffineRealization_natural]
  have hv : (((fun q => if q = f v then 1 else 0) ∘ f) ∘
      (Subtype.val : orderNerveVertexStar P v → P)) =
      ((fun p => if p = v then (1 : ℝ) else 0) ∘ Subtype.val) := by
    funext p
    have he : f p.val = f v ↔ p.val = v := by
      constructor
      · intro h
        rcases p.property with hp | hp
        · exact hf.down_inj hp (le_refl v) h
        · exact hf.up_inj hp (le_refl v) h
      · simp_all
    simp_all
  simp_all

/-- Each lifted open star is genuinely homeomorphic to its target open star. -/
noncomputable def vertexOpenStarHomeomorph :=
  (orderNerveNestedCarrierHomeomorph _ _
    (orderNerveRealizationOpenStar_subset_subcomplex v)).trans
    (((hf.vertexStarCarrierHomeomorph v).subtype (p := fun x =>
      x.val ∈ orderNerveRealizationOpenStar P v) (q := fun x =>
      x.val ∈ orderNerveRealizationOpenStar Q (f v)) (by
        intro x
        change (0 < orderNerveRealizationCoordinates P x.val v) ↔
          (0 < orderNerveRealizationCoordinates Q
            (hf.vertexStarCarrierHomeomorph v x).val (f v))
        rw [hf.vertexStarCarrierHomeomorph_coe, hf.vertexStarCarrier_coordinate])).trans
      (orderNerveNestedCarrierHomeomorph _ _
        (orderNerveRealizationOpenStar_subset_subcomplex (f v))).symm)

/-- The open-sheet homeomorphism is the actual realized projection. -/
theorem vertexOpenStarHomeomorph_coe
    (x : orderNerveRealizationOpenStar P v) :
    (hf.vertexOpenStarHomeomorph v x).val = orderNerveRealizationMap f hf.mono x.val := hf.vertexStarCarrierHomeomorph_coe v
    _

end IsPosetCover
end FiniteChains.Comb
