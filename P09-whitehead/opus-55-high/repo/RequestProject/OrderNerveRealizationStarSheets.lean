import RequestProject.OrderNerveRealizationOpenStars
import RequestProject.Tac
noncomputable section


bwd

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

/-- The actual supported closed-star carriers are homeomorphic under a poset cover. -/
def vertexStarCarrierHomeomorph (hf : IsPosetCover f) v :=
  (orderNerveRealizationSubtypeHomeomorph _).symm.trans
    ((hf.vertexStarRealizationHomeomorph v).trans
      (orderNerveRealizationSubtypeHomeomorph _))

/-- The closed-star carrier homeomorphism agrees with the actual realized projection. -/
theorem vertexStarCarrierHomeomorph_coe (hf : IsPosetCover f) v
    x :
    (hf.vertexStarCarrierHomeomorph v x).val = orderNerveRealizationMap f hf.mono x.val := by
  obtain ⟨y, rfl⟩ := (orderNerveRealizationSubtypeHomeomorph
    _).surjective x
  change (orderNerveRealizationSubtypeHomeomorph _
    (hf.vertexStarRealizationHomeomorph v
      ((orderNerveRealizationSubtypeHomeomorph _).symm
        (orderNerveRealizationSubtypeHomeomorph _ y)))).val = _
  rwd [Homeomorph.symm_apply_apply, orderNerveRealizationSubtypeHomeomorph_coe,
    orderNerveRealizationSubtypeHomeomorph_coe]
  rwd [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
  rfl

/-- On a lifted closed star, the center coordinate is preserved by the projection. -/
theorem vertexStarCarrier_coordinate (hf : IsPosetCover f) v
    (x : (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v) :
      Set (orderNerveRealization P))) :
    orderNerveRealizationCoordinates Q (orderNerveRealizationMap f hf.mono x.val) (f v) =
      orderNerveRealizationCoordinates P x.val v := by
  obtain ⟨y, rfl⟩ := (orderNerveRealizationSubtypeHomeomorph
    _).surjective x
  change orderNerveAffineRealization (if · = f v then 1 else 0)
    (orderNerveRealizationMap f hf.mono
      (orderNerveRealizationMap Subtype.val (by tauto) y)) =
    orderNerveAffineRealization (if · = v then 1 else 0)
      (orderNerveRealizationMap Subtype.val (by tauto) y)
  rwd [orderNerveAffineRealization_natural, orderNerveAffineRealization_natural,
    orderNerveAffineRealization_natural]
  have hv : (((if · = f v then (1 : ℝ) else 0) ∘ f) ∘
      (Subtype.val : orderNerveVertexStar P v → P)) =
      ((if · = v then (1) else 0) ∘ Subtype.val) := by
    funext p
    have he : f p.val = f v ↔ p.val = v := by
      constructor
      · intro h
        rcases p.property with hp | hp
        · exact hf.down_inj hp (le_refl v) h
        · exact hf.up_inj hp (le_refl v) h
      simp_all
    simp_all
  simp_all

/-- Each lifted open star is genuinely homeomorphic to its target open star. -/
def vertexOpenStarHomeomorph (hf : IsPosetCover f) v :=
  (orderNerveNestedCarrierHomeomorph _ _
    (orderNerveRealizationOpenStar_subset_subcomplex v)).trans
    (((hf.vertexStarCarrierHomeomorph v).subtype (p := fun x =>
      x.val ∈ orderNerveRealizationOpenStar P v) (q := fun x =>
      x.val ∈ orderNerveRealizationOpenStar Q (f v)) (by
        intro x
        change (0 < orderNerveRealizationCoordinates P x.val v) ↔
          (0 < orderNerveRealizationCoordinates Q
            (hf.vertexStarCarrierHomeomorph v x).val (f v))
        grind [hf.vertexStarCarrierHomeomorph_coe, hf.vertexStarCarrier_coordinate])).trans
      (orderNerveNestedCarrierHomeomorph _ _
        (orderNerveRealizationOpenStar_subset_subcomplex _)).symm)

/-- The open-sheet homeomorphism is the actual realized projection. -/
theorem vertexOpenStarHomeomorph_coe (hf : IsPosetCover f) v
    x :
    (hf.vertexOpenStarHomeomorph v x).val = orderNerveRealizationMap f hf.mono x.val := hf.vertexStarCarrierHomeomorph_coe v
    _
