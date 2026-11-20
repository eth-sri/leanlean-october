module

public import RequestProject.OrderNerveRealizationPosetCover
public import RequestProject.PosetCoverLowerInterval

@[expose] public section

noncomputable section

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

section

variable (P : Type) [PartialOrder P]

/-- Vertices comparable with a chosen vertex; their induced nerve is its closed star. -/
def orderNerveVertexStar (v : P) :=
  {a | a ≤ v ∨ v ≤ a}

/-- Identity vertex maps induce identity maps of the actual realization. -/
theorem orderNerveRealizationMap_id
    (x : orderNerveRealization P) : orderNerveRealizationMap id monotone_id x = x := by
  change SSet.toTop.map (𝟙 (nerve P)) x = x
  aesop

end

/-- Every order isomorphism induces a homeomorphism of the actual realizations. -/
def orderNerveRealizationOrderIso {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (e : P ≃o Q) : orderNerveRealization P ≃ₜ orderNerveRealization Q where
  toFun := orderNerveRealizationMap e e.monotone
  invFun := orderNerveRealizationMap e.symm e.symm.monotone
  left_inv x := by
    rw [orderNerveRealizationMap_comp]
    have he : (e.symm ∘ e) = id := by
      funext p
      exact e.symm_apply_apply p
    simp [he, orderNerveRealizationMap_id]
  right_inv x := by
    rw [orderNerveRealizationMap_comp]
    have he : (e ∘ e.symm) = id := by
      funext q
      exact e.apply_symm_apply q
    simp [he, orderNerveRealizationMap_id]
  continuous_toFun := (orderNerveRealizationMap e e.monotone).hom.continuous
  continuous_invFun := (orderNerveRealizationMap e.symm e.symm.monotone).hom.continuous

namespace IsPosetCover
variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {f : P → Q}

variable (hf : IsPosetCover f)
include hf

/-- A poset covering reflects order among vertices comparable with one fixed vertex. -/
theorem le_of_le_vertexStar {a b v : P}
    (ha : a ∈ orderNerveVertexStar P v) (hb : b ∈ orderNerveVertexStar P v)
    (h : f a ≤ f b) : a ≤ b := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · apply hf.le_of_le_below <;> assumption
  · exact ha.trans hb
  · have hia := hf.up_inj ha (le_refl v) (le_antisymm (h.trans (hf.mono hb)) (hf.mono ha))
    have hib := hf.down_inj hb (le_refl v) (le_antisymm (hf.mono hb) ((hf.mono ha).trans h))
    simp_all
  · apply hf.le_of_le_above <;> assumption

variable (v : P)

/-- The covering projection restricts to the comparable-vertex star. -/
def vertexStarMap :
    orderNerveVertexStar P v → orderNerveVertexStar Q (f v) :=
  fun a => ⟨f a.val, a.property.elim (fun h => Or.inl (hf.mono h))
    (fun h => Or.inr (hf.mono h))⟩

/-- Restricted star projections are bijective, by unique upper and lower interval lifts. -/
theorem vertexStarMap_bijective :
    Function.Bijective (hf.vertexStarMap v) := by
  constructor
  · intro a b h
    have he := congrArg Subtype.val h
    exact le_antisymm (hf.le_of_le_vertexStar a.property b.property he.le)
      (hf.le_of_le_vertexStar b.property a.property he.symm.le)
  · intro q
    rcases q.property with hq | hq
    · obtain ⟨a, ⟨hav, hfa⟩, _⟩ := hf.down v q.val hq
      exact ⟨⟨a, Or.inl hav⟩, Subtype.ext hfa⟩
    · obtain ⟨a, ⟨hva, hfa⟩, _⟩ := hf.up v q.val hq
      exact ⟨⟨a, Or.inr hva⟩, Subtype.ext hfa⟩

/-- The actual comparable-vertex stars of a poset cover are order isomorphic. -/
def vertexStarOrderIso :
    orderNerveVertexStar P v ≃o orderNerveVertexStar Q (f v) where
  toEquiv := Equiv.ofBijective _ (hf.vertexStarMap_bijective v)
  map_rel_iff' := by
    intro a b
    exact ⟨fun h => hf.le_of_le_vertexStar a.property b.property h, fun h => hf.mono h⟩

/-- The closed vertex stars have genuinely homeomorphic actual realizations. -/
def vertexStarRealizationHomeomorph :=
  orderNerveRealizationOrderIso (hf.vertexStarOrderIso v)

end IsPosetCover
end FiniteChains.Comb
