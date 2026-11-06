import RequestProject.OrderNerveRealizationPosetCover
import RequestProject.PosetCoverLowerInterval
noncomputable section


namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

/-- Vertices comparable with a chosen vertex; their induced nerve is its closed star. -/
def orderNerveVertexStar (P : Type) [PartialOrder P] (v : P) :=
  {a | a ≤ v ∨ v ≤ a}

/-- Identity vertex maps induce identity maps of the actual realization. -/
theorem orderNerveRealizationMap_id P [PartialOrder P]
    (x : orderNerveRealization P) : orderNerveRealizationMap id monotone_id x = x := by
  change SSet.toTop.map (𝟙 _) x = x
  aesop

/-- Every order isomorphism induces a homeomorphism of the actual realizations. -/
def orderNerveRealizationOrderIso {P Q} [PartialOrder P] [PartialOrder Q]
    (e : P ≃o Q) : orderNerveRealization P ≃ₜ orderNerveRealization Q where
  toFun := orderNerveRealizationMap e e.monotone
  invFun := orderNerveRealizationMap e.symm e.symm.monotone
  left_inv x := by
    rw [orderNerveRealizationMap_comp]
    have he : (e.symm ∘ e : P → P) = id := by
      aesop
    simp [he, orderNerveRealizationMap_id]
  right_inv x := by
    rw [orderNerveRealizationMap_comp]
    have he : (e ∘ e.symm : Q → Q) = id := by
      aesop
    simp [he, orderNerveRealizationMap_id]
  continuous_toFun := (orderNerveRealizationMap e e.monotone).hom.continuous
  continuous_invFun := (orderNerveRealizationMap e.symm e.symm.monotone).hom.continuous

namespace IsPosetCover
variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {f : P → Q}

/-- A poset covering reflects order among vertices comparable with one fixed vertex. -/
theorem le_of_le_vertexStar (hf : IsPosetCover f) {a b v}
    (ha : a ∈ orderNerveVertexStar P v) (hb : b ∈ orderNerveVertexStar P v)
    (h : f a ≤ f b) : a ≤ b := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact hf.le_of_le_below ha hb h
  · exact ha.trans hb
  · have hea := le_antisymm (h.trans (hf.mono hb)) (hf.mono ha)
    have heb := le_antisymm (hf.mono hb) (by simp_all)
    have hia := hf.up_inj ha (le_refl v) hea
    have hib := hf.down_inj hb (le_refl v) heb
    simp_all
  · exact hf.le_of_le_above ha hb h

/-- The covering projection restricts to the comparable-vertex star. -/
def vertexStarMap (hf : IsPosetCover f) v :
    orderNerveVertexStar P v → orderNerveVertexStar Q (f v) :=
  fun a => ⟨f a.val, a.property.elim (fun h => Or.inl (hf.mono h))
    (fun h => Or.inr (hf.mono h))⟩

/-- Restricted star projections are bijective, by unique upper and lower interval lifts. -/
theorem vertexStarMap_bijective (hf : IsPosetCover f) v :
    Function.Bijective (hf.vertexStarMap v) := by
  constructor
  · intro a b h
    have he := congrArg Subtype.val h
    apply Subtype.ext
    exact le_antisymm (hf.le_of_le_vertexStar a.property b.property he.le)
      (hf.le_of_le_vertexStar b.property a.property he.symm.le)
  · intro q
    rcases q.property with hq | hq
    · obtain ⟨a, ⟨hav, hfa⟩, _⟩ := hf.down v q.val hq
      exact ⟨⟨a, Or.inl hav⟩, Subtype.ext hfa⟩
    · obtain ⟨a, ⟨hva, hfa⟩, _⟩ := hf.up v q.val hq
      exact ⟨⟨a, Or.inr hva⟩, Subtype.ext hfa⟩

/-- The actual comparable-vertex stars of a poset cover are order isomorphic. -/
def vertexStarOrderIso (hf : IsPosetCover f) v :
    orderNerveVertexStar P v ≃o orderNerveVertexStar Q (f v) where
  toEquiv := Equiv.ofBijective (hf.vertexStarMap v) (hf.vertexStarMap_bijective v)
  map_rel_iff' := by
    intro a b
    exact ⟨(hf.le_of_le_vertexStar a.property b.property), fun h => hf.mono h⟩

/-- The closed vertex stars have genuinely homeomorphic actual realizations. -/
def vertexStarRealizationHomeomorph (hf : IsPosetCover f) v :=
  orderNerveRealizationOrderIso (hf.vertexStarOrderIso v)
