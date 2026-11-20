module

public import RequestProject.PresWordEmbedding
public import RequestProject.PresRealizationWordDisks
public import RequestProject.RelatorCircleBoundaryHomeomorph

@[expose] public section

/-! Restrict a literal presentation-word embedding to each actual
relator circle. Positions, cyclic indices, and the letter-reading map
are retained exactly. -/

noncomputable section

namespace FiniteChains.PresModel.PresWordEmbedding
open Comb
open scoped Topology

variable {A B J K : Type} {w : J → List (A × Bool)} {v : K → List (B × Bool)}
  (h : PresWordEmbedding w v)

variable (j : J)

def relatorCircleMap : RelatorCircle w j ↪o RelatorCircle v (h.cell j) where
  toFun x := ⟨h.circleFun x.val, by
    constructor
    · exact congrArg h.cell x.property.1
    · erw [h.word_length]; exact x.property.2⟩
  inj' := fun _ _ he => Subtype.ext (h.circleFun_injective (congrArg Subtype.val he))
  map_rel_iff' := h.circleFun_le_iff _ _

variable (x : RelatorCircle w j)

@[simp] theorem relatorCircleMap_val :
    (h.relatorCircleMap j x).val = h.circleFun x.val := rfl

@[simp] theorem relatorCircleMap_position :
    (h.relatorCircleMap j x).val.2 = x.val.2 := rfl

@[simp] theorem relatorCircleMap_index :
    (relatorCircleIndexEquiv v _ (h.relatorCircleMap j x)).val =
      (relatorCircleIndexEquiv w j x).val := rfl

theorem relatorCircleMap_surjective : Function.Surjective (h.relatorCircleMap j) := by
  intro y
  let k : Fin (w j).length := ⟨y.val.2.1, by
    grind [h.word_length]⟩
  refine ⟨relatorCirclePoint w j k y.val.2.2, ?_⟩
  apply Subtype.ext
  exact Prod.ext y.property.1.symm rfl

def relatorCircleOrderIso : RelatorCircle w j ≃o RelatorCircle v (h.cell j) where
  toEquiv := Equiv.ofBijective _
    ⟨(h.relatorCircleMap j).injective, h.relatorCircleMap_surjective j⟩
  map_rel_iff' := (h.relatorCircleMap j).le_iff_le

def relatorCircleRealizationMap :
    C(orderNerveRealization (RelatorCircle w j), orderNerveRealization (RelatorCircle v (h.cell j))) :=
  ⟨orderNerveRealizationMap _ (h.relatorCircleMap j).monotone,
    (orderNerveRealizationMap _ (h.relatorCircleMap j).monotone).hom.continuous⟩

theorem presCircleWordMap_natural (x : orderNerveRealization (RelatorCircle w j)) :
    orderNerveRealizationMap h.roseMap h.roseMap.monotone (presCircleWordMap w j x) =
      presCircleWordMap v _ (h.relatorCircleRealizationMap j x) := by
  erw [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
  have hf : (h.roseMap ∘ (fun c : RelatorCircle w j => aFun w c.val)) =
      ((fun c : RelatorCircle v _ => aFun v c.val) ∘ h.relatorCircleMap j) := by
    funext c
    exact (h.attaching_map c.val).symm
  simp_all

end FiniteChains.PresModel.PresWordEmbedding
