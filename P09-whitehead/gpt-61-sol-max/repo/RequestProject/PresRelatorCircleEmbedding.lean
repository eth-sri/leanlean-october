import Mathlib.Tactic

import RequestProject.PresWordEmbedding
import RequestProject.PresRealizationWordDisks
import RequestProject.RelatorCircleBoundaryHomeomorph

/-! Restrict a literal presentation-word embedding to each actual
relator circle. Positions, cyclic indices, and the letter-reading map
are retained exactly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel.PresWordEmbedding
open Comb


variable {A B J K : Type} {w : J → List (A × Bool)} {v : K → List (B × Bool)}
  (h : PresWordEmbedding w v)

variable (j : J)
def relatorCircleMap  : RelatorCircle w j ↪o RelatorCircle v (h.cell j) where
  toFun x := ⟨h.circleFun x.val, by
    constructor
    · exact congrArg h.cell x.property.1
    · change x.val.2.1 < (v (h.cell j)).length
      rw  [h.word_length]
      exact x.property.2⟩
  inj' := fun _ _ he => Subtype.ext (h.circleFun_injective (congrArg Subtype.val he))
  map_rel_iff' := h.circleFun_le_iff _ _







theorem relatorCircleMap_surjective  : Function.Surjective (h.relatorCircleMap j) := by
  intro y
  let k : Fin (w j).length := ⟨y.val.2.1, by
    rw  [← h.word_length j]
    exact y.property.2⟩
  refine ⟨relatorCirclePoint w j k y.val.2.2, ?_⟩
  apply Subtype.ext
  exact Prod.ext y.property.1.symm rfl

def relatorCircleOrderIso  : RelatorCircle w j ≃o RelatorCircle v (h.cell j) where
  toEquiv := Equiv.ofBijective (h.relatorCircleMap j)
    ⟨(h.relatorCircleMap j).injective, h.relatorCircleMap_surjective j⟩
  map_rel_iff' := (h.relatorCircleMap j).le_iff_le

def relatorCircleRealizationMap  :
    C(orderNerveRealization (RelatorCircle w j), orderNerveRealization (RelatorCircle v (h.cell j))) :=
  ⟨orderNerveRealizationMap (h.relatorCircleMap j) (h.relatorCircleMap j).monotone,
    (orderNerveRealizationMap (h.relatorCircleMap j) (h.relatorCircleMap j).monotone).hom.continuous⟩

theorem presCircleWordMap_natural  (x : orderNerveRealization (RelatorCircle w j)) :
    orderNerveRealizationMap h.roseMap h.roseMap.monotone (presCircleWordMap w j x) =
      presCircleWordMap v (h.cell j) (h.relatorCircleRealizationMap j x) := by
  
  rw (config := { transparency := .default }) [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
  have hf : (h.roseMap ∘ (fun c : RelatorCircle w j => aFun w c.val)) =
      ((fun c : RelatorCircle v (h.cell j) => aFun v c.val) ∘ h.relatorCircleMap j) := by
    funext c
    exact (h.attaching_map c.val).symm
  exact orderNerveRealizationMap_congr _ _ hf x

end FiniteChains.PresModel.PresWordEmbedding
