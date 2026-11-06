import RequestProject.PresWordEmbedding
import RequestProject.PresRealizationWordDisks
import RequestProject.RelatorCircleBoundaryHomeomorph
import RequestProject.Tac


/-! Restrict a literal presentation-word embedding to each actual
relator circle. Positions, cyclic indices, and the letter-reading map
are retained exactly. -/

noncomputable section
bwd

namespace FiniteChains.PresModel.PresWordEmbedding
open Comb
open scoped Topology

variable {A B J K : Type} {w : J → List (A × Bool)} {v : K → List (B × Bool)}
  (h : PresWordEmbedding w v)

def relatorCircleMap j : RelatorCircle w j ↪o RelatorCircle v (h.cell j) where
  toFun x := ⟨h.circleFun x.val, by
    constructor
    · exact congrArg h.cell x.property.1
    · rwd [h.word_length]
      exact x.property.2⟩
  inj' := fun _ _ he => Subtype.ext (h.circleFun_injective (congrArg Subtype.val he))
  map_rel_iff' := h.circleFun_le_iff _ _




theorem relatorCircleMap_surjective j : Function.Surjective (h.relatorCircleMap j) := by
  intro y
  let k : Fin (w j).length := ⟨y.val.2.1, by
    rwd [← h.word_length j]
    exact y.property.2⟩
  refine ⟨relatorCirclePoint w j k y.val.2.2, ?_⟩
  apply Subtype.ext
  exact Prod.ext y.property.1.symm rfl

def relatorCircleOrderIso j : RelatorCircle w j ≃o RelatorCircle v (h.cell j) where
  toEquiv := Equiv.ofBijective (h.relatorCircleMap j)
    ⟨(h.relatorCircleMap j).injective, h.relatorCircleMap_surjective j⟩
  map_rel_iff' := (h.relatorCircleMap j).le_iff_le

def relatorCircleRealizationMap j :
    C(orderNerveRealization (RelatorCircle w j), orderNerveRealization (RelatorCircle v (h.cell j))) :=
  ⟨orderNerveRealizationMap (h.relatorCircleMap j) (h.relatorCircleMap j).monotone,
    (orderNerveRealizationMap _ (h.relatorCircleMap j).monotone).hom.continuous⟩

theorem presCircleWordMap_natural j x :
    orderNerveRealizationMap h.roseMap h.roseMap.monotone (presCircleWordMap w j x) =
      presCircleWordMap v (h.cell j) (h.relatorCircleRealizationMap j x) := by
  rwd [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
  have hf : (h.roseMap ∘ (aFun w ·.val)) =
      ((aFun v ·.val) ∘ h.relatorCircleMap j) := by
    funext c
    exact (h.attaching_map c.val).symm
  simp_all
