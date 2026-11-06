import RequestProject.PresWordEmbeddingFoxPi2
import RequestProject.PresWordEmbeddingTopology
import RequestProject.PresWordEmbeddingPi1
import RequestProject.PresValidPi2
import RequestProject.Tac


bwd

namespace FiniteChains.PresModel.PresWordEmbedding
open Comb
variable {α β J K : Type}
variable {w : J → List (α × Bool)} {v : K → List (β × Bool)}
  (h : PresWordEmbedding w v)

noncomputable def realizationMap :
    C(orderNerveRealization (PresPos w), orderNerveRealization (PresPos v)) :=
  ⟨orderNerveRealizationMap h.posMap h.posMap.monotone,
    (orderNerveRealizationMap h.posMap h.posMap.monotone).hom.continuous⟩

variable [DecidableEq α]
  (ρ : J → FreeGroup α) (σ : K → FreeGroup β)
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hv : ∀ k, FreeGroup.mk (v k) = σ k)
  (hwp : ∀ j, 0 < (w j).length) (hvp : ∀ k, 0 < (v k).length)
