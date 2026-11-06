module

public import RequestProject.Oriented
public import RequestProject.PresWordEmbeddingFoxPi2
public import RequestProject.PresWordEmbeddingTopology
public import RequestProject.PresWordEmbeddingPi1
public import RequestProject.PresValidPi2

@[expose] public section

backwardOptions




namespace FiniteChains.PresModel.PresWordEmbedding
open Comb
variable {α β J K : Type}
variable {w : J → FiniteChains.Comb.Oriented α} {v : K → FiniteChains.Comb.Oriented β}
  (h : PresWordEmbedding w v)

noncomputable def realizationMap :
    C(orderNerveRealization (PresPos w), orderNerveRealization (PresPos v)) :=
  ⟨orderNerveRealizationMap h.posMap h.posMap.monotone,
    (orderNerveRealizationMap h.posMap h.posMap.monotone).hom.continuous⟩

variable [DecidableEq α]
  (ρ : J → FreeGroup α) (σ : K → FreeGroup β)
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hv : ∀ k, FreeGroup.mk (v k) = σ k)
  (hwp : ∀ j, 0 < (w j).length) (hvp : ∀ k, 0 < (v k).length)

end FiniteChains.PresModel.PresWordEmbedding
