module

public import RequestProject.PresWordEmbeddingFoxPi2
public import RequestProject.PresCanonicalWords
public import RequestProject.PresValidFinite
public import RequestProject.OrderNerveRealizationSubtypeHomeomorph
public import RequestProject.OrderNerveTwoComplex
public import RequestProject.OrderNervePosetCoverVertexStars
public import RequestProject.PresWordEmbedding
public import RequestProject.PresPosetGroupEquiv
public import RequestProject.OrderCxNullTransfer
public import RequestProject.ZeroPi2Descent
public import RequestProject.OrderNerveRealizationContraction
public import RequestProject.TopologicalSingular.MathlibComparison
public import RequestProject.TopologicalCoverPi2

@[expose] public section


namespace FiniteChains.PresModel.PresWordEmbedding
open Comb
variable {α β J K : Type}
variable {w : J → List (α × Bool)} {v : K → List (β × Bool)}
  (h : PresWordEmbedding w v)

noncomputable def realizationMap :
    C(orderNerveRealization (PresPos w), orderNerveRealization (PresPos v)) :=
  ⟨orderNerveRealizationMap h.posMap h.posMap.monotone,
    (orderNerveRealizationMap h.posMap h.posMap.monotone).hom.continuous⟩






end FiniteChains.PresModel.PresWordEmbedding
