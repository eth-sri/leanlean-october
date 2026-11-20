module

public import RequestProject.OrderNerveRealizationSubtypeHomeomorph
public import RequestProject.OrderNerveTwoComplex

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

/-- Actual realization maps compose as the underlying monotone maps do. -/
theorem orderNerveRealizationMap_comp {P Q R : Type}
    [PartialOrder P] [PartialOrder Q] [PartialOrder R]
    (f : P → Q) (hf : Monotone f) (g : Q → R) (hg : Monotone g)
    (x : orderNerveRealization P) :
    orderNerveRealizationMap g hg (orderNerveRealizationMap f hf x) =
      orderNerveRealizationMap _ (hg.comp hf) x := by
  change (SSet.toTop.map _ ≫
    SSet.toTop.map _) x = _
  erw [← Functor.map_comp]
  rfl

end FiniteChains.Comb
