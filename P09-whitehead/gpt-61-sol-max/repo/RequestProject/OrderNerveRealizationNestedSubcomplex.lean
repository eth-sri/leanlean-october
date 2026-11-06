import Mathlib.Tactic

import RequestProject.OrderNerveRealizationSubtypeCells



namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

/-- Actual realization maps compose as the underlying monotone maps do. -/
theorem orderNerveRealizationMap_comp {P Q R : Type}
    [PartialOrder P] [PartialOrder Q] [PartialOrder R]
    (f : P → Q) (hf : Monotone f) (g : Q → R) (hg : Monotone g)
    (x : orderNerveRealization P) :
    orderNerveRealizationMap g hg (orderNerveRealizationMap f hf x) =
      orderNerveRealizationMap (g ∘ f) (hg.comp hf) x := by
  change (SSet.toTop.map (nerveMap hf.functor) ≫
    SSet.toTop.map (nerveMap hg.functor)) x = _
  rw  [← Functor.map_comp]
  rfl

end FiniteChains.Comb
