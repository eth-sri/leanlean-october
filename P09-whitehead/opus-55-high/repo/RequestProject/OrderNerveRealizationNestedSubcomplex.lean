import RequestProject.OrderNerveRealizationSubtypeCells
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

/-- Actual realization maps compose as the underlying monotone maps do. -/
theorem orderNerveRealizationMap_comp {P Q R}
    [PartialOrder P] [PartialOrder Q] [PartialOrder R]
    f hf (g : Q → R) hg
    (x : orderNerveRealization P) :
    orderNerveRealizationMap g hg (orderNerveRealizationMap f hf x) =
      orderNerveRealizationMap (g ∘ f) (hg.comp hf) x := by
  change (SSet.toTop.map (nerveMap hf.functor) ≫
    SSet.toTop.map (nerveMap hg.functor)) x = _
  rwd [← Functor.map_comp]
  rfl
