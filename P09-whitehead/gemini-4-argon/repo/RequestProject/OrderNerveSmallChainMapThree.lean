module

public import RequestProject.OrderNerveSmallChainMapTwo

@[expose] public section

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision

theorem orderSmallToNerve2_single_carrier {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 2) :
    orderSmallToNerve2 (orderSmallSingle σ 1) ∈ Nerve.IncOn (orderNerveSingularCarrier σ.val) := by
  rw [orderSmallToNerve2_single, one_smul]
  exact (orderSmallTwoFill_exists σ).choose_spec.1
