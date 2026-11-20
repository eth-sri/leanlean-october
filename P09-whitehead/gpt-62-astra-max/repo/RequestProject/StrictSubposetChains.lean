module

public import RequestProject.OrderSubposetChains

@[expose] public section

/-! Finite chains and cycles on an actual induced subposet. -/
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] (S : Set P)

abbrev strictSubposetIncl := inducedIncl (· < ·) S

theorem strictSubposetIncl_onE_injective : Function.Injective (strictSubposetIncl S).onE :=
  inducedIncl_edges _ _

end FiniteChains.Comb
