module

public import RequestProject.OrderNerveOneDictionary

@[expose] public section

/-! Recovering genuine cellular one-cycles from homogeneous increasing nerve cycles. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
open FreeAbelianGroup
universe u
variable {P : Type u} [PartialOrder P]

omit [PartialOrder P] in
theorem ordNerveChain0_injective : Function.Injective (ordNerveChain0 (P := P)) :=
  Nerve.encode_injective ⟨fun p => [p], by simp [Function.Injective]⟩

theorem ordNerveChain1_cycle_iff (c : OrdEdge P →₀ ℤ) :
    Nerve.bdry (ordNerveChain1 c) = 0 ↔ bdry1 (orderCx P) c = 0 := by
  rw [← ordNerveChain0_bdry1]
  exact ⟨fun h => ordNerveChain0_injective (P := P) (h.trans (map_zero _).symm),
    fun h => by rw [h, map_zero]⟩

end FiniteChains.Comb
