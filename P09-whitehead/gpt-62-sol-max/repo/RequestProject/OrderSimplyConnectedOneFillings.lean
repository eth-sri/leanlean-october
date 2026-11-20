module

public import RequestProject.OrderComponentLabels
public import RequestProject.CombPerfectOneFillings
public import RequestProject.OrderNervePositiveFillings

@[expose] public section

/-! Finite one-cycle fillings when every component has trivial edge-path pi1. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

/-- A componentwise path contraction gives actual finite cellular fillings.
Connectedness or finiteness of the whole poset is not required. -/
theorem order_oneCycle_filling_of_simplyConnected (hsc : SimplyConnected (orderCx P))
    (c : OrdEdge P →₀ ℤ) (hc : bdry1 (orderCx P) c = 0) :
    ∃ y : OrdTri P →₀ ℤ, bdry2 (orderCx P) y = c := by
  let r := fun v => Quotient.out (orderComponentLabel P v)
  have hreach (v : P) : Reach (orderCx P) (r v) v :=
    (orderComponentLabel_eq_iff _ _).mp (Quotient.out_eq _)
  choose p hp using hreach
  refine oneCycle_filling_of_root_paths (orderCx P) r p hp
    (fun e => congrArg Quotient.out (orderComponentLabel_eq_of_le e.2)) ?_ c hc
  intro _ l
  simpa using (hsc _ l.val l.property).exists_boundary

end FiniteChains.Comb
