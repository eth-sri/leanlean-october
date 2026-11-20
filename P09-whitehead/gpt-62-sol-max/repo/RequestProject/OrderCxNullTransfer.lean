module

public import RequestProject.OrderCxNatHtpy
public import RequestProject.OrderCxConeNull

@[expose] public section

/-! Null homotopies transfer through an actual order homotopy, including changing bases. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb

variable {P Q : Type} [Preorder P] [Preorder Q]

/-- An explicit three-step order contraction gives simple connectedness. -/
theorem simplyConnected_orderCx_of_zigzag {f g : P → P}
    (hf : Monotone f) (hg : Monotone g) (hig : ∀ x, x ≤ g x)
    (hfg : ∀ x, f x ≤ g x) (d : P) (hfd : ∀ x, f x ≤ d) :
    SimplyConnected (orderCx P) := by
  intro a p hp
  have hc := htpy_nil_mapPath_const d hp
  have hfnil := (htpy_nil_mapPath_le_iff hf monotone_const hfd hp).mpr hc
  have hgnil := (htpy_nil_mapPath_le_iff hf hg hfg hp).mp hfnil
  have hinil := (htpy_nil_mapPath_le_iff monotone_id hg hig hp).mpr hgnil
  simpa [mapPath, orderCxMap] using hinil

/-- The same contraction supplies paths to the common point, hence connectedness. -/
theorem isConnected_orderCx_of_zigzag {f g : P → P}
    (hig : ∀ x, x ≤ g x) (hfg : ∀ x, f x ≤ g x)
    (d : P) (hfd : ∀ x, f x ≤ d) : IsConnected (orderCx P) := by
  let p (a : P)  :=
    [ordPos (hig a), ordNeg (hfg a), ordPos (hfd a)]
  have hp (a : P) : IsPath (orderCx P).src (orderCx P).tgt (p a) a d :=
    ⟨rfl, rfl, rfl, rfl⟩
  intro a b
  exact ⟨p a ++ revPath (p b), (hp a).append (isPath_revPath (hp b))⟩

end FiniteChains.Comb
