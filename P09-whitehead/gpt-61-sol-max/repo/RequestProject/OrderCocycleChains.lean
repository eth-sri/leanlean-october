import Mathlib.Tactic

import RequestProject.OrderCxMonodromy
import RequestProject.UnivCoverIncl

/-! Integral cellular cocycles obtained from actual order cocycles. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.OrdCocycle
variable {P : Type u} [Preorder P] {M : Type v} [AddCommGroup M]
  (c : OrdCocycle P (Multiplicative M))

noncomputable def chain1 : ((orderCx P).E →₀ ℤ) →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ (fun e => Multiplicative.toAdd (c.val e.1.1 e.1.2))

theorem chain1_pathChain (p : List ((orderCx P).E × Bool)) :
    c.chain1 (pathChain p) = Multiplicative.toAdd (c.readPath p) := by
  classical
  induction p <;> aesop (add simp [chain1, readPath, pathChain, pathChain_cons, map_add, readPath_cons])

theorem chain1_bdry2 (d : (orderCx P).F →₀ ℤ) : c.chain1 (bdry2 (orderCx P) d) = 0 := by
  induction d using Finsupp.induction_linear <;> simp_all [chain1_pathChain]

/-- Pull an actual order cocycle back along a monotone map. -/
def pullback {Q : Type u} [Preorder Q] (f : Q → P) (hf : Monotone f) :
    OrdCocycle Q (Multiplicative M) where
  val a b := c.val (f a) (f b)
  comp hab hbc := c.comp (hf hab) (hf hbc)

theorem pullback_readPath {Q : Type u} [Preorder Q] (f : Q → P) (hf : Monotone f)
    (p : List ((orderCx Q).E × Bool)) :
    (c.pullback f hf).readPath p = c.readPath (mapPath (orderCxMap f hf) p) := by
  induction p <;> aesop (add simp [mapPath, List.map_cons, readPath_cons])

end FiniteChains.Comb.OrdCocycle
