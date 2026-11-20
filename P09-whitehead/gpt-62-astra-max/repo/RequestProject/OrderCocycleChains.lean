module

public import RequestProject.OrderCxMonodromy
public import RequestProject.UnivCoverIncl

@[expose] public section

/-! Integral cellular cocycles obtained from actual order cocycles. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.OrdCocycle
universe u v
variable {P : Type u} [Preorder P] {M : Type v} [AddCommGroup M]
  (c : OrdCocycle P (Multiplicative M))

noncomputable def chain1 : ((orderCx P).E →₀ ℤ) →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ (fun e => Multiplicative.toAdd (c.val e.1.1 e.1.2))

theorem chain1_pathChain (p : List _) :
    c.chain1 (pathChain p) = Multiplicative.toAdd (c.readPath p) := by
  induction p with
  | nil => rfl
  | cons eb p ih =>
      rw [pathChain_cons, map_add, ih, readPath_cons]
      obtain ⟨e, b⟩ := eb; cases b <;> simp [chain1, readGerm]

theorem chain1_bdry2 (d : (orderCx P).F →₀ ℤ) : c.chain1 (bdry2 (orderCx P) d) = 0 := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simp_all
  | single t n => simp [bdry2_single, LinearMap.map_smul, chain1_pathChain, readPath_att]

variable {Q : Type u} [Preorder Q] (f : Q → P) (hf : Monotone f)

/-- Pull an actual order cocycle back along a monotone map. -/
def pullback :
    OrdCocycle Q (Multiplicative M) where
  val a b := c.val _ (f b)
  comp hab hbc := c.comp (hf hab) (hf hbc)

theorem pullback_readPath
    (p : List _) :
    (c.pullback f hf).readPath p = c.readPath (mapPath (orderCxMap f hf) p) := by
  induction p with
  | nil => rfl
  | cons eb p ih =>
      aesop

end FiniteChains.Comb.OrdCocycle
