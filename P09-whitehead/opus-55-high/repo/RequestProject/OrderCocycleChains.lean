import RequestProject.OrderCxMonodromy
import RequestProject.UnivCoverIncl
import RequestProject.Tac


/-! Integral cellular cocycles obtained from actual order cocycles. -/
bwd

namespace FiniteChains.Comb.OrdCocycle
universe u v
variable {P : Type u} [Preorder P] {M : Type v} [AddCommGroup M]
  (c : OrdCocycle P (Multiplicative M))

noncomputable def chain1 : ((orderCx P).E →₀ ℤ) →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ (fun e => Multiplicative.toAdd (c.val e.1.1 e.1.2))

theorem chain1_pathChain p :
    c.chain1 (pathChain p) = Multiplicative.toAdd (c.readPath p) := by
  induction p with
  | nil => rfl
  | cons eb p ih =>
      rw [pathChain_cons, map_add, ih, readPath_cons]
      cases' eb with e b
      cases b <;> simp [chain1, readGerm]

theorem chain1_bdry2 d : c.chain1 (bdry2 (orderCx P) d) = 0 := by
  lin_ind d t n => rw [bdry2_single, LinearMap.map_smul, chain1_pathChain, readPath_att]; simp

/-- Pull an actual order cocycle back along a monotone map. -/
def pullback {Q : Type u} [Preorder Q] (f : Q → P) (hf : Monotone f) :
    OrdCocycle Q (Multiplicative M) where
  val a b := c.val (f a) (f b)
  comp hab hbc := c.comp (hf hab) (hf hbc)

