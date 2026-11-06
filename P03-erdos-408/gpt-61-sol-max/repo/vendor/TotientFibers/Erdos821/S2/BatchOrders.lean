module
public import Mathlib.Tactic

public import Erdos821.S2.SpanHistory
public import Mathlib.Data.List.FinRange

/-! Ordered ghost batches have permutation fibers with invariant coefficients. -/

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {P : PrimeGroups}

theorem zeroBirthBatch_perm {g : P.Group} {b : ℕ} (p : Fin b → P.Prime g)
    (sigma : Equiv.Perm (Fin b)) :
    zeroBirthBatch (fun i => p (sigma i)) = zeroBirthBatch p := by
  unfold zeroBirthBatch
  exact Multiset.coe_eq_coe.mpr (sigma.ofFn_comp_perm (fun i => (⟨p i, 0⟩ : P.Particle g)))

def reorderGhostChoice {M } {s t : P.MemoryState M} (c : GhostChoice s t)
    (sigma : (g : P.BigGroup) → Equiv.Perm (Fin (c.2.1 g).val)) : GhostChoice s t :=
  ⟨c.1, c.2.1, fun g i => c.2.2 g (sigma g i)⟩

section
variable (F : FixedData) (n : ℕ) (rho : ℝ) (i : Fin (n + 1)) {M : ℕ} {s t : P.MemoryState M} (c : GhostChoice s t) (sigma : (g : P.BigGroup) → Equiv.Perm (Fin (c.2.1 g).val))


theorem reorderGhostChoice_valid      
      :
    ghostChoiceValid (reorderGhostChoice c sigma) ↔ ghostChoiceValid c := by
  unfold ghostChoiceValid reorderGhostChoice
  simp only [zeroBirthBatch_perm]

theorem reorderGhostChoice_weight      
           
      :
    ghostChoiceWeight F n rho i (reorderGhostChoice c sigma) =
      ghostChoiceWeight F n rho i c := by
  unfold ghostChoiceWeight reorderGhostChoice
  apply Finset.prod_congr rfl
  intro g _
  congr 1
  exact Equiv.prod_comp (sigma g) (fun h => tiltedMu F P n g.val (c.2.2 g h))

theorem reorderGhostChoice_injective    
      (hp : ∀ g, Function.Injective (c.2.2 g)) :
    Function.Injective (reorderGhostChoice c) := fun ⦃sigma tau⦄ he => funext fun g => Equiv.ext fun i => hp g (congrFun (congrFun (eq_of_heq (Sigma.mk.inj_iff.mp (Prod.mk.inj he).right).right) g) i)

end

end Erdos821.S2Core
