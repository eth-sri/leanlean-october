module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootWordCancellationSum

/-!
# Reindexing the fixed-amplitude word sum into root-slot fibers

Every permutation occurs in exactly one fiber, determined by the slot carrying
the distinguished label. This is the finite-sum interface used to separate
root-incident T₁ words from terms canceled away from that slot.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- All permutations grouped by the slot which carries the label `l`. -/
abbrev RootSlotFiberIndex (n : ℕ) (l : Fin (n + 1)) :=
  {q : Fin (n + 1) × Equiv.Perm (Fin (n + 1)) // q.2 q.1 = l}

/-- The root-slot fibers partition the permutation group. -/
noncomputable def rootSlotFiberEquiv {n : ℕ} (l : Fin (n + 1)) :
    RootSlotFiberIndex n l ≃ Equiv.Perm (Fin (n + 1)) where
  toFun q := q.1.2
  invFun σ := ⟨(σ.symm l, σ), σ.apply_symm_apply l⟩
  left_inv := by
    grind
  right_inv := by
    grind


end PottsDiscontinuity.BetheAnsatz
