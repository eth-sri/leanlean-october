/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.Model

/-! # Empty-tuple evaluation from consistency and covering

This elementary model consequence is independent of terminal histories and rank analysis. -/

namespace VaughtConjecture.Knight


namespace KnightRealization

variable {α : LimitStage} {M : Type*}

/-- Stage-generic empty evaluation, the only missing adapter in the preserved pair-local
terminal-code draft. -/
theorem exists_eval_empty_of_structural {R : KnightRealization α M}
    (hcons : R.IsExactParentConsistent) (hcov : R.IsInitialSegmentCovering) :
    ∃ p₀ : S α.1 0,
      R.eval (Function.Embedding.ofIsEmpty : Fin 0 ↪ M) = some p₀ := by
  obtain ⟨k, s, -, hsome⟩ := hcov (Function.Embedding.ofIsEmpty : Fin 0 ↪ M)
  obtain ⟨Q, hQ⟩ := Option.isSome_iff_exists.mp hsome
  let f : Fin 0 ↪ Fin (0 + k) := Function.Embedding.ofIsEmpty
  have heval := hcons s Q f hQ
  have hsome' : (knightTower.pull f Q).isSome := by
    
    apply (typeMap_isSome_iff).mpr
    have h0 : Finset.univ.image f = (∅) := by
      simp 
    
    exact Q.scheme.scheme.isPlan.empty_mem
  obtain ⟨p₀, hp₀⟩ := Option.isSome_iff_exists.mp hsome'
  have hft : f.trans s = (Function.Embedding.ofIsEmpty) :=
    Function.Embedding.ext fun i => i.elim0
  exact ⟨p₀, by rw [← hft, heval, hp₀]; rfl⟩

/-- Compatibility wrapper for models. -/
def exists_eval_empty_at {R : KnightRealization α M} (hR : R.IsModel) :=
  exists_eval_empty_of_structural hR.consistent hR.covering


