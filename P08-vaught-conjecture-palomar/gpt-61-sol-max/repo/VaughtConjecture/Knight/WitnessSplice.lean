import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.PullbackSemantics
import VaughtConjecture.Knight.WitnessAlgebra
import VaughtConjecture.Knight.NormalForm

/-! # Witness-level transformation tools: probes, source collapse, truncation, cap, splices

* **Controller probes, ordered.**  From locality at `Sig` with witnesses `(g, σ)`:
  `RespectsSemanticsBelow.probe_ge_of_row_eq` (antitone `g`): equal sources at grades `k ≤ k'`
  give `min (q d') (q Sig) ≤ min (q d) (q Sig)`; a cell whose source is the diagonal's is labelled
  at least `q Sig` (`ge_of_row_eq_diag`).  `probe_le_of_lt` (monotone `σ`): a smaller source
  gives a smaller probe when the larger probe lies strictly below the cap.
* **Source collapse** (`TransformsTo.collapse`): a transformation from `f` also transforms any
  `f'` with `min (f' d) ξ = f d`, for a `K`-visible ordinal cutoff `ξ` above every `f d`
  (witnesses `σ ∘ min (·, ξ)` and `g` truncated to `⊥` above `K`).  A directional source
  precomposition, not transitivity.
* **Witnesses.**  A `Witness g σ` bundles the five clauses of Def. 2.3.9.  `Witness.truncate`
  (`g` set to `⊥` above `K`), `Witness.cap` (the Cap Lemma at the witness level),
  `Witness.raise` (`σ` raised to at least a `K`-visible `c` on the nonbottom fibre above a cutoff
  `ξ` with `K < finitePart ξ`), `Witness.lower` (`σ` lowered to at most `c` on the tail of the
  block of `ξ`, when `σ ≤ c` below `ξ`).  The grade bound and the cutoff visibility are explicit
  hypotheses throughout.

Construction-private (not root-exported). -/

namespace VaughtConjecture.Knight

open  Value ExtOrd



/-- A label is at most its visibility replacement at its own threshold. -/
theorem le_extVisibilityReplace_self x k : x ≤ extVisibilityReplace x k k := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · exact le_rfl
  · exact le_rfl
  · rw [extVisibilityReplace_ofOrd, ofOrd_le_ofOrd]
    unfold visibilityReplace
    split_ifs with h
    · 
      calc α = limitPart α + ↑(finitePart α) := (decomposition α).symm
        _ ≤ limitPart α + (k) := add_le_add_right (by exact_mod_cast h.le) _
    · exact le_rfl

theorem limitPart_visibilityReplace α k i :
    limitPart (visibilityReplace α k i) = limitPart α := by
  unfold visibilityReplace
  split_ifs
  · exact limitPart_limitPart_add_nat α i
  · rfl

/-! ## Splices of the shifter -/

