import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CofinalEnumeration
import VaughtConjecture.Knight.LimitOfChain
import VaughtConjecture.Knight.PartialExpansion

/-! # Countable-limit expansion existence

A model that expands, on its own carrier, to every block below a countable limit `l` expands
to block `l` (`exists_model_at_limit_of_forall_lt`): choose a cofinal `ℕ`-sequence of blocks
(countability of `l` supplies the enumeration; the carrier need not be countable), take the
unique partial expansions at those blocks — coherent by expansion uniqueness — and apply the
constructed model-limit theorem.  This is the limit branch of the canonical-stop argument with
the stop rank replaced by an arbitrary countable limit and the lower witnesses supplied as a
hypothesis; `CanonicalStop` and the expansion-domain continuity theorem are its clients.
No stopping rank, termination, or terminal classification is used. -/

namespace VaughtConjecture.Knight.KnightRealization

open TypeTower Cardinal

universe w

variable {M : Type w}

/-- **Expansion to a countable limit block** from expansions to every lower block. -/
theorem exists_model_at_limit_of_forall_lt {l} (hlim : Order.IsSuccLimit l)
    (hl : l < (aleph 1).ord) {R}
    (h : ∀ ξ, ξ < l → ∃ W : KnightRealization (blockStage ξ) M,
      W.IsModel ∧ W.reduct (blockStage_zero_le ξ) = R) :
    ∃ W : KnightRealization (blockStage l) M,
      W.IsModel ∧ W.reduct (blockStage_zero_le l) = R := by 
  have h0  := hlim.pos
  obtain ⟨g, hg1, hg2⟩ := exists_nat_enum_lt hl h0
  have hcs_lt  := cofSeq_lt h0 hg1
  have hmono  := cofSeq_monotone 0 g
  let bases (n : ℕ) : PartialExpansion.Domain
      (zero_le) M :=
    ⟨R, h _ (hcs_lt n)⟩
  let W (n : ℕ) := PartialExpansion.value _ (bases n)
  have hWm (n : ℕ) : (W n).IsModel := PartialExpansion.isModel _ (bases n)
  have hWr (n : ℕ) : (W n).reduct (blockStage_zero_le (cofSeq 0 g n)) = R :=
    PartialExpansion.reduct_value _ (bases n)
  have hc : Monotone fun n => blockStage (cofSeq 0 g n) := fun i j h =>
    blockStage_mono (hmono h)
  have hchain : IsReductChain hc W := by
    intro i j h
    exact PartialExpansion.coherent zero_le (hmono h) (bases j) (bases i) rfl
  have hδ  := fun i =>
    blockStage_mono (hcs_lt i).le
  have hcof : ∀ γ , γ < (blockStage l).1 →
      ∃ i, γ < (blockStage (cofSeq 0 g i)).1 := fun γ hγ =>
    exists_lt_blockStage_of_cofinal hlim (fun ξ hξ => lt_cofSeq hlim hg2 hξ) hγ
  let core1 := limitOfChain hc W hchain (blockStage l) hδ
  refine ⟨core1,
    IsModel.limitOfChain hc hchain hWm (blockStage l) hδ hcof, ?_⟩
  calc core1.reduct (blockStage_zero_le l)
      = (core1.reduct
          (hδ 0)).reduct (blockStage_zero_le (cofSeq 0 g 0)) := by
        rw [Realization.reduct_reduct]
    _ = (W 0).reduct (blockStage_zero_le (cofSeq 0 g 0)) := by
        simp_rw [core1, reduct_limitOfChain]
    _ = R := hWr 0

