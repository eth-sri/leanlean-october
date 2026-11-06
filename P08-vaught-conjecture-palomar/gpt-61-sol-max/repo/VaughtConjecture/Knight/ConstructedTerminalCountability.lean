import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.NonHollowGrowthProlongation
import VaughtConjecture.Knight.HollowGrowthComparison
import VaughtConjecture.Knight.TopGradeTerminalCounting
import VaughtConjecture.Knight.BlockSuccessor
import VaughtConjecture.Knight.GrowthProlongationInterface

/-! # Constructed terminal countability, before the spectrum applications

Non-hollow growth prolongs; hollow growth models compare. Together with the
top-grade count of `TopGradeTerminalCounting` (rigid cores, eventual top grade,
hollow growth), these give countable terminal fibres. The count consumes the
coinitial top-grade tail directly; it does not pass through characteristic.
Neither cofinal high-stage existence nor an exact-cardinality conclusion is an
input. Both cardinality and expansion-domain thinness consume this producer.

The historical namespace and theorem names are retained. This separates the
producer from the cardinality application, not from all rank-related imports
inside the existing classification infrastructure.
-/

namespace VaughtConjecture.Knight.ConstructedSpectrumEndpoint
open  KnightRealization
universe w

/-- The constructed non-hollow growth prolongation producer at every block stage. -/
theorem growthAnchorProlongationAt {M : Type w} {ρ : Ordinal₀}
    {W : KnightRealization (blockStage ρ) M} (hW : W.IsModel) :
    GrowthAnchorProlongationAt W := by
  rintro ⟨hh, hg⟩
  rw [prolongsToIn_isModelClass_iff_on]
  exact NonHollowGrowthReceiving.prolongsToOnIn_of_eq_nextBlock hW hh hg
    (blockStage_succ_eq_nextBlock ρ) _

/-- Every countable-rank terminal fibre has countably many isomorphism classes. -/
def countableTerminalFibres :=
  TopGradeTerminalCounting.countableTerminalFibres_of_growth_results
    (fun _ _ W hh hg => growthAnchorProlongationAt W.2.1 ⟨hh, hg⟩)
    (fun _ _ W V hgW hgV hhW hhV =>
      HollowGrowth.nonempty_iso W.2.1 V.2.1 hgW hgV hhW hhV)

