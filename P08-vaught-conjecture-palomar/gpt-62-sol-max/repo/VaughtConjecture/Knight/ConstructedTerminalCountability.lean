/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.NonHollowGrowthProlongation
public import VaughtConjecture.Knight.HollowGrowthComparison
public import VaughtConjecture.Knight.TopGradeTerminalCounting
public import VaughtConjecture.Knight.BlockSuccessor
public import VaughtConjecture.Knight.GrowthProlongationInterface

@[expose] public section

namespace VaughtConjecture.Knight.ConstructedSpectrumEndpoint

open TypeTower KnightRealization

universe w

/-- The constructed non-hollow growth prolongation producer at every block stage. -/
theorem growthAnchorProlongationAt {M : Type w} {ρ : Ordinal.{0}}
    {W : KnightRealization (blockStage ρ) M} (hW : W.IsModel) :
    GrowthAnchorProlongationAt W := by
  rintro ⟨hh, hg⟩
  rw [prolongsToIn_isModelClass_iff_on]
  exact NonHollowGrowthReceiving.prolongsToOnIn_of_eq_nextBlock hW hh hg
    (blockStage_succ_eq_nextBlock ρ) _

/-- Every countable-rank terminal fibre has countably many isomorphism classes. -/
theorem countableTerminalFibres : CountableTerminalFibres :=
  TopGradeTerminalCounting.countableTerminalFibres_of_growth_results
    (fun _ _ W hh hg => growthAnchorProlongationAt W.2.1 ⟨hh, hg⟩)
    (fun _ _ W V hgW hgV hhW hhV =>
      HollowGrowth.nonempty_iso W.2.1 V.2.1 hgW hgV hhW hhV)

end VaughtConjecture.Knight.ConstructedSpectrumEndpoint
