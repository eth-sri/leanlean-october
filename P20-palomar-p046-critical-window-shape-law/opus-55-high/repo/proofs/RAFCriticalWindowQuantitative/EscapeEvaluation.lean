module

public import proofs.RAFCriticalWindowQuantitative.FiniteEventProbability
public import proofs.RAFCriticalWindowQuantitative.FiniteEscapeAdapters

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open MeasureTheory

def splitEscapeBool (N K : ℕ) (ω : Reaction N → Bool) : Bool :=
  decide (∃ x ∈ computedClosure N 2 (Finset.univ.filter (fun r => ω r)), K < molLength x)

def quotientEscapeBool (N K : ℕ) (ω : RepositoryChannel N → Bool) : Bool :=
  splitEscapeBool N K $ fun r => ω $ splitToQuotient r

variable (q : ℚ) (K : ℕ)

def splitEscapeEval  : ℚ :=
  rationalEventProbability (Reaction $ 2*(K+2)) q (splitEscapeBool _ (K+2))

def quotientEscapeEval  : ℚ :=
  rationalEventProbability (RepositoryChannel $ 2*(K+2)) q (quotientEscapeBool _ (K+2))


theorem _root_.HordijkSteelThreshold.SplitModel.eval_correct (M : SplitModel) [∀ N, DecidableEq $ M.C N]
    (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (K : ℕ) :
    (rationalEventProbability (M.C $ 2*(K+2)) q (fun ω => splitEscapeBool _ (K+2) fun r => ω $ M.π r) : ℝ) =
      (M.μ _ (rationalParameter q hq hq1) $ M.esc K).toReal := by
  rw [← rationalEventProbability_correct _ q hq hq1]
  congr
  simp only [splitEscapeBool, decide_eq_true_eq, computedClosure_eq]
  rfl

end RAFCriticalWindowQuantitative
