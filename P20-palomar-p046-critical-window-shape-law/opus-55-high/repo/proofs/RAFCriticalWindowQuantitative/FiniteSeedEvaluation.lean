module

public import proofs.RAFCriticalWindowQuantitative.EscapeEvaluation

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient RAF.Polymer RAF.Concrete
open OverlapCorrectedRAF.Source MeasureTheory

variable (N L : ℕ)

def splitSeedBool  (ω : Reaction N → Bool) : Bool :=
  decide $ binaryFood N L ⊆ computedClosure N 2 (Finset.univ.filter $ fun r => ω r)

def quotientSeedBool  (ω : RepositoryChannel N → Bool) : Bool :=
  splitSeedBool N L $ fun r => ω $ splitToQuotient r

variable (q : ℚ)

def splitSeedEval   : ℚ :=
  rationalEventProbability (Reaction N) q $ splitSeedBool N L

def quotientSeedEval   : ℚ :=
  rationalEventProbability (RepositoryChannel N) q $ quotientSeedBool N L


theorem _root_.HordijkSteelThreshold.SplitModel.seedEval_correct (M : SplitModel) [∀ N, DecidableEq $ M.C N]
    (N L : ℕ) (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (rationalEventProbability (M.C N) q (fun ω => splitSeedBool N L fun r => ω $ M.π r) : ℝ) =
      (M.μ N (rationalParameter q hq hq1) {x | binaryFood N L ⊆ M.cl N 2 x}).toReal := by
  rw [← rationalEventProbability_correct _ q hq hq1]
  congr
  simp only [splitSeedBool, decide_eq_true_eq, computedClosure_eq]
  rfl

end RAFCriticalWindowQuantitative
