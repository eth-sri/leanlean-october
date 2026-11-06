module

public import proofs.RAFCriticalWindowQuantitative.EscapeEvaluation

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient RAF.Polymer RAF.Concrete
open OverlapCorrectedRAF.Source MeasureTheory

def splitSeedBool (N L : ℕ) (ω : Reaction N → Bool) : Bool :=
  decide (binaryFood N L ⊆ computedClosure N 2 (Finset.univ.filter (fun r => ω r)))

def quotientSeedBool (N L : ℕ) (ω : RepositoryChannel N → Bool) : Bool :=
  splitSeedBool N L (fun r => ω (splitToQuotient r))

def splitSeedEval (N L : ℕ) (q : ℚ) : ℚ :=
  rationalEventProbability (Reaction N) q (splitSeedBool N L)

def quotientSeedEval (N L : ℕ) (q : ℚ) : ℚ :=
  rationalEventProbability (RepositoryChannel N) q (quotientSeedBool N L)

theorem splitSeedEval_correct (N L : ℕ) (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (splitSeedEval N L q : ℝ) =
      (staticReactionMeasure N (rationalParameter q hq hq1)
        {ω | binaryFood N L ⊆ temporaryReactionClosure 2 (staticOpenReactions ω)}).toReal := by
  classical
  rw [splitSeedEval, ← rationalEventProbability_correct (Reaction N) q hq hq1,
    staticReactionMeasure, Measure.infinitePi_eq_pi]
  congr 2; ext ω
  simp [splitSeedBool, computedClosure_eq, staticOpenReactions]

theorem quotientSeedEval_correct (N L : ℕ) (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (quotientSeedEval N L q : ℝ) =
      (quotientStaticMeasure N (rationalParameter q hq hq1)
        {ω | binaryFood N L ⊆ quotientClosure N 2 (quotientOpen ω)}).toReal := by
  classical
  rw [quotientSeedEval, ← rationalEventProbability_correct (RepositoryChannel N) q hq hq1]
  congr 2; ext ω
  simp only [Set.mem_ofPred_eq, quotientSeedBool, splitSeedBool, decide_eq_true_eq, computedClosure_eq]
  change (binaryFood N L ⊆ temporaryReactionClosure 2 (staticOpenReactions (fun r => ω (splitToQuotient r)))) ↔ _
  rw [← quotientClosure_pullback]

end RAFCriticalWindowQuantitative
