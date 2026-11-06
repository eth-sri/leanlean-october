import proofs.RAFCriticalWindowQuantitative.FiniteClosure
import proofs.RAFCriticalWindowQuantitative.SeedDeficit
import proofs.HordijkSteelThreshold.StaticEventContinuity
import proofs.RAFCriticalWindowQuantitative.FiniteEscapeAdapters


namespace RAFCriticalWindowQuantitative

open Classical HordijkSteelThreshold MeasureTheory

variable (J : Type*)

variable [Fintype J] [DecidableEq J] (q : ℚ)

def rationalEventProbability  
    (event : (J → Bool) → Bool)  :=
  ∑ ω : J → Bool, if event ω then ∏ j, if ω j then q else 1-q else 0

/-- Exact probability semantics for an arbitrary executable Boolean event. -/
theorem rationalEventProbability_correct  
    (hq : _) (hq1 : _) (event : _) :
    ((Measure.pi (fun _ : J => ambientCoordLaw (rationalParameter q hq hq1)))
      {ω | event (fun j => decide (ω j))}).toReal =
      rationalEventProbability J q event := by
  classical
  change Measure.real _ _ = _
  rw [← Finset.coe_filter_univ, ← sum_measureReal_singleton]
  simp only [measureReal_def, Measure.pi_singleton, ambientCoordLaw_atom,
    ENNReal.toReal_prod, ENNReal.coe_toReal, Finset.sum_filter]
  rw [← (Equiv.piCongrRight fun _ : J => Equiv.propEquivBool.symm).sum_comp]
  simp [rationalEventProbability, Equiv.propEquivBool,
    staticAtomWeight, rationalParameter, apply_ite]

open RAFReactionQuotient RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

def splitEscapeBool (N K : ℕ) (ω : Reaction N → Bool)  :=
  decide (∃ x ∈ computedClosure N 2 (Finset.univ.filter (fun r => ω r)), K < molLength x)

def quotientEscapeBool (N K : ℕ) (ω : RepositoryChannel N → Bool)  :=
  splitEscapeBool N K (fun r => ω (splitToQuotient r))

def splitEscapeEval (q : ℚ) (K : ℕ)  :=
  rationalEventProbability (Reaction (2*(K+2))) q (splitEscapeBool _ (K+2))

def quotientEscapeEval (q : ℚ) (K : ℕ)  :=
  rationalEventProbability (RepositoryChannel (2*(K+2))) q (quotientEscapeBool _ (K+2))

variable (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (K : ℕ)

theorem splitEscapeEval_correct  :
    splitEscapeEval q K =
      (staticReactionMeasure _ (rationalParameter q hq hq1) (staticEscapeEvent 2 K)).toReal := by
  classical
  simpa [splitEscapeEval, splitEscapeBool, computedClosure_eq, staticOpenReactions,
    staticEscapeEvent,moleculeWord_length,staticReactionMeasure] using
    (rationalEventProbability_correct (Reaction (2*(K+2))) q hq hq1 (splitEscapeBool _ (K+2))).symm

theorem quotientEscapeEval_correct  :
    quotientEscapeEval q K =
      (quotientStaticMeasure _ (rationalParameter q hq hq1) (quotientEscapeEvent 2 K)).toReal := by
  classical
  simpa [quotientEscapeEval, quotientEscapeBool, splitEscapeBool, computedClosure_eq, quotientStaticMeasure, quotientClosure_pullback, staticOpenReactions, quotientEscapeEvent, moleculeWord_length] using
    (rationalEventProbability_correct (RepositoryChannel (2*(K+2))) q hq hq1
      (quotientEscapeBool _ (K+2))).symm

end RAFCriticalWindowQuantitative
