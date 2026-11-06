module

public import proofs.RAFCriticalWindowQuantitative.FiniteOpenCount
public import proofs.RAFCriticalWindowQuantitative.QuotientSparseClosure
public import proofs.HordijkSteelThreshold.StaticSurvivalContinuity
public import proofs.RAFReactionQuotient.SurvivalContinuity

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAFReactionQuotient RAF.Polymer RAF.Concrete
open OverlapCorrectedRAF.Source MeasureTheory unitInterval
open scoped ENNReal

def sparseWitnessCap (r : ℕ) : ℕ := 2*(2^(r+1)+2)

def splitSparseCoefficient (r : ℕ) : ℕ := (Fintype.card (Reaction (sparseWitnessCap r))).choose r

def quotientSparseCoefficient (r : ℕ) : ℕ := (Fintype.card (RepositoryChannel (sparseWitnessCap r))).choose r

theorem split_sparse_probability (a : I) (r : ℕ) :
    staticSurvival a ≤ (splitSparseCoefficient r : ENNReal)*(toNNReal a : ENNReal)^r := by
  let K := 2^(r+1)
  have hs : staticEscapeEvent 2 K ⊆ {ω | r ≤ (Finset.univ.filter (fun j : Reaction (2*(K+2)) => ω j)).card} := by
    rintro ω ⟨x, hx, hlen⟩; by_contra hn
    change ¬ r ≤ (staticOpenReactions ω).card at hn
    have hb := sparse_closure_length _ (staticOpenReactions ω) x hx
    have hp : 2^((staticOpenReactions ω).card+1) ≤ 2^(r+1) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [moleculeWord_length] at hlen; dsimp [K] at hlen; omega
  have hle : staticSurvival a ≤ staticReactionMeasure (2*(K+2)) a (staticEscapeEvent 2 K) := by
    rw [finite_static_escape_measure_eq]
    exact measure_mono fun field hf => (reversibleEscapeEvent_iff 2 K field).mpr (hf (K+2))
  refine hle.trans ((measure_mono hs).trans ?_)
  simpa +instances only [staticReactionMeasure, Measure.infinitePi_eq_pi,
    splitSparseCoefficient, sparseWitnessCap, K, ENNReal.instLE, ENNReal.instPartialOrder] using
    finite_many_open_probability (Reaction (2*(K+2))) a r

theorem quotient_sparse_probability (a : I) (r : ℕ) :
    quotientSurvival a ≤ (quotientSparseCoefficient r : ENNReal)*(toNNReal a : ENNReal)^r := by
  let K := 2^(r+1)
  have hs : quotientEscapeEvent 2 K ⊆ {ω | r ≤ (Finset.univ.filter (fun j : RepositoryChannel (2*(K+2)) => ω j)).card} := by
    rintro ω ⟨x, hx, hlen⟩; by_contra hn
    change ¬ r ≤ (quotientOpen ω).card at hn
    have hb := quotient_sparse_closure_length _ (quotientOpen ω) x hx
    have hp : 2^((quotientOpen ω).card+1) ≤ 2^(r+1) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [moleculeWord_length] at hlen; dsimp [K] at hlen; omega
  have hle : quotientSurvival a ≤ quotientStaticMeasure (2*(K+2)) a (quotientEscapeEvent 2 K) := by
    rw [quotient_escape_measure_eq, quotientSurvival_eq]
    exact measure_mono fun field hf => (reversibleEscapeEvent_iff 2 K field).mpr (hf (K+2))
  exact hle.trans ((measure_mono hs).trans (finite_many_open_probability (RepositoryChannel (2*(K+2))) a r))

theorem split_sparse_real (a : I) (r : ℕ) :
    (staticSurvival a).toReal ≤ (splitSparseCoefficient r : ℝ)*(a : ℝ)^r := by
  simpa using ENNReal.toReal_mono (by finiteness) (split_sparse_probability a r)

theorem quotient_sparse_real (a : I) (r : ℕ) :
    (quotientSurvival a).toReal ≤ (quotientSparseCoefficient r : ℝ)*(a : ℝ)^r := by
  simpa using ENNReal.toReal_mono (by finiteness) (quotient_sparse_probability a r)

end RAFCriticalWindowQuantitative
