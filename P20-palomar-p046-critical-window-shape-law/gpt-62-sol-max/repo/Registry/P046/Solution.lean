module

public import proofs.RAF.Concrete.PolymerCRS
public import proofs.RAFCriticalWindowQuantitative.ApproximationParameters
public import proofs.HordijkSteelThreshold.InfiniteStaticLaw
public import proofs.RAFReactionQuotient.QuotientMap
public import proofs.RAFCriticalWindowQuantitative.SourceContract
public import proofs.RAFCriticalWindowQuantitative.CertifiedEvaluator
public import proofs.RAFCriticalWindowQuantitative.SparseClosure

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient unitInterval RAF.Concrete OverlapCorrectedRAF.Source

/-- Compiled minimum quantitative/computability successor for both literal RAF models.
The programs are explicit definitions; no desired bound or validity oracle is assumed. -/
theorem quantitative_critical_window_resolution :
    ProfileGuarantees staticSurvival splitEscapeProbability
      splitTotalInterval splitEvaluationCap splitSparseCoefficient ∧
    ProfileGuarantees quotientSurvival quotientEscapeProbability
      quotientTotalInterval quotientEvaluationCap quotientSparseCoefficient ∧
    SourceGuarantees ∧
    (∀ N k S x, x ∈ temporaryReactionClosure (N := N) 2 S → 2^(k+1) < molLength x →
      ∃ T, ProductiveHistory (binaryPolymerCRS N 2) S k T ∧ T.card = k ∧ T ⊆ S) ∧
    (∀ N k S x, x ∈ quotientClosure N 2 S → 2^(k+1) < molLength x →
      ∃ T, ProductiveHistory (repositoryCRS N 2) S k T ∧ T.card = k ∧ T ⊆ S) ∧
    (∀ a : I, (a : ℝ) ≤ 1/10^20 → (staticSurvival a).toReal < 8/10^26) := by
  refine ⟨splitProfile, quotientProfile, source_guarantees, ?_, ?_, worked_low_openness_bound⟩ <;>
    intro N k S x hx hl
  all_goals
    have h := long_target_productive_history _ (by first | exact split_growth N | exact quotient_growth N)
      S k x (by simpa [temporaryReactionClosure, quotientClosure] using hx) hl
    grind

end RAFCriticalWindowQuantitative
