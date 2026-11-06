module

public import proofs.RAFCriticalWindowQuantitative.FiniteSeedEvaluation
public import proofs.RAFCriticalWindowQuantitative.QuotientEffectiveBulk
public import proofs.HordijkSteelThreshold.SourceStaticRAFBound
public import proofs.RAFReactionQuotient.SourceBounds

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open scoped ENNReal

theorem split_finite_source_lower (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (lambda : ℝ)
    (hk : 6 < nearFullPoolSize n m)
    (hpool : rationalParameter q hq.le hq1 ≤ fixedPoolParameter (catalysisP n lambda) (nearFullPoolSize n m)) :
    staticReactionMeasure n (rationalParameter q hq.le hq1)
      {ω | binaryFood n (10*seedIndex q hq hq1 m) ⊆ temporaryReactionClosure 2 (staticOpenReactions ω)} ≤
      uniformCatalysisMeasure n lambda (HasRAFEvent n) + (m : ENNReal)⁻¹ := by
  have he : (finiteInitialSegment (Molecule n) (nearFullPoolSize n m)).card = nearFullPoolSize n m :=
    card_finiteInitialSegment _ _ (nearFullPoolSize_le n m)
  exact (seed_mass_union_bound _ n _ m staticOpenReactions _ fun _ h => h).trans
    (add_le_add (canonical_raf_ge_near_full_static n m lambda hm (rationalParameter q hq.le hq1) hk
      (by change _ ≤ fixedPoolParameter _ (finiteInitialSegment (Molecule n) (nearFullPoolSize n m)).card; rwa [he]))
      (effective_static_bulk q hq hq1 m hm n hn))

theorem quotient_finite_source_lower (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (p : I)
    (hk : 6 < nearFullPoolSize n m)
    (hpool : rationalParameter q hq.le hq1 ≤ fixedPoolParameter p (nearFullPoolSize n m)) :
    let hh : 0 < q/2 := by positivity
    let hh1 : q/2 ≤ 1 := by linarith
    quotientStaticMeasure n (rationalParameter q hq.le hq1)
      {ω | binaryFood n (10*seedIndex (q/2) hh hh1 m) ⊆ quotientClosure n 2 (quotientOpen ω)} ≤
      quotientRAFProbability n p + (m : ENNReal)⁻¹ := by
  dsimp only
  have h1 : quotientStaticMeasure n (rationalParameter q hq.le hq1)
      {ω | binaryFood n (10*seedIndex (q/2) (by positivity) (by linarith) m) ⊆ quotientClosure n 2 (quotientOpen ω)} ≤
      quotientStaticMeasure n (rationalParameter q hq.le hq1)
        {ω | (m-1)*Fintype.card (Molecule n) ≤ m*(quotientClosure n 2 (quotientOpen ω)).card} +
      quotientStaticMeasure n (rationalParameter q hq.le hq1)
        {ω | m*(quotientClosure n (10*seedIndex (q/2) (by positivity) (by linarith) m) (quotientOpen ω)).card <
          (m-1)*Fintype.card (Molecule n)} := by
    simp_rw [quotientClosure_pullback]
    exact seed_mass_union_bound _ n _ m _ _ fun _ h => h
  exact h1.trans (add_le_add (quotient_near_full_lower n m p _ hm hk hpool)
    (effective_quotient_bulk q hq hq1 m hm _ le_rfl n hn))

end RAFCriticalWindowQuantitative
