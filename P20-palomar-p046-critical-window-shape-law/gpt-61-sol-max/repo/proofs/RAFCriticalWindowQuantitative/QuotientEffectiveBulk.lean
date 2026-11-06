
import proofs.RAFCriticalWindowQuantitative.EffectiveBulk
import proofs.RAFReactionQuotient.SeedBulk


namespace RAFCriticalWindowQuantitative
open MeasureTheory unitInterval HordijkSteelThreshold RAFReactionQuotient
open RAF.Polymer OverlapCorrectedRAF.Source

/-- Explicit seed cutoff transported through the source's bounded-fibre domination. -/
theorem effective_quotient_bulk (q : ℚ) (hq : 0 < q) (hq1 : _)
    (m : ℕ) :
    let hhalf  := by positivity
    let hhalf1  := by linarith
    let L := 10*seedIndex (q/2) hhalf hhalf1 m
    ∀ a : I, rationalParameter q hq.le hq1 ≤ a → ∀ n : ℕ, 0 < n →
      quotientStaticMeasure n a {ω |
        MassDeficit m (quotientClosure n L (quotientOpen ω))} ≤ (m : ENNReal)⁻¹ := by
  dsimp 
  have hhalf : 0 < q/2 := by positivity
  have hhalf1 : q/2 ≤ 1 := by linarith
  let a0 := rationalParameter q hq.le hq1
  let L := 10*seedIndex (q/2) hhalf hhalf1 m
  intro a ha n hn
  let E := fun ω : RepositoryChannel n → Prop =>
    MassDeficit m (quotientClosure n L (quotientOpen ω))
  have hi := product_decreasing_mono
    (fibreParameter (@splitToQuotient n) (halfParameter a0)) (fun _ => a)
    (fun j => ha.trans' (by
      have ha0 := a0.property.1
      change 1-(1-(a0 : ℝ)/2)^_ ≤ a0
      generalize ht : Finset.card _ = t
      have hm : t ≤ 2 := by
        rw [← ht]
        convert split_fibre_le_two j using 1
        congr 1
        ext r
        simp
      interval_cases t <;> norm_num <;> nlinarith))
    E (quotient_mass_failure_antitone n L m)
  
  rw [← fieldOR_map (@splitToQuotient n) (halfParameter a0), Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet] at hi
  apply hi.trans
  simpa [E,quotientClosure_OR,staticReactionMeasure,
    RAFEmergenceApprox.Generic.colLaw,halfParameter,rationalParameter,a0] using
    effective_static_bulk (q/2) hhalf hhalf1 m n hn

end RAFCriticalWindowQuantitative
