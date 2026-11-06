module

public import proofs.RAFCriticalWindowQuantitative.EffectiveBulk
public import proofs.RAFReactionQuotient.SeedBulk

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold RAFReactionQuotient
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open scoped ENNReal

/-- Explicit seed cutoff transported through the source's bounded-fibre domination. -/
theorem effective_quotient_bulk (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m : ℕ) (hm : 0 < m) :
    let hhalf : 0 < q/2 := by positivity
    let hhalf1 : q/2 ≤ 1 := by linarith
    let L := 10*seedIndex (q/2) hhalf hhalf1 m
    ∀ a : I, rationalParameter q hq.le hq1 ≤ a → ∀ n : ℕ, 0 < n →
      quotientStaticMeasure n a {ω |
        m*(quotientClosure n L (quotientOpen ω)).card <
          (m-1)*Fintype.card (Molecule n)} ≤ (m : ENNReal)⁻¹ := by
  dsimp only
  have hhalf : 0 < q/2 := by positivity
  have hhalf1 : q/2 ≤ 1 := by linarith
  let a0 := rationalParameter q hq.le hq1
  let L := 10*seedIndex (q/2) hhalf hhalf1 m
  have hbulk := effective_static_bulk (q/2) hhalf hhalf1 m hm
  dsimp only at hbulk
  rw [show rationalParameter (q/2) hhalf.le hhalf1 = halfParameter a0 from
    Subtype.ext (by simp [rationalParameter, halfParameter, a0])] at hbulk
  intro a ha n hn
  let E := fun ω : RepositoryChannel n → Prop =>
    m*(quotientClosure n L (quotientOpen ω)).card < (m-1)*Fintype.card (Molecule n)
  have hi := product_decreasing_mono
    (fibreParameter (@splitToQuotient n) (halfParameter a0)) (fun _ => a)
    (fun j => (fibreParameter_half_le splitToQuotient a0 j
      (by convert split_fibre_le_two j using 1; congr 1; ext; simp)).trans ha)
    E (quotient_mass_failure_antitone n L m)
  rw [← fieldOR_map (@splitToQuotient n) (halfParameter a0),
    Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet] at hi
  refine hi.trans ?_
  simpa only [Set.preimage_ofPred_eq, Set.mem_ofPred_eq, E, quotientClosure_OR, staticReactionMeasure,
    Measure.infinitePi_eq_pi, RAFEmergenceApprox.Generic.colLaw] using hbulk n hn

end RAFCriticalWindowQuantitative
