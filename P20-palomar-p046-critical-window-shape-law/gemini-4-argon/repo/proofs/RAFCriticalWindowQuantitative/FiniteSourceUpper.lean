module

public import proofs.HordijkSteelThreshold.CanonicalEscapeUpper
public import proofs.HordijkSteelThreshold.Gateway

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold MeasureTheory RAF RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal

theorem canonical_raf_le_finite_escape_36 (n K : ℕ) (_ : 4 ≤ n) (lambda : ℝ) :
    uniformCatalysisMeasure n lambda (HasRAFEvent n) ≤
      staticReactionMeasure (2*(K+2))
        (fixedPoolParameter (catalysisP n lambda) (Fintype.card (Molecule n)))
        (staticEscapeEvent 2 K) +
      (Fintype.card (Molecule (K+2)) : ENNReal)*36*(toNNReal (catalysisP n lambda) : ENNReal) := by
  let E : Set (AmbientCoord n → Prop) := {ω | ∃ x ∈
    temporaryReactionClosure 2 (catalystActive ω Finset.univ), K+2 < molLength x}
  let J := ↥(binaryFood n (K+2)) × PolymerSeedReaction n 2
  have hseed : ambientPiMeasure n lambda (boundedSeedCatalystEvent n (K+2)) ≤
      (Fintype.card (Molecule (K+2)) : ENNReal) * 36 * (toNNReal (catalysisP n lambda) : ENNReal) := by
    rw [show boundedSeedCatalystEvent n (K+2) = ⋃ j : J, {ω | ω (j.1.1, j.2.1)} by
      ext; simp [boundedSeedCatalystEvent, J, binaryFood]]
    refine (measure_iUnion_fintype_le _ _).trans ?_
    simp only [ambient_coordinate_probability, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    gcongr
    exact_mod_cast (Fintype.card_prod _ _).trans_le
      (by simpa using Nat.mul_le_mul (binaryFood_card_le_cutoff n (K+2)) (card_concrete_gateway_binary_t2 n))
  have hs : {ω | ∃ S : Finset (Reaction n),
      IsRevRAF (binaryPolymerCRS n 2) (fun x r => ω (x,r)) S} ⊆
      E ∪ boundedSeedCatalystEvent n (K+2) := fun ω hraf =>
    if he : ω ∈ E then Or.inl he
    else Or.inr <| bounded_raf_has_seed_catalyst ω (fun x hx => Nat.le_of_not_gt fun h => he ⟨x, hx, h⟩) hraf
  rw [canonical_raf_measure_eq_ambient]
  exact (measure_mono hs).trans ((measure_union_le _ _).trans
    (add_le_add (ambient_escape_le_finite_static n K lambda) hseed))

end RAFCriticalWindowQuantitative
