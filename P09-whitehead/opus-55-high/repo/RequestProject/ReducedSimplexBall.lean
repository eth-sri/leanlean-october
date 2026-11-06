import RequestProject.ReducedSimplexInterior
noncomputable section


namespace FiniteChains

/-- The actual ambient homeomorphism furnished by the proved convex-simplex parametrization. -/
def reducedSimplexBallAmbient n :=
  (reducedSimplex_exists_ball_homeomorph n).choose

 theorem reducedSimplexBallAmbient_properties n :
    reducedSimplexBallAmbient n '' interior (reducedSimplex n) = Metric.ball 0 1 ∧
    reducedSimplexBallAmbient n '' reducedSimplex n = Metric.closedBall 0 1 ∧
    reducedSimplexBallAmbient n '' frontier (reducedSimplex n) = Metric.sphere 0 1 :=
  (reducedSimplex_exists_ball_homeomorph n).choose_spec

/-- The standard simplex, in every dimension, is homeomorphic to the closed unit ball. -/
def standardSimplexClosedBallHomeomorph n :=
  (reducedSimplexHomeomorph n).symm.trans
    (((reducedSimplexBallAmbient n).image _).trans
      (Homeomorph.setCongr (reducedSimplexBallAmbient_properties n).2.1))

 theorem standardSimplexClosedBallHomeomorph_val n
    z :
    (standardSimplexClosedBallHomeomorph n z).val =
      reducedSimplexBallAmbient n (standardSimplexToReduced n z).val := rfl

/-- Positive barycentric coordinates correspond exactly to the open unit ball. -/
theorem standardSimplexClosedBallHomeomorph_positive_iff n
    z :
    (∀ i, 0 < z.val i) ↔ (standardSimplexClosedBallHomeomorph n z).val ∈ Metric.ball 0 1 := by
  have hz := (reducedSimplexHomeomorph n).apply_symm_apply z
  have hp := reducedSimplexToStandard_positive_iff n (standardSimplexToReduced n z)
  change (∀ i, 0 < (reducedSimplexHomeomorph n
      ((reducedSimplexHomeomorph n).symm z)).val i) ↔ _ at hp
  simp_all [hz, hp, standardSimplexClosedBallHomeomorph_val, ← (reducedSimplexBallAmbient_properties n).1]
