module

public import NearlyMinimax.HighSourceAllGeometry
public import NearlyMinimax.CompleteSourceSaddleParameters
public import NearlyMinimax.HighGeometryEnvelopeMonotone
public import NearlyMinimax.OrdinaryFineAliasSaddleEnvelope

@[expose] public section

/-! The concrete geometry-only envelope at the actual rounded source
saddle. Its count profile uses the true normalized activation budget. -/
noncomputable section
open MeasureTheory Set
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local instance] Classical.propDecidable

def completeSaddleGeometryParameters {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (Cfr cf Cω : ℝ) (n : ℕ) : SourceGeometry d :=
  ⟨completeSaddleD C n, completeSaddleM C n,
    ordinaryFineAliasSaddleTargetBound C.smoothness d C.densityLower C.densityUpper,
    lowerSaddleResponseOrder C.smoothness d, C.densityLower, C.densityUpper,
    completeSaddleC0 C, completeSaddleEll C Cω n, completeSaddleN C Cω n, completeSaddleMu C Cω n,
    Cfr, Q.a, Q.ρ, completeSaddleEta C Cω cf n⟩

def completeSaddleGeometryEnvelope {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (Cfr cf Cω : ℝ) (n : ℕ) :
    (r : ℕ) → (Fin r → Covariate d) → ℝ :=
  let S := completeSaddleGeometryParameters C Q Cfr cf Cω n
  S.envelope (highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1)
    (completeSourceSaddleActivity C S.q Cfr (spatialInterpolationLambda d) Cω n)

 section
variable {d : ℕ}

theorem completeSaddleGeometryEnvelope_nonneg (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (Cfr cf Cω : ℝ) (n r : ℕ) (U : Fin r → Covariate d) :
    0 ≤ completeSaddleGeometryEnvelope C Q Cfr cf Cω n r U :=
  SourceGeometry.envelope_nonneg ..

 theorem completeSaddleGeometryEnvelope_integrable [NeZero d] (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (hd : 5 ≤ d) (Cfr cf Cω : ℝ) (n r : ℕ)
    (hell : 1 ≤ completeSaddleEll C Cω n) (hellN : completeSaddleEll C Cω n ≤ completeSaddleN C Cω n) :
    Integrable (completeSaddleGeometryEnvelope C Q Cfr cf Cω n r) (fullSpatialPatchDesign d r) :=
  SourceGeometry.envelope_integrable _ _ _ hd hell hellN r

end

end NearlyMinimax
