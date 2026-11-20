module

public import NearlyMinimax.HighCompleteGeometry
public import NearlyMinimax.CompleteSourceSaddleParameters


@[expose] public section

/-! The true source activation budget dominates its unbalanced row mass,
and the complete geometry H increases with this budget. -/
noncomputable section
open MeasureTheory Set
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
attribute [local instance] Classical.propDecidable

 theorem completeSourceGeometryEnvelope_mono_total {d : ℕ} (D M R q : ℕ)
    (aD bD c0 ell N mu C a rho eta Chi : ℝ) {B1 B2 : ℝ}
    (hB1 : 0 ≤ B1) (hB : B1 ≤ B2) {n : ℕ} (U : DesignSample d n) :
    let geometryEnvelope := completeSourceGeometryEnvelope D M R q aD bD c0 ell N mu C a rho eta Chi
    geometryEnvelope B1 n U ≤
      geometryEnvelope B2 n U := by
  rcases n with _|_|_|n <;> try exact le_rfl
  · change (if n+3 ≤ D then _ else (3*Chi^2)^(n+3)*eta^4*(B1+1)^2) ≤
      (if n+3 ≤ D then _ else (3*Chi^2)^(n+3)*eta^4*(B2+1)^2)
    split_ifs
    · exact le_rfl
    · gcongr <;> assumption

end NearlyMinimax
