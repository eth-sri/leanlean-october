module

public import NearlyMinimax.HighSourceHigherGeometry
public import NearlyMinimax.HighCompleteSourceMarkedTail

@[expose] public section

/-! A deterministic measurable integrable full-count spatial envelope for
complete source scores, including empty/singleton cancellation, the genuine
pair defect, matched higher counts, and the exterior-degree crude bound. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

 variable {d : ℕ} (D M R q : ℕ) (aD bD c0 ell N mu C a rho eta Chi Bl : ℝ)

def completeSourceGeometryEnvelope : (n : ℕ) → (DesignSample d n) → ℝ
  | 0, _ => 0
  | 1, _ => 0
  | 2, U => finePairCountTwoGeometryEnvelope (bD-(M : ℝ)⁻¹) a rho eta N U
  | n+3, U => if n+3 ≤ D then
      completeSourceHigherGeometryEnvelope (D := D) aD bD c0 ell N mu M R q C a rho eta U
    else (3*Chi^2)^(n+3)*eta^4*(Bl+1)^2

 theorem completeSourceGeometryEnvelope_nonneg {n : ℕ} (U : DesignSample d n) :
    0 ≤ completeSourceGeometryEnvelope D M R q aD bD c0 ell N mu C a rho eta Chi Bl n U := by
  rcases n with _|_|_|n
  · norm_num [completeSourceGeometryEnvelope]
  · norm_num [completeSourceGeometryEnvelope]
  · exact finePairCountTwoGeometryEnvelope_nonneg _ _ _ _ _ U
  · try simp [completeSourceGeometryEnvelope]
    split_ifs
    · apply completeSourceHigherGeometryEnvelope_nonneg
    · positivity

 theorem completeSourceGeometryEnvelope_integrable [NeZero d] (hd : 5 ≤ d)
    (D M R q : ℕ) (aD bD c0 ell N mu C a rho eta Chi Bl : ℝ)
    (hell : 1 ≤ ell) (hN : ell ≤ N) (n : ℕ) :
    Integrable (completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu C a rho eta Chi Bl n)
      (fullSpatialPatchDesign d n) := by
  rcases n with _|_|_|n
  · exact integrable_zero _ _ _
  · exact integrable_zero _ _ _
  · exact (finePairCountTwoGeometryEnvelope_integrable_and_le (by omega) _ _ _ _
      (lt_of_lt_of_le zero_lt_one (hell.trans hN))).1
  · change Integrable (fun U : DesignSample d (n+3) => if n+3 ≤ D then
      completeSourceHigherGeometryEnvelope (D := D) aD bD c0 ell N mu M R q C a rho eta U
      else (3*Chi^2)^(n+3)*eta^4*(Bl+1)^2) _
    split_ifs
    · exact (completeSourceHigherGeometryEnvelope_integral hd (by omega) _ _ _ _ _ _ _ _ _ _ _ _ _ hell hN).1
    · exact integrable_const _

 theorem completeSourceGeometryEnvelope_exterior_integral (n : ℕ)
    (aD bD c0 ell N mu C a rho eta Chi Bl : ℝ) (hn : D < n+3) :
    (∫ U, completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu C a rho eta Chi Bl (n+3) U
      ∂fullSpatialPatchDesign d (n+3)) =
      (3*(2 : ℝ)^d*Chi^2)^(n+3)*eta^4*(Bl+1)^2 := by
  simp only [completeSourceGeometryEnvelope, if_neg (not_le.mpr hn), integral_const,
    fullSpatialPatchDesign_real_univ, smul_eq_mul]
  ring

 theorem fineFieldGeometryEnvelope_count_three (ad bd T0 N : ℝ)
    (M q : ℕ) (C a rho eta : ℝ) (U : Fin 3 → Covariate d) :
    fineFieldGeometryEnvelope ad bd T0 N M q C a rho eta U = 0 := by
  have hs : ((Finset.univ : Finset (Fin 3)).powerset).filter
      (fun S => 4 ≤ S.card ∧ Even S.card) = ∅ := by
    rfl
  unfold fineFieldGeometryEnvelope
  rw [hs]
  simp

end NearlyMinimax
