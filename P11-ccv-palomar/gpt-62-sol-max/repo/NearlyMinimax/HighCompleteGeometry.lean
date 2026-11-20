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

namespace SourceGeometry
variable {d : ℕ} (S : SourceGeometry d) (Chi Bl : ℝ)

def envelope : (n : ℕ) → (Fin n → Covariate d) → ℝ
  | 0, _ => 0
  | 1, _ => 0
  | 2, U => finePairCountTwoGeometryEnvelope S.bd S.a S.rho S.eta S.N U
  | n+3, U => if n+3 ≤ S.D then S.higherEnvelope U else (3*Chi^2)^(n+3)*S.eta^4*(Bl+1)^2

theorem envelope_nonneg (n : ℕ) (U : Fin n → Covariate d) : 0 ≤ S.envelope Chi Bl n U := by
  rcases n with _|_|_|n
  · rfl
  · rfl
  · exact finePairCountTwoGeometryEnvelope_nonneg _ _ _ _ _ U
  · simp only [envelope]
    split_ifs
    · exact S.higherEnvelope_nonneg U
    · positivity

theorem envelope_integrable [NeZero d] (hd : 5 ≤ d)
    (hell : 1 ≤ S.ell) (hN : S.ell ≤ S.N) (n : ℕ) :
    Integrable (S.envelope Chi Bl n) (fullSpatialPatchDesign d n) := by
  rcases n with _|_|_|n
  · exact integrable_zero _ _ _
  · exact integrable_zero _ _ _
  · exact (finePairCountTwoGeometryEnvelope_integrable_and_le (by omega) _ _ _ _
      (zero_lt_one.trans_le (hell.trans hN))).1
  · change Integrable (fun U : Fin (n+3) → Covariate d =>
      if n+3 ≤ S.D then S.higherEnvelope U else (3*Chi^2)^(n+3)*S.eta^4*(Bl+1)^2) _
    split_ifs
    · exact (S.higherEnvelope_integrable_and_eq hd (by omega) hell hN).1
    · exact integrable_const _

theorem envelope_pair_integral_le (hd : 0 < d) (hN : 0 < S.N) :
    (∫ U, S.envelope Chi Bl 2 U ∂fullSpatialPatchDesign d 2) ≤
      9*finePairCountTwoSpatialBudget d S.bd S.a S.rho S.eta S.N :=
    (finePairCountTwoGeometryEnvelope_integrable_and_le hd _ _ _ _ hN).2

theorem envelope_exterior_integral (n : ℕ) (h3 : 3 ≤ n) (hn : S.D < n) :
    (∫ U, S.envelope Chi Bl n U ∂fullSpatialPatchDesign d n) =
      (3*(2 : ℝ)^d*Chi^2)^n*S.eta^4*(Bl+1)^2 := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r+3 := ⟨n-3, by omega⟩
  simp only [envelope, if_neg (not_le.mpr hn), integral_const,
    fullSpatialPatchDesign_real_univ, smul_eq_mul]
  ring

end SourceGeometry

 theorem fineFieldGeometryEnvelope_count_three (ad bd T0 N : ℝ)
    (M q : ℕ) (C a rho eta : ℝ) (U : Fin 3 → Covariate d) :
    fineFieldGeometryEnvelope ad bd T0 N M q C a rho eta U = 0 := by
  have hs : ((Finset.univ : Finset (Fin 3)).powerset).filter
      (fun S => 4 ≤ S.card ∧ Even S.card) = ∅ := by
    rfl
  unfold fineFieldGeometryEnvelope fineSelectedGeometryEnvelope
  rw [hs]
  simp

end NearlyMinimax
