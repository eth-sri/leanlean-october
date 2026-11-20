module

public import NearlyMinimax.HighSourceCountCancellation

@[expose] public section

/-! The complete source's higher-count first action: ordinary pair and
singleton selectors vanish, leaving the actual higher family plus the
fine-pair alias and even field actions. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem finePairThreeRowFirstAction_higher {d n D : ℕ} [NeZero d]
    (hn : 3 ≤ n) (hnD : n ≤ D) (ad bd ℓ N : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (M q : ℕ) (C : ℝ) (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Icc ad bd) (c : HighFrameIndex d D → ℝ)
    (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    finePairThreeRowFirstAction ad bd ℓ N D M q C U p c Φ =
      finePairPairAliasAction ad bd ℓ N M q C U p c Φ +
        finePairEvenFieldAction ad bd ℓ N M q C U p c Φ := by
  have hD : 1 ≤ D := by omega
  simp [finePairThreeRowFirstAction, finePairUnitFirstAction_count ad bd ha hab D q hD hnD C p hp,
    finePairCoarseFirstAction_count ad bd ℓ ha hab D q hD hnD C U p hp, show n ≠ 2 by omega,
    finePairFineFirstAction_alias_even_field ad bd ℓ N ha hab M q C U p hp c Φ]

section
variable {d n : ℕ} [NeZero d]
    (ad bd lam ℓ N μ : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (D M q : ℕ) (hn : 3 ≤ n) (hnD : n ≤ D)
include ha hab hn hnD

theorem completeSourceSignedFirstAction_higher (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    completeSourceSignedFirstAction ad bd lam ℓ N μ D M q C U p c Φ =
      higherBandFamilyFirstAction ad bd lam ℓ N μ D M q C U p c Φ +
        finePairPairAliasAction ad bd ℓ N M q C U p c Φ +
        finePairEvenFieldAction ad bd ℓ N M q C U p c Φ := by
  rw [completeSourceSignedFirstAction_eq_family,
    singletonFirstAction_zero_other_count ad bd ha hab D q (by omega) hnD (by omega) C p hp c Φ,
    finePairThreeRowFirstAction_higher hn hnD ad bd ℓ N ha hab M q C U p hp c Φ]
  ring

theorem completeSourceRawNumerator_higher (C a V η : ℝ)
    (U : Fin n → Covariate d) (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (y : Fin n → Fin 3) :
    completeSourceRawNumerator ad bd lam ℓ N μ D M q C a V η U p g w c y =
      higherBandFamilyFirstAction ad bd lam ℓ N μ D M q C U p c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) +
      finePairPairAliasAction ad bd ℓ N M q C U p c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) +
      finePairEvenFieldAction ad bd ℓ N M q C U p c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) -
      η^2 * (∏ i, p i) * ∑ i, (w i)^2 *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i := by
  unfold completeSourceRawNumerator
  rw [completeSourceSignedFirstAction_higher ad bd lam ℓ N μ ha hab D M q hn hnD C U p hp c]

end

end NearlyMinimax
