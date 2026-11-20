module

public import NearlyMinimax.HighSourceRawDecomposition


@[expose] public section

/-! Count-zero, count-one and count-two identities for the complete
source, including every selected higher-target coarse/fine row. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

section
variable {d n : ℕ} (ad bd lam ℓ N μ : ℝ)

def higherBandFamilyFirstAction
    {D : ℕ} (M q : ℕ) (C : ℝ) (U : DesignSample d n) (p : Fin n → ℝ)
    (c : HighFrameVector d D) (Φ : (HighFrameVector d D) → ℝ) : ℝ :=
  ∑ i : HigherBandFamilyIndex d D M q ad bd C lam ℓ N μ,
    higherBandFirstAction ad bd lam ℓ (higherBandFamilyUpper d ℓ N μ i.val)
      (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) q C i.val.2 U p c Φ

theorem higherBandFamilyFirstAction_zero_small_count
    {ad bd : ℝ} (lam ℓ N μ : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (D M q : ℕ) (hD : 1 ≤ D) (hnD : n ≤ D) (hn : n ≤ 2) (C : ℝ)
    (U : DesignSample d n) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameVector d D) (Φ : (HighFrameVector d D) → ℝ) :
    higherBandFamilyFirstAction ad bd lam ℓ N μ M q C U p c Φ = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hr := (higherBandFamily_target_bounds i).1
  exact higherBandFirstAction_zero_small_count lam ℓ _ ha hab i.property.1
    _ _ D q (by omega) hD hnD (by omega) C i.val.2 hU hp c Φ

theorem completeSourceSignedFirstAction_eq_family (D M q : ℕ) (C : ℝ)
    (U : DesignSample d n) (p : Fin n → ℝ)
    (c : HighFrameVector d D) (Φ : (HighFrameVector d D) → ℝ) :
    completeSourceSignedFirstAction ad bd lam ℓ N μ M q C U p c Φ =
      finePairThreeRowFirstAction ad bd ℓ N D M q C U p c Φ +
        singletonFirstAction ad bd q C p c Φ +
        higherBandFamilyFirstAction ad bd lam ℓ N μ M q C U p c Φ := rfl

theorem completeSourceRawNumerator_count_zero [NeZero d]
    (ad bd lam ℓ N μ : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (D M q : ℕ) (hD : 1 ≤ D) (C a V η : ℝ)
    (U : Fin 0 → Covariate d) (p g w : Fin 0 → ℝ)
    (c : HighFrameVector d D) (y : Fin 0 → Fin 3) :
    completeSourceRawNumerator ad bd lam ℓ N μ M q C a V η U p g w c y = 0 := by
  unfold completeSourceRawNumerator
  rw [completeSourceSignedFirstAction_eq_family,
    finePairThreeRowFirstAction_small_count (by omega) ad bd ℓ N ha hab D M q hD C U p
      (fun i => Fin.elim0 i) c,
    singletonFirstAction_zero_other_count ha hab D q hD (by omega) (by omega)
      C p (fun i => Fin.elim0 i) c,
    higherBandFamilyFirstAction_zero_small_count lam ℓ N μ ha hab D M q hD
      (by omega) (by omega) C U (fun i => Fin.elim0 i) p (fun i => Fin.elim0 i) c]
  simp

theorem singletonFirstAction_response_heat
    {ad bd : ℝ} (ha : 0 < ad) (hab : ad < bd) {D q : ℕ} (hD : 1 ≤ D) (hq : 1 ≤ q)
    (C a V η : ℝ) (hC : C ≠ 0) (U : Fin 1 → Covariate d) (p g w : Fin 1 → ℝ)
    (hp : ∀ i, p i ∈ Icc ad bd) (c : HighFrameVector d D) (y : Fin 1 → Fin 3) :
    singletonFirstAction ad bd q C p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) =
      η^2 * (∏ i, p i) * ∑ i, (w i)^2 *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i := by
  rw [singletonFirstAction_count_one ha hab D q hD C hp c]
  have he := high_response_matrix_heat hq C a V η hC
    (finePairUnitMatrix_symmetric d D) g w (fun i => highFrameFeature (U i)) c y
    (fun _ => 1) (by
      simp [finePairUnitMatrix_kernel])
  rw [he]
  simp
  ring

end

variable {d : ℕ} [NeZero d] (ad bd lam ℓ N μ : ℝ) (ha : 0 < ad) (hab : ad < bd)
include ha hab

theorem completeSourceRawNumerator_count_one
    (D M q : ℕ) (hD : 1 ≤ D) (hq : 1 ≤ q) (C a V η : ℝ) (hC : C ≠ 0)
    {U : Fin 1 → Covariate d} (hU : ∀ i j, |U i j| ≤ 2)
    (p g w : Fin 1 → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameVector d D) (y : Fin 1 → Fin 3) :
    completeSourceRawNumerator ad bd lam ℓ N μ M q C a V η U p g w c y = 0 := by
  unfold completeSourceRawNumerator
  rw [completeSourceSignedFirstAction_eq_family,
    finePairThreeRowFirstAction_small_count (by omega) ad bd ℓ N ha hab D M q hD C U p hp c,
    higherBandFamilyFirstAction_zero_small_count lam ℓ N μ ha hab D M q hD
      hD (by omega) C U hU p hp c,
    singletonFirstAction_response_heat ha hab hD hq C a V η hC U p g w hp c y]
  ring

theorem completeSourceRawNumerator_count_two
    {D M q : ℕ} (hD : 2 ≤ D) (C a V η : ℝ) {U : DesignSample d 2}
    (hU : ∀ i j, |U i j| ≤ 2) (p g w : Fin 2 → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameVector d D) (y : TernaryVector 2) :
    completeSourceRawNumerator ad bd lam ℓ N μ M q C a V η U p g w c y =
      finePairCountTwoRawNumerator ad bd ℓ N D M q C a V η U p g w c y := by
  unfold completeSourceRawNumerator
  rw [completeSourceSignedFirstAction_eq_family,
    singletonFirstAction_zero_other_count ha hab D q (by omega) (by omega) (by omega)
      C p hp c,
    higherBandFamilyFirstAction_zero_small_count lam ℓ N μ ha hab D M q (by omega)
      (by omega) (by omega) C U hU p hp c]
  simp [finePairCountTwoRawNumerator]

end NearlyMinimax
