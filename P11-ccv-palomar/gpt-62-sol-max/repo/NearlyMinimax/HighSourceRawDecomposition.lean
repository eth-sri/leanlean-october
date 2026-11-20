module

public import NearlyMinimax.CompleteSourceRows
public import NearlyMinimax.FinePairAllCounts
public import NearlyMinimax.HighCardinalScores
public import NearlyMinimax.CardinalGlobalBandL2
public import NearlyMinimax.SpatialSubsetIntegral
public import NearlyMinimax.FinePairUnionMassAnnihilation


@[expose] public section

/-! Exact count decomposition of the actual complete source packets.
The statements below evaluate genuine signed integrals; no local action
identity or count cancellation is supplied as a hypothesis. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
attribute [local instance] Classical.propDecidable

def higherBandFirstAction {d n : ℕ} (ad bd lam L T : ℝ) (r m D q : ℕ)
    (C : ℝ) (fine : Bool) (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) : ℝ :=
  highPacketFirstAction (higherBandCarrierMeasure d r L T fine) ad bd m r D q C
    (higherBandCarrierAmplitude d r D lam fine) c p
    (fun ζ i l => higherBandCarrierFactor d r lam fine ζ l (U i)) Φ

section
variable {d n : ℕ}

theorem higherBandFirstAction_count_expansion
    (ad bd lam L T : ℝ) (ha : 0 < ad) (hab : ad < bd) (hT : 1 ≤ T)
    (r m D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hnD : n ≤ D)
    (C : ℝ) (fine : Bool) (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFirstAction ad bd lam L T r m D q C fine U p c Φ =
      densityCountCoefficient ad bd m r n *
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, (∏ i ∈ S, p i) *
          responseMatrixAction q C
            (separatedSubsetMatrix (higherBandCarrierMeasure d r L T fine) r
              (fun ζ i l => higherBandCarrierFactor d r lam fine ζ l (U i))
              (higherBandCarrierAmplitude d r D lam fine) S) c Φ := by
  let := higherBandCarrierMeasure_finite d r L T hT fine
  exact highPacketFirstAction_count_expansion _ ad bd ha hab m r D q hr hD hnD C _
    (higherBandCarrierAmplitude_integrable d r D lam L T hT fine) c p hp _
    (fun i l => (higherBandCarrierFactor_joint_measurable d r lam fine l).comp
      (measurable_id.prodMk measurable_const))
    (fun ζ i l => higherBandCarrierFactor_bound d r lam fine ζ l (U i) (hU i)) Φ

theorem higherBandFirstAction_zero_small_count
    (ad bd lam L T : ℝ) (ha : 0 < ad) (hab : ad < bd) (hT : 1 ≤ T)
    (r m D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hnD : n ≤ D) (hnr : n < r)
    (C : ℝ) (fine : Bool) (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFirstAction ad bd lam L T r m D q C fine U p c Φ = 0 := by
  rw [higherBandFirstAction_count_expansion ad bd lam L T ha hab hT r m D q hr hD hnD
    C fine U hU p hp c Φ]
  have he : (Finset.univ : Finset (Fin n)).powersetCard r = ∅ :=
    Finset.powersetCard_eq_empty.mpr (by simpa using hnr)
  grind

theorem higherBandFirstAction_zero_other_count
    (ad bd lam L T : ℝ) (ha : 0 < ad) (hab : ad < bd) (hT : 1 ≤ T)
    (r m D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hnD : n ≤ D)
    (hnm : n ≤ m) (hne : n ≠ r) (C : ℝ) (fine : Bool)
    (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFirstAction ad bd lam L T r m D q C fine U p c Φ = 0 := by
  by_cases hnr : n < r
  · apply higherBandFirstAction_zero_small_count <;> assumption
  rw [higherBandFirstAction_count_expansion ad bd lam L T ha hab hT r m D q hr hD hnD
    C fine U hU p hp c Φ,
    densityCountCoefficient_exact ad bd ha hab m r n hr (by omega) hnm, if_neg hne, zero_mul]

theorem cardinal_density_subset_sym_eq (lam : ℝ)
    (S : Finset (Fin n)) (z : CardinalSeparatedMark d S.card)
    (U : Fin n → Covariate d) :
    densitySeparatedSym S.card (fun i l => cardinalSeparatedFactor lam z l (U i)) S =
      cardinalSeparatedSymmetricFactor lam z (spatialSubsetConfiguration S U) := by
  let e :=
    ((Fintype.equivFin S).trans (finCongr (Fintype.card_coe S))).symm
  rw [densitySeparatedSym_eq_permutation_average S.card _ S e]
  unfold cardinalSeparatedSymmetricFactor
  congr 1
  apply Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin S.card)))
  intro τ
  have h := Equiv.prod_comp τ
    (fun l => cardinalSeparatedFactor lam z l (U (e (τ.symm l)).val))
  simp only [Equiv.symm_apply_apply] at h
  convert h using 1
  rfl

end

def higherBandActualMatrix {d n D : ℕ} (lam L T : ℝ) (fine : Bool)
    (U : Fin n → Covariate d) : HighFrameIndex d D → HighFrameIndex d D → ℝ :=
  if fine then globalCardinalBandMatrix lam L T U else integratedCardinalMatrix lam T U

theorem higherBand_subset_matrix_actual {d n D : ℕ} (lam : ℝ) (hlam : 0 ≤ lam)
    (L T : ℝ) (hL : 0 < L) (hT : 1 ≤ T) (fine : Bool)
    (S : Finset (Fin n)) (hS : 2 ≤ S.card) (U : Fin n → Covariate d)
    (hU : ∀ i j, |U i j| ≤ 2) :
    separatedSubsetMatrix (higherBandCarrierMeasure d S.card L T fine) S.card
      (fun ζ i l => higherBandCarrierFactor d S.card lam fine ζ l (U i))
      (higherBandCarrierAmplitude d S.card D lam fine) S =
      higherBandActualMatrix lam L T fine (spatialSubsetConfiguration S U) := by
  have hb : ∀ l j, |spatialSubsetConfiguration S U l j| ≤ 2 := fun l => hU _
  funext β β'
  cases fine
  · change (∫ z, densitySeparatedSym S.card
        (fun i l => cardinalSeparatedFactor lam z l (U i)) S *
        cardinalSeparatedAmplitude lam z β β' ∂cardinalSeparatedMeasure d S.card T) = _
    simp_rw [cardinal_density_subset_sym_eq]
    exact (integrated_cardinal_symmetric_separated_exact lam hlam hT _ hb β β').symm
  · change (∫ z, densitySeparatedSym S.card
        (fun i l => cardinalSeparatedFactor lam z.2 l (U i)) S *
        cardinalBandAmplitude lam z β β' ∂cardinalBandMeasure d S.card L T) = _
    simp_rw [cardinal_density_subset_sym_eq]
    exact (integrated_cardinal_actual_band_separated_exact hS lam hlam hL hT _ hb β β').symm

theorem higherBandFirstAction_actual_count_expansion {d n : ℕ}
    (ad bd lam L T : ℝ) (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    (hL : 0 < L) (hT : 1 ≤ T) (r m D q : ℕ) (hr : 2 ≤ r) (hD : 1 ≤ D) (hnD : n ≤ D)
    (C : ℝ) (fine : Bool) (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFirstAction ad bd lam L T r m D q C fine U p c Φ =
      densityCountCoefficient ad bd m r n *
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, (∏ i ∈ S, p i) *
          responseMatrixAction q C
            (higherBandActualMatrix lam L T fine (spatialSubsetConfiguration S U)) c Φ := by
  rw [higherBandFirstAction_count_expansion ad bd lam L T ha hab hT r m D q (by omega)
    hD hnD C fine U hU p hp c Φ]
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  have he := (Finset.mem_powersetCard.mp hS).2
  have hh := higherBand_subset_matrix_actual (D := D) lam hlam L T hL hT fine S
    (by omega) U hU
  subst r
  rw [hh]

def singletonFirstAction {d n : ℕ} (ad bd : ℝ) (D q : ℕ) (C : ℝ)
    (p : Fin n → ℝ) (c : HighFrameIndex d D → ℝ)
    (Φ : (HighFrameIndex d D → ℝ) → ℝ) : ℝ :=
  highPacketFirstAction (Measure.dirac ()) ad bd D 1 D q C
    (fun _ => finePairUnitMatrix d D) c p (fun _ _ _ => 1) Φ

section
variable {d n : ℕ} (ad bd : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (D q : ℕ) (hD : 1 ≤ D) (hnD : n ≤ D) (C : ℝ)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ)
include ha hab hD hnD hp

private theorem singletonFirstAction_count :
    singletonFirstAction ad bd D q C p c Φ =
      if n = 1 then (∏ i, p i) * responseMatrixAction q C (finePairUnitMatrix d D) c Φ else 0 := by
  rw [singletonFirstAction, highPacketFirstAction_identical_columns (Measure.dirac ()) ad bd ha hab
    D 1 D q (by omega) hD hnD C _ (SeparatedMatrixIntegrable.const _ _) c p hp hnD
    (fun _ _ => 1) (fun _ => measurable_const) (by simp)]
  simp

end

theorem singletonFirstAction_zero_other_count {d n : ℕ}
    (ad bd : ℝ) (ha : 0 < ad) (hab : ad < bd) (D q : ℕ) (hD : 1 ≤ D)
    (hnD : n ≤ D) (hne : n ≠ 1) (C : ℝ)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    singletonFirstAction ad bd D q C p c Φ = 0 := by
  simp [singletonFirstAction_count ad bd ha hab D q hD hnD C p hp, hne]

theorem singletonFirstAction_count_one {d : ℕ}
    (ad bd : ℝ) (ha : 0 < ad) (hab : ad < bd) (D q : ℕ) (hD : 1 ≤ D) (C : ℝ)
    (p : Fin 1 → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    singletonFirstAction ad bd D q C p c Φ =
      (∏ i, p i) * responseMatrixAction q C (finePairUnitMatrix d D) c Φ := by
  simp [singletonFirstAction_count ad bd ha hab D q hD hD C p hp]

def completeSourceSignedFirstAction {d n : ℕ} (ad bd lam ℓ N μ : ℝ)
    (D M q : ℕ) (C : ℝ) (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) : ℝ :=
  finePairThreeRowFirstAction ad bd ℓ N D M q C U p c Φ +
    singletonFirstAction ad bd D q C p c Φ +
    ∑ i : HigherBandFamilyIndex d D M q ad bd C lam ℓ N μ,
      higherBandFirstAction ad bd lam ℓ (higherBandFamilyUpper d ℓ N μ i.val)
        (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) D q C i.val.2 U p c Φ

/-- The raw complete-source numerator subtracts the global variance
derivative once, after adding every genuine row first action. -/
def completeSourceRawNumerator {d n : ℕ} (ad bd lam ℓ N μ : ℝ)
    (D M q : ℕ) (C a V η : ℝ) (U : Fin n → Covariate d) (p g w : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (y : Fin n → Fin 3) : ℝ :=
  completeSourceSignedFirstAction ad bd lam ℓ N μ D M q C U p c
    (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) -
    η^2 * (∏ i, p i) * ∑ i, (w i)^2 *
      highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i

end NearlyMinimax
