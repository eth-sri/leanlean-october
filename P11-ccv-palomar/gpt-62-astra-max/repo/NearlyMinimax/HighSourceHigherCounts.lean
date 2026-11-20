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

section Pair
variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [MeasurableSpace Z]

theorem ordinaryPairPacket_zero_other_count {n : ℕ} (hn : 3 ≤ n)
    {σ : Measure Z} [IsFiniteMeasure σ] {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (m D q : ℕ) (hnm : n ≤ m) (hnD : n ≤ D) (C : ℝ)
    {A : Z → ι → ι → ℝ} (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (c : ι → ℝ)
    {p : Fin n → ℝ} (hp : ∀ i, p i ∈ Icc a b) (ψ : Z → Fin n → ℝ)
    (hmψ : ∀ i, Measurable (fun ζ => ψ ζ i)) (hbψ : ∀ ζ i, |ψ ζ i| ≤ 1)
    (Φ : (ι → ℝ) → ℝ) :
    (∫ᵛ e, highPacketObservable a b C c
      (fun ζ z eps => ∏ i, localDensityReset a b z eps p (fun i _ => ψ ζ i) i) Φ e
      ∂<•highPacketSignedMeasure σ a b m 2 D q C A) = 0 := by
  rw [highPacketSignedMeasure_factor_integral a b m 2 D hA hcost
    (fun ζ z eps => ∏ i, localDensityReset a b z eps p (fun i _ => ψ ζ i) i)
    (fun z eps => Finset.measurable_fun_prod _ (fun i _ => ordinaryPairReset_measurable a b p hmψ z eps i)) (by bound)
    (fun ζ e => finite_density_product_abs_bound _ (ha.trans hab).le
      (ordinaryPairReset_atom_abs_le ha hab hp (hbψ ζ) e)) (finePairResponseAtomBound_le q C c Φ)]
  have hh := highSeparatedPacketAction_count_selector ha hab m 2 D q
    (by omega) (by omega) Finset.univ (by simpa using hnD)
    (by simpa using hnm) (by simpa using (show 2 ≤ n by omega)) p
    (fun ζ i _ => ψ ζ i) (fun i _ => hmψ i) (fun ζ i _ => hbψ ζ i) C hA hcost c Φ
  simpa only [Finset.card_univ, Fintype.card_fin, if_neg (show n ≠ 2 by omega)] using hh

end Pair

theorem finePairThreeRowFirstAction_higher {d n D : ℕ} [NeZero d]
    (hn : 3 ≤ n) (hnD : n ≤ D) (ad bd ℓ N : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (M q : ℕ) (C : ℝ) (U : DesignSample d n) {p : Fin n → ℝ}
    (hp : ∀ i, p i ∈ Icc ad bd) (c : HighFrameVector d D)
    (Φ : (HighFrameVector d D) → ℝ) :
    finePairThreeRowFirstAction ad bd ℓ N D M q C U p c Φ =
      finePairPairAliasAction ad bd ℓ N M q C U p c Φ +
        finePairEvenFieldAction ad bd ℓ N M q C U p c Φ := by
  have hu : finePairUnitFirstAction ad bd D q C p c Φ = 0 :=
    ordinaryPairPacket_zero_other_count hn ha hab D D q hnD hnD C (A := (fun _ => finePairUnitMatrix d D)) (fun _ _ => measurable_const) (integrable_const _) c hp _ (fun _ => measurable_const) (by norm_num) Φ
  have hc : finePairCoarseFirstAction ad bd ℓ D q C U p c Φ = 0 :=
    ordinaryPairPacket_zero_other_count hn ha hab D D q hnD hnD C
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 ℓ _) c hp
      (fun ζ i => finePairTimeFieldValue ζ (U i))
      (fun i => (boundedHyperplaneFieldValue_section_measurable (U i)).comp measurable_snd)
      (fun ζ i => (finePairTimeFieldValue_abs ζ (U i)).le) Φ
  rw [finePairThreeRowFirstAction, hu, hc,
    finePairFineFirstAction_alias_even_field ad bd ℓ N ha hab M q C U hp c Φ]
  ring

variable {d n : ℕ} [NeZero d] (ad bd lam ℓ N μ : ℝ) (ha : 0 < ad) (hab : ad < bd) (D M q : ℕ)
    (hn : 3 ≤ n) (hnD : n ≤ D) (C a V η : ℝ) (U : DesignSample d n)
include ha hab hn hnD

theorem completeSourceSignedFirstAction_higher {p : Fin n → ℝ} (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameVector d D) (Φ : (HighFrameVector d D) → ℝ) :
    completeSourceSignedFirstAction ad bd lam ℓ N μ M q C U p c Φ =
      higherBandFamilyFirstAction ad bd lam ℓ N μ M q C U p c Φ +
        finePairPairAliasAction ad bd ℓ N M q C U p c Φ +
        finePairEvenFieldAction ad bd ℓ N M q C U p c Φ := by
  rw [completeSourceSignedFirstAction_eq_family,
    singletonFirstAction_zero_other_count ha hab D q (by omega) hnD (by omega) C p hp c Φ,
    finePairThreeRowFirstAction_higher hn hnD ad bd ℓ N ha hab M q C U hp c Φ]
  ring

theorem completeSourceRawNumerator_higher (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameVector d D) (y : TernaryVector n) :
    let product := highResponseProduct a V η g w (fun i => highFrameFeature (U i))
    completeSourceRawNumerator ad bd lam ℓ N μ M q C a V η U p g w c y =
      higherBandFamilyFirstAction ad bd lam ℓ N μ M q C U p c
        (fun v => product v y) +
      finePairPairAliasAction ad bd ℓ N M q C U p c
        (fun v => product v y) +
      finePairEvenFieldAction ad bd ℓ N M q C U p c
        (fun v => product v y) -
      η^2 * (∏ i, p i) * ∑ i, (w i)^2 *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i := by
  unfold completeSourceRawNumerator
  rw [completeSourceSignedFirstAction_higher ad bd lam ℓ N μ ha hab D M q hn hnD C U hp c]

end NearlyMinimax
