module

public import NearlyMinimax.CardinalFactorialEnergy
public import NearlyMinimax.HighSpatialEnvelopes
public import NearlyMinimax.HigherBandFamily
public import NearlyMinimax.FiniteCountEnergyAssembly
public import NearlyMinimax.FinePairSaddleFactorialEnergy
public import NearlyMinimax.HighCompleteGeometry


@[expose] public section

/-! Factorial integration of the genuine deterministic spatial envelopes.
All constants in these bounds precede the count and cutoff quantifiers. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem higherBandTargetScale_max_eq_matched {d r : ℕ} (hr : 2 ≤ r) (N mu : ℝ) :
    max 1 (higherBandTargetScale d r N mu) = matchedCardinalTargetCutoff d (r-2) N mu := by
  simp_all [matchedCardinalTargetCutoff, higherBandTargetScale]

def cardinalGeometryFactorialConstant (d q : ℕ) (B C a rho Cs : ℝ) : ℝ :=
  cardinalInterpolationFactorialConstant d B a (3*Cs) +
    cardinalTaylorFactorialConstant d q B C a rho (3*Cs)

theorem finite_cardinal_geometry_budget_le {d D F : ℕ} (hd : 5 ≤ d)
    {bd B : ℝ} (hbd : 0 ≤ bd) (hbdB : bd ≤ B) (q : ℕ) (C a rho eta Cs : ℝ)
    (ha : 0 < a) (hCs : 0 ≤ Cs) {N mu : ℝ} (hN : 1 ≤ N) (hmu : 0 < mu)
    (hmu1 : mu ≤ 1) (hmuH : mu*(1+Real.log N) ≤ 1)
    (hTaylor : eta^(4*q)*N^d ≤ 1) :
    (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
      ∫ U, cardinalGeometryEnvelope (d := d) (n := 3+j) (F := F) q bd C a rho eta
        (max 1 (higherBandTargetScale d (3+j) N mu)) U ∂fullSpatialPatchDesign d (3+j)) ≤
      cardinalGeometryFactorialConstant d q B C a rho Cs * eta^4*N^(-(d : ℝ))*mu^2 := by
  let f := fun r => poissonCountWeight ((3*Cs)*mu) r *
    (cardinalAliasSpatialComponent d r bd a eta (matchedCardinalTargetCutoff d (r-2) N mu) +
      cardinalTaylorSpatialComponent d r q bd C a rho eta)
  have hf (r : ℕ) : 0 ≤ f r := by
    dsimp [f]
    have h := poissonCountWeight_nonneg (by positivity : 0 ≤ (3*Cs)*mu) r
    have hb : 0 ≤ cardinalDefectSquareBudget d r (matchedCardinalTargetCutoff d (r-2) N mu) := by
      have hT : 1 ≤ matchedCardinalTargetCutoff d (r-2) N mu := le_max_left _ _
      have hlog : 0 ≤ 1+Real.log (matchedCardinalTargetCutoff d (r-2) N mu) := by
        linarith only [Real.log_nonneg hT]
      unfold cardinalDefectSquareBudget
      unfold spatialUnaryIntegralConstant
      positivity
    unfold cardinalAliasSpatialComponent cardinalTaylorSpatialComponent
      cardinalRawAliasCoefficient cardinalRawTaylorCoefficient spatialScaleIntegralConstant
    positivity
  refine (Finset.sum_le_sum (g := fun j => f (3+j)) ?_).trans
    ((finite_refined_sum_le_start_two D f hf).trans ?_)
  · intro j _
    rw [higherBandTargetScale_max_eq_matched (by omega)]
    have hT := higherBandTargetScale_max_eq_matched (d := d) (r := 3+j) (by omega) N mu
    have hi := (cardinalGeometryEnvelope_integrable_and_le (d := d) (n := 3+j) (F := F)
      hd (by omega) q bd C a rho eta (T := max 1 (higherBandTargetScale d (3+j) N mu))
        (le_max_left _ _)).2
    rw [cardinalRawSpatialEnergyBudget_split, hT] at hi
    simpa only [f, mul_assoc] using poissonCountWeight_mul_le_of_le_pow (x := Cs*mu) (by positivity) hi
  dsimp [f]
  simp_rw [show ∀ j : ℕ, 2+j-2=j from fun j => by omega, mul_add]
  rw [Finset.sum_add_distrib]
  have hA := finite_cardinal_interpolation_budget_le hbd hbdB (by omega : 0 < d)
    (D-1) a eta (3*Cs) ha (by positivity) hN hmu hmuH
  have hT := finite_cardinal_taylor_budget_le hbd hbdB d q (D-1) C a rho eta (3*Cs)
    (by positivity) (lt_of_lt_of_le zero_lt_one hN) hmu.le hmu1 hTaylor
  exact (add_le_add hA hT).trans_eq (by unfold cardinalGeometryFactorialConstant; ring)

section
variable {d D : ℕ} [NeZero d] (hd : 5 ≤ d)
include hd

theorem finite_fine_field_geometry_budget_le (hD : 3 ≤ D)
    {aD bD ad bd c0 : ℝ} (haD : 0 < aD) (had : aD ≤ ad) (hbd : bd ≤ bD)
    (hab : ad < bd) (htau : exteriorTau ((ad+bd)/(bd-ad)) ≤ c0)
    (M q : ℕ) (C a rho eta ell N Cs mu : ℝ) (hell : 0 < ell)
    (hCs : 0 ≤ Cs) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) :
    (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
      ∫ U, fineFieldGeometryEnvelope (d := d) (n := 3+j) ad bd ell N M q C a rho eta U
        ∂fullSpatialPatchDesign d (3+j)) ≤
      finePairFieldFactorialConstant d q aD bD C a rho c0 (3*Cs) * eta^4 *
        Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M) * (ell^(2-(d : ℝ)))^2 * mu^4 := by
  let f := fun r => poissonCountWeight (Cs*mu) r *
    ∫ U, fineFieldGeometryEnvelope (d := d) (n := r) ad bd ell N M q C a rho eta U
      ∂fullSpatialPatchDesign d r
  have hf3 : f 3=0 := by
    simp [f, fineFieldGeometryEnvelope_count_three]
  change (∑ j ∈ Finset.range (D-2), f (3+j)) ≤ _
  rw [finite_refined_sum_eq_start_four D hD f hf3]
  refine (Finset.sum_le_sum (g := fun j => poissonCountWeight ((3*Cs)*mu) (4+j) *
    finePairEvenActionSpatialBudget d (4+j) M q ad bd C a rho eta ell) ?_).trans
    (finite_fine_pair_field_budget_le haD had hbd hab htau d M q (D-3)
      C a rho eta ell (3*Cs) mu (by positivity) hmu hmu1)
  intro j _
  simpa only [f, mul_assoc] using poissonCountWeight_mul_le_of_le_pow (x := Cs*mu) (by positivity)
    (fineFieldGeometryEnvelope_integrable_and_le (d := d) (n := 4+j) (by omega)
      ad bd ell N hell M q C a rho eta).2

theorem finite_fine_pair_alias_geometry_budget_le
    {aD bD ad bd c0 K : ℝ} (haD : 0 < aD) (had : aD ≤ ad) (hbd : bd ≤ bD)
    (hab : ad < bd) (htau : exteriorTau ((ad+bd)/(bd-ad)) ≤ c0)
    (hc0 : 0 ≤ c0) (hK : 0 ≤ K) (M q : ℕ) (C a rho eta ell N Cs mu : ℝ)
    (hN : 0 < N) (hell : ell=N*Real.exp (-c0*D)) (hell1 : 1 ≤ ell)
    (hellN : ell ≤ N) (hDM : (D : ℝ) ≤ K*M)
    (hCs : 0 ≤ Cs) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) :
    (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
      (if M<3+j then ∫ U, finePairAliasGeometryEnvelope (d := d) (n := 3+j)
        ad bd ell N M q C a rho eta U ∂fullSpatialPatchDesign d (3+j) else 0)) ≤
      finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3*Cs) *
        (eta^4*N^(4-(d : ℝ))) *
          poissonCountWeight (finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3*Cs)*mu) (M+1) := by
  let f := fun r => poissonCountWeight ((3*Cs)*mu) r *
    finePairAliasActionSpatialBudget d r M q ad bd C a rho eta ell
  have hf (r : ℕ) : 0 ≤ f r := by
    dsimp [f, finePairAliasActionSpatialBudget]
    have h := poissonCountWeight_nonneg (by positivity : 0 ≤ (3*Cs)*mu) r
    have hK := spatialInverseFourConstant_nonneg d
    positivity
  simp_rw [mul_ite, mul_zero]
  refine (finite_refined_gated_sum_le_tail D M (fun r => poissonCountWeight (Cs*mu) r *
    ∫ U, finePairAliasGeometryEnvelope (d := d) (n := r) ad bd ell N M q C a rho eta U
      ∂fullSpatialPatchDesign d r) f hf ?_).trans
    (finite_fine_pair_saddle_alias_budget_le (by omega) haD had hbd hab htau hc0 hK M D q (D-M)
      C a rho eta ell N (3*Cs) mu hN hell hDM (by positivity) hmu hmu1)
  intro r hr _
  simpa only [f, mul_assoc] using poissonCountWeight_mul_le_of_le_pow (x := Cs*mu) (by positivity)
    (finePairAliasGeometryEnvelope_integrable_and_le (d := d) (n := r) hd
      ad bd ell N (lt_of_lt_of_le zero_lt_one hell1) hellN M q C a rho eta).2

end

end NearlyMinimax
