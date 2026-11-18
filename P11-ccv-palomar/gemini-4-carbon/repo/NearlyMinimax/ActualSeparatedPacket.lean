module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import NearlyMinimax.AnchoredGeometry
public import NearlyMinimax.CellPolynomialProjection
public import NearlyMinimax.CoordinatePartialBridge
public import NearlyMinimax.HighResponseRemainder
public import NearlyMinimax.LowSmoothnessPrior
public import NearlyMinimax.Model
public import RoughRegime.ComplexDerivativeBridge

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped BigOperators ENNReal Topology
namespace NearlyMinimax

-- ============================================================================
-- 1. High Density Updates, Separated Rows, and Actual Separated Packet
-- ============================================================================

section DensityUpdatesAndPackets
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

section PolyDensity
open Polynomial

def densityDerivativeWeight (D : ℕ) (j : Fin (derivativeOrder D + 1)) : ℝ :=
  lobattoDerivativeWeight ((D - 1) / 2) j

def densityUnitExponent (r : ℕ) : Fin r →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun _ => 1) (by simp)

@[simp] lemma densityUnitExponent_apply (r : ℕ) (i : Fin r) :
    densityUnitExponent r i = 1 := by simp [densityUnitExponent]

@[simp] lemma densityUnitExponent_degree (r : ℕ) :
    (densityUnitExponent r).degree = r := by simp [Finsupp.degree_eq_sum]

def densityDerivativeAction (r D : ℕ) (f : (Fin r → ℝ) → ℝ) : ℝ :=
  ∑ h : Fin r → Fin (derivativeOrder D + 1),
    (∏ l, densityDerivativeWeight D (h l)) * f fun l => lobattoNode (derivativeOrder D) (h l)

private lemma densityDerivativeAction_polynomial (r D : ℕ) (hD : 1 ≤ D)
    (P : MvPolynomial (Fin r) ℝ) (hP : ∀ d ∈ P.support, ∀ l, d l ≤ D) :
    densityDerivativeAction r D (fun ε => MvPolynomial.eval ε P) = P.coeff (densityUnitExponent r) := by
  have h1 (k : ℕ) (hk : k ≤ D) :
      (∑ j : Fin (derivativeOrder D + 1), densityDerivativeWeight D j * lobattoNode (derivativeOrder D) j ^ k) =
        if k = 1 then 1 else 0 := by
    have hp : (X ^ k : ℝ[X]).degree ≤ D := by
      simpa only [degree_X_pow, Nat.cast_withBot] using WithBot.coe_le_coe.mpr hk
    simpa [densityDerivativeWeight, ← coeff_zero_eq_eval_zero, coeff_derivative, coeff_X_pow, eq_comm] using
      derivative_rule_exact D hD (X ^ k) hp
  have hmon (d : Fin r →₀ ℕ) (hd : ∀ l, d l ≤ D) :
      densityDerivativeAction r D (fun ε => ∏ l, ε l ^ d l) = if d = densityUnitExponent r then 1 else 0 := by
    unfold densityDerivativeAction
    simp_rw [← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum fun (l : Fin r) (j : Fin (derivativeOrder D + 1)) =>
      densityDerivativeWeight D j * lobattoNode (derivativeOrder D) j ^ d l]
    simp_rw [h1 _ (hd _)]
    by_cases he : d = densityUnitExponent r
    · subst he; simp
    · rw [if_neg he]
      obtain ⟨l, hl⟩ : ∃ l, d l ≠ 1 := by by_contra hn; exact he (by ext l; simpa using not_exists.mp hn l)
      exact Finset.prod_eq_zero (Finset.mem_univ l) (by simp [hl])
  unfold densityDerivativeAction
  simp only [MvPolynomial.eval_eq', Finset.mul_sum]; rw [Finset.sum_comm]
  simp_rw [show ∀ d : Fin r →₀ ℕ,
    (∑ h : Fin r → Fin (derivativeOrder D + 1), (∏ l, densityDerivativeWeight D (h l)) *
      (P.coeff d * ∏ l, lobattoNode (derivativeOrder D) (h l) ^ d l)) =
    P.coeff d * densityDerivativeAction r D (fun ε => ∏ l, ε l ^ d l) from fun _ => by
      unfold densityDerivativeAction; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring]
  refine (Finset.sum_congr rfl fun d hd => by rw [hmon d (hP d hd)]).trans ?_
  simp [Finset.sum_ite_eq', MvPolynomial.mem_support_iff]; exact fun h => h.symm

def densityModulationPolynomial {ι : Type*} (r : ℕ) (B : ι → Fin r → ℝ) (i : ι) : MvPolynomial (Fin r) ℝ :=
  ∑ l, MvPolynomial.C (B i l) * MvPolynomial.X l

private lemma densityModulationPolynomial_homogeneous {ι : Type*} (r : ℕ) (B : ι → Fin r → ℝ) (i : ι) :
    (densityModulationPolynomial r B i).IsHomogeneous 1 :=
  MvPolynomial.IsHomogeneous.sum _ _ _ fun _ _ => MvPolynomial.isHomogeneous_C_mul_X _ _

private def densityResetPolynomial {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (r : ℕ) (z t : ℝ) (p : ι → ℝ) (B : ι → Fin r → ℝ) : MvPolynomial (Fin r) ℝ :=
  ∏ i ∈ S, (MvPolynomial.C z + MvPolynomial.C (t * p i) * densityModulationPolynomial r B i)

private lemma density_derivative_product_exact {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (r D : ℕ) (hD : 1 ≤ D) (hSD : S.card ≤ D)
    (z t : ℝ) (p : ι → ℝ) (B : ι → Fin r → ℝ) :
    densityDerivativeAction r D (fun ε => ∏ i ∈ S, (z + t * p i * ∑ l, ε l * B i l)) =
      z ^ (S.card - r) * t ^ r *
        ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
          (∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r) := by
  have htdeg : (densityResetPolynomial S r z t p B).totalDegree ≤ S.card :=
    (MvPolynomial.totalDegree_finsetProd _ _).trans
      ((Finset.sum_le_sum (g := fun _ => 1) fun i _ => (MvPolynomial.totalDegree_add _ _).trans
        (max_le (by simp) ((densityModulationPolynomial_homogeneous r B i).C_mul (t * p i)).totalDegree_le)).trans_eq (by simp))
  rw [show (fun ε => ∏ i ∈ S, (z + t * p i * ∑ l, ε l * B i l)) =
      fun ε => MvPolynomial.eval ε (densityResetPolynomial S r z t p B) from funext fun ε => by
        simp only [densityResetPolynomial, map_prod, map_add, map_mul, MvPolynomial.eval_C,
          densityModulationPolynomial, map_sum, MvPolynomial.eval_X, mul_comm (B _ _)],
    densityDerivativeAction_polynomial r D hD _ fun d hd l =>
      (MvPolynomial.le_degreeOf_of_mem_support l hd).trans ((MvPolynomial.degreeOf_le_totalDegree _ _).trans (htdeg.trans hSD))]
  classical
  unfold densityResetPolynomial
  simp_rw [add_comm (MvPolynomial.C z)]; rw [Finset.prod_add]; simp only [MvPolynomial.coeff_sum]
  rw [Finset.sum_congr rfl fun U _ => show ((∏ i ∈ U, MvPolynomial.C (t * p i) * densityModulationPolynomial r B i) *
      ∏ i ∈ S \ U, MvPolynomial.C z).coeff (densityUnitExponent r) =
      z ^ (S \ U).card * t ^ U.card * (∏ i ∈ U, p i) *
        (∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r) by
    rw [Finset.prod_mul_distrib, ← map_prod, ← map_prod, mul_comm _ (MvPolynomial.C _),
      mul_assoc, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul]
    simp only [Finset.prod_const, Finset.prod_mul_distrib]; ring]
  rw [Finset.sum_congr rfl fun U hU => show z ^ (S \ U).card * t ^ U.card * (∏ i ∈ U, p i) *
        (∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r) =
      if U.card = r then z ^ (S.card - r) * t ^ r * ((∏ i ∈ U, p i) *
        (∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r)) else 0 by
    by_cases hc : U.card = r
    · rw [if_pos hc, Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hU), hc]; ring
    · rw [if_neg hc]
      have hh := MvPolynomial.IsHomogeneous.prod U (fun i => densityModulationPolynomial r B i) (fun _ => 1)
        fun i _ => densityModulationPolynomial_homogeneous r B i
      simp only [hh.coeff_eq_zero (d := densityUnitExponent r) (by simpa using Ne.symm hc), mul_zero]]
  rw [← Finset.sum_filter, ← Finset.powersetCard_eq_filter, ← Finset.mul_sum]

def densityMargin (a b z : ℝ) : ℝ := (z - a) * (b - z) / (b - a)

theorem densityMargin_bounds (a b : ℝ) (hab : a < b) (z : ℝ) (hz : z ∈ Icc a b) :
    0 ≤ densityMargin a b z ∧ densityMargin a b z ≤ z - a ∧
      densityMargin a b z ≤ b - z ∧ densityMargin a b z ≤ (b - a) / 4 := by
  have hba : 0 < b - a := sub_pos.mpr hab
  dsimp [densityMargin]
  exact ⟨div_nonneg (mul_nonneg (sub_nonneg.mpr hz.1) (sub_nonneg.mpr hz.2)) hba.le,
    (div_le_iff₀ hba).mpr (by nlinarith [hz.1, hz.2]),
    (div_le_iff₀ hba).mpr (by nlinarith [hz.1, hz.2]),
    (div_le_iff₀ hba).mpr (by nlinarith [sq_nonneg (z - (a + b) / 2)])⟩

theorem densityMargin_zero_ne (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    densityMargin a b 0 ≠ 0 :=
  div_ne_zero (mul_ne_zero (by simpa using ha.ne') (by simpa using (ha.trans hab).ne')) (sub_pos.mpr hab).ne'

def densityCountCoefficient (a b : ℝ) (m r k : ℕ) : ℝ :=
  (∑ j : Fin (m + r + 1), exteriorWeight a b (m + r) j *
    (exteriorNode a b (m + r) j ^ (k - r) *
      densityMargin a b (exteriorNode a b (m + r) j) ^ r)) / densityMargin a b 0 ^ r

theorem densityCountCoefficient_exact (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r k : ℕ) (hr : 1 ≤ r) (hrk : r ≤ k) (hkm : k ≤ m) :
    densityCountCoefficient a b m r k = if k = r then 1 else 0 := by
  let mp : ℝ[X] := (X - C a) * (C b - X) * C ((b - a)⁻¹)
  let cp : ℝ[X] := X ^ (k - r) * mp ^ r
  have hmdeg : mp.natDegree ≤ 2 := by
    have h1 : (X - C a : ℝ[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
    have h2 : (C b - X : ℝ[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
    exact natDegree_mul_le.trans (by simpa using (natDegree_mul_le (p := X - C a) (q := C b - X)).trans (add_le_add h1 h2))
  have hcdeg : cp.degree ≤ m + r := degree_le_natDegree.trans <| by
    have hdeg1 : cp.natDegree ≤ (k - r) + r * 2 := by
      dsimp only [cp]
      exact natDegree_mul_le.trans (by
        rw [natDegree_X_pow]
        exact Nat.add_le_add_left ((natDegree_pow_le.trans (Nat.mul_le_mul_left r hmdeg))) _)
    exact_mod_cast (by omega : cp.natDegree ≤ m + r)
  have he := exterior_rule_exact a b hab (m + r) (by omega) cp hcdeg
  simp only [cp, mp, eval_mul, eval_pow, eval_sub, eval_X, eval_C, ← div_eq_mul_inv] at he
  change (∑ j : Fin (m + r + 1), exteriorWeight a b (m + r) j *
    (exteriorNode a b (m + r) j ^ (k - r) * densityMargin a b (exteriorNode a b (m + r) j) ^ r)) =
    0 ^ (k - r) * densityMargin a b 0 ^ r at he
  unfold densityCountCoefficient; rw [he]
  by_cases hkr : k = r
  · subst k; simp [pow_ne_zero r (densityMargin_zero_ne a b ha hab)]
  · simp [zero_pow (by omega : k - r ≠ 0), hkr]

theorem densityCountCoefficient_abs_bound (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r k : ℕ) (hr : 1 ≤ r) :
    |densityCountCoefficient a b m r k| ≤
      (b ^ (k - r) * ((b - a) / 4) ^ r / |densityMargin a b 0| ^ r) *
        Real.cosh ((m + r : ℕ) * exteriorTau ((a + b) / (b - a))) := by
  have hbn : 0 ≤ b := (ha.trans hab).le
  have hs : |∑ j : Fin (m + r + 1), exteriorWeight a b (m + r) j *
      (exteriorNode a b (m + r) j ^ (k - r) * densityMargin a b (exteriorNode a b (m + r) j) ^ r)| ≤
      Real.cosh ((m + r : ℕ) * exteriorTau ((a + b) / (b - a))) * (b ^ (k - r) * ((b - a) / 4) ^ r) := by
    refine ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum
      (g := fun j => |exteriorWeight a b (m + r) j| * (b ^ (k - r) * ((b - a) / 4) ^ r)) fun j _ => ?_)).trans_eq
      (by rw [← Finset.sum_mul, exterior_rule_variation a b ha hab _ (by omega)])
    have hz := exteriorNode_mem a b hab.le (m + r) j
    have ht := densityMargin_bounds a b hab _ hz
    rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg (ha.le.trans hz.1), abs_of_nonneg ht.1]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (pow_le_pow_left₀ (ha.le.trans hz.1) hz.2 _)
        (pow_le_pow_left₀ ht.1 ht.2.2.2 _) (pow_nonneg ht.1 _) (pow_nonneg hbn _))
      (abs_nonneg _)
  unfold densityCountCoefficient; rw [abs_div, abs_pow]
  exact (div_le_div_of_nonneg_right hs (by positivity)).trans_eq (by ring)

end PolyDensity

def localDensityReset {ι : Type*} (a b : ℝ) (r : ℕ) (z : ℝ)
    (ε : Fin r → ℝ) (p : ι → ℝ) (B : ι → Fin r → ℝ) (i : ι) : ℝ :=
  z + densityMargin a b z / ((r : ℝ) * b) * p i * ∑ l, ε l * B i l

theorem localDensityReset_slope_bound {ι : Type*} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (r : ℕ) (hr : 1 ≤ r) (z : ℝ) (hz : z ∈ Icc a b)
    (ε : Fin r → ℝ) (hε : ∀ l, |ε l| ≤ 1) (B : ι → Fin r → ℝ) (i : ι)
    (hB : ∀ l, |B i l| ≤ 1) :
    |densityMargin a b z / ((r : ℝ) * b) * ∑ l, ε l * B i l| ≤ (b - a) / (4 * b) := by
  have hb : 0 < b := ha.trans hab
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hθ := densityMargin_bounds a b hab z hz
  have hsum : |∑ l, ε l * B i l| ≤ (r : ℝ) :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (g := fun _ => (1 : ℝ)) fun l _ => by
        rw [abs_mul]; exact (mul_le_mul (hε l) (hB l) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)).trans_eq (by simp))
  have hcoef : 0 ≤ densityMargin a b z / ((r : ℝ) * b) := div_nonneg hθ.1 (mul_pos hrR hb).le
  rw [abs_mul, abs_of_nonneg hcoef]
  exact ((mul_le_mul_of_nonneg_left hsum hcoef).trans_eq (by field_simp)).trans
    ((div_le_div_of_nonneg_right hθ.2.2.2 hb.le).trans_eq (by ring))

theorem localDensityReset_mem_interval {ι : Type*} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (r : ℕ) (hr : 1 ≤ r) (z : ℝ) (hz : z ∈ Icc a b)
    (ε : Fin r → ℝ) (hε : ∀ l, |ε l| ≤ 1) (p : ι → ℝ)
    (B : ι → Fin r → ℝ) (i : ι) (hp : p i ∈ Icc a b) (hB : ∀ l, |B i l| ≤ 1) :
    localDensityReset a b r z ε p B i ∈ Icc a b := by
  have hb : 0 < b := ha.trans hab
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hθ := densityMargin_bounds a b hab z hz
  have hp0 : 0 ≤ p i := ha.le.trans hp.1
  have hsum : |∑ l, ε l * B i l| ≤ (r : ℝ) :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (g := fun _ => (1 : ℝ)) fun l _ => by
        rw [abs_mul]; exact (mul_le_mul (hε l) (hB l) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)).trans_eq (by simp))
  have hcoef : 0 ≤ densityMargin a b z / ((r : ℝ) * b) := div_nonneg hθ.1 (mul_pos hrR hb).le
  have hshift : |densityMargin a b z / ((r : ℝ) * b) * p i * ∑ l, ε l * B i l| ≤ densityMargin a b z := by
    rw [abs_mul, abs_mul, abs_of_nonneg hcoef, abs_of_nonneg hp0]
    exact ((mul_le_mul_of_nonneg_left hsum (mul_nonneg hcoef hp0)).trans_eq (by field_simp)).trans
      ((mul_le_mul_of_nonneg_left hp.2 (div_nonneg hθ.1 hb.le)).trans_eq (div_mul_cancel₀ _ hb.ne'))
  obtain ⟨hl, hu⟩ := abs_le.mp hshift
  constructor <;> dsimp [localDensityReset] <;> linarith [hθ.2.1, hθ.2.2.1]

def densitySeparatedSym {ι : Type*} [DecidableEq ι] (r : ℕ) (B : ι → Fin r → ℝ) (S : Finset ι) : ℝ :=
  (∏ i ∈ S, densityModulationPolynomial r B i).coeff (densityUnitExponent r) / (r.factorial : ℝ)

def densityPacketPrefactor (a b : ℝ) (r : ℕ) : ℝ :=
  (r : ℝ) ^ r / (r.factorial : ℝ) * (b / densityMargin a b 0) ^ r

def densityPacketAction (a b : ℝ) (m r D : ℕ) (f : ℝ → (Fin r → ℝ) → ℝ) : ℝ :=
  densityPacketPrefactor a b r * ∑ j : Fin (m + r + 1),
    exteriorWeight a b (m + r) j * densityDerivativeAction r D (f (exteriorNode a b (m + r) j))

private lemma density_packet_product_exact {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r D : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hSD : S.card ≤ D)
    (p : ι → ℝ) (B : ι → Fin r → ℝ) :
    densityPacketAction a b m r D (fun z ε => ∏ i ∈ S, localDensityReset a b r z ε p B i) =
      densityCountCoefficient a b m r S.card *
        ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) * densitySeparatedSym r B U := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have hb : b ≠ 0 := (ha.trans hab).ne'
  have hθ : densityMargin a b 0 ≠ 0 := densityMargin_zero_ne a b ha hab
  have hfac : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
  unfold densityPacketAction localDensityReset
  simp_rw [density_derivative_product_exact S r D hD hSD]
  unfold densityCountCoefficient densitySeparatedSym densityPacketPrefactor
  rw [show (∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
      ((∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r) / (r.factorial : ℝ))) =
    (∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
      (∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r)) / (r.factorial : ℝ) by
    simp_rw [← mul_div_assoc]; rw [Finset.sum_div]]
  simp only [div_pow, mul_pow]; rw [Finset.mul_sum]
  refine (Finset.sum_congr rfl fun j _ => show _ =
    (exteriorWeight a b (m + r) j *
      (exteriorNode a b (m + r) j ^ (S.card - r) *
        densityMargin a b (exteriorNode a b (m + r) j) ^ r) / densityMargin a b 0 ^ r) *
      ((∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
        (∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r)) / (r.factorial : ℝ)) by
    field_simp).trans ?_
  simp only [← Finset.sum_mul, Finset.sum_div]

private def densityAssignmentExponent (r : ℕ) (f : Fin r → Fin r) : Fin r →₀ ℕ :=
  ∑ i, Finsupp.single (f i) 1

theorem densitySeparatedSym_eq_permutation_average {ι : Type*} [DecidableEq ι]
    (r : ℕ) (B : ι → Fin r → ℝ) (S : Finset ι) (e : Fin r ≃ S) :
    densitySeparatedSym r B S =
      (∑ σ : Equiv.Perm (Fin r), ∏ i, B (e i) (σ i)) / (r.factorial : ℝ) := by
  classical
  have hperm (B' : Fin r → Fin r → ℝ) :
      (∏ i, densityModulationPolynomial r B' i).coeff (densityUnitExponent r) =
        ∑ σ : Equiv.Perm (Fin r), ∏ i, B' i (σ i) := by
    unfold densityModulationPolynomial; rw [Fintype.prod_sum]
    simp_rw [MvPolynomial.C_mul_X_eq_monomial,
      show ∀ f : Fin r → Fin r, (∏ i, MvPolynomial.monomial (Finsupp.single (f i) 1) (B' i (f i))) =
        MvPolynomial.monomial (densityAssignmentExponent r f) (∏ i, B' i (f i)) from
        fun _ => (MvPolynomial.monomial_sum_prod Finset.univ _ _).symm]
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    have hbij (f : Fin r → Fin r) : densityAssignmentExponent r f = densityUnitExponent r ↔ Function.Bijective f :=
      ⟨fun he => by
        have hs : Function.Surjective f := fun l => by
          by_contra hn
          have hne (i : Fin r) : f i ≠ l := fun h => hn ⟨i, h⟩
          have hv := congrArg (fun d : Fin r →₀ ℕ => d l) he
          simp [densityAssignmentExponent, hne] at hv
        exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩,
       fun hf => by
        let ef := Equiv.ofBijective f hf
        change (∑ i, Finsupp.single (ef i) 1) = densityUnitExponent r
        rw [ef.sum_comp fun l => Finsupp.single l 1]; ext; simp⟩
    simp only [hbij]
    have hs : (∑ f : Fin r → Fin r, if Function.Bijective f then ∏ i, B' i (f i) else 0) =
        ∑ f : {f : Fin r → Fin r // Function.Bijective f}, ∏ i, B' i (f.1 i) := by
      apply Finset.sum_congr_set {f : Fin r → Fin r | Function.Bijective f}
      · intro _ hf; exact if_pos hf
      · intro _ hf; exact if_neg hf
    rw [hs]
    exact Fintype.sum_equiv Equiv.bijectiveEquiv _ _ fun _ => rfl
  unfold densitySeparatedSym
  rw [show (∏ i ∈ S, densityModulationPolynomial r B i) =
      ∏ i : Fin r, densityModulationPolynomial r (fun i l => B (e i) l) i by
    rw [← Finset.prod_coe_sort]; exact (e.prod_comp fun i : S => densityModulationPolynomial r B i).symm, hperm]

theorem density_packet_product_zero_of_small_count {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r D : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hSD : S.card ≤ D)
    (hSr : S.card < r) (p : ι → ℝ) (B : ι → Fin r → ℝ) :
    densityPacketAction a b m r D (fun z ε => ∏ i ∈ S, localDensityReset a b r z ε p B i) = 0 := by
  rw [density_packet_product_exact S a b ha hab m r D hr hD hSD p B,
    Finset.powersetCard_eq_empty.mpr hSr]; simp

theorem density_packet_product_count_selector {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r D : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hSD : S.card ≤ D)
    (hSm : S.card ≤ m) (p : ι → ℝ) (B : ι → Fin r → ℝ) :
    densityPacketAction a b m r D (fun z ε => ∏ i ∈ S, localDensityReset a b r z ε p B i) =
      if S.card = r then ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) * densitySeparatedSym r B U else 0 := by
  by_cases hSr : r ≤ S.card
  · rw [density_packet_product_exact S a b ha hab m r D hr hD hSD p B,
      densityCountCoefficient_exact a b ha hab m r S.card hr hSr hSm]
    split_ifs <;> simp
  · rw [density_packet_product_zero_of_small_count S a b ha hab m r D hr hD hSD (by omega) p B, if_neg (by omega)]

def densityPacketAtom (a b : ℝ) (m r D : ℕ)
    (j : Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1))) : ℝ × (Fin r → ℝ) :=
  (exteriorNode a b (m + r) j.1, fun l => lobattoNode (derivativeOrder D) (j.2 l))

def densityPacketWeight (a b : ℝ) (m r D : ℕ)
    (j : Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1))) : ℝ :=
  densityPacketPrefactor a b r * exteriorWeight a b (m + r) j.1 *
    ∏ l, densityDerivativeWeight D (j.2 l)

theorem densityPacketAtom_mem (a b : ℝ) (hab : a ≤ b) (m r D : ℕ)
    (j : Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1))) :
    (densityPacketAtom a b m r D j).1 ∈ Icc a b ∧
      ∀ l, |(densityPacketAtom a b m r D j).2 l| ≤ 1 :=
  ⟨exteriorNode_mem a b hab (m + r) j.1, fun _ => abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩⟩

theorem densityPacketWeight_variation (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r D : ℕ) (hr : 1 ≤ r) :
    (∑ j : Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1)),
      |densityPacketWeight a b m r D j|) =
      |densityPacketPrefactor a b r| *
        Real.cosh ((m + r : ℕ) * exteriorTau ((a + b) / (b - a))) * (derivativeOrder D : ℝ) ^ r := by
  have htv : (∑ h : Fin r → Fin (derivativeOrder D + 1), ∏ l, |densityDerivativeWeight D (h l)|) =
      (derivativeOrder D : ℝ) ^ r := by
    have hv : (∑ j : Fin (derivativeOrder D + 1), |densityDerivativeWeight D j|) = (derivativeOrder D : ℝ) :=
      lobatto_derivative_rule_variation ((D - 1) / 2)
    rw [← Fintype.prod_sum fun (_ : Fin r) (j : Fin (derivativeOrder D + 1)) => |densityDerivativeWeight D j|]
    simp only [hv, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [densityPacketWeight, abs_mul, Finset.abs_prod, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, htv]
  rw [← Finset.sum_mul, ← Finset.mul_sum, exterior_rule_variation a b ha hab _ (by omega)]

private lemma densitySeparatedSym_abs_le_one {ι : Type*} [DecidableEq ι]
    (r : ℕ) (B : ι → Fin r → ℝ) (S : Finset ι) (hS : S.card = r)
    (hB : ∀ i ∈ S, ∀ l, |B i l| ≤ 1) : |densitySeparatedSym r B S| ≤ 1 := by
  classical
  let e : Fin r ≃ S := (Fintype.equivFinOfCardEq (show Fintype.card S = r by simpa)).symm
  rw [densitySeparatedSym_eq_permutation_average r B S e, abs_div,
    abs_of_pos (by exact_mod_cast r.factorial_pos : (0 : ℝ) < r.factorial)]
  refine (div_le_iff₀ (by exact_mod_cast r.factorial_pos : (0 : ℝ) < r.factorial)).mpr
    ((Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (g := fun _ => (1 : ℝ)) fun σ _ => ?_).trans_eq (by simp [Fintype.card_perm])))
  rw [Finset.abs_prod]
  exact (Finset.prod_le_prod₀ (g := fun _ => (1 : ℝ)) (fun _ _ => abs_nonneg _)
    fun i _ => hB (e i) (e i).2 (σ i)).trans_eq (by simp)

-- Separated rows and actual separated packet

section SeparatedRowsAndPacket

def responseMatrixEntryCoefficient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) (C : ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) (i j : ι) : ℝ :=
  ∑ s : Bool, ∑ t : Bool, (C ^ 2 / 2 * fairSign s * fairSign t) *
    ∑ h : Fin (2 * q + 2), responseWeight q h *
      Φ (coefficientReset c (covarianceAtom C i j s t) (responseNode q h))

theorem responseMatrixAction_entry_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) (C : ℝ) (A : ι → ι → ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    responseMatrixAction q C A c Φ =
      ∑ i, ∑ j, A i j * responseMatrixEntryCoefficient q C c Φ i j := by
  simp only [responseMatrixAction, covarianceAction, covarianceWeight,
    responseMatrixEntryCoefficient, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring

theorem responseMatrixAction_scalar_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) (C t : ℝ) (A : ι → ι → ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    responseMatrixAction q C (fun i j => t * A i j) c Φ = t * responseMatrixAction q C A c Φ := by
  simp only [responseMatrixAction_entry_sum, Finset.mul_sum, mul_assoc]

theorem responseMatrixAction_integrable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
    (σ : Measure Z) (q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Integrable (fun ζ => A ζ i j) σ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    Integrable (fun ζ => responseMatrixAction q C (A ζ) c Φ) σ := by
  simp only [responseMatrixAction_entry_sum]
  exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => (hA i j).mul_const _

private lemma responseMatrixAction_integral {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
    (σ : Measure Z) (q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Integrable (fun ζ => A ζ i j) σ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    responseMatrixAction q C (fun i j => ∫ ζ, A ζ i j ∂σ) c Φ =
      ∫ ζ, responseMatrixAction q C (A ζ) c Φ ∂σ := by
  simp only [responseMatrixAction_entry_sum]
  rw [integral_finset_sum Finset.univ fun i _ => integrable_finset_sum _ fun j _ => (hA i j).mul_const _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum Finset.univ fun j _ => (hA i j).mul_const _]
  simp only [integral_mul_const]

def separatedMatrixCost {Z ι : Type*} [Fintype ι] (A : Z → ι → ι → ℝ) (ζ : Z) : ℝ :=
  ∑ i, ∑ j, |A ζ i j|

theorem separatedMatrix_entry_integrable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
    (σ : Measure Z) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable fun ζ => A ζ i j)
    (hcost : Integrable (separatedMatrixCost A) σ) (i j : ι) :
    Integrable (fun ζ => A ζ i j) σ :=
  hcost.mono' (hA i j).aestronglyMeasurable <| Eventually.of_forall fun ζ => by
    rw [Real.norm_eq_abs]
    exact (Finset.single_le_sum (fun k _ => abs_nonneg (A ζ i k)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => abs_nonneg (A ζ k l)) (Finset.mem_univ i))

def separatedSubsetMatrix {Z α ι : Type*} [MeasurableSpace Z] [DecidableEq α]
    (σ : Measure Z) (r : ℕ) (B : Z → α → Fin r → ℝ) (A : Z → ι → ι → ℝ) (S : Finset α) : ι → ι → ℝ :=
  fun i j => ∫ ζ, densitySeparatedSym r (B ζ) S * A ζ i j ∂σ

private lemma separated_subset_entry_integrable {Z α ι : Type*} [MeasurableSpace Z]
    [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (σ : Measure Z) (r : ℕ) (B : Z → α → Fin r → ℝ) (hB : ∀ i l, Measurable fun ζ => B ζ i l)
    (hBbound : ∀ ζ i l, |B ζ i l| ≤ 1) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable fun ζ => A ζ i j) (hcost : Integrable (separatedMatrixCost A) σ)
    (S : Finset α) (hS : S.card = r) (i j : ι) :
    Integrable (fun ζ => densitySeparatedSym r (B ζ) S * A ζ i j) σ := by
  classical
  let e : Fin r ≃ S := (Fintype.equivFinOfCardEq (show Fintype.card S = r by simpa using hS)).symm
  have hmS : Measurable fun ζ => densitySeparatedSym r (B ζ) S := by
    rw [show (fun ζ => densitySeparatedSym r (B ζ) S) =
      fun ζ => (∑ τ : Equiv.Perm (Fin r), ∏ k, B ζ (e k) (τ k)) / (r.factorial : ℝ) from
        funext fun ζ => densitySeparatedSym_eq_permutation_average r (B ζ) S e]
    exact (Finset.measurable_fun_sum _ fun τ _ => Finset.measurable_fun_prod _ fun k _ => hB (e k) (τ k)).div_const _
  refine hcost.mono' (hmS.mul (hA i j)).aestronglyMeasurable (Eventually.of_forall fun ζ => ?_)
  change ‖densitySeparatedSym r (B ζ) S * A ζ i j‖ ≤ separatedMatrixCost A ζ
  rw [Real.norm_eq_abs, abs_mul]
  exact ((mul_le_mul_of_nonneg_right
    (densitySeparatedSym_abs_le_one r (B ζ) S hS fun k _ l => hBbound ζ k l) (abs_nonneg _)).trans_eq (one_mul _)).trans
    ((Finset.single_le_sum (fun k _ => abs_nonneg (A ζ i k)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => abs_nonneg (A ζ k l)) (Finset.mem_univ i)))

theorem densityPacketAction_mul_right (a b : ℝ) (m r D : ℕ)
    (f : ℝ → (Fin r → ℝ) → ℝ) (t : ℝ) :
    densityPacketAction a b m r D (fun z ε => f z ε * t) = densityPacketAction a b m r D f * t := by
  simp only [densityPacketAction, densityDerivativeAction, Finset.sum_mul, mul_assoc]

def highSeparatedPacketAction {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
    (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (c : ι → ℝ) (G : Z → ℝ → (Fin r → ℝ) → ℝ) (Φ : (ι → ℝ) → ℝ) : ℝ :=
  ∫ ζ, densityPacketAction a b m r D (fun z ε => G ζ z ε * responseMatrixAction q C (A ζ) c Φ) ∂σ

theorem highSeparatedPacketAction_row {Z α ι : Type*} [MeasurableSpace Z]
    [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (σ : Measure Z) (a b : ℝ) (ha : 0 < a) (hab : a < b) (m r D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (S : Finset α) (hSD : S.card ≤ D) (p : α → ℝ)
    (B : Z → α → Fin r → ℝ) (hB : ∀ i l, Measurable fun ζ => B ζ i l)
    (hBbound : ∀ ζ i l, |B ζ i l| ≤ 1) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable fun ζ => A ζ i j)
    (hcost : Integrable (separatedMatrixCost A) σ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    highSeparatedPacketAction σ a b m r D q C A c
      (fun ζ z ε => ∏ i ∈ S, localDensityReset a b r z ε p (B ζ) i) Φ =
      densityCountCoefficient a b m r S.card *
        ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
          responseMatrixAction q C (separatedSubsetMatrix σ r B A U) c Φ := by
  have hInt (U : Finset α) (hU : U ∈ S.powersetCard r) :
      Integrable (fun ζ => (∏ i ∈ U, p i) *
        (densitySeparatedSym r (B ζ) U * responseMatrixAction q C (A ζ) c Φ)) σ := by
    have hr' : Integrable (fun ζ => densitySeparatedSym r (B ζ) U * responseMatrixAction q C (A ζ) c Φ) σ := by
      simpa only [responseMatrixAction_scalar_matrix] using
        responseMatrixAction_integrable σ q C (fun ζ i j => densitySeparatedSym r (B ζ) U * A ζ i j)
          (separated_subset_entry_integrable σ r B hB hBbound A hA hcost U (Finset.mem_powersetCard.mp hU).2) c Φ
    exact hr'.const_mul _
  unfold highSeparatedPacketAction
  simp_rw [show ∀ ζ : Z, densityPacketAction a b m r D
      (fun z ε => (∏ i ∈ S, localDensityReset a b r z ε p (B ζ) i) * responseMatrixAction q C (A ζ) c Φ) =
      densityCountCoefficient a b m r S.card *
        ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
          (densitySeparatedSym r (B ζ) U * responseMatrixAction q C (A ζ) c Φ) from fun ζ => by
    rw [densityPacketAction_mul_right, density_packet_product_exact S a b ha hab m r D hr hD hSD p (B ζ)]
    simp only [Finset.sum_mul, mul_assoc]]
  rw [integral_const_mul, integral_finsetSum _ hInt]
  congr 1; refine Finset.sum_congr rfl fun U hU => ?_
  rw [integral_const_mul]
  congr 1; unfold separatedSubsetMatrix
  rw [responseMatrixAction_integral σ q C _
    (separated_subset_entry_integrable σ r B hB hBbound A hA hcost U (Finset.mem_powersetCard.mp hU).2)]
  simp only [responseMatrixAction_scalar_matrix]

theorem highSeparatedPacketAction_count_selector {Z α ι : Type*} [MeasurableSpace Z]
    [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (σ : Measure Z) (a b : ℝ) (ha : 0 < a) (hab : a < b) (m r D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (S : Finset α) (hSD : S.card ≤ D) (hSm : S.card ≤ m) (hrS : r ≤ S.card) (p : α → ℝ)
    (B : Z → α → Fin r → ℝ) (hB : ∀ i l, Measurable fun ζ => B ζ i l)
    (hBbound : ∀ ζ i l, |B ζ i l| ≤ 1) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable fun ζ => A ζ i j)
    (hcost : Integrable (separatedMatrixCost A) σ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    highSeparatedPacketAction σ a b m r D q C A c
      (fun ζ z ε => ∏ i ∈ S, localDensityReset a b r z ε p (B ζ) i) Φ =
      if S.card = r then ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
        responseMatrixAction q C (separatedSubsetMatrix σ r B A U) c Φ else 0 := by
  rw [highSeparatedPacketAction_row σ a b ha hab m r D q hr hD S hSD p B hB hBbound C A hA hcost c Φ,
    densityCountCoefficient_exact a b ha hab m r S.card hr hrS hSm]
  split_ifs <;> simp

theorem signedDensity_integral {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (w : X → ℝ) (hw : Integrable w μ) (hmw : Measurable w)
    (f : X → ℝ) (hf : Measurable f) (M : ℝ) (hbound : ∀ x, ‖f x‖ ≤ M) :
    (∫ᵛ x, f x ∂<•(μ.withDensityᵥ w)) = ∫ x, w x * f x ∂μ := by
  let μp := μ.withDensity fun x => ENNReal.ofReal (w x)
  let μn := μ.withDensity fun x => ENNReal.ofReal (-w x)
  letI : IsFiniteMeasure μp := isFiniteMeasure_withDensity_ofReal hw.hasFiniteIntegral
  letI : IsFiniteMeasure μn := isFiniteMeasure_withDensity_ofReal hw.neg.hasFiniteIntegral
  have hpv : μp.toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using
      (integrable_const M).mono' hf.aestronglyMeasurable (Eventually.of_forall hbound)
  have hnv : μn.toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using
      (integrable_const M).mono' hf.aestronglyMeasurable (Eventually.of_forall hbound)
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hw,
    VectorMeasure.integral_sub_vectorMeasure hpv hnv, VectorMeasure.integral_toSignedMeasure,
    VectorMeasure.integral_toSignedMeasure]
  dsimp only [μp, μn]
  have hmn : Measurable fun x => ENNReal.ofReal (-w x) := hmw.neg.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hmw.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul hmn
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  rw [← integral_sub (hw.pos_part.mul_bdd hf.aestronglyMeasurable (Eventually.of_forall hbound))
    (hw.neg_part.mul_bdd hf.aestronglyMeasurable (Eventually.of_forall hbound))]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only; rw [← sub_mul]
  congr 1; by_cases hh : 0 ≤ w x <;> simp [max_eq_left, max_eq_right, hh, neg_nonpos.mpr, neg_nonneg.mpr]

theorem joint_finite_integrable {Z I : Type*} [MeasurableSpace Z] [MeasurableSpace I]
    [Fintype I] [MeasurableSingletonClass I] (σ : Measure Z) [IsFiniteMeasure σ] (f : Z × I → ℝ)
    (hf : ∀ i, Measurable fun ζ => f (ζ, i)) (hi : ∀ i, Integrable (fun ζ => f (ζ, i)) σ) :
    Integrable f (σ.prod Measure.count) := by
  refine (integrable_prod_iff (measurable_from_prod_countable_left hf).aestronglyMeasurable).mpr
    ⟨Eventually.of_forall fun ζ => (integrable_const (∑ i, ‖f (ζ, i)‖)).mono'
      (measurable_of_countable _).aestronglyMeasurable
      (Eventually.of_forall fun i => Finset.single_le_sum (f := fun j => ‖f (ζ, j)‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ i)), ?_⟩
  simp only [integral_count]
  exact integrable_finsetSum _ fun i _ => (hi i).norm

abbrev HighDensityMarkIndex (m r D : ℕ) :=
  Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1))

abbrev HighResponseMarkIndex (ι : Type*) (q : ℕ) := (ι × ι) × (Bool × Bool) × Fin (2 * q + 2)

abbrev HighPacketMarkIndex (ι : Type*) (m r D q : ℕ) :=
  HighDensityMarkIndex m r D × HighResponseMarkIndex ι q

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

def highResponseMarkAtom (C : ℝ) (q : ℕ) (h : HighResponseMarkIndex ι q) : ℝ × (ι → ℝ) :=
  (responseNode q h.2.2, covarianceAtom C h.1.1 h.1.2 h.2.1.1 h.2.1.2)

def highResponseMarkWeight (C : ℝ) (q : ℕ) (A : ι → ι → ℝ) (h : HighResponseMarkIndex ι q) : ℝ :=
  responseWeight q h.2.2 * covarianceWeight C A h.1.1 h.1.2 h.2.1.1 h.2.1.2

def highPacketMarkWeight (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (e : Z × HighPacketMarkIndex ι m r D q) : ℝ :=
  densityPacketWeight a b m r D e.2.1 * highResponseMarkWeight C q (A e.1) e.2.2

theorem highPacketMarkWeight_measurable (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable fun ζ => A ζ i j) :
    Measurable (highPacketMarkWeight a b m r D q C A) :=
  measurable_from_prod_countable_left fun _ => by
    dsimp [highPacketMarkWeight, highResponseMarkWeight, covarianceWeight]; fun_prop

theorem highPacketMarkWeight_integrable (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable fun ζ => A ζ i j) (hcost : Integrable (separatedMatrixCost A) σ) :
    Integrable (highPacketMarkWeight a b m r D q C A) (σ.prod Measure.count) :=
  joint_finite_integrable σ _
    (fun _ => by dsimp [highPacketMarkWeight, highResponseMarkWeight, covarianceWeight]; fun_prop)
    fun h => by
      dsimp [highPacketMarkWeight, highResponseMarkWeight, covarianceWeight]
      exact (((((separatedMatrix_entry_integrable σ A hA hcost h.2.1.1 h.2.1.2).const_mul
        (C ^ 2 / 2)).mul_const (fairSign h.2.2.1.1)).mul_const (fairSign h.2.2.1.2)).const_mul
          (responseWeight q h.2.2.2)).const_mul (densityPacketWeight a b m r D h.1)

def highPacketSignedMeasure (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : SignedMeasure (Z × HighPacketMarkIndex ι m r D q) :=
  (σ.prod Measure.count).withDensityᵥ (highPacketMarkWeight a b m r D q C A)

theorem highResponseMark_action (q : ℕ) (C : ℝ) (A : ι → ι → ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    (∑ h : HighResponseMarkIndex ι q, highResponseMarkWeight C q A h *
      Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)) =
      responseMatrixAction q C A c Φ := by
  simp only [Fintype.sum_prod_type, highResponseMarkWeight, highResponseMarkAtom,
    responseMatrixAction, covarianceAction, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring

def highPacketObservable (a b : ℝ) (m r D q : ℕ) (C : ℝ) (c : ι → ℝ)
    (G : Z → ℝ → (Fin r → ℝ) → ℝ) (Φ : (ι → ℝ) → ℝ)
    (e : Z × HighPacketMarkIndex ι m r D q) : ℝ :=
  G e.1 (densityPacketAtom a b m r D e.2.1).1 (densityPacketAtom a b m r D e.2.1).2 *
    Φ (coefficientReset c (highResponseMarkAtom C q e.2.2).2 (highResponseMarkAtom C q e.2.2).1)

private lemma highPacketObservable_finite_action (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (c : ι → ℝ)
    (G : Z → ℝ → (Fin r → ℝ) → ℝ) (Φ : (ι → ℝ) → ℝ) (ζ : Z) :
    (∑ h : HighPacketMarkIndex ι m r D q,
      highPacketMarkWeight a b m r D q C A (ζ, h) * highPacketObservable a b m r D q C c G Φ (ζ, h)) =
      densityPacketAction a b m r D (fun z ε => G ζ z ε * responseMatrixAction q C (A ζ) c Φ) := by
  rw [Fintype.sum_prod_type]
  simp_rw [show ∀ h : HighDensityMarkIndex m r D,
      (∑ v : HighResponseMarkIndex ι q,
        highPacketMarkWeight a b m r D q C A (ζ, (h, v)) *
          highPacketObservable a b m r D q C c G Φ (ζ, (h, v))) =
      densityPacketWeight a b m r D h *
        (G ζ (densityPacketAtom a b m r D h).1 (densityPacketAtom a b m r D h).2 *
          responseMatrixAction q C (A ζ) c Φ) from fun _ => by
    rw [← highResponseMark_action q C (A ζ) c Φ]
    simp only [Finset.mul_sum, highPacketMarkWeight, highPacketObservable]
    exact Finset.sum_congr rfl fun _ _ => by ring]
  simp only [Fintype.sum_prod_type, densityPacketWeight, densityPacketAtom,
    densityPacketAction, densityDerivativeAction, Finset.mul_sum, mul_assoc]

theorem highPacketSignedMeasure_factor_integral (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable fun ζ => A ζ i j) (hcost : Integrable (separatedMatrixCost A) σ)
    (c : ι → ℝ) (G : Z → ℝ → (Fin r → ℝ) → ℝ)
    (hG : ∀ z ε, Measurable fun ζ => G ζ z ε) (L : ℝ) (hL : 0 ≤ L)
    (hGbound : ∀ (ζ : Z) (h : HighDensityMarkIndex m r D),
      |G ζ (densityPacketAtom a b m r D h).1 (densityPacketAtom a b m r D h).2| ≤ L)
    (Φ : (ι → ℝ) → ℝ) (M : ℝ)
    (hΦ : ∀ h : HighResponseMarkIndex ι q,
      |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)| ≤ M) :
    (∫ᵛ e, highPacketObservable a b m r D q C c G Φ e
      ∂<•(highPacketSignedMeasure σ a b m r D q C A)) =
      highSeparatedPacketAction σ a b m r D q C A c G Φ := by
  let F := highPacketObservable a b m r D q C c G Φ
  have hw := highPacketMarkWeight_integrable σ a b m r D q C A hA hcost
  have hmF : Measurable F := measurable_from_prod_countable_left fun h => by
    dsimp [F, highPacketObservable]; exact (hG _ _).mul_const _
  have hb (e : Z × HighPacketMarkIndex ι m r D q) : ‖F e‖ ≤ L * M := by
    dsimp only [F, highPacketObservable]; rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hGbound e.1 e.2.1) (hΦ e.2.2) (abs_nonneg _) hL
  rw [highPacketSignedMeasure, signedDensity_integral _ _ hw
      (highPacketMarkWeight_measurable a b m r D q C A hA) F hmF (L * M) hb,
    integral_prod _ (hw.mul_bdd hmF.aestronglyMeasurable (Eventually.of_forall hb))]
  simp only [integral_count, F, highPacketObservable_finite_action, highSeparatedPacketAction]

theorem highResponseMark_variation (q : ℕ) (C : ℝ) (A : ι → ι → ℝ) :
    (∑ h : HighResponseMarkIndex ι q, |highResponseMarkWeight C q A h|) =
      (∑ h : Fin (2 * q + 2), |responseWeight q h|) * (2 * C ^ 2 * ∑ i, ∑ j, |A i j|) := by
  simp only [highResponseMarkWeight, Fintype.sum_prod_type, abs_mul]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]; rw [covariance_weight_variation]

theorem highPacketSignedMeasure_totalVariation (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable fun ζ => A ζ i j) (hcost : Integrable (separatedMatrixCost A) σ) :
    ((highPacketSignedMeasure σ a b m r D q C A).variation univ).toReal =
      (∑ h : HighDensityMarkIndex m r D, |densityPacketWeight a b m r D h|) *
        (∑ h : Fin (2 * q + 2), |responseWeight q h|) * (2 * C ^ 2) *
          ∫ ζ, separatedMatrixCost A ζ ∂σ := by
  have hw := highPacketMarkWeight_integrable σ a b m r D q C A hA hcost
  rw [highPacketSignedMeasure, Measure.variation_withDensityᵥ hw,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← integral_norm_eq_lintegral_enorm hw.aestronglyMeasurable, integral_prod _ hw.norm]
  have hvar (ζ : Z) : (∑ h : HighPacketMarkIndex ι m r D q, |highPacketMarkWeight a b m r D q C A (ζ, h)|) =
      (∑ h : HighDensityMarkIndex m r D, |densityPacketWeight a b m r D h|) *
        (∑ h : Fin (2 * q + 2), |responseWeight q h|) * (2 * C ^ 2) * separatedMatrixCost A ζ := by
    rw [Fintype.sum_prod_type]; simp only [highPacketMarkWeight, abs_mul]
    simp_rw [← Finset.mul_sum, highResponseMark_variation]; rw [← Finset.sum_mul]
    unfold separatedMatrixCost; ring
  simp only [integral_count, Real.norm_eq_abs, hvar]; rw [integral_const_mul]

theorem densityPacketWeight_exponential_cost (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r D : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) :
    (∑ h : HighDensityMarkIndex m r D, |densityPacketWeight a b m r D h|) ≤
      (Real.exp (1 + exteriorTau ((a + b) / (b - a))) * |b / densityMargin a b 0|) ^ r *
        (D : ℝ) ^ r * Real.exp ((m : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  rw [densityPacketWeight_variation a b ha hab m r D hr]
  have hp : |densityPacketPrefactor a b r| ≤ Real.exp (r : ℝ) * |b / densityMargin a b 0| ^ r := by
    unfold densityPacketPrefactor
    rw [abs_mul, abs_pow, abs_of_nonneg (by positivity : 0 ≤ (r : ℝ) ^ r / (r.factorial : ℝ))]
    exact mul_le_mul_of_nonneg_right (Real.pow_div_factorial_le_exp (r : ℝ) (Nat.cast_nonneg r) r) (by positivity)
  have he : Real.cosh ((m + r : ℕ) * exteriorTau ((a + b) / (b - a))) ≤
      Real.exp ((m + r : ℕ) * exteriorTau ((a + b) / (b - a))) := by
    rw [← exterior_rule_variation a b ha hab (m + r) (by omega)]
    exact exterior_rule_variation_le_exp a b ha hab (m + r) (by omega)
  refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (derivative_rule_variation D hD).2 r)
    (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le)).trans
    ((mul_le_mul_of_nonneg_right (mul_le_mul hp he (Real.cosh_pos _).le (by positivity)) (by positivity)).trans_eq ?_)
  rw [mul_pow, ← Real.exp_nat_mul]
  rw [show Real.exp (r : ℝ) * |b / densityMargin a b 0| ^ r *
      Real.exp ((m + r : ℕ) * exteriorTau ((a + b) / (b - a))) * (D : ℝ) ^ r =
    (Real.exp (r : ℝ) * Real.exp ((m + r : ℕ) * exteriorTau ((a + b) / (b - a)))) *
      |b / densityMargin a b 0| ^ r * (D : ℝ) ^ r by ring,
    ← Real.exp_add, show (r : ℝ) + (m + r : ℕ) * exteriorTau ((a + b) / (b - a)) =
      (r : ℝ) * (1 + exteriorTau ((a + b) / (b - a))) + (m : ℝ) * exteriorTau ((a + b) / (b - a)) by push_cast; ring,
    Real.exp_add]
  ring

theorem highPacketSignedMeasure_exponential_cost (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (m r D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (C : ℝ) (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable fun ζ => A ζ i j)
    (hcost : Integrable (separatedMatrixCost A) σ) :
    ((highPacketSignedMeasure σ a b m r D q C A).variation univ).toReal ≤
      ((Real.exp (1 + exteriorTau ((a + b) / (b - a))) * |b / densityMargin a b 0|) ^ r *
        (D : ℝ) ^ r * Real.exp ((m : ℝ) * exteriorTau ((a + b) / (b - a)))) *
          (∑ h : Fin (2 * q + 2), |responseWeight q h|) * (2 * C ^ 2) *
            ∫ ζ, separatedMatrixCost A ζ ∂σ := by
  rw [highPacketSignedMeasure_totalVariation σ a b m r D q C A hA hcost]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (densityPacketWeight_exponential_cost a b ha hab m r D hr hD)
        (Finset.sum_nonneg fun _ _ => abs_nonneg _))
      (by positivity))
    (integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem highPacketSignedMeasure_zero_mass (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable fun ζ => A ζ i j) (hcost : Integrable (separatedMatrixCost A) σ) :
    highPacketSignedMeasure σ a b m r D q C A univ = 0 := by
  have hw := highPacketMarkWeight_integrable σ a b m r D q C A hA hcost
  rw [highPacketSignedMeasure, withDensityᵥ_apply hw MeasurableSet.univ, Measure.restrict_univ, integral_prod _ hw]
  simp only [integral_count]
  have hz (ζ : Z) : (∑ h : HighPacketMarkIndex ι m r D q, highPacketMarkWeight a b m r D q C A (ζ, h)) = 0 := by
    have h := highPacketObservable_finite_action a b m r D q C A (fun _ => 0) (fun _ _ _ => 1) (fun _ => 1) ζ
    simpa only [highPacketObservable, mul_one, mul_zero, responseMatrixAction_zero_mass,
      densityPacketAction, densityDerivativeAction, Finset.sum_const_zero] using h
  simp only [hz, integral_zero]

end Packet
end SeparatedRowsAndPacket
end DensityUpdatesAndPackets

-- ============================================================================
-- 2. Smooth Windows, Periodized Polynomial Frame, and History Append/Deletion
-- ============================================================================

section SmoothWindowsAndFrame
open scoped ContDiff
open RoughRegime.ComplexDerivativeBridge
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem high_raw_mass_lower {d : ℕ} (C : ModelConstants d) (M cm m : ℝ)
    (hM : 2 ≤ M) (hcm : 0 ≤ cm) (hcmU : cm ≤ 1 / C.densityUpper)
    (hm : |m - 1| ≤ cm / M) : 1 / 2 ≤ m := by
  have hU : 0 < C.densityUpper := lt_trans zero_lt_one C.one_lt_densityUpper
  have hcm1 : cm ≤ 1 := hcmU.trans ((div_le_one hU).mpr C.one_lt_densityUpper.le)
  have hhalf : cm / M ≤ 1 / 2 := (div_le_iff₀ (by linarith)).mpr (by nlinarith)
  linarith [(abs_le.mp hm).1]

def highRawDensityMass {d : ℕ} (p : Covariate d → ℝ) : ℝ := ∫ x, p x ∂cubeVolume d

def highNormalizedDensity {d : ℕ} (p : Covariate d → ℝ) (x : Covariate d) : ℝ :=
  p x / highRawDensityMass p

theorem highNormalizedDensity_measurable {d : ℕ} (p : Covariate d → ℝ) (hp : Measurable p) :
    Measurable (highNormalizedDensity p) := hp.div_const _

theorem highRawDensity_integrable {d : ℕ} (C : ModelConstants d) (M : ℝ) (hM : 0 < M)
    (p : Covariate d → ℝ) (hp : Measurable p)
    (hb : ∀ᵐ x ∂cubeVolume d, C.densityLower + 1 / M ≤ p x ∧ p x ≤ C.densityUpper - 1 / M) :
    Integrable p (cubeVolume d) := by
  let _ : IsFiniteMeasure (cubeVolume d) := ⟨by rw [cubeVolume_univ]; exact ENNReal.one_lt_top⟩
  refine (integrable_const C.densityUpper).mono' hp.aestronglyMeasurable ?_
  filter_upwards [hb] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [C.densityLower_pos, one_div_pos.mpr hM])]
  linarith [one_div_pos.mpr hM]

theorem highNormalizedDensity_normalized {d : ℕ} (p : Covariate d → ℝ)
    (hp : Integrable p (cubeVolume d)) (hp0 : 0 ≤ᵐ[cubeVolume d] p)
    (hm : 0 < highRawDensityMass p) :
    (∫⁻ x, ENNReal.ofReal (highNormalizedDensity p x) ∂cubeVolume d) = 1 := by
  unfold highNormalizedDensity
  rw [← ofReal_integral_eq_lintegral_ofReal (hp.div_const _) (hp0.mono fun _ hx => div_nonneg hx hm.le),
    integral_div]
  change ENNReal.ofReal (highRawDensityMass p / highRawDensityMass p) = 1
  simp only [div_self hm.ne', ENNReal.ofReal_one]

theorem highNormalizedDensity_bounds {d : ℕ} (C : ModelConstants d) (M cm : ℝ)
    (hM : 2 ≤ M) (hcm : 0 ≤ cm) (hcmU : cm ≤ 1 / C.densityUpper) (p : Covariate d → ℝ)
    (hb : ∀ᵐ x ∂cubeVolume d, C.densityLower + 1 / M ≤ p x ∧ p x ≤ C.densityUpper - 1 / M)
    (hm : |highRawDensityMass p - 1| ≤ cm / M) :
    ∀ᵐ x ∂cubeVolume d, C.densityLower ≤ highNormalizedDensity p x ∧ highNormalizedDensity p x ≤ C.densityUpper := by
  have hU : 0 < C.densityUpper := lt_trans zero_lt_one C.one_lt_densityUpper
  have hM0 : 0 < M := by linarith
  have hm0 : 0 < highRawDensityMass p :=
    lt_of_lt_of_le (by norm_num) (high_raw_mass_lower C M cm _ hM hcm hcmU hm)
  have hcmprod : C.densityUpper * cm ≤ 1 := by linarith [(le_div_iff₀ hU).mp hcmU]
  have hLcm : C.densityLower * cm ≤ 1 :=
    (mul_le_mul_of_nonneg_right (C.densityLower_lt_one.le.trans C.one_lt_densityUpper.le) hcm).trans hcmprod
  have hmass := abs_le.mp hm
  have hmulU : C.densityUpper * (cm / M) ≤ 1 / M := by
    simpa only [mul_div_assoc, one_div] using div_le_div_of_nonneg_right hcmprod hM0.le
  have hmulL : C.densityLower * (cm / M) ≤ 1 / M := by
    simpa only [mul_div_assoc, one_div] using div_le_div_of_nonneg_right hLcm hM0.le
  filter_upwards [hb] with x hx
  exact ⟨(le_div_iff₀ hm0).mpr (by nlinarith [mul_le_mul_of_nonneg_left hmass.2 C.densityLower_pos.le]),
    (div_le_iff₀ hm0).mpr (by nlinarith [mul_le_mul_of_nonneg_left hmass.1 hU.le])⟩

def normalizedDensityTernaryParameter {d : ℕ} (p F : Covariate d → ℝ)
    (a V : ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) : RegressionParameter d where
  density := highNormalizedDensity p
  regression := F
  variance := V
  errors := ternaryErrorKernel a V F hF
  errors_markov := ternaryErrorKernel_markov a V F hF ha hp

private def boundedMultiIndexMultiset (d ℓ : ℕ) (γ : Fin d → Fin (ℓ + 1)) : Multiset (Fin (d + 1)) :=
  (∑ r, Multiset.replicate (γ r).val r.castSucc) +
    Multiset.replicate (ℓ - ∑ r, (γ r).val) (Fin.last d)

theorem holderNorm_of_global_mixed_bounds_binomial {d : ℕ} (U : Set (Covariate d))
    (F : Covariate d → ℝ) (ℓ : ℕ) (α B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hsup : ∀ γ : Fin d → Fin (ℓ + 1), (∑ i, (γ i).val) ≤ ℓ →
      ∀ x, |multiPartial F (fun i => (γ i).val) x| ≤ B)
    (hmod : ∀ γ : Fin d → Fin (ℓ + 1), (∑ i, (γ i).val) = ℓ → ∀ x y,
      |multiPartial F (fun i => (γ i).val) x - multiPartial F (fun i => (γ i).val) y| ≤
        L * euclideanNorm (x - y) ^ α) :
    holderNorm U F ℓ α ≤ ENNReal.ofReal (((d + ℓ).choose d : ℝ) * B + L) := by
  let A := Finset.univ.filter fun γ : Fin d → Fin (ℓ + 1) => (∑ i, (γ i).val) ≤ ℓ
  have hcnt : A.card ≤ (d + ℓ).choose d := by
    let encode : A → Sym (Fin (d + 1)) ℓ := fun γ =>
      ⟨boundedMultiIndexMultiset d ℓ γ, by
        simp only [boundedMultiIndexMultiset, Multiset.card_add, Multiset.card_sum, Multiset.card_replicate]
        have := (Finset.mem_filter.mp γ.property).2; omega⟩
    have hinj : Function.Injective encode := fun γ δ he => Subtype.ext <| funext fun r => Fin.ext <| by
      have hm := congrArg (fun s : Sym (Fin (d + 1)) ℓ => s.val.count r.castSucc) he
      have hc (β : Fin d → Fin (ℓ + 1)) : (boundedMultiIndexMultiset d ℓ β).count r.castSucc = (β r).val := by
        simp only [boundedMultiIndexMultiset, Multiset.count_add, Multiset.count_sum', Multiset.count_replicate]
        have hlast : Fin.last d ≠ r.castSucc := fun h => by
          have hv := congrArg Fin.val h; simp only [Fin.val_last, Fin.val_castSucc] at hv; omega
        simp only [hlast, ite_false, add_zero, Fin.castSucc_inj]
        simpa only [Finset.mem_univ, ite_true] using Finset.sum_ite_eq' Finset.univ r fun i => (β i).val
      simpa only [encode, hc] using hm
    have hc := Fintype.card_le_of_injective encode hinj
    rw [Fintype.card_coe, Sym.card_sym_eq_choose, Fintype.card_fin,
      show d + 1 + ℓ - 1 = d + ℓ by omega, ← Nat.choose_symm (by omega : ℓ ≤ d + ℓ)] at hc
    simpa only [A, show d + ℓ - ℓ = d by omega] using hc
  have hsum : (∑ γ : Fin d → Fin (ℓ + 1),
      if (∑ i, (γ i).val) ≤ ℓ then derivativeSup U (multiPartial F fun i => (γ i).val) else 0) ≤
      ENNReal.ofReal (((d + ℓ).choose d : ℝ) * B) := by
    calc
      _ = ∑ γ ∈ A, derivativeSup U (multiPartial F fun i => (γ i).val) := by
        dsimp only [A]; rw [Finset.sum_filter]
      _ ≤ ∑ _γ ∈ A, ENNReal.ofReal B :=
        Finset.sum_le_sum fun γ hγ => iSup_le fun x => ENNReal.ofReal_le_ofReal (hsup γ (Finset.mem_filter.mp hγ).2 x)
      _ = ENNReal.ofReal ((A.card : ℝ) * B) := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => hB, Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by exact_mod_cast hcnt) hB)
  have hsem : (⨆ γ : Fin d → Fin (ℓ + 1), if (∑ i, (γ i).val) = ℓ then
      holderSeminorm U (multiPartial F fun i => (γ i).val) α else 0) ≤ ENNReal.ofReal L :=
    iSup_le fun γ => by
      split_ifs with h
      · refine iSup_le fun x => iSup_le fun y => ?_
        by_cases hxy : (x : Covariate d) = y
        · simp [hxy]
        · simp only [ite_eq_right_iff.mpr fun h' => False.elim (hxy h')]
          exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ (Real.rpow_pos_of_pos
            (euclideanNorm_pos_of_ne_zero (x.val - y.val) (sub_ne_zero.mpr hxy)) α)).mpr (hmod γ h x y))
      · exact bot_le
  unfold holderNorm
  rw [ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) hB) hL]
  exact add_le_add hsum hsem

-- Smooth compact normalized lattice windows

def highWindowBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 3 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def highWindowSeed : ℝ → ℝ := highWindowBump

private lemma integerTranslate_locallyFinite (g : ℝ → ℝ) (hg : ∀ x, 1 ≤ |x| → g x = 0) :
    LocallyFinite fun j : ℤ => support fun x : ℝ => g (x - j) := fun x =>
  ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith),
    (finite_Icc (⌊x⌋ - 3) (⌊x⌋ + 3)).subset fun j ⟨y, hy, hnear⟩ => by
      have hd := abs_lt.mp (by by_contra h; exact hy (hg _ (not_lt.mp h)) : |y - j| < 1)
      have hf := Int.floor_le x; have hc := Int.lt_floor_add_one x
      exact ⟨(Int.cast_le (R := ℝ)).mp (by push_cast; linarith [hnear.1, hnear.2]),
        (Int.cast_le (R := ℝ)).mp (by push_cast; linarith [hnear.1, hnear.2])⟩⟩

def highWindowEnergy (x : ℝ) : ℝ := ∑ᶠ j : ℤ, highWindowSeed (x - j) ^ 2

private lemma highWindowEnergy_props :
    LocallyFinite (fun j : ℤ => support fun x : ℝ => highWindowSeed (x - j) ^ 2) ∧
      ContDiff ℝ ∞ highWindowEnergy ∧ (∀ x, 0 < highWindowEnergy x) ∧
      ∀ x (k : ℤ), highWindowEnergy (x + k) = highWindowEnergy x := by
  have hseed0 (x : ℝ) (hx : 3 / 4 ≤ |x|) : highWindowSeed x = 0 :=
    highWindowBump.zero_of_le_dist (by simpa [Real.dist_eq, highWindowBump] using hx)
  have hlf : LocallyFinite fun j : ℤ => support fun x : ℝ => highWindowSeed (x - j) ^ 2 :=
    integerTranslate_locallyFinite (fun x => highWindowSeed x ^ 2) fun x hx => by
      rw [hseed0 x (by linarith)]; norm_num
  have hcd : ContDiff ℝ ∞ highWindowEnergy := by
    unfold highWindowEnergy
    apply ContMDiff.contDiff
    apply contMDiff_finsum _ hlf
    intro j
    apply ContDiff.contMDiff
    exact ((highWindowBump.contDiff : ContDiff ℝ ∞ highWindowSeed).comp (contDiff_id.sub contDiff_const)).pow 2
  have hpos (x : ℝ) : 0 < highWindowEnergy x := by
    let j : ℤ := ⌊x + 1 / 2⌋
    have hj0 := Int.floor_le (x + 1 / 2)
    have hj1 := Int.lt_floor_add_one (x + 1 / 2)
    have hone : highWindowSeed (x - j) = 1 := highWindowBump.one_of_mem_closedBall <| by
      simpa [Metric.mem_closedBall, Real.dist_eq, highWindowBump] using
        (abs_le.mpr ⟨by dsimp [j]; linarith, by dsimp [j]; linarith⟩ : |x - j| ≤ 1 / 2)
    have hle := single_le_finsum j (hlf.point_finite x) fun z : ℤ => sq_nonneg (highWindowSeed (x - z))
    exact lt_of_lt_of_le zero_lt_one (by simpa [highWindowEnergy, hone] using hle)
  refine ⟨hlf, hcd, hpos, fun x k => ?_⟩
  unfold highWindowEnergy
  exact (finsum_congr fun j => by congr 2; push_cast; ring).trans
    (finsum_comp (g := fun j : ℤ => highWindowSeed (x - j) ^ 2) (fun j : ℤ => j - k)
      ⟨fun i j h => by change i - k = j - k at h; simpa only [sub_left_inj] using h,
       fun j => ⟨j + k, by dsimp; ring⟩⟩)

def highWindowProfile (x : ℝ) : ℝ := highWindowSeed x / Real.sqrt (highWindowEnergy x)

private lemma highWindowProfile_contDiff : ContDiff ℝ ∞ highWindowProfile :=
  highWindowBump.contDiff.div
    (highWindowEnergy_props.2.1.sqrt fun x => (highWindowEnergy_props.2.2.1 x).ne')
    fun x => (Real.sqrt_pos.mpr (highWindowEnergy_props.2.2.1 x)).ne'

private lemma highWindowProfile_nonneg (x : ℝ) : 0 ≤ highWindowProfile x :=
  div_nonneg highWindowBump.nonneg (Real.sqrt_nonneg _)

theorem highWindowProfile_eq_zero (x : ℝ) (hx : 3 / 4 ≤ |x|) : highWindowProfile x = 0 := by
  have hs : highWindowSeed x = 0 := highWindowBump.zero_of_le_dist (by simpa [Real.dist_eq, highWindowBump] using hx)
  simp [highWindowProfile, hs]

def highWindowTensor (d : ℕ) (x : Covariate d) : ℝ := ∏ i, highWindowProfile (x i)

private lemma highWindowTensor_contDiff (d : ℕ) : ContDiff ℝ ∞ (highWindowTensor d) :=
  contDiff_prod fun i _ => highWindowProfile_contDiff.comp (contDiff_apply ℝ ℝ i)

private lemma highWindowTensor_support_bound {d : ℕ} {x : Covariate d}
    (hx : highWindowTensor d x ≠ 0) (i : Fin d) : |x i| < 3 / 4 := by
  by_contra hi; exact hx (Finset.prod_eq_zero (Finset.mem_univ i) (highWindowProfile_eq_zero _ (not_lt.mp hi)))

private lemma highWindowTensor_tsupport_bound {d : ℕ} {x : Covariate d}
    (hx : x ∈ tsupport (highWindowTensor d)) : ∀ i, |x i| ≤ 3 / 4 := by
  have hsub : tsupport (highWindowTensor d) ⊆ Metric.closedBall (0 : Covariate d) (3 / 4 : ℝ) :=
    closure_minimal (fun y hy => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i =>
        by simpa only [Real.norm_eq_abs] using (highWindowTensor_support_bound hy i).le)
      Metric.isClosed_closedBall
  have hn := hsub hx
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)] at hn
  simpa only [Real.norm_eq_abs] using hn

def highPeriodicWindow (k : ℕ) (j : ZMod k) (x : ℝ) : ℝ :=
  ∑ᶠ z : ℤ, if (z : ZMod k) = j then highWindowProfile ((k : ℝ) * x - z) else 0

private lemma highPeriodicWindow_locallyFinite (k : ℕ) (j : ZMod k) :
    LocallyFinite fun z : ℤ => support fun x : ℝ =>
      if (z : ZMod k) = j then highWindowProfile ((k : ℝ) * x - z) else 0 :=
  ((integerTranslate_locallyFinite highWindowProfile fun x hx =>
      highWindowProfile_eq_zero x (by linarith)).preimage_continuous
    (continuous_const.mul continuous_id)).subset fun z x hx => by
      by_cases hz : (z : ZMod k) = j <;> [simpa [hz] using hx; simp [hz] at hx]

private lemma highPeriodicWindow_support_subsingleton (k : ℕ) (hk : 2 ≤ k) (j : ZMod k) (x : ℝ) :
    (support fun z : ℤ => if (z : ZMod k) = j then highWindowProfile ((k : ℝ) * x - z) else 0).Subsingleton := by
  intro z hz q hq
  have hzj : (z : ZMod k) = j := by by_contra h; exact hz (by simp [h])
  have hqj : (q : ZMod k) = j := by by_contra h; exact hq (by simp [h])
  have hzd : |(k : ℝ) * x - z| < 3 / 4 := by by_contra h; exact hz (by simp [highWindowProfile_eq_zero _ (not_lt.mp h)])
  have hqd : |(k : ℝ) * x - q| < 3 / 4 := by by_contra h; exact hq (by simp [highWindowProfile_eq_zero _ (not_lt.mp h)])
  obtain ⟨l, hl⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub z q k).mp (hzj.trans hqj.symm)
  have h1 := abs_lt.mp hzd
  have h2 := abs_lt.mp hqd
  have hdiff : |(q : ℝ) - z| < 3 / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hdiffZ : |q - z| < (2 : ℤ) := (Int.cast_lt (R := ℝ)).mp (by push_cast; linarith)
  have hkZ : (2 : ℤ) ≤ k := by exact_mod_cast hk
  have hl0 : l = 0 := by
    by_contra h
    have habsl : (1 : ℤ) ≤ |l| := by have := abs_pos.mpr h; omega
    have hm : (2 : ℤ) ≤ |(k : ℤ) * l| := by rw [abs_mul, abs_of_nonneg (by omega)]; nlinarith
    rw [← hl] at hm; omega
  simp only [hl0, mul_zero] at hl; omega

private lemma highPeriodicWindow_sq_partition (k : ℕ) [NeZero k] (hk : 2 ≤ k) (x : ℝ) :
    (∑ j : ZMod k, highPeriodicWindow k j x ^ 2) = 1 := by
  have hfsq (f : ℤ → ℝ) (hs : (support f).Subsingleton) : (∑ᶠ z, f z) ^ 2 = ∑ᶠ z, f z ^ 2 := by
    by_cases hn : ∃ z, f z ≠ 0
    · obtain ⟨z, hz⟩ := hn
      have h0 : ∀ q, q ≠ z → f q = 0 := fun q hq => by by_contra h; exact hq (hs h hz)
      rw [finsum_eq_single f z h0, finsum_eq_single (fun q => f q ^ 2) z fun q hq => by rw [h0 q hq]; norm_num]
    · have h0 : ∀ z, f z = 0 := by simpa using hn
      simp only [h0, zero_pow (by decide : (2 : ℕ) ≠ 0), finsum_zero]
  simp_rw [show ∀ j : ZMod k, highPeriodicWindow k j x ^ 2 =
    ∑ᶠ z : ℤ, if (z : ZMod k) = j then highWindowProfile ((k : ℝ) * x - z) ^ 2 else 0 from fun j => by
      rw [highPeriodicWindow, hfsq _ (highPeriodicWindow_support_subsingleton k hk j x)]
      exact finsum_congr fun _ => by split_ifs <;> simp]
  rw [sum_finsum_comm]
  · simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hE := (highWindowEnergy_props.2.2.1 ((k : ℝ) * x)).ne'
    calc
      (∑ᶠ j : ℤ, highWindowProfile ((k : ℝ) * x - j) ^ 2) =
        ∑ᶠ j : ℤ, highWindowSeed ((k : ℝ) * x - j) ^ 2 * (highWindowEnergy ((k : ℝ) * x))⁻¹ :=
          finsum_congr fun j => by
            have hp : highWindowEnergy ((k : ℝ) * x - j) = highWindowEnergy ((k : ℝ) * x) := by
              simpa [sub_eq_add_neg] using highWindowEnergy_props.2.2.2 ((k : ℝ) * x) (-j)
            rw [highWindowProfile, div_pow, hp, Real.sq_sqrt (highWindowEnergy_props.2.2.1 _).le]; rfl
      _ = highWindowEnergy ((k : ℝ) * x) * (highWindowEnergy ((k : ℝ) * x))⁻¹ :=
        (finsum_mul (fun j : ℤ => highWindowSeed ((k : ℝ) * x - j) ^ 2) _).symm
      _ = 1 := mul_inv_cancel₀ hE
  · intro j _
    refine ((highPeriodicWindow_locallyFinite k j).point_finite x).subset fun z hz => ?_
    change (if (z : ZMod k) = j then highWindowProfile ((k : ℝ) * x - z) else 0) ≠ 0
    change (if (z : ZMod k) = j then highWindowProfile ((k : ℝ) * x - z) ^ 2 else 0) ≠ 0 at hz
    by_cases hzj : (z : ZMod k) = j
    · simp only [ite_eq_left hzj] at hz ⊢; exact fun h => hz (by rw [h]; norm_num)
    · exact False.elim (hz (by simp [hzj]))

abbrev HighWindowLabels (d k : ℕ) := Fin d → ZMod k

def highPeriodicTensor (d k : ℕ) (j : HighWindowLabels d k) (x : Covariate d) : ℝ :=
  ∏ i, highPeriodicWindow k (j i) (x i)

theorem highPeriodicTensor_contDiff (d k : ℕ) (j : HighWindowLabels d k) :
    ContDiff ℝ ∞ (highPeriodicTensor d k j) :=
  contDiff_prod fun i _ => by
    have hw : ContDiff ℝ ∞ (highPeriodicWindow k (j i)) := by
      unfold highPeriodicWindow
      apply ContMDiff.contDiff
      apply contMDiff_finsum _ (highPeriodicWindow_locallyFinite k (j i))
      intro z
      apply ContDiff.contMDiff
      by_cases hz : (z : ZMod k) = j i
      · simp only [if_pos hz]; exact highWindowProfile_contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
      · simp only [if_neg hz]; exact contDiff_const
    exact hw.comp (contDiff_apply ℝ ℝ i)

theorem highPeriodicTensor_nonneg (d k : ℕ) (j : HighWindowLabels d k) (x : Covariate d) :
    0 ≤ highPeriodicTensor d k j x :=
  Finset.prod_nonneg fun _ _ => finsum_nonneg fun _ => by split_ifs <;> [exact highWindowProfile_nonneg _; exact le_rfl]

theorem highPeriodicTensor_le_one (d k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (j : HighWindowLabels d k) (x : Covariate d) : highPeriodicTensor d k j x ≤ 1 :=
  Finset.prod_le_one₀
    (fun _ _ => finsum_nonneg fun _ => by split_ifs <;> [exact highWindowProfile_nonneg _; exact le_rfl])
    fun i _ => by
      have hnn : 0 ≤ highPeriodicWindow k (j i) (x i) :=
        finsum_nonneg fun _ => by split_ifs <;> [exact highWindowProfile_nonneg _; exact le_rfl]
      have hsq : highPeriodicWindow k (j i) (x i) ^ 2 ≤ 1 := by
        rw [← highPeriodicWindow_sq_partition k hk (x i)]
        exact Finset.single_le_sum (fun z _ => sq_nonneg (highPeriodicWindow k z (x i))) (Finset.mem_univ (j i))
      nlinarith

theorem highPeriodicTensor_sq_partition (d k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (x : Covariate d) : (∑ j : HighWindowLabels d k, highPeriodicTensor d k j x ^ 2) = 1 := by
  simp only [highPeriodicTensor, ← Finset.prod_pow]
  rw [← Fintype.prod_sum fun i (j : ZMod k) => highPeriodicWindow k j (x i) ^ 2]
  simp only [highPeriodicWindow_sq_partition k hk, Finset.prod_const_one]

theorem highPeriodicTensor_support_lift (d k : ℕ) (j : HighWindowLabels d k)
    (x : Covariate d) (hx : highPeriodicTensor d k j x ≠ 0) :
    ∃ z : Fin d → ℤ, (∀ i, (z i : ZMod k) = j i) ∧ ∀ i, |(k : ℝ) * x i - z i| < 3 / 4 := by
  have h1 (i : Fin d) : ∃ z : ℤ, (z : ZMod k) = j i ∧ |(k : ℝ) * x i - z| < 3 / 4 := by
    have hne : highPeriodicWindow k (j i) (x i) ≠ 0 := fun h => hx (Finset.prod_eq_zero (Finset.mem_univ i) h)
    obtain ⟨w, hw⟩ : ∃ w : ℤ, (if (w : ZMod k) = j i then highWindowProfile ((k : ℝ) * x i - w) else 0) ≠ 0 := by
      by_contra h; push Not at h; exact hne (by simp only [highPeriodicWindow, h, finsum_zero])
    exact ⟨w, by by_contra h; exact hw (by simp [h]),
      by by_contra h; exact hw (by simp [highWindowProfile_eq_zero _ (not_lt.mp h)])⟩
  choose z hz using h1
  exact ⟨z, fun i => (hz i).1, fun i => (hz i).2⟩

private lemma highPeriodicWindow_eventuallyEq_single (k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : ZMod k) (x : ℝ) :
    ∃ z : ℤ, (z : ZMod k) = j ∧ highPeriodicWindow k j =ᶠ[𝓝 x]
      fun y => highWindowProfile ((k : ℝ) * y - z) := by
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  let l : ℤ := ⌊x - (j.val : ℝ) / k + 1 / 2⌋
  let z : ℤ := (j.val : ℤ) + (k : ℤ) * l
  have hzj : (z : ZMod k) = j := by simp [z, ZMod.natCast_zmod_val]
  have hdiv : (k : ℝ) * ((j.val : ℝ) / k) = j.val := by field_simp
  have hclose : |(k : ℝ) * x - z| ≤ (k : ℝ) / 2 := by
    dsimp [z]; push_cast; apply abs_le.mpr; dsimp [l]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left (Int.floor_le (x - (j.val : ℝ) / k + 1 / 2)) hk0.le,
      mul_lt_mul_of_pos_left (Int.lt_floor_add_one (x - (j.val : ℝ) / k + 1 / 2)) hk0]
  refine ⟨z, hzj, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x (by positivity : 0 < 1 / (4 * (k : ℝ)))] with y hy
  have hxy : |(k : ℝ) * y - (k : ℝ) * x| < 1 / 4 := by
    have hdist : |y - x| < 1 / (4 * (k : ℝ)) := by simpa only [Metric.mem_ball, Real.dist_eq] using hy
    rw [← mul_sub, abs_mul, abs_of_pos hk0]
    simpa only [show (k : ℝ) * (1 / (4 * (k : ℝ))) = 1 / 4 by field_simp] using mul_lt_mul_of_pos_left hdist hk0
  rw [highPeriodicWindow, finsum_eq_single _ z]
  · simp only [hzj, ite_true]
  · intro q hq
    by_cases hqj : (q : ZMod k) = j
    · simp only [hqj, ite_true]; apply highWindowProfile_eq_zero
      by_contra hdist
      have hqclose : |(k : ℝ) * y - q| < 3 / 4 := not_le.mp hdist
      obtain ⟨b, hb⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub z q k).mp (hzj.trans hqj.symm)
      have hb0 : b ≠ 0 := fun hb0 => by simp only [hb0, mul_zero] at hb; exact hq (by omega)
      have habs : (1 : ℤ) ≤ |b| := by have := abs_pos.mpr hb0; omega
      have hsep : (k : ℝ) ≤ |(q : ℝ) - z| := by
        exact_mod_cast (by rw [hb, abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ k)]; nlinarith : (k : ℤ) ≤ |q - z|)
      have htri : |(q : ℝ) - z| ≤ |(k : ℝ) * y - q| + |(k : ℝ) * y - (k : ℝ) * x| + |(k : ℝ) * x - z| := by
        calc
          _ = |(q - (k : ℝ) * y) + ((k : ℝ) * y - (k : ℝ) * x) + ((k : ℝ) * x - z)| := by congr 1; ring
          _ ≤ |(q - (k : ℝ) * y) + ((k : ℝ) * y - (k : ℝ) * x)| + |(k : ℝ) * x - z| := abs_add_le _ _
          _ ≤ |q - (k : ℝ) * y| + |(k : ℝ) * y - (k : ℝ) * x| + |(k : ℝ) * x - z| := by gcongr; exact abs_add_le _ _
          _ = _ := by rw [abs_sub_comm (q : ℝ) ((k : ℝ) * y)]
      linarith
    · simp only [hqj, ite_false]

-- High field regularity, polynomial frame, and periodized chart

private lemma mixed_bounds_of_scaled_derivatives {d : ℕ} (C : ModelConstants d)
    (F : Covariate d → ℝ) (hF : ContDiff ℝ ∞ F) (k A : ℝ) (hk : 1 ≤ k) (hA : 0 ≤ A)
    (hbound : ∀ q ≤ C.order + 1, ∀ x, ‖iteratedFDeriv ℝ q F x‖ ≤ A * k ^ ((q : ℝ) - C.smoothness)) :
    (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) ≤ C.order → ∀ x,
      |multiPartial F (fun r => (γ r).val) x| ≤ A) ∧
    (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) = C.order → ∀ x y,
      |multiPartial F (fun r => (γ r).val) x - multiPartial F (fun r => (γ r).val) y| ≤
        (2 * A) * euclideanNorm (x - y) ^ C.alpha) := by
  have hkpos : 0 < k := lt_of_lt_of_le one_pos hk
  have hbnorm (γ : Fin d → ℕ) (j : Fin (∑ r, γ r)) : ‖multiIndexBasis γ j‖ = 1 := by
    simp [multiIndexBasis, wordBasis, Pi.norm_single]
  refine ⟨fun γ hγ x => ?_, fun γ hγ x y => ?_⟩
  · have hm : |multiPartial F (fun r => (γ r).val) x| ≤ ‖iteratedFDeriv ℝ (∑ r, (γ r).val) F x‖ := by
      rw [multiPartial_eq_iteratedFDeriv univ isOpen_univ F _ (hF.of_le (by simp)).contDiffOn _ le_rfl x (mem_univ x)]
      simpa only [Real.norm_eq_abs, hbnorm, Finset.prod_const_one, mul_one] using
        (iteratedFDeriv ℝ (∑ r, (γ r).val) F x).le_opNorm (multiIndexBasis _)
    refine hm.trans ((hbound _ (by omega) x).trans ?_)
    have hcast : ((∑ r, (γ r).val : ℕ) : ℝ) ≤ C.order := by exact_mod_cast hγ
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos hk (by linarith [C.order_lt])) hA
  · have hsup (z : Covariate d) : ‖iteratedFDeriv ℝ C.order F z‖ ≤ A * k ^ (-C.alpha) := by
      simpa only [show (C.order : ℝ) - C.smoothness = -C.alpha by unfold ModelConstants.alpha; ring] using
        hbound C.order (by omega) z
    have hnext (z : Covariate d) : ‖fderiv ℝ (iteratedFDeriv ℝ C.order F) z‖ ≤ A * k ^ (1 - C.alpha) := by
      rw [norm_fderiv_iteratedFDeriv]
      simpa only [show ((C.order + 1 : ℕ) : ℝ) - C.smoothness = 1 - C.alpha by
        unfold ModelConstants.alpha; push_cast; ring] using hbound (C.order + 1) le_rfl z
    have hlarge : ‖iteratedFDeriv ℝ C.order F x - iteratedFDeriv ℝ C.order F y‖ ≤ 2 * A * k ^ (-C.alpha) :=
      (norm_sub_le _ _).trans (by nlinarith [hsup x, hsup y])
    have hsmall : ‖iteratedFDeriv ℝ C.order F x - iteratedFDeriv ℝ C.order F y‖ ≤
        A * k ^ (1 - C.alpha) * ‖x - y‖ :=
      Convex.norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => (hF.of_le (by simp) : ContDiff ℝ (C.order + 1) F).contDiffAt.differentiableAt_iteratedFDeriv
          (by exact_mod_cast Nat.lt_succ_self C.order))
        (fun z _ => hnext z) convex_univ (mem_univ y) (mem_univ x)
    have hh : ‖iteratedFDeriv ℝ C.order F x - iteratedFDeriv ℝ C.order F y‖ ≤ 2 * A * ‖x - y‖ ^ C.alpha := by
      let r := ‖x - y‖
      have hr : 0 ≤ r := norm_nonneg _
      by_cases hr0 : r = 0
      · simpa only [r, hr0, mul_zero, Real.zero_rpow C.alpha_pos.ne'] using hsmall
      have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      by_cases hkr : k * r ≤ 1
      · have hp : (k * r) ^ (1 - C.alpha) ≤ 1 := Real.rpow_le_one (mul_nonneg hkpos.le hr) hkr (sub_nonneg.mpr C.alpha_le_one)
        have hid : k ^ (1 - C.alpha) * r = (k * r) ^ (1 - C.alpha) * r ^ C.alpha := by
          rw [Real.mul_rpow hkpos.le hr, mul_assoc, ← Real.rpow_add hrpos]; simp only [sub_add_cancel, Real.rpow_one]
        have hs1 : A * k ^ (1 - C.alpha) * r ≤ A * r ^ C.alpha := by
          rw [mul_assoc, hid, ← mul_assoc]
          exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hA) (Real.rpow_nonneg hr _)).trans_eq (by ring)
        exact (hsmall.trans hs1).trans (by nlinarith [mul_nonneg hA (Real.rpow_nonneg hr C.alpha)])
      · have hp : 1 ≤ (k * r) ^ C.alpha := Real.one_le_rpow (le_of_not_ge hkr) C.alpha_pos.le
        have hkinv : k ^ (-C.alpha) ≤ r ^ C.alpha := by
          rw [Real.rpow_neg hkpos.le, ← one_div]
          exact (div_le_iff₀ (Real.rpow_pos_of_pos hkpos C.alpha)).mpr
            (by simpa only [Real.mul_rpow hkpos.le hr, one_mul, mul_comm] using hp)
        exact hlarge.trans (mul_le_mul_of_nonneg_left hkinv (by positivity))
    have heval : |multiPartial F (fun r => (γ r).val) x - multiPartial F (fun r => (γ r).val) y| ≤
        ‖iteratedFDeriv ℝ (∑ r, (γ r).val) F x - iteratedFDeriv ℝ (∑ r, (γ r).val) F y‖ := by
      rw [multiPartial_eq_iteratedFDeriv univ isOpen_univ F _ (hF.of_le (by simp)).contDiffOn _ le_rfl x (mem_univ x),
        multiPartial_eq_iteratedFDeriv univ isOpen_univ F _ (hF.of_le (by simp)).contDiffOn _ le_rfl y (mem_univ y)]
      simpa only [ContinuousMultilinearMap.sub_apply, Real.norm_eq_abs, hbnorm, Finset.prod_const_one, mul_one] using
        (iteratedFDeriv ℝ (∑ r, (γ r).val) F x - iteratedFDeriv ℝ (∑ r, (γ r).val) F y).le_opNorm (multiIndexBasis _)
    rw [hγ] at heval
    exact (heval.trans hh).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _)
        ((pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun r =>
          by simpa only [Real.norm_eq_abs, euclideanNorm] using abs_coordinate_le_euclideanNorm (x - y) r)
        C.alpha_pos.le)
      (by positivity))

def frameCoefficientL1 {d : ℕ} (P : MvPolynomial (Fin d) ℝ) : ℝ :=
  ∑ β ∈ P.support, |P.coeff β|

theorem frameCoefficientL1_nonneg {d : ℕ} (P : MvPolynomial (Fin d) ℝ) :
    0 ≤ frameCoefficientL1 P := Finset.sum_nonneg fun _ _ => abs_nonneg _

def frameScaledPolynomial {d : ℕ} (P : MvPolynomial (Fin d) ℝ) : MvPolynomial (Fin d) ℝ :=
  MvPolynomial.bind₁ (fun r => MvPolynomial.C (1 / 8 : ℝ) * MvPolynomial.X r) P

theorem frameScaledPolynomial_eval {d : ℕ} (P : MvPolynomial (Fin d) ℝ) (x : Covariate d) :
    MvPolynomial.eval x (frameScaledPolynomial P) = MvPolynomial.eval (fun r => x r / 8) P := by
  change MvPolynomial.eval₂Hom (RingHom.id ℝ) x _ = MvPolynomial.eval₂Hom (RingHom.id ℝ) _ P
  rw [frameScaledPolynomial, MvPolynomial.eval₂Hom_bind₁]
  simp only [map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply]
  rw [show (fun r => (1 / 8 : ℝ) * x r) = fun r => x r / 8 from funext fun _ => by ring]

def highFrameProfile {d : ℕ} (P : MvPolynomial (Fin d) ℝ) (u : Covariate d) : ℝ :=
  highWindowTensor d u * MvPolynomial.eval u (frameScaledPolynomial P)

theorem highFrameProfile_contDiff {d : ℕ} (P : MvPolynomial (Fin d) ℝ) :
    ContDiff ℝ ∞ (highFrameProfile P) :=
  (highWindowTensor_contDiff d).mul
    ((RoughRegime.PolynomialDerivatives.polynomial_contDiff _).of_le le_top)

private lemma highFrameProfile_derivative_bound (d m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ P : MvPolynomial (Fin d) ℝ, ∀ q ≤ m, ∀ u : Covariate d,
      ‖iteratedFDeriv ℝ q (highFrameProfile P) u‖ ≤ K * frameCoefficientL1 P := by
  have hcs : HasCompactSupport (highWindowTensor d) :=
    (isCompact_closedBall (0 : Covariate d) (3 / 4 : ℝ)).of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal (fun x hx => by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i =>
          by simpa only [Real.norm_eq_abs] using (highWindowTensor_support_bound hx i).le)
        Metric.isClosed_closedBall)
  obtain ⟨B, _, hB⟩ := hcs.exists_bound_iteratedFDeriv (highWindowTensor_contDiff d) m
  let B' : ℝ := max B 1
  let Cp := (m.factorial : ℝ) * (Real.exp 1) ^ m
  let K := (2 : ℝ) ^ m * B' * Cp
  refine ⟨K, by dsimp [B', Cp, K]; positivity, fun P q hq u => ?_⟩
  have hcBnd (v : Covariate d) (hv : ‖v‖ ≤ 1) (z : Fin d → ℂ) (hz : ‖z - fun r => (v r : ℂ)‖ < 1) :
      ‖MvPolynomial.eval z (complexify (frameScaledPolynomial P))‖ ≤ frameCoefficientL1 P := by
    have hce : MvPolynomial.eval z (complexify (frameScaledPolynomial P)) =
        MvPolynomial.eval₂ Complex.ofRealHom (fun r => z r / 8) P := by
      rw [complexify, MvPolynomial.eval_map]
      change MvPolynomial.eval₂Hom Complex.ofRealHom z _ = MvPolynomial.eval₂Hom Complex.ofRealHom _ P
      rw [frameScaledPolynomial, MvPolynomial.eval₂Hom_bind₁]
      simp only [map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
      change MvPolynomial.eval₂Hom Complex.ofRealHom (fun r => ((1 / 8 : ℝ) : ℂ) * z r) P = _
      rw [show (fun r => ((1 / 8 : ℝ) : ℂ) * z r) = fun r => z r / 8 from funext fun _ => by push_cast; ring]
    rw [hce, MvPolynomial.eval₂_eq']
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
    rw [norm_mul]; change ‖(P.coeff β : ℂ)‖ * ‖∏ r, (z r / 8) ^ β r‖ ≤ |P.coeff β|
    rw [Complex.norm_real]
    have hp : ‖∏ r, (z r / 8) ^ β r‖ ≤ 1 := by
      rw [norm_prod]
      refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun r _ => ?_
      rw [norm_pow]; refine pow_le_one₀ (norm_nonneg _) ?_
      have hcoord : ‖z r - (v r : ℂ)‖ < 1 := (norm_le_pi_norm (z - fun r => (v r : ℂ)) r).trans_lt hz
      have hvcoord : ‖(v r : ℂ)‖ ≤ 1 := by simpa only [Complex.norm_real] using (norm_le_pi_norm v r).trans hv
      have htri := norm_sub_norm_le (z r) (v r : ℂ)
      rw [norm_div]; norm_num; exact (div_le_one (by norm_num : (0 : ℝ) < 8)).mpr (by linarith)
    exact (mul_le_mul_of_nonneg_left hp (abs_nonneg _)).trans_eq (mul_one _)
  have hpDer (k₀ : ℕ) (hk₀ : k₀ ≤ m) (hu1 : ‖u‖ ≤ 1) :
      ‖iteratedFDeriv ℝ k₀ (fun x => MvPolynomial.eval x (frameScaledPolynomial P)) u‖ ≤
        frameCoefficientL1 P * Cp := by
    have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp_iff.mpr zero_le_one
    by_cases hk0 : k₀ = 0
    · subst hk0; rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      have hc0 := hcBnd u hu1 (fun r => (u r : ℂ)) (by simp)
      rw [complexify, MvPolynomial.eval_map] at hc0
      change ‖MvPolynomial.eval₂ Complex.ofRealHom (Complex.ofRealHom ∘ u) (frameScaledPolynomial P)‖ ≤ _ at hc0
      rw [← MvPolynomial.eval₂_comp] at hc0
      change ‖(MvPolynomial.eval u (frameScaledPolynomial P) : ℂ)‖ ≤ _ at hc0
      simp only [Complex.norm_real, Real.norm_eq_abs] at hc0
      have hmfac : (1 : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_pos m
      have hmexp : (1 : ℝ) ≤ (Real.exp 1) ^ m := one_le_pow₀ he1
      exact hc0.trans ((le_mul_of_one_le_right (frameCoefficientL1_nonneg P)
        (by dsimp [Cp]; nlinarith)))
    · have hd := real_polynomial_derivative_norm_bound (frameScaledPolynomial P) u 1
        (frameCoefficientL1 P) zero_lt_one (frameCoefficientL1_nonneg P) (hcBnd u hu1) (Nat.pos_of_ne_zero hk0)
      simp only [div_one] at hd
      refine hd.trans ?_
      dsimp [Cp]; rw [← mul_assoc]
      have hf : (k₀.factorial : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_le hk₀
      have hp : (Real.exp 1) ^ k₀ ≤ (Real.exp 1) ^ m := pow_le_pow_right₀ he1 hk₀
      have hL1 := frameCoefficientL1_nonneg P
      gcongr
  by_cases hu : u ∈ tsupport (highWindowTensor d)
  · have hu1 : ‖u‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun r => by
      rw [Real.norm_eq_abs]; exact (highWindowTensor_tsupport_bound hu r).trans (by norm_num)
    have hpcd : ContDiff ℝ ∞ fun x => MvPolynomial.eval x (frameScaledPolynomial P) :=
      (RoughRegime.PolynomialDerivatives.polynomial_contDiff _).of_le le_top
    have hder := norm_iteratedFDeriv_mul_le (highWindowTensor_contDiff d) hpcd u (n := q) (by simp)
    change ‖iteratedFDeriv ℝ q (highFrameProfile P) u‖ ≤ _ at hder
    refine hder.trans ((Finset.sum_le_sum (g := fun j => (q.choose j : ℝ) * B' * (frameCoefficientL1 P * Cp))
      fun j hj => ?_).trans ?_)
    · have hjq : j ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have h1 := (hB j (hjq.trans hq) u).trans (le_max_left B 1)
      have h2 := hpDer (q - j) ((Nat.sub_le _ _).trans hq) hu1
      have hBp : 0 < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
      gcongr
    · rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
      refine (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hq)
          (le_trans zero_le_one (le_max_right _ _)))
        (mul_nonneg (frameCoefficientL1_nonneg P) (by dsimp [Cp]; positivity))).trans_eq ?_
      dsimp [K]; ring
  · have hz : iteratedFDeriv ℝ q (highFrameProfile P) u = 0 := by
      by_contra hn
      exact hu (tsupport_mul_subset_left (support_iteratedFDeriv_subset (𝕜 := ℝ) q hn))
    rw [hz, norm_zero]
    exact mul_nonneg (by dsimp [B', Cp, K]; positivity) (frameCoefficientL1_nonneg P)

def highPeriodizedChart (d k : ℕ) (j : HighWindowLabels d k)
    (G : Covariate d → ℝ) (x : Covariate d) : ℝ :=
  ∑ᶠ z : Fin d → ℤ, if (∀ r, (z r : ZMod k) = j r) then G fun r => (k : ℝ) * x r - z r else 0

theorem highPeriodizedChart_locallyFinite (d k : ℕ) (j : HighWindowLabels d k)
    (G : Covariate d → ℝ) (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0) :
    LocallyFinite fun z : Fin d → ℤ => support fun x : Covariate d =>
      if (∀ r, (z r : ZMod k) = j r) then G (fun r => (k : ℝ) * x r - z r) else 0 := by
  have hlf : LocallyFinite fun z : Fin d → ℤ => support fun x : Covariate d => G fun r => x r - z r := fun x =>
    ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one,
      (Fintype.piFinset fun r => Finset.Icc (⌊x r⌋ - 3) (⌊x r⌋ + 3)).finite_toSet.subset fun z ⟨y, hy, hnear⟩ =>
        Fintype.mem_piFinset.mpr fun r => by
          have hw : highWindowTensor d (fun r => y r - z r) ≠ 0 := fun h => hy (hG0 _ h)
          have hcl := abs_lt.mp ((highWindowTensor_support_bound hw r).trans (by norm_num : (3 / 4 : ℝ) < 1))
          have hnorm : ‖y - x‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hnear
          have hcd := abs_lt.mp ((show |y r - x r| ≤ ‖y - x‖ by
            simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (y - x) r).trans_lt hnorm)
          have hf := Int.floor_le (x r); have hc := Int.lt_floor_add_one (x r)
          exact Finset.mem_Icc.mpr ⟨(Int.cast_le (R := ℝ)).mp (by push_cast; linarith),
            (Int.cast_le (R := ℝ)).mp (by push_cast; linarith)⟩⟩
  refine (hlf.preimage_continuous (by fun_prop : Continuous fun x : Covariate d => fun r => (k : ℝ) * x r)).subset
    fun z x hx => ?_
  by_cases hz : ∀ r, (z r : ZMod k) = j r
  · change (if (∀ r, (z r : ZMod k) = j r) then G (fun r => (k : ℝ) * x r - z r) else 0) ≠ 0 at hx
    rwa [ite_eq_left hz] at hx
  · simp [hz] at hx

theorem highPeriodizedChart_contDiff (d k : ℕ) (j : HighWindowLabels d k)
    (G : Covariate d → ℝ) (hG : ContDiff ℝ ∞ G) (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0) :
    ContDiff ℝ ∞ (highPeriodizedChart d k j G) := by
  unfold highPeriodizedChart
  apply ContMDiff.contDiff
  apply contMDiff_finsum _ (highPeriodizedChart_locallyFinite d k j G hG0)
  intro z
  apply ContDiff.contMDiff
  by_cases hz : ∀ r, (z r : ZMod k) = j r
  · simp only [ite_eq_left hz]; exact hG.comp (by fun_prop)
  · simp only [ite_eq_right hz]; exact contDiff_const

private lemma highPeriodizedChart_eventuallyEq_single (d k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (G : Covariate d → ℝ)
    (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0) (x : Covariate d) :
    ∃ z : Fin d → ℤ, (∀ r, (z r : ZMod k) = j r) ∧
      highPeriodizedChart d k j G =ᶠ[𝓝 x] fun y => G fun r => (k : ℝ) * y r - z r := by
  choose z hz he using fun r => highPeriodicWindow_eventuallyEq_single k hk (j r) (x r)
  refine ⟨z, hz, ?_⟩
  filter_upwards [Filter.eventually_all.mpr fun r => (continuous_apply r).continuousAt.eventually (he r)] with y hy
  rw [highPeriodizedChart, finsum_eq_single _ z]
  · simp only [ite_eq_left hz]
  · intro q hq
    by_cases hqj : ∀ r, (q r : ZMod k) = j r
    · simp only [ite_eq_left hqj]
      by_contra hnonzero
      have hprof : highWindowTensor d (fun r => (k : ℝ) * y r - q r) ≠ 0 := fun h => hnonzero (hG0 _ h)
      refine hq (funext fun r => ?_)
      have hqr : highWindowProfile ((k : ℝ) * y r - q r) ≠ 0 :=
        fun hh => hprof (Finset.prod_eq_zero (Finset.mem_univ r) hh)
      have hqp : 0 < highWindowProfile ((k : ℝ) * y r - q r) := lt_of_le_of_ne (highWindowProfile_nonneg _) (Ne.symm hqr)
      have htle : highWindowProfile ((k : ℝ) * y r - q r) ≤ highPeriodicWindow k (j r) (y r) := by
        simpa only [ite_eq_left (hqj r), highPeriodicWindow] using
          single_le_finsum (q r) ((highPeriodicWindow_locallyFinite k (j r)).point_finite (y r))
            fun a : ℤ => by split_ifs <;> [exact highWindowProfile_nonneg _; exact le_rfl]
      rw [hy r] at htle
      have hqs : q r ∈ support fun a : ℤ => if (a : ZMod k) = j r then highWindowProfile ((k : ℝ) * y r - a) else 0 := by
        simpa only [mem_support, ite_eq_left (hqj r)] using hqr
      have hzs : z r ∈ support fun a : ℤ => if (a : ZMod k) = j r then highWindowProfile ((k : ℝ) * y r - a) else 0 := by
        simpa only [mem_support, ite_eq_left (hz r)] using (hqp.trans_le htle).ne'
      exact highPeriodicWindow_support_subsingleton k (by omega) (j r) (y r) hqs hzs
    · simp only [ite_eq_right hqj]

def highFrameField (d k : ℕ) [NeZero k] (η : ℝ)
    (P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ) (x : Covariate d) : ℝ :=
  η * ∑ j, highPeriodizedChart d k j (highFrameProfile (P j)) x

theorem highFrameProfile_zero_of_window_zero {d : ℕ} (P : MvPolynomial (Fin d) ℝ)
    (u : Covariate d) (hu : highWindowTensor d u = 0) : highFrameProfile P u = 0 := by
  simp only [highFrameProfile, hu, zero_mul]

theorem highFrameField_contDiff (d k : ℕ) [NeZero k] (η : ℝ)
    (P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ) :
    ContDiff ℝ ∞ (highFrameField d k η P) := by
  change ContDiff ℝ ∞ fun x => η • ∑ j, highPeriodizedChart d k j (highFrameProfile (P j)) x
  exact ContDiff.const_smul _ (ContDiff.sum fun j _ =>
    highPeriodizedChart_contDiff d k j _ (highFrameProfile_contDiff (P j))
      (highFrameProfile_zero_of_window_zero (P j)))

private lemma highFrameField_derivative_bound (d m : ℕ) :
    ∃ Cfr : ℝ, 1 ≤ Cfr ∧ ∀ k : ℕ, ∀ (_ : NeZero k), 4 ≤ k → ∀ η : ℝ,
      ∀ P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ,
      (∀ j, frameCoefficientL1 (P j) ≤ Cfr⁻¹) → ∀ q ≤ m, ∀ x : Covariate d,
      ‖iteratedFDeriv ℝ q (highFrameField d k η P) x‖ ≤
        |η| * (2 : ℝ) ^ d * (k : ℝ) ^ q := by
  obtain ⟨B, _, hB⟩ := highFrameProfile_derivative_bound d m
  let Cfr := max B 1
  have hCfr1 : 1 ≤ Cfr := le_max_right _ _
  have hCfr0 : 0 < Cfr := lt_of_lt_of_le one_pos hCfr1
  refine ⟨Cfr, hCfr1, fun k hk0 hk η P hP q hq x => ?_⟩
  letI := hk0
  have hchart (j : HighWindowLabels d k) :
      ‖iteratedFDeriv ℝ q (highPeriodizedChart d k j (highFrameProfile (P j))) x‖ ≤ (k : ℝ) ^ q := by
    obtain ⟨z, _, he⟩ := highPeriodizedChart_eventuallyEq_single d k hk j _
      (highFrameProfile_zero_of_window_zero (P j)) x
    rw [(he.iteratedFDeriv ℝ q).eq_of_nhds]
    let g : Covariate d →L[ℝ] Covariate d := (k : ℝ) • ContinuousLinearMap.id ℝ (Covariate d)
    let G0 : Covariate d → ℝ := fun y => highFrameProfile (P j) (y - fun r => (z r : ℝ))
    have hG0 : ContDiff ℝ q G0 := ((highFrameProfile_contDiff (P j)).of_le (by simp)).comp
      (contDiff_id.sub contDiff_const)
    have hid := g.iteratedFDerivWithin_comp_right hG0.contDiffOn uniqueDiffOn_univ
      (by simpa using (uniqueDiffOn_univ : UniqueDiffOn ℝ (univ : Set (Covariate d))))
      (x := x) (mem_univ _) (i := q) le_rfl
    simp only [preimage_univ, iteratedFDerivWithin_univ] at hid
    change ‖iteratedFDeriv ℝ q (G0 ∘ g) x‖ ≤ _
    rw [hid]
    have hg : ‖g‖ ≤ (k : ℝ) := by
      dsimp [g]; rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg k)]
      exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (Nat.cast_nonneg k)).trans_eq (mul_one _)
    have hGF : ‖iteratedFDeriv ℝ q G0 (g x)‖ ≤ 1 := by
      simpa only [G0, iteratedFDeriv_comp_sub] using
        (hB (P j) q hq (g x - fun r => (z r : ℝ))).trans
          ((mul_le_mul (le_max_left _ _) (hP j) (frameCoefficientL1_nonneg _) hCfr0.le).trans_eq (mul_inv_cancel₀ hCfr0.ne'))
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    simpa only [one_mul] using mul_le_mul hGF (pow_le_pow_left₀ (norm_nonneg g) hg q)
      (pow_nonneg (norm_nonneg g) _) zero_le_one
  have hsmooth (j : HighWindowLabels d k) :
      ContDiffAt ℝ q (highPeriodizedChart d k j (highFrameProfile (P j))) x :=
    ((highPeriodizedChart_contDiff d k j _ (highFrameProfile_contDiff (P j))
      (highFrameProfile_zero_of_window_zero (P j))).of_le (by simp)).contDiffAt
  have he : iteratedFDeriv ℝ q (highFrameField d k η P) x =
      η • ∑ j, iteratedFDeriv ℝ q (highPeriodizedChart d k j (highFrameProfile (P j))) x := by
    change iteratedFDeriv ℝ q (fun y => η • ∑ j, highPeriodizedChart d k j (highFrameProfile (P j)) y) x = _
    rw [iteratedFDeriv_const_smul_apply' (ContDiffAt.sum fun j _ => hsmooth j),
      iteratedFDeriv_fun_sum_apply fun j _ => hsmooth j]
  rw [he, norm_smul, Real.norm_eq_abs]
  let A := Finset.univ.filter fun j : HighWindowLabels d k =>
    iteratedFDeriv ℝ q (highPeriodizedChart d k j (highFrameProfile (P j))) x ≠ 0
  have hov : A.card ≤ 2 ^ d := by
    let box : Finset (HighWindowLabels d k) := Fintype.piFinset fun r =>
      {((⌊(k : ℝ) * x r⌋ : ℤ) : ZMod k), ((⌊(k : ℝ) * x r⌋ + 1 : ℤ) : ZMod k)}
    have hsub : A ⊆ box := fun j hj => by
      obtain ⟨z, hz, heq⟩ := highPeriodizedChart_eventuallyEq_single d k hk j _
        (highFrameProfile_zero_of_window_zero (P j)) x
      let Af : Covariate d → ℝ := fun y => highFrameProfile (P j) fun r => (k : ℝ) * y r - z r
      have hn : iteratedFDeriv ℝ q Af x ≠ 0 := by
        have hne := (Finset.mem_filter.mp hj).2
        rwa [← (heq.iteratedFDeriv ℝ q).eq_of_nhds]
      have ht := tsupport_comp_subset_preimage (highFrameProfile (P j))
        (by fun_prop : Continuous fun y : Covariate d => fun r => (k : ℝ) * y r - (z r : ℝ))
        (support_iteratedFDeriv_subset (𝕜 := ℝ) q hn)
      have hclose := highWindowTensor_tsupport_bound (tsupport_mul_subset_left ht)
      refine Fintype.mem_piFinset.mpr fun r => ?_
      have hf := Int.floor_le ((k : ℝ) * x r)
      have hc := Int.lt_floor_add_one ((k : ℝ) * x r)
      have hcl := abs_le.mp (hclose r)
      have hlo : ⌊(k : ℝ) * x r⌋ ≤ z r := by
        by_contra h
        have hcast : (z r : ℝ) + 1 ≤ ⌊(k : ℝ) * x r⌋ := by exact_mod_cast (by omega : z r + 1 ≤ _)
        linarith
      have hhi : z r ≤ ⌊(k : ℝ) * x r⌋ + 1 := by
        by_contra h
        have hcast : (⌊(k : ℝ) * x r⌋ : ℝ) + 2 ≤ z r := by exact_mod_cast (by omega : _ + 2 ≤ z r)
        linarith
      rcases (by omega : z r = ⌊(k : ℝ) * x r⌋ ∨ z r = ⌊(k : ℝ) * x r⌋ + 1) with hr | hr
      · simp only [← hz r, hr, Finset.mem_insert, Finset.mem_singleton, true_or]
      · simp only [← hz r, hr, Finset.mem_insert, Finset.mem_singleton, or_true]
    refine (Finset.card_le_card hsub).trans ?_
    dsimp [box]; rw [Fintype.card_piFinset]
    exact (Finset.prod_le_prod' fun _ _ => Finset.card_le_two).trans_eq (by simp)
  have hsum : ‖∑ j, iteratedFDeriv ℝ q (highPeriodizedChart d k j (highFrameProfile (P j))) x‖ ≤
      (2 ^ d : ℝ) * (k : ℝ) ^ q := by
    refine (norm_sum_le _ _).trans ?_
    rw [show (∑ j, ‖iteratedFDeriv ℝ q (highPeriodizedChart d k j (highFrameProfile (P j))) x‖) =
      ∑ j ∈ A, ‖iteratedFDeriv ℝ q (highPeriodizedChart d k j (highFrameProfile (P j))) x‖ by
        dsimp [A]; rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun j _ => by
          by_cases hg : iteratedFDeriv ℝ q (highPeriodizedChart d k j (highFrameProfile (P j))) x = 0 <;> simp [hg]]
    calc
      _ ≤ ∑ _j ∈ A, (k : ℝ) ^ q := Finset.sum_le_sum fun j _ => hchart j
      _ = (A.card : ℝ) * (k : ℝ) ^ q := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hov) (pow_nonneg (Nat.cast_nonneg k) _)
  have hh := mul_le_mul_of_nonneg_left hsum (abs_nonneg η)
  convert hh using 1; ring

theorem highFrameField_model_bounds {d : ℕ} (C : ModelConstants d) :
    ∃ Cfr : ℝ, 1 ≤ Cfr ∧ ∀ k : ℕ, ∀ (_ : NeZero k), 4 ≤ k →
      ∀ cf : ℝ, 0 ≤ cf → ∀ P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ,
      (∀ j, frameCoefficientL1 (P j) ≤ Cfr⁻¹) →
      let F := highFrameField d k (cf * (k : ℝ) ^ (-C.smoothness)) P
      (∀ x, |F x| ≤ (2 : ℝ) ^ d * (cf * (k : ℝ) ^ (-C.smoothness))) ∧
      (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) ≤ C.order → ∀ x,
        |multiPartial F (fun r => (γ r).val) x| ≤ (2 : ℝ) ^ d * cf) ∧
      (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) = C.order → ∀ x y,
        |multiPartial F (fun r => (γ r).val) x - multiPartial F (fun r => (γ r).val) y| ≤
          (2 * ((2 : ℝ) ^ d * cf)) * euclideanNorm (x - y) ^ C.alpha) := by
  obtain ⟨Cfr, hCfr1, hCfr⟩ := highFrameField_derivative_bound d (C.order + 1)
  refine ⟨Cfr, hCfr1, fun k hk0 hk cf hcf P hP => ?_⟩
  letI := hk0
  let F := highFrameField d k (cf * (k : ℝ) ^ (-C.smoothness)) P
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hkpos : (0 : ℝ) < k := lt_of_lt_of_le one_pos hkR
  have hη0 : 0 ≤ cf * (k : ℝ) ^ (-C.smoothness) := by positivity
  have hbound : ∀ q ≤ C.order + 1, ∀ x,
      ‖iteratedFDeriv ℝ q F x‖ ≤ ((2 : ℝ) ^ d * cf) * (k : ℝ) ^ ((q : ℝ) - C.smoothness) := fun q hq x => by
    have hh := hCfr k hk0 hk (cf * (k : ℝ) ^ (-C.smoothness)) P hP q hq x
    rw [abs_of_nonneg hη0] at hh
    convert hh using 1
    rw [show (k : ℝ) ^ ((q : ℝ) - C.smoothness) = (k : ℝ) ^ (-C.smoothness) * (k : ℝ) ^ q by
      rw [← Real.rpow_natCast, ← Real.rpow_add hkpos]; congr 1; ring]
    ring
  obtain ⟨hs, hm⟩ := mixed_bounds_of_scaled_derivatives C F (highFrameField_contDiff _ _ _ _)
    (k : ℝ) ((2 : ℝ) ^ d * cf) hkR (by positivity) hbound
  refine ⟨fun x => ?_, hs, hm⟩
  have hh := hCfr k hk0 hk (cf * (k : ℝ) ^ (-C.smoothness)) P hP 0 (by omega) x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg hη0, pow_zero, mul_one] at hh
  simpa only [F, mul_comm] using hh

end SmoothWindowsAndFrame

-- History coordinate transport, maximal deletion, marked append, and density derivative

section HistoryAppendAndDeletion
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private lemma historyScaledUpperDensity_orderEmbedding_map {A B : Type*}
    [PartialOrder A] [PartialOrder B] [DecidableEq A] [DecidableEq B]
    (f : A ↪o B) (weight : B → ℝ) (ρ : ℝ) (S : Finset A) (t : ℝ) :
    historyScaledUpperDensity weight ρ (S.map f.toEmbedding) t =
      historyScaledUpperDensity (weight ∘ f) ρ S t := by
  have hmax (T : Finset A) : historyMaximalPieces (T.map f.toEmbedding) = (historyMaximalPieces T).map f.toEmbedding := by
    ext b; refine ⟨fun hb => ?_, fun hb => ?_⟩
    · obtain ⟨hb, hm⟩ := mem_historyMaximalPieces.1 hb
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hb
      exact Finset.mem_map.2 ⟨x, mem_historyMaximalPieces.2 ⟨hx, fun y hy hxy =>
        f.injective (hm (f y) (Finset.mem_map.2 ⟨y, hy, rfl⟩) (f.monotone hxy))⟩, rfl⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hb
      obtain ⟨hx, hm⟩ := mem_historyMaximalPieces.1 hx
      exact mem_historyMaximalPieces.2 ⟨Finset.mem_map.2 ⟨x, hx, rfl⟩, fun c hc hxc => by
        obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hc
        exact congrArg f (hm y hy (f.le_iff_le.1 hxc))⟩
  have hdel : ∀ (k : ℕ) (T : Finset A),
      historyDeletionCoefficient (fun x => weight x / ρ) k (T.map f.toEmbedding) =
        historyDeletionCoefficient ((fun x => weight x / ρ) ∘ f) k T := by
    intro k; induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro T
      rw [historyDeletionCoefficient_succ, historyDeletionCoefficient_succ, hmax, Finset.sum_map]
      exact Finset.sum_congr rfl fun x _ => by rw [← Finset.map_erase, ih]; rfl
  unfold historyScaledUpperDensity
  rw [historyUpperDensity_eq_deletionPolynomial, historyUpperDensity_eq_deletionPolynomial]
  unfold historyDeletionPolynomial; rw [Finset.card_map]
  exact Finset.sum_congr rfl fun k _ => by rw [hdel]; rfl

def wordHeapPiecePositionEquiv {J : Type*} (word : List J) (dependent : J → J → Prop) :
    WordHeapPiece word dependent ≃ Fin word.length where
  toFun := WordHeapPiece.position
  invFun i := ⟨i⟩
  left_inv x := by cases x; rfl
  right_inv _ := rfl

def historyHeapCoordinateEquiv {J : Type*} {u v : List J} {dependent : J → J → Prop}
    (e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent) : Fin u.length ≃ Fin v.length :=
  (wordHeapPiecePositionEquiv u dependent).symm.trans
    (e.toEquiv.trans (wordHeapPiecePositionEquiv v dependent))

@[simp] theorem historyHeapCoordinateEquiv_position {J : Type*} {u v : List J} {dependent : J → J → Prop}
    (e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent) (x : WordHeapPiece u dependent) :
    historyHeapCoordinateEquiv e x.position = (e x).position := by cases x; rfl

def historyHeapMarkEquiv {J : Type*} {u v : List J} {dependent : J → J → Prop}
    (e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent) {E : Type*} [MeasurableSpace E] :
    (Fin u.length → E) ≃ᵐ (Fin v.length → E) :=
  MeasurableEquiv.piCongrLeft (fun _ => E) (historyHeapCoordinateEquiv e)

@[simp] theorem historyHeapMarkEquiv_position {J : Type*} {u v : List J} {dependent : J → J → Prop}
    (e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent) {E : Type*} [MeasurableSpace E]
    (marks : Fin u.length → E) (x : WordHeapPiece u dependent) :
    historyHeapMarkEquiv e marks (e x).position = marks x.position := by
  simpa only [historyHeapMarkEquiv, historyHeapCoordinateEquiv_position] using
    MeasurableEquiv.piCongrLeft_apply_apply (historyHeapCoordinateEquiv e)
      (β := fun _ : Fin v.length => E) marks x.position

def wordHeapAppendedPiece {J : Type*} (word : List J) (dependent : J → J → Prop) (j : J) :
    WordHeapPiece (word ++ [j]) dependent := ⟨⟨word.length, by simp⟩⟩

@[simp] lemma wordHeapAppendedPiece_label {J : Type*} (word : List J) (dependent : J → J → Prop) (j : J) :
    wordHeapLabel (wordHeapAppendedPiece word dependent j) = j := by
  unfold wordHeapLabel wordHeapAppendedPiece
  rw [List.get_eq_getElem, List.getElem_append_right (by rfl)]; simp

lemma wordHeapAppendedPiece_maximal {J : Type*} (word : List J) (dependent : J → J → Prop) (j : J) :
    wordHeapAppendedPiece word dependent j ∈ historyMaximalPieces Finset.univ :=
  mem_historyMaximalPieces.2 ⟨Finset.mem_univ _, fun y _ hxy => by
    have hlo := wordHeap_reachable_position_le hxy
    have hhi := y.position.isLt
    simp only [List.length_append, List.length_singleton] at hhi
    apply WordHeapPiece.ext; apply Fin.ext
    change word.length ≤ y.position.val at hlo
    change y.position.val = word.length; omega⟩

theorem historyShape_terminal_iff_maximal {J : Type*} (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    g ∈ Set.range (historyShapeAppend dependent j) ↔
      ∃ x : WordHeapPiece g.out dependent,
        x ∈ historyMaximalPieces Finset.univ ∧ wordHeapLabel x = j := by
  refine ⟨?_, ?_⟩
  · rintro ⟨u, hu⟩
    have hmk : (Quotient.mk _ (u.out ++ [j]) : HistoryShape (fun a b => ¬ dependent a b)) = g :=
      (congrArg (historyShapeAppend dependent j) (Quotient.out_eq u)).trans hu
    obtain ⟨e, he⟩ := historyShapeRelation_heapIso dependent hsymm
      (Quotient.exact (hmk.trans (Quotient.out_eq g).symm))
    let x := wordHeapAppendedPiece u.out dependent j
    have hxmap : e x ∈ historyMaximalPieces
        ((Finset.univ : Finset (WordHeapPiece (u.out ++ [j]) dependent)).map e.toEquiv.toEmbedding) := by
      rw [historyMaximalPieces_orderIso_map]
      exact Finset.mem_map.2 ⟨x, wordHeapAppendedPiece_maximal u.out dependent j, rfl⟩
    rw [Finset.map_univ_equiv e.toEquiv] at hxmap
    exact ⟨e x, hxmap, (he x).trans (wordHeapAppendedPiece_label u.out dependent j)⟩
  · rintro ⟨x, hx, hlabel⟩
    let del := g.out.take x.position.val ++ g.out.drop (x.position.val + 1)
    have hsuf (b : J) (hb : b ∈ g.out.drop (x.position.val + 1)) : ¬ dependent (wordHeapLabel x) b := fun hdep => by
      obtain ⟨k, hk, hkb⟩ := List.mem_iff_getElem.1 hb
      have hyb : x.position.val + 1 + k < g.out.length := by simp only [List.length_drop] at hk; omega
      let y : WordHeapPiece g.out dependent := ⟨⟨x.position.val + 1 + k, hyb⟩⟩
      have hyl : wordHeapLabel y = b := by
        change g.out.get ⟨x.position.val + 1 + k, hyb⟩ = b
        rw [List.get_eq_getElem]; simpa only [List.getElem_drop] using hkb
      have hxy : x ≤ y := wordHeapStep_le ⟨by dsimp [y]; change x.position.val < x.position.val + 1 + k; omega,
        by simpa only [hyl] using hdep⟩
      have hv : x.position.val + 1 + k = x.position.val :=
        congrArg (fun z : WordHeapPiece g.out dependent => z.position.val)
          ((mem_historyMaximalPieces.1 hx).2 y (Finset.mem_univ y) hxy)
      omega
    have hmove : ∀ (after : List J), (∀ b ∈ after, ¬ dependent (wordHeapLabel x) b) →
        Relation.EqvGen (IndependentHistoryExchange fun a b => ¬ dependent a b)
          (wordHeapLabel x :: after) (after ++ [wordHeapLabel x]) := by
      intro after; induction after with
      | nil => intro _; exact .refl _
      | cons b after ih =>
        intro ha
        exact .trans _ _ _ (.rel _ _ (IndependentHistoryExchange.swap [] after _ b (ha b List.mem_cons_self)))
          (historyShapeRelation_cons b (ih fun c hc => ha c (List.mem_cons_of_mem _ hc)))
    have hpref : ∀ (pre : List J) {u v : List J},
        Relation.EqvGen (IndependentHistoryExchange fun a b => ¬ dependent a b) u v →
        Relation.EqvGen (IndependentHistoryExchange fun a b => ¬ dependent a b) (pre ++ u) (pre ++ v) := by
      intro pre; induction pre with
      | nil => exact id
      | cons a _ ih => exact fun h => historyShapeRelation_cons a (ih h)
    have hrel : Relation.EqvGen (IndependentHistoryExchange fun a b => ¬ dependent a b)
        g.out (del ++ [wordHeapLabel x]) := by
      have hp := hpref (g.out.take x.position.val) (hmove _ hsuf)
      have hw : g.out = g.out.take x.position.val ++ wordHeapLabel x :: g.out.drop (x.position.val + 1) := by
        change g.out = g.out.take x.position.val ++ g.out.get x.position :: g.out.drop (x.position.val + 1)
        rw [List.cons_get_drop_succ]; exact (List.take_append_drop _ _).symm
      conv_lhs => rw [hw]
      simpa only [del, List.append_assoc] using hp
    refine ⟨Quotient.mk _ del, ?_⟩
    rw [← hlabel, historyShapeAppend_mk]
    exact (Quotient.sound hrel).symm.trans (Quotient.out_eq g)

theorem historyCanonicalAppendHeapIso_exists {J : Type*} (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    ∃ e : WordHeapPiece (g.out ++ [j]) dependent ≃o
        WordHeapPiece (historyShapeAppend dependent j g).out dependent,
      ∀ x, wordHeapLabel (e x) = wordHeapLabel x :=
  historyShapeRelation_heapIso dependent hsymm <| Quotient.exact <|
    (congrArg (historyShapeAppend dependent j) (Quotient.out_eq g)).trans (Quotient.out_eq _).symm

def historyCanonicalAppendHeapIso {J : Type*} [Fintype J] [LinearOrder J]
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    WordHeapPiece (g.out ++ [j]) dependent ≃o
      WordHeapPiece (historyShapeAppend dependent j g).out dependent :=
  (historyCanonicalAppendHeapIso_exists dependent hsymm j g).choose

theorem historyCanonicalAppendHeapIso_label {J : Type*} [Fintype J] [LinearOrder J]
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b))
    (x : WordHeapPiece (g.out ++ [j]) dependent) :
    wordHeapLabel (historyCanonicalAppendHeapIso dependent hsymm j g x) = wordHeapLabel x :=
  (historyCanonicalAppendHeapIso_exists dependent hsymm j g).choose_spec x

def historyFiniteMarkAppendEquiv (n : ℕ) {E : Type*} [MeasurableSpace E] :
    E × (Fin n → E) ≃ᵐ (Fin (n + 1) → E) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) (Fin.last n)).symm

theorem historyFiniteMarkAppendEquiv_preserving (n : ℕ) {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] :
    MeasurePreserving (historyFiniteMarkAppendEquiv n (E := E))
      (π.prod (Measure.pi fun _ : Fin n => π)) (Measure.pi fun _ : Fin (n + 1) => π) :=
  (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => π) (Fin.last n)).symm _

@[simp] theorem historyFiniteMarkAppendEquiv_last (n : ℕ) {E : Type*} [MeasurableSpace E]
    (fresh : E) (marks : Fin n → E) :
    historyFiniteMarkAppendEquiv n (fresh, marks) (Fin.last n) = fresh :=
  congrArg Prod.fst
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) (Fin.last n)).apply_symm_apply (fresh, marks))

@[simp] theorem historyFiniteMarkAppendEquiv_old (n : ℕ) {E : Type*} [MeasurableSpace E]
    (fresh : E) (marks : Fin n → E) (x : Fin n) :
    historyFiniteMarkAppendEquiv n (fresh, marks) x.castSucc = marks x := by
  have hh := congrArg (fun p : E × (Fin n → E) => p.2 x)
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) (Fin.last n)).apply_symm_apply (fresh, marks))
  change historyFiniteMarkAppendEquiv n (fresh, marks) ((Fin.last n).succAbove x) = marks x at hh
  simpa only [Fin.succAbove_last_apply] using hh

section MarkedAppendJ
variable {J : Type*} [Fintype J] [LinearOrder J]

def historyCanonicalAppendCoordinates (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    Fin (historyShapeLength dependent g + 1) ≃ Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) :=
  (finCongr (by rw [historyShapeLength_out]; simp)).trans
    ((historyHeapCoordinateEquiv (historyCanonicalAppendHeapIso dependent hsymm j g)).trans
      (finCongr (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm))

def historyCanonicalMarkAppendEquiv (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) {E : Type*} [MeasurableSpace E] :
    E × (Fin (historyShapeLength dependent g) → E) ≃ᵐ
      (Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) → E) :=
  (historyFiniteMarkAppendEquiv (historyShapeLength dependent g)).trans
    (MeasurableEquiv.piCongrLeft (fun _ => E) (historyCanonicalAppendCoordinates dependent hsymm j g))

def historyCanonicalAppendedPiece (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    WordHeapPiece (historyShapeAppend dependent j g).out dependent :=
  historyCanonicalAppendHeapIso dependent hsymm j g (wordHeapAppendedPiece g.out dependent j)

theorem historyCanonicalAppendedPiece_maximal (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    historyCanonicalAppendedPiece dependent hsymm j g ∈ historyMaximalPieces Finset.univ := by
  let e := historyCanonicalAppendHeapIso dependent hsymm j g
  have hx : e (wordHeapAppendedPiece g.out dependent j) ∈ historyMaximalPieces
      ((Finset.univ : Finset (WordHeapPiece (g.out ++ [j]) dependent)).map e.toEquiv.toEmbedding) := by
    rw [historyMaximalPieces_orderIso_map]
    exact Finset.mem_map.2 ⟨_, wordHeapAppendedPiece_maximal g.out dependent j, rfl⟩
  rwa [Finset.map_univ_equiv e.toEquiv] at hx

@[simp] theorem historyCanonicalAppendedPiece_label (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    wordHeapLabel (historyCanonicalAppendedPiece dependent hsymm j g) = j :=
  ((historyCanonicalAppendHeapIso_exists dependent hsymm j g).choose_spec _).trans
    (wordHeapAppendedPiece_label g.out dependent j)

@[simp] theorem historyCanonicalMarkAppendEquiv_fresh (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) {E : Type*} [MeasurableSpace E]
    (fresh : E) (marks : Fin (historyShapeLength dependent g) → E) :
    historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)
      (Fin.cast (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm
        (historyCanonicalAppendedPiece dependent hsymm j g).position) = fresh := by
  let hlen : historyShapeLength dependent g + 1 = (g.out ++ [j]).length := by
    rw [historyShapeLength_out]; simp
  have hlast : historyCanonicalAppendCoordinates dependent hsymm j g (Fin.last (historyShapeLength dependent g)) =
      Fin.cast (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm
        (historyCanonicalAppendedPiece dependent hsymm j g).position := by
    have hl : (finCongr hlen) (Fin.last (historyShapeLength dependent g)) =
        (wordHeapAppendedPiece g.out dependent j).position := Fin.ext (historyShapeLength_out dependent g)
    unfold historyCanonicalAppendCoordinates historyCanonicalAppendedPiece
    change Fin.cast (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm
      (historyHeapCoordinateEquiv (historyCanonicalAppendHeapIso dependent hsymm j g)
        ((finCongr hlen) (Fin.last (historyShapeLength dependent g)))) = _
    rw [hl, historyHeapCoordinateEquiv_position]
  rw [← hlast]
  have hh := MeasurableEquiv.piCongrLeft_apply_apply
    (historyCanonicalAppendCoordinates dependent hsymm j g)
    (β := fun _ => E) (historyFiniteMarkAppendEquiv _ (fresh, marks)) (Fin.last _)
  change MeasurableEquiv.piCongrLeft
    (fun _ : Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) => E)
    (historyCanonicalAppendCoordinates dependent hsymm j g)
    (historyFiniteMarkAppendEquiv _ (fresh, marks))
    (historyCanonicalAppendCoordinates dependent hsymm j g (Fin.last (historyShapeLength dependent g))) = fresh
  rw [hh, historyFiniteMarkAppendEquiv_last]

omit [Fintype J] [LinearOrder J] in
theorem historySigma_measurable_iff {I : Type*} {X : I → Type*} {Y : Type*}
    [∀ i, MeasurableSpace (X i)] [MeasurableSpace Y] (f : Sigma X → Y) :
    Measurable f ↔ ∀ i, Measurable fun x => f ⟨i, x⟩ :=
  ⟨fun hf i => hf.comp (Measurable.of_le_map (iInf_le _ i)),
   fun hf _ hs => MeasurableSpace.measurableSet_iInf.mpr fun i => hf i hs⟩

omit [Fintype J] [LinearOrder J] in
def historySigmaProdMeasurableEquiv {I : Type*} [Countable I] (X : I → Type*) (Y : Type*)
    [∀ i, MeasurableSpace (X i)] [∀ i, StandardBorelSpace (X i)]
    [MeasurableSpace Y] [StandardBorelSpace Y] : (Sigma X) × Y ≃ᵐ Sigma fun i => X i × Y := by
  let _ := fun i => upgradeStandardBorel (X i)
  let _ := upgradeStandardBorel Y
  let _ : BorelSpace (Sigma X) := historySigma_borelSpace
  let _ : BorelSpace (Sigma fun i => X i × Y) := historySigma_borelSpace
  exact (Homeomorph.sigmaProdDistrib (X := X) (Y := Y)).toMeasurableEquiv

def historyMarkedAppend (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) {E : Type*} [MeasurableSpace E] (h : HistoryMarked dependent E × E) :
    HistoryMarked dependent E :=
  ⟨historyShapeAppend dependent j h.1.1,
    historyCanonicalMarkAppendEquiv dependent hsymm j h.1.1 (h.2, h.1.2)⟩

theorem historyMarkedAppend_measurable (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] :
    Measurable (historyMarkedAppend dependent hsymm j (E := E)) := by
  let X := fun g : HistoryShape (fun a b => ¬ dependent a b) => Fin (historyShapeLength dependent g) → E
  have hf : Measurable (fun h : Sigma fun g => X g × E =>
      (⟨historyShapeAppend dependent j h.1,
        historyCanonicalMarkAppendEquiv dependent hsymm j h.1 (h.2.2, h.2.1)⟩ : HistoryMarked dependent E)) :=
    (historySigma_measurable_iff _).mpr fun g =>
      (historyMarked_measurable_mk dependent (historyShapeAppend dependent j g)).comp
        ((historyCanonicalMarkAppendEquiv dependent hsymm j g).measurable.comp MeasurableEquiv.prodComm.measurable)
  exact hf.comp (historySigmaProdMeasurableEquiv X E).measurable

def historyPrefixPosition (word : List J) (j : J) : Fin word.length ↪ Fin (word ++ [j]).length where
  toFun x := ⟨x.val, by have := x.isLt; simp only [List.length_append, List.length_singleton]; omega⟩
  inj' _ _ h := Fin.ext (congrArg (fun z : Fin (word ++ [j]).length => z.val) h)

private lemma historyPrefixPosition_reachable_reflect (word : List J) (dependent : J → J → Prop) (j : J)
    {p q : Fin (word ++ [j]).length} (hp : p.val < word.length) (hq : q.val < word.length)
    (h : Relation.ReflTransGen (historyPositionStep dependent (word ++ [j]).get) p q) :
    Relation.ReflTransGen (historyPositionStep dependent word.get) ⟨p.val, hp⟩ ⟨q.val, hq⟩ := by
  induction h with
  | refl => exact .refl
  | @tail r q _ hstep ih =>
    have hlt : r.val < q.val := hstep.1
    have hr : r.val < word.length := hlt.trans hq
    refine (ih hr).tail ⟨hstep.1, ?_⟩
    have hg1 : (word ++ [j]).get r = word.get ⟨r.val, hr⟩ := by
      rw [List.get_eq_getElem, List.getElem_append_left hr, List.get_eq_getElem]
    have hg2 : (word ++ [j]).get q = word.get ⟨q.val, hq⟩ := by
      rw [List.get_eq_getElem, List.getElem_append_left hq, List.get_eq_getElem]
    simpa only [hg1, hg2] using hstep.2

def historyPrefixHeapEmbedding (word : List J) (dependent : J → J → Prop) (j : J) :
    WordHeapPiece word dependent ↪o WordHeapPiece (word ++ [j]) dependent where
  toFun x := ⟨historyPrefixPosition word j x.position⟩
  inj' _ _ h := WordHeapPiece.ext ((historyPrefixPosition word j).injective (congrArg WordHeapPiece.position h))
  map_rel_iff' := by
    intro x y
    rw [wordHeap_le_iff_position_reachable, wordHeap_le_iff_position_reachable]
    have hpget (z : Fin word.length) : (word ++ [j]).get (historyPrefixPosition word j z) = word.get z := by
      change (word ++ [j]).get ⟨z.val, _⟩ = word.get z
      rw [List.get_eq_getElem, List.getElem_append_left z.isLt, List.get_eq_getElem]
    refine ⟨fun h => ?_, Relation.ReflTransGen.lift (historyPrefixPosition word j)
      (fun a b h => ⟨h.1, by simpa only [hpget] using h.2⟩) x.position y.position⟩
    have hh := historyPrefixPosition_reachable_reflect word dependent j x.position.isLt y.position.isLt h
    rcases x with ⟨⟨_, _⟩⟩; rcases y with ⟨⟨_, _⟩⟩; exact hh

theorem historyCanonicalAppend_density_delete (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) {E : Type*} [MeasurableSpace E]
    (fresh : E) (marks : Fin (historyShapeLength dependent g) → E)
    (a : E → ℝ) (ρ t : ℝ) :
    historyScaledUpperDensity
      (historyMarkedPieceWeight dependent a
        ⟨historyShapeAppend dependent j g, historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)⟩)
      ρ (Finset.univ.erase (historyCanonicalAppendedPiece dependent hsymm j g)) t =
      historyMarkedDensity dependent ρ t a ⟨g, marks⟩ := by
  classical
  let e := historyCanonicalAppendHeapIso dependent hsymm j g
  let w := historyMarkedPieceWeight dependent a
    ⟨historyShapeAppend dependent j g, historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)⟩
  have ht := historyScaledUpperDensity_orderIso_map e w ρ
    (Finset.univ.erase (wordHeapAppendedPiece g.out dependent j)) t
  rw [Finset.map_erase, Finset.map_univ_equiv] at ht
  have huniv : (Finset.univ : Finset (WordHeapPiece g.out dependent)).map
      (historyPrefixHeapEmbedding g.out dependent j).toEmbedding =
      (Finset.univ : Finset (WordHeapPiece (g.out ++ [j]) dependent)).erase
        (wordHeapAppendedPiece g.out dependent j) := by
    ext y; refine ⟨fun hy => ?_, fun hy => ?_⟩
    · obtain ⟨x, _, rfl⟩ := Finset.mem_map.1 hy
      refine Finset.mem_erase.2 ⟨fun he => ?_, Finset.mem_univ _⟩
      have hv := congrArg (fun z : WordHeapPiece (g.out ++ [j]) dependent => z.position.val) he
      have := x.position.isLt; change x.position.val = g.out.length at hv; omega
    · have hne := (Finset.mem_erase.1 hy).1
      have hlt := y.position.isLt; simp only [List.length_append, List.length_singleton] at hlt
      have hb : y.position.val < g.out.length := by
        have hval : y.position.val ≠ g.out.length := fun hv => hne (WordHeapPiece.ext (Fin.ext hv))
        omega
      exact Finset.mem_map.2 ⟨⟨⟨y.position.val, hb⟩⟩, Finset.mem_univ _, WordHeapPiece.ext (Fin.ext rfl)⟩
  have hdel : historyScaledUpperDensity (w ∘ e) ρ
      (Finset.univ.erase (wordHeapAppendedPiece g.out dependent j)) t =
      historyScaledUpperDensity ((w ∘ e) ∘ historyPrefixHeapEmbedding g.out dependent j) ρ Finset.univ t := by
    rw [← huniv]; exact historyScaledUpperDensity_orderEmbedding_map _ _ ρ _ t
  have hold (x : WordHeapPiece g.out dependent) :
      historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)
        (Fin.cast (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm
          (e (historyPrefixHeapEmbedding g.out dependent j x)).position) =
        marks (Fin.cast (historyShapeLength_out dependent g).symm x.position) := by
    let hlen : historyShapeLength dependent g + 1 = (g.out ++ [j]).length := by
      rw [historyShapeLength_out]; simp
    have hco : historyCanonicalAppendCoordinates dependent hsymm j g
        (Fin.cast (historyShapeLength_out dependent g).symm x.position).castSucc =
        Fin.cast (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm
          (e (historyPrefixHeapEmbedding g.out dependent j x)).position := by
      have hp : (finCongr hlen) (Fin.cast (historyShapeLength_out dependent g).symm x.position).castSucc =
          (historyPrefixHeapEmbedding g.out dependent j x).position := Fin.ext rfl
      unfold historyCanonicalAppendCoordinates
      change Fin.cast (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm
        (historyHeapCoordinateEquiv e
          ((finCongr hlen) (Fin.cast (historyShapeLength_out dependent g).symm x.position).castSucc)) = _
      rw [hp, historyHeapCoordinateEquiv_position]
    rw [← hco]
    have hh := MeasurableEquiv.piCongrLeft_apply_apply
      (historyCanonicalAppendCoordinates dependent hsymm j g)
      (β := fun _ => E) (historyFiniteMarkAppendEquiv _ (fresh, marks))
      (Fin.cast (historyShapeLength_out dependent g).symm x.position).castSucc
    change MeasurableEquiv.piCongrLeft
      (fun _ : Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) => E)
      (historyCanonicalAppendCoordinates dependent hsymm j g)
      (historyFiniteMarkAppendEquiv _ (fresh, marks))
      (historyCanonicalAppendCoordinates dependent hsymm j g
        (Fin.cast (historyShapeLength_out dependent g).symm x.position).castSucc) = _
    rw [hh, historyFiniteMarkAppendEquiv_old]
  rw [hdel, show (w ∘ e) ∘ historyPrefixHeapEmbedding g.out dependent j =
    historyMarkedPieceWeight dependent a ⟨g, marks⟩ from funext fun x => congrArg a (hold x)] at ht
  exact ht

def historyMarkedTerminalSet (dependent : J → J → Prop) (j : J) {E : Type*} :
    Set (HistoryMarked dependent E) := {h | h.1 ∈ Set.range (historyShapeAppend dependent j)}

theorem historyMarkedTerminalSet_measurable (dependent : J → J → Prop) (j : J)
    {E : Type*} [MeasurableSpace E] : MeasurableSet (historyMarkedTerminalSet dependent j (E := E)) := by
  rw [MeasurableSpace.measurableSet_iInf]; intro g
  change MeasurableSet {marks : Fin (historyShapeLength dependent g) → E |
    g ∈ Set.range (historyShapeAppend dependent j)}
  by_cases hg : g ∈ Set.range (historyShapeAppend dependent j) <;> simp [hg]

theorem historyMarkedReference_append_restrict (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (j : J) {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] :
    ENNReal.ofReal (historyReferenceRho Δ) •
      Measure.map (historyMarkedAppend dependent hsymm j (E := E))
        ((historyMarkedReference dependent Δ π).prod π) =
      (historyMarkedReference dependent Δ π).restrict (historyMarkedTerminalSet dependent j) := by
  classical
  have hfib (g : HistoryShape (fun a b => ¬ dependent a b)) :
      Measure.map (historyMarkedAppend dependent hsymm j (E := E))
        ((Measure.map (Sigma.mk g) (Measure.pi fun _ : Fin (historyShapeLength dependent g) => π)).prod π) =
      Measure.map (Sigma.mk (historyShapeAppend dependent j g))
        (Measure.pi fun _ : Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) => π) := by
    let ν := Measure.pi fun _ : Fin (historyShapeLength dependent g) => π
    have hm : (Measure.map (Sigma.mk g) ν).prod π =
        Measure.map (Prod.map (fun marks : Fin (historyShapeLength dependent g) → E =>
          (⟨g, marks⟩ : HistoryMarked dependent E)) id) (ν.prod π) := by
      simpa only [Measure.map_id] using
        Measure.map_prod_map ν π (historyMarked_measurable_mk dependent g) measurable_id
    rw [hm, Measure.map_map (historyMarkedAppend_measurable dependent hsymm j)
      ((historyMarked_measurable_mk dependent g).prodMap measurable_id)]
    let m := fun p : (Fin (historyShapeLength dependent g) → E) × E =>
      historyCanonicalMarkAppendEquiv dependent hsymm j g (p.2, p.1)
    have hp : MeasurePreserving m (ν.prod π)
        (Measure.pi fun _ : Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) => π) :=
      ((measurePreserving_piCongrLeft (fun _ => π) (historyCanonicalAppendCoordinates dependent hsymm j g)).comp
        (historyFiniteMarkAppendEquiv_preserving _ π)).comp Measure.measurePreserving_swap
    change Measure.map ((fun marks : Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) → E =>
      (⟨historyShapeAppend dependent j g, marks⟩ : HistoryMarked dependent E)) ∘ m) (ν.prod π) = _
    rw [← Measure.map_map (historyMarked_measurable_mk dependent _) hp.measurable, hp.map_eq]
  have hraw : ENNReal.ofReal (historyReferenceRho Δ) •
      Measure.map (historyMarkedAppend dependent hsymm j (E := E))
        ((historyMarkedReferenceRaw dependent Δ π).prod π) =
      (historyMarkedReferenceRaw dependent Δ π).restrict (historyMarkedTerminalSet dependent j) := by
    let μf := fun g : HistoryShape (fun a b => ¬ dependent a b) =>
      ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g) •
        Measure.map (fun marks : Fin (historyShapeLength dependent g) → E =>
          (⟨g, marks⟩ : HistoryMarked dependent E)) (Measure.pi fun _ : Fin (historyShapeLength dependent g) => π)
    have h1 : ENNReal.ofReal (historyReferenceRho Δ) •
        Measure.map (historyMarkedAppend dependent hsymm j (E := E))
          ((historyMarkedReferenceRaw dependent Δ π).prod π) =
        Measure.sum fun g => μf (historyShapeAppend dependent j g) := by
      unfold historyMarkedReferenceRaw
      rw [Measure.prod_sum_left, Measure.map_sum (historyMarkedAppend_measurable dependent hsymm j).aemeasurable]
      have hsm : ∀ (c : ℝ≥0∞) (νs : HistoryShape (fun a b => ¬ dependent a b) → Measure (HistoryMarked dependent E)),
          c • Measure.sum νs = Measure.sum fun g => c • νs g := fun c νs => by
        ext s hs; simp only [Measure.smul_apply, Measure.sum_apply _ hs, smul_eq_mul]
        exact ENNReal.tsum_mul_left.symm
      rw [hsm]; congr 1; funext g; dsimp only [μf]
      rw [Measure.prod_smul_left, Measure.map_smul, smul_smul, hfib,
        historyShapeReferenceWeight_append, ENNReal.ofReal_mul (historyReferenceRho_pos Δ).le]
      exact (historyMarkedAppend_measurable dependent hsymm j).aemeasurable
    rw [h1]; change _ = (Measure.sum μf).restrict _
    rw [Measure.restrict_sum _ (historyMarkedTerminalSet_measurable dependent j)]
    let G := Set.range (historyShapeAppend dependent j)
    have hr (g) : (μf g).restrict (historyMarkedTerminalSet dependent j) = if g ∈ G then μf g else 0 := by
      rw [Measure.restrict_smul, Measure.restrict_map (historyMarked_measurable_mk dependent g)
        (historyMarkedTerminalSet_measurable dependent j),
        show (fun marks : Fin (historyShapeLength dependent g) → E =>
          (⟨g, marks⟩ : HistoryMarked dependent E)) ⁻¹' historyMarkedTerminalSet dependent j =
          if g ∈ G then Set.univ else ∅ by
            ext; simp only [Set.mem_preimage, historyMarkedTerminalSet, Set.mem_ofPred_eq]
            by_cases hg : g ∈ G <;> simp [G, hg]]
      by_cases hg : g ∈ G <;> simp [hg, μf]
    simp_rw [hr]
    have hsub : Measure.sum (fun g => if g ∈ G then μf g else 0) = Measure.sum fun g : G => μf g.val := by
      ext s hs; simp only [Measure.sum_apply _ hs]
      calc
        _ = ∑' i, if i ∈ G then μf i s else 0 := tsum_congr fun i => by split_ifs <;> simp
        _ = _ := by simpa [Set.indicator_apply] using (tsum_subtype G fun i => μf i s).symm
    rw [hsub]
    exact Measure.sum_comp_equiv
      (Equiv.ofInjective (historyShapeAppend dependent j) (historyShapeAppend_injective dependent hrefl hsymm j))
      fun g : G => μf g.val
  let c := (historyMarkedReferenceRaw dependent Δ π Set.univ)⁻¹
  change ENNReal.ofReal (historyReferenceRho Δ) •
    Measure.map (historyMarkedAppend dependent hsymm j) ((c • historyMarkedReferenceRaw dependent Δ π).prod π) =
      (c • historyMarkedReferenceRaw dependent Δ π).restrict _
  rw [Measure.prod_smul_left, Measure.map_smul, Measure.restrict_smul]
  swap
  · exact (historyMarkedAppend_measurable dependent hsymm j).aemeasurable
  rw [smul_smul, mul_comm, ← smul_smul, hraw]

def historyMarkedDensityDerivative (dependent : J → J → Prop) (ρ t : ℝ)
    {E : Type*} (a : E → ℝ) (h : HistoryMarked dependent E) : ℝ :=
  ρ⁻¹ * ∑ x ∈ historyMaximalPieces Finset.univ,
    historyMarkedPieceWeight dependent a h x *
      historyScaledUpperDensity (historyMarkedPieceWeight dependent a h) ρ (Finset.univ.erase x) t

theorem historyMarkedDensity_hasDerivAt (dependent : J → J → Prop) (ρ t : ℝ)
    {E : Type*} (a : E → ℝ) (h : HistoryMarked dependent E) :
    HasDerivAt (fun u => historyMarkedDensity dependent ρ u a h)
      (historyMarkedDensityDerivative dependent ρ t a h) t :=
  historyScaledUpperDensity_hasDerivAt _ ρ Finset.univ t

theorem historyMarkedDensityDerivative_bound (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (ρ t B : ℝ) (hρ : 0 < ρ) (ht : 0 ≤ t) (hB : 0 ≤ B)
    {E : Type*} [MeasurableSpace E] (a : E → ℝ) (ha : ∀ e, |a e| ≤ B)
    (hsmall : t * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2)) (h : HistoryMarked dependent E) :
    |historyMarkedDensityDerivative dependent ρ t a h| ≤
      ρ⁻¹ * (Fintype.card J : ℝ) * B * (3 / 2 : ℝ) ^ Fintype.card J := by
  classical
  let S := historyMaximalPieces (Finset.univ : Finset (WordHeapPiece h.1.out dependent))
  let C : ℝ := (3 / 2 : ℝ) ^ Fintype.card J
  have hC : 0 ≤ C := by positivity
  have hw : ∀ x ∈ S, |historyMarkedPieceWeight dependent a h x *
      historyScaledUpperDensity (historyMarkedPieceWeight dependent a h) ρ (Finset.univ.erase x) t| ≤ B * C := by
    intro x hx
    rcases h with ⟨g, marks⟩
    generalize hj : wordHeapLabel x = j
    obtain ⟨old, rfl⟩ := (historyShape_terminal_iff_maximal dependent hsymm j g).2 ⟨x, hx, hj⟩
    have hxe : x = historyCanonicalAppendedPiece dependent hsymm j old :=
      wordHeap_maximal_label_injective hrefl hsymm Finset.univ hx
        (historyCanonicalAppendedPiece_maximal dependent hsymm j old)
        (hj.trans (historyCanonicalAppendedPiece_label dependent hsymm j old).symm)
    let p := (historyCanonicalMarkAppendEquiv dependent hsymm j old (E := E)).symm marks
    have hm := (historyCanonicalMarkAppendEquiv dependent hsymm j old).apply_symm_apply marks
    have hb : (1 / 2 : ℝ) ^ Fintype.card J ≤
        historyScaledUpperDensity (historyMarkedPieceWeight dependent a ⟨_, marks⟩) ρ (Finset.univ.erase x) t ∧
        historyScaledUpperDensity (historyMarkedPieceWeight dependent a ⟨_, marks⟩) ρ (Finset.univ.erase x) t ≤ C := by
      rw [hxe, ← hm, historyCanonicalAppend_density_delete]
      exact historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels ρ t B hρ ht hB a ha hsmall ⟨old, p.2⟩
    have hn : 0 ≤ historyScaledUpperDensity (historyMarkedPieceWeight dependent a ⟨_, marks⟩) ρ (Finset.univ.erase x) t :=
      (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
    rw [abs_mul, abs_of_nonneg hn]; exact mul_le_mul (ha _) hb.2 hn hB
  have hc : (S.card : ℝ) ≤ Fintype.card J := by
    exact_mod_cast wordHeap_maximal_card_le_labels hrefl hsymm Finset.univ
  unfold historyMarkedDensityDerivative
  rw [abs_mul, abs_of_pos (inv_pos.2 hρ)]
  refine ((mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.2 hρ.le)).trans
    (by simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc] using
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hw) (inv_nonneg.2 hρ.le))).trans ?_
  change _ ≤ ρ⁻¹ * (Fintype.card J : ℝ) * B * C
  nlinarith [mul_nonneg hB hC, mul_le_mul_of_nonneg_right hc (mul_nonneg (inv_nonneg.2 hρ.le) (mul_nonneg hB hC))]

theorem historyMarkedSubdensity_fiber_measurable (dependent : J → J → Prop) (ρ t : ℝ)
    {E : Type*} [MeasurableSpace E] (a : E → ℝ) (ha : Measurable a)
    (g : HistoryShape (fun i j => ¬ dependent i j)) (S : Finset (WordHeapPiece g.out dependent)) :
    Measurable fun marks : Fin (historyShapeLength dependent g) → E =>
      historyScaledUpperDensity (historyMarkedPieceWeight dependent a ⟨g, marks⟩) ρ S t := by
  classical
  simp_rw [historyScaledUpperDensity_eq_components, historyComponentWeight]
  change Measurable fun marks : Fin (historyShapeLength dependent g) → E =>
    ∑ P ∈ historyUpperSets S, (t / ρ) ^ P.card * historyOrderVolume P *
      ∏ x ∈ P, a (marks (Fin.cast (historyShapeLength_out dependent g).symm x.position))
  exact Finset.measurable_fun_sum _ fun P _ =>
    (Finset.measurable_fun_prod _ fun x _ =>
      ha.comp (measurable_pi_apply (Fin.cast (historyShapeLength_out dependent g).symm x.position))).const_mul _

theorem historyMarkedDensityDerivative_measurable (dependent : J → J → Prop) (ρ t : ℝ)
    {E : Type*} [MeasurableSpace E] (a : E → ℝ) (ha : Measurable a) :
    Measurable (historyMarkedDensityDerivative dependent ρ t a) := by
  classical
  rw [historyMarked_measurable_iff]; intro g
  change Measurable fun marks : Fin (historyShapeLength dependent g) → E =>
    ρ⁻¹ * ∑ x ∈ historyMaximalPieces (Finset.univ : Finset (WordHeapPiece g.out dependent)),
      a (marks (Fin.cast (historyShapeLength_out dependent g).symm x.position)) *
      historyScaledUpperDensity (historyMarkedPieceWeight dependent a ⟨g, marks⟩) ρ (Finset.univ.erase x) t
  exact (Finset.measurable_fun_sum _ fun x _ =>
    (ha.comp (measurable_pi_apply (Fin.cast (historyShapeLength_out dependent g).symm x.position))).mul
      (historyMarkedSubdensity_fiber_measurable dependent ρ t a ha g (Finset.univ.erase x))).const_mul _

end MarkedAppendJ
end HistoryAppendAndDeletion

-- ============================================================================
-- 3. Cardinal Covariance, Scale Weights, Gaussian Domination, and Orthant Tails
-- ============================================================================

section CardinalAndGaussianAnalysis
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

abbrev HighFrameIndex (d D : ℕ) :=
  {γ : PolynomialBox d (D - 1) // (∑ r, (γ r).val) ≤ D - 1}

def highFrameFeature {d D : ℕ} (x : Covariate d) (γ : HighFrameIndex d D) : ℝ :=
  ∏ r, (x r / 8) ^ (γ.val r).val

def highFrameCoefficients {d D : ℕ} (P : MvPolynomial (Fin d) ℝ) (γ : HighFrameIndex d D) : ℝ :=
  P.coeff (polynomialBoxExponent γ.val)

theorem high_frame_polynomial_evaluation {d D : ℕ} (P : MvPolynomial (Fin d) ℝ)
    (hP : P.totalDegree ≤ D - 1) (x : Covariate d) :
    eval (fun r => x r / 8) P =
      ∑ γ : HighFrameIndex d D, highFrameFeature x γ * highFrameCoefficients P γ := by
  classical
  rw [polynomial_box_evaluation P hP]
  have hzero (γ : PolynomialBox d (D - 1)) (hγ : ¬ (∑ r, (γ r).val) ≤ D - 1) :
      P.coeff (polynomialBoxExponent γ) = 0 := by
    by_contra hne
    have ht := (le_totalDegree (mem_support_iff.mpr hne)).trans hP
    rw [Finsupp.sum_fintype _ _ fun _ => rfl] at ht
    simpa only [polynomial_box_exponent_apply] using hγ ht
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun γ : PolynomialBox d (D - 1) => (∑ r, (γ r).val) ≤ D - 1)
    fun γ => P.coeff (polynomialBoxExponent γ) * ∏ r, (x r / 8) ^ (γ r).val
  have hc : (∑ γ : {γ : PolynomialBox d (D - 1) // ¬ (∑ r, (γ r).val) ≤ D - 1},
      P.coeff (polynomialBoxExponent γ.val) * ∏ r, (x r / 8) ^ (γ.val r).val) = 0 :=
    Finset.sum_eq_zero fun γ _ => by rw [hzero γ.val γ.property, zero_mul]
  rw [hc, add_zero] at hsplit; rw [← hsplit]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

def spatialSquaredDistance {d : ℕ} (x y : Covariate d) : ℝ := ∑ r, (y r - x r) ^ 2

def spatialCardinalAffine {d : ℕ} (x y : Covariate d) : MvPolynomial (Fin d) ℝ :=
  ∑ r, (C ((y r - x r) * y r) - C (8 * (y r - x r)) * X r)

private lemma spatial_cardinal_affine_eval {d : ℕ} (x y u : Covariate d) :
    eval (fun r => u r / 8) (spatialCardinalAffine x y) = ∑ r, (y r - x r) * (y r - u r) := by
  simp only [spatialCardinalAffine, map_sum, map_sub, map_mul, eval_C, eval_X]
  exact Finset.sum_congr rfl fun _ _ => by ring

def spatialCardinalPolynomial {d n : ℕ} (U : Fin n → Covariate d) (i : Fin n) :
    MvPolynomial (Fin d) ℝ :=
  ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, spatialCardinalAffine (U i) (U j)

def spatialUnaryWeight {d : ℕ} (lam t : ℝ) (x y : Covariate d) : ℝ :=
  t * (lam * spatialSquaredDistance x y) ^ 2 * Real.exp (-(t * lam * spatialSquaredDistance x y))

def spatialCardinalScale {d n : ℕ} (lam : ℝ) (t : Fin n → ℝ)
    (U : Fin n → Covariate d) (i : Fin n) : ℝ :=
  ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
    t j * lam ^ 2 * Real.exp (-(t j * lam * spatialSquaredDistance (U i) (U j)))

def spatialCardinalWeight {d n : ℕ} (lam : ℝ) (t : Fin n → ℝ)
    (U : Fin n → Covariate d) (i : Fin n) : ℝ :=
  ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, spatialUnaryWeight lam (t j) (U i) (U j)

theorem spatial_frame_covariance_rank_one {κ : Type*} [Fintype κ] [DecidableEq κ]
    {n : ℕ} (v : κ → ℝ) (S : ℝ) (φ : Fin n → κ → ℝ) (i l : Fin n) :
    spatialFrameCovariance (fun β β' => S * v β * v β') φ i l =
      S * (∑ β, φ i β * v β) * (∑ β, φ l β * v β) := by
  simp only [spatialFrameCovariance, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem spatial_frame_covariance_add {κ : Type*} [Fintype κ] [DecidableEq κ]
    {n : ℕ} (A B : κ → κ → ℝ) (φ : Fin n → κ → ℝ) (i l : Fin n) :
    spatialFrameCovariance (fun β β' => A β β' + B β β') φ i l =
      spatialFrameCovariance A φ i l + spatialFrameCovariance B φ i l := by
  simp only [spatialFrameCovariance, mul_add, Finset.sum_add_distrib]

theorem spatial_frame_covariance_sum {κ J : Type*} [Fintype κ] [DecidableEq κ]
    {n : ℕ} (s : Finset J) (A : J → κ → κ → ℝ) (φ : Fin n → κ → ℝ) (i l : Fin n) :
    spatialFrameCovariance (fun β β' => ∑ j ∈ s, A j β β') φ i l =
      ∑ j ∈ s, spatialFrameCovariance (A j) φ i l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [spatialFrameCovariance]
  | @insert j s hj ih => simp only [Finset.sum_insert hj]; rw [spatial_frame_covariance_add, ih]

abbrev SpatialScaleIndex {n : ℕ} (i : Fin n) := {j : Fin n // j ≠ i}
abbrev SpatialScaleVector {n : ℕ} (i : Fin n) := SpatialScaleIndex i → ℝ

def spatialScaleExtend {n : ℕ} (i : Fin n) (t : SpatialScaleVector i) (j : Fin n) : ℝ :=
  if h : j ≠ i then t ⟨j, h⟩ else 0

def spatialScaleLogSum {n : ℕ} (i : Fin n) (t : SpatialScaleVector i) : ℝ :=
  ∑ j, Real.log (1 + max 0 (t j))

def spatialScaleDomain {n : ℕ} (i : Fin n) (T : ℝ) : Set (SpatialScaleVector i) :=
  Ici 0 ∩ {t | spatialScaleLogSum i t ≤ 2 * Real.log T}

theorem spatial_scale_domain_isClosed {n : ℕ} (i : Fin n) (T : ℝ) :
    IsClosed (spatialScaleDomain i T) :=
  isClosed_Ici.inter (isClosed_le
    (continuous_finsetSum _ fun j _ =>
      (continuous_const.add (continuous_const.max (continuous_apply j))).log fun _ => by positivity)
    continuous_const)

theorem spatial_scale_domain_subset_box {n : ℕ} (i : Fin n) (T : ℝ) (hT : 1 ≤ T) :
    spatialScaleDomain i T ⊆ Icc 0 (fun _ => T ^ 2 - 1) := fun t ht =>
  ⟨ht.1, fun j => by
    have hT0 : 0 < T := by linarith
    have hlogj := (Finset.single_le_sum
      (f := fun k : SpatialScaleIndex i => Real.log (1 + max 0 (t k)))
      (fun k _ => Real.log_nonneg (by linarith [le_max_left (0 : ℝ) (t k)]))
      (Finset.mem_univ j)).trans ht.2
    have htj : (0 : ℝ) ≤ t j := ht.1 j
    rw [max_eq_right htj] at hlogj
    have he := Real.exp_le_exp.mpr hlogj
    rw [Real.exp_log (by linarith : 0 < 1 + t j),
      show Real.exp (2 * Real.log T) = T ^ 2 by
        simpa only [Nat.cast_ofNat, Real.exp_log hT0] using Real.exp_nat_mul (Real.log T) 2] at he
    linarith⟩

theorem spatial_scale_domain_isCompact {n : ℕ} (i : Fin n) (T : ℝ) (hT : 1 ≤ T) :
    IsCompact (spatialScaleDomain i T) :=
  isCompact_Icc.of_isClosed_subset (spatial_scale_domain_isClosed i T)
    (spatial_scale_domain_subset_box i T hT)

def spatialScaleMeasure {n : ℕ} (i : Fin n) (T : ℝ) : Measure (SpatialScaleVector i) :=
  volume.restrict (spatialScaleDomain i T)

theorem spatial_scale_measure_finite {n : ℕ} (i : Fin n) (T : ℝ) (hT : 1 ≤ T) :
    IsFiniteMeasure (spatialScaleMeasure i T) :=
  isFiniteMeasure_restrict.mpr (spatial_scale_domain_isCompact i T hT).measure_ne_top

def spatialCenteredCardinalMatrix {d n D : ℕ} (i : Fin n) (lam : ℝ)
    (U : Fin n → Covariate d) (t : SpatialScaleVector i) (β β' : HighFrameIndex d D) : ℝ :=
  spatialCardinalScale lam (spatialScaleExtend i t) U i *
    highFrameCoefficients (spatialCardinalPolynomial U i) β *
    highFrameCoefficients (spatialCardinalPolynomial U i) β'

theorem spatial_centered_cardinal_scale_continuous {d n : ℕ}
    (i : Fin n) (lam : ℝ) (U : Fin n → Covariate d) :
    Continuous fun t : SpatialScaleVector i => spatialCardinalScale lam (spatialScaleExtend i t) U i := by
  have hext : Continuous (spatialScaleExtend i) := continuous_pi fun j => by
    by_cases hji : j ≠ i
    · simpa only [spatialScaleExtend, dite_eq_left hji] using continuous_apply (⟨j, hji⟩ : SpatialScaleIndex i)
    · simp only [spatialScaleExtend, dite_eq_right hji]; exact continuous_const
  unfold spatialCardinalScale
  exact continuous_finsetProd _ fun j _ =>
    (((continuous_apply j).comp hext).mul continuous_const).mul
      (Real.continuous_exp.comp (((((continuous_apply j).comp hext).mul continuous_const).mul continuous_const).neg))

theorem spatial_centered_cardinal_matrix_integrable {d n D : ℕ}
    (i : Fin n) (lam T : ℝ) (hT : 1 ≤ T) (U : Fin n → Covariate d)
    (β β' : HighFrameIndex d D) :
    Integrable (fun t => spatialCenteredCardinalMatrix i lam U t β β') (spatialScaleMeasure i T) :=
  (((spatial_centered_cardinal_scale_continuous i lam U).mul continuous_const).mul
    continuous_const).continuousOn.integrableOn_compact (spatial_scale_domain_isCompact i T hT)

def integratedCardinalMatrix {d n D : ℕ} (lam T : ℝ) (U : Fin n → Covariate d)
    (β β' : HighFrameIndex d D) : ℝ :=
  ∑ i, ∫ t, spatialCenteredCardinalMatrix i lam U t β β' ∂spatialScaleMeasure i T

def integratedCardinalWeight {d n : ℕ} (lam T : ℝ) (U : Fin n → Covariate d) (i : Fin n) : ℝ :=
  ∫ t, spatialCardinalWeight lam (spatialScaleExtend i t) U i ∂spatialScaleMeasure i T

theorem integrated_cardinal_response_heat {d n D : ℕ} (hn : n ≤ D) (q : ℕ)
    (C a V η lam T : ℝ) (hC : C ≠ 0) (hT : 1 ≤ T) (U : Fin n → Covariate d)
    (g w : Fin n → ℝ) (c : HighFrameIndex d D → ℝ) (y : Fin n → Fin 3) :
    responseMatrixAction q C (integratedCardinalMatrix lam T U) c
      (fun c => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) c y) =
      η ^ 2 * ∑ i, (w i) ^ 2 * integratedCardinalWeight lam T U i *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i +
      highResponseDefect q C a V η (integratedCardinalMatrix lam T U) g w
        (fun i => highFrameFeature (U i)) c y := by
  have hsym (β β' : HighFrameIndex d D) :
      integratedCardinalMatrix lam T U β β' = integratedCardinalMatrix lam T U β' β :=
    Finset.sum_congr rfl fun i _ => integral_congr_ae (Eventually.of_forall fun _ => by
      unfold spatialCenteredCardinalMatrix; ring)
  have hdiag (i l : Fin n) :
      spatialFrameCovariance (integratedCardinalMatrix (D := D) lam T U)
        (fun j => highFrameFeature (U j)) i l =
        if i = l then integratedCardinalWeight lam T U i else 0 := by
    have hdeg (j : Fin n) : (spatialCardinalPolynomial U j).totalDegree ≤ D - 1 :=
      ((totalDegree_finsetProd _ _).trans
        ((Finset.sum_le_sum (g := fun _ => 1) fun m _ =>
          (totalDegree_finsetSum _ _).trans (Finset.sup_le fun r _ =>
            (totalDegree_sub _ _).trans (max_le (by simp only [totalDegree_C]; omega)
              ((totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X]))))).trans_eq (by simp))).trans
        (Nat.sub_le_sub_right hn 1)
    have hcdiag (j : Fin n) (t : SpatialScaleVector j) :
        spatialFrameCovariance (spatialCenteredCardinalMatrix (D := D) j lam U t)
          (fun r => highFrameFeature (U r)) i l =
          if j = i ∧ i = l then spatialCardinalWeight lam (spatialScaleExtend j t) U j else 0 := by
      unfold spatialCenteredCardinalMatrix
      rw [spatial_frame_covariance_rank_one, ← high_frame_polynomial_evaluation _ (hdeg j),
        ← high_frame_polynomial_evaluation _ (hdeg j)]
      have hnb (p q₀ : Fin n) (hpq : q₀ ≠ p) : eval (fun r => U q₀ r / 8) (spatialCardinalPolynomial U p) = 0 := by
        rw [spatialCardinalPolynomial, map_prod]
        exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hpq, Finset.mem_univ q₀⟩)
          (by rw [spatial_cardinal_affine_eval]; simp)
      by_cases hji : j = i
      · subst j; by_cases hil : i = l
        · subst l; rw [ite_eq_left ⟨rfl, rfl⟩]
          have hct : eval (fun r => U i r / 8) (spatialCardinalPolynomial U i) =
              ∏ m ∈ (Finset.univ : Finset (Fin n)).erase i, spatialSquaredDistance (U i) (U m) := by
            simp only [spatialCardinalPolynomial, map_prod, spatial_cardinal_affine_eval, spatialSquaredDistance, pow_two]
          rw [mul_assoc, ← sq, hct, ← Finset.prod_pow]
          unfold spatialCardinalScale spatialCardinalWeight
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun _ _ => by unfold spatialUnaryWeight; ring
        · rw [ite_eq_right (by tauto), hnb i l (Ne.symm hil), mul_zero]
      · rw [ite_eq_right (by tauto), hnb j i (Ne.symm hji), mul_zero, zero_mul]
    unfold integratedCardinalMatrix
    rw [spatial_frame_covariance_sum]
    simp_rw [show ∀ j : Fin n,
      spatialFrameCovariance (fun β β' => ∫ t, spatialCenteredCardinalMatrix (D := D) j lam U t β β' ∂spatialScaleMeasure j T)
        (fun m => highFrameFeature (U m)) i l =
      ∫ t, spatialFrameCovariance (spatialCenteredCardinalMatrix (D := D) j lam U t)
        (fun m => highFrameFeature (U m)) i l ∂spatialScaleMeasure j T from fun j => by
          unfold spatialFrameCovariance
          rw [integral_finsetSum _ fun β _ => integrable_finsetSum _ fun β' _ =>
            (spatial_centered_cardinal_matrix_integrable j lam T hT U β β').const_mul _]
          refine Finset.sum_congr rfl fun β _ => ?_
          rw [integral_finsetSum _ fun β' _ =>
            (spatial_centered_cardinal_matrix_integrable j lam T hT U β β').const_mul _]
          exact Finset.sum_congr rfl fun _ _ => by rw [integral_const_mul], hcdiag]
    rw [Finset.sum_eq_single i]
    · by_cases hil : i = l
      · subst hil; simp only [and_self, ite_true, integratedCardinalWeight]
      · simp only [hil, and_false, ite_false, integral_zero]
    · intro j _ hji; simp only [hji, false_and, ite_false, integral_zero]
    · simp
  exact high_response_matrix_heat_with_defect q C a V η _ hC hsym g w _ c y _ hdiag

-- Scale weights, Gaussian domination, Gamma tails, and exponential orthant tails

private def unaryScaleDensity (alpha t : ℝ) : ℝ := t * alpha ^ 2 * Real.exp (-(alpha * t))

private lemma unary_scale_density_props (alpha : ℝ) (ha : 0 ≤ alpha) :
    IntegrableOn (unaryScaleDensity alpha) (Ici (0 : ℝ)) ∧
      (∫ t in Ici (0 : ℝ), unaryScaleDensity alpha t) = if alpha = 0 then 0 else 1 := by
  refine ⟨?_, ?_⟩
  · rcases eq_or_lt_of_le ha with rfl | hpos
    · change Integrable (fun t : ℝ => t * 0 ^ 2 * Real.exp (-(0 * t))) (volume.restrict (Ici 0))
      simpa using (integrable_zero ℝ ℝ : Integrable (fun _ : ℝ => (0 : ℝ)) (volume.restrict (Ici 0)))
    · rw [integrableOn_Ici_iff_integrableOn_Ioi]
      have h := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := alpha)
        (by norm_num) (by norm_num) hpos).const_mul (alpha ^ 2)
      change Integrable (fun t => t * alpha ^ 2 * Real.exp (-(alpha * t))) (volume.restrict (Ioi 0))
      convert h using 1
      funext t; simp only [Real.rpow_one]; ring
  · by_cases hzero : alpha = 0
    · simp [unaryScaleDensity, hzero]
    · have hpos : 0 < alpha := lt_of_le_of_ne ha (Ne.symm hzero)
      have hGamma := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := alpha) (by norm_num) hpos
      rw [show unaryScaleDensity alpha = fun t => alpha ^ 2 * (t * Real.exp (-(alpha * t))) from
        funext fun _ => by unfold unaryScaleDensity; ring,
        integral_Ici_eq_integral_Ioi, integral_const_mul, ite_eq_right hzero]
      norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] at hGamma
      have hG2 : Real.Gamma 2 = 1 := by simpa using Real.Gamma_nat_eq_factorial 1
      rw [hGamma, hG2, mul_one, Real.rpow_two]; field_simp

theorem spatial_cardinal_weight_scale_product {d n : ℕ} (i : Fin n) (lam : ℝ)
    (U : Fin n → Covariate d) (t : SpatialScaleVector i) :
    spatialCardinalWeight lam (spatialScaleExtend i t) U i =
      ∏ j : SpatialScaleIndex i, spatialUnaryWeight lam (t j) (U i) (U j.val) := by
  unfold spatialCardinalWeight
  rw [Finset.prod_subtype (p := fun j : Fin n => j ≠ i) ((Finset.univ : Finset (Fin n)).erase i)
    (fun _ => by simp) fun j : Fin n => spatialUnaryWeight lam (spatialScaleExtend i t j) (U i) (U j)]
  exact Finset.prod_congr rfl fun j _ => by simp only [spatialScaleExtend, dite_eq_left j.property]

private lemma spatial_scale_orthant_measure {n : ℕ} (i : Fin n) :
    (volume : Measure (SpatialScaleVector i)).restrict (Ici 0) =
      Measure.pi fun _ : SpatialScaleIndex i => volume.restrict (Ici (0 : ℝ)) := by
  rw [show Ici (0 : SpatialScaleVector i) = Set.univ.pi fun _ => Ici (0 : ℝ) by
    ext; simp only [mem_Ici, Set.mem_pi, mem_univ, forall_true_left]; rfl]
  exact Measure.restrict_pi_pi (μ := fun _ : SpatialScaleIndex i => (volume : Measure ℝ)) _

theorem spatial_cardinal_weight_orthant_integrable {d n : ℕ} (i : Fin n)
    (lam : ℝ) (hlam : 0 ≤ lam) (U : Fin n → Covariate d) :
    Integrable (fun t => spatialCardinalWeight lam (spatialScaleExtend i t) U i)
      (volume.restrict (Ici (0 : SpatialScaleVector i))) := by
  simp_rw [spatial_cardinal_weight_scale_product]; rw [spatial_scale_orthant_measure]
  exact Integrable.fintype_prod (𝕜 := ℝ)
    (f := fun (j : SpatialScaleIndex i) (t : ℝ) => spatialUnaryWeight lam t (U i) (U j.val))
    (μ := fun _ : SpatialScaleIndex i => volume.restrict (Ici (0 : ℝ))) fun j => by
      rw [show (fun t => spatialUnaryWeight lam t (U i) (U j.val)) =
        unaryScaleDensity (lam * spatialSquaredDistance (U i) (U j.val)) from
          funext fun _ => by unfold spatialUnaryWeight unaryScaleDensity; congr 1; ring]
      exact (unary_scale_density_props _ (mul_nonneg hlam (Finset.sum_nonneg fun _ _ => sq_nonneg _))).1

theorem spatial_cardinal_weight_orthant_nonnegative {d n : ℕ} (i : Fin n)
    (lam : ℝ) (U : Fin n → Covariate d) :
    0 ≤ᵐ[volume.restrict (Ici (0 : SpatialScaleVector i))]
      fun t => spatialCardinalWeight lam (spatialScaleExtend i t) U i := by
  filter_upwards [ae_restrict_mem (measurableSet_Ici : MeasurableSet (Ici (0 : SpatialScaleVector i)))] with t ht
  rw [spatial_cardinal_weight_scale_product]
  exact Finset.prod_nonneg fun j _ => by have : (0 : ℝ) ≤ t j := ht j; unfold spatialUnaryWeight; positivity

theorem spatial_cardinal_weight_orthant_integral_le_one {d n : ℕ} (i : Fin n)
    (lam : ℝ) (hlam : 0 ≤ lam) (U : Fin n → Covariate d) :
    (∫ t, spatialCardinalWeight lam (spatialScaleExtend i t) U i
      ∂volume.restrict (Ici (0 : SpatialScaleVector i))) ≤ 1 := by
  simp_rw [spatial_cardinal_weight_scale_product]
  rw [spatial_scale_orthant_measure, integral_fintype_prod_eq_prod
    (μ := fun _ : SpatialScaleIndex i => volume.restrict (Ici (0 : ℝ)))
    fun (j : SpatialScaleIndex i) (t : ℝ) => spatialUnaryWeight lam t (U i) (U j.val)]
  refine (Finset.prod_le_prod₀ (g := fun _ => (1 : ℝ)) (fun j _ => integral_nonneg_of_ae <| by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t (ht : (0 : ℝ) ≤ t)
      unfold spatialUnaryWeight; positivity)
    fun j _ => ?_).trans_eq Finset.prod_const_one
  have hdist : 0 ≤ spatialSquaredDistance (U i) (U j.val) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [show (fun t => spatialUnaryWeight lam t (U i) (U j.val)) =
    unaryScaleDensity (lam * spatialSquaredDistance (U i) (U j.val)) from
      funext fun _ => by unfold spatialUnaryWeight unaryScaleDensity; congr 1; ring]
  change (∫ t in Ici (0 : ℝ), unaryScaleDensity (lam * spatialSquaredDistance (U i) (U j.val)) t) ≤ 1
  rw [(unary_scale_density_props _ (mul_nonneg hlam hdist)).2]
  split_ifs <;> norm_num

theorem integrated_cardinal_weight_mem_unit {d n : ℕ} (i : Fin n)
    (lam T : ℝ) (hlam : 0 ≤ lam) (U : Fin n → Covariate d) :
    integratedCardinalWeight lam T U i ∈ Icc (0 : ℝ) 1 := by
  have hnn := spatial_cardinal_weight_orthant_nonnegative i lam U
  have hμ : spatialScaleMeasure i T ≤ volume.restrict (Ici (0 : SpatialScaleVector i)) :=
    Measure.restrict_mono_set _ fun _ ht => ht.1
  exact ⟨integral_nonneg_of_ae (hnn.filter_mono (ae_mono hμ)),
    (integral_mono_measure hμ hnn (spatial_cardinal_weight_orthant_integrable i lam hlam U)).trans
      (spatial_cardinal_weight_orthant_integral_le_one i lam hlam U)⟩

theorem spatial_scale_domain_mono {n : ℕ} (i : Fin n) {L T : ℝ}
    (hL : 0 < L) (hLT : L ≤ T) : spatialScaleDomain i L ⊆ spatialScaleDomain i T :=
  fun _ ht => ⟨ht.1, (ht.2 : spatialScaleLogSum i _ ≤ _).trans
    (mul_le_mul_of_nonneg_left (Real.log_le_log hL hLT) (by norm_num))⟩

theorem integrated_cardinal_matrix_one_eq_zero {d n D : ℕ} (hn : 2 ≤ n)
    (lam : ℝ) (U : Fin n → Covariate d) : integratedCardinalMatrix (D := D) lam 1 U = 0 := by
  funext β β'; unfold integratedCardinalMatrix
  have hm0 (i : Fin n) : spatialScaleMeasure i 1 = 0 := by
    letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
    obtain ⟨j, hji⟩ := exists_ne i
    letI : Nonempty (SpatialScaleIndex i) := ⟨⟨j, hji⟩⟩
    have hd1 : spatialScaleDomain i 1 = {0} := by
      ext t; refine ⟨fun ht => mem_singleton_iff.mpr <| funext fun k => ?_, ?_⟩
      · have hs := spatial_scale_domain_subset_box i 1 le_rfl ht
        have hl : (0 : ℝ) ≤ t k := hs.1 k; have hh : t k ≤ (1 : ℝ) ^ 2 - 1 := hs.2 k
        norm_num at hh; exact le_antisymm hh hl
      · rintro rfl; exact ⟨show (0 : SpatialScaleVector i) ≤ 0 from le_rfl, by simp [spatialScaleLogSum]⟩
    unfold spatialScaleMeasure; rw [hd1]
    exact Measure.restrict_eq_zero.mpr (measure_singleton (0 : SpatialScaleVector i))
  simp_rw [hm0, integral_zero_measure]; exact Finset.sum_const_zero

theorem integrated_cardinal_weight_defect_eq_complement {d n : ℕ} (i : Fin n)
    (lam T : ℝ) (hlam : 0 < lam) (U : Fin n → Covariate d)
    (hU : ∀ j, j ≠ i → U i ≠ U j) :
    1 - integratedCardinalWeight lam T U i =
      ∫ t, spatialCardinalWeight lam (spatialScaleExtend i t) U i
        ∂volume.restrict ((Ici (0 : SpatialScaleVector i)) \ spatialScaleDomain i T) := by
  have hdom := (spatial_scale_domain_isClosed i T).measurableSet
  have h := integral_add_compl hdom (spatial_cardinal_weight_orthant_integrable i lam hlam.le U)
  have h1 : (∫ t, spatialCardinalWeight lam (spatialScaleExtend i t) U i
      ∂volume.restrict (Ici (0 : SpatialScaleVector i))) = 1 := by
    simp_rw [spatial_cardinal_weight_scale_product]
    rw [spatial_scale_orthant_measure, integral_fintype_prod_eq_prod
      (μ := fun _ : SpatialScaleIndex i => volume.restrict (Ici (0 : ℝ)))
      fun (j : SpatialScaleIndex i) (t : ℝ) => spatialUnaryWeight lam t (U i) (U j.val)]
    refine Finset.prod_eq_one fun j _ => ?_
    have hxy := hU j.val j.property
    obtain ⟨r, hr⟩ : ∃ r, U i r ≠ U j.val r := by by_contra hn; push Not at hn; exact hxy (funext hn)
    have ha : 0 < lam * spatialSquaredDistance (U i) (U j.val) :=
      mul_pos hlam (Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨r, Finset.mem_univ r, sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm hr))⟩)
    rw [show (fun t => spatialUnaryWeight lam t (U i) (U j.val)) =
      unaryScaleDensity (lam * spatialSquaredDistance (U i) (U j.val)) from
        funext fun _ => by unfold spatialUnaryWeight unaryScaleDensity; congr 1; ring]
    change (∫ t in Ici (0 : ℝ), unaryScaleDensity (lam * spatialSquaredDistance (U i) (U j.val)) t) = 1
    rw [(unary_scale_density_props _ ha.le).2, ite_eq_right ha.ne']
  rw [Measure.restrict_restrict_of_subset (fun _ ht => ht.1 : spatialScaleDomain i T ⊆ Ici 0),
    show (volume.restrict (Ici (0 : SpatialScaleVector i))).restrict (spatialScaleDomain i T)ᶜ =
      volume.restrict ((Ici (0 : SpatialScaleVector i)) \ spatialScaleDomain i T) by
      rw [Measure.restrict_restrict hdom.compl]; congr 1; ext
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_diff]; tauto,
    h1] at h
  change integratedCardinalWeight lam T U i + _ = 1 at h; linarith

def spatialPatchBox (d : ℕ) : Set (Covariate d) := Icc (fun _ => -1) (fun _ => 1)

def spatialInterpolationLambda (d : ℕ) : ℝ := 1 / (8 * (d : ℝ))

def spatialUnaryIntegralConstant (d : ℕ) : ℝ :=
  8 * Real.exp (1 / 2) * (Real.sqrt (2 * Real.pi / spatialInterpolationLambda d)) ^ d

private lemma radial_gaussian_props {d : ℕ} (b : ℝ) (hb : 0 < b) (x : Covariate d) :
    Integrable (fun y => Real.exp (-b * spatialSquaredDistance x y)) volume ∧
      (∫ y, Real.exp (-b * spatialSquaredDistance x y)) = (Real.sqrt (Real.pi / b)) ^ d := by
  have hfac (y : Covariate d) : Real.exp (-b * spatialSquaredDistance x y) =
      ∏ r, Real.exp (-b * (y r - x r) ^ 2) := by
    unfold spatialSquaredDistance; rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [hfac]
  refine ⟨Integrable.fintype_prod (𝕜 := ℝ)
    (f := fun (r : Fin d) (y : ℝ) => Real.exp (-b * (y - x r) ^ 2))
    (μ := fun _ : Fin d => (volume : Measure ℝ))
    fun r => (integrable_exp_neg_mul_sq hb).comp_sub_right (x r), ?_⟩
  rw [integral_fintype_prod_volume_eq_prod fun (r : Fin d) (y : ℝ) => Real.exp (-b * (y - x r) ^ 2)]
  simp_rw [integral_sub_right_eq_self (μ := volume) fun y : ℝ => Real.exp (-b * y ^ 2), integral_gaussian]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private lemma radial_gaussian_scale_normalization (d : ℕ) (lam t : ℝ) (hlam : 0 < lam) (ht : 0 ≤ t) :
    (Real.sqrt (Real.pi / (lam * (1 + t) / 2))) ^ d =
      (Real.sqrt (2 * Real.pi / lam)) ^ d * (1 + t) ^ (-(d : ℝ) / 2) := by
  have hs : 0 < 1 + t := by linarith
  rw [show Real.pi / (lam * (1 + t) / 2) = (2 * Real.pi / lam) / (1 + t) by field_simp,
    Real.sqrt_div (by positivity), div_pow,
    show (Real.sqrt (1 + t)) ^ d = (1 + t) ^ ((d : ℝ) / 2) by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((1 + t) ^ (1 / 2 : ℝ)) d, ← Real.rpow_mul hs.le]; congr 1; ring,
    show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring, Real.rpow_neg hs.le, div_eq_mul_inv]

private lemma spatial_patch_alpha_bounds {d : ℕ} (hd : 0 < d) (x y : Covariate d)
    (hx : x ∈ spatialPatchBox d) (hy : y ∈ spatialPatchBox d) :
    0 ≤ spatialInterpolationLambda d * spatialSquaredDistance x y ∧
      spatialInterpolationLambda d * spatialSquaredDistance x y ≤ 1 / 2 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdu : spatialSquaredDistance x y ≤ 4 * d := by
    unfold spatialSquaredDistance
    refine (Finset.sum_le_sum (g := fun _ => (4 : ℝ)) fun r _ => ?_).trans_eq (by simp [mul_comm])
    have hxr : |x r| ≤ 1 := abs_le.mpr ⟨hx.1 r, hx.2 r⟩
    have hyr : |y r| ≤ 1 := abs_le.mpr ⟨hy.1 r, hy.2 r⟩
    have hsub : |y r - x r| ≤ 2 := (abs_sub _ _).trans (by linarith)
    simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using pow_le_pow_left₀ (abs_nonneg _) hsub 2
  have hdl : 0 ≤ spatialSquaredDistance x y := Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact ⟨by unfold spatialInterpolationLambda; positivity,
    by unfold spatialInterpolationLambda; rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]; linarith⟩

theorem spatial_unary_patch_integral_decay {d : ℕ} (hd : 0 < d)
    (t : ℝ) (ht : 0 ≤ t) (x : Covariate d) (hx : x ∈ spatialPatchBox d) :
    (∫ y in spatialPatchBox d, spatialUnaryWeight (spatialInterpolationLambda d) t x y) ≤
      spatialUnaryIntegralConstant d * (1 + t) ^ (-(d : ℝ) / 2 - 1) := by
  let lam := spatialInterpolationLambda d
  let b := lam * (1 + t) / 2
  let A := 8 * Real.exp (1 / 2) / (1 + t)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hlam : 0 < lam := by dsimp [lam, spatialInterpolationLambda]; positivity
  have hs : 0 < 1 + t := by linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hrg := radial_gaussian_props b hb x
  have hInt := hrg.1.const_mul A
  have hActual : IntegrableOn (fun y => spatialUnaryWeight lam t x y) (spatialPatchBox d) :=
    (by unfold spatialUnaryWeight spatialSquaredDistance; fun_prop : Continuous _).continuousOn.integrableOn_compact isCompact_Icc
  have hbound (y : Covariate d) (hy : y ∈ spatialPatchBox d) :
      spatialUnaryWeight lam t x y ≤ A * Real.exp (-b * spatialSquaredDistance x y) := by
    obtain ⟨ha, haHalf⟩ := spatial_patch_alpha_bounds hd x y hx hy
    let alpha := lam * spatialSquaredDistance x y
    let z := (1 + t) * alpha / 2
    have hpow := Real.pow_div_factorial_le_exp z (by dsimp [z]; positivity) 2
    norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, mul_one] at hpow
    have hAbs := mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg (-2 * z))
    rw [← Real.exp_add, show z + -2 * z = -z by ring, show -2 * z = -((1 + t) * alpha) by dsimp [z]; ring] at hAbs
    have hscaled := mul_le_mul_of_nonneg_left (show z ^ 2 * Real.exp (-((1 + t) * alpha)) ≤ 2 * Real.exp (-z) by linarith)
      (by positivity : 0 ≤ 4 / (1 + t) ^ 2)
    rw [show 4 / (1 + t) ^ 2 * (z ^ 2 * Real.exp (-((1 + t) * alpha))) =
      alpha ^ 2 * Real.exp (-((1 + t) * alpha)) by dsimp [z]; field_simp; ring] at hscaled
    have hmain : alpha ^ 2 * Real.exp (-((1 + t) * alpha)) ≤ 8 / (1 + t) ^ 2 * Real.exp (-z) :=
      hscaled.trans_eq (by ring)
    have hratio : t / (1 + t) ^ 2 ≤ 1 / (1 + t) := (div_le_div_iff₀ (sq_pos_of_pos hs) hs).mpr (by nlinarith)
    have hr2 := mul_le_mul_of_nonneg_right hratio (by positivity : 0 ≤ 8 * Real.exp (1 / 2) * Real.exp (-z))
    calc
      spatialUnaryWeight lam t x y = t * Real.exp alpha * (alpha ^ 2 * Real.exp (-((1 + t) * alpha))) := by
        unfold spatialUnaryWeight; dsimp [alpha]
        rw [show -(t * lam * spatialSquaredDistance x y) = lam * spatialSquaredDistance x y + -((1 + t) * (lam * spatialSquaredDistance x y)) by ring,
          Real.exp_add]; ring
      _ ≤ t * Real.exp (1 / 2) * (8 / (1 + t) ^ 2 * Real.exp (-z)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr haHalf) ht) hmain (by positivity) (by positivity)
      _ ≤ A * Real.exp (-z) := by dsimp [A]; convert hr2 using 1 <;> ring
      _ = A * Real.exp (-b * spatialSquaredDistance x y) := by
        congr 2; dsimp [z, alpha, b]; ring
  calc
    (∫ y in spatialPatchBox d, spatialUnaryWeight lam t x y) ≤
        ∫ y in spatialPatchBox d, A * Real.exp (-b * spatialSquaredDistance x y) :=
      setIntegral_mono_on hActual hInt.integrableOn measurableSet_Icc hbound
    _ ≤ ∫ y, A * Real.exp (-b * spatialSquaredDistance x y) :=
      integral_mono_measure Measure.restrict_le_self (ae_of_all _ fun _ => by dsimp [A]; positivity) hInt
    _ = A * (Real.sqrt (Real.pi / b)) ^ d := by rw [integral_const_mul, hrg.2]
    _ = _ := by
      rw [radial_gaussian_scale_normalization d lam t hlam ht]
      unfold spatialUnaryIntegralConstant; dsimp [A, lam]
      rw [Real.rpow_sub hs, Real.rpow_one]; ring

theorem spatial_scale_exponential_patch_integral_decay {d : ℕ} (hd : 0 < d)
    (t : ℝ) (ht : 0 ≤ t) (x : Covariate d) (hx : x ∈ spatialPatchBox d) :
    (∫ y in spatialPatchBox d,
      t * Real.exp (-(t * spatialInterpolationLambda d * spatialSquaredDistance x y))) ≤
      (Real.exp (1 / 2) * (Real.sqrt (2 * Real.pi / spatialInterpolationLambda d)) ^ d) *
        (1 + t) ^ (1 - (d : ℝ) / 2) := by
  let lam := spatialInterpolationLambda d
  let b := lam * (1 + t) / 2
  let A := t * Real.exp (1 / 2)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hlam : 0 < lam := by dsimp [lam, spatialInterpolationLambda]; positivity
  have hs : 0 < 1 + t := by linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hrg := radial_gaussian_props b hb x
  have hInt := hrg.1.const_mul A
  have hActual : IntegrableOn (fun y => t * Real.exp (-(t * lam * spatialSquaredDistance x y))) (spatialPatchBox d) :=
    (by unfold spatialSquaredDistance; fun_prop : Continuous _).continuousOn.integrableOn_compact isCompact_Icc
  have hBound (y : Covariate d) (hy : y ∈ spatialPatchBox d) :
      t * Real.exp (-(t * lam * spatialSquaredDistance x y)) ≤ A * Real.exp (-b * spatialSquaredDistance x y) := by
    obtain ⟨_, haHalf⟩ := spatial_patch_alpha_bounds hd x y hx hy
    have h := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by dsimp [b, lam]; nlinarith : -(t * lam * spatialSquaredDistance x y) ≤ 1 / 2 + -b * spatialSquaredDistance x y)) ht
    rw [Real.exp_add] at h; exact h.trans_eq (by dsimp [A]; ring)
  calc
    _ ≤ ∫ y in spatialPatchBox d, A * Real.exp (-b * spatialSquaredDistance x y) :=
      setIntegral_mono_on hActual hInt.integrableOn measurableSet_Icc hBound
    _ ≤ ∫ y, A * Real.exp (-b * spatialSquaredDistance x y) :=
      integral_mono_measure Measure.restrict_le_self (ae_of_all _ fun _ => by dsimp [A]; positivity) hInt
    _ = A * ((Real.sqrt (2 * Real.pi / lam)) ^ d * (1 + t) ^ (-(d : ℝ) / 2)) := by
      rw [integral_const_mul, hrg.2, radial_gaussian_scale_normalization d lam t hlam ht]
    _ ≤ _ := by
      rw [Real.rpow_sub hs, Real.rpow_one, show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring, Real.rpow_neg hs.le]
      have h := mul_le_mul_of_nonneg_right (by linarith : t ≤ 1 + t)
        (by positivity : 0 ≤ Real.exp (1 / 2) * (Real.sqrt (2 * Real.pi / lam)) ^ d / (1 + t) ^ ((d : ℝ) / 2))
      dsimp [A, lam]; convert h using 1 <;> ring

-- Gamma tails and exponential orthant tails

theorem gamma_monomial_integrable {b : ℝ} (hb : 0 < b) (r : ℕ) :
    IntegrableOn (fun v : ℝ => v ^ r * Real.exp (-(b * v))) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using
    integrableOn_rpow_mul_exp_neg_mul_rpow (s := (r : ℝ)) (p := 1) (b := b)
      (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg r)) (by norm_num) hb

theorem gamma_monomial_integral {b : ℝ} (hb : 0 < b) (r : ℕ) :
    (∫ v : ℝ in Ici 0, v ^ r * Real.exp (-(b * v))) = (r.factorial : ℝ) / b ^ (r + 1) := by
  rw [integral_Ici_eq_integral_Ioi]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (r : ℝ) + 1) (r := b) (by positivity) hb
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  rw [h, show (r : ℝ) + 1 = ((r + 1 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_pow, one_pow]
  field_simp

theorem gamma_polynomial_tail_integral {b : ℝ} (hb : 0 < b) (A : ℝ) (m : ℕ) :
    (∫ u : ℝ in Ici A, u ^ m * Real.exp (-(b * u)) / (m.factorial : ℝ)) =
      Real.exp (-(b * A)) *
        ∑ l ∈ Finset.range (m + 1), A ^ l / ((l.factorial : ℝ) * b ^ (m + 1 - l)) := by
  have hp := (measurePreserving_add_left (volume : Measure ℝ) A).restrict_preimage (s := Ici A) measurableSet_Ici
  rw [show (fun v : ℝ => A + v) ⁻¹' Ici A = Ici 0 by
    ext; simp only [mem_preimage, mem_Ici]; constructor <;> intro h <;> linarith] at hp
  rw [← hp.integral_comp (MeasurableEquiv.addLeft A).measurableEmbedding
      fun u : ℝ => u ^ m * Real.exp (-(b * u)) / (m.factorial : ℝ),
    show (fun v : ℝ => (A + v) ^ m * Real.exp (-(b * (A + v))) / (m.factorial : ℝ)) =
      fun v => (Real.exp (-(b * A)) / (m.factorial : ℝ)) *
        ∑ l ∈ Finset.range (m + 1), (A ^ l * (m.choose l : ℝ)) * (v ^ (m - l) * Real.exp (-(b * v))) from
      funext fun v => by
        rw [show -(b * (A + v)) = -(b * A) + -(b * v) by ring, Real.exp_add, add_pow,
          Finset.sum_mul, Finset.sum_div, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring,
    integral_const_mul, integral_finsetSum _ fun l _ => (gamma_monomial_integrable hb (m - l)).const_mul _]
  simp_rw [integral_const_mul, gamma_monomial_integral hb]
  rw [div_mul_eq_mul_div, div_eq_mul_inv, mul_assoc]; congr 1; rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hlm : l ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
  have hf : (m.factorial : ℝ) ≠ 0 := by positivity
  have hfl : (l.factorial : ℝ) ≠ 0 := by positivity
  have hfr : ((m - l).factorial : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_choose ℝ hlm, show m + 1 - l = (m - l) + 1 by omega]
  field_simp [hb.ne']

theorem gamma_polynomial_tail_integrable {b : ℝ} (hb : 0 < b) (A : ℝ) (m : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ m * Real.exp (-(b * u)) / (m.factorial : ℝ)) (Ici A) := by
  have hp := (measurePreserving_add_left (volume : Measure ℝ) A).restrict_preimage (s := Ici A) measurableSet_Ici
  rw [show (fun v : ℝ => A + v) ⁻¹' Ici A = Ici 0 by
    ext; simp only [mem_preimage, mem_Ici]; constructor <;> intro h <;> linarith] at hp
  refine (hp.integrable_comp_emb (MeasurableEquiv.addLeft A).measurableEmbedding).mp ?_
  have htm : IntegrableOn (fun v : ℝ => (A + v) ^ m * Real.exp (-(b * v))) (Ici 0) := by
    rw [show (fun v : ℝ => (A + v) ^ m * Real.exp (-(b * v))) =
      fun v => ∑ l ∈ Finset.range (m + 1), (A ^ l * (m.choose l : ℝ)) * (v ^ (m - l) * Real.exp (-(b * v))) from
        funext fun _ => by rw [add_pow, Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring]
    exact integrable_finsetSum _ fun l _ => (gamma_monomial_integrable hb (m - l)).const_mul _
  convert htm.const_mul (Real.exp (-(b * A)) / (m.factorial : ℝ)) using 1
  funext v; simp only [Function.comp_apply]
  rw [show -(b * (A + v)) = -(b * A) + -(b * v) by ring, Real.exp_add]; ring

section OrthantTail
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def exponentialOrthantMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι => volume.restrict (Ici (0 : ℝ))

instance exponentialOrthantMeasure_sigmaFinite : SigmaFinite (exponentialOrthantMeasure ι) := by
  unfold exponentialOrthantMeasure; infer_instance

theorem exponential_orthant_measure_eq_restrict :
    exponentialOrthantMeasure ι = volume.restrict (Ici (0 : ι → ℝ)) := by
  rw [show Ici (0 : ι → ℝ) = Set.univ.pi fun _ : ι => Ici (0 : ℝ) by
    ext; simp only [mem_Ici, Set.mem_pi, mem_univ, forall_true_left]; rfl]
  exact (Measure.restrict_pi_pi (μ := fun _ : ι => (volume : Measure ℝ)) _).symm

theorem orthant_cube_indicator_integrable (A C : ℝ) :
    Integrable ((Icc (0 : ι → ℝ) fun _ => A).indicator fun _ => C) (exponentialOrthantMeasure ι) := by
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  rw [IntegrableOn, exponential_orthant_measure_eq_restrict, Measure.restrict_restrict_of_subset fun _ hs => hs.1]
  exact integrableOn_const isCompact_Icc.measure_lt_top.ne

theorem orthant_cube_indicator_integral {A : ℝ} (hA : 0 ≤ A) (C : ℝ) :
    (∫ s : ι → ℝ, (Icc (0 : ι → ℝ) fun _ => A).indicator (fun _ => C) s
      ∂exponentialOrthantMeasure ι) = A ^ Fintype.card ι * C := by
  rw [integral_indicator measurableSet_Icc, exponential_orthant_measure_eq_restrict,
    Measure.restrict_restrict_of_subset fun _ hs => hs.1, integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul,
    Real.volume_Icc_pi_toReal (a := (0 : ι → ℝ)) (b := fun _ => A) fun _ => hA,
    Pi.zero_apply, sub_zero, Finset.prod_const, Finset.card_univ]

private def orthantExponential (b : ℝ) (s : ι → ℝ) : ℝ := Real.exp (-(b * ∑ j, s j))
private def orthantHeadTail (b A : ℝ) (s : ι → ℝ) : ℝ := Real.exp (-(b * max A (∑ j, s j))) / b
private def orthantCoordinateTail (b A : ℝ) (j : ι) (s : ι → ℝ) : ℝ :=
  ∏ l, if l = j then (Ioi A).indicator (fun v : ℝ => Real.exp (-(b * v))) (s l) else Real.exp (-(b * s l))
private def orthantSumTail (b A : ℝ) (z : ℝ × (ι → ℝ)) : ℝ :=
  if A ≤ z.1 + ∑ j, z.2 j then Real.exp (-(b * (z.1 + ∑ j, z.2 j))) else 0

private lemma orthant_sum_tail_integrable {b : ℝ} (hb : 0 < b) (A : ℝ) :
    Integrable (orthantSumTail b A : (ℝ × (ι → ℝ)) → ℝ)
      ((volume.restrict (Ici (0 : ℝ))).prod (exponentialOrthantMeasure ι)) := by
  have hsI : IntegrableOn (fun v : ℝ => Real.exp (-(b * v))) (Ici 0) := by
    simpa only [pow_zero, one_mul] using gamma_monomial_integrable hb 0
  have hoI : Integrable (orthantExponential b : (ι → ℝ) → ℝ) (exponentialOrthantMeasure ι) := by
    change Integrable (fun s : ι → ℝ => orthantExponential b s) _
    simp_rw [show ∀ s : ι → ℝ, orthantExponential b s = ∏ j, Real.exp (-(b * s j)) from fun _ => by
      unfold orthantExponential; rw [← Real.exp_sum]; congr 1; rw [Finset.mul_sum, Finset.sum_neg_distrib]]
    exact Integrable.fintype_prod (𝕜 := ℝ) (f := fun (_ : ι) (v : ℝ) => Real.exp (-(b * v)))
      (μ := fun _ : ι => volume.restrict (Ici (0 : ℝ))) fun _ => hsI
  have hbase := hsI.mul_prod hoI
  rw [show (fun z : ℝ × (ι → ℝ) => Real.exp (-(b * z.1)) * orthantExponential b z.2) =
    fun z => Real.exp (-(b * (z.1 + ∑ j, z.2 j))) from funext fun _ => by
      unfold orthantExponential; rw [← Real.exp_add]; congr 1; ring] at hbase
  have hmeas : MeasurableSet {z : ℝ × (ι → ℝ) | A ≤ z.1 + ∑ j, z.2 j} :=
    measurableSet_le measurable_const
      (measurable_fst.add (Finset.measurable_sum Finset.univ fun j _ => (measurable_pi_apply j).comp measurable_snd))
  convert hbase.indicator hmeas using 1
  funext; simp only [orthantSumTail, Set.indicator, mem_setOf_eq]

def finiteOrthantTail {q : ℕ} (b A : ℝ) (s : Fin q → ℝ) : ℝ :=
  if A ≤ ∑ j, s j then Real.exp (-(b * ∑ j, s j)) else 0

theorem finite_orthant_tail_integrable {m : ℕ} {b : ℝ} (hb : 0 < b) (A : ℝ) :
    Integrable (finiteOrthantTail b A : (Fin (m + 1) → ℝ) → ℝ)
      (exponentialOrthantMeasure (Fin (m + 1))) := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => volume.restrict (Ici (0 : ℝ))) 0).symm
  refine (hp.integrable_comp_emb
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm.measurableEmbedding).mp ?_
  convert orthant_sum_tail_integrable (ι := Fin m) hb A using 1
  · funext z
    simp only [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      finiteOrthantTail, orthantSumTail, Fin.sum_univ_succ, Fin.insertNth_zero,
      Equiv.coe_fn_mk, Fin.cons_succ, Fin.zero_succAbove, cast_eq, Fin.cons_zero]
  · rfl

theorem finite_orthant_tail_integral_uniform {m : ℕ} {b A : ℝ}
    (hb : (1 / 2 : ℝ) ≤ b) (hA : 0 ≤ A) :
    (∫ s : Fin (m + 1) → ℝ, finiteOrthantTail b A s
      ∂exponentialOrthantMeasure (Fin (m + 1))) ≤
      8 ^ (m + 1) * Real.exp (-(b * A)) * (1 + A) ^ m := by
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hsI : IntegrableOn (fun v : ℝ => Real.exp (-(b * v))) (Ici 0) := by
    simpa only [pow_zero, one_mul] using gamma_monomial_integrable hbpos 0
  have hsTail (C : ℝ) : (∫ v : ℝ in Ici C, Real.exp (-(b * v))) = Real.exp (-(b * C)) / b := by
    simpa [div_eq_mul_inv] using gamma_polynomial_tail_integral hbpos C 0
  have hsplit : (∫ s : Fin (m + 1) → ℝ, finiteOrthantTail b A s ∂exponentialOrthantMeasure (Fin (m + 1))) =
      ∫ s : Fin m → ℝ, orthantHeadTail b A s ∂exponentialOrthantMeasure (Fin m) := by
    have h1 : (∫ s : Fin (m + 1) → ℝ, finiteOrthantTail b A s ∂exponentialOrthantMeasure (Fin (m + 1))) =
        ∫ z : ℝ × (Fin m → ℝ), orthantSumTail b A z
          ∂((volume.restrict (Ici (0 : ℝ))).prod (exponentialOrthantMeasure (Fin m))) := by
      unfold exponentialOrthantMeasure
      rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => volume.restrict (Ici (0 : ℝ))) 0).symm).integral_comp']
      exact integral_congr_ae (Eventually.of_forall fun z => by
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          finiteOrthantTail, orthantSumTail, Fin.sum_univ_succ, Fin.insertNth_zero,
          Equiv.coe_fn_mk, Fin.cons_succ, Fin.zero_succAbove, cast_eq, Fin.cons_zero])
    rw [h1, integral_prod_symm _ (orthant_sum_tail_integrable hbpos A)]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    dsimp only
    rw [show (fun v : ℝ => orthantSumTail b A (v, s)) =
        fun v => (Ici (A - ∑ j, s j)).indicator (fun v : ℝ => Real.exp (-(b * (v + ∑ j, s j)))) v from
        funext fun v => by
          simp only [orthantSumTail, Set.indicator, mem_Ici,
            show (A ≤ v + ∑ j, s j ↔ A - ∑ j, s j ≤ v) by constructor <;> intro h <;> linarith],
      integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici, Set.Ici_inter_Ici,
      show (fun v : ℝ => Real.exp (-(b * (v + ∑ j, s j)))) =
        fun v => Real.exp (-(b * ∑ j, s j)) * Real.exp (-(b * v)) from
        funext fun _ => by rw [← Real.exp_add]; congr 1; ring,
      integral_const_mul, hsTail, div_eq_mul_inv, ← mul_assoc, ← Real.exp_add]
    have hmx : (∑ j, s j) + max (A - ∑ j, s j) 0 = max A (∑ j, s j) := by
      by_cases h : ∑ j, s j ≤ A
      · rw [max_eq_left (by linarith), max_eq_left h]; ring
      · rw [max_eq_right (by linarith), max_eq_right (le_of_not_ge h)]; ring
    rw [show -(b * ∑ j, s j) + -(b * max (A - ∑ j, s j) 0) = -(b * ((∑ j, s j) + max (A - ∑ j, s j) 0)) by ring, hmx]
    rfl
  rw [hsplit]
  have hcI (j : Fin m) : Integrable (orthantCoordinateTail b A j) (exponentialOrthantMeasure (Fin m)) :=
    Integrable.fintype_prod (𝕜 := ℝ)
      (f := fun (l : Fin m) (v : ℝ) => if l = j then (Ioi A).indicator (fun v : ℝ => Real.exp (-(b * v))) v else Real.exp (-(b * v)))
      (μ := fun _ : Fin m => volume.restrict (Ici (0 : ℝ)))
      fun _ => by split_ifs <;> [exact hsI.indicator measurableSet_Ioi; exact hsI]
  have hcEq (j : Fin m) : (∫ s : Fin m → ℝ, orthantCoordinateTail b A j s ∂exponentialOrthantMeasure (Fin m)) =
      Real.exp (-(b * A)) / b ^ m := by
    unfold orthantCoordinateTail exponentialOrthantMeasure
    rw [integral_fintype_prod_eq_prod fun (l : Fin m) (v : ℝ) =>
      if l = j then (Ioi A).indicator (fun v : ℝ => Real.exp (-(b * v))) v else Real.exp (-(b * v)),
      show (fun l : Fin m => ∫ v : ℝ in Ici 0,
        if l = j then (Ioi A).indicator (fun v : ℝ => Real.exp (-(b * v))) v else Real.exp (-(b * v))) =
        fun l => if l = j then Real.exp (-(b * A)) / b else 1 / b from funext fun l => by
          split_ifs
          · have hs0 : Ioi A ∩ Ici (0 : ℝ) = Ioi A :=
              Set.inter_eq_left.mpr fun v hv => le_of_lt (lt_of_le_of_lt hA hv)
            rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
              hs0, ← integral_Ici_eq_integral_Ioi, hsTail]
          · simpa using hsTail 0,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    simp only [ite_true]
    rw [show (∏ l ∈ (Finset.univ : Finset (Fin m)).erase j,
        if l = j then Real.exp (-(b * A)) / b else 1 / b) = (1 / b) ^ (m - 1) by
      refine (Finset.prod_congr rfl fun l hl => ite_eq_right (Finset.mem_erase.mp hl).1).trans ?_
      rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_fin]]
    have hm0 : 0 < m := j.pos
    rw [show b ^ m = b ^ (m - 1) * b by conv_lhs => rw [show m = (m - 1) + 1 by omega]; rw [pow_succ],
      div_pow, one_pow]
    field_simp
  let cube := Icc (0 : Fin m → ℝ) fun _ => A
  let G := fun s : Fin m → ℝ => cube.indicator (fun _ => Real.exp (-(b * A)) / b) s +
    (1 / b) * ∑ j, orthantCoordinateTail b A j s
  have hG : Integrable G (exponentialOrthantMeasure (Fin m)) :=
    (orthant_cube_indicator_integrable A _).add ((integrable_finsetSum _ fun j _ => hcI j).const_mul _)
  have hoI : Integrable (orthantExponential b : (Fin m → ℝ) → ℝ) (exponentialOrthantMeasure (Fin m)) := by
    change Integrable (fun s : Fin m → ℝ => orthantExponential b s) _
    simp_rw [show ∀ s : Fin m → ℝ, orthantExponential b s = ∏ j, Real.exp (-(b * s j)) from fun _ => by
      unfold orthantExponential; rw [← Real.exp_sum]; congr 1; rw [Finset.mul_sum, Finset.sum_neg_distrib]]
    exact Integrable.fintype_prod (𝕜 := ℝ) (f := fun (_ : Fin m) (v : ℝ) => Real.exp (-(b * v)))
      (μ := fun _ : Fin m => volume.restrict (Ici (0 : ℝ))) fun _ => hsI
  have hhI : Integrable (orthantHeadTail b A : (Fin m → ℝ) → ℝ) (exponentialOrthantMeasure (Fin m)) := by
    have hcont : Continuous (orthantHeadTail b A : (Fin m → ℝ) → ℝ) :=
      (Real.continuous_exp.comp (continuous_const.mul
        (continuous_const.max (continuous_finsetSum _ fun j _ => continuous_apply j))).neg).div_const b
    exact (hoI.div_const b).mono' hcont.aestronglyMeasurable <| Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by unfold orthantHeadTail; positivity)]
      exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [le_max_right A (∑ j, s j)])) hbpos.le
  have hheadLe : (∫ s : Fin m → ℝ, orthantHeadTail b A s ∂exponentialOrthantMeasure (Fin m)) ≤
      Real.exp (-(b * A)) * (A ^ m / b + (m : ℝ) / b ^ (m + 1)) := by
    have hae : ∀ᵐ s ∂exponentialOrthantMeasure (Fin m), s ∈ Ici (0 : Fin m → ℝ) := by
      rw [exponential_orthant_measure_eq_restrict]; exact ae_restrict_mem measurableSet_Ici
    have hdom : (orthantHeadTail b A : (Fin m → ℝ) → ℝ) ≤ᵐ[exponentialOrthantMeasure (Fin m)] G := by
      filter_upwards [hae] with s hs
      have hcnn (l : Fin m) : 0 ≤ orthantCoordinateTail b A l s := Finset.prod_nonneg fun _ _ => by
        split_ifs <;> [exact Set.indicator_nonneg (fun _ _ => Real.exp_nonneg _) _; exact Real.exp_nonneg _]
      by_cases hcube : s ∈ cube
      · simp only [G, Set.indicator_of_mem hcube]
        have h1 : orthantHeadTail b A s ≤ Real.exp (-(b * A)) / b :=
          div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [le_max_left A (∑ j, s j)])) hbpos.le
        have hsum0 : 0 ≤ ∑ l : Fin m, orthantCoordinateTail b A l s := Finset.sum_nonneg fun l _ => hcnn l
        nlinarith [mul_nonneg (by positivity : 0 ≤ 1 / b) hsum0]
      · obtain ⟨j, hj⟩ : ∃ j, A < s j := by
          by_contra h; exact hcube ⟨hs, fun j => le_of_not_gt fun hj => h ⟨j, hj⟩⟩
        have hterm : orthantExponential b s ≤ ∑ l, orthantCoordinateTail b A l s := by
          have hcej : orthantCoordinateTail b A j s = orthantExponential b s := by
            have hep : orthantExponential b s = ∏ l, Real.exp (-(b * s l)) := by
              unfold orthantExponential; rw [← Real.exp_sum]; congr 1; rw [Finset.mul_sum, Finset.sum_neg_distrib]
            rw [hep]; unfold orthantCoordinateTail
            exact Finset.prod_congr rfl fun l _ => by
              split_ifs with hl
              · subst hl; exact Set.indicator_of_mem hj _
              · rfl
          rw [← hcej]
          exact Finset.single_le_sum (fun l _ => hcnn l) (Finset.mem_univ j)
        simp only [G, Set.indicator_of_notMem hcube, zero_add]
        have h1 : orthantHeadTail b A s ≤ orthantExponential b s / b := by
          unfold orthantHeadTail orthantExponential
          exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [le_max_right A (∑ k, s k)])) hbpos.le
        exact h1.trans (by convert mul_le_mul_of_nonneg_left hterm (by positivity : 0 ≤ 1 / b) using 1 <;> ring)
    have h := integral_mono_ae hhI hG hdom
    dsimp [G] at h
    rw [integral_add (orthant_cube_indicator_integrable A _) ((integrable_finsetSum _ fun j _ => hcI j).const_mul _),
      orthant_cube_indicator_integral hA, integral_const_mul, integral_finsetSum _ fun j _ => hcI j] at h
    simp_rw [hcEq] at h
    simp only [Fintype.card_fin, Finset.sum_const, Finset.card_univ, Finset.card_fin, nsmul_eq_mul] at h
    convert h using 1 <;> rw [pow_succ] <;> ring
  have hinv : 1 / b ≤ (2 : ℝ) := by simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hb
  have hpow : (1 / b) ^ (m + 1) ≤ (2 : ℝ) ^ (m + 1) := pow_le_pow_left₀ (by positivity) hinv _
  have htwo : (2 : ℝ) ≤ 2 ^ (m + 1) := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ m + 1)
  have hAone : 1 ≤ (1 + A) ^ m := one_le_pow₀ (by linarith)
  have hApow : A ^ m ≤ (1 + A) ^ m := pow_le_pow_left₀ hA (by linarith) _
  have hfirst : A ^ m / b ≤ 2 ^ (m + 1) * (1 + A) ^ m := by
    convert mul_le_mul hApow (hinv.trans htwo) (by positivity) (by positivity) using 1 <;> ring
  have hsecond : (m : ℝ) / b ^ (m + 1) ≤ (m : ℝ) * 2 ^ (m + 1) * (1 + A) ^ m := by
    have h1 := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg m)
    rw [div_pow, one_pow] at h1
    exact (show (m : ℝ) / b ^ (m + 1) = (m : ℝ) * (1 / b ^ (m + 1)) by ring).trans_le
      (h1.trans (by simpa using mul_le_mul_of_nonneg_left hAone (by positivity : 0 ≤ (m : ℝ) * 2 ^ (m + 1))))
  have h4pow : ∀ k : ℕ, (k : ℝ) + 2 ≤ (4 : ℝ) ^ (k + 1) := fun k => by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [Nat.cast_succ, show k + 1 + 1 = (k + 1) + 1 by omega, pow_succ]
      have : (1 : ℝ) ≤ 4 ^ (k + 1) := one_le_pow₀ (by norm_num)
      nlinarith
  have hconst : ((m : ℝ) + 1) * 2 ^ (m + 1) ≤ (8 : ℝ) ^ (m + 1) := by
    have h := mul_le_mul_of_nonneg_right (h4pow m) (by positivity : 0 ≤ (2 : ℝ) ^ (m + 1))
    rw [← mul_pow] at h; norm_num only at h; nlinarith
  have hsum : A ^ m / b + (m : ℝ) / b ^ (m + 1) ≤ 8 ^ (m + 1) * (1 + A) ^ m := by
    nlinarith [mul_le_mul_of_nonneg_right hconst (by positivity : 0 ≤ (1 + A) ^ m)]
  exact hheadLe.trans ((mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _)).trans_eq (by ring))

end OrthantTail

-- Gaussian separated characteristic and affine Hermite representation

abbrev standardGaussianLine : Measure ℝ := gaussianReal 0 1

abbrev standardGaussianPi (d : ℕ) : Measure (Covariate d) :=
  Measure.pi fun _ => standardGaussianLine

def gaussianPhase {d : ℕ} (w Z : Covariate d) : ℝ := ∑ l, w l * Z l

private def gaussianFourierMomentFactor (p : ℕ) (t : ℝ) : ℂ :=
  if p = 0 then 1 else if p = 1 then (t : ℂ) * Complex.I else 1 - (t : ℂ) ^ 2

private def gaussianCrossExponent {d : ℕ} (a b l : Fin d) : ℕ :=
  (if l = a then 1 else 0) + (if l = b then 1 else 0)

private lemma gaussian_monomial_characteristic {d : ℕ} (p : Fin d → ℕ) (hp : ∀ l, p l ≤ 2) (w : Covariate d) :
    Integrable (fun Z => (∏ l, (Z l : ℂ) ^ p l) * Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I))
      (standardGaussianPi d) ∧
      (∫ Z, (∏ l, (Z l : ℂ) ^ p l) * Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I)
        ∂standardGaussianPi d) =
        (∏ l, gaussianFourierMomentFactor (p l) (w l)) *
          Complex.exp ((-(∑ l, (w l) ^ 2) / 2 : ℝ) : ℂ) := by
  have hprod (Z : Covariate d) :
      (∏ l, (Z l : ℂ) ^ p l) * Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I) =
        ∏ l, (Z l : ℂ) ^ p l * Complex.exp ((w l : ℂ) * Complex.I * Z l) := by
    simp only [gaussianPhase, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul,
      Complex.exp_sum, Finset.prod_mul_distrib]
    exact congrArg ((∏ l, (Z l : ℂ) ^ p l) * ·) (Finset.prod_congr rfl fun _ _ => by congr 1; ring)
  have hcexp (z : ℂ) : (∫ x : ℝ, Complex.exp (z * x) ∂standardGaussianLine) = Complex.exp (z ^ 2 / 2) := by
    simpa only [complexMGF, id_eq, Complex.ofReal_zero, mul_zero, NNReal.coe_one,
      Complex.ofReal_one, one_mul, zero_add] using complexMGF_id_gaussianReal (μ := 0) (v := 1) z
  have hcder (z : ℂ) : HasDerivAt (fun z : ℂ => Complex.exp (z ^ 2 / 2)) (z * Complex.exp (z ^ 2 / 2)) z := by
    have hp' : HasDerivAt (fun z : ℂ => z ^ 2 / 2) z z := by
      convert ((hasDerivAt_id z).pow 2).div_const 2 using 1 <;> simp only [Pi.pow_apply, id_eq] <;> ring
    simpa only [mul_comm] using hp'.cexp
  have hm1 (z : ℂ) : (∫ x : ℝ, (x : ℂ) * Complex.exp (z * x) ∂standardGaussianLine) =
      z * Complex.exp (z ^ 2 / 2) := by
    have hz : z.re ∈ interior (integrableExpSet id standardGaussianLine) := by
      simp only [integrableExpSet_id_gaussianReal, interior_univ, mem_univ]
    have h := hasDerivAt_complexMGF hz
    rw [show complexMGF id standardGaussianLine = fun z => Complex.exp (z ^ 2 / 2) from funext hcexp] at h
    exact h.unique (hcder z)
  have hm2 (z : ℂ) : (∫ x : ℝ, (x : ℂ) ^ 2 * Complex.exp (z * x) ∂standardGaussianLine) =
      (1 + z ^ 2) * Complex.exp (z ^ 2 / 2) := by
    have hz : z.re ∈ interior (integrableExpSet id standardGaussianLine) := by
      simp only [integrableExpSet_id_gaussianReal, interior_univ, mem_univ]
    have h := hasDerivAt_integral_pow_mul_exp hz 1
    simp only [id_eq, pow_one, Nat.reduceAdd] at h
    rw [show (fun z : ℂ => ∫ x : ℝ, (x : ℂ) * Complex.exp (z * x) ∂standardGaussianLine) =
      fun z => z * Complex.exp (z ^ 2 / 2) from funext hm1] at h
    exact (h.unique ((hasDerivAt_id z).mul (hcder z))).trans (by simp only [id_eq]; ring)
  have hline (k : ℕ) (hk : k ≤ 2) (t : ℝ) :
      (∫ x : ℝ, (x : ℂ) ^ k * Complex.exp ((t : ℂ) * Complex.I * x) ∂standardGaussianLine) =
        gaussianFourierMomentFactor k t * Complex.exp ((-t ^ 2 / 2 : ℝ) : ℂ) := by
    have he : ((t : ℂ) * Complex.I) ^ 2 / 2 = ((-t ^ 2 / 2 : ℝ) : ℂ) := by
      push_cast; rw [mul_pow, Complex.I_sq]; ring
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · simp only [pow_zero, one_mul, gaussianFourierMomentFactor, ite_true]; rw [hcexp, he]
    · simp only [pow_one, gaussianFourierMomentFactor, if_neg (by omega : 1 ≠ 0), ite_true]; rw [hm1, he]
    · simp only [gaussianFourierMomentFactor, if_neg (by omega : 2 ≠ 0), if_neg (by omega : 2 ≠ 1)]
      rw [hm2, he]; congr 1; rw [mul_pow, Complex.I_sq]; ring
  have hInt : Integrable (fun Z => (∏ l, (Z l : ℂ) ^ p l) * Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I))
      (standardGaussianPi d) := by
    convert Integrable.fintype_prod (μ := fun _ : Fin d => standardGaussianLine) (fun l : Fin d => by
      have hz : ((w l : ℂ) * Complex.I).re ∈ interior (integrableExpSet id standardGaussianLine) := by
        simp only [integrableExpSet_id_gaussianReal, interior_univ, mem_univ]
      exact integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet hz (p l)) using 1
    exact funext hprod
  refine ⟨hInt, ?_⟩
  simp_rw [hprod]
  rw [integral_fintype_prod_eq_prod fun (l : Fin d) (x : ℝ) =>
    (x : ℂ) ^ p l * Complex.exp ((w l : ℂ) * Complex.I * x)]
  simp_rw [hline _ (hp _) _, Finset.prod_mul_distrib]
  refine congrArg ((∏ l, gaussianFourierMomentFactor (p l) (w l)) * ·) ?_
  rw [← Complex.exp_sum]; congr 1
  simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_ofNat,
    Complex.ofReal_sum, neg_div]
  rw [Finset.sum_neg_distrib, Finset.sum_div]

private lemma gaussianCrossExponent_props {d : ℕ} (a b : Fin d) :
    (∀ l, gaussianCrossExponent a b l ≤ 2) ∧
    (∀ Z : Covariate d, (∏ l, (Z l : ℂ) ^ gaussianCrossExponent a b l) = (Z a : ℂ) * Z b) ∧
    ∀ w : Covariate d, (∏ l, gaussianFourierMomentFactor (gaussianCrossExponent a b l) (w l)) =
      (if a = b then (1 : ℂ) else 0) - (w a : ℂ) * w b := by
  classical
  refine ⟨fun _ => by unfold gaussianCrossExponent; split_ifs <;> omega, fun Z => ?_, fun w => ?_⟩
  · have he (c : Fin d) : (∏ l, (Z l : ℂ) ^ (if l = c then 1 else 0)) = Z c := by
      simp_rw [show ∀ l : Fin d, (Z l : ℂ) ^ (if l = c then 1 else 0) = if l = c then (Z c : ℂ) else 1 from
        fun l => by split_ifs with hl <;> [rw [hl, pow_one]; exact pow_zero _], Fintype.prod_ite_eq']
    simp only [gaussianCrossExponent, pow_add, Finset.prod_mul_distrib, he]
  · by_cases hab : a = b
    · subst hab
      simp_rw [show ∀ l : Fin d, gaussianFourierMomentFactor (gaussianCrossExponent a a l) (w l) =
        if l = a then 1 - (w a : ℂ) ^ 2 else 1 from fun l => by
          by_cases hl : l = a <;> simp [gaussianCrossExponent, gaussianFourierMomentFactor, hl]]
      rw [Fintype.prod_ite_eq']; simp only [ite_true, pow_two]
    · simp_rw [show ∀ l : Fin d, gaussianFourierMomentFactor (gaussianCrossExponent a b l) (w l) =
        (if l = a then (w a : ℂ) * Complex.I else 1) * (if l = b then (w b : ℂ) * Complex.I else 1) from
        fun l => by
          by_cases hla : l = a
          · subst hla; simp [gaussianCrossExponent, gaussianFourierMomentFactor, hab]
          · by_cases hlb : l = b
            · subst hlb; simp [gaussianCrossExponent, gaussianFourierMomentFactor, hab, Ne.symm hab]
            · simp [gaussianCrossExponent, gaussianFourierMomentFactor, hla, hlb],
        Finset.prod_mul_distrib, Fintype.prod_ite_eq']
      rw [if_neg hab]
      calc
        _ = (w a : ℂ) * w b * Complex.I ^ 2 := by ring
        _ = _ := by rw [Complex.I_sq]; ring

def gaussianHermite {d : ℕ} (a b : Fin d) (Z : Covariate d) : ℝ :=
  (if a = b then 1 else 0) - Z a * Z b

private lemma standardGaussian_cross_integrable {d : ℕ} (a b : Fin d) :
    Integrable (fun Z : Covariate d => Z a * Z b) (standardGaussianPi d) := by
  have h := (gaussian_monomial_characteristic (gaussianCrossExponent a b)
    (gaussianCrossExponent_props a b).1 (fun _ => 0)).1
  simp only [(gaussianCrossExponent_props a b).2] at h
  simpa [gaussianPhase, Complex.mul_re] using h.re

theorem gaussianHermite_integrable {d : ℕ} (a b : Fin d) :
    Integrable (gaussianHermite a b) (standardGaussianPi d) :=
  (integrable_const _).sub (standardGaussian_cross_integrable a b)

theorem standardGaussian_hermite_abs_integral_le_two {d : ℕ} (a b : Fin d) :
    (∫ Z, |gaussianHermite a b Z| ∂standardGaussianPi d) ≤ 2 := by
  have hsq (c : Fin d) : (∫ Z : Covariate d, (Z c) ^ 2 ∂standardGaussianPi d) = 1 := by
    have h := (gaussian_monomial_characteristic (gaussianCrossExponent c c)
      (gaussianCrossExponent_props c c).1 (fun _ => 0)).2
    simp only [(gaussianCrossExponent_props c c).2, (gaussianCrossExponent_props c c).2.2] at h
    simp [gaussianPhase] at h
    rw [show (fun Z : Covariate d => (Z c : ℂ) * Z c) =
      fun Z : Covariate d => (((Z c) ^ 2 : ℝ) : ℂ) from funext fun _ => by simp [pow_two],
      integral_complex_ofReal] at h
    exact_mod_cast h
  have ha : Integrable (fun Z : Covariate d => (Z a) ^ 2) (standardGaussianPi d) := by
    simpa only [pow_two] using standardGaussian_cross_integrable a a
  have hb : Integrable (fun Z : Covariate d => (Z b) ^ 2) (standardGaussianPi d) := by
    simpa only [pow_two] using standardGaussian_cross_integrable b b
  have hdiv : Integrable (fun Z : Covariate d => ((Z a) ^ 2 + (Z b) ^ 2) / 2) (standardGaussianPi d) :=
    (ha.add hb).div_const 2
  have hi : Integrable (fun Z : Covariate d => 1 + ((Z a) ^ 2 + (Z b) ^ 2) / 2) (standardGaussianPi d) :=
    (integrable_const 1).add hdiv
  have hm := integral_mono (gaussianHermite_integrable a b).abs hi fun Z =>
    (abs_sub _ _).trans (add_le_add (by split_ifs <;> norm_num)
      (by rw [abs_mul]; nlinarith [sq_nonneg (|Z a| - |Z b|), sq_abs (Z a), sq_abs (Z b)]))
  rw [integral_add (integrable_const 1) hdiv, integral_div, integral_add ha hb, hsq a, hsq b] at hm
  norm_num at hm; exact hm

def gaussianSpatialFrequency {d : ℕ} (lam t : ℝ) (x y : Covariate d) : Covariate d :=
  fun l => Real.sqrt (2 * lam * t) * (y l - x l)

theorem gaussianSpatialFrequency_squared {d : ℕ} (lam t : ℝ) (hlam : 0 ≤ lam) (ht : 0 ≤ t)
    (x y : Covariate d) :
    (∑ l, (gaussianSpatialFrequency lam t x y l) ^ 2) =
      2 * lam * t * spatialSquaredDistance x y := by
  unfold gaussianSpatialFrequency spatialSquaredDistance
  simp_rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * lam * t)]
  rw [Finset.mul_sum]

theorem standardGaussian_hermite_cos_integral_const {d : ℕ} (w : Covariate d)
    (a b : Fin d) (α β : ℝ) :
    (∫ Z, gaussianHermite a b Z * α * β * Real.cos (gaussianPhase w Z)
      ∂standardGaussianPi d) =
      α * β * (w a * w b) * Real.exp (-(∑ l, (w l) ^ 2) / 2) := by
  have h0 := gaussian_monomial_characteristic (fun _ : Fin d => 0) (fun _ => by omega) w
  simp only [pow_zero, Finset.prod_const_one, one_mul, gaussianFourierMomentFactor, ite_true] at h0
  have hc := gaussian_monomial_characteristic (gaussianCrossExponent a b)
    (gaussianCrossExponent_props a b).1 w
  simp only [(gaussianCrossExponent_props a b).2.1, (gaussianCrossExponent_props a b).2.2] at hc
  have hiC : Integrable (fun Z => ((if a = b then (1 : ℂ) else 0) - (Z a : ℂ) * Z b) *
      Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I)) (standardGaussianPi d) := by
    convert (h0.1.const_mul (if a = b then (1 : ℂ) else 0)).sub hc.1 using 1
    exact funext fun _ => sub_mul _ _ _
  have heC : (∫ Z, ((if a = b then (1 : ℂ) else 0) - (Z a : ℂ) * Z b) *
      Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I) ∂standardGaussianPi d) =
      ((w a : ℂ) * w b) * Complex.exp ((-(∑ l, (w l) ^ 2) / 2 : ℝ) : ℂ) := by
    simp_rw [sub_mul]
    rw [integral_sub (h0.1.const_mul _) hc.1, integral_const_mul, h0.2, hc.2]; ring
  have hre := integral_re hiC
  change (∫ Z, (((if a = b then (1 : ℂ) else 0) - (Z a : ℂ) * Z b) *
    Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I)).re ∂standardGaussianPi d) =
      (∫ Z, ((if a = b then (1 : ℂ) else 0) - (Z a : ℂ) * Z b) *
        Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I) ∂standardGaussianPi d).re at hre
  have hcos : (∫ Z, gaussianHermite a b Z * Real.cos (gaussianPhase w Z) ∂standardGaussianPi d) =
      (w a * w b) * Real.exp (-(∑ l, (w l) ^ 2) / 2) := by
    have hr := hre.trans (congrArg Complex.re heC)
    unfold gaussianHermite
    simpa only [Complex.sub_re, Complex.mul_re, Complex.sub_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, add_zero, zero_add,
      mul_zero, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_re,
      apply_ite Complex.re, Complex.one_re, Complex.zero_re, apply_ite Complex.im,
      Complex.one_im, Complex.zero_im, ite_self] using hr
  rw [show (fun Z => gaussianHermite a b Z * α * β * Real.cos (gaussianPhase w Z)) =
    fun Z => α * β * (gaussianHermite a b Z * Real.cos (gaussianPhase w Z)) from funext fun _ => by ring,
    integral_const_mul, hcos]
  ring

end CardinalAndGaussianAnalysis
end NearlyMinimax
