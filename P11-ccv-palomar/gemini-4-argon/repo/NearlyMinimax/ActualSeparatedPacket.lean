module
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Analysis.Complex.Exponential
public import NearlyMinimax.HighResponseUpdates
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Prod
@[expose] public section
noncomputable section
open MeasureTheory Set Polynomial
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*}
def densityDerivativeWeight (D ) (j : Fin (derivativeOrder D + 1)) : ℝ :=
  lobattoDerivativeWeight ((D - 1) / 2) j
def densityUnitExponent (r ) : Fin r →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun _ => 1) (by simp)
@[simp] theorem densityUnitExponent_apply (r i) :
    densityUnitExponent r i = 1 := by simp [densityUnitExponent]
@[simp] theorem densityUnitExponent_degree (r ) :
    (densityUnitExponent r).degree = r := by
  simp [Finsupp.degree_eq_sum]
def densityDerivativeAction (r D : ℕ) (f : (Fin r → ℝ) → ℝ) : ℝ :=
  ∑ h : Fin r → Fin (derivativeOrder D + 1),
    (∏ l, densityDerivativeWeight D (h l)) *
      f (fun l => lobattoNode (derivativeOrder D) (h l))
def densityModulationPolynomial  (r ) (B : ι → Fin r → ℝ)
    (i : ι) : MvPolynomial (Fin r) ℝ :=
  ∑ l, MvPolynomial.C (B i l) * MvPolynomial.X l
def densityResetPolynomial  [DecidableEq ι] (S : Finset ι)
    (r ) (z t : ℝ) (p : ι → ℝ) (B : ι → Fin r → ℝ) : MvPolynomial (Fin r) ℝ :=
  ∏ i ∈ S, (MvPolynomial.C z + MvPolynomial.C (t * p i) *
    densityModulationPolynomial r B i)
theorem density_derivative_product_exact  [DecidableEq ι]
    (S r D) (hD : 1 ≤ D) (hSD : S.card ≤ D)
    (z t : ℝ) (p : ι → ℝ) (B : ι → Fin r → ℝ) :
    densityDerivativeAction r D (fun ε => ∏ i ∈ S, (z + t * p i * ∑ l, ε l * B i l)) =
      z ^ (S.card - r) * t ^ r *
        ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
          (∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r) := by
  have h_densityModulationPolynomial_homogeneous (i : ι) : (densityModulationPolynomial r B i).IsHomogeneous 1 := by
    apply MvPolynomial.IsHomogeneous.sum
    intro l _
    exact MvPolynomial.isHomogeneous_C_mul_X _ _
  have hf : (fun ε => ∏ i ∈ S, (z + t * p i * ∑ l, ε l * B i l)) =
      (fun ε => MvPolynomial.eval ε (densityResetPolynomial S r z t p B)) := by
    funext ε
    have h_densityResetPolynomial_eval : MvPolynomial.eval ε (densityResetPolynomial S r z t p B) =
        ∏ i ∈ S, (z + t * p i * ∑ l, ε l * B i l) := by
      simp only [densityResetPolynomial, map_prod, map_add, map_mul,
        MvPolynomial.eval_C, densityModulationPolynomial, map_sum, MvPolynomial.eval_X]
      simp only [mul_comm (B _ _)]
    exact h_densityResetPolynomial_eval.symm
  rw [hf]
  have h_densityDerivativeAction_polynomial (P) (hP : ∀ d ∈ P.support, ∀ l, d l ≤ D) : densityDerivativeAction r D (fun ε => MvPolynomial.eval ε P) =
      P.coeff (densityUnitExponent r) := by
    unfold densityDerivativeAction
    simp only [MvPolynomial.eval_eq', Finset.mul_sum]
    rw [Finset.sum_comm]
    have hm (d : Fin r →₀ ℕ) :
        (∑ h : Fin r → Fin (derivativeOrder D + 1),
          (∏ l, densityDerivativeWeight D (h l)) *
            (P.coeff d * ∏ l, lobattoNode (derivativeOrder D) (h l) ^ d l)) =
          P.coeff d *
            ∑ h : Fin r → Fin (derivativeOrder D + 1),
              (∏ l, densityDerivativeWeight D (h l)) *
                ∏ l, lobattoNode (derivativeOrder D) (h l) ^ d l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    simp_rw [hm]
    have h_densityDerivativeAction_monomial (d) (hd : ∀ l, d l ≤ D) : densityDerivativeAction r D (fun ε => ∏ l, ε l ^ d l) =
        if d = densityUnitExponent r then 1 else 0 := by
      unfold densityDerivativeAction
      simp_rw [← Finset.prod_mul_distrib]
      have h_derivative_rule_monomial (k) (hk : k ≤ D) : (∑ j : Fin (derivativeOrder D + 1),
          densityDerivativeWeight D j *
            lobattoNode (derivativeOrder D) j ^ k) = if k = 1 then 1 else 0 := by
        have h_derivative_rule_exact (P : ℝ[X]) (hP : P.degree ≤ D) : (∑ i : Fin (derivativeOrder D + 1),
            lobattoDerivativeWeight ((D - 1) / 2) i * P.eval (lobattoNode (derivativeOrder D) i)) =
            P.derivative.eval 0 := by
          apply lobatto_derivative_rule_exact_extra
          exact hP.trans (by exact_mod_cast (derivativeOrder_bounds D hD).2)
        simpa [densityDerivativeWeight, ← coeff_zero_eq_eval_zero, coeff_derivative,
          coeff_X_pow, eq_comm] using (h_derivative_rule_exact (X ^ k) (by simpa only [degree_X_pow, Nat.cast_withBot] using WithBot.coe_le_coe.mpr hk))
      rw [← Fintype.prod_sum (fun (l : Fin r) (j : Fin (derivativeOrder D + 1)) =>
        densityDerivativeWeight D j * lobattoNode (derivativeOrder D) j ^ d l)]
      simp_rw [h_derivative_rule_monomial _ (hd _)]
      by_cases he : d = densityUnitExponent r
      · subst d
        simp
      · rw [if_neg he]
        obtain ⟨l, hl⟩ : ∃ l, d l ≠ 1 := by
          by_contra hn
          apply he
          ext l
          simpa using not_exists.mp hn l
        apply Finset.prod_eq_zero (Finset.mem_univ l)
        simp [hl]
    have he (d : Fin r →₀ ℕ) (hd : d ∈ P.support) :
        (∑ h : Fin r → Fin (derivativeOrder D + 1),
          (∏ l, densityDerivativeWeight D (h l)) *
            ∏ l, lobattoNode (derivativeOrder D) (h l) ^ d l) =
          if d = densityUnitExponent r then 1 else 0 :=
      h_densityDerivativeAction_monomial d (hP d hd)
    calc
      _ = ∑ d ∈ P.support, P.coeff d * (if d = densityUnitExponent r then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [he d hd]
      _ = _ := by
        simp [Finset.sum_ite_eq', MvPolynomial.mem_support_iff]
        exact fun h => h.symm
  rw [h_densityDerivativeAction_polynomial]
  · classical
    unfold densityResetPolynomial
    simp_rw [add_comm (MvPolynomial.C z)]
    rw [Finset.prod_add]
    simp only [MvPolynomial.coeff_sum]
    have he (U : Finset ι) (hU : U ∈ S.powerset) :
        ((∏ i ∈ U, MvPolynomial.C (t * p i) * densityModulationPolynomial r B i) *
          ∏ i ∈ S \ U, MvPolynomial.C z).coeff (densityUnitExponent r) =
        z ^ (S \ U).card * t ^ U.card * (∏ i ∈ U, p i) *
          (∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r) := by
      rw [Finset.prod_mul_distrib, ← map_prod, ← map_prod,
        mul_comm _ (MvPolynomial.C _), mul_assoc, MvPolynomial.coeff_C_mul,
        MvPolynomial.coeff_C_mul]
      simp only [Finset.prod_const, Finset.prod_mul_distrib]
      ring
    rw [Finset.sum_congr rfl he]
    have hz (U : Finset ι) (hU : U ∈ S.powerset) :
        z ^ (S \ U).card * t ^ U.card * (∏ i ∈ U, p i) *
          (∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r) =
        if U.card = r then
          z ^ (S.card - r) * t ^ r * ((∏ i ∈ U, p i) *
            (∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r))
        else 0 := by
      by_cases hc : U.card = r
      · rw [if_pos hc, Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hU), hc]
        ring
      · rw [if_neg hc]
        have hh := MvPolynomial.IsHomogeneous.prod U
          (fun i => densityModulationPolynomial r B i) (fun _ => 1)
          (fun i _ => h_densityModulationPolynomial_homogeneous i)
        have hzero := hh.coeff_eq_zero (d := densityUnitExponent r) (by simpa using Ne.symm hc)
        simp only [hzero, mul_zero]
    rw [Finset.sum_congr rfl hz, ← Finset.sum_filter, ← Finset.powersetCard_eq_filter, ← Finset.mul_sum]
  · intro d hd l
    have h_densityResetPolynomial_totalDegree : (densityResetPolynomial S r z t p B).totalDegree ≤ S.card := by
      apply (MvPolynomial.totalDegree_finsetProd _ _).trans
      calc
        _ ≤ ∑ _i ∈ S, 1 := by
          apply Finset.sum_le_sum
          intro i _
          apply (MvPolynomial.totalDegree_add _ _).trans
          apply max_le
          · simp
          · have h := (h_densityModulationPolynomial_homogeneous i).C_mul (t * p i)
            exact h.totalDegree_le
        _ = _ := by simp
    exact (MvPolynomial.le_degreeOf_of_mem_support l hd).trans
      ((MvPolynomial.degreeOf_le_totalDegree _ _).trans
        (h_densityResetPolynomial_totalDegree.trans hSD))
def densityMargin (a b z : ℝ) : ℝ := (z - a) * (b - z) / (b - a)
theorem densityMargin_bounds (a b ) (hab : a < b) (z ) (hz : z ∈ Icc a b) :
    0 ≤ densityMargin a b z ∧ densityMargin a b z ≤ z - a ∧
      densityMargin a b z ≤ b - z ∧ densityMargin a b z ≤ (b - a) / 4 := by
  have hba  := sub_pos.mpr hab
  have hn  := sub_nonneg.mpr hz.1
  have hm  := sub_nonneg.mpr hz.2
  refine ⟨div_nonneg (mul_nonneg hn hm) hba.le, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hba).mpr
    nlinarith
  · apply (div_le_iff₀ hba).mpr
    nlinarith
  · apply (div_le_iff₀ hba).mpr
    nlinarith [sq_nonneg (z - (a + b) / 2)]
theorem densityMargin_zero_ne (a b ) (ha : 0 < a) (hab : a < b) :
    densityMargin a b 0 ≠ 0 := by
  exact div_ne_zero (mul_ne_zero (by simpa using ha.ne') (by simpa using (ha.trans hab).ne'))
    (sub_pos.mpr hab).ne'
def densityMarginPolynomial (a b : ℝ) : ℝ[X] :=
  (X - C a) * (C b - X) * C ((b - a)⁻¹)
@[simp] theorem densityMarginPolynomial_eval (a b z ) :
    (densityMarginPolynomial a b).eval z = densityMargin a b z := by
  simp [densityMarginPolynomial, densityMargin, div_eq_mul_inv]
def densityCountPolynomial (a b : ℝ) (k r : ℕ) : ℝ[X] :=
  X ^ (k - r) * densityMarginPolynomial a b ^ r
def densityCountCoefficient (a b : ℝ) (m r k : ℕ) : ℝ :=
  (∑ j : Fin (m + r + 1), exteriorWeight a b (m + r) j *
    (exteriorNode a b (m + r) j ^ (k - r) *
      densityMargin a b (exteriorNode a b (m + r) j) ^ r)) / densityMargin a b 0 ^ r
theorem densityCountCoefficient_exact (a b ) (ha : 0 < a) (hab : a < b)
    (m r k ) (hr : 1 ≤ r) (hrk : r ≤ k) (hkm : k ≤ m) :
    densityCountCoefficient a b m r k = if k = r then 1 else 0 := by
  have h_densityCountPolynomial_natDegree : (densityCountPolynomial a b k r).natDegree ≤ k + r := by
    apply (natDegree_mul_le).trans
    have h_densityMarginPolynomial_natDegree : (densityMarginPolynomial a b).natDegree ≤ 2 := by
      apply (natDegree_mul_le).trans
      have h₁ : (X - C a : ℝ[X]).natDegree ≤ 1 :=
        (natDegree_sub_le _ _).trans (by simp)
      have h₂ : (C b - X : ℝ[X]).natDegree ≤ 1 :=
        (natDegree_sub_le _ _).trans (by simp)
      have hm := (natDegree_mul_le (p := X - C a) (q := C b - X)).trans (add_le_add h₁ h₂)
      simpa using hm
    have := (natDegree_pow_le (p := densityMarginPolynomial a b) (n := r)).trans
      (Nat.mul_le_mul_left r h_densityMarginPolynomial_natDegree)
    simp only [natDegree_X_pow]
    omega
  have hdeg : (densityCountPolynomial a b k r).degree ≤ m + r :=
    degree_le_natDegree.trans (by
      exact_mod_cast h_densityCountPolynomial_natDegree.trans (Nat.add_le_add_right hkm r))
  have he := exterior_rule_exact a b hab (m + r) (by omega)
    (densityCountPolynomial a b k r) hdeg
  have h_densityCountPolynomial_eval (z) (k) (r) : (densityCountPolynomial a b k r).eval z = z ^ (k - r) * densityMargin a b z ^ r := by
    simp [densityCountPolynomial]
  simp only [h_densityCountPolynomial_eval] at he
  unfold densityCountCoefficient
  rw [he]
  by_cases hkr : k = r
  · subst k
    simp [pow_ne_zero r (densityMargin_zero_ne a b ha hab)]
  · have hpos : k - r ≠ 0 := by omega
    simp [zero_pow hpos, hkr]
def localDensityReset  (a b : ℝ) (r ) (z : ℝ)
    (ε : Fin r → ℝ) (p : ι → ℝ) (B : ι → Fin r → ℝ) (i : ι) : ℝ :=
  z + densityMargin a b z / (r * b) * p i * ∑ l, ε l * B i l
theorem localDensityReset_slope_bound  (a b ) (ha : 0 < a) (hab : a < b)
    (r : ℕ) (hr : 1 ≤ r) (z : ℝ) (hz : z ∈ Icc a b)
    (ε : Fin r → ℝ) (hε : ∀ l, |ε l| ≤ 1) (B : ι → Fin r → ℝ) (i : ι)
    (hB : ∀ l, |B i l| ≤ 1) :
    |densityMargin a b z / (r * b) * ∑ l, ε l * B i l| ≤
      (b - a) / (4 * b) := by
  have hb : 0 < b := ha.trans hab
  have hθ := densityMargin_bounds a b hab z hz
  have hsum : |∑ l, ε l * B i l| ≤ r := by
    calc
      _ ≤ ∑ l, |ε l * B i l| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin r, 1 := by
        apply Finset.sum_le_sum
        intro l _
        rw [abs_mul]
        exact (mul_le_mul (hε l) (hB l) (abs_nonneg _) (by norm_num)).trans_eq (by ring)
      _ = _ := by simp
  have hcoef : 0 ≤ densityMargin a b z / (r * b) :=
    div_nonneg hθ.1 (mul_pos (by exact_mod_cast hr) hb).le
  rw [abs_mul, abs_of_nonneg hcoef]
  calc
    _ ≤ densityMargin a b z / (r * b) * r :=
      mul_le_mul_of_nonneg_left hsum hcoef
    _ = densityMargin a b z / b := by field_simp
    _ ≤ ((b - a) / 4) / b := div_le_div_of_nonneg_right hθ.2.2.2 hb.le
    _ = _ := by ring
theorem localDensityReset_mem_interval  (a b ) (ha : 0 < a) (hab : a < b)
    (r : ℕ) (hr : 1 ≤ r) (z : ℝ) (hz : z ∈ Icc a b)
    (ε : Fin r → ℝ) (hε : ∀ l, |ε l| ≤ 1) (p : ι → ℝ)
    (B : ι → Fin r → ℝ) (i : ι) (hp : p i ∈ Icc a b) (hB : ∀ l, |B i l| ≤ 1) :
    localDensityReset a b r z ε p B i ∈ Icc a b := by
  have hb : 0 < b := ha.trans hab
  have hθ := densityMargin_bounds a b hab z hz
  have hp0 : 0 ≤ p i := ha.le.trans hp.1
  have hsum : |∑ l, ε l * B i l| ≤ r := by
    calc
      _ ≤ ∑ l, |ε l * B i l| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin r, 1 := by
        apply Finset.sum_le_sum
        intro l _
        rw [abs_mul]
        exact (mul_le_mul (hε l) (hB l) (abs_nonneg _) (by norm_num)).trans_eq (by ring)
      _ = _ := by simp
  have hcoef : 0 ≤ densityMargin a b z / (r * b) :=
    div_nonneg hθ.1 (mul_pos (by exact_mod_cast hr) hb).le
  have hshift : |densityMargin a b z / (r * b) * p i * ∑ l, ε l * B i l| ≤
      densityMargin a b z := by
    rw [abs_mul, abs_mul, abs_of_nonneg hcoef, abs_of_nonneg hp0]
    calc
      _ ≤ densityMargin a b z / (r * b) * p i * r :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hcoef hp0)
      _ = densityMargin a b z / b * p i := by field_simp
      _ ≤ densityMargin a b z / b * b :=
        mul_le_mul_of_nonneg_left hp.2 (div_nonneg hθ.1 hb.le)
      _ = _ := div_mul_cancel₀ _ hb.ne'
  obtain ⟨hl, hu⟩ := abs_le.mp hshift
  constructor <;> dsimp [localDensityReset] <;> linarith [hθ.2.1, hθ.2.2.1]
def densitySeparatedSym  [DecidableEq ι] (r )
    (B : ι → Fin r → ℝ) (S : Finset ι) : ℝ :=
  (∏ i ∈ S, densityModulationPolynomial r B i).coeff (densityUnitExponent r) /
    r.factorial
def densityPacketPrefactor (a b : ℝ) (r : ℕ) : ℝ :=
  r ^ r / r.factorial * (b / densityMargin a b 0) ^ r
def densityPacketAction (a b : ℝ) (m r D : ℕ) (f : ℝ → (Fin r → ℝ) → ℝ) : ℝ :=
  densityPacketPrefactor a b r * ∑ j : Fin (m + r + 1),
    exteriorWeight a b (m + r) j *
      densityDerivativeAction r D (f (exteriorNode a b (m + r) j))
theorem density_packet_product_exact  [DecidableEq ι]
    (S a b) (ha : 0 < a) (hab : a < b)
    (m r D ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hSD : S.card ≤ D)
    (p ) (B : ι → Fin r → ℝ) :
    densityPacketAction a b m r D (fun z ε => ∏ i ∈ S, localDensityReset a b r z ε p B i) =
      densityCountCoefficient a b m r S.card *
        ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) * densitySeparatedSym r B U := by
  have  := (ha.trans hab).ne'
  have  := densityMargin_zero_ne a b ha hab
  have : r.factorial ≠ 0 := by exact_mod_cast r.factorial_ne_zero
  unfold densityPacketAction localDensityReset
  simp_rw [density_derivative_product_exact S r D hD hSD]
  unfold densityCountCoefficient densitySeparatedSym
  have hsum : (∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
      ((∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r) /
        r.factorial)) =
      (∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
        (∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r)) /
        r.factorial := by simp_rw [← mul_div_assoc]; rw [Finset.sum_div]
  rw [hsum]
  unfold densityPacketPrefactor
  simp only [div_pow, mul_pow]
  rw [Finset.mul_sum]
  calc
    _ = ∑ j : Fin (m + r + 1),
      (exteriorWeight a b (m + r) j *
        (exteriorNode a b (m + r) j ^ (S.card - r) *
          densityMargin a b (exteriorNode a b (m + r) j) ^ r) / densityMargin a b 0 ^ r) *
        ((∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
          (∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r)) /
          r.factorial) := by
      apply Finset.sum_congr rfl
      intro j _
      field_simp
    _ = _ := by simp only [← Finset.sum_mul, Finset.sum_div]
def densityAssignmentExponent (r ) (f : Fin r → Fin r) : Fin r →₀ ℕ :=
  ∑ i, Finsupp.single (f i) 1
theorem density_linear_product_permanent (r B) :
    (∏ i, densityModulationPolynomial r B i).coeff (densityUnitExponent r) =
      ∑ σ : Equiv.Perm (Fin r), ∏ i, B i (σ i) := by
  classical
  unfold densityModulationPolynomial
  rw [Fintype.prod_sum]
  simp_rw [MvPolynomial.C_mul_X_eq_monomial]
  have hm (f : Fin r → Fin r) :
      (∏ i, MvPolynomial.monomial (Finsupp.single (f i) 1) (B i (f i))) =
      MvPolynomial.monomial (densityAssignmentExponent r f) (∏ i, B i (f i)) :=
    (MvPolynomial.monomial_sum_prod Finset.univ _ _).symm
  simp_rw [hm]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  have h_densityAssignmentExponent_eq_unit_iff (f) : densityAssignmentExponent r f = densityUnitExponent r ↔ Function.Bijective f := by
    constructor
    · intro he
      have hs : Function.Surjective f := by
        intro l
        by_contra hn
        have hne (i : Fin r) : f i ≠ l := fun h => hn ⟨i, h⟩
        have hv := congrArg (fun d => d l) he
        simp [densityAssignmentExponent, hne] at hv
      exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
    · intro hf
      let e := Equiv.ofBijective f hf
      change (∑ i, Finsupp.single (e i) 1) = densityUnitExponent r
      rw [e.sum_comp (fun l => Finsupp.single l 1)]
      ext l
      simp
  simp only [h_densityAssignmentExponent_eq_unit_iff]
  have hs : (∑ f : Fin r → Fin r, if Function.Bijective f then ∏ i, B i (f i) else 0) =
      ∑ f : {f : Fin r → Fin r // Function.Bijective f}, ∏ i, B i (f.1 i) := by
    apply Finset.sum_congr_set {f : Fin r → Fin r | Function.Bijective f}
    · intro f hf
      exact if_pos hf
    · intro f hf
      exact if_neg hf
  rw [hs]
  apply Fintype.sum_equiv Equiv.bijectiveEquiv
  intro f
  rfl
theorem densitySeparatedSym_eq_permutation_average  [DecidableEq ι]
    (r : ℕ) (B : ι → Fin r → ℝ) (S : Finset ι) (e : Fin r ≃ S) :
    densitySeparatedSym r B S =
      (∑ σ : Equiv.Perm (Fin r), ∏ i, B (e i) (σ i)) / r.factorial := by
  unfold densitySeparatedSym
  have he : (∏ i ∈ S, densityModulationPolynomial r B i) =
      ∏ i : Fin r, densityModulationPolynomial r (fun i l => B (e i) l) i := by
    rw [← Finset.prod_coe_sort]
    exact (e.prod_comp (fun i => densityModulationPolynomial r B i)).symm
  rw [he, density_linear_product_permanent]
theorem density_packet_product_zero_of_small_count  [DecidableEq ι]
    (S : Finset ι) (a b ) (ha : 0 < a) (hab : a < b)
    (m r D ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hSD : S.card ≤ D)
    (hSr : S.card < r) (p B) :
    densityPacketAction a b m r D (fun z ε => ∏ i ∈ S, localDensityReset a b r z ε p B i) = 0 := by
  rw [density_packet_product_exact S a b ha hab m r D hr hD hSD p B,
    Finset.powersetCard_eq_empty.mpr hSr]
  simp
theorem density_packet_product_count_selector  [DecidableEq ι]
    (S : Finset ι) (a b ) (ha : 0 < a) (hab : a < b)
    (m r D ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hSD : S.card ≤ D)
    (hSm : S.card ≤ m) (p B) :
    densityPacketAction a b m r D (fun z ε => ∏ i ∈ S, localDensityReset a b r z ε p B i) =
      if S.card = r then ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) * densitySeparatedSym r B U else 0 := by
  by_cases hSr : r ≤ S.card
  · rw [density_packet_product_exact S a b ha hab m r D hr hD hSD p B,
      densityCountCoefficient_exact a b ha hab m r S.card hr hSr hSm]
    split_ifs <;> simp
  · rw [density_packet_product_zero_of_small_count S a b ha hab m r D hr hD hSD (by omega) p B,
      if_neg (by omega)]
def densityPacketAtom (a b : ℝ) (m r D )
    (j : Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1))) : ℝ × (Fin r → ℝ) :=
  (exteriorNode a b (m + r) j.1, fun l => lobattoNode (derivativeOrder D) (j.2 l))
def densityPacketWeight (a b : ℝ) (m r D )
    (j : Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1))) : ℝ :=
  densityPacketPrefactor a b r * exteriorWeight a b (m + r) j.1 *
    ∏ l, densityDerivativeWeight D (j.2 l)
def densityPacketSignedRule (a b : ℝ) (m r D : ℕ) : SignedMeasure (ℝ × (Fin r → ℝ)) :=
  atomicSignedRule (densityPacketAtom a b m r D) (densityPacketWeight a b m r D)
theorem densityPacketAtom_mem (a b ) (hab : a ≤ b) (m r D j) :
    (densityPacketAtom a b m r D j).1 ∈ Icc a b ∧
      ∀ l, |(densityPacketAtom a b m r D j).2 l| ≤ 1 := by
  constructor
  · exact exteriorNode_mem a b hab (m + r) j.1
  · intro l
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
theorem densityPacketWeight_variation (a b ) (ha : 0 < a) (hab : a < b)
    (m r D ) (hr : 1 ≤ r) :
    (∑ j : Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1)),
      |densityPacketWeight a b m r D j|) =
      |densityPacketPrefactor a b r| *
        Real.cosh ((m + r : ℕ) * exteriorTau ((a + b) / (b - a))) * (derivativeOrder D : ℝ) ^ r := by
  have h_densityDerivativeWeight_tensor_variation : (∑ h : Fin r → Fin (derivativeOrder D + 1), ∏ l, |densityDerivativeWeight D (h l)|) =
      (derivativeOrder D ) ^ r := by
    rw [← Fintype.prod_sum (fun (_l : Fin r) (j : Fin (derivativeOrder D + 1)) =>
      |densityDerivativeWeight D j|)]
    have h_densityDerivativeWeight_variation : (∑ j : Fin (derivativeOrder D + 1), |densityDerivativeWeight D j|) = (derivativeOrder D ) := lobatto_derivative_rule_variation ((D - 1) / 2)
    simp only [h_densityDerivativeWeight_variation, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [densityPacketWeight, abs_mul, Finset.abs_prod, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, h_densityDerivativeWeight_tensor_variation]
  rw [← Finset.sum_mul, ← Finset.mul_sum, exterior_rule_variation a b ha hab _ (by omega)]
section ResponseIntegral
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def responseMatrixEntryCoefficient (q : ℕ) (C : ℝ) (c : ι → ℝ)
    (Φ : (ι → ℝ) → ℝ) (i j : ι) : ℝ :=
  ∑ s : Bool, ∑ t : Bool, (C ^ 2 / 2 * fairSign s * fairSign t) *
    ∑ h : Fin (2 * q + 2), responseWeight q h *
      Φ (coefficientReset c (covarianceAtom C i j s t) (responseNode q h))
theorem responseMatrixAction_entry_sum (q C A c) (Φ : (ι → ℝ) → ℝ) :
    responseMatrixAction q C A c Φ =
      ∑ i, ∑ j, A i j * responseMatrixEntryCoefficient q C c Φ i j := by
  simp only [responseMatrixAction, covarianceAction, covarianceWeight,
    responseMatrixEntryCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro h _
  ring
theorem responseMatrixAction_scalar_matrix (q C t A c) (Φ : (ι → ℝ) → ℝ) :
    responseMatrixAction q C (fun i j => t * A i j) c Φ =
      t * responseMatrixAction q C A c Φ := by
  simp only [responseMatrixAction_entry_sum, Finset.mul_sum, mul_assoc]
variable {Z : Type*} [MeasurableSpace Z] (σ : Measure Z)
theorem responseMatrixAction_integrable (q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Integrable (fun ζ => A ζ i j) σ)
    (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    Integrable (fun ζ => responseMatrixAction q C (A ζ) c Φ) σ := by
  simp only [responseMatrixAction_entry_sum]
  exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _
    (fun j _ => (hA i j).mul_const _))
end ResponseIntegral
section Separated
variable {Z α : Type*} [MeasurableSpace Z] [DecidableEq α]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def separatedMatrixCost (A : Z → ι → ι → ℝ) (ζ : Z) : ℝ := ∑ i, ∑ j, |A ζ i j|
theorem separatedMatrixCost_entry_le (A : Z → ι → ι → ℝ) (ζ : Z) (i j : ι) :
    |A ζ i j| ≤ separatedMatrixCost A ζ := by
  apply (Finset.single_le_sum (fun k _ => abs_nonneg (A ζ i k)) (Finset.mem_univ j)).trans
  exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => abs_nonneg (A ζ k l)))
    (Finset.mem_univ i)
theorem separatedMatrix_entry_integrable (σ : Measure Z) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (i j : ι) :
    Integrable (fun ζ => A ζ i j) σ := by
  apply hcost.mono' (hA i j).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ζ => by
    simpa only [Real.norm_eq_abs] using separatedMatrixCost_entry_le A ζ i j)
def separatedSubsetMatrix (σ : Measure Z) (r ) (B : Z → α → Fin r → ℝ)
    (A : Z → ι → ι → ℝ) (S : Finset α) : ι → ι → ℝ :=
  fun i j => ∫ ζ, densitySeparatedSym r (B ζ) S * A ζ i j ∂σ
theorem separated_subset_entry_integrable (σ : Measure Z) (r : ℕ)
    (B : Z → α → Fin r → ℝ) (hB : ∀ i l, Measurable (fun ζ => B ζ i l))
    (hBbound : ∀ ζ i l, |B ζ i l| ≤ 1) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ)
    (S : Finset α) (hS : S.card = r) (i j : ι) :
    Integrable (fun ζ => densitySeparatedSym r (B ζ) S * A ζ i j) σ := by
  have h_densitySeparatedSym_measurable : Measurable (fun ζ => densitySeparatedSym r (B ζ) S) := by
    let e : Fin r ≃ S := (Fintype.equivFinOfCardEq (show Fintype.card S = r by simpa using hS)).symm
    have he : (fun ζ => densitySeparatedSym r (B ζ) S) =
        (fun ζ => (∑ τ : Equiv.Perm (Fin r), ∏ i, B ζ (e i) (τ i)) / ↑r.factorial) := by
      funext ζ
      exact densitySeparatedSym_eq_permutation_average r (B ζ) S e
    rw [he]
    exact (Finset.measurable_fun_sum _ (fun τ _ => Finset.measurable_fun_prod _
      (fun i _ => hB (e i) (τ i)))).div_const _
  apply hcost.mono' (h_densitySeparatedSym_measurable.mul (hA i j)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ζ
  change ‖densitySeparatedSym r (B ζ) S * A ζ i j‖ ≤ separatedMatrixCost A ζ
  rw [Real.norm_eq_abs, abs_mul]
  have h_densitySeparatedSym_abs_le_one : |densitySeparatedSym r (B ζ) S| ≤ 1 := by
    have hB : ∀ i ∈ S, ∀ l, |(B ζ) i l| ≤ 1 := fun i _ l => hBbound ζ i l
    let e : Fin r ≃ S := (Fintype.equivFinOfCardEq (show Fintype.card S = r by simpa)).symm
    rw [densitySeparatedSym_eq_permutation_average r (B ζ) S e, abs_div,
      abs_of_pos (by exact_mod_cast r.factorial_pos : (0 : ℝ) < r.factorial)]
    apply (div_le_iff₀ (by exact_mod_cast r.factorial_pos : (0 : ℝ) < r.factorial)).mpr
    calc
      _ ≤ ∑ σ : Equiv.Perm (Fin r), |∏ i, (B ζ) (e i) (σ i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin r), ↑1 := by
        apply Finset.sum_le_sum
        intro σ _
        rw [Finset.abs_prod]
        exact (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hB (e i) (e i).2 (σ i))).trans_eq
          (by simp)
      _ = _ := by simp [Fintype.card_perm]
  calc
    _ ≤ 1 * |A ζ i j| := mul_le_mul_of_nonneg_right
      h_densitySeparatedSym_abs_le_one (abs_nonneg _)
    _ ≤ separatedMatrixCost A ζ := by simpa using separatedMatrixCost_entry_le A ζ i j
theorem separatedSubsetMatrix_response (σ : Measure Z) (r : ℕ)
    (B : Z → α → Fin r → ℝ) (hB : ∀ i l, Measurable (fun ζ => B ζ i l))
    (hBbound : ∀ ζ i l, |B ζ i l| ≤ 1) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (S : Finset α) (hS : S.card = r)
    (q C c Φ) :
    responseMatrixAction q C (separatedSubsetMatrix σ r B A S) c Φ =
      ∫ ζ, densitySeparatedSym r (B ζ) S * responseMatrixAction q C (A ζ) c Φ ∂σ := by
  unfold separatedSubsetMatrix
  have h_responseMatrixAction_integral (A : Z → ι → ι → ℝ) (hA : ∀ i j, Integrable (fun ζ => A ζ i j) σ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) : responseMatrixAction q C (fun i j => ∫ ζ, A ζ i j ∂σ) c Φ =
      ∫ ζ, responseMatrixAction q C (A ζ) c Φ ∂σ := by
    simp only [responseMatrixAction_entry_sum]
    rw [integral_finset_sum Finset.univ (fun i _ => integrable_finset_sum _
      (fun j _ => (hA i j).mul_const _))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finset_sum Finset.univ (fun j _ => (hA i j).mul_const _)]
    simp only [integral_mul_const]
  rw [h_responseMatrixAction_integral _ (separated_subset_entry_integrable σ r B hB hBbound A hA hcost S hS)]
  simp only [responseMatrixAction_scalar_matrix]
theorem densityDerivativeAction_mul_right (r D f t) :
    densityDerivativeAction r D (fun ε => f ε * t) = densityDerivativeAction r D f * t := by
  simp only [densityDerivativeAction, Finset.sum_mul, mul_assoc]
theorem densityPacketAction_mul_right (a b m r D f t) :
    densityPacketAction a b m r D (fun z ε => f z ε * t) = densityPacketAction a b m r D f * t := by
  simp only [densityPacketAction, densityDerivativeAction_mul_right, Finset.sum_mul, mul_assoc]
def highSeparatedPacketAction (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (c : ι → ℝ)
    (G : Z → ℝ → (Fin r → ℝ) → ℝ) (Φ : (ι → ℝ) → ℝ) : ℝ :=
  ∫ ζ, densityPacketAction a b m r D
    (fun z ε => G ζ z ε * responseMatrixAction q C (A ζ) c Φ) ∂σ
theorem separated_subset_response_integrable (σ : Measure Z) (r : ℕ)
    (B : Z → α → Fin r → ℝ) (hB : ∀ i l, Measurable (fun ζ => B ζ i l))
    (hBbound : ∀ ζ i l, |B ζ i l| ≤ 1) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (S : Finset α) (hS : S.card = r)
    (q : ℕ) (C : ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    Integrable (fun ζ => densitySeparatedSym r (B ζ) S * responseMatrixAction q C (A ζ) c Φ) σ := by
  have h := responseMatrixAction_integrable σ q C
    (fun ζ i j => densitySeparatedSym r (B ζ) S * A ζ i j)
    (separated_subset_entry_integrable σ r B hB hBbound A hA hcost S hS) c Φ
  simpa only [responseMatrixAction_scalar_matrix] using h
theorem highSeparatedPacketAction_row (σ a b)
    (ha : 0 < a) (hab : a < b) (m r D q ) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (S : Finset α) (hSD : S.card ≤ D) (p : α → ℝ)
    (B : Z → α → Fin r → ℝ) (hB : ∀ i l, Measurable (fun ζ => B ζ i l))
    (hBbound : ∀ ζ i l, |B ζ i l| ≤ 1) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (c Φ) :
    highSeparatedPacketAction σ a b m r D q C A c
      (fun ζ z ε => ∏ i ∈ S, localDensityReset a b r z ε p (B ζ) i) Φ =
      densityCountCoefficient a b m r S.card *
        ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
          responseMatrixAction q C (separatedSubsetMatrix σ r B A U) c Φ := by
  have hInt (U : Finset α) (hU : U ∈ S.powersetCard r) :
      Integrable (fun ζ => (∏ i ∈ U, p i) *
        (densitySeparatedSym r (B ζ) U * responseMatrixAction q C (A ζ) c Φ)) σ :=
    (separated_subset_response_integrable σ r B hB hBbound A hA hcost U
      (Finset.mem_powersetCard.mp hU).2 q C c Φ).const_mul _
  have he (ζ : Z) : densityPacketAction a b m r D
      (fun z ε => (∏ i ∈ S, localDensityReset a b r z ε p (B ζ) i) *
        responseMatrixAction q C (A ζ) c Φ) =
      densityCountCoefficient a b m r S.card *
        ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
          (densitySeparatedSym r (B ζ) U * responseMatrixAction q C (A ζ) c Φ) := by
    rw [densityPacketAction_mul_right,
      density_packet_product_exact S a b ha hab m r D hr hD hSD p (B ζ)]
    simp only [Finset.sum_mul, mul_assoc]
  unfold highSeparatedPacketAction
  simp_rw [he]
  rw [integral_const_mul, integral_finsetSum _ hInt]
  apply congrArg (fun t => densityCountCoefficient a b m r S.card * t)
  apply Finset.sum_congr rfl
  intro U hU
  rw [integral_const_mul, ← separatedSubsetMatrix_response σ r B hB hBbound A hA hcost U
    (Finset.mem_powersetCard.mp hU).2 q C c Φ]
theorem highSeparatedPacketAction_count_selector (σ a b)
    (ha : 0 < a) (hab : a < b) (m r D q ) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (S : Finset α) (hSD : S.card ≤ D) (hSm : S.card ≤ m) (hrS : r ≤ S.card) (p : α → ℝ)
    (B : Z → α → Fin r → ℝ) (hB : ∀ i l, Measurable (fun ζ => B ζ i l))
    (hBbound : ∀ ζ i l, |B ζ i l| ≤ 1) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (c Φ) :
    highSeparatedPacketAction σ a b m r D q C A c
      (fun ζ z ε => ∏ i ∈ S, localDensityReset a b r z ε p (B ζ) i) Φ =
      if S.card = r then ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
        responseMatrixAction q C (separatedSubsetMatrix σ r B A U) c Φ else 0 := by
  rw [highSeparatedPacketAction_row σ a b ha hab m r D q hr hD S hSD p B hB hBbound C A hA hcost c Φ,
    densityCountCoefficient_exact a b ha hab m r S.card hr hrS hSm]
  split_ifs <;> simp
end Separated
section SignedDensity
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
theorem signedDensity_integral (w : X → ℝ) (hw : Integrable w μ) (hmw : Measurable w)
    (f : X → ℝ) (hf : Measurable f) (M : ℝ) (hbound : ∀ x, ‖f x‖ ≤ M) :
    (∫ᵛ x, f x ∂<•(μ.withDensityᵥ w)) = ∫ x, w x * f x ∂μ := by
  let μp := μ.withDensity (fun x => ENNReal.ofReal (w x))
  let μn := μ.withDensity (fun x => ENNReal.ofReal (-w x))
  letI : IsFiniteMeasure μp := isFiniteMeasure_withDensity_ofReal hw.hasFiniteIntegral
  letI : IsFiniteMeasure μn := isFiniteMeasure_withDensity_ofReal hw.neg.hasFiniteIntegral
  have hp : Integrable f μp := (integrable_const M).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
  have hn : Integrable f μn := (integrable_const M).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hw,
    VectorMeasure.integral_sub_vectorMeasure (by simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hp) (by simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hn), VectorMeasure.integral_toSignedMeasure,
    VectorMeasure.integral_toSignedMeasure]
  have hmn : Measurable (fun x => ENNReal.ofReal (-w x)) := hmw.neg.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hmw.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
    integral_withDensity_eq_integral_toReal_smul hmn
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  rw [← integral_sub (hw.pos_part.mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)) (hw.neg_part.mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  have he : max (w x) 0 - max (-w x) 0 = w x := by
    by_cases hh : 0 ≤ w x <;> simp [hh, neg_nonpos.mpr]
  dsimp only
  rw [← sub_mul, he]
end SignedDensity
section FiniteProduct
variable {Z I : Type*} [MeasurableSpace Z] [MeasurableSpace I]
  [Fintype I] [MeasurableSingletonClass I]
theorem finite_count_integrable (f : I → ℝ) : Integrable f Measure.count := by
  apply (integrable_const (∑ i, ‖f i‖)).mono' (measurable_of_countable f).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun i =>
    Finset.single_le_sum (fun j _ => norm_nonneg (f j)) (Finset.mem_univ i))
theorem joint_finite_integrable (σ : Measure Z) [IsFiniteMeasure σ] (f : Z × I → ℝ)
    (hf : ∀ i, Measurable (fun ζ => f (ζ, i)))
    (hi : ∀ i, Integrable (fun ζ => f (ζ, i)) σ) :
    Integrable f (σ.prod Measure.count) := by
  apply (integrable_prod_iff (measurable_from_prod_countable_left hf).aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun ζ => finite_count_integrable _), ?_⟩
  simp only [integral_count]
  exact integrable_finsetSum _ (fun i _ => (hi i).norm)
end FiniteProduct
abbrev HighDensityMarkIndex (m r D : ℕ) :=
  Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1))
abbrev HighResponseMarkIndex (ι : Type*) (q : ℕ) := (ι × ι) × (Bool × Bool) × Fin (2 * q + 2)
abbrev HighPacketMarkIndex (ι : Type*) (m r D q : ℕ) :=
  HighDensityMarkIndex m r D × HighResponseMarkIndex ι q
section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
def highResponseMarkAtom (C : ℝ) (q : ℕ) (h : HighResponseMarkIndex ι q) :
    ℝ × (ι → ℝ) :=
  (responseNode q h.2.2, covarianceAtom C h.1.1 h.1.2 h.2.1.1 h.2.1.2)
def highResponseMarkWeight (C : ℝ) (q : ℕ) (A : ι → ι → ℝ)
    (h : HighResponseMarkIndex ι q) : ℝ :=
  responseWeight q h.2.2 * covarianceWeight C A h.1.1 h.1.2 h.2.1.1 h.2.1.2
def highPacketMarkWeight (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (e : Z × HighPacketMarkIndex ι m r D q) : ℝ :=
  densityPacketWeight a b m r D e.2.1 * highResponseMarkWeight C q (A e.1) e.2.2
theorem highPacketMarkWeight_slice_measurable (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (h : HighPacketMarkIndex ι m r D q) :
    Measurable (fun ζ => highPacketMarkWeight a b m r D q C A (ζ, h)) := by
  dsimp [highPacketMarkWeight, highResponseMarkWeight, covarianceWeight]
  fun_prop
theorem highPacketMarkWeight_measurable (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) :
    Measurable (highPacketMarkWeight a b m r D q C A) :=
  measurable_from_prod_countable_left (highPacketMarkWeight_slice_measurable a b m r D q C A hA)
theorem highPacketMarkWeight_integrable (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ) :
    Integrable (highPacketMarkWeight a b m r D q C A) (σ.prod Measure.count) :=
  have h_highPacketMarkWeight_slice_integrable (h : HighPacketMarkIndex ι m r D q) : Integrable (fun ζ => highPacketMarkWeight a b m r D q C A (ζ, h)) σ := by
    exact (((((separatedMatrix_entry_integrable σ A hA hcost h.2.1.1 h.2.1.2).const_mul
      (C ^ 2 / 2)).mul_const (fairSign h.2.2.1.1)).mul_const (fairSign h.2.2.1.2)).const_mul
        (responseWeight q h.2.2.2)).const_mul (densityPacketWeight a b m r D h.1)
  joint_finite_integrable σ _ (highPacketMarkWeight_slice_measurable a b m r D q C A hA)
    h_highPacketMarkWeight_slice_integrable
def highPacketSignedMeasure (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : SignedMeasure (Z × HighPacketMarkIndex ι m r D q) :=
  (σ.prod Measure.count).withDensityᵥ (highPacketMarkWeight a b m r D q C A)
theorem highResponseMark_action (q : ℕ) (C : ℝ) (A : ι → ι → ℝ)
    (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    (∑ h : HighResponseMarkIndex ι q, highResponseMarkWeight C q A h *
      Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)) =
      responseMatrixAction q C A c Φ := by
  simp only [Fintype.sum_prod_type, highResponseMarkWeight, highResponseMarkAtom,
    responseMatrixAction, covarianceAction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro h _
  ring
def highPacketObservable (a b : ℝ) (m r D q : ℕ) (C : ℝ) (c : ι → ℝ)
    (G : Z → ℝ → (Fin r → ℝ) → ℝ) (Φ : (ι → ℝ) → ℝ)
    (e : Z × HighPacketMarkIndex ι m r D q) : ℝ :=
  G e.1 (densityPacketAtom a b m r D e.2.1).1 (densityPacketAtom a b m r D e.2.1).2 *
    Φ (coefficientReset c (highResponseMarkAtom C q e.2.2).2 (highResponseMarkAtom C q e.2.2).1)
theorem highPacketObservable_finite_action (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (c : ι → ℝ)
    (G : Z → ℝ → (Fin r → ℝ) → ℝ) (Φ : (ι → ℝ) → ℝ) (ζ : Z) :
    (∑ h : HighPacketMarkIndex ι m r D q,
      highPacketMarkWeight a b m r D q C A (ζ, h) * highPacketObservable a b m r D q C c G Φ (ζ, h)) =
      densityPacketAction a b m r D (fun z ε => G ζ z ε * responseMatrixAction q C (A ζ) c Φ) := by
  rw [Fintype.sum_prod_type]
  have he (h : HighDensityMarkIndex m r D) :
      (∑ v : HighResponseMarkIndex ι q,
        highPacketMarkWeight a b m r D q C A (ζ, (h, v)) *
          highPacketObservable a b m r D q C c G Φ (ζ, (h, v))) =
      densityPacketWeight a b m r D h *
        (G ζ (densityPacketAtom a b m r D h).1 (densityPacketAtom a b m r D h).2 *
          responseMatrixAction q C (A ζ) c Φ) := by
    rw [← highResponseMark_action q C (A ζ) c Φ]
    simp only [Finset.mul_sum, highPacketMarkWeight, highPacketObservable]
    apply Finset.sum_congr rfl
    intro v _
    ring
  simp_rw [he]
  have h_densityPacketSignedRule_integral : (∫ᵛ e, (fun z ε => G ζ z ε * responseMatrixAction q C (A ζ) c Φ) e.1 e.2 ∂<•(densityPacketSignedRule a b m r D)) =
      densityPacketAction a b m r D (fun z ε => G ζ z ε * responseMatrixAction q C (A ζ) c Φ) := by
    rw [densityPacketSignedRule, atomicSignedRule_integral]
    simp only [Fintype.sum_prod_type, densityPacketWeight, densityPacketAtom,
      densityPacketAction, densityDerivativeAction]
    simp only [Finset.mul_sum, mul_assoc]
  have hi := h_densityPacketSignedRule_integral
  rw [densityPacketSignedRule, atomicSignedRule_integral] at hi
  exact hi
theorem highPacketSignedMeasure_factor_integral (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (c : ι → ℝ) (G : Z → ℝ → (Fin r → ℝ) → ℝ)
    (hG : ∀ z ε, Measurable (fun ζ => G ζ z ε)) (L : ℝ) (hL : 0 ≤ L)
    (hGbound : ∀ (ζ : Z) (h : HighDensityMarkIndex m r D),
      |G ζ (densityPacketAtom a b m r D h).1 (densityPacketAtom a b m r D h).2| ≤ L)
    (Φ : (ι → ℝ) → ℝ) (M : ℝ)
    (hΦ : ∀ h : HighResponseMarkIndex ι q,
      |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)| ≤ M) :
    (∫ᵛ e, highPacketObservable a b m r D q C c G Φ e
      ∂<•(highPacketSignedMeasure σ a b m r D q C A)) =
      highSeparatedPacketAction σ a b m r D q C A c G Φ := by
  have hmF (h : HighPacketMarkIndex ι m r D q) :
      Measurable (fun ζ => highPacketObservable a b m r D q C c G Φ (ζ, h)) := by
    change Measurable (fun ζ => G ζ (densityPacketAtom a b m r D h.1).1
      (densityPacketAtom a b m r D h.1).2 *
        Φ (coefficientReset c (highResponseMarkAtom C q h.2).2 (highResponseMarkAtom C q h.2).1))
    exact (hG _ _).mul_const _
  have h_highPacketSignedMeasure_integral (F : Z × HighPacketMarkIndex ι m r D q → ℝ) (hF : ∀ h, Measurable (fun ζ => F (ζ, h))) (M : ℝ) (hBound : ∀ ζ h, ‖F (ζ, h)‖ ≤ M) : (∫ᵛ e, F e ∂<•(highPacketSignedMeasure σ a b m r D q C A)) =
      ∫ ζ, ∑ h : HighPacketMarkIndex ι m r D q,
        highPacketMarkWeight a b m r D q C A (ζ, h) * F (ζ, h) ∂σ := by
    have hw := highPacketMarkWeight_integrable σ a b m r D q C A hA hcost
    have hmF  := measurable_from_prod_countable_left hF
    have hb : ∀ e : Z × HighPacketMarkIndex ι m r D q, ‖F e‖ ≤ M := fun e => hBound e.1 e.2
    rw [highPacketSignedMeasure, signedDensity_integral _ _ hw
      (highPacketMarkWeight_measurable a b m r D q C A hA) F hmF M hb,
      integral_prod _ (hw.mul_bdd hmF.aestronglyMeasurable (Filter.Eventually.of_forall hb))]
    simp only [integral_count]
  rw [h_highPacketSignedMeasure_integral _ hmF (L * M)]
  · simp only [highPacketObservable_finite_action, highSeparatedPacketAction]
  · intro ζ h
    rw [highPacketObservable, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hGbound ζ h.1) (hΦ h.2) (abs_nonneg _) hL
theorem highResponseMark_variation (q : ℕ) (C : ℝ) (A : ι → ι → ℝ) :
    (∑ h : HighResponseMarkIndex ι q, |highResponseMarkWeight C q A h|) =
      (∑ h : Fin (2 * q + 2), |responseWeight q h|) * (2 * C ^ 2 * ∑ i, ∑ j, |A i j|) := by
  simp only [highResponseMarkWeight, Fintype.sum_prod_type, abs_mul]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [covariance_weight_variation]
theorem highPacketSignedMeasure_totalVariation (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ) :
    ((highPacketSignedMeasure σ a b m r D q C A).variation univ).toReal =
      (∑ h : HighDensityMarkIndex m r D, |densityPacketWeight a b m r D h|) *
        (∑ h : Fin (2 * q + 2), |responseWeight q h|) * (2 * C ^ 2) *
          ∫ ζ, separatedMatrixCost A ζ ∂σ := by
  have h_highPacketSignedMeasure_variation : ((highPacketSignedMeasure σ a b m r D q C A).variation univ).toReal =
      ∫ ζ, ∑ h : HighPacketMarkIndex ι m r D q,
        |highPacketMarkWeight a b m r D q C A (ζ, h)| ∂σ := by
    have hw := highPacketMarkWeight_integrable σ a b m r D q C A hA hcost
    rw [highPacketSignedMeasure, Measure.variation_withDensityᵥ hw,
      withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    rw [← integral_norm_eq_lintegral_enorm hw.aestronglyMeasurable,
      integral_prod _ hw.norm]
    simp only [integral_count, Real.norm_eq_abs]
  rw [h_highPacketSignedMeasure_variation]
  have h_highPacketMarkWeight_variation (ζ : Z) : (∑ h : HighPacketMarkIndex ι m r D q, |highPacketMarkWeight a b m r D q C A (ζ, h)|) =
      (∑ h : HighDensityMarkIndex m r D, |densityPacketWeight a b m r D h|) *
        (∑ h : Fin (2 * q + 2), |responseWeight q h|) * (2 * C ^ 2) * separatedMatrixCost A ζ := by
    rw [Fintype.sum_prod_type]
    simp only [highPacketMarkWeight, abs_mul]
    simp_rw [← Finset.mul_sum, highResponseMark_variation]
    rw [← Finset.sum_mul]
    unfold separatedMatrixCost
    ring
  simp only [h_highPacketMarkWeight_variation]
  rw [integral_const_mul]
theorem densityPacketWeight_exponential_cost (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r D : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) :
    (∑ h : HighDensityMarkIndex m r D, |densityPacketWeight a b m r D h|) ≤
      (Real.exp (1 + exteriorTau ((a + b) / (b - a))) * |b / densityMargin a b 0|) ^ r *
        ↑D ^ r * Real.exp (↑m * exteriorTau ((a + b) / (b - a))) := by
  have h_densityPacketAtom_injective : Function.Injective (densityPacketAtom a b m r D) := by
    intro e f he
    apply Prod.ext
    · exact (exteriorNode_strictAnti a b hab (m + r) (by omega)).injective (congrArg Prod.fst he)
    · funext l
      exact (lobattoNode_strictAnti (derivativeOrder D) (by unfold derivativeOrder; omega)).injective
        (congrArg (fun e : ℝ × (Fin r → ℝ) => e.2 l) he)
  have he := atomicSignedRule_totalVariation_eq (densityPacketAtom a b m r D)
    (densityPacketWeight a b m r D) h_densityPacketAtom_injective
  rw [← he]
  have h_densityPacketSignedRule_totalVariation_bound : ((densityPacketSignedRule a b m r D).variation univ).toReal ≤
      |densityPacketPrefactor a b r| *
        Real.cosh ((m + r : ℕ) * exteriorTau ((a + b) / (b - a))) * ↑D ^ r := by
    apply (atomicSignedRule_totalVariation_le _ _).trans
    rw [densityPacketWeight_variation a b ha hab m r D hr]
    have h_derivative_rule_variation : (∑ i : Fin (derivativeOrder D + 1), |lobattoDerivativeWeight ((D - 1) / 2) i|) =
      derivativeOrder D ∧ (derivativeOrder D : ℝ) ≤ D := by
      constructor
      · exact lobatto_derivative_rule_variation ((D - 1) / 2)
      · exact_mod_cast (derivativeOrder_bounds D hD).1
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) h_derivative_rule_variation.2 r)
      (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le)
  apply h_densityPacketSignedRule_totalVariation_bound.trans
  calc
    _ ≤ Real.exp ↑r * |b / densityMargin a b 0| ^ r *
        Real.exp ((m + r : ℕ) * exteriorTau ((a + b) / (b - a))) * ↑D ^ r := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have h_densityPacketPrefactor_abs_le : |densityPacketPrefactor a b r| ≤ Real.exp ↑r * |b / densityMargin a b 0| ^ r := by
        unfold densityPacketPrefactor
        rw [abs_mul, abs_pow, abs_of_nonneg (by positivity : 0 ≤ (r : ℝ) ^ r / (r.factorial : ℝ))]
        exact mul_le_mul_of_nonneg_right (Real.pow_div_factorial_le_exp ↑r (Nat.cast_nonneg r) r)
          (by positivity)
      exact mul_le_mul h_densityPacketPrefactor_abs_le (by rw [← exterior_rule_variation a b ha hab (m + r) (by omega)]; exact exterior_rule_variation_le_exp a b ha hab (m + r) (by omega)) (Real.cosh_pos _).le
        (mul_nonneg (Real.exp_pos _).le (by positivity))
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul]
      have heq : Real.exp ↑r *
          Real.exp ((m + r : ℕ) * exteriorTau ((a + b) / (b - a))) =
          Real.exp (↑r * (1 + exteriorTau ((a + b) / (b - a)))) *
            Real.exp (↑m * exteriorTau ((a + b) / (b - a))) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        push_cast
        ring
      calc
        _ = Real.exp ↑r * Real.exp ((m + r : ℕ) * exteriorTau ((a + b) / (b - a))) *
            |b / densityMargin a b 0| ^ r * ↑D ^ r := by ring
        _ = _ := by rw [heq]; ring
theorem highPacketSignedMeasure_exponential_cost (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (m r D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (C : ℝ) (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) :
    ((highPacketSignedMeasure σ a b m r D q C A).variation univ).toReal ≤
      ((Real.exp (1 + exteriorTau ((a + b) / (b - a))) * |b / densityMargin a b 0|) ^ r *
        ↑D ^ r * Real.exp (↑m * exteriorTau ((a + b) / (b - a)))) *
          (∑ h : Fin (2 * q + 2), |responseWeight q h|) * (2 * C ^ 2) *
            ∫ ζ, separatedMatrixCost A ζ ∂σ := by
  rw [highPacketSignedMeasure_totalVariation σ a b m r D q C A hA hcost]
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right (densityPacketWeight_exponential_cost a b ha hab m r D hr hD)
        (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    · positivity
  · apply integral_nonneg
    intro ζ
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg (A ζ i j)))
variable {α : Type*} [DecidableEq α]
end Packet
end NearlyMinimax
