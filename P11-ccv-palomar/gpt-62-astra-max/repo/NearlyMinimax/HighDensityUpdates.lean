module

public import NearlyMinimax.AtomicVariation
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

/-! The genuine finite density-mark operator used by the high-smoothness
lower bound. Tensor derivative marks are proved to extract the square-free
coefficient, and exterior marks produce the count selector. -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Polynomial
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def densityDerivativeWeight {D : ℕ} (j : Fin (derivativeOrder D + 1)) : ℝ :=
  lobattoDerivativeWeight j

/-- The exponent selected by one first-derivative mark in every coordinate. -/
def densityUnitExponent (r : ℕ) : Fin r →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun _ => 1) (by simp)

section
variable {ι : Type*} (r D : ℕ) (B : ι → Fin r → ℝ) (i : ι)

@[simp] theorem densityUnitExponent_apply (i : Fin r) :
    densityUnitExponent r i = 1 := rfl

@[simp] theorem densityUnitExponent_degree :
    (densityUnitExponent r).degree = r := by
  simp [Finsupp.degree_eq_sum]

/-- Actual product of the finite Chebyshev derivative marks. -/
def densityDerivativeAction (f : (Fin r → ℝ) → ℝ) : ℝ :=
  ∑ h : Fin r → Fin (derivativeOrder D + 1),
    (∏ l, densityDerivativeWeight (h l)) *
      f (fun l => lobattoNode (h l))

section
variable (hD : 1 ≤ D)
include hD

theorem derivative_rule_monomial {k : ℕ} (hk : k ≤ D) :
    (∑ j : Fin (derivativeOrder D + 1),
      densityDerivativeWeight j *
        lobattoNode j ^ k) = if k = 1 then 1 else 0 := by
  have hp : (X ^ k : ℝ[X]).degree ≤ D := by
    simpa using WithBot.coe_le_coe.mpr hk
  have h := derivative_rule_exact hD hp
  simpa [densityDerivativeWeight, ← coeff_zero_eq_eval_zero, coeff_derivative,
    coeff_X_pow, eq_comm] using h

theorem densityDerivativeAction_monomial
    {d : Fin r →₀ ℕ} (hd : ∀ l, d l ≤ D) :
    densityDerivativeAction r D (fun ε => ∏ l, ε l ^ d l) =
      if d = densityUnitExponent r then 1 else 0 := by
  unfold densityDerivativeAction
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun l j =>
    densityDerivativeWeight j * lobattoNode j ^ d l)]
  simp_rw [derivative_rule_monomial D hD (hd _)]
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

/-- Tensor exactness follows from the proved one-variable moments, without
an assumed mixed-derivative or interpolation identity. -/
theorem densityDerivativeAction_polynomial
    (P : MvPolynomial (Fin r) ℝ)
    (hP : ∀ d ∈ P.support, ∀ l, d l ≤ D) :
    densityDerivativeAction r D (fun ε => MvPolynomial.eval ε P) =
      P.coeff (densityUnitExponent r) := by
  unfold densityDerivativeAction
  simp [MvPolynomial.eval_eq', Finset.mul_sum]
  rw [Finset.sum_comm]
  have hm (d : Fin r →₀ ℕ) :
      (∑ h : Fin r → Fin (derivativeOrder D + 1),
        (∏ l, densityDerivativeWeight (h l)) *
          (P.coeff d * ∏ l, lobattoNode (h l) ^ d l)) =
        P.coeff d *
          ∑ h : Fin r → Fin (derivativeOrder D + 1),
            (∏ l, densityDerivativeWeight (h l)) *
              ∏ l, lobattoNode (h l) ^ d l := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    ring
  simp_rw [hm]
  have he (d : Fin r →₀ ℕ) (hd : d ∈ P.support) :
      (∑ h : Fin r → Fin (derivativeOrder D + 1),
        (∏ l, densityDerivativeWeight (h l)) *
          ∏ l, lobattoNode (h l) ^ d l) =
        if d = densityUnitExponent r then 1 else 0 :=
    densityDerivativeAction_monomial r D hD (hP d hd)
  calc
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [he d hd]
    _ = _ := by
      simp
      exact fun h => h.symm

end

/-- Each mark acts on one affine density factor. -/
def densityModulationPolynomial : MvPolynomial (Fin r) ℝ :=
  ∑ l, MvPolynomial.C (B i l) * MvPolynomial.X l

theorem densityModulationPolynomial_homogeneous :
    (densityModulationPolynomial r B i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro l _
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

end

/-- The product of the incoming densities after their affine mark reset. -/
def densityResetPolynomial {ι : Type*} [DecidableEq ι] (S : Finset ι)
    {r : ℕ} (z t : ℝ) (p : ι → ℝ) (B : ι → Fin r → ℝ) : MvPolynomial (Fin r) ℝ :=
  ∏ i ∈ S, (MvPolynomial.C z + MvPolynomial.C (t * p i) *
    densityModulationPolynomial r B i)

theorem densityResetPolynomial_eval {ι : Type*} [DecidableEq ι] (S : Finset ι)
    {r : ℕ} (z t : ℝ) (p : ι → ℝ) (B : ι → Fin r → ℝ) (ε : Fin r → ℝ) :
    MvPolynomial.eval ε (densityResetPolynomial S z t p B) =
      ∏ i ∈ S, (z + t * p i * ∑ l, ε l * B i l) := by
  simp [densityResetPolynomial, densityModulationPolynomial]
  simp [mul_comm (B _ _)]

section
variable {ι : Type*} [DecidableEq ι] (S : Finset ι) {r : ℕ} (z t : ℝ) (p : ι → ℝ) (B : ι → Fin r → ℝ)

theorem densityResetPolynomial_totalDegree :
    (densityResetPolynomial S z t p B).totalDegree ≤ S.card := by
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le
      · simp
      · have h := (densityModulationPolynomial_homogeneous r B i).C_mul (t * p i)
        exact h.totalDegree_le
    _ = _ := by simp

/-- Exactly one occurrence of every mark selects only observation subsets
of cardinality r. -/
theorem densityResetPolynomial_coefficient :
    (densityResetPolynomial S z t p B).coeff (densityUnitExponent r) =
      z ^ (S.card - r) * t ^ r *
        ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
          (∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r) := by
  classical
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
    simp [Finset.prod_const, Finset.prod_mul_distrib]
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
        (fun i _ => densityModulationPolynomial_homogeneous r B i)
      have hzero := hh.coeff_eq_zero (d := densityUnitExponent r) (by simpa using Ne.symm hc)
      simp [hzero]
  rw [Finset.sum_congr rfl hz]
  rw [← Finset.sum_filter, ← Finset.powersetCard_eq_filter, ← Finset.mul_sum]

theorem density_derivative_product_exact
    {S : Finset ι} (r D : ℕ) (hD : 1 ≤ D) (hSD : S.card ≤ D)
    (z t : ℝ) (p : ι → ℝ) (B : ι → Fin r → ℝ) :
    densityDerivativeAction r D (fun ε => ∏ i ∈ S, (z + t * p i * ∑ l, ε l * B i l)) =
      z ^ (S.card - r) * t ^ r *
        ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
          (∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r) := by
  have hf : (fun ε => ∏ i ∈ S, (z + t * p i * ∑ l, ε l * B i l)) =
      (fun ε => MvPolynomial.eval ε (densityResetPolynomial S z t p B)) := by
    funext ε
    exact (densityResetPolynomial_eval S z t p B ε).symm
  rw [hf]
  rw [densityDerivativeAction_polynomial r D hD]
  · exact densityResetPolynomial_coefficient S z t p B
  · intro d hd l
    exact (MvPolynomial.le_degreeOf_of_mem_support l hd).trans
      ((MvPolynomial.degreeOf_le_totalDegree _ _).trans
        ((densityResetPolynomial_totalDegree S z t p B).trans hSD))

end

section
variable (a b z : ℝ) (k r : ℕ)

/-- The quadratic density-interval margin in the manuscript. -/
def densityMargin : ℝ := (z - a) * (b - z) / (b - a)

theorem densityMargin_bounds (hab : a < b) {z : ℝ} (hz : z ∈ Icc a b) :
    0 ≤ densityMargin a b z ∧ densityMargin a b z ≤ z - a ∧
      densityMargin a b z ≤ b - z ∧ densityMargin a b z ≤ (b - a) / 4 := by
  have hba  := sub_pos.mpr hab
  have hn  := sub_nonneg.mpr hz.1
  have hm  := sub_nonneg.mpr hz.2
  dsimp [densityMargin]
  refine ⟨div_nonneg (mul_nonneg hn hm) hba.le, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hba).mpr
    nlinarith
  · apply (div_le_iff₀ hba).mpr
    nlinarith
  · apply (div_le_iff₀ hba).mpr
    nlinarith [sq_nonneg (z - (a + b) / 2)]

theorem densityMargin_zero_ne (ha : 0 < a) (hab : a < b) :
    densityMargin a b 0 ≠ 0 := by
  exact div_ne_zero (mul_ne_zero (by simpa using ha.ne') (by bound))
    (sub_pos.mpr hab).ne'

def densityMarginPolynomial : ℝ[X] :=
  (X - C a) * (C b - X) * C ((b - a)⁻¹)

@[simp] theorem densityMarginPolynomial_eval :
    (densityMarginPolynomial a b).eval z = densityMargin a b z := by
  simp [densityMarginPolynomial, densityMargin, div_eq_mul_inv]

theorem densityMarginPolynomial_natDegree :
    (densityMarginPolynomial a b).natDegree ≤ 2 := by
  apply (natDegree_mul_le).trans
  have h₁ : (X - C a : ℝ[X]).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (by simp)
  have h₂ : (C b - X : ℝ[X]).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (by simp)
  have hm := (natDegree_mul_le (p := X - C a) (q := C b - X)).trans (add_le_add h₁ h₂)
  simpa using hm

def densityCountPolynomial : ℝ[X] :=
  X ^ (k - r) * densityMarginPolynomial a b ^ r

@[simp] theorem densityCountPolynomial_eval :
    (densityCountPolynomial a b k r).eval z = z ^ (k - r) * densityMargin a b z ^ r := by
  simp [densityCountPolynomial]

theorem densityCountPolynomial_natDegree (hrk : r ≤ k) :
    (densityCountPolynomial a b k r).natDegree ≤ k + r := by
  apply (natDegree_mul_le).trans
  have hp := (natDegree_pow_le (p := densityMarginPolynomial a b) (n := r)).trans
    (Nat.mul_le_mul_left r (densityMarginPolynomial_natDegree a b))
  simp only [natDegree_X_pow]
  omega

/-- The actual exterior count factor, including counts above the cutoff. -/
def densityCountCoefficient (m r k : ℕ) : ℝ :=
  (∑ j : Fin (m + r + 1), exteriorWeight a b j *
    (exteriorNode a b j ^ (k - r) *
      densityMargin a b (exteriorNode a b j) ^ r)) / densityMargin a b 0 ^ r

end

section
variable (a b : ℝ) (ha : 0 < a) (hab : a < b) (m r k : ℕ) (hr : 1 ≤ r)
include ha hab hr

/-- Exact target-count selection is derived from the concrete exterior
rule: every other count through m is annihilated. -/
theorem densityCountCoefficient_exact (hrk : r ≤ k) (hkm : k ≤ m) :
    densityCountCoefficient a b m r k = if k = r then 1 else 0 := by
  have hdeg : (densityCountPolynomial a b k r).degree ≤ m + r :=
    degree_le_natDegree.trans (by
      exact_mod_cast (densityCountPolynomial_natDegree a b k r hrk).trans (Nat.add_le_add_right hkm r))
  have he := exterior_rule_exact hab (n := (m + r)) (by omega) hdeg
  simp at he
  unfold densityCountCoefficient
  rw [he]
  by_cases hkr : k = r
  · subst k
    simp [pow_ne_zero r (densityMargin_zero_ne a b ha hab)]
  · have hpos : k - r ≠ 0 := by omega
    simp [zero_pow hpos, hkr]

/-- Uniform finite-variation control for the count factor beyond the cutoff. -/
theorem densityCountCoefficient_abs_bound :
    let ratio := b ^ (k - r) * ((b - a) / 4) ^ r
    |densityCountCoefficient a b m r k| ≤
      (ratio / |densityMargin a b 0| ^ r) *
        Real.cosh ((m + r : ℕ) * intervalExteriorTau a b) := by
  intro ratio
  have hb : ∀ j : Fin (m + r + 1),
      |exteriorNode a b j ^ (k - r) *
        densityMargin a b (exteriorNode a b j) ^ r| ≤
      ratio := by
    intro j
    have hz := exteriorNode_mem hab.le j
    have ht := densityMargin_bounds a b hab hz
    rw [abs_mul, abs_pow, abs_pow, abs_of_nonneg (ha.le.trans hz.1), abs_of_nonneg ht.1]
    bound
  have hs : |∑ j : Fin (m + r + 1), exteriorWeight a b j *
      (exteriorNode a b j ^ (k - r) *
        densityMargin a b (exteriorNode a b j) ^ r)| ≤
      Real.cosh ((m + r : ℕ) * intervalExteriorTau a b) *
        (ratio) := by
    calc
      _ ≤ ∑ j : Fin (m + r + 1), |exteriorWeight a b j| *
          (ratio) := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        bound
      _ = _ := by rw [← Finset.sum_mul, exterior_rule_variation ha hab _ (by omega)]
  unfold densityCountCoefficient
  rw [abs_div, abs_pow]
  exact (div_le_div_of_nonneg_right hs (by positivity)).trans_eq (by ring)

end

/-- The incoming density is reset exactly as in (LB-loc-update). -/
def localDensityReset {ι : Type*} (a b : ℝ) {r : ℕ} (z : ℝ)
    (ε : Fin r → ℝ) (p : ι → ℝ) (B : ι → Fin r → ℝ) (i : ι) : ℝ :=
  z + densityMargin a b z / ((r : ℝ) * b) * p i * ∑ l, ε l * B i l

section
variable {ι : Type*} (a b : ℝ) (ha : 0 < a) (hab : a < b) (r : ℕ) (hr : 1 ≤ r) (z : ℝ) (hz : z ∈ Icc a b)
    (ε : Fin r → ℝ) (hε : ∀ l, |ε l| ≤ 1)
include ha hab hr hz hε

theorem localDensityReset_slope_bound {B : ι → Fin r → ℝ} (i : ι)
    (hB : ∀ l, |B i l| ≤ 1) :
    |densityMargin a b z / ((r : ℝ) * b) * ∑ l, ε l * B i l| ≤
      (b - a) / (4 * b) := by
  have hb  := ha.trans hab
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hθ := densityMargin_bounds a b hab hz
  have hsum : |∑ l, ε l * B i l| ≤ (r : ℝ) := by
    calc
      _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin r, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro l _
        rw [abs_mul]
        bound
      _ = _ := by simp
  have hcoef  :=
    div_nonneg hθ.1 (mul_pos hrR hb).le
  rw [abs_mul, abs_of_nonneg hcoef]
  calc
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left hsum hcoef
    _ = densityMargin a b z / b := by field_simp
    _ ≤ ((b - a) / 4) / b := by bound
    _ = _ := by ring

theorem localDensityReset_mem_interval {p : ι → ℝ}
    (B : ι → Fin r → ℝ) {i : ι} (hp : p i ∈ Icc a b) (hB : ∀ l, |B i l| ≤ 1) :
    localDensityReset a b z ε p B i ∈ Icc a b := by
  have hb  := ha.trans hab
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hθ := densityMargin_bounds a b hab hz
  have hp0  := ha.le.trans hp.1
  have hsum : |∑ l, ε l * B i l| ≤ (r : ℝ) := by
    calc
      _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin r, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro l _
        rw [abs_mul]
        bound
      _ = _ := by simp
  have hcoef  :=
    div_nonneg hθ.1 (mul_pos hrR hb).le
  have hshift : |densityMargin a b z / ((r : ℝ) * b) * p i * ∑ l, ε l * B i l| ≤
      densityMargin a b z := by
    rw [abs_mul, abs_mul, abs_of_nonneg hcoef, abs_of_nonneg hp0]
    calc
      _ ≤ densityMargin a b z / ((r : ℝ) * b) * p i * r :=
        by bound
      _ = _ := by field_simp
      _ ≤ _ :=
        mul_le_mul_of_nonneg_left hp.2 (div_nonneg hθ.1 hb.le)
      _ = _ := div_mul_cancel₀ _ hb.ne'
  obtain ⟨hl, hu⟩ := abs_le.mp hshift
  constructor <;> dsimp [localDensityReset] <;> linarith [hθ.2.1, hθ.2.2.1]

end

section
variable {ι : Type*} (a b : ℝ) (m r D : ℕ)

/-- Symmetrization is the square-free coefficient divided by r!: it is
independent of any ordering chosen for the observation subset. -/
def densitySeparatedSym [DecidableEq ι] (r : ℕ)
    (B : ι → Fin r → ℝ) (S : Finset ι) : ℝ :=
  (∏ i ∈ S, densityModulationPolynomial r B i).coeff (densityUnitExponent r) /
    (r.factorial : ℝ)

def densityPacketPrefactor : ℝ :=
  (r : ℝ) ^ r / (r.factorial : ℝ) * (b / densityMargin a b 0) ^ r

/-- The exact finite action of Gamma_{r,m}. -/
def densityPacketAction (f : ℝ → (Fin r → ℝ) → ℝ) : ℝ :=
  densityPacketPrefactor a b r * ∑ j : Fin (m + r + 1),
    exteriorWeight a b j *
      densityDerivativeAction r D (f (exteriorNode a b j))

theorem density_packet_product_exact [DecidableEq ι]
    {S : Finset ι} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (m : ℕ) {r D : ℕ} (hr : 1 ≤ r) (hD : 1 ≤ D) (hSD : S.card ≤ D)
    (p : ι → ℝ) (B : ι → Fin r → ℝ) :
    densityPacketAction a b m r D (fun z ε => ∏ i ∈ S, localDensityReset a b z ε p B i) =
      densityCountCoefficient a b m r S.card *
        ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) * densitySeparatedSym r B U := by
  have hb  := (ha.trans hab).ne'
  unfold densityPacketAction localDensityReset
  simp_rw [density_derivative_product_exact r D hD hSD]
  unfold densityCountCoefficient densitySeparatedSym
  have hsum : (∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
      ((∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r) /
        r.factorial)) =
      (∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
        (∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r)) /
        r.factorial := by simp_rw [← mul_div_assoc]; rw [Finset.sum_div]
  rw [hsum]
  unfold densityPacketPrefactor
  simp [div_pow, mul_pow]
  rw [Finset.mul_sum]
  calc
    _ = ∑ j : Fin (m + r + 1),
      (exteriorWeight a b j *
        (exteriorNode a b j ^ (S.card - r) *
          densityMargin a b (exteriorNode a b j) ^ r) / densityMargin a b 0 ^ r) *
        ((∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
          (∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r)) /
          r.factorial) := by
      apply Finset.sum_congr rfl
      intro j _
      field_simp
    _ = _ := by simp [← Finset.sum_mul, Finset.sum_div]

private def densityAssignmentExponent {r : ℕ} (f : Fin r → Fin r) : Fin r →₀ ℕ :=
  ∑ i, Finsupp.single (f i) 1

private theorem densityAssignmentExponent_eq_unit_iff (f : Fin r → Fin r) :
    densityAssignmentExponent f = densityUnitExponent r ↔ Function.Bijective f := by
  classical
  constructor
  · intro he
    have hs : Function.Surjective f := by
      intro l
      by_contra hn
      have hne (i : Fin r) : f i ≠ l := fun h => hn ⟨i, h⟩
      have hv := congrArg (fun d : Fin r →₀ ℕ => d l) he
      simp [densityAssignmentExponent, hne] at hv
    exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  · intro hf
    let e := Equiv.ofBijective f hf
    change (∑ i, Finsupp.single (e i) 1) = _
    rw [e.sum_comp (fun l => Finsupp.single l 1)]
    ext l
    simp

/-- The selected coefficient is the genuine permanent, hence the sum of
all r! assignments of distinct marks to distinct observations. -/
theorem density_linear_product_permanent (B : Fin r → Fin r → ℝ) :
    (∏ i, densityModulationPolynomial r B i).coeff (densityUnitExponent r) =
      ∑ σ : Equiv.Perm (Fin r), ∏ i, B i (σ i) := by
  classical
  unfold densityModulationPolynomial
  rw [Fintype.prod_sum]
  simp_rw [MvPolynomial.C_mul_X_eq_monomial]
  have hm (f : Fin r → Fin r) :
      (∏ i, MvPolynomial.monomial (Finsupp.single (f i) 1) (B i (f i))) =
      MvPolynomial.monomial (densityAssignmentExponent f) (∏ i, B i (f i)) :=
    (MvPolynomial.monomial_sum_prod Finset.univ _ _).symm
  simp_rw [hm]
  simp
  simp only [densityAssignmentExponent_eq_unit_iff]
  have hs : (∑ f : Fin r → Fin r, if Function.Bijective f then ∏ i, B i (f i) else 0) =
      ∑ f : {f : Fin r → Fin r // Function.Bijective f}, ∏ i, B i (f.1 i) := by
    apply Finset.sum_congr_set {f : Fin r → Fin r | Function.Bijective f}
    · solve_by_elim [if_pos]
    · solve_by_elim [if_neg]
  rw [hs]
  apply Fintype.sum_equiv Equiv.bijectiveEquiv
  intro f
  rfl

/-- Coefficient-based symmetrization agrees with the paper's average over
permutations, for every enumeration of a cardinality-r subset. -/
theorem densitySeparatedSym_eq_permutation_average [DecidableEq ι]
    {r : ℕ} (B : ι → Fin r → ℝ) {S : Finset ι} (e : Fin r ≃ S) :
    densitySeparatedSym r B S =
      (∑ σ : Equiv.Perm (Fin r), ∏ i, B (e i) (σ i)) / (r.factorial : ℝ) := by
  unfold densitySeparatedSym
  have he : (∏ i ∈ S, densityModulationPolynomial r B i) =
      ∏ i : Fin r, densityModulationPolynomial r (fun i l => B (e i) l) i := by
    rw [← Finset.prod_coe_sort]
    exact (e.prod_comp (fun i : S => densityModulationPolynomial r B i)).symm
  rw [he, density_linear_product_permanent]

end

section
variable {ι : Type*} [DecidableEq ι] (S : Finset ι) (a b : ℝ) (ha : 0 < a) (hab : a < b) (m r D : ℕ)
    (hr : 1 ≤ r) (hD : 1 ≤ D) (hSD : S.card ≤ D)
include hD hSD ha hab hr

theorem density_packet_product_zero_of_small_count
    (hSr : S.card < r) (p : ι → ℝ) (B : ι → Fin r → ℝ) :
    densityPacketAction a b m r D (fun z ε => ∏ i ∈ S, localDensityReset a b z ε p B i) = 0 := by
  rw [density_packet_product_exact ha hab m hr hD hSD p B,
    Finset.powersetCard_eq_empty.mpr hSr]
  simp

/-- The full count selector identity for all counts through m. -/
theorem density_packet_product_count_selector
    (hSm : S.card ≤ m) (p : ι → ℝ) (B : ι → Fin r → ℝ) :
    densityPacketAction a b m r D (fun z ε => ∏ i ∈ S, localDensityReset a b z ε p B i) =
      if S.card = r then ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) * densitySeparatedSym r B U else 0 := by
  by_cases hSr : r ≤ S.card
  · rw [density_packet_product_exact ha hab m hr hD hSD p B,
      densityCountCoefficient_exact a b ha hab m r S.card hr hSr hSm]
    split_ifs <;> simp
  · rw [density_packet_product_zero_of_small_count S a b ha hab m r D hr hD hSD (by omega) p B,
      if_neg (by omega)]

end

section
variable (a b : ℝ) (m r D : ℕ) (j : Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1)))

def densityPacketAtom : ℝ × (Fin r → ℝ) :=
  (exteriorNode a b j.1, fun l => lobattoNode (j.2 l))

def densityPacketWeight : ℝ :=
  densityPacketPrefactor a b r * exteriorWeight a b j.1 *
    ∏ l, densityDerivativeWeight (j.2 l)

/-- Gamma_{r,m} as an actual finite signed measure on density marks. -/
def densityPacketSignedRule : SignedMeasure (ℝ × (Fin r → ℝ)) :=
  atomicSignedRule (densityPacketAtom a b m r D) (densityPacketWeight a b m r D)

theorem densityPacketSignedRule_integral
    (f : ℝ → (Fin r → ℝ) → ℝ) :
    (∫ᵛ e, f e.1 e.2 ∂<•(densityPacketSignedRule a b m r D)) =
      densityPacketAction a b m r D f := by
  rw [densityPacketSignedRule, atomicSignedRule_integral]
  simp only [Fintype.sum_prod_type, densityPacketWeight, densityPacketAtom,
    densityPacketAction, densityDerivativeAction]
  simp [Finset.mul_sum, mul_assoc]

theorem densityPacketAtom_mem (hab : a ≤ b) {m r D : ℕ}
    (j : Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1))) :
    (densityPacketAtom a b m r D j).1 ∈ Icc a b ∧
      ∀ l, |(densityPacketAtom a b m r D j).2 l| ≤ 1 := by
  constructor
  · solve_by_elim [exteriorNode_mem]
  · intro l
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

end

theorem densityDerivativeWeight_variation (D : ℕ) :
    (∑ j : Fin (derivativeOrder D + 1), |densityDerivativeWeight j|) = (derivativeOrder D : ℝ) :=
  lobatto_derivative_rule_variation ((D - 1) / 2)

theorem densityDerivativeWeight_tensor_variation (r D : ℕ) :
    (∑ h : Fin r → Fin (derivativeOrder D + 1), ∏ l, |densityDerivativeWeight (h l)|) =
      (derivativeOrder D : ℝ) ^ r := by
  rw [← Fintype.prod_sum (fun _l j =>
    |densityDerivativeWeight j|)]
  simp [densityDerivativeWeight_variation]

section
variable (a b : ℝ) (ha : 0 < a) (hab : a < b) (m r D : ℕ) (hr : 1 ≤ r)
include ha hab hr

theorem densityPacketWeight_variation :
    (∑ j : Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1)),
      |densityPacketWeight a b m r D j|) =
      |densityPacketPrefactor a b r| *
        Real.cosh ((m + r : ℕ) * intervalExteriorTau a b) * (derivativeOrder D : ℝ) ^ r := by
  simp only [densityPacketWeight, abs_mul, Finset.abs_prod, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, densityDerivativeWeight_tensor_variation]
  rw [← Finset.sum_mul, ← Finset.mul_sum, exterior_rule_variation ha hab _ (by omega)]

theorem densityPacketSignedRule_totalVariation_bound (hD : 1 ≤ D) :
    ((densityPacketSignedRule a b m r D).variation univ).toReal ≤
      |densityPacketPrefactor a b r| *
        Real.cosh ((m + r : ℕ) * intervalExteriorTau a b) * (D : ℝ) ^ r := by
  apply (atomicSignedRule_totalVariation_le _ _).trans
  rw [densityPacketWeight_variation a b ha hab m r D hr]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (derivative_rule_variation hD).2 r)
    (by positivity)

end

/-- The factorial normalization has the required exponential cost. -/
theorem densityPacketPrefactor_abs_le (a b : ℝ) (r : ℕ) :
    |densityPacketPrefactor a b r| ≤ Real.exp (r : ℝ) * |b / densityMargin a b 0| ^ r := by
  unfold densityPacketPrefactor
  rw [abs_mul, abs_pow, abs_of_nonneg (by positivity : 0 ≤ (r : ℝ) ^ r / r.factorial)]
  exact mul_le_mul_of_nonneg_right (Real.pow_div_factorial_le_exp (r : ℝ) (Nat.cast_nonneg r) r)
    (by positivity)

/-- The actual packet has cost C^r D^r exp(m tau), with an explicit C
depending only on the fixed density interval. -/
theorem densityPacketSignedRule_exponential_cost (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r D : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) :
    ((densityPacketSignedRule a b m r D).variation univ).toReal ≤
      (Real.exp (1 + intervalExteriorTau a b) * |b / densityMargin a b 0|) ^ r *
        (D : ℝ) ^ r * Real.exp ((m : ℝ) * intervalExteriorTau a b) := by
  let expScale := Real.exp ((m + r : ℕ) * intervalExteriorTau a b)
  have he : Real.cosh ((m + r : ℕ) * intervalExteriorTau a b) ≤
      expScale := by
    rw [← exterior_rule_variation ha hab (m + r) (by omega)]
    exact exterior_rule_variation_le_exp ha hab (m + r) (by omega)
  apply (densityPacketSignedRule_totalVariation_bound a b ha hab m r D hr hD).trans
  calc
    _ ≤ Real.exp (r : ℝ) * |b / densityMargin a b 0| ^ r *
        expScale * (D : ℝ) ^ r := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul (densityPacketPrefactor_abs_le a b r) he (Real.cosh_pos _).le
        (by positivity)
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul]
      have heq : Real.exp (r : ℝ) *
          expScale =
          Real.exp ((r : ℝ) * (1 + intervalExteriorTau a b)) *
            Real.exp ((m : ℝ) * intervalExteriorTau a b) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        push_cast
        ring
      grind

theorem densitySeparatedSym_abs_le_one {ι : Type*} [DecidableEq ι]
    {r : ℕ} (B : ι → Fin r → ℝ) {S : Finset ι} (hS : S.card = r)
    (hB : ∀ i ∈ S, ∀ l, |B i l| ≤ 1) : |densitySeparatedSym r B S| ≤ 1 := by
  classical
  let e  := (Fintype.equivFinOfCardEq (show Fintype.card S = r by simpa)).symm
  rw [densitySeparatedSym_eq_permutation_average B e, abs_div,
    abs_of_pos (by exact_mod_cast r.factorial_pos : (0 : ℝ) < r.factorial)]
  apply (div_le_iff₀ (by exact_mod_cast r.factorial_pos : (0 : ℝ) < r.factorial)).mpr
  calc
    _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin r), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro σ _
      rw [Finset.abs_prod]
      exact (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hB (e i) (e i).2 (σ i))).trans_eq
        (by simp)
    _ = _ := by simp [Fintype.card_perm]

end NearlyMinimax
