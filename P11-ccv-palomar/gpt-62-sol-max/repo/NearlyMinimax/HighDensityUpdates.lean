module

public import NearlyMinimax.FiniteBounds

public import NearlyMinimax.AtomicRules
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

def densityDerivativeWeight (D : ℕ) (j : Fin (derivativeOrder D + 1)) : ℝ :=
  lobattoDerivativeWeight ((D - 1) / 2) j

/-- Actual product of the finite Chebyshev derivative marks. -/
def densityDerivativeAction (r D : ℕ) (f : (Fin r → ℝ) → ℝ) : ℝ :=
  ∑ h : Fin r → Fin (derivativeOrder D + 1),
    (∏ l, densityDerivativeWeight D (h l)) *
      f (fun l => lobattoNode (derivativeOrder D) (h l))

theorem derivative_rule_monomial (D : ℕ) (hD : 1 ≤ D) (k : ℕ) (hk : k ≤ D) :
    (∑ j : Fin (derivativeOrder D + 1),
      densityDerivativeWeight D j *
        lobattoNode (derivativeOrder D) j ^ k) = if k = 1 then 1 else 0 := by
  have hp : (X ^ k : ℝ[X]).degree ≤ D := by
    simp_all
  have h := derivative_rule_exact D hD (X ^ k) hp
  simpa [densityDerivativeWeight, ← coeff_zero_eq_eval_zero, coeff_derivative,
    coeff_X_pow, eq_comm] using h

private theorem densityDerivativeAction_linear_sum {ι : Type*} (r D : ℕ)
    (S : Finset ι) (c : ι → ℝ) (F : ι → (Fin r → ℝ) → ℝ) :
    densityDerivativeAction r D (fun ε => ∑ i ∈ S, c i * F i ε) =
      ∑ i ∈ S, c i * densityDerivativeAction r D (F i) := by
  unfold densityDerivativeAction
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  grind [Finset.sum_congr]

private theorem all_fibers_card_one_iff_bijective {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (f : ι → κ) : (∀ j, Fintype.card {i // f i = j} = 1) ↔ Function.Bijective f := by
  simp only [Fintype.card_eq_one_iff, Function.bijective_iff_existsUnique, ExistsUnique,
    Subtype.exists, Subtype.forall, Subtype.mk.injEq, exists_prop]

/-- Each coordinate's derivative mark selects exactly one assigned factor. -/
private theorem densityDerivativeAction_assignment {ι : Type*} [Fintype ι] {r D : ℕ}
    (hD : 1 ≤ D) (hd : Fintype.card ι ≤ D) (f : ι → Fin r) :
    densityDerivativeAction r D (fun ε => ∏ i, ε (f i)) = if Function.Bijective f then 1 else 0 := by
  classical
  have he (ε : Fin r → ℝ) : (∏ i, ε (f i)) = ∏ j, ε j ^ Fintype.card {i // f i = j} := by
    simpa using (Fintype.prod_fiberwise' f ε).symm
  simp_rw [he, densityDerivativeAction, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j h => densityDerivativeWeight D h *
    lobattoNode (derivativeOrder D) h ^ Fintype.card {i // f i = j})]
  simp_rw [derivative_rule_monomial D hD _ ((Fintype.card_subtype_le _).trans hd)]
  simp [Fintype.prod_ite_zero, all_fibers_card_one_iff_bijective]

/-- Sum over distinct assignments of the marks, without choosing an ordering
on the observation subset. -/
def densityMarkSum {ι : Type*} [DecidableEq ι] (r : ℕ)
    (B : ι → Fin r → ℝ) (S : Finset ι) : ℝ :=
  ∑ f : S ≃ Fin r, ∏ i : S, B i (f i)

section
variable {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (r D : ℕ) (hD : 1 ≤ D) (hSD : S.card ≤ D)
include hD hSD

private theorem densityDerivativeAction_linear_product (B : ι → Fin r → ℝ) :
    densityDerivativeAction r D (fun ε => ∏ i ∈ S, ∑ j, ε j * B i j) = densityMarkSum r B S := by
  classical
  have he (ε : Fin r → ℝ) : (∏ i ∈ S, ∑ j, ε j * B i j) =
      ∑ f : S → Fin r, (∏ i : S, B i (f i)) * ∏ i : S, ε (f i) := by
    rw [← Finset.prod_coe_sort, Fintype.prod_sum]
    simp only [Finset.prod_mul_distrib]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  simp_rw [he, densityDerivativeAction_linear_sum,
    densityDerivativeAction_assignment (ι := S) hD (by simpa using hSD),
    mul_ite, mul_one, mul_zero]
  have hmem (u : S → Fin r) : u ∈ Finset.univ.filter (fun f : S → Fin r => Function.Bijective f) ↔
      Function.Bijective u := by simp
  rw [densityMarkSum, ← Finset.sum_filter, Finset.sum_subtype _ hmem]
  exact Fintype.sum_equiv Equiv.bijectiveEquiv _ _ (fun _ => rfl)

private theorem density_derivative_product_exact
    (z t : ℝ) (p : ι → ℝ) (B : ι → Fin r → ℝ) :
    densityDerivativeAction r D (fun ε => ∏ i ∈ S, (z + t * p i * ∑ l, ε l * B i l)) =
      z ^ (S.card - r) * t ^ r * ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) * densityMarkSum r B U := by
  classical
  simp_rw [add_comm z, Finset.prod_add]
  have he (ε : Fin r → ℝ) :
      (∑ U ∈ S.powerset, (∏ i ∈ U, t * p i * ∑ l, ε l * B i l) * ∏ _i ∈ S \ U, z) =
      ∑ U ∈ S.powerset, (z ^ (S.card - U.card) * t ^ U.card * ∏ i ∈ U, p i) *
        ∏ i ∈ U, ∑ l, ε l * B i l := by
    apply Finset.sum_congr rfl
    intro U hU
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hU)]
    ring
  simp_rw [he, densityDerivativeAction_linear_sum]
  rw [Finset.powersetCard_eq_filter, Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro U hU
  rw [densityDerivativeAction_linear_product U r D hD ((Finset.card_le_card (Finset.mem_powerset.mp hU)).trans hSD)]
  by_cases h : U.card = r
  · simp only [h, if_true]
    ring
  · letI : IsEmpty (U ≃ Fin r) := ⟨fun e => h (by simpa using Fintype.card_congr e)⟩
    simp [h, densityMarkSum]

end

/-- The quadratic density-interval margin in the manuscript. -/
def densityMargin (a b z : ℝ) : ℝ := (z - a) * (b - z) / (b - a)

section
variable (a b : ℝ)

theorem densityMargin_bounds (hab : a < b) (z : ℝ) (hz : z ∈ Icc a b) :
    0 ≤ densityMargin a b z ∧ densityMargin a b z ≤ z - a ∧
      densityMargin a b z ≤ b - z ∧ densityMargin a b z ≤ (b - a) / 4 := by
  have hba := sub_pos.mpr hab
  have hn := sub_nonneg.mpr hz.1
  have hm := sub_nonneg.mpr hz.2
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
  simp [densityMargin] <;> grind

end

def densityMarginPolynomial (a b : ℝ) : ℝ[X] :=
  (X - C a) * (C b - X) * C ((b - a)⁻¹)

@[simp] theorem densityMarginPolynomial_eval (a b z : ℝ) :
    (densityMarginPolynomial a b).eval z = densityMargin a b z := by
  simp [densityMarginPolynomial, densityMargin, div_eq_mul_inv]

theorem densityMarginPolynomial_natDegree (a b : ℝ) :
    (densityMarginPolynomial a b).natDegree ≤ 2 := by
  apply (natDegree_mul_C_le _ _).trans
  apply (natDegree_mul_le).trans
  rw [natDegree_sub (p := C b), natDegree_sub_C, natDegree_sub_C, natDegree_X]

def densityCountPolynomial (a b : ℝ) (k r : ℕ) : ℝ[X] :=
  X ^ (k - r) * densityMarginPolynomial a b ^ r

@[simp] theorem densityCountPolynomial_eval (a b z : ℝ) (k r : ℕ) :
    (densityCountPolynomial a b k r).eval z = z ^ (k - r) * densityMargin a b z ^ r := by
  simp [densityCountPolynomial]

theorem densityCountPolynomial_natDegree (a b : ℝ) (k r : ℕ) (hrk : r ≤ k) :
    (densityCountPolynomial a b k r).natDegree ≤ k + r := by
  apply (natDegree_mul_le).trans
  have hp := (natDegree_pow_le (p := densityMarginPolynomial a b) (n := r)).trans
    (Nat.mul_le_mul_left r (densityMarginPolynomial_natDegree a b))
  simp only [natDegree_X_pow]
  omega

/-- The actual exterior count factor, including counts above the cutoff. -/
def densityCountCoefficient (a b : ℝ) (m r k : ℕ) : ℝ :=
  (∑ j : Fin (m + r + 1), exteriorWeight a b (m + r) j *
    (exteriorNode a b (m + r) j ^ (k - r) *
      densityMargin a b (exteriorNode a b (m + r) j) ^ r)) / densityMargin a b 0 ^ r

/-- Variation bound for exterior moments, including rescaled density margins. -/
theorem densityExteriorMoment_abs_le (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m k r : ℕ) (hm : 1 ≤ m) (t : ℝ) (ht : 0 ≤ t) :
    |∑ j : Fin (m + 1), exteriorWeight a b m j *
      (exteriorNode a b m j ^ k * (densityMargin a b (exteriorNode a b m j) / t) ^ r)| ≤
      Real.cosh (m * exteriorTau ((a + b) / (b - a))) *
        (b ^ k * (((b - a) / 4) / t) ^ r) := by
  rw [← exterior_rule_variation a b ha hab m hm]
  apply abs_weighted_sum_le
  intro j _
  have hz := exteriorNode_mem a b hab.le m j
  have hd := densityMargin_bounds a b hab _ hz
  have h0 := ha.le.trans hz.1
  have h1 := div_nonneg hd.1 ht
  rw [abs_mul, abs_pow, abs_pow, abs_of_nonneg h0, abs_of_nonneg h1]
  have hb := (ha.trans hab).le
  have hdiv := div_le_div_of_nonneg_right hd.2.2.2 ht
  gcongr
  exact hz.2

section
variable (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r k : ℕ) (hr : 1 ≤ r)
include ha hab hr

/-- Exact target-count selection is derived from the concrete exterior
rule: every other count through m is annihilated. -/
theorem densityCountCoefficient_exact (hrk : r ≤ k) (hkm : k ≤ m) :
    densityCountCoefficient a b m r k = if k = r then 1 else 0 := by
  have hdeg := degree_le_of_natDegree_le ((densityCountPolynomial_natDegree a b k r hrk).trans
    (show k + r ≤ m + r by omega))
  have he := exterior_rule_exact a b hab (m + r) (by omega)
    (densityCountPolynomial a b k r) hdeg
  simp only [densityCountPolynomial_eval] at he
  unfold densityCountCoefficient
  rw [he]
  by_cases hkr : k = r
  · subst k
    simp [pow_ne_zero r (densityMargin_zero_ne a b ha hab)]
  · have hpos : k - r ≠ 0 := by omega
    simp [zero_pow hpos, hkr]

/-- Uniform finite-variation control for the count factor beyond the cutoff. -/
theorem densityCountCoefficient_abs_bound :
    |densityCountCoefficient a b m r k| ≤
      (b ^ (k - r) * ((b - a) / 4) ^ r / |densityMargin a b 0| ^ r) *
        Real.cosh ((m + r : ℕ) * exteriorTau ((a + b) / (b - a))) := by
  have h := densityExteriorMoment_abs_le a b ha hab (m + r) (k - r) r (by omega) 1 (by norm_num)
  simp only [div_one] at h
  unfold densityCountCoefficient
  rw [abs_div, abs_pow]
  exact (div_le_div_of_nonneg_right h (by positivity)).trans_eq (by ring)

end

/-- The incoming density is reset exactly as in (LB-loc-update). -/
def localDensityReset {ι : Type*} (a b : ℝ) (r : ℕ) (z : ℝ)
    (ε : Fin r → ℝ) (p : ι → ℝ) (B : ι → Fin r → ℝ) (i : ι) : ℝ :=
  z + densityMargin a b z / ((r : ℝ) * b) * p i * ∑ l, ε l * B i l

section
variable {ι : Type*} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (r : ℕ) (hr : 1 ≤ r) (z : ℝ) (hz : z ∈ Icc a b)
    (ε : Fin r → ℝ) (hε : ∀ l, |ε l| ≤ 1)
include ha hab hr hz hε

section
variable (B : ι → Fin r → ℝ) (i : ι)
    (hB : ∀ l, |B i l| ≤ 1)
include hB

private theorem localDensityReset_slope_le_margin :
    |densityMargin a b z / ((r : ℝ) * b) * ∑ l, ε l * B i l| ≤ densityMargin a b z / b := by
  have hb := ha.trans hab
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hθ := densityMargin_bounds a b hab z hz
  have hsum : |∑ l, ε l * B i l| ≤ (r : ℝ) := by
    refine (abs_sum_le_card_mul (s := Finset.univ) (B := 1) ?_).trans_eq (by simp)
    intro l _
    rw [abs_mul]
    simpa using mul_le_mul (hε l) (hB l) (abs_nonneg _) (zero_le_one' ℝ)
  have hcoef := div_nonneg hθ.1 (mul_pos hrR hb).le
  rw [abs_mul, abs_of_nonneg hcoef]
  exact (mul_le_mul_of_nonneg_left hsum hcoef).trans_eq (by field_simp)

theorem localDensityReset_slope_bound :
    |densityMargin a b z / ((r : ℝ) * b) * ∑ l, ε l * B i l| ≤
      (b - a) / (4 * b) := by
  apply (localDensityReset_slope_le_margin a b ha hab r hr z hz ε hε B i hB).trans
  exact (div_le_div_of_nonneg_right (densityMargin_bounds a b hab z hz).2.2.2
    (ha.trans hab).le).trans_eq (by ring)

end

theorem localDensityReset_mem_interval (p : ι → ℝ)
    (B : ι → Fin r → ℝ) (i : ι) (hp : p i ∈ Icc a b) (hB : ∀ l, |B i l| ≤ 1) :
    localDensityReset a b r z ε p B i ∈ Icc a b := by
  have hb := ha.trans hab
  have ht := densityMargin_bounds a b hab z hz
  have hshift : |p i * (densityMargin a b z / ((r : ℝ) * b) * ∑ l, ε l * B i l)| ≤ densityMargin a b z := by
    rw [abs_mul, abs_of_nonneg (ha.le.trans hp.1)]
    calc
      _ ≤ p i * (densityMargin a b z / b) := mul_le_mul_of_nonneg_left
        (localDensityReset_slope_le_margin a b ha hab r hr z hz ε hε B i hB) (ha.le.trans hp.1)
      _ ≤ b * (densityMargin a b z / b) := mul_le_mul_of_nonneg_right hp.2 (div_nonneg ht.1 hb.le)
      _ = _ := by field_simp
  obtain ⟨hl, hu⟩ := abs_le.mp hshift
  constructor <;> dsimp [localDensityReset] <;> nlinarith only [hl, hu, ht.2.1, ht.2.2.1]

end

/-- The average over all distinct mark assignments. -/
def densitySeparatedSym {ι : Type*} [DecidableEq ι] (r : ℕ)
    (B : ι → Fin r → ℝ) (S : Finset ι) : ℝ :=
  densityMarkSum r B S / (r.factorial : ℝ)

def densityPacketPrefactor (a b : ℝ) (r : ℕ) : ℝ :=
  (r : ℝ) ^ r / (r.factorial : ℝ) * (b / densityMargin a b 0) ^ r

/-- The exact finite action of Gamma_{r,m}. -/
def densityPacketAction (a b : ℝ) (m r D : ℕ) (f : ℝ → (Fin r → ℝ) → ℝ) : ℝ :=
  densityPacketPrefactor a b r * ∑ j : Fin (m + r + 1),
    exteriorWeight a b (m + r) j *
      densityDerivativeAction r D (f (exteriorNode a b (m + r) j))

theorem density_packet_product_exact {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r D : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hSD : S.card ≤ D)
    (p : ι → ℝ) (B : ι → Fin r → ℝ) :
    densityPacketAction a b m r D (fun z ε => ∏ i ∈ S, localDensityReset a b r z ε p B i) =
      densityCountCoefficient a b m r S.card *
        ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) * densitySeparatedSym r B U := by
  have hb := (ha.trans hab).ne'
  have hθ := densityMargin_zero_ne a b ha hab
  have hfac : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
  unfold densityPacketAction localDensityReset
  simp_rw [density_derivative_product_exact S r D hD hSD]
  unfold densityCountCoefficient densitySeparatedSym
  have hsum : (∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
      (densityMarkSum r B U /
        (r.factorial : ℝ))) =
      (∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
        densityMarkSum r B U) /
        (r.factorial : ℝ) := by rw [Finset.sum_div] <;> grind
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
          densityMarkSum r B U) /
          (r.factorial : ℝ)) := by
      apply Finset.sum_congr rfl
      intro j _
      field_simp
    _ = _ := by simp only [← Finset.sum_mul, Finset.sum_div]

section
variable {ι : Type*} [DecidableEq ι]

/-- Reindexing mark assignments by any enumeration gives the permutation average. -/
theorem densitySeparatedSym_eq_permutation_average
    (r : ℕ) (B : ι → Fin r → ℝ) (S : Finset ι) (e : Fin r ≃ S) :
    densitySeparatedSym r B S =
      (∑ σ : Equiv.Perm (Fin r), ∏ i, B (e i) (σ i)) / (r.factorial : ℝ) := by
  unfold densitySeparatedSym densityMarkSum
  congr 1
  apply Fintype.sum_equiv (Equiv.equivCongr e.symm (Equiv.refl _))
  intro f
  exact (e.prod_comp (fun i : S => B i (f i))).symm

section
variable (S : Finset ι) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r D : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hSD : S.card ≤ D)
include ha hab hr hD hSD

theorem density_packet_product_zero_of_small_count
    (hSr : S.card < r) (p : ι → ℝ) (B : ι → Fin r → ℝ) :
    densityPacketAction a b m r D (fun z ε => ∏ i ∈ S, localDensityReset a b r z ε p B i) = 0 := by
  simp [density_packet_product_exact S a b ha hab m r D hr hD hSD p B, Finset.powersetCard_eq_empty.mpr hSr]

/-- The full count selector identity for all counts through m. -/
theorem density_packet_product_count_selector
    (hSm : S.card ≤ m) (p : ι → ℝ) (B : ι → Fin r → ℝ) :
    densityPacketAction a b m r D (fun z ε => ∏ i ∈ S, localDensityReset a b r z ε p B i) =
      if S.card = r then ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) * densitySeparatedSym r B U else 0 := by
  by_cases hSr : r ≤ S.card
  · simp_all [density_packet_product_exact, densityCountCoefficient_exact]
  · aesop (add safe apply [density_packet_product_zero_of_small_count])

end

end

def densityPacketAtom (a b : ℝ) (m r D : ℕ)
    (j : Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1))) : ℝ × (Fin r → ℝ) :=
  (exteriorNode a b (m + r) j.1, fun l => lobattoNode (derivativeOrder D) (j.2 l))

def densityPacketWeight (a b : ℝ) (m r D : ℕ)
    (j : Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1))) : ℝ :=
  densityPacketPrefactor a b r * exteriorWeight a b (m + r) j.1 *
    ∏ l, densityDerivativeWeight D (j.2 l)

/-- Gamma_{r,m} as an actual finite signed measure on density marks. -/
def densityPacketSignedRule (a b : ℝ) (m r D : ℕ) : SignedMeasure (ℝ × (Fin r → ℝ)) :=
  atomicSignedRule (densityPacketAtom a b m r D) (densityPacketWeight a b m r D)

section
variable (a b : ℝ)

theorem densityPacketSignedRule_integral (m r D : ℕ)
    (f : ℝ → (Fin r → ℝ) → ℝ) :
    (∫ᵛ e, f e.1 e.2 ∂<•(densityPacketSignedRule a b m r D)) =
      densityPacketAction a b m r D f := by
  rw [densityPacketSignedRule, atomicSignedRule_integral]
  simp only [Fintype.sum_prod_type, densityPacketWeight, densityPacketAtom,
    densityPacketAction, densityDerivativeAction]
  simp only [Finset.mul_sum, mul_assoc]

theorem densityPacketAtom_mem (hab : a ≤ b) (m r D : ℕ)
    (j : Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1))) :
    (densityPacketAtom a b m r D j).1 ∈ Icc a b ∧
      ∀ l, |(densityPacketAtom a b m r D j).2 l| ≤ 1 := by
  constructor
  · apply exteriorNode_mem <;> assumption
  · intro l
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

section
variable {ι : Type*} (ha : 0 < a) (hab : a < b) (m r D : ℕ) (hr : 1 ≤ r)
    (e : Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1)))
    (p : ι → ℝ) (B : ι → Fin r → ℝ) (i : ι) (hp : p i ∈ Icc a b) (hB : ∀ l, |B i l| ≤ 1)
include ha hab hr hp hB

theorem densityPacketReset_mem :
    localDensityReset a b r (densityPacketAtom a b m r D e).1
      (densityPacketAtom a b m r D e).2 p B i ∈ Icc a b := by
  grind [localDensityReset_mem_interval, densityPacketAtom_mem]

theorem densityPacketReset_abs_le :
    |localDensityReset a b r (densityPacketAtom a b m r D e).1
      (densityPacketAtom a b m r D e).2 p B i| ≤ b := by
  grind [densityPacketReset_mem]

end

end

theorem densityDerivativeWeight_variation (D : ℕ) :
    (∑ j : Fin (derivativeOrder D + 1), |densityDerivativeWeight D j|) = (derivativeOrder D : ℝ) :=
  by apply lobatto_derivative_rule_variation

theorem densityDerivativeWeight_tensor_variation (r D : ℕ) :
    (∑ h : Fin r → Fin (derivativeOrder D + 1), ∏ l, |densityDerivativeWeight D (h l)|) =
      (derivativeOrder D : ℝ) ^ r := by
  rw [← Fintype.prod_sum (fun (_l : Fin r) (j : Fin (derivativeOrder D + 1)) =>
    |densityDerivativeWeight D j|)]
  simp only [densityDerivativeWeight_variation, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

section
variable (a b : ℝ)

section
variable (ha : 0 < a) (hab : a < b)
    (m r D : ℕ) (hr : 1 ≤ r)
include ha hab hr

theorem densityPacketWeight_variation :
    (∑ j : Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1)),
      |densityPacketWeight a b m r D j|) =
      |densityPacketPrefactor a b r| *
        Real.cosh ((m + r : ℕ) * exteriorTau ((a + b) / (b - a))) * (derivativeOrder D : ℝ) ^ r := by
  simp only [densityPacketWeight, abs_mul, Finset.abs_prod, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, densityDerivativeWeight_tensor_variation]
  rw [← Finset.sum_mul, ← Finset.mul_sum, exterior_rule_variation a b ha hab _ (by omega)]

end

/-- The factorial normalization has the required exponential cost. -/
theorem densityPacketPrefactor_abs_le (r : ℕ) :
    |densityPacketPrefactor a b r| ≤ Real.exp (r : ℝ) * |b / densityMargin a b 0| ^ r := by
  unfold densityPacketPrefactor
  rw [abs_mul, abs_pow, abs_of_nonneg (by positivity : 0 ≤ (r : ℝ) ^ r / (r.factorial : ℝ))]
  exact mul_le_mul_of_nonneg_right (Real.pow_div_factorial_le_exp (r : ℝ) (Nat.cast_nonneg r) r)
    (by positivity)

/-- The actual packet has cost C^r D^r exp(m tau), with an explicit C
depending only on the fixed density interval. -/
theorem densityPacketWeight_exponential_cost (ha : 0 < a) (hab : a < b)
    (m r D : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) :
    (∑ h : Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1)), |densityPacketWeight a b m r D h|) ≤
      (Real.exp (1 + exteriorTau ((a + b) / (b - a))) * |b / densityMargin a b 0|) ^ r *
        (D : ℝ) ^ r * Real.exp ((m : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  rw [densityPacketWeight_variation a b ha hab m r D hr]
  set τ := exteriorTau ((a + b) / (b - a))
  have hτ : 0 ≤ τ := exteriorTau_interval_nonneg ha.le hab
  have he : Real.cosh ((m + r : ℕ) * τ) ≤ Real.exp ((m + r : ℕ) * τ) := cosh_le_exp_of_nonneg (by positivity)
  calc
    _ ≤ Real.exp (r : ℝ) * |b / densityMargin a b 0| ^ r *
        Real.exp ((m + r : ℕ) * τ) * (D : ℝ) ^ r := by
      gcongr
      · exact densityPacketPrefactor_abs_le a b r
      · exact_mod_cast (derivative_rule_variation D hD).2
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul, Nat.cast_add, add_mul, Real.exp_add, mul_add, mul_one, Real.exp_add]
      ring

end

theorem densitySeparatedSym_abs_le_one {ι : Type*} [DecidableEq ι]
    (r : ℕ) (B : ι → Fin r → ℝ) (S : Finset ι) (hS : S.card = r)
    (hB : ∀ i ∈ S, ∀ l, |B i l| ≤ 1) : |densitySeparatedSym r B S| ≤ 1 := by
  classical
  let e : Fin r ≃ S := (Fintype.equivFinOfCardEq (show Fintype.card S = r by simpa)).symm
  rw [densitySeparatedSym_eq_permutation_average r B S e, abs_div,
    abs_of_pos (by exact_mod_cast r.factorial_pos : (0 : ℝ) < r.factorial)]
  apply (div_le_iff₀ (by exact_mod_cast r.factorial_pos : (0 : ℝ) < r.factorial)).mpr
  refine (abs_sum_le_card_mul (s := Finset.univ) (B := 1) ?_).trans_eq (by simp [Fintype.card_perm])
  exact fun σ _ => abs_prod_le_one fun i _ => hB (e i) (e i).2 (σ i)

end NearlyMinimax
