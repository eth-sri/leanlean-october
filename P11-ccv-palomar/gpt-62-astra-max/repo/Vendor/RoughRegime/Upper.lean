module

public import Mathlib

@[expose] public section

/-!
Algebraic and analytic ingredients of Section 4.
The declarations explicitly document which paper claims they cover.
-/

noncomputable section
open scoped BigOperators
open Complex
namespace RoughRegime.Upper

/-- The complete cosine generating series, with its constant term corrected to one. -/
def cosineKernel (q : ℂ) (t : ℝ) : ℂ :=
  2 * (∑' k : ℕ, q ^ k * (Real.cos (k * t) : ℂ)) - 1

lemma cosine_geometric_term (q : ℂ) (t : ℝ) (k : ℕ) :
    q ^ k * (Real.cos ((k : ℝ) * t) : ℂ) =
      ((q * Complex.exp ((t : ℂ) * I)) ^ k +
       (q * Complex.exp ((-t : ℂ) * I)) ^ k) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos, mul_pow, mul_pow,
    ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  push_cast
  ring

lemma cosine_geometric_hasSum (q : ℂ) (t : ℝ) (hq : ‖q‖ < 1) :
    HasSum (fun k : ℕ => q ^ k * (Real.cos ((k : ℝ) * t) : ℂ))
      (((1 - q * Complex.exp ((t : ℂ) * I))⁻¹ +
        (1 - q * Complex.exp ((-t : ℂ) * I))⁻¹) / 2) := by
  have ha : ‖q * Complex.exp (t * I)‖ < 1 := by
    simpa using hq
  have hb : ‖q * Complex.exp (-t * I)‖ < 1 := by
    simpa only [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one] using hq
  convert ((hasSum_geometric_of_norm_lt_one ha).add
    (hasSum_geometric_of_norm_lt_one hb)).div_const 2 using 1
  ext k
  exact cosine_geometric_term ..

section
variable (lo hi : ℝ) {q : ℂ}

/-- Poisson-kernel identity underlying Lemma 4, for complex `q` in the open unit disk. -/
theorem cosineKernel_eq (t : ℝ) (hq : ‖q‖ < 1) :
    cosineKernel q t =
      (1 - q ^ 2) / (1 - 2 * q * (Real.cos t) + q ^ 2) := by
  let E  := Complex.exp (t * I)
  let F  := Complex.exp ((-t) * I)
  have hEF : E * F = 1 := by
    dsimp [E, F]
    rw [← Complex.exp_add]
    simp
  have hsum : E + F = 2 * (Real.cos t) := by
    rw [Complex.ofReal_cos, Complex.cos]
    ring
  have hE : 1 - q * E ≠ 0 := by
    intro h
    have : q * E = 1 := by linear_combination -h
    have hnorm : ‖q * E‖ < 1 := by simpa [E, norm_mul] using hq
    simpa [this] using hnorm
  have hF : 1 - q * F ≠ 0 := by
    intro h
    have : q * F = 1 := by linear_combination -h
    have hnorm : ‖q * F‖ < 1 := by
      dsimp [F]
      simpa only [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one] using hq
    simpa [this] using hnorm
  rw [cosineKernel, (cosine_geometric_hasSum q t hq).tsum_eq]
  grind

/-- The midpoint, half-width, geometric mean, and convergence ratio of the paper. -/
def intervalCenter : ℝ := (hi + lo) / 2
def intervalHalfWidth : ℝ := (hi - lo) / 2
def intervalGeometricMean : ℝ := Real.sqrt (lo * hi)
def intervalRho : ℝ :=
  (Real.sqrt hi - Real.sqrt lo) / (Real.sqrt hi + Real.sqrt lo)

end

lemma intervalRho_pos (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) :
    0 < intervalRho lo hi := div_pos (sub_pos.mpr (Real.sqrt_lt_sqrt hlo.le hlt))
    (add_pos (Real.sqrt_pos.mpr (lt_trans hlo hlt)) (Real.sqrt_pos.mpr hlo))

lemma intervalRho_lt_one (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) :
    intervalRho lo hi < 1 := by
  have hu := Real.sqrt_pos.mpr hlo
  apply (div_lt_one (add_pos (Real.sqrt_pos.mpr (lt_trans hlo hlt)) hu)).mpr
  linarith

/-- The two normalization identities used at `z = 1` in Lemma 4. -/
lemma interval_normalizations (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) :
    (1 - intervalRho lo hi ^ 2) * intervalCenter lo hi =
      intervalGeometricMean lo hi * (1 + intervalRho lo hi ^ 2) ∧
    (1 - intervalRho lo hi ^ 2) * intervalHalfWidth lo hi =
      2 * intervalRho lo hi * intervalGeometricMean lo hi := by
  unfold intervalRho intervalCenter intervalHalfWidth intervalGeometricMean
  rw [Real.sqrt_mul hlo.le]
  grind

lemma interval_angular_pos (lo hi t : ℝ) (hlo : 0 < lo) (hlt : lo < hi) :
    0 < intervalCenter lo hi + intervalHalfWidth lo hi * Real.cos t := by
  have hc := Real.neg_one_le_cos t
  unfold intervalCenter intervalHalfWidth at *
  nlinarith

/-- The normalized reciprocal cosine series in Lemma 4, without any assumed series identity. -/
theorem interval_reciprocal_angular (lo hi t : ℝ) (hlo : 0 < lo) (hlt : lo < hi) :
    let center := intervalCenter lo hi + intervalHalfWidth lo hi * Real.cos t
    cosineKernel (-(intervalRho lo hi)) t =
      (intervalGeometricMean lo hi) /
        (center : ℝ) := by
  intro center
  let ρ := intervalRho lo hi
  have hρ := intervalRho_pos lo hi hlo hlt
  have hρ1 := intervalRho_lt_one lo hi hlo hlt
  have hq : ‖(-(ρ : ℂ))‖ < 1 := by simpa [ρ,   abs_of_pos hρ] using hρ1
  have hn := interval_normalizations lo hi hlo hlt
  have hC := hn.1
  have hnonzero  := ne_of_gt (interval_angular_pos lo hi t hlo hlt)
  have hden :
      (1 - 2 * (-ρ) * (Real.cos t) + (-ρ) ^ 2) *
      (intervalGeometricMean lo hi : ℂ) =
      (1 - (-ρ) ^ 2) *
      (center : ℝ) := by
    exact_mod_cast (by
      linear_combination -hC - Real.cos t * (hn.2))
  rw [cosineKernel_eq _ hq]
  have hdnonzero : (1 - 2 * (-ρ) * (Real.cos t : ℂ) + (-ρ) ^ 2) ≠ 0 := by
    have hB : (1 - (-(ρ : ℂ)) ^ 2) ≠ 0 := by
      simpa using (show (1 - (ρ : ℂ) ^ 2) ≠ 0 by exact_mod_cast (by nlinarith))
    intro hz
    rw [hz, zero_mul] at hden
    have : ((1 - (-(ρ : ℂ)) ^ 2) *
      (center : ℝ)) ≠ 0 :=
      mul_ne_zero hB (by exact_mod_cast hnonzero)
    exact this hden.symm
  apply (div_eq_div_iff hdnonzero (by exact_mod_cast hnonzero)).mpr
  simpa only [mul_comm] using hden.symm

open MeasureTheory ProbabilityTheory

/-- Ordered, distinct-sample lift of one monomial. The denominator is exactly `(n)_q`. -/
def monomialLift {Ω : Type*} {n q p : ℕ} (σ : Fin q → Fin p)
    (X : Fin n → Ω → Fin p → ℝ) (ω : Ω) : ℝ :=
  (n.descFactorial q : ℝ)⁻¹ *
    ∑ e : Fin q ↪ Fin n, ∏ i, X (e i) ω (σ i)

/-- The Chebyshev series of Lemma 4; index `k + 1` enumerates the positive integers. -/
def reciprocalSeries (lo hi : ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  1 + 2 * ∑' k,
    (-(intervalRho lo hi) * z) ^ (k + 1) *
      ((Polynomial.Chebyshev.T ℝ (k + 1 : ℕ)).eval
        ((x - intervalCenter lo hi) / intervalHalfWidth lo hi) : ℝ)

lemma reciprocalSeries_eq_cosineKernel (lo hi x : ℝ) (z : ℂ) (t : ℝ)
    (hrep : (x - intervalCenter lo hi) / intervalHalfWidth lo hi = Real.cos t)
    (hq : ‖(-(intervalRho lo hi : ℂ) * z)‖ < 1) :
    reciprocalSeries lo hi z x = cosineKernel (-(intervalRho lo hi : ℂ) * z) t := by
  have hs := (cosine_geometric_hasSum (-intervalRho lo hi * z) t hq).summable
  have heval k :
      (Polynomial.Chebyshev.T ℝ (k + 1 : ℕ)).eval (Real.cos t) =
        Real.cos ((k + 1 : ℕ) * t) := by
    simp
  unfold reciprocalSeries cosineKernel
  rw [hrep]
  simp_rw [heval]
  rw [hs.tsum_eq_zero_add]
  simp only [pow_zero, Nat.cast_zero, zero_mul, Real.cos_zero, Complex.ofReal_one, mul_one]
  ring

lemma interval_argument_mem (lo hi x : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (hx : x ∈ Set.Icc lo hi) :
    (x - intervalCenter lo hi) / intervalHalfWidth lo hi ∈ Set.Icc (-1) 1 := by
  have hd : 0 < intervalHalfWidth lo hi := by unfold intervalHalfWidth; positivity
  constructor
  · apply (le_div_iff₀ hd).mpr
    grind [intervalCenter, intervalHalfWidth]
  · apply (div_le_iff₀ hd).mpr
    grind [intervalCenter, intervalHalfWidth]

/-- The `z = 1` reciprocal identity of Lemma 4, for every point in the interval. -/
theorem reciprocal_expansion_at_one {lo hi x : ℝ} (hlo : 0 < lo) (hlt : lo < hi)
    (hx : x ∈ Set.Icc lo hi) :
    reciprocalSeries lo hi 1 x = (intervalGeometricMean lo hi) / x := by
  let t := Real.arccos ((x - intervalCenter lo hi) / intervalHalfWidth lo hi)
  have hy := interval_argument_mem lo hi x hlo hlt hx
  have hcos  := Real.cos_arccos hy.1 hy.2
  have hp := intervalRho_pos lo hi hlo hlt
  have hlt1 := intervalRho_lt_one lo hi hlo hlt
  rw [reciprocalSeries_eq_cosineKernel lo hi x 1 t hcos.symm (by
    simpa [  Real.norm_eq_abs, abs_of_pos hp] using hlt1)]
  simp
  rw [interval_reciprocal_angular lo hi t hlo hlt]
  grind [intervalHalfWidth]

section
variable {p : ℕ} (α : Fin p →₀ ℕ)

/-- Slots of an exponent vector: variable `i` occurs `α i` times. -/
def ExponentSlots := Σ i : Fin p, Fin (α i)

instance : Fintype (ExponentSlots α) := by
  unfold ExponentSlots
  infer_instance

/-- A fixed ordering of the factors of a monomial. -/
def exponentCoordinates :
    Fin (Fintype.card (ExponentSlots α)) → Fin p :=
  fun j => ((Fintype.equivFin (ExponentSlots α)).symm j).1

end

lemma exponentSlots_card {p : ℕ} (α : Fin p →₀ ℕ) :
    Fintype.card (ExponentSlots α) = α.sum (fun _ e => e) := by
  unfold ExponentSlots
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact (Finsupp.sum_fintype α (fun _ e => e) (fun _ => rfl)).symm

lemma exponentCoordinates_prod {p : ℕ} (α : Fin p →₀ ℕ) (m : Fin p → ℝ) :
    (∏ j, m (exponentCoordinates α j)) = ∏ i : Fin p, m i ^ α i := by
  change (∏ j : Fin (Fintype.card (ExponentSlots α)),
    m (((Fintype.equivFin (ExponentSlots α)).symm j).1)) = _
  rw [Fintype.prod_equiv (Fintype.equivFin (ExponentSlots α)).symm
    (fun j => m (((Fintype.equivFin (ExponentSlots α)).symm j).1))
    (fun s  => m s.1) (fun _ => rfl)]
  unfold ExponentSlots
  rw [Fintype.prod_sigma]
  simp

/-- The polynomial lift, explicitly replacing each monomial by its distinct-sample statistic. -/
def polynomialLift {Ω : Type*} {n p : ℕ} (F : MvPolynomial (Fin p) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (ω : Ω) : ℝ :=
  ∑ α ∈ F.support, F.coeff α * monomialLift (exponentCoordinates α) X ω

lemma chebyshev_abs_le_one (y : ℝ) (hy : y ∈ Set.Icc (-1) 1) (k : ℕ) :
    |(Polynomial.Chebyshev.T ℝ (k : ℕ)).eval y| ≤ 1 := by
  rw [← (Real.cos_arccos hy.1 hy.2), Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

/-- Scalar real form of the reciprocal series. -/
lemma reciprocal_real_series (lo hi x : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (hx : x ∈ Set.Icc lo hi) :
    1 + 2 * ∑' k : ℕ, (-intervalRho lo hi) ^ (k + 1) *
      (Polynomial.Chebyshev.T ℝ (k + 1 : ℕ)).eval
        ((x - intervalCenter lo hi) / intervalHalfWidth lo hi) =
      intervalGeometricMean lo hi / x := by
  have h := reciprocal_expansion_at_one hlo hlt hx
  unfold reciprocalSeries at h
  simp only [mul_one, ← Complex.ofReal_neg, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_tsum, ← Complex.ofReal_ofNat, ← Complex.ofReal_div] at h
  apply Complex.ofReal_injective
  simpa using h

end RoughRegime.Upper
