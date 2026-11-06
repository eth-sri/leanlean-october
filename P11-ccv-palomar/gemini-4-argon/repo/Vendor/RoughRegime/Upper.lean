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


variable {n p : ℕ}
/-- The complete cosine generating series, with its constant term corrected to one. -/
def cosineKernel (q : ℂ) (t : ℝ) : ℂ :=
  2 * (∑' k : ℕ, q ^ k * (Real.cos (↑k * t) : ℂ)) - 1

lemma cosine_geometric_hasSum (q : ℂ) (t : ℝ) (hq : ‖q‖ < 1) :
    HasSum (fun k : ℕ => q ^ k * (Real.cos (↑k * t) : ℂ))
      (((1 - q * Complex.exp (↑t * I))⁻¹ +
        (1 - q * Complex.exp ((-t : ℂ) * I))⁻¹) / 2) := by
  have ha : ‖q * Complex.exp (↑t * I)‖ < 1 := by
    simpa [norm_mul] using hq
  have hb : ‖q * Complex.exp ((-t : ℂ) * I)‖ < 1 := by
    simpa only [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one] using hq
  convert ((hasSum_geometric_of_norm_lt_one ha).add
    (hasSum_geometric_of_norm_lt_one hb)).div_const 2 using 1
  ext k
  rw [Complex.ofReal_cos, Complex.cos, mul_pow, mul_pow,
    ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  push_cast
  rw [show -(↑k * ↑t) * I = ↑k * ((-t : ℂ) * I) by ring,
    show ↑k * ↑t * I = ↑k * (↑t * I) by ring]
  ring

/-- Poisson-kernel identity underlying Lemma 4, for complex `q` in the open unit disk. -/
theorem cosineKernel_eq (q : ℂ) (t : ℝ) (hq : ‖q‖ < 1) :
    cosineKernel q t =
      (1 - q ^ 2) / (1 - 2 * q * (Real.cos t : ℂ) + q ^ 2) := by
  let E : ℂ := Complex.exp (↑t * I)
  let F : ℂ := Complex.exp ((-t : ℂ) * I)
  have hEF : E * F = 1 := by
    rw [← Complex.exp_add]
    have hz : ↑t * I + (-t : ℂ) * I = 0 := by push_cast; ring
    rw [hz, Complex.exp_zero]
  have hsum : E + F = 2 * (Real.cos t : ℂ) := by
    rw [Complex.ofReal_cos, Complex.cos]
    ring
  have : 1 - q * E ≠ 0 := by
    intro h
    have : q * E = 1 := by linear_combination -h
    have hnorm : ‖q * E‖ < 1 := by simpa [E, norm_mul] using hq
    simp [this] at hnorm
  have : 1 - q * F ≠ 0 := by
    intro h
    have : q * F = 1 := by linear_combination -h
    have hnorm : ‖q * F‖ < 1 := by
      dsimp [F]
      simpa only [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one] using hq
    simp [this] at hnorm
  have hden : 1 - 2 * q * (Real.cos t : ℂ) + q ^ 2 =
      (1 - q * E) * (1 - q * F) := by
    calc
      _ = 1 - q * (E + F) + q ^ 2 * (E * F) := by rw [hsum, hEF]; ring
      _ = _ := by ring
  rw [cosineKernel, (cosine_geometric_hasSum q t hq).tsum_eq]
  change 2 * (((1 - q * E)⁻¹ + (1 - q * F)⁻¹) / 2) - 1 = _
  rw [hden]
  field_simp
  linear_combination -q ^ 2 * hEF

/-- The midpoint, half-width, geometric mean, and convergence ratio of the paper. -/
def intervalCenter (lo hi : ℝ) : ℝ := (hi + lo) / 2
def intervalHalfWidth (lo hi : ℝ) : ℝ := (hi - lo) / 2
def intervalGeometricMean (lo hi : ℝ) : ℝ := Real.sqrt (lo * hi)
def intervalRho (lo hi : ℝ) : ℝ :=
  (Real.sqrt hi - Real.sqrt lo) / (Real.sqrt hi + Real.sqrt lo)

lemma intervalRho_pos (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) :
    0 < intervalRho lo hi := by
  exact div_pos (sub_pos.mpr (Real.sqrt_lt_sqrt hlo.le hlt))
    (add_pos (Real.sqrt_pos.mpr (lt_trans hlo hlt)) (Real.sqrt_pos.mpr hlo))

lemma intervalRho_lt_one (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) :
    intervalRho lo hi < 1 := by
  have hu := Real.sqrt_pos.mpr hlo
  have hv := Real.sqrt_pos.mpr (lt_trans hlo hlt)
  apply (div_lt_one (add_pos hv hu)).mpr
  linarith

open MeasureTheory ProbabilityTheory

/-- Ordered, distinct-sample lift of one monomial. The denominator is exactly `(n)_q`. -/
def monomialLift {Ω : Type*} {n q p : ℕ} (σ : Fin q → Fin p)
    (X : Fin n → Ω → Fin p → ℝ) (ω : Ω) : ℝ :=
  (n.descFactorial q : ℝ)⁻¹ *
    ∑ e : Fin q ↪ Fin n, ∏ i : Fin q, X (e i) ω (σ i)

/-- The Chebyshev series of Lemma 4; index `k + 1` enumerates the positive integers. -/
def reciprocalSeries (lo hi : ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  1 + 2 * ∑' k : ℕ,
    (-(intervalRho lo hi : ℂ) * z) ^ (k + 1) *
      (((Polynomial.Chebyshev.T ℝ (k + 1 : ℕ)).eval
        ((x - intervalCenter lo hi) / intervalHalfWidth lo hi) : ℝ) : ℂ)

lemma interval_argument_mem (lo hi x : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (hx : x ∈ Set.Icc lo hi) :
    (x - intervalCenter lo hi) / intervalHalfWidth lo hi ∈ Set.Icc (-1) 1 := by
  have hd : 0 < intervalHalfWidth lo hi := by unfold intervalHalfWidth; positivity
  constructor
  · apply (le_div_iff₀ hd).mpr
    unfold intervalCenter intervalHalfWidth
    linarith [hx.1]
  · apply (div_le_iff₀ hd).mpr
    unfold intervalCenter intervalHalfWidth
    linarith [hx.2]

/-- Slots of an exponent vector: variable `i` occurs `α i` times. -/
def ExponentSlots {p : ℕ} (α : Fin p →₀ ℕ) := Σ i : Fin p, Fin (α i)

instance {p : ℕ} (α : Fin p →₀ ℕ) : Fintype (ExponentSlots α) := by
  unfold ExponentSlots
  infer_instance

/-- A fixed ordering of the factors of a monomial. -/
def exponentCoordinates  (α : Fin p →₀ ℕ) :
    Fin (Fintype.card (ExponentSlots α)) → Fin p :=
  fun j => ((Fintype.equivFin (ExponentSlots α)).symm j).1

lemma exponentSlots_card  (α : Fin p →₀ ℕ) :
    Fintype.card (ExponentSlots α) = α.sum (fun _ e => e) := by
  unfold ExponentSlots
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact (Finsupp.sum_fintype α (fun _ e => e) (fun _ => rfl)).symm

lemma exponentCoordinates_prod  (α : Fin p →₀ ℕ) (m : Fin p → ℝ) :
    (∏ j, m (exponentCoordinates α j)) = ∏ i : Fin p, m i ^ α i := by
  change (∏ j : Fin (Fintype.card (ExponentSlots α)),
    m (((Fintype.equivFin (ExponentSlots α)).symm j).1)) = _
  rw [Fintype.prod_equiv (Fintype.equivFin (ExponentSlots α)).symm
    (fun j => m (((Fintype.equivFin (ExponentSlots α)).symm j).1))
    (fun s : ExponentSlots α => m s.1) (fun _ => rfl)]
  unfold ExponentSlots
  rw [Fintype.prod_sigma]
  simp

/-- The polynomial lift, explicitly replacing each monomial by its distinct-sample statistic. -/
def polynomialLift {Ω : Type*}  (F : MvPolynomial (Fin p) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (ω : Ω) : ℝ :=
  ∑ α ∈ F.support, F.coeff α * monomialLift (exponentCoordinates α) X ω

lemma chebyshev_abs_le_one (y : ℝ) (hy : y ∈ Set.Icc (-1) 1) (k : ℕ) :
    |(Polynomial.Chebyshev.T ℝ ↑k).eval y| ≤ 1 := by
  rw [← (Real.cos_arccos hy.1 hy.2), Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

end RoughRegime.Upper
