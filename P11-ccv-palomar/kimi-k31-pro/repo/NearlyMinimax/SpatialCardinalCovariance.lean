module

public import NearlyMinimax.CellPolynomialProjection
public import NearlyMinimax.HighResponseRemainder

@[expose] public section

/-! The paper's actual polynomial frame and cardinal covariance tensor.
The affine products below avoid division by distances, so coincident
observations are included in the exact diagonal identity. -/
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- Exactly the finite monomial frame of total degree at most D-1. -/
abbrev HighFrameIndex (d D : ℕ) :=
  {γ : PolynomialBox d (D - 1) // (∑ r, (γ r).val) ≤ D - 1}

def highFrameFeature {d D : ℕ} (x : Covariate d) (γ : HighFrameIndex d D) : ℝ :=
  ∏ r, (x r / 8) ^ (γ.val r).val

def highFrameCoefficients {d D : ℕ} (P : MvPolynomial (Fin d) ℝ)
    (γ : HighFrameIndex d D) : ℝ := P.coeff (polynomialBoxExponent γ.val)

/-- Exact frame evaluation is proved from polynomial coefficients; no
cardinal evaluation premise is supplied. -/
theorem high_frame_polynomial_evaluation {d D : ℕ} (P : MvPolynomial (Fin d) ℝ)
    (hP : P.totalDegree ≤ D - 1) (x : Covariate d) :
    eval (fun r => x r / 8) P =
      ∑ γ : HighFrameIndex d D, highFrameFeature x γ * highFrameCoefficients P γ := by
  classical
  rw [polynomial_box_evaluation P hP]
  have hzero (γ : PolynomialBox d (D - 1))
      (hγ : ¬ (∑ r, (γ r).val) ≤ D - 1) : P.coeff (polynomialBoxExponent γ) = 0 := by
    by_contra hne
    have ht := (le_totalDegree (mem_support_iff.mpr hne)).trans hP
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at ht
    simpa only [polynomial_box_exponent_apply] using hγ ht
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun γ : PolynomialBox d (D - 1) => (∑ r, (γ r).val) ≤ D - 1)
    (fun γ => P.coeff (polynomialBoxExponent γ) * ∏ r, (x r / 8) ^ (γ r).val)
  have hc : (∑ γ : {γ : PolynomialBox d (D - 1) // ¬ (∑ r, (γ r).val) ≤ D - 1},
      P.coeff (polynomialBoxExponent γ.val) * ∏ r, (x r / 8) ^ (γ.val r).val) = 0 := by
    apply Finset.sum_eq_zero
    intro γ _
    rw [hzero γ.val γ.property, zero_mul]
  rw [hc, add_zero] at hsplit
  rw [← hsplit]
  apply Finset.sum_congr rfl
  intro γ _
  exact mul_comm _ _

def spatialSquaredDistance {d : ℕ} (x y : Covariate d) : ℝ := ∑ r, (y r - x r) ^ 2

/-- The numerator of the actual affine cardinal polynomial, in the
scaled coordinates u/8 of the paper's frame. -/
def spatialCardinalAffine {d : ℕ} (x y : Covariate d) : MvPolynomial (Fin d) ℝ :=
  ∑ r, (C ((y r - x r) * y r) - C (8 * (y r - x r)) * X r)

theorem spatial_cardinal_affine_eval {d : ℕ} (x y u : Covariate d) :
    eval (fun r => u r / 8) (spatialCardinalAffine x y) =
      ∑ r, (y r - x r) * (y r - u r) := by
  simp only [spatialCardinalAffine, map_sum, map_sub, map_mul, eval_C, eval_X]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem spatial_cardinal_affine_eval_neighbor {d : ℕ} (x y : Covariate d) :
    eval (fun r => y r / 8) (spatialCardinalAffine x y) = 0 := by
  rw [spatial_cardinal_affine_eval]
  simp

theorem spatial_cardinal_affine_eval_center {d : ℕ} (x y : Covariate d) :
    eval (fun r => x r / 8) (spatialCardinalAffine x y) = spatialSquaredDistance x y := by
  rw [spatial_cardinal_affine_eval]
  simp only [spatialSquaredDistance, pow_two]

theorem spatial_cardinal_affine_degree {d : ℕ} (x y : Covariate d) :
    (spatialCardinalAffine x y).totalDegree ≤ 1 := by
  unfold spatialCardinalAffine
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro r _
  apply (totalDegree_sub _ _).trans
  apply max_le
  · simp only [totalDegree_C]; omega
  · exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])

/-- Product over every other observation, including collisions. -/
def spatialCardinalPolynomial {d n : ℕ} (U : Fin n → Covariate d) (i : Fin n) :
    MvPolynomial (Fin d) ℝ :=
  ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, spatialCardinalAffine (U i) (U j)

theorem spatial_cardinal_polynomial_degree {d n : ℕ} (U : Fin n → Covariate d) (i : Fin n) :
    (spatialCardinalPolynomial U i).totalDegree ≤ n - 1 := by
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _j ∈ (Finset.univ : Finset (Fin n)).erase i, 1 :=
      Finset.sum_le_sum (fun j _ => spatial_cardinal_affine_degree (U i) (U j))
    _ = _ := by simp

theorem spatial_cardinal_polynomial_eval_neighbor {d n : ℕ}
    (U : Fin n → Covariate d) (i j : Fin n) (hji : j ≠ i) :
    eval (fun r => U j r / 8) (spatialCardinalPolynomial U i) = 0 := by
  rw [spatialCardinalPolynomial, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
    (spatial_cardinal_affine_eval_neighbor (U i) (U j))

theorem spatial_cardinal_polynomial_eval_center {d n : ℕ}
    (U : Fin n → Covariate d) (i : Fin n) :
    eval (fun r => U i r / 8) (spatialCardinalPolynomial U i) =
      ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, spatialSquaredDistance (U i) (U j) := by
  simp only [spatialCardinalPolynomial, map_prod, spatial_cardinal_affine_eval_center]

/-- Squared-distance unary scale density from Appendix A. -/
def spatialUnaryWeight {d : ℕ} (lam t : ℝ) (x y : Covariate d) : ℝ :=
  t * (lam * spatialSquaredDistance x y) ^ 2 *
    Real.exp (-(t * lam * spatialSquaredDistance x y))

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
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro β' _
  ring

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
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    rw [spatial_frame_covariance_add, ih]

theorem spatial_cardinal_weight_product {d n : ℕ} (lam : ℝ) (t : Fin n → ℝ)
    (U : Fin n → Covariate d) (i : Fin n) :
    spatialCardinalScale lam t U i *
      (eval (fun r => U i r / 8) (spatialCardinalPolynomial U i)) ^ 2 =
      spatialCardinalWeight lam t U i := by
  rw [spatial_cardinal_polynomial_eval_center, ← Finset.prod_pow]
  unfold spatialCardinalScale spatialCardinalWeight
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  unfold spatialUnaryWeight
  ring

end NearlyMinimax
