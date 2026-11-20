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

abbrev HighFrameVector (d D : ℕ) := HighFrameIndex d D → ℝ

section
variable {d n D : ℕ} (lam : ℝ) (t : Fin n → ℝ) (U : DesignSample d n) (i : Fin n)
    (P : MvPolynomial (Fin d) ℝ) (x y u : Covariate d)

def highFrameFeature (γ : HighFrameIndex d D) : ℝ :=
  ∏ r, (x r / 8) ^ (γ.val r).val

def highFrameCoefficients
    (γ : HighFrameIndex d D) : ℝ := P.coeff (polynomialBoxExponent γ.val)

/-- Exact frame evaluation is proved from polynomial coefficients; no
cardinal evaluation premise is supplied. -/
theorem high_frame_polynomial_evaluation {P : MvPolynomial (Fin d) ℝ}
    (hP : P.totalDegree ≤ D - 1) (x : Covariate d) :
    eval (fun r => x r / 8) P =
      ∑ γ : HighFrameIndex d D, highFrameFeature x γ * highFrameCoefficients P γ := by
  let box := PolynomialBox d (D - 1)
  classical
  rw [polynomial_box_evaluation hP]
  have hzero (γ : box)
      (hγ : ¬ (∑ r, (γ r).val) ≤ D - 1) : P.coeff (polynomialBoxExponent γ) = 0 := by
    by_contra hne
    have ht := (le_totalDegree (mem_support_iff.mpr hne)).trans hP
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at ht
    exact hγ ht
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun γ : box => (∑ r, (γ r).val) ≤ D - 1)
    (fun γ => P.coeff (polynomialBoxExponent γ) * ∏ r, (x r / 8) ^ (γ r).val)
  have hc : (∑ γ : {γ : box // ¬ (∑ r, (γ r).val) ≤ D - 1},
      P.coeff (polynomialBoxExponent γ.val) * ∏ r, (x r / 8) ^ (γ.val r).val) = 0 := by
    apply Finset.sum_eq_zero
    grind
  rw [hc, add_zero] at hsplit
  rw [← hsplit]
  apply Finset.sum_congr rfl
  intro γ _
  exact mul_comm _ _

def spatialSquaredDistance : ℝ := ∑ r, (y r - x r) ^ 2

/-- The numerator of the actual affine cardinal polynomial, in the
scaled coordinates u/8 of the paper's frame. -/
def spatialCardinalAffine : MvPolynomial (Fin d) ℝ :=
  ∑ r, (C ((y r - x r) * y r) - C (8 * (y r - x r)) * X r)

theorem spatial_cardinal_affine_eval :
    eval (fun r => u r / 8) (spatialCardinalAffine x y) =
      ∑ r, (y r - x r) * (y r - u r) := by
  simp only [spatialCardinalAffine, map_sum, map_sub, map_mul, eval_C, eval_X]
  ring

theorem spatial_cardinal_affine_eval_center :
    eval (fun r => x r / 8) (spatialCardinalAffine x y) = spatialSquaredDistance x y := by
  rw [spatial_cardinal_affine_eval]
  simp only [spatialSquaredDistance, pow_two]

theorem spatial_cardinal_affine_degree :
    (spatialCardinalAffine x y).totalDegree ≤ 1 := by
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro r _
  apply (totalDegree_sub _ _).trans
  apply max_le
  · simp only [totalDegree_C]; omega
  · exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])

/-- Product over every other observation, including collisions. -/
def spatialCardinalPolynomial :
    MvPolynomial (Fin d) ℝ :=
  ∏ j ∈ Finset.univ.erase i, spatialCardinalAffine (U i) (U j)

theorem spatial_cardinal_polynomial_degree :
    (spatialCardinalPolynomial U i).totalDegree ≤ n - 1 := by
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ _ :=
      Finset.sum_le_sum (fun j _ => spatial_cardinal_affine_degree ..)
    _ = _ := by simp

theorem spatial_cardinal_polynomial_eval_neighbor {i j : Fin n} (hji : j ≠ i) :
    eval (fun r => U j r / 8) (spatialCardinalPolynomial U i) = 0 := by
  rw [spatialCardinalPolynomial, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
    (by simp [spatial_cardinal_affine_eval])

/-- Squared-distance unary scale density from Appendix A. -/
def spatialUnaryWeight (t : ℝ) (x y : Covariate d) : ℝ :=
  t * (lam * spatialSquaredDistance x y) ^ 2 *
    Real.exp (-(t * lam * spatialSquaredDistance x y))

def spatialCardinalScale : ℝ :=
  ∏ j ∈ Finset.univ.erase i,
    t j * lam ^ 2 * Real.exp (-(t j * lam * spatialSquaredDistance (U i) (U j)))

def spatialCardinalWeight : ℝ :=
  ∏ j ∈ Finset.univ.erase i, spatialUnaryWeight lam (t j) (U i) (U j)

end

section
variable {κ J : Type*} [Fintype κ] [DecidableEq κ] {n : ℕ} (v : κ → ℝ) (s : Finset J) (S : ℝ)
    (A : J → κ → κ → ℝ) (φ : Fin n → κ → ℝ) (i l : Fin n)

theorem spatial_frame_covariance_rank_one :
    spatialFrameCovariance (fun β β' => S * v β * v β') φ i l =
      S * (∑ β, φ i β * v β) * (∑ β, φ l β * v β) := by
  simp only [spatialFrameCovariance, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  grind

theorem spatial_frame_covariance_add (A B : κ → κ → ℝ) (φ : Fin n → κ → ℝ) (i l : Fin n) :
    spatialFrameCovariance (fun β β' => A β β' + B β β') φ i l =
      spatialFrameCovariance A φ i l + spatialFrameCovariance B φ i l := by
  simp only [spatialFrameCovariance, mul_add, Finset.sum_add_distrib]

theorem spatial_frame_covariance_sum :
    spatialFrameCovariance (fun β β' => ∑ j ∈ s, A j β β') φ i l =
      ∑ j ∈ s, spatialFrameCovariance (A j) φ i l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [spatialFrameCovariance]
  | @insert j s hj ih =>
    simp [Finset.sum_insert hj]
    rw [spatial_frame_covariance_add, ih]

end

theorem spatial_cardinal_weight_product {d n : ℕ} (lam : ℝ) (t : Fin n → ℝ)
    (U : DesignSample d n) (i : Fin n) :
    spatialCardinalScale lam t U i *
      (eval (fun r => U i r / 8) (spatialCardinalPolynomial U i)) ^ 2 =
      spatialCardinalWeight lam t U i := by
  rw [((by simp [spatialCardinalPolynomial, map_prod, spatial_cardinal_affine_eval_center] : ∀ (U : DesignSample d n) (i : Fin n), (eval fun r => U i r / 8) (spatialCardinalPolynomial U i) = ∏ j ∈ Finset.univ.erase i, spatialSquaredDistance (U i) (U j))), ← Finset.prod_pow]
  unfold spatialCardinalScale spatialCardinalWeight
  rw [← Finset.prod_mul_distrib]
  grind [spatialUnaryWeight]

end NearlyMinimax
