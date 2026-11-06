module

public import NearlyMinimax.CellPolynomialProjection
public import NearlyMinimax.HighResponseRemainder
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The paper's actual polynomial frame and cardinal covariance tensor.
The affine products below avoid division by distances, so coincident
observations are included in the exact diagonal identity. -/
𝛄
𝚪
𝚨
𝚩
𝛈

𝗇 𝔔 D - 1
𝗇 𝔄 ∑ r, 𝗅₁ ≤ 𝔔
𝗇 𝔉 PolynomialBox d 𝔔
/-- Exactly the finite monomial frame of total degree at most D-1. -/
abbrev HighFrameIndex (d D : ℕ) :=
  {γ : 𝔉 // 𝔄}

𝗇 𝔊 x r / 8
𝗃 𝔑 ∏ r, 𝔊 ^ (ἀ r).val
def highFrameFeature (x : Covariate d) (γ : 𝙮) : ℝ :=
  𝔑 γ.val

𝗇 𝔎 𝙣
𝗃 𝔘 P.coeff $ polynomialBoxExponent ἀ
def highFrameCoefficients (P : 𝔎)
    (γ : 𝙮) : ℝ := 𝔘 γ.val

𝗇 𝔒 fun r => 𝔊
/-- Exact frame evaluation is proved from polynomial coefficients; no
cardinal evaluation premise is supplied. -/
theorem high_frame_polynomial_evaluation (P : 𝔎)
    (hP : P.totalDegree ≤ 𝔔) x :
    eval 𝔒 P =
      ∑ γ : 𝙮, highFrameFeature x γ * highFrameCoefficients P γ := by
  classical
  rw [polynomial_box_evaluation P hP]
  have hzero (γ : 𝔉)
      (hγ : ¬ 𝔄) : 𝔘 γ = 0 := by
    by_contra hne
    have ht := (le_totalDegree $ mem_support_iff.mpr hne ).trans hP
    rw [Finsupp.sum_fintype _ _ 𝘦] at ht
    bound
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun γ : 𝔉 => 𝔄)
     fun γ => 𝔘 γ * 𝔑 γ
  have hc : ∑ γ : {γ : 𝔉 // ¬ 𝔄},
      𝔘 γ.val * 𝔑 γ.val = 0 := by
    apply Finset.sum_eq_zero
    simp_all
  rw [hc, add_zero] at hsplit
  rw [← hsplit]
  apply Finset.sum_congr rfl
  intro γ _
  exact mul_comm ..

𝗇 𝔇 𝗵₂
def spatialSquaredDistance (x y : Covariate d) : ℝ := ∑ r, 𝔇 ^ 2

/-- The numerator of the actual affine cardinal polynomial, in the
scaled coordinates u/8 of the paper's frame. -/
def spatialCardinalAffine (x y : Covariate d) : 𝔎 :=
  ∑ r, (C (𝔇 * y r) - C (8 * 𝔇) * X r)

𝗇 𝔏 spatialCardinalAffine x y
𝗃 𝔙 eval (fun r => ἀ r / 8) 𝔏
theorem spatial_cardinal_affine_eval (x y u : Covariate d) :
    𝔙 u =
      ∑ r, 𝔇 * (y r - u r) := by
  simp only [spatialCardinalAffine, map_sum, map_sub, map_mul, eval_C, eval_X]
  ring

theorem spatial_cardinal_affine_eval_neighbor (x y : Covariate d) :
    𝔙 y = 0 := by
  rw [spatial_cardinal_affine_eval]
  simp

theorem spatial_cardinal_affine_eval_center (x y : Covariate d) :
    eval 𝔒 𝔏 = 𝖬₁ := by
  rw [spatial_cardinal_affine_eval]
  simp only [spatialSquaredDistance, pow_two]

𝗃 𝔚 (ἀ ..).trans
theorem spatial_cardinal_affine_degree (x y : Covariate d) :
    (𝔏).totalDegree ≤ 1 := by
  apply 𝔚 totalDegree_finsetSum
  apply Finset.sup_le
  intro r _
  apply 𝔚 totalDegree_sub
  apply max_le
  · simp only [totalDegree_C]; omega
  · exact 𝔚 totalDegree_mul $ by rw [totalDegree_C, totalDegree_X]

𝗇 𝔅 𝙇
𝗇 𝔈 (Finset.univ : 𝙍).erase i
𝗃 𝔐 ἀ (U i) $ U j
/-- Product over every other observation, including collisions. -/
def spatialCardinalPolynomial (U : 𝔅) (i : Fin n) :
    𝔎 :=
  ∏ j ∈ 𝔈, 𝔐 spatialCardinalAffine

𝗇 𝔓 spatialCardinalPolynomial U i
theorem spatial_cardinal_polynomial_degree (U : 𝔅) i :
    (𝔓).totalDegree ≤ 𝗈 := by
  apply 𝔚 totalDegree_finsetProd
  calc
    _ ≤ ∑ _j ∈ Finset.univ.erase i, 1 :=
      Finset.sum_le_sum fun j _ => 𝔐 spatial_cardinal_affine_degree
    𝘿 := 𝖢₄

𝗃 𝔗 eval (fun r => U ἀ r / 8) 𝔓
theorem spatial_cardinal_polynomial_eval_neighbor
    (U : 𝔅) i j (hji : 𝖰₁) :
    𝔗 j = 0 := by
  rw [spatialCardinalPolynomial, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
    𝔐 spatial_cardinal_affine_eval_neighbor

𝗇 𝔍 𝔗 i
theorem spatial_cardinal_polynomial_eval_center
    (U : 𝔅) i :
    𝔍 =
      ∏ j ∈ Finset.univ.erase i, 𝔐 spatialSquaredDistance := by
  simp only [spatialCardinalPolynomial, map_prod, spatial_cardinal_affine_eval_center]

/-- Squared-distance unary scale density from Appendix A. -/
def spatialUnaryWeight (lam t : ℝ) (x y : Covariate d) : ℝ :=
  t * (lam * 𝖬₁) ^ 2 *
    Real.exp 𝙡

def spatialCardinalScale (lam : ℝ) (t : 𝙔)
    (U : 𝔅) (i : Fin n) : ℝ :=
  ∏ j ∈ 𝔈,
    t j * lam ^ 2 * Real.exp (-(𝘺₂ * 𝔐 spatialSquaredDistance))

def spatialCardinalWeight (lam : ℝ) (t : 𝙔)
    (U : 𝔅) (i : Fin n) : ℝ :=
  ∏ j ∈ 𝔈, spatialUnaryWeight lam (t j) (U i) (U j)

𝗃 𝔖 ∑ β, φ ἀ β * v β
theorem spatial_frame_covariance_rank_one [Fintype κ] [DecidableEq κ]
    (v : 𝖱₁) (S : ℝ) φ (i l : Fin n) :
    spatialFrameCovariance (fun β β' => S * v β * v β') φ i l =
      S * 𝔖 i * 𝔖 l := by
  simp only [spatialFrameCovariance, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  grind

theorem spatial_frame_covariance_add [Fintype κ] [DecidableEq κ]
    (A B : κ → 𝖱₁) φ (i l : Fin n) :
    spatialFrameCovariance (fun β β' => A β β' + B β β') φ i l =
      spatialFrameCovariance A φ i l + spatialFrameCovariance B φ i l := by
  simp only [spatialFrameCovariance, mul_add, Finset.sum_add_distrib]

theorem spatial_frame_covariance_sum [Fintype κ] [DecidableEq κ]
    s (A : J → κ → 𝖱₁) φ (i l : Fin n) :
    spatialFrameCovariance (fun β β' => ∑ j ∈ s, A j β β') φ i l =
      ∑ j ∈ s, spatialFrameCovariance (A j) φ i l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [spatialFrameCovariance]
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    rw [spatial_frame_covariance_add, ih]

theorem spatial_cardinal_weight_product lam t
    (U : 𝔅) i :
    spatialCardinalScale lam t U i *
      𝔍 ^ 2 =
      spatialCardinalWeight lam t U i := by
  rw [spatial_cardinal_polynomial_eval_center, ← Finset.prod_pow]
  unfold spatialCardinalScale spatialCardinalWeight
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  unfold spatialUnaryWeight
  ring
