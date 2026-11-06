module

public import NearlyMinimax.SpatialCardinalCovariance
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

𝛄
𝚪
𝚨
𝚩
set_option maxHeartbeats 200000

/-- Coefficients of any finite polynomial product vary continuously
when each factor coefficient does; the antidiagonal convolution is
finite and independent of the parameter. -/
theorem mvpolynomial_product_coefficients_continuous
    [TopologicalSpace α] [DecidableEq σ] (s : Finset κ)
    (P : κ → α → MvPolynomial σ ℝ)
    (hP : ∀ k ∈ s, ∀ β, Continuous fun x => (P k x).coeff β ) :
    ∀ β, Continuous fun x => (∏ k ∈ s, P k x).coeff β := by
  classical
  induction s using Finset.induction_on with
  | empty => intro β; exact continuous_const
  | @insert k s hk ih =>
    intro β
    simp only [Finset.prod_insert hk, coeff_mul]
    apply continuous_finsetSum
    intro w _
    exact (hP k (Finset.mem_insert_self ..) w.1).mul
      $ ih 𝗨₁ w.2

𝗇 𝔄 𝙇
𝗇 𝔅 spatialCardinalAffine (U i) $ U j
theorem spatial_cardinal_polynomial_coefficients_continuous
    i β :
    Continuous fun U : 𝔄 => (spatialCardinalPolynomial U i).coeff β := by
  have hcoeff j δ :
      Continuous fun U : 𝔄 => (𝔅).coeff δ := by
    simp only [spatialCardinalAffine, coeff_sum, coeff_sub, coeff_C_mul]
    apply continuous_finsetSum
    intro r _
    apply Continuous.sub
    · by_cases hδ : 0 = δ
      · simp only [coeff_C, hδ, ite_true]; fun_prop
      · simp only [coeff_C, hδ]; exact continuous_const
    fun_prop
  exact mvpolynomial_product_coefficients_continuous

    (Finset.univ.erase i)
    (fun j (U : 𝔄) => 𝔅)
    (fun j _ δ => hcoeff j δ) β
