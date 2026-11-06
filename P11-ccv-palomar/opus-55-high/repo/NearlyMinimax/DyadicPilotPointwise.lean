module

public import NearlyMinimax.IncrementPilotFeatures
public import NearlyMinimax.PopulationRowDerivatives
public import NearlyMinimax.DyadicFit
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual original-law factorial pilots at a dyadic anchor. Their population
point and derivative constants are derived from the original admissibility
conditions, rather than supplied as stochastic budget assumptions. -/

open MeasureTheory ProbabilityTheory Matrix MvPolynomial
𝚼
𝚨

𝚭
𝚩

𝗇 𝔟 dyadicNormalizedDensity θ j x
𝗇 𝔠 𝘎₂
𝗃 𝔬 θ.regression ∘ dyadicCellAffine ἀ x
𝗇 𝔍 anchoredFinMomentFamilies 𝔠 𝔟 𝔬 j
𝗇 𝔐 𝙟
𝗇 𝔓 𝗌
𝗃 𝔘 ἀ C θ hθ
𝗃 𝔣 𝔘 ἀ j x
𝗃 𝔨 ἀ (ℓ := ℓ)
theorem dyadicFinPilotMoments_eq_anchored C
    θ (hθ : 𝔐) j x
    (hx : 𝔓) :
    𝔨 dyadicFinPilotMoments θ j x = 𝔍 := by
  funext t i
  exact 𝔣 dyadicFinPilotMoments_eq_normalized hx t i

𝗇 𝔅 𝘮
𝗃 𝔫 (Fintype.equivFin $ incrementVariables ἀ ).symm a
𝗇 𝔏 𝔫 𝚃
𝗇 𝔇 dyadicIncrementRawMean θ j x
𝗇 𝔚 dyadicNormalizedDensity θ 𝔅 x
𝗇 𝔛 dyadicNormalizedAnchor 𝔅 x
𝗃 𝔩 𝔘 ἀ 𝔅 x
theorem dyadicIncrementRawMean_eq_normalized C
    θ (hθ : 𝔐) j (hj : j ≠ 0)
    x (hx : 𝔓) :
    𝔇 = fun a =>
      incrementValuation
        (anchoredFinNormalizedGram 𝔠 𝔟)
        (anchoredFinNormalizedGram 𝔛 𝔚)
        𝔍
        (anchoredFinMomentFamilies 𝔛 𝔚
          𝔬 𝔅)
        𝔏 := by
  rw [𝔣 dyadicIncrementRawMean_eq_population hx]
  simp only [dyadicIncrementPopulation, if_neg hj,
    𝔘 dyadicFinPilotGram_eq_normalized,
    𝔣 dyadicFinPilotMoments_eq_anchored hx,
    𝔩 dyadicFinPilotMoments_eq_anchored hx]

𝗃 𝔦 ἀ d C.order
𝗇 𝔄 incrementFinScalar 𝔦 anchoredDimension C.densityLower C.densityUpper 𝔦 anchoredFinTransport y m row
𝗇 𝔑 Nonempty 𝔦 AnchoredIndex
𝗇 𝔙 𝚇₁
𝗇 𝔜 ‖𝗸₁ 𝔄 𝔇‖
𝗃 𝔡 fun w hw => 𝔘 admissible_regression_value_bound _ $ dyadicCellAffine_mem_cube ἀ x w hw
𝗃 𝔥 ἀ (d := d) (ℓ := C.order) C.densityLower C.densityUpper
/-- Uniform genuine derivative operator bounds at the true free-moment mean
of the actual current/parent observations. -/
theorem admissible_dyadic_increment_derivative_bound (C : ModelConstants d)
    [𝔑] :
    ∃ D A , 𝙱₁ ∧ 𝘪 ∧
      ∀ θ , 𝔐 → ∀ j , j ≠ 0 →
      ∀ x ∈ unitCube d, ∀ y , |y| ≤ C.holderBound → ∀ m k ,
      ∀ row ,
        𝔜 ≤
          (∑ i, |row i|) * D * k.factorial * 𝔙 := by
  obtain ⟨D, A, hD, hA, hder⟩ := 𝔥 anchored_actual_population_row_derivative_operator_bound C.holderBound C.holderBound
    C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper)
    C.holderBound_pos.le C.holderBound_pos.le
  refine ⟨D, A, hD, hA, ?_⟩
  intro θ hθ j hj x hx y hy m k row
  rw [𝔘 dyadicIncrementRawMean_eq_normalized j hj x hx]
  exact hder _ _ (gridNormalizedAnchor_mem_cube _  𝖠₃  x hx)
    (gridNormalizedAnchor_mem_cube _  𝖠₃  x hx) _ _ _ _
    𝔣 dyadicNormalizedDensity_measurable
    𝔩 dyadicNormalizedDensity_measurable
    𝔣 dyadicNormalizedDensity_bounds
    𝔩 dyadicNormalizedDensity_bounds
    𝔡 j
    𝔡 𝔅
    y hy m k row

𝗃 𝔢 ἀ r a b T y m
def rowIncrementPolynomial (r : ℕ) (a b : ℝ) (T : 𝗲 ℝ)
    (y : ℝ) (m : ℕ) (row : 𝗢) :
    MvPolynomial 𝚕 ℝ :=
  ∑ i, C (row i) * 𝔢 incrementFinPolynomial i

𝗇 𝔔 𝔢 rowIncrementPolynomial row
theorem rowIncrementPolynomial_eval r a b T
    y m row z :
    eval z 𝔔 = 𝔢 incrementFinScalar row z := by
  simp [rowIncrementPolynomial, incrementFinScalar, incrementFinVector, dotProduct]

theorem rowIncrementPolynomial_degree (r : ℕ) [NeZero r] a b
    T y m row :
    (𝔔).totalDegree ≤ m + r + 1 := by
  apply totalDegree_finsetSum_le
  intro i _
  apply (totalDegree_mul ..).trans
  simpa only [totalDegree_C, zero_add, incrementFinPolynomial] using
    (totalDegree_rename_le ..).trans $ 𝔢 incrementEntryPolynomial_degree i

𝗇 𝔊 𝙃
theorem anchoredFinNormalizedGram_one (u : Covariate d) :
    𝔨 anchoredFinNormalizedGram u 𝔊 = 1 := by
  have hG : 𝔨 anchoredDensityGram u 𝔊 = anchoredGram u := by
    ext γ δ
    simp [anchoredDensityGram, anchoredGram]
  unfold anchoredFinNormalizedGram
  rw [hG, Matrix.nonsing_inv_mul _
    $ (Matrix.isUnit_iff_isUnit_det _).mp (anchoredGram_posDef u).isUnit ]
  exact map_one _

𝗇 𝔉 dyadicNormalizedAnchor 0 x
𝗇 𝔎 dyadicNormalizedDensity θ 0 x
𝗇 𝔖 incrementValuation (anchoredFinNormalizedGram 𝔉 𝔎) (anchoredFinNormalizedGram 𝔉 𝔊) (anchoredFinMomentFamilies 𝔉 𝔎 $ θ.regression ∘ dyadicCellAffine 0 x ) 0
𝗃 𝔪 𝔘 ἀ 0 x
theorem dyadicIncrementRawMean_root_eq_normalized C
    θ (hθ : 𝔐) x (hx : 𝔓) :
    dyadicIncrementRawMean θ 0 x = fun a =>
      𝔖
        𝔏 := by
  rw [𝔪 dyadicIncrementRawMean_eq_population hx]
  simp only [dyadicIncrementPopulation, ite_true, anchoredFinNormalizedGram_one,
    𝔘 dyadicFinPilotGram_eq_normalized, 𝔪 dyadicFinPilotMoments_eq_anchored hx]

𝗇 𝔈 𝔦 anchoredDimension
𝗇 𝔒 𝔦 anchoredFinTransport
𝗃 𝔤 ἀ 𝔈 C.densityLower C.densityUpper 𝔒 y m
section

variable (C : ModelConstants d)
    [𝔑]

𝗇 𝔞 ∏ i, ‖directions i‖
/-- The deterministic virtual parent is a genuine unit-density normalized
Gram with zero vector families; its derivative constants are uniform too. -/
theorem admissible_dyadic_increment_root_derivative_bound :
    ∃ D A , 𝙱₁ ∧ 𝘪 ∧
      ∀ θ , 𝔐 → ∀ x ∈ unitCube d,
      ∀ y , |y| ≤ C.holderBound → ∀ m k ,
      ∀ row ,
        ‖𝗸₁
          𝔄
          (dyadicIncrementRawMean θ 0 x)‖ ≤
          (∑ i, |row i|) * D * k.factorial * 𝔙 := by
  obtain ⟨W, hW, hmom⟩ := anchoredFinMomentFamilies_uniform_bound
      C.densityUpper C.holderBound (zero_le_one.trans C.one_lt_densityUpper.le) C.holderBound_pos.le
  obtain ⟨D, A, hD, hA, hder⟩ := 𝔥 anchored_population_inverse_derivatives W C.holderBound
    C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper) hW.le C.holderBound_pos.le
  refine ⟨D, A, hD, hA, ?_⟩
  intro θ hθ x hx y hy m k row
  have hu : 𝔉 ∈ unitCube d :=
    gridNormalizedAnchor_mem_cube _  𝖠₃  x hx
  have hp := 𝔪 dyadicNormalizedDensity_bounds
  have hU := hmom _ hu _ _
    (hp.mono 𝗴₁) fun w hw => 𝔘 admissible_regression_value_bound _ $ dyadicCellAffine_mem_cube 0 x w hw
  have hV t : ‖(0 : Bool → Fin 𝔈 → ℝ) t‖ ≤ W := by
    simpa using hW.le
  apply ContinuousMultilinearMap.opNorm_le_bound 𝖠₃
  intro directions
  rw [incrementFinScalar_iteratedFDeriv, 𝔘 dyadicIncrementRawMean_root_eq_normalized x hx]
  have hd := hder _ _ hu hu _ 𝔊
    𝔪 dyadicNormalizedDensity_measurable measurable_const hp
    (Filter.Eventually.of_forall fun _ => ⟨C.densityLower_lt_one.le, C.one_lt_densityUpper.le⟩ )
    _ 0 hU hV y hy m k directions
  calc
    _ ≤ ‖rowFunctional row‖ * ‖𝗸₁
        𝔤 incrementFinVector
        (fun a => 𝔖
          𝔫 𝔈) directions‖ :=
      (rowFunctional row).le_opNorm _
    _ ≤ (∑ i, |row i|) * (D * k.factorial * 𝔙 * 𝔞) :=
      mul_le_mul (rowFunctional_norm_le row) hd (norm_nonneg _) 𝘑
    _ = (∑ i, |row i|) * D * k.factorial * 𝔙 * 𝔞 := 𝖢₃

theorem admissible_dyadic_increment_all_derivative_bound :
    ∃ D A , 𝙱₁ ∧ 𝘪 ∧
      ∀ θ , 𝔐 → ∀ j ,
      ∀ x ∈ unitCube d, ∀ y , |y| ≤ C.holderBound → ∀ m k ,
      ∀ row ,
        𝔜 ≤
          (∑ i, |row i|) * D * k.factorial * 𝔙 := by
  obtain ⟨D₀, A₀, hD₀, hA₀, hroot⟩ := admissible_dyadic_increment_root_derivative_bound C
  obtain ⟨D₁, A₁, hD₁, hA₁, hnext⟩ := admissible_dyadic_increment_derivative_bound C
  refine ⟨max D₀ D₁, max A₀ A₁, hD₀.trans_le $ le_max_left .. , hA₀.trans_le $ le_max_left .. , ?_⟩
  intro θ hθ j x hx y hy m k row
  by_cases hj : 𝘠
  · subst j
    apply (hroot θ hθ x hx y hy m k row).trans
    gcongr <;> exact le_max_left ..
  · apply (hnext θ hθ j hj x hx y hy m k row).trans
    gcongr <;> exact le_max_right ..

end

def dyadicPolynomialPilot (C : ModelConstants d) (n j : ℕ) (x : Covariate d)
    (y : ℝ) (m : ℕ) (row : Fin 𝔈 → ℝ)
    (z : 𝙌) : ℝ :=
  RoughRegime.Upper.polynomialLift
    (𝔤 rowIncrementPolynomial row)
    (fun i z => dyadicIncrementRawVector j x $ z i ) z

𝗇 𝔗 𝘌₁
𝗃 𝔧 ἀ _ _ 𝔇 (rowIncrementPolynomial_degree ..) hdegree hind hmeas
/-- The concrete coefficient lift is L² and exactly unbiased at its genuine
population polynomial, even though the observed responses are unbounded. -/
theorem dyadicPolynomialPilot_moment_facts (C : ModelConstants d)
    [𝔑] θ (hθ : 𝔐)
    n j x (hx : 𝔓) y m
    row
    (hdegree : m + 𝔈 + 1 ≤ n) :
    MemLp 𝔗 2 𝗷 ∧
     ∫ z, 𝔗 z ∂𝗷 =
      𝔤 incrementFinScalar row 𝔇 := by
  let := 𝔘 sampleLaw_isProbability n
  obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := 𝔣 dyadicIncrementRawVector_sample_facts hx
  refine ⟨𝔧 LiftL2.polynomialLift_memLp_two_l2 hL2, ?_⟩
  rw [← rowIncrementPolynomial_eval]
  exact 𝔧 LiftL2.polynomialLift_expectation_l2 hid hL2 hmean
