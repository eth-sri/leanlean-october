module

public import NearlyMinimax.PopulationMomentDerivatives
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗎

/-! Scalar feature-row derivative bounds for the actual population inverse pilots. -/

open Matrix MeasureTheory
𝚺

𝗇 𝔅 𝗢
𝗇 𝔊 𝔅 →L[ℝ] ℝ
def rowFunctional (row : 𝔅) : 𝔊 :=
  ∑ i, row i • (ContinuousLinearMap.proj i : 𝔊)

@[simp] theorem rowFunctional_apply (row z : 𝔅) :
    rowFunctional row z = row ⬝ᵥ z := by
  simp [rowFunctional, dotProduct]

theorem rowFunctional_norm_le (row : 𝔅) :
    ‖rowFunctional row‖ ≤ ∑ i, |row i| := by
  apply ContinuousLinearMap.opNorm_le_bound
  · positivity
  intro z
  rw [rowFunctional_apply, dotProduct]
  calc
    ‖∑ i, row i * z i‖ ≤ ∑ i, ‖row i * z i‖ := norm_sum_le ..
    _ ≤ ∑ i, |row i| * ‖z‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z i) $ abs_nonneg _
    _ = (∑ i, |row i|) * ‖z‖ := by rw [Finset.sum_mul]

𝗃 𝔏 ἀ r lo hi T y m
𝗇 𝔇 𝔏 incrementFinVector
def incrementFinScalar (r : ℕ) (lo hi : ℝ) (T : 𝗲 ℝ)
    (y : ℝ) (m : ℕ) (row : 𝔅) :
    (𝚕 → ℝ) → ℝ :=
  fun x => row ⬝ᵥ 𝔇 x

𝗇 𝔈 𝔏 incrementFinScalar row
𝗇 𝔍 𝗸₁
theorem incrementFinScalar_iteratedFDeriv (r : ℕ) [NeZero r] lo hi
    T y m k row
    x
    v :
    𝔍 𝔈 x v =
      rowFunctional row (𝔍 𝔇 x v) := by
  have h := (rowFunctional row).iteratedFDeriv_comp_left (x := x)
    (𝔏 incrementFinVector_contDiff).contDiffAt $ show 𝘪₂ from le_top
  have hFun : rowFunctional row ∘ 𝔇 =
      𝔈 := by
    aesop
  simp_all

𝗃 𝔉 ἀ d ℓ
𝗇 𝔄 fun j => incrementValuation (anchoredFinNormalizedGram u p) (anchoredFinNormalizedGram v q) (anchoredFinMomentFamilies u p f) (anchoredFinMomentFamilies v q g) $ (Fintype.equivFin $ incrementVariables 𝔉 anchoredDimension ).symm j
𝗇 𝔎 ∏ j, ‖directions j‖
𝗃 𝔐 ἀ 𝔉 anchoredDimension a b 𝔉 anchoredFinTransport y m
/-- Passing to a scalar row and to the genuine derivative operator norm costs
only a fixed finite row factor. Constants still do not depend on polynomial
degree, derivative order, anchor, density, response, or the moment center. -/
theorem anchored_actual_population_row_derivative_operator_bound
    [Nonempty 𝔉 AnchoredIndex] a b F Y
    (ha : 𝙆) (hab : 𝙭) (hF : 0 ≤ F) (hY : 0 ≤ Y) :
    ∃ C A , 𝙴 ∧ 𝘪 ∧
      ∀ u v , 𝘨₁ → v ∈ unitCube d →
      ∀ p q f g , Measurable p → Measurable q →
      𝖡 →
      𝗭 →
      (∀ w ∈ unitCube d, |f w| ≤ F) → (∀ w ∈ unitCube d, |g w| ≤ F) →
      ∀ y , |y| ≤ Y → ∀ m k ,
      ∀ row ,
        ‖𝔍
          (𝔐 incrementFinScalar row)
          𝔄‖ ≤
          (∑ i, |row i|) * C * k.factorial * 𝚇₁ := by
  obtain ⟨C, A, hC, hA, hDer⟩ := anchored_actual_population_inverse_derivatives
    (d := d) (ℓ := ℓ) a b F Y ha hab hF hY
  refine ⟨C, A, hC, hA, ?_⟩
  intro u v hu hv p q f g hpmeas hqmeas hp hq hf hg y hy m k row
  apply ContinuousMultilinearMap.opNorm_le_bound 𝖠₃
  intro directions
  rw [incrementFinScalar_iteratedFDeriv]
  calc
    _ ≤ ‖rowFunctional row‖ * ‖𝔍
        𝔐 incrementFinVector
        𝔄 directions‖ :=
      (rowFunctional row).le_opNorm _
    _ ≤ (∑ i, |row i|) * (C * k.factorial * 𝚇₁ * 𝔎) := by
      apply mul_le_mul (rowFunctional_norm_le row)
        (hDer u v hu hv p q f g hpmeas hqmeas hp hq hf hg y hy m k directions)
        (norm_nonneg _) 𝘑
    _ = (∑ i, |row i|) * C * k.factorial * 𝚇₁ * 𝔎 := 𝖢₃
