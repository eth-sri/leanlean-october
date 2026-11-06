module

public import NearlyMinimax.UniformPopulationPairBounds
public import NearlyMinimax.PilotModelEnvelope
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! Genuine all-order inverse-pilot derivative witnesses chosen before every
extension domain, including the actual identity/zero virtual parent at root. -/
𝛎
𝚺
𝚨
𝚭
𝚩

theorem pilotModelConstants_withDomain C (U : ExtensionDomain d) :
    pilotModelConstants (C.withDomain U) = (pilotModelConstants C).withDomain U := rfl

𝗇 𝔄 𝘮
𝗃 𝔊 ἀ d C.order
𝗃 𝔑 ἀ θ j x
𝗇 𝔎 𝔑 dyadicIncrementRawMean
𝗃 𝔐 ἀ 𝔊 anchoredDimension C.densityLower C.densityUpper 𝔊 anchoredFinTransport y m
𝗇 𝔅 ‖𝗸₁ 𝔐 incrementFinVector 𝔎 directions‖
𝗇 𝔇 ∏ i, ‖directions i‖
𝗇 𝔈 𝘠
section

variable (C : ModelConstants d)
    [Nonempty 𝔊 AnchoredIndex]

𝗃 𝔉 ἀ (C.withDomain Udom) θ
𝗇 𝔍 𝚇₁
𝗃 𝔏 𝔉 ἀ hθ j x
/-- A common genuine vector derivative bound at all actual population means. -/
theorem uniform_domain_dyadic_increment_vector_derivative_bound Y (hY : 0 ≤ Y) :
    ∃ D A , 𝙱₁ ∧ 𝘪 ∧
      ∀ Udom , ∀ θ , 𝔉 Admissible →
      ∀ j , ∀ x ∈ unitCube d, ∀ y , |y| ≤ Y → ∀ m k ,
      ∀ directions ,
        𝔅 ≤
          D * k.factorial * 𝔍 * 𝔇 := by
  obtain ⟨W, hW, hmom⟩ := uniform_domain_admissible_dyadicFinPilotMoments_uniform_bound C
  obtain ⟨B, A, hB, hA, hder⟩ := anchored_population_inverse_derivatives
    (d := d) (ℓ := C.order) C.densityLower C.densityUpper W Y C.densityLower_pos
    (C.densityLower_lt_one.trans C.one_lt_densityUpper) hW.le hY
  refine ⟨B, A, hB, hA, ?_⟩
  intro Udom θ hθ j x hx y hy m k directions
  let q := if 𝔈 then 𝙃 else dyadicNormalizedDensity θ 𝔄 x
  have hqm : Measurable q := by
    by_cases hj : 𝔈
    · simpa [q, hj, ModelConstants.withDomain] using measurable_const
    · simpa [q, hj, ModelConstants.withDomain] using 𝔉 dyadicNormalizedDensity_measurable hθ 𝔄 x
  have hqb : 𝚎₂ := by
    by_cases hj : 𝔈
    · exact Filter.Eventually.of_forall fun _ => by
        simpa [q, hj, ModelConstants.withDomain] using And.intro C.densityLower_lt_one.le C.one_lt_densityUpper.le
    · simpa [q, hj, ModelConstants.withDomain] using 𝔉 dyadicNormalizedDensity_bounds hθ 𝔄 x
  have hV t : ‖(if 𝔈 then (0 : Bool → Fin 𝔊 anchoredDimension → ℝ)
      else dyadicFinPilotMoments θ 𝔄 x) t‖ ≤ W := by
    by_cases hj : 𝔈
    · simpa [hj] using hW.le
    · simpa only [hj, ite_false] using hmom Udom θ hθ 𝔄 x hx t
  have hd := hder 𝘎₂ (dyadicNormalizedAnchor 𝔄 x)
    (gridNormalizedAnchor_mem_cube 𝘷  𝖠₃  x hx)
    (gridNormalizedAnchor_mem_cube (2 ^ 𝔄)  𝖠₃  x hx)
    𝔑 dyadicNormalizedDensity q
    𝔏 dyadicNormalizedDensity_measurable hqm
    𝔏 dyadicNormalizedDensity_bounds hqb
    𝔑 dyadicFinPilotMoments (if 𝔈 then 0 else dyadicFinPilotMoments θ 𝔄 x)
    (hmom Udom θ hθ j x hx) hV y hy m k directions
  rw [← 𝔏 dyadicIncrementRawMean_eq_with_virtual_parent hx] at hd
  exact hd

/-- Uniform-domain U5(4) after arbitrary scalar feature-row postcomposition.
The constants precede the domain and all polynomial/derivative orders. -/
theorem uniform_domain_admissible_dyadic_increment_all_derivative_bound (Y : ℝ) (hY : 0 ≤ Y) :
    ∃ D A : ℝ, 𝙱₁ ∧ 𝘪 ∧
      ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, 𝔉 Admissible →
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ y : ℝ, |y| ≤ Y → ∀ m k : ℕ,
      ∀ row ,
        ‖𝗸₁
          (𝔐 incrementFinScalar row)
          𝔎‖ ≤
          (∑ i, |row i|) * D * 𝖽₁ * 𝔍 := by
  obtain ⟨D, A, hD, hA, hder⟩ := uniform_domain_dyadic_increment_vector_derivative_bound C Y hY
  refine ⟨D, A, hD, hA, ?_⟩
  intro Udom θ hθ j x hx y hy m k row
  apply ContinuousMultilinearMap.opNorm_le_bound 𝖠₃
  intro directions
  rw [incrementFinScalar_iteratedFDeriv]
  calc
    _ ≤ ‖rowFunctional row‖ * 𝔅 := (rowFunctional row).le_opNorm _
    _ ≤ (∑ i, |row i|) * (D * 𝖽₁ * 𝔍 * 𝔇) :=
      mul_le_mul (rowFunctional_norm_le row) (hder Udom θ hθ j x hx y hy m k directions) (norm_nonneg _) 𝘑
    _ = (∑ i, |row i|) * D * k.factorial * 𝔍 * 𝔇 := 𝖢₃
