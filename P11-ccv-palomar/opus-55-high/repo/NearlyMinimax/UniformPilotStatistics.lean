module

public import NearlyMinimax.PilotAnalyticToStatistics
public import NearlyMinimax.UniformPilotDerivatives
public import RoughRegime.Macro
public import RoughRegime.Notation


public section

/-! Domain-uniform actual statistical pilot bounds. Analytic witnesses are
chosen before the extension domain, then transferred through the genuine
L² factorial kernel calculations and multilevel aggregation. -/
𝚵
𝚮
𝚨

section

𝗇 𝔗 Nonempty 𝘘
variable (C : ModelConstants d)
    [𝔗]

𝗇 𝔢 𝗣
𝗇 𝔄 m + 𝔢 + 1
𝗇 𝔅 A ^ 2 * (Fintype.card (incrementVariables 𝔢) * preconditionedPilotMomentConstant C C.order * 𝘟) / Λ
𝗇 𝔊 𝘻₁
𝗇 𝔎 sampleLaw θ n
𝗇 𝔚 𝖠₂
𝗇 𝔛 𝘌₁
𝗇 𝔜 t.val + 1
𝗃 𝔭 ἀ C A Λ
𝗇 𝔮 dyadicPilotRow j x z
𝗇 𝔯 𝙱₁
𝗇 𝔰 𝘪
𝗇 𝔱 𝔄 ≤ n
𝗇 𝔲 Λ ≤ n - 𝔄 + 1
𝗇 𝔳 dyadicPilotErrorField C θ n j y m
𝗇 𝕭 (x, z)
𝗃 𝕰 ἀ C θ hθ n
𝗃 𝕱 (dyadicPilotRowCap d C.order ἀ L * D) ^ 2
theorem dyadicPilotErrorField_point_second_of_variance θ (hθ : 𝙟)
    D A (hD : 𝔯) (hA : 𝔰)
    (hv : ∀ n j ,
      ∀ x ∈ unitCube d, ∀ y , |y| ≤ C.holderBound → ∀ m ,
      ∀ row ,
      𝔱 →
      ∀ Λ : ℝ, 𝔚 → 𝔲 →
        variance 𝔛 𝔎 ≤
          ((∑ i, |row i|) * D) ^ 2 *
            ∑ t : Fin 𝔄,
               (𝔜).factorial *
                𝔅 ^ 𝔜) :
    ∀ n j L , j ≤ L → ∀ x ∈ unitCube d, ∀ z ∈ unitCube d,
      regularGridCell 𝔊  𝖠₃  x =
        regularGridCell 𝔊  𝖠₃  z →
      ∀ y , |y| ≤ C.holderBound → ∀ m ,
      𝔱 → ∀ Λ : ℝ, 𝔚 →
      𝔲 →
       ∫ t, 𝔳 t 𝕭 ^ 2 ∂ 𝔎 ≤
        𝕱 j * 𝔭 dyadicPilotSeries j m := by
  intro n j L hj x hx z hz hc y hy m hdegree Λ hΛ hΛn
  obtain ⟨hL2, hmean⟩ := 𝕰 dyadicPolynomialPilot_moment_facts j x hx y m
    𝔮 hdegree
  have h := hv n j x hx y hy m 𝔮 hdegree Λ hΛ hΛn
  rw [variance_eq_integral hL2.aemeasurable, hmean] at h
  have hr := dyadicPilotRow_sum_abs_le_fine_cell (ℓ := C.order) j L hj x z hx hz hc.symm
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ $ 𝔭 dyadicPilotSeries_nonneg hΛ.le ..
  apply pow_le_pow_left₀ $ mul_nonneg 𝘑 hD.le
  bound


𝗇 𝔥 Fin 𝗯
𝗇 𝔩 m j.val + 𝔢 + 1
𝗇 𝔈 ∀ j : 𝔥, 𝔩 ≤ n
𝗇 𝔉 𝗟 ^ L
𝗃 𝕲 Λ ≤ (n : ℝ) - ἀ + 1
𝗇 𝔍 ∀ j : 𝔥, 𝕲 𝔩
𝗇 𝔏 (𝔢 * D) ^ 2
𝗇 𝔪 ((𝔢 : ℝ) * D) ^ 2
𝗇 𝔐 𝔪
𝗇 𝔒 𝔭 dyadicSeriesEnvelope J m
𝗇 𝔔 (Nat.le_of_lt_succ j.isLt).trans hJL
𝗇 𝕯 dyadicMultilevelErrorField C θ n J y m t
𝗇 𝔘 𝕯 𝕭 ^ 2
𝗇 𝔞 𝔥
𝗇 𝔟 (2 ^ L)⁻¹ ^ 2
𝗇 𝔣 ∫ t, X j t ^ 2 ∂ 𝔎
𝗇 𝔤 𝙊
𝗇 𝔦 𝕲 𝔄
𝗇 𝔨 ∫ t, 𝔘 ∂ 𝔎
𝗇 𝔫 dyadicPilotErrorField C θ n j.val y (m j.val) t
𝗇 𝔴 (2 ^ j.val) ^ 2
𝗃 𝕴 𝔏 * d * 𝔟 * ἀ
theorem dyadicMultilevelErrorField_point_second_of_variance (θ : RegressionParameter d) (hθ : 𝙟)
    (D A : ℝ) (hD : 𝔯) (hA : 𝔰)
    (hv : ∀ n j : ℕ,
      ∀ x ∈ unitCube d, ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m : ℕ,
      ∀ row ,
      𝔱 →
      ∀ Λ : ℝ, 𝔚 → 𝔦 →
        variance 𝔛 𝔎 ≤
          ((∑ i, |row i|) * D) ^ 2 *
            ∑ t : Fin 𝔄,
              ((𝔜).factorial : ℝ) *
                𝔅 ^ 𝔜) :
    ∀ n J L : ℕ, 𝚗₂ → ∀ x ∈ unitCube d, ∀ z ∈ unitCube d,
      regularGridCell 𝔉  𝖠₃  x =
        regularGridCell 𝔉  𝖠₃  z →
      ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m : 𝙦₁,
      𝔈 →
      ∀ Λ : ℝ, 𝔚 →
      𝔍 →
      𝔨 ≤
        4 * 𝔐 * 𝔤 *
          dyadicMultilevelBudget 𝔒 J L := by
  have hpoint := dyadicPilotErrorField_point_second_of_variance C θ hθ D A hD hA hv
  intro n J L hJL x hx z hz hc y hy m hdegree Λ hΛ hΛn
  let H := 𝔒
  have hH := 𝔭 dyadicSeriesEnvelope_nonneg hΛ.le J m
  let B := 𝕴 H
  have hB : 𝙐 := 𝖠₃
  let X (j : 𝔞) t :=
    𝔫 𝕭
  have hX j :=
    (𝕰 dyadicPilotErrorField_point_moment_facts j.val x hx z y (m j.val) $ hdegree j ).1
  have hE j : 𝔣 ≤ B * 𝔴 := by
    have h := hpoint n j.val L 𝔔
      x hx z hz hc y hy (m j.val) (hdegree j) Λ hΛ $ hΛn j
    apply h.trans
    rw [dyadicPilotRowCap_square]
    calc
      _ ≤ 𝕴 𝔴 * H :=
        mul_le_mul_of_nonneg_left (𝔭 dyadicPilotSeries_le_envelope hΛ.le J m j) 𝖠₃
      𝘿 := 𝖢₃
  have h := secondMoment_dyadic_sum_le 𝔎 J X hX B hB hE
  apply h.trans_eq
  dsimp [dyadicMultilevelBudget]
  ring


𝗇 𝔧 C.densityUpper ^ 2
𝗇 𝕮 𝙉
𝗃 𝕳 (ἀ ^ L)⁻¹ ^ 2
𝗇 𝔇 𝔧 * 𝔪 * 𝔤 * 𝕳 𝕮 * (𝕮 ^ j.val) ^ 2
𝗇 𝔑 ν w * 𝕯 w
𝗇 𝔓 𝗟 ^ J
𝗇 𝔖 𝕮
𝗇 𝔠 j.val - 1
𝗇 𝔡 ν w ^ 2
𝗇 𝔵 𝔖 ^ d
𝗇 𝔶 H / Λ
𝗇 𝔷 𝔭 dyadicPilotSeries j.val $ m j.val
𝗇 𝕬 regularPairDesignMeasure θ 𝔉
𝗃 𝕵 𝔧 / dyadicPilotScale d ἀ
theorem dyadicMultilevelErrorField_test_second_of_variance (θ : RegressionParameter d) (hθ : 𝙟)
    (D A : ℝ) (hD : 𝔯) (hA : 𝔰)
    (htest : ∀ n j J : ℕ, j ≤ J →
      ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m : ℕ,
      𝔱 →
      ∀ Λ : ℝ, 𝔚 → 𝔦 →
      ∀ ν ,
      MemLp ν 2 (regularPairDesignMeasure θ 𝔓 𝖠₃ ) →
      variance (fun z => ∫ w, ν w * 𝔳 z w
        ∂regularPairDesignMeasure θ 𝔓  𝖠₃ ) 𝔎 ≤
      𝕵 𝘮 *
        ((dyadicPilotRowCap d C.order j J * D) ^ 2 *
          ∑ r : Fin 𝔄,
            ((𝗙₁).factorial : ℝ) *
              𝔅 ^ 𝗙₁) *
         ∫ w, 𝔡 ∂regularPairDesignMeasure θ 𝔓  𝖠₃  ) :
    ∀ n J L : ℕ, 𝚗₂ → ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m : 𝙦₁,
      𝔈 →
      ∀ Λ : ℝ, 𝔚 →
      𝔍 →
      ∀ ν ,
      MemLp ν 2 (𝕬 𝖠₃ ) →
       ∫ t, (∫ w, 𝔑
        ∂𝕬  𝖠₃ ) ^ 2 ∂ 𝔎 ≤
         4 * 𝔧 * 𝔵 *
          𝔐 * 𝔤 *
            dyadicMultilevelBudget 𝔒 J L / Λ *
           ∫ w, 𝔡 ∂𝕬  𝖠₃  := by
  intro n J L hJL y hy m hdegree Λ hΛ hΛn ν hν
  let := 𝕰 sampleLaw_isProbability
  let M := 𝕬 𝖠₃
  let H := 𝔒
  have hH := 𝔭 dyadicSeriesEnvelope_nonneg hΛ.le J m
  let I := ∫ w, 𝔡 ∂M
  have hI : 0 ≤ I := integral_nonneg 𝖸
  let B := 𝔧 * 𝔵 *
    𝔐 * 𝔤 *
      𝕳 𝔖 * 𝔶 * I
  have hB : 𝙐 := 𝖠₃
  let X (j : 𝔞) t :=
    ∫ w, ν w * 𝔫 w ∂M
  have hf j := 𝕰 dyadicPilotErrorField_test_moment_facts j.val L
    𝔔 y hy (m j.val) (hdegree j) ν hν
  have hE j : 𝔣 ≤ B * (𝔖 ^ j.val) ^ 2 := by
    have h := htest n j.val L 𝔔 y hy
      (m j.val) (hdegree j) Λ hΛ (hΛn j) ν hν
    rw [variance_of_integral_eq_zero (hf j).1.aemeasurable (hf j).2] at h
    apply h.trans
    change 𝕵 𝔠 *
      (𝕱 j.val * 𝔷) * I ≤ _
    rw [dyadicPilotRowCap_square]
    have hs := 𝔭 dyadicPilotSeries_div_scale_le_envelope hΛ J m j
    have hsnon := div_nonneg (𝔭 dyadicPilotSeries_nonneg hΛ.le j.val $ m j.val )
      (dyadicPilotScale_pos d j.val).le
    calc
      _ = 𝔇 *
          (dyadicPilotScale d j.val / dyadicPilotScale d 𝔠) *
          (𝔷 / dyadicPilotScale d j.val) * I := by
        field_simp [(dyadicPilotScale_pos d j.val).ne', (dyadicPilotScale_pos d 𝔠).ne']
        <;> ring
      _ ≤ 𝔇 *
          𝔵 * 𝔶 * I := by
        apply mul_le_mul_of_nonneg_right _ hI
        exact mul_le_mul (mul_le_mul_of_nonneg_left ((div_le_iff₀ $ dyadicPilotScale_pos _ _ ).mpr dyadicPilotScale_parent_ratio_le) 𝖠₃ ) hs hsnon 𝖠₃
      𝘿 := 𝖢₃
  have h := secondMoment_dyadic_sum_le 𝔎 J X (fun j => (hf j).1) B hB hE
  have heq : (fun t => ∑ j, X j t) =
       fun t => ∫ w, 𝔑 ∂M := by
    funext t
    exact (𝕰 dyadicMultilevelErrorField_test_integral_sum J L hJL y hy m hdegree ν hν t).symm
  have heqpoint t := congrFun heq t
  simp_rw [heqpoint] at h
  apply h.trans_eq
  dsimp [B, dyadicMultilevelBudget]
  ring


𝗇 𝔙 dyadicMultilevelBudget (dyadicSeriesEnvelope (pilotModelConstants C) A Λ J m) J L
𝗃 𝔬 ἀ CE θ hθe D A hD hA
theorem uniform_domain_common_dyadicMultilevel_bounds :
    ∃ D A , 𝔯 ∧ 𝔰 ∧ ∀ U , ∀ θ , Admissible (C.withDomain U) θ →
      ∀ n J L , 𝚗₂ → ∀ y , |y| ≤ max C.holderBound 1 → ∀ m ,
      𝔈 →
      ∀ Λ : ℝ, 𝔚 →
      (∀ j : 𝔞, Λ ≤ n - 𝔩 + 1) →
      (∀ x ∈ unitCube d, ∀ z ∈ unitCube d,
        regularGridCell 𝔊  𝖠₃  x =
          regularGridCell 𝔊  𝖠₃  z →
        𝔨 ≤
          4 * 𝔏 * d *
            𝔙) ∧
       ∀ ν ,
        MemLp ν 2 (regularPairDesignMeasure θ 𝔊 𝖠₃ ) →
         ∫ t, (∫ w, 𝔑
          ∂regularPairDesignMeasure θ 𝔊  𝖠₃ ) ^ 2 ∂ 𝔎 ≤
           4 * 𝔧 * 𝖥 *
            𝔏 * d *
              𝔙 / Λ *
             ∫ w, 𝔡 ∂regularPairDesignMeasure θ 𝔊  𝖠₃  := by
  letI : Nonempty $ AnchoredIndex d (pilotModelConstants C).order :=
    inferInstanceAs 𝔗
  obtain ⟨D, A, hD, hA, hder⟩ := uniform_domain_admissible_dyadic_increment_all_derivative_bound
    (pilotModelConstants C) (pilotModelConstants C).holderBound (pilotModelConstants C).holderBound_pos.le
  refine ⟨D, A, hD, hA, ?_⟩
  intro U θ hθ n J L hJL y hy m hdegree Λ hΛ hΛn
  let CE := (pilotModelConstants C).withDomain U
  letI : Nonempty $ AnchoredIndex d CE.order := inferInstanceAs 𝔗
  have hθe : Admissible CE θ := by
    simpa only [pilotModelConstants_withDomain] using admissible_pilotModelConstants (C.withDomain U) θ hθ
  have hd := hder U θ hθe
  have hv := 𝔬 dyadicPolynomialPilot_variance_of_derivative hd
  have ht := 𝔬 dyadicPilotErrorField_test_variance_of_raw_budget $ 𝔬 dyadicIncrementKernel_raw_budget_of_derivative hd
  constructor
  · intro x hx z hz hc
    exact 𝔬 dyadicMultilevelErrorField_point_second_of_variance hv
      n J L hJL x hx z hz hc y hy m hdegree Λ hΛ hΛn
  · intro ν hν
    exact 𝔬 dyadicMultilevelErrorField_test_second_of_variance ht
      n J L hJL y hy m hdegree Λ hΛ hΛn ν hν
