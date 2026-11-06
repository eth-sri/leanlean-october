module

public import NearlyMinimax.PilotCommonBounds
public import RoughRegime.Macro
public import RoughRegime.Notation


public section

/-! Actual statistical consequences of a genuine population derivative bound.
The endpoint below will discharge its analytic input uniformly over domains. -/
open MeasureTheory ProbabilityTheory Matrix MvPolynomial
open scoped ENNReal Matrix.Norms.L2Operator
𝚨

𝗇 𝔇 𝖳₂ x y m row k (fun i => incrementGlobalVector j $ z $ Fin.castLEEmb hk i ) ^ 2
𝗇 𝔎 mul_nonneg 𝘑 hD.le
𝗇 𝔑 𝙌
𝗇 𝔘 sampleLaw θ n
𝗇 𝔧 𝗣
𝗇 𝔲 Fintype.card $ incrementVariables 𝔧
𝗇 𝕬 𝔲 * preconditionedPilotMomentConstant C C.order * 𝘟
𝗇 𝔄 A ^ 2 * 𝕬 / Λ
𝗇 𝔊 m + 𝔧 + 1
𝗇 𝔦 ∫ z : 𝔑, 𝔇 ∂ 𝔘
𝗃 𝔫 ἀ C θ hθ
𝗇 𝔬 𝘘
𝗇 𝔭 𝖠₂
𝗃 𝔴 ἀ (ℓ := C.order)
𝗃 𝕭 (ἀ * Λ ^ k)⁻¹ * 𝔦
section

𝗇 𝔳 𝖼₁
𝗇 𝔅 incrementFinScalar 𝔧 C.densityLower C.densityUpper 𝔳 y m row
𝗇 𝔐 dyadicIncrementRawMean θ j x
𝗇 𝔨 𝗸₁ 𝔅 𝔐
variable (C : ModelConstants d)
    [Nonempty 𝔬]
    (θ)
    (hθ : 𝙟)
    (D)
    (A)
    (hD : 𝙱₁)
    (hA : 𝘪)
    (hder : ∀ j , ∀ x ∈ unitCube d, ∀ y , |y| ≤ C.holderBound → ∀ m k ,
      ∀ row ,
        ‖𝔨‖ ≤ (∑ i, |row i|) * D * k.factorial * 𝚇₁)

include hθ hD hA hder

𝗇 𝔓 𝕬
𝗇 𝔖 fun i => 𝔫 dyadicIncrementRawVector_sample_second_le j x hx $ e i
𝗇 𝔙 𝚍₁ (preconditionedPilotMomentConstant_pos C _).le
𝗃 𝔵 ἀ $ e i
𝗇 𝔚 fun i a => 𝔵 hL2 a
𝗇 𝔞 𝔴 dyadicIncrementRawVector j x $ z i
𝗇 𝔟 fun i => 𝔵 X
𝗇 𝔠 fun i => 𝔵 hmeas
𝗃 𝔷 KernelMomentBounds.factorial_kernel_budget ἀ 𝔟 (hind.precomp e.injective) 𝔠 𝔚 E
theorem dyadicIncrementKernel_raw_budget_of_derivative :
    ∀ n j ,
      ∀ x ∈ unitCube d, ∀ y , |y| ≤ C.holderBound → ∀ m k ,
      ∀ row , ∀ hk ,
      ∀ Λ : ℝ, 𝔭 →
        𝕭 k.factorial ≤
          ((∑ i, |row i|) * D) ^ 2 * k.factorial *
            𝔄 ^ k := by
  intro n j x hx y hy m k row hk Λ hΛ
  let := 𝔫 sampleLaw_isProbability n
  obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := 𝔫 dyadicIncrementRawVector_sample_facts j x hx
  let X i (z : 𝔑) := 𝔞
  let e := Fin.castLEEmb hk
  let E := 𝔓
  have hE : 𝘃₂ := mul_nonneg 𝔙
      (dyadicPilotScale_pos ..).le
  have hb := 𝔷 𝔨 ((∑ i, |row i|) * D) A Λ hE 𝔎 hA.le hΛ
    𝔖
    $ hder j x hx y hy m k row
  have heq : (fun z =>
      𝔇) =
       fun z => 𝔨
        (fun i => 𝔵 X z) ^ 2 := by
    funext z
    rw [dyadicIncrementKernel_raw]
  grind


𝗇 𝔗 t.val + 1
𝗇 𝔣 fun z => eval z F
𝗇 𝔮 iteratedFDeriv ℝ 𝔗 𝔣 𝔐
theorem dyadicPolynomialPilot_variance_of_derivative :
    ∀ n j ,
      ∀ x ∈ unitCube d, ∀ y , |y| ≤ C.holderBound → ∀ m ,
      ∀ row ,
      𝔊 ≤ n →
      ∀ Λ : ℝ, 𝔭 → Λ ≤ n - 𝔊 + 1 →
        variance 𝘌₁ 𝔘 ≤
          ((∑ i, |row i|) * D) ^ 2 *
            ∑ t : Fin 𝔊,
               (𝔗).factorial *
                𝔄 ^ 𝔗 := by
  intro n j x hx y hy m row hdegree Λ hΛ hΛn
  let := 𝔫 sampleLaw_isProbability n
  let F := rowIncrementPolynomial 𝔧 C.densityLower C.densityUpper
    𝔳 y m row
  let X i (z : 𝔑) := 𝔞
  let E := 𝔓
  have hE : 𝘃₂ := mul_nonneg 𝔙
      (dyadicPilotScale_pos _ _).le
  obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := 𝔫 dyadicIncrementRawVector_sample_facts j x hx
  have hv := LiftL2.polynomialLift_variance_le_raw_power_l2 F X 𝔐
    (rowIncrementPolynomial_degree ..) hdegree hind hmeas hid hL2 hmean Λ hΛ
    𝖧₄
  apply hv.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  let e := Fin.castLEEmb $ (Nat.succ_le_of_lt t.isLt).trans hdegree
  have hFeval : 𝔣 = 𝔅 := by
    funext z
    exact rowIncrementPolynomial_eval ..
  have hd : ‖𝔮‖ ≤
       (∑ i, |row i|) * D * ((𝔗).factorial : ℝ) * A ^ 𝔗 := by
    simp_all
  have hb := 𝔷 𝔮 ((∑ i, |row i|) * D) A Λ hE 𝔎 hA.le hΛ
    𝔖 hd
  linarith

end


𝗇 𝔈 𝗟 ^ J
𝗇 𝔉 𝘮
𝗇 𝔍 𝗙₁
𝗇 𝔒 dyadicPilotRow j w.1 w.2
𝗇 𝔛 𝙩
𝗇 𝔜 ν w ^ 2
𝗇 𝔡 ν w * dyadicPilotErrorField C θ n j y m z w
𝗇 𝔢 (Nat.succ_le_of_lt r.isLt).trans hdegree
𝗇 𝔏 H w r
𝗇 𝔔 C.densityUpper ^ 2 / dyadicPilotScale d 𝔉
𝗇 𝔤 ((𝔍).factorial : ℝ)
𝗇 𝔥 DyadicPilotLabelIndex d 𝔉
𝗇 𝔩 δ r * ‖Op r 𝔏‖ ^ 2
𝗃 𝕮 ἀ (e r) X hind hmeas hL2
𝗇 𝔪 𝕮 FieldLiftCovariance.raw_kernel_operator_norm_sq 𝔏
𝗇 𝔯 ‖Op r‖ * B r
𝗇 𝔰 e r i
𝗇 𝔱 regularPairDesignMeasure θ 𝔈
𝗃 𝔶 ∑ r : Fin ἀ, 𝔤 * 𝔄 ^ 𝔍
theorem dyadicPilotErrorField_test_variance_of_raw_budget (C : ModelConstants d)
    [Nonempty 𝔬] (θ : RegressionParameter d) (hθ : 𝙟)
    (D A : ℝ) (hD : 𝙱₁) (hA : 𝘪)
    (hraw : ∀ n j : ℕ,
      ∀ x ∈ unitCube d, ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m k : ℕ,
      ∀ row : Fin 𝔧 → ℝ, ∀ hk : k ≤ n,
      ∀ Λ : ℝ, 𝔭 →
        𝕭 𝖽₁ ≤
          ((∑ i, |row i|) * D) ^ 2 * 𝖽₁ *
            𝔄 ^ k) :
    ∀ n j J : ℕ, j ≤ J →
      ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m : ℕ,
      𝔊 ≤ n →
      ∀ Λ : ℝ, 𝔭 → Λ ≤ 𝙒 - 𝔊 + 1 →
      ∀ ν : 𝔛 → ℝ,
      MemLp ν 2 (𝔱 𝖠₃ ) →
      variance (fun z => ∫ w, 𝔡
        ∂𝔱  𝖠₃ ) 𝔘 ≤
      𝔔 *
        ((dyadicPilotRowCap d C.order j J * D) ^ 2 *
          𝔶 𝔊) *
         ∫ w, 𝔜 ∂𝔱  𝖠₃  := by
  intro n j J hj y hy m hdegree Λ hΛ hΛn ν hν
  let := 𝔫 sampleLaw_isProbability n
  let M := 𝔱 𝖠₃
  let := 𝔫 regularPairDesignMeasure_isFinite 𝔈 𝖠₃
  let R := 𝔊
  let X (i : Fin n) (z : 𝔑) := 𝔴 incrementGlobalVector j $ z i
  let H (w : 𝔛) (r : Fin R) :=
    𝖳₂ w.1 y m 𝔒 𝔍
  let rowcap := dyadicPilotRowCap d C.order j J
  have hrowcap : 0 ≤ rowcap := dyadicPilotRowCap_nonneg _ _ _ _
  have hcube : 𝖶₂ :=
    (𝔫 regularPairDesignMeasure_cube_ae 𝔈 𝖠₃ ).mono fun w hw => hw.1
  have hrow := 𝔴 dyadicPilotRow_pair_cap C θ hθ j J hj
  have hHmeas (r : Fin R) : AEStronglyMeasurable (fun w => 𝔏) M :=
    (𝔫 dyadicIncrementKernel_field_measurable j y m 𝔍 _
      $ dyadicPilotRow_field_measurable j ).aestronglyMeasurable
  have hH (r : Fin R) : Integrable (fun w => ν w • 𝔏) M :=
    𝔫 dyadicIncrementKernel_weighted_integrable j y hy m 𝔍 _
      (dyadicPilotRow_field_measurable j) M rowcap hrowcap hcube hrow ν hν
  obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := 𝔴 incrementGlobalVector_sample_facts C θ hθ j
  let e (r : Fin R) := Fin.castLEEmb 𝔢
  let Op (r : Fin R) := 𝕮 FieldLiftCovariance.rawKernelOperator
  have hcaps (r : Fin R) : ∃ B : ℝ, 𝘶₁ ∧ ∀ᵐ w ∂M, ‖𝔏‖ ≤ B :=
    𝔫 dyadicIncrementKernel_field_norm_bound j y hy m 𝔍 _ M rowcap hrowcap hcube hrow
  let B (r : Fin R) := Classical.choose $ hcaps r
  have hBpos (r : Fin R) : 0 < B r := (Classical.choose_spec $ hcaps r ).1
  have hBcap (r : Fin R) : ∀ᵐ w ∂M, ‖𝔏‖ ≤ B r := (Classical.choose_spec $ hcaps r ).2
  have hopcap (r : Fin R) : ∀ᵐ w ∂M, ‖Op r 𝔏‖ ≤ 𝔯 := by
    filter_upwards [hBcap r] with w hw
    exact ((Op r).le_opNorm _).trans $ mul_le_mul_of_nonneg_left hw $ norm_nonneg _
  have hblock (c : Fin $ Fintype.card 𝔥 ) :
      M.real {w | dyadicPilotLabel 𝔉 w.1 = c} ≤ 𝔔 := by
    have hs : {w : 𝔛 | dyadicPilotLabel 𝔉 w.1 = c} =
        {w | regularGridCell (𝗟 ^ 𝔉)  𝖠₃  w.1 =
          (Fintype.equivFin 𝔥).symm c} := by
      ext w
      exact (Fintype.equivFin 𝔥).apply_eq_iff_eq_symm_apply
    rw [hs]
    exact 𝔫 regularPairDesignMeasure_parent_block_mass 𝔈  𝖠₃  j _
  have hu := FieldLiftCovariance.integrated_centered_lift_variance_localized
    (μ := 𝔘) (M := M) (n := n)
    (p := Fintype.card $ IncrementGlobalIndex d C.order j ) (R := R)
    (q := Fintype.card 𝔥) H ν hν hH hHmeas
    (fun w r σ v => dyadicIncrementKernel_symmetric C θ j w.1 y m 𝔒 _ σ v)
    X 𝚆₁ hdegree hind hmeas hid hL2 hmean Λ hΛ
     𝖤₃ 
    (fun w => dyadicPilotLabel 𝔉 w.1) ((dyadicPilotLabel_measurable _).comp measurable_fst)
    (fun r => 𝔯) (fun r => mul_nonneg (norm_nonneg $ Op r ) (hBpos r).le) hopcap
    (fun r w v hv => Filter.Eventually.of_forall fun z =>
      dyadicIncrementKernel_disjoint C θ j 𝔍  𝖡₃  w.1 v.1 hv y y m m
        𝔒 (dyadicPilotRow j v.1 v.2) fun i => z 𝔰 )
    𝔔 hblock
  let δ (r : Fin R) := (𝔤 * Λ ^ 𝔍)⁻¹
  let S (w : 𝔛) := ∑ r : Fin R, 𝔩
  let P := (rowcap * D) ^ 2 * 𝔶 R
  have hSmeas : AEStronglyMeasurable S M := by
    have hm : AEStronglyMeasurable (∑ r : Fin R, fun w => 𝔩) M :=
      Finset.aestronglyMeasurable_sum Finset.univ fun r _ =>
        ((Op r).continuous.comp_aestronglyMeasurable $ hHmeas r ).norm.pow 2 |>.const_mul (δ r)
    convert hm using 1
    funext w
    simp only [S, Finset.sum_apply]
  have hSnon w : 0 ≤ S w := Finset.sum_nonneg fun r _ => mul_nonneg  𝖠₃  $ sq_nonneg _
  have hSbound : ∀ᵐ w ∂M, S w ≤ P := by
    filter_upwards [hcube, hrow] with w hw hr
    unfold S P
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    have hb := hraw n j w.1 hw y hy m 𝔍 𝔒
      𝔢 Λ hΛ
    have he :=
      𝔪
    rw [he]
    apply hb.trans
    have hprod : 0 ≤ 𝔄 := by
      have hc := preconditionedPilotMomentConstant_pos C C.order
      have hk := dyadicPilotScale_pos d j
      positivity
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_right _
      $ 𝚍₁ $ pow_nonneg hprod _
    apply pow_le_pow_left₀ 𝔎
    exact mul_le_mul_of_nonneg_right hr hD.le
  have hStop : MemLp S ∞ M := memLp_top_of_bound hSmeas P $ hSbound.mono fun w hw => by
    rw [Real.norm_eq_abs, abs_of_nonneg $ hSnon w ]
    exact hw
  have hi : Integrable (fun w => 𝔜 * S w) M := by
    convert hν.integrable_sq.mul_of_top_right hStop using 1
    funext w
    simp only [Pi.mul_apply]
    ring
  have hile := integral_mono_ae hi (hν.integrable_sq.const_mul P)
    $ hSbound.mono fun w hw => (mul_le_mul_of_nonneg_left hw $ sq_nonneg $ ν w ).trans_eq $ mul_comm _ _
  rw [integral_const_mul] at hile
  have hrhs : ∫ w, 𝔜 * ∑ r : Fin R, δ r *
      ∫ z : 𝔑, 𝔏 (fun i => X 𝔰 z) ^ 2 ∂ 𝔘 ∂M =
      ∫ w, 𝔜 * S w ∂M := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w => by
      apply congrArg fun a => 𝔜 * a
      apply Finset.sum_congr rfl
      intro r _
      rw [← 𝔪]
  have herr : (fun z : 𝔑 => ∫ w, ν w *
      LiftL2.centeredKernelExpansion 0 (H w) (fun i z => X i z - 𝚆₁) z ∂M) =
       fun z => ∫ w, 𝔡 ∂M := by
    funext z
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w => congrArg (fun a => ν w * a)
      $ 𝔫 dyadicPolynomialPilot_centered_global n j w.1 y m 𝔒 hdegree z
  rw [herr, hrhs] at hu
  exact hu.trans $ by
    have hL : 0 ≤ 𝔔 := by
      exact 𝚚₁ (dyadicPilotScale_pos _ _).le
    nlinarith
