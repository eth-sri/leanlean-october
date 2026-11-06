module

public import NearlyMinimax.HistoryCanonicalDeletion
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Genuine independent finite mark histories preserve the mean of affine
updates. Integrability is derived by product Fubini, without a desired-history
integrability or expectation premise. -/
𝚯
𝚨
𝚽
𝚩

𝗇 𝔇 J → 𝙏
𝗇 𝔈 fun i : Fin n => i
def finiteAffineHistory (slope offset : 𝔇)
    (n : ℕ) (labels : Fin n → J) (marks : 𝗚₁) : ℝ :=
  (List.ofFn 𝔈).foldl
    (fun value i => slope (labels i) (marks i) * value + offset (labels i) (marks i)) 1

𝗇 𝔄 finiteAffineHistory slope offset n fun i => labels i.castSucc
𝗇 𝔅 labels $ Fin.last n
𝗇 𝔊 marks $ Fin.last n
𝗇 𝔍 finiteAffineHistory slope offset 𝗉 labels
theorem finiteAffineHistory_succ (slope offset : 𝔇)
    n labels marks :
    𝔍 marks =
      slope 𝔅 𝔊 *
        𝔄 (fun i => marks i.castSucc) +
      offset 𝔅 𝔊 := by
  unfold finiteAffineHistory
  rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hh : (List.ofFn fun i => i.castSucc ) =
      (List.ofFn 𝔈).map Fin.castSucc := 𝖨₄
  rw [hh, List.foldl_map]

𝗇 𝔉 (ho j).comp_fst _
section

variable [MeasurableSpace E]
    (π : Measure E)
    [IsProbabilityMeasure π]
    (slope offset : 𝔇)
    (hs : ∀ j, Integrable (slope j) π)
    (ho : ∀ j, Integrable (offset j) π)

include hs ho

𝗇 𝔎 𝘰
𝗇 𝔏 finiteAffineHistory slope offset n labels
theorem finiteAffineHistory_integrable n labels :
    Integrable 𝔏 𝔎 := by
  induction n with
  | zero => exact integrable_const _
  | succ n ih =>
    let j := 𝔅
    let f := 𝔄
    apply ((historyFiniteMarkAppendEquiv_preserving n π).integrable_comp_emb
      (historyFiniteMarkAppendEquiv n).measurableEmbedding).mp
    convert ((hs j).mul_prod $ ih _ ).add 𝔉 using 1
    funext ⟨fresh, marks⟩
    simp only [Function.comp_apply, finiteAffineHistory_succ,
      historyFiniteMarkAppendEquiv_last, historyFiniteMarkAppendEquiv_old]
    rfl

𝗃 𝔐 ∫ e, ἀ j e ∂π
theorem finiteAffineHistory_integral_one (hmean : ∀ j, 𝔐 slope + 𝔐 offset = 1)
    n labels :
     ∫ marks, 𝔏 marks
      ∂𝔎 = 1 := by
  induction n with
  | zero => simp only [finiteAffineHistory, List.ofFn_zero, List.foldl_nil, integral_const,
      measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, mul_one]
  | succ n ih =>
    let j := 𝔅
    let f := 𝔄
    rw [← (historyFiniteMarkAppendEquiv_preserving n π).integral_comp
      (historyFiniteMarkAppendEquiv n).measurableEmbedding]
    have he : (fun p =>
        𝔍 $ historyFiniteMarkAppendEquiv n p ) =
         fun p => slope j p.1 * f p.2 + offset j p.1 := by
      funext ⟨fresh, marks⟩
      simp only [finiteAffineHistory_succ, historyFiniteMarkAppendEquiv_last,
        historyFiniteMarkAppendEquiv_old]
      rfl
    rw [he, integral_add ((hs j).mul_prod $ finiteAffineHistory_integrable π slope offset hs ho n _ )
      𝔉, integral_prod_mul, integral_fun_fst]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, ih, mul_one]
    exact hmean j
