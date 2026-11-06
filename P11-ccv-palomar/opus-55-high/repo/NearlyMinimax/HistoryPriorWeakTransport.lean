module

public import NearlyMinimax.HistoryWeakTransport
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-!
# Weak evolution under the actual positive history prior, rather than only its polynomial
-/

𝛊
𝚨

𝚲

𝗇 𝔄 𝘼
𝗇 𝔅 𝚉₂ (historyReferenceRho Δ) t B (historyReferenceRho_pos Δ) ht hB a habound hsmall
𝗇 𝔇 t * B / historyReferenceRho Δ ≤ 𝙥
𝗇 𝔈 0 ≤ (𝙖 : ℝ) ^ Fintype.card J
𝗇 𝔉 𝘽
𝗇 𝔊 𝙁
𝗇 𝔍 (historyMarkedDensity_measurable dependent _ t a ha).ennreal_ofReal
𝗇 𝔎 Eventually.of_forall 𝘕
𝗇 𝔏 𝙤
𝗃 𝔑 ἀ dependent Δ t π a
𝗇 𝔐 𝔑 historyMarkedPrior_eq_withDensity ha
𝗃 𝔒 ἀ dependent $ historyReferenceRho Δ
/-- A source-positive history prior expectation is exactly its actual polynomial integral. -/
theorem historyMarkedPrior_integral_eq_expectation (dependent : 𝔊)
    (hrefl : 𝙂) (hsymm : 𝔄)
    (Δ : ℕ) (hlabels : 𝔉)
    (t B : ℝ) (ht : 𝘈) (hB : 𝙐) [MeasurableSpace E]
    (π : Measure E) a (ha : Measurable a) (habound : ∀ e, |a e| ≤ B)
    (hsmall : 𝔇)
    F :
     ∫ h, F h ∂𝔑 historyMarkedPrior =
      𝔒 historyMarkedExpectation 𝔏 a F t := by
  rw [𝔐,
    integral_withDensity_eq_integral_toReal_smul
      𝔍
      𝔎 F]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro h
  have hb := 𝔅 h
  simp only [ENNReal.toReal_ofReal $ (by positivity : 𝔈).trans hb.1 ]
  ring

/-- The signed local append expression evaluated under the actual positive prior. -/
def historyMarkedPriorGenerator (dependent : 𝔊)
    (hsymm : 𝔄) (Δ : ℕ) (t : ℝ)
    [MeasurableSpace E] (π : Measure E) (a : 𝙏)
    (F : 𝙗 → ℝ) : ℝ :=
  ∑ j, ∫ p : 𝙗 × E,
    F (𝙯₁ p) * a p.2
      ∂(𝔑 historyMarkedPrior).prod π

/-- The genuine prior generator equals the source reference polynomial generator. -/
theorem historyMarkedPriorGenerator_eq_reference (dependent : 𝔊)
    (hrefl : 𝙂) (hsymm : 𝔄)
    (Δ : ℕ) (hlabels : 𝔉)
    (t B : ℝ) (ht : 𝘈) (hB : 𝙐) [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] a (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : 𝔇)
    F :
    𝚄₂ a F =
      historyMarkedGeneratorExpectation dependent hsymm (historyReferenceRho Δ) t
        𝔏 π a F := by
  apply Finset.sum_congr rfl
  intro j hj
  have hm : Measurable fun p : 𝙗 × E =>
      ENNReal.ofReal $ 𝔒 historyMarkedDensity t a p.1 :=
    (𝔒 historyMarkedDensity_measurable t a ha).ennreal_ofReal.comp measurable_fst
  rw [𝔐,
    prod_withDensity_left 𝔍,
    integral_withDensity_eq_integral_toReal_smul hm
      𝔎]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  have hb := 𝔅 p.1
  simp only [ENNReal.toReal_ofReal $ (by positivity : 𝔈).trans hb.1 ]
  ring
