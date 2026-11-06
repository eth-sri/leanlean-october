module

public import NearlyMinimax.HighSourceOriginalGuards
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Direct original-model response identities for the canonical complete
source. Uniform ternary positivity is derived from the actual periodic
field, and low-count cancellation has no supplied response guard. -/
𝚫
𝚪
𝚨
𝚩
set_option maxHeartbeats 1800000
𝚬
𝚿

𝗇 𝔄 highUnionSourceMarkedNumerator C R n Q.a V eta j h x y
𝗇 𝔅 fun i => highLocalFieldWithout d k D eta c j $ x i
𝗇 𝔇 𝖿
𝗃 𝔏 ἀ d k j $ x i
𝗇 𝔈 fun i => 𝔏 highLocalCoordinates
𝗇 𝔉 fun i => 𝙾 $ x i
𝗇 𝔊 fun i => 𝔏 highPeriodicTensor
𝗇 𝔍 𝖻 lam ell N mu
𝗇 𝔎 𝖯
𝗃 𝔐 ἀ _ _ lam ell N mu
theorem completeSource_original_response_exact_and_low_counts [NeZero d]
    C (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 eta0 , 𝚣₂ ∧ 𝖴₁ ∧
      ∀ k D M q : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder 𝙯),
      𝗑 → 𝗕 → 𝗘 → 𝘧 →
      ∀ Cfr lam ell N mu cf : ℝ, Cfr0 ≤ Cfr → 𝚁₁ → 𝘈₂ → 𝚐₁ →
      𝔇 ≤ eta0 →
      ∀ V , |𝖮₂| ≤ Q.ρ → ∀ j ,
      ∀ h ,
      ∀ n , ∀ x , (∀ i, x i ∈ 𝘋) →
      ∀ y ,
      let R := 𝔍
      let eta := 𝔇
      let c := 𝔎
      𝔄 =
        completeSourceRawNumerator (C.densityLower+𝗙) (C.densityUpper-𝗙)
          lam ell N mu D M q Cfr Q.a V eta 𝔈
          𝔉
          𝔅
          𝔊 (c j) y ∧
        (n ≤ 1 → 𝔄 = 0) := by
  obtain ⟨Cfr0,eta0,hfr0,heta0,hguards⟩ := completeSource_original_local_guards C Q
  refine ⟨Cfr0,eta0,hfr0,heta0,?_⟩
  intro k D M q hk0 horder hk hD hq hM Cfr lam ell N mu cf hfr hell hellN hcf heta V hV j h n x hx y
  letI := hk0
  letI := horder
  let R := 𝔍
  let eta := 𝔇
  let c := 𝔎
  let U := 𝔈
  let p := 𝔉
  let g := 𝔅
  let w := 𝔊
  have hfr1 := hfr0.trans hfr
  have G := 𝖠 ell N mu hfr1 hell hellN
  have H := hguards k D M q hk0 horder hk hD hq hM Cfr lam ell N mu cf hfr hell hellN hcf heta h
  have hmass (v : 𝙮 → ℝ) (hv : ∑ γ, |v γ| ≤ 𝗾₁) i b :
      0 ≤ ternaryMass Q.a
        (coefficientRegression eta g w 𝚏₁ v i) V b := Q.c_pos.le.trans $ H.ternary_floor Q hV j v hv (x i) b
  have he := completeSourceRawNumerator_eq_canonical C hD hq hM Cfr lam ell N mu
    hfr1 hell hellN j h x hx Q.a V eta Q.a_pos.ne' g w hmass y
  change 𝔄 =
    𝔐 completeSourceRawNumerator D M q Cfr Q.a V eta U p g w (c j) y at he
  refine ⟨he,?_⟩
  intro hn
  rw [he]
  obtain ⟨ha,hab⟩ := 𝗌₁
  have hp i :=
    𝘄₁
  have hU i r : |U i r| ≤ 2 :=
    (𝔏 highLocalCoordinates_abs_le_one r).trans 𝖠₄
  have hcases : n = 0 ∨ n = 1 := 𝖡₃
  rcases hcases with rfl | rfl
  · exact 𝔐 completeSourceRawNumerator_count_zero ha hab D M q  𝖡₃ 
      Cfr Q.a V eta U p g w (c j) y
  · exact 𝔐 completeSourceRawNumerator_count_one ha hab D M q  𝖡₃  hq
      Cfr Q.a V eta  𝖡₄  U hU p g w hp (c j) y
