module

public import NearlyMinimax.HighCompleteSourceMarkedTail
public import NearlyMinimax.HighSourceCanonicalResponse
public import NearlyMinimax.HigherBandRawCollapse
public import NearlyMinimax.HighSourceHigherCounts
public import RoughRegime.Macro
public import RoughRegime.Notation


@[expose] public section

/-! Primitive local response guards derived uniformly from the actual
periodic frame and canonical source. Constants are fixed before the grid,
selector orders, history and sample configuration. -/
𝚫
𝚨
𝚬
𝚿

𝗃 𝔖 ἀ d k
𝗇 𝔅 𝔖 highLocalFieldWithout D eta c j
𝗇 𝔓 highLocalFrameFeature k j x
𝗇 𝔇 eta*𝔖 highPeriodicTensor j x* ∑ γ, 𝔓 γ*v γ
𝗇 𝔈 𝙮 → ℝ
𝗇 𝔉 𝔖 highPeriodicTensor j
𝗇 𝔍 𝗾₁
𝗇 𝔐 𝔖 HighWindowLabels
structure HighFrameOriginalLocalGuards (d k D : ℕ) [NeZero k] (Cfr eta rho : ℝ)
    (c : 𝔐 → 𝔈) : Prop where
  amplitude_nonneg : 0 ≤ eta
  amplitude_half : eta ≤ rho/2
  coefficient_ball : ∀ j, ∑ γ, |c j γ| ≤ 𝔍
  weight_abs : ∀ j x, |𝔉 x| ≤ 1
  without_abs : ∀ j x, |𝔅 x| ≤ rho/2
  regression_abs : ∀ j (v : 𝔈), ∑ γ, |v γ| ≤ 𝔍 →
    ∀ x, |𝔅 x + 𝔇| ≤ rho

𝗇 𝔄 𝖿
𝗇 𝔎 𝗝+1
𝗇 𝔏 𝔖 HighFrameOriginalLocalGuards D Cfr
𝗇 𝔑 highFramePolynomial $ c j
𝗃 𝔔 ἀ j v hv x
theorem highFrame_original_local_guards (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 eta0 , 𝚣₂ ∧ 𝖴₁ ∧
      ∀ k D : ℕ, ∀ (_ : NeZero k), 𝗑 → ∀ Cfr cf : ℝ,
      Cfr0 ≤ Cfr → 𝚐₁ → 𝔄 ≤ eta0 →
      ∀ c ,
      (∀ j, ∑ γ, |c j γ| ≤ 𝔍) →
      𝔏 𝔄 Q.ρ c := by
  obtain ⟨Cfr0,hfr0,hfield⟩ := highFrameField_original_model_bounds C
  let eta0 := Q.ρ/(2*𝔎)
  refine ⟨Cfr0,eta0,hfr0,div_pos Q.ρ_pos 𝖠₃ ,?_⟩
  intro k D hk0 hk Cfr cf hfr hcf heta c hc
  letI := hk0
  let eta := 𝔄
  have hfr1 := hfr0.trans hfr
  have hen : 0 ≤ eta := 𝖠₃
  have hamp : 𝔎*eta ≤ Q.ρ/2 := by
    have ht := (le_div_iff₀ 𝖠₃ ).mp heta
    nlinarith
  have hehalf : eta ≤ Q.ρ/2 := by nlinarith [pow_nonneg (by norm_num : 𝙋 ≤ 2) d]
  have hP j : frameCoefficientL1 𝔑 ≤ Cfr0⁻¹ := by
    apply (highFramePolynomial_coefficientL1_le _).trans
    exact (hc j).trans $ (inv_le_inv₀  𝖡₄  𝖡₄ ).mpr hfr
  have hF := (hfield k hk0 hk cf hcf (fun j => 𝔑) hP).1
  have hw j x : |𝔉 x| ≤ 1 := by
    rw [abs_of_nonneg $ 𝔖 highPeriodicTensor_nonneg j x ]
    exact 𝔖 highPeriodicTensor_le_one  𝖡₃  j x
  have hprof j (v : 𝔈) hv x :=
    highLocalFrameFeature_ball_abs_le_one k j x Cfr hfr1 v hv
  have hterm j (v : 𝔈) (hv : ∑ γ, |v γ| ≤ 𝔍) x :
      |𝔇| ≤ eta := by
    rw [abs_mul,abs_mul,abs_of_nonneg hen]
    have ht := mul_le_mul (hw j x) 𝔔 hprof (abs_nonneg _) 𝖠₄
    nlinarith
  have hg j x : |𝔅 x| ≤ Q.ρ/2 := by
    have he : 𝔅 x =
        𝔖 highFrameField eta 𝗏₁ x -
          eta*𝔉 x* ∑ γ, 𝔓 γ*c j γ := by
      linarith [ 𝔖 highFrameField_local_decomposition D hk eta c j x ]
    rw [he]
    exact (abs_sub ..).trans $ (add_le_add (hF x) $ hterm j (c j) (hc j) x ).trans
      $ by nlinarith only [hamp]
  refine ⟨hen,hehalf,hc,hw,hg,?_⟩
  intro j v hv x
  exact 𝘝₂ $ by linarith only [hg j x,𝔔 hterm,hehalf]

𝗇 𝔊 𝖻 lam ell N mu
𝗇 𝔒 𝖯
theorem completeSource_original_local_guards [NeZero d]
    C (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 eta0 , 𝚣₂ ∧ 𝖴₁ ∧
      ∀ k D M q : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder 𝔐),
      𝗑 → 𝗕 → 𝗘 → 𝘧 →
      ∀ Cfr lam ell N mu cf : ℝ, Cfr0 ≤ Cfr → 𝚁₁ → 𝘈₂ → 𝚐₁ →
      𝔄 ≤ eta0 →
      ∀ h ,
      let R := 𝔊
      𝔏 𝔄 Q.ρ
        𝔒 := by
  obtain ⟨Cfr0,eta0,hfr0,heta0,hguards⟩ := highFrame_original_local_guards C Q
  refine ⟨Cfr0,eta0,hfr0,heta0,?_⟩
  intro k D M q hk0 horder hk hD hq hM Cfr lam ell N mu cf hfr hell hellN hcf heta h
  letI := hk0
  letI := horder
  let R := 𝔊
  have G := 𝖠 ell N mu
    (hfr0.trans hfr) hell hellN
  exact hguards k D hk0 hk Cfr cf hfr hcf heta 𝔒
    𝘛₁

theorem HighFrameOriginalLocalGuards.ternary_floor
    [NeZero k] (Q : LowSmoothnessTernaryConstants C)

    (H : 𝔏 eta Q.ρ c)
    (hV : |𝖮₂| ≤ Q.ρ) (j : 𝔐)
    (v : 𝔈) (hv : ∑ γ, |v γ| ≤ 𝔍)
    (x : Covariate d) (y : Fin 3) :
    Q.c ≤ highMarkedResponseMass Q.a V eta 𝔅
      𝔉 (fun x => 𝔓) v x y := (Q.legal _ V 𝔔 H.regression_abs hV).2.2.1 y
