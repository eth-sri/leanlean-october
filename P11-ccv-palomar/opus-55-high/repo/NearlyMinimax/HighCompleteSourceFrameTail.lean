module

public import NearlyMinimax.HighCompleteSourceTail
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The all-count numerator cap for the actual periodic source field.
Frame and amplitude thresholds are fixed before the grid, selector orders,
history, and extension domain. No field/profile/cap premise remains. -/
𝚸
𝚪
𝚨
𝛀
set_option maxHeartbeats 1800000
𝚬
𝚿

𝗇 𝔄 η*w u* ∑ γ, φ u γ*c j γ
𝗃 𝔑 ἀ d k
𝗇 𝔅 fun u => 𝔑 highLocalFieldWithout D η c j $ x u
𝗇 𝔇 fun u => 𝔑 highPeriodicTensor j $ x u
𝗇 𝔈 𝚏₁
𝗇 𝔐 highFramePolynomial $ c l
𝗇 𝔉 fun l => 𝔐
𝗇 𝔊 𝖻 lam ℓ N μ
𝗇 𝔍 𝗝+1
𝗇 𝔎 𝖿
𝗇 𝔏 𝖯
𝗃 𝔒 ἀ R $ highCenterMix C
theorem completeSourceNumerator_original_field_bound [NeZero d]
    C (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 η0 : ℝ, 𝚣₂ ∧ 0 < η0 ∧
      ∀ k D M q n : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder 𝔑 HighWindowLabels),
      𝗑 → 𝗕 → 𝗘 → 𝗚 →
      highCenterResolutionThreshold C ≤ 𝖧 →
      ∀ Cfr lam ℓ N μ cf : ℝ, Cfr0 ≤ Cfr → 𝙲₁ → 𝖰₂ → 𝚐₁ →
      cf*𝙦^(-C.smoothness) ≤ η0 →
      ∀ V : ℝ, |𝖮₂| ≤ Q.ρ →
      ∀ j : 𝔑 HighWindowLabels,
      ∀ h ,
      ∀ x : 𝙇, ∀ y ,
      let R := 𝔊
      let η := 𝔎
      let c := 𝔏
      |highMarkedLocalScoreNumerator 𝔒 highUnionLaw
        𝔒 highUnionActivation Q.a V η
        (fun u => 𝙾 $ x u )
        (fun e u => 𝘖₁ e $ x u )
        𝚑₁
        𝔅
        𝔇
        𝔈 (c j) y| ≤
        𝙪₂^n*
          𝙎*(highRowTotalMass R.rowMass+1) := by
  obtain ⟨Cfr0,hfr0,hfield⟩ := highFrameField_original_model_bounds C
  let η0 := Q.ρ/(2*𝔍)
  refine ⟨Cfr0,η0,hfr0, div_pos Q.ρ_pos 𝖠₃ ,?_⟩
  intro k D M q n hk0 horder hk hD hq hn hM Cfr lam ℓ N μ cf hfr hℓ hℓN hcf hη V hV j h x y
  letI := hk0
  letI := horder
  let R := 𝔊
  let G := 𝖠 ℓ N μ (hfr0.trans hfr) hℓ hℓN
  let c := 𝔏
  let η := 𝔎
  let g := 𝔅
  let w := 𝔇
  let φ : Fin n → 𝙮 → ℝ := 𝔈
  have hηn : 𝗼 := 𝖠₃
  have hamp : 𝔍*η ≤ Q.ρ/2 := by
    have ht := (le_div_iff₀ 𝖠₃ ).mp hη
    nlinarith
  have hηρ : η ≤ Q.ρ/2 := by nlinarith [pow_nonneg (by norm_num : 𝙋 ≤ 2) d]
  have hP l : frameCoefficientL1 𝔐 ≤ Cfr0⁻¹ := by
    apply (highFramePolynomial_coefficientL1_le _).trans
    exact (𝘛₁ l).trans
      $ (inv_le_inv₀  𝖡₄  𝖡₄ ).mpr hfr
  have hF := (hfield k hk0 hk cf hcf 𝔉 hP).1
  have hw u : |w u| ≤ 1 := by
    rw [abs_of_nonneg $ 𝔑 highPeriodicTensor_nonneg j $ x u ]
    exact 𝔑 highPeriodicTensor_le_one  𝖡₃  j $ x u
  have hφ (v : 𝙮 → ℝ) hv u :=
    highLocalFrameFeature_ball_abs_le_one k j (x u) Cfr (hfr0.trans hfr) v hv
  have hg u : |g u| ≤ Q.ρ/2 := by
    have hh : |𝔄| ≤ η := by
      rw [abs_mul,abs_mul,abs_of_nonneg hηn]
      have ht := mul_le_mul (hw u) (hφ (c j) (𝘛₁ j) u) (abs_nonneg _) 𝖠₄
      nlinarith
    have hd := 𝔑 highFrameField_local_decomposition D hk η c j $ x u
    have he : g u = 𝔑 highFrameField η 𝔉 (x u)-
        𝔄 := 𝖡₄
    rw [he]
    exact (abs_sub _ _).trans $ (add_le_add (hF $ x u ) hh).trans $ by nlinarith only [hamp]
  exact completeSourceNumerator_all_count_exponential_bound C hD hq hM Cfr lam ℓ N μ
    (hfr0.trans hfr) hℓ hℓN hn j h Q.a V η Q.ρ Q.a_pos hηn Q.ρ_pos.le hηρ x g w φ
    hg hw hφ (fun f hf z => Q.c_pos.le.trans $ (Q.legal f V hf hV).2.2.1 z ) y
