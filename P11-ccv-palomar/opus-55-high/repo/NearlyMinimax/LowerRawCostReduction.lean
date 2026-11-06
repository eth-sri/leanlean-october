module

public import NearlyMinimax.LowerSaddle
public import NearlyMinimax.RawCostAlgebra
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The exact raw-energy expression at the actual lower saddle gives the
squared target risk scale. This module is purely numerical: no minimax or
desired-rate premise occurs in its raw-energy input. -/
𝚷
𝚨
𝚭
𝚩

𝗃 𝔐 ἀ s d m θ C
𝗇 𝔅 𝔐 lowerSaddleEta cf x
𝗇 𝔏 𝔐 lowerSaddleN τM x
𝗃 𝔔 ἀ+1
𝗃 𝔖 ἀ^(-d)
/-- The three actual primitive local-score energy contributions. -/
def lowerSaddleRawEnergyBound (s d m θ C cf C5 C6 C7 ch Bl : ℝ)
    (τM : 𝙜) (x : ℝ) : ℝ :=
  let η := 𝔅
  let μ := lowerSaddleMu d m θ C x
  let N := 𝔏
  let M := 𝗫
  let D := 𝙵
  3*(C5+C7)*𝗩*μ^2*𝔖 N +
    3*C6*𝗩*(Real.exp (2*τM M*M)*N^𝚜₂)*(C6*μ)^𝔔 M/(𝔔 M).factorial +
    Real.exp ch*𝗩*𝔔 Bl^2*(ch*μ)^𝔔 D/(𝔔 D).factorial

𝗇 𝔄 𝔐 lowerSaddleActivity τM x
𝗇 𝔒 lowerSaddleH d m θ C x
𝗇 𝔇 𝘄₂+𝔖 𝔒*E
𝗇 𝔈 E ≤ 𝔐 lowerSaddleRawEnergyBound cf C5 C6 C7 ch Bl τM x
𝗇 𝔉 𝙽₁
𝗇 𝔊 𝚄
𝗇 𝔎 Real.rpow_nonneg (lowerSaddleN_positive ..).le _
𝗃 𝔓 0 ≤ ἀ
/-- Exact inverse-volume bookkeeping converts the genuine primitive
energy bound to the source's explicit seven-constant cost expression. -/
theorem lowerSaddle_raw_energy_cost
    τM (hx : 𝔓 x) (hcf : 𝔓 cf) (hCB : 𝔓 CB)
    (hC5 : 𝔓 C5) (hC6 : 𝔓 C6) (hC7 : 𝔓 C7) (hch : 𝔓 ch)
    (hB : 1 ≤ 𝔄) (hBl : 𝔓 Bl)
    (hcost : Bl ≤ CB*𝔄)
    (hE : 𝔈) :
    let CG := 𝔉
    𝔇 ≤
      CG*(𝔄^2+
        𝔐 lowerSaddleEnergyOne τM x+
        𝔐 lowerSaddleEnergyTwo CG τM x+
        𝔐 lowerSaddleEnergyThree CG τM x) := by
  let h := 𝔒
  have hh : 0 < h := lowerSaddleH_positive ..
  have he : 𝔅^4 = cf^4*h^𝔊 := by
    unfold lowerSaddleEta
    rw [mul_pow, ← Real.rpow_mul_natCast hh.le]
    ring
  have hp : h^d*h^𝔊 = h^(d+𝔊) := (Real.rpow_add hh ..).symm
  have hr := raw_energy_cost_bound





    (Real.rpow_pos_of_pos hh _)
     𝖦₄  hx (Real.rpow_nonneg hh.le _) he hB hBl hCB hC5 hC6 hC7 hcf hch
    𝔎
    (mul_nonneg 𝙫 𝔎)
    hcost 𝗫 𝙵 hE
  rw [Real.rpow_neg hh.le] at ⊢
  have he1 : x^2*h^d*h^𝔊*𝔖 𝔏 =
      𝔐 lowerSaddleEnergyOne τM x := by
    unfold lowerSaddleEnergyOne
    grind
  rw [he1] at hr
  simpa only [lowerSaddleEnergyTwo, lowerSaddleEnergyThree, ← mul_assoc] using hr

𝗇 𝔍 𝘦₂
𝗇 𝔑 𝙾₁
/-- The actual shrunk-endpoint saddle supplies the cost bound eventually;
the only remaining variables are the genuine raw activity and energy. -/
theorem eventually_actual_lowerSaddle_raw_cost
    (hs : 𝚊₁) (hd : 𝔊 < d) (ha : 𝙆) (hab : 𝙭)
    (hcf : 𝔓 cf) (hCB : 𝔓 CB) (hC5 : 𝔓 C5) (hC6 : 𝔓 C6)
    (hC7 : 𝔓 C7) (hch : 𝔓 ch)
    (hC : 1+Real.log 𝔉+
      (𝙷₁-16*s)/(d*𝔑)*lowerSaddleTheta s d 𝔍+
      𝖩₁*𝔍/𝔑 < C) :
    ∀ᶠ x : ℝ in atTop,
      let m := lowerSaddleCoefficient s d 𝔍
      let θ := lowerSaddleTheta s d 𝔍
      let τM := 𝙉₂
      let B := 𝔄
      ∀ Bl E , 1 ≤ B → 𝔓 Bl → Bl ≤ CB*B →
        𝔈 →
      𝔇 ≤
        3*𝔉*B^2 := by
  filter_upwards [eventually_actual_lowerSaddle_numeric_cost hs hd ha hab (lt_of_lt_of_le zero_lt_one $ rawCostConstant_ge_one .. ) hC,
    eventually_ge_atTop 0] with x hx hx0
  dsimp at hx ⊢
  intro Bl E hB hBl hcost hE
  exact (lowerSaddle_raw_energy_cost _ hx0 hcf hCB hC5 hC6 hC7 hch hB hBl hcost hE).trans hx

/-- A true cost denominator bound yields the square of the actual saddle
risk. This is algebra, without a statistical lower-bound premise. -/
theorem lowerSaddle_cost_risk_reduction
    τM (hden : 0 < den) (hCG : 0 < CG) (hctr : 𝔓 ctr)
    (hcost : den ≤ 3*CG*𝔄^2) :
    ctr/(3*CG)* 𝔐 lowerSaddleRisk cf τM x ^2 ≤
      ctr*𝔅^4/den := by
  have hh := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ ctr*𝔅^4) hden hcost
  apply le_trans _ hh
  apply le_of_eq
  unfold lowerSaddleRisk
  field_simp
