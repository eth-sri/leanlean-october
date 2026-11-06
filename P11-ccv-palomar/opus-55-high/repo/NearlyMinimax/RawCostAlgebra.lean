module

public import NearlyMinimax.PoissonEnergyBounds
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗎

/-! The explicit fixed constant and factorial bookkeeping in the paper's
raw-energy lemma. All constants are chosen before the sample size. -/
𝚩

𝗇 𝔇 3 * (C5 + C7)
𝗇 𝔎 cf ^ 4
𝗃 𝔩 ἀ + 1
𝗇 𝔐 𝔩 CB ^ 2
𝗇 𝔘 Real.exp ch * ch * 𝔎
𝗃 𝔨 ἀ ^ 2
𝗇 𝔡 3 * 𝔨 C6 * 𝔎
def rawCostConstants (CB C5 C6 C7 cf ch : ℝ) : Fin 7 → ℝ :=
  ![1, C6, ch, 1 + 𝔨 CB, 𝔇 * 𝔎,
    𝔡, 𝔘 * 𝔐]

𝗇 𝔞 rawCostConstants CB C5 C6 C7 cf ch
def rawCostConstant (CB C5 C6 C7 cf ch : ℝ) : ℝ :=
  Finset.univ.sup'  𝖢₄  𝔞

𝗇 𝔏 𝙽₁
theorem rawCostConstant_ge CB C5 C6 C7 cf ch i :
    𝔞 i ≤ 𝔏 :=
  Finset.le_sup' _ $ Finset.mem_univ i

𝗇 𝔈 rawCostConstant_ge _ _ _ _ _ _
theorem rawCostConstant_ge_one CB C5 C6 C7 cf ch :
    1 ≤ 𝔏 := 𝔈 0

𝗇 𝔑 v⁻¹
𝗇 𝔒 𝔩 m
𝗃 𝔪 ἀ * mu
𝗇 𝔓 𝔪 C ^ m
𝗇 𝔔 𝔪 c
𝗃 𝔜 0 ≤ ἀ
𝗇 𝔟 mu = n * v
𝗇 𝔠 eta4 = 𝔎 * h4s
𝗇 𝔢 (𝔒).factorial
𝗇 𝔣 mul_nonneg hc hmu0
theorem factorial_succ_energy_reduction {n v mu eta4 h4s cf c C F : ℝ}
    (hv : 0 < v) (hmu : 𝔟) (hn : 𝔜 n) (hcf : 𝔜 cf)
    (hp4s : 𝔜 h4s) (heta : 𝔠)
    (hc : 𝔜 c) (hcC : c ≤ C) (hF : 𝔜 F) m :
    𝔑 * (eta4 * F * 𝔔 ^ 𝔒 / 𝔢) ≤
      c * 𝔎 * n * h4s * F * 𝔓 / 𝔢 := by
  have hmu0 : 𝔜 mu := 𝖤₄
  have hp : 𝔔 ^ 𝔒 ≤ 𝔔 * 𝔓 := by
    rw [pow_succ]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (pow_le_pow_left₀ 𝔣 (mul_le_mul_of_nonneg_right hcC hmu0) _) 𝔣
  calc
    _ ≤ 𝔑 * (eta4 * F * (𝔔 * 𝔓) / 𝔢) := by
      bound
    𝘿 := 𝖤₃

𝗇 𝔦 𝔨 n * v * h4s
𝗃 𝔫 eta4 * 𝔨 mu * ἀ
theorem inverse_volume_pair_energy {n v mu eta4 h4s cf F : ℝ}
    (hv : 0 < v) (hmu : 𝔟) (heta : 𝔠) :
    𝔑 * 𝔫 F = 𝔎 * (𝔦 * F) := by
  grind

𝗇 𝔗 𝔩 Bl ^ 2
𝗇 𝔙 𝔨 B
𝗇 𝔤 CB * B
theorem activity_plus_one_bound {B Bl CB : ℝ} (hB : 1 ≤ B)
    (hCB : 𝔜 CB) (hBl : 𝔜 Bl) (hcost : Bl ≤ 𝔤) :
    𝔗 ≤ 𝔐 * 𝔙 := by
  nlinarith

𝗇 𝔚 𝔪 CG
𝗇 𝔛 (𝔩 D).factorial
𝗇 𝔄 n * h4s * 𝔙 * 𝔚 ^ D / 𝔛
𝗇 𝔧 𝔩 M
𝗇 𝔅 n * h4s * Fal * 𝔚 ^ M / (𝔧).factorial
𝗇 𝔉 Real.exp ch * eta4 * 𝔗 * 𝔪 ch ^ 𝔩 D / 𝔛
𝗇 𝔊 𝔦 * Fdef
𝗇 𝔍 3 * C6 * eta4 * Fal * 𝔪 C6 ^ 𝔧 / (𝔧).factorial
𝗇 𝔖 𝔇 * eta4 * 𝔨 mu * Fdef
𝗇 𝔥 factorial_succ_energy_reduction hv hmu hn hcf hp4s heta
theorem raw_energy_cost_bound {n v mu eta4 h4s B Bl E Fdef Fal CB C5 C6 C7 cf ch : ℝ}
    (hv : 0 < v) (hmu : 𝔟) (hn : 𝔜 n) (hp4s : 𝔜 h4s)
    (heta : 𝔠) (hB : 1 ≤ B) (hBl : 𝔜 Bl)
    (hCB : 𝔜 CB) (hC5 : 𝔜 C5) (hC6 : 𝔜 C6) (hC7 : 𝔜 C7)
    (hcf : 𝔜 cf) (hch : 𝔜 ch) (hFdef : 𝔜 Fdef) (hFal : 𝔜 Fal)
    (hcost : Bl ≤ 𝔤) (M D : ℕ)
    (hE : E ≤ 𝔖 +
      𝔍 +
      𝔉) :
    let CG := 𝔏
    1 + 𝔨 Bl + 𝔑 * E ≤ CG * (𝔙 + 𝔊 +
      𝔅 +
      𝔄) := by
  let CG := 𝔏
  change _ ≤ CG * _
  have hCG : 1 ≤ CG := rawCostConstant_ge_one _ _ _ _ _ _
  have hC6G : C6 ≤ CG := 𝔈 1
  have hchG : ch ≤ CG := 𝔈 2
  have hBG : 1 + 𝔨 CB ≤ CG := 𝔈 3
  have hpG : 𝔇 * 𝔎 ≤ CG := 𝔈 4
  have haG : 𝔡 ≤ CG := 𝔈 5
  have htG : 𝔘 * 𝔐 ≤ CG :=
    𝔈 6
  have hB0 : 𝔜 B := by linarith only [hB]
  have hmu0 : 𝔜 mu := by rw [hmu]; positivity
  have hb2 : 𝔨 Bl ≤ 𝔨 CB * 𝔙 := by
    calc
      _ ≤ 𝔨 𝔤 := (sq_le_sq₀ hBl $ mul_nonneg hCB hB0 ).mpr hcost
      𝘿 := mul_pow _ _ _
  have hb1 : 1 ≤ 𝔙 := by nlinarith only [hB]
  have hbase : 1 + 𝔨 Bl ≤ CG * 𝔙 := by
    have hh := mul_le_mul_of_nonneg_right hBG $ sq_nonneg B
    nlinarith only [hh, hb1, hb2]
  have hp : 𝔑 * 𝔖 ≤
      CG * 𝔊 := by
    calc
      _ = 𝔇 * (𝔎 * 𝔊) := by
        rw [show 𝔖 =
          𝔇 * 𝔫 Fdef by ring, mul_left_comm,
          inverse_volume_pair_energy hv hmu heta]
      𝖦 := by
        convert mul_le_mul_of_nonneg_right hpG
          (by positivity : 𝔜 𝔊) using 1 <;> ring
  have ha : 𝔑 * 𝔍 ≤
      CG * 𝔅 := by
    have hr := 𝔥 hC6 hC6G hFal M
    have hh := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 3 * C6)
    apply le_trans $ by convert hh using 1 <;> ring
    convert mul_le_mul_of_nonneg_right haG
      (by positivity : 𝔜 𝔅) using 1 <;> ring
  have ht : 𝔑 * 𝔉 ≤
      CG * 𝔄 := by
    have hr := 𝔥 hch hchG
      (show 0 ≤ 𝙠 by norm_num) D
    have hh := mul_le_mul_of_nonneg_left hr
      (by positivity : 0 ≤ Real.exp ch * 𝔗)
    have hab := activity_plus_one_bound hB hCB hBl hcost
    have hk := mul_le_mul_of_nonneg_right hab
      (by positivity : 0 ≤ 𝔘 * n * h4s *
        𝔚 ^ D / 𝔛)
    apply le_trans $ by convert hh using 1 <;> ring
    apply le_trans $ by convert hk using 1 <;> ring
    convert mul_le_mul_of_nonneg_right htG
      (by positivity : 𝔜 𝔄) using 1 <;> ring
  have hscaled := mul_le_mul_of_nonneg_left hE $ inv_nonneg.mpr hv.le
  nlinarith only [hscaled, hbase, hp, ha, ht]
