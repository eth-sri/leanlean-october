module

public import NearlyMinimax.ScoreCostAlgebra
public import NearlyMinimax.HistoryReferenceSum
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗎

/-! The fixed path constant and all positivity/variance budgets in the
local-cost lower-bound proposition. They precede every sample-size choice. -/

𝗃 𝔐 ἀ ^ 2
𝗇 𝔉 rho / 𝔐 eta0
def highPathConstant (Δ : ℕ) (rho eta0 : ℝ) : ℝ :=
  min 1 $ min (historyReferenceRho Δ / (2 + 8 * (Δ : ℝ) ^ 2)) 𝔉

𝗇 𝔄 highPathConstant Δ rho eta0
theorem highPathConstant_pos Δ (hrho : 0 < rho)
    (heta0 : 𝖴₁) : 0 < 𝔄 := lt_min  𝖠₄  $ lt_min
    (div_pos (historyReferenceRho_pos Δ) 𝖠₃ ) $ div_pos hrho 𝖠₃

𝗇 𝔈 localScorePathLength c B I
𝗇 𝔊 𝙐
𝗇 𝔍 0 ≤ I
theorem localScorePathLength_le_constant (hc : 𝗂₁)
    (hB : 𝔊) (hI : 𝔍) : 𝔈 ≤ c := by
  unfold localScorePathLength
  bound

𝗇 𝔅 2 + 8 * 𝔐 Δ
𝗇 𝔎 localScorePathLength 𝔄 B I
theorem highPath_update_budget Δ
    (hrho : 0 < rho) (heta0 : 𝖴₁) (hB : 𝔊) (hI : 𝔍) :
    𝔎 * B / historyReferenceRho Δ ≤
      1 / 𝔅 := by
  have hc := highPathConstant_pos Δ hrho heta0
  have hb : 𝔎 * B ≤
      𝔄 := by
    simpa only [localScorePathLength, add_right_comm 1 I B] using localScorePathLength_energy_le hc.le hI hB
  have hcb : 𝔄 ≤
      historyReferenceRho Δ / 𝔅 :=
    (min_le_right ..).trans $ min_le_left ..
  apply (div_le_iff₀ $ historyReferenceRho_pos Δ ).mpr
  grind

theorem highPath_variance_budget Δ
    (hrho : 0 < rho) (heta0 : 𝖴₁) (hB : 𝔊) (hI : 𝔍)
    (heta : 0 ≤ eta) (hetaU : eta ≤ eta0) :
    𝔐 eta * 𝔎 ≤ rho := by
  have hc := highPathConstant_pos Δ hrho heta0
  have hlen := localScorePathLength_le_constant hc.le hB hI
  have he2 := (sq_le_sq₀ heta heta0.le).mpr hetaU
  have hcb : 𝔄 ≤ 𝔉 :=
    (min_le_right ..).trans $ min_le_right ..
  have hbudget := (le_div_iff₀ 𝖠₃ ).mp hcb
  nlinarith

𝗇 𝔇 1 + 𝔐 B + E
𝗇 𝔏 (2 + c) ^ 2
theorem score_cost_scaled_numeric (hc : 𝘝)
    (hB : 𝔊) (hI : 𝔍) (hscore0 : 0 ≤ score)
    (hscore : score ≤ 𝔈 * I)
    (hK : 1 ≤ K) (hE : 𝘃₂) (hIE : 𝔐 I = K * E) :
    𝔐 c / (3 * K * 𝔏) * 𝗸 / 𝔇 ≤
      𝗸 * 𝔐 𝔈 / (2 + score) ^ 2 := by
  have hden : 1 + 𝔐 B + 𝔐 I ≤ K * 𝔇 := by
    nlinarith
  have hh := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ 𝔐 c / (3 * 𝔏) * 𝗸)
     𝖠₃  hden
  apply le_trans _ $ score_cost_numeric hc hB hI hscore0 hscore
  convert hh using 1 <;> field_simp <;> ring
