module

public import NearlyMinimax.ScoreCostAlgebra
public import NearlyMinimax.HistoryReferenceSum

@[expose] public section

/-! The fixed path constant and all positivity/variance budgets in the
local-cost lower-bound proposition. They precede every sample-size choice. -/
noncomputable section
namespace NearlyMinimax

variable (Δ : ℕ) {rho eta0 c B I eta : ℝ} (hrho : 0 < rho) (heta0 : 0 < eta0) {score K E : ℝ}
    (hB : 0 ≤ B) (hI : 0 ≤ I)

def highPathConstant (rho eta0 : ℝ) : ℝ :=
  min 1 (min (historyReferenceRho Δ / (2 + 8 * Δ ^ 2)) (rho / eta0 ^ 2))

include hrho heta0 in
theorem highPathConstant_pos : 0 < highPathConstant Δ rho eta0 := lt_min (by norm_num) (lt_min
    (div_pos (historyReferenceRho_pos Δ) (by positivity)) (div_pos hrho (by positivity)))

theorem localScorePathLength_le_constant (hc : 0 ≤ c)
    (hB : 0 ≤ B) (hI : 0 ≤ I) : localScorePathLength c B I ≤ c := by
  apply (div_le_iff₀ (by linarith only [hB, hI])).mpr
  bound [mul_le_mul_of_nonneg_left (by linarith only [hB, hI]) hc]

include hrho heta0 hB hI in
theorem highPath_update_budget :
    localScorePathLength (highPathConstant Δ rho eta0) B I * B / historyReferenceRho Δ ≤
      historyActivityRadius Δ := by
  have hc := highPathConstant_pos Δ hrho heta0
  have hb : localScorePathLength (highPathConstant Δ rho eta0) B I * B ≤
      highPathConstant Δ rho eta0 := by
    simpa only [localScorePathLength, add_right_comm 1 I B] using localScorePathLength_energy_le hc.le hI hB
  have hcb : highPathConstant Δ rho eta0 ≤
      historyReferenceRho Δ / (2 + 8 * Δ ^ 2) :=
    (min_le_right _ _).trans (min_le_left _ _)
  apply (div_le_iff₀ (historyReferenceRho_pos Δ)).mpr
  grind

include hrho heta0 hB hI in
theorem highPath_variance_budget
    (heta : 0 ≤ eta) (hetaU : eta ≤ eta0) :
    eta ^ 2 * localScorePathLength (highPathConstant Δ rho eta0) B I ≤ rho := by
  have hc := highPathConstant_pos Δ hrho heta0
  have hlen := localScorePathLength_le_constant hc.le hB hI
  have he2  := (sq_le_sq₀ heta heta0.le).mpr hetaU
  have hcb : highPathConstant Δ rho eta0 ≤ rho / eta0 ^ 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  nlinarith [(le_div_iff₀ (by positivity)).mp hcb]

theorem score_cost_scaled_numeric (hc : 0 < c)
    (hB : 0 ≤ B) (hI : 0 ≤ I) (hscore0 : 0 ≤ score)
    (hscore : score ≤ localScorePathLength c B I * I)
    (hK : 1 ≤ K) (hE : 0 ≤ E) (hIE : I ^ 2 = K * E) :
    c ^ 2 / (3 * K * (2 + c) ^ 2) * eta ^ 4 / (1 + B ^ 2 + E) ≤
      eta ^ 4 * (localScorePathLength c B I) ^ 2 / (2 + score) ^ 2 := by
  have hden : 1 + B ^ 2 + I ^ 2 ≤ K * (1 + B ^ 2 + E) := by
    nlinarith
  have hh := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ c ^ 2 / (3 * (2 + c) ^ 2) * eta ^ 4)
    (by positivity) hden
  apply le_trans _ (score_cost_numeric (η := eta) hc hB hI hscore0 hscore)
  convert hh using 1 <;> field_simp <;> ring

end NearlyMinimax
