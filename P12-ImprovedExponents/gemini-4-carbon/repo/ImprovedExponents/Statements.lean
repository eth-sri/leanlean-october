module

public import ThreeSumApsp.Statements.Exponents
public import ImprovedExponents.PrunedProgram.Wrapper
public import ImprovedExponents.AllEdges.Pairs.TimeBound
public import ImprovedExponents.AllEdges.Host.ClaimAE

@[expose] public section

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.WordRam Light Light.Sec4 Real

theorem thinClaimP_gammaX {a b p q : ℕ} (hb : 1 ≤ b) (hq : 1 ≤ q) (hc : 10 * b < a) (hp : 1 ≤ p)
    (hθ : 10 * p < 9 * q) (hrs : basePruned ((a : ℝ) / b) < 18 * log 4) {γ ε : ℝ}
    (hγ0 : 0 < γ) (hε0 : 0 < ε) (hγ : γ < gammaX ((a : ℝ) / b) ((p : ℝ) / q))
    (hε : ε < RcP ((a : ℝ) / b) γ) (hεrs : ε ≤ 1 / 18) :
    ThinClaim lightModel ε γ (qOf ((p : ℝ) / q)) := by
  obtain ⟨m₁, h₁⟩ := offlineWithinP cShared30 hb hq hc hp hθ hγ0 hε0 hγ hε
  obtain ⟨m₂, h₂⟩ := exists_fits18 hb hq hc hp hθ hrs
  have hm₀ : 1 ≤ max (max m₁ m₂) 1 := le_max_right _ _
  exact thinClaim_programP (h₂ _ hm₀ ((le_max_right _ _).trans (le_max_left _ _))) hεrs
    (h₁ _ hm₀ ((le_max_left _ _).trans (le_max_left _ _)))

section
set_option exponentiation.threshold 2000

private lemma log_four_eq : log (4 : ℝ) = 2 * log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; push_cast; ring

private lemma log_nine_eq : log (9 : ℝ) = 2 * log 3 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, log_pow]; push_cast; ring

private lemma basePruned_109_5_lt : basePruned ((109 : ℝ) / 5) < 359 / 10 * log 2 := by
  have hlog := log_lt_log (by positivity)
    (by norm_num : (109 : ℝ) ^ 109 * 3 ^ 208 < 104 ^ 104 * 5 ^ 5 * 2 ^ 359)
  repeat rw [log_mul (by positivity) (by positivity)] at hlog
  simp only [log_pow] at hlog
  unfold basePruned entropy
  rw [show (1 : ℝ) / ((109 : ℝ) / 5) = 5 / 109 by norm_num,
    show (1 : ℝ) - 5 / 109 = 104 / 109 by norm_num,
    log_div (by norm_num) (by norm_num), log_div (by norm_num) (by norm_num)]
  push_cast at hlog ⊢; linarith

private lemma gammaX_109_5_gt : (0.07545 : ℝ) < gammaX ((109 : ℝ) / 5) ((23 : ℝ) / 198) := by
  have hl1 := log_lt_log (by positivity) (by norm_num : (2 : ℝ) ^ 2 * 20592 ^ 249 < 20707 ^ 249)
  have hl2 := log_lt_log (by positivity)
    (by norm_num : (990 : ℝ) ^ 115 * 198 ^ 875 * 3 ^ 230 < 20707 ^ 115 * 175 ^ 875 * 2 ^ 16)
  rw [log_mul (by positivity) (by positivity)] at hl1
  repeat rw [log_mul (by positivity) (by positivity)] at hl2
  simp only [log_pow] at hl1 hl2
  rw [show (20592 : ℝ) = 104 * 198 by norm_num, log_mul (by norm_num) (by norm_num)] at hl1
  have h990 : log (990 : ℝ) = log 5 + log 198 := by
    rw [← log_mul (by norm_num) (by norm_num)]; norm_num
  unfold gammaX g2 negMulLog
  rw [show (109 : ℝ) / 5 - 1 + (23 : ℝ) / 198 = 20707 / 990 by norm_num,
    show (109 : ℝ) / 5 - 1 = 104 / 5 by norm_num,
    show (1 : ℝ) - (23 : ℝ) / 198 = 175 / 198 by norm_num, log_four_eq, log_nine_eq,
    log_div (by norm_num) (by norm_num), log_div (by norm_num) (by norm_num),
    log_div (by norm_num) (by norm_num)]
  rw [h990] at hl2 ⊢
  have : 0 < log (2 : ℝ) := log_pos (by norm_num)
  rw [lt_div_iff₀ (by positivity)]
  push_cast at hl1 hl2 ⊢; linarith

private lemma qOf_23_198_lt : qOf ((23 : ℝ) / 198) < 1229 / 2772 := by
  have hl := log_lt_log (by positivity)
    (by norm_num : (198 : ℝ) ^ 1386 * 3 ^ 322 < 23 ^ 161 * 175 ^ 1225 * 2 ^ 1229)
  repeat rw [log_mul (by positivity) (by positivity)] at hl
  simp only [log_pow] at hl
  unfold qOf entropy
  rw [show (1 : ℝ) - (23 : ℝ) / 198 = 175 / 198 by norm_num, log_four_eq, log_nine_eq,
    log_div (by norm_num) (by norm_num), log_div (by norm_num) (by norm_num)]
  have : 0 < log (2 : ℝ) := log_pos (by norm_num)
  rw [div_lt_iff₀ (by positivity)]
  push_cast at hl ⊢; linarith

private theorem explicit_ae_main : ExplicitFrom AllEdges.lightModelAE 0.002091 1 := by
  have h4 := log_four_eq
  have hb := basePruned_109_5_lt
  have hb0 : 0 < basePruned ((109 : ℝ) / 5) := basePruned_pos (by norm_num)
  have hR : (0.055477 : ℝ) < RcP ((109 : ℝ) / 5) 0.07545 := by
    unfold RcP thinR; rw [h4, lt_div_iff₀ (by positivity)]; linarith
  have hthin := thinClaimP_gammaX (a := 109) (b := 5) (p := 23) (q := 198)
    (γ := 0.07545) (ε := 0.055477) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by grind) (by norm_num) (by norm_num) gammaX_109_5_gt hR (by norm_num)
  have hql := qOf_23_198_lt
  exact explicitFrom_mid AllEdges.lightModelAE (d := (1439 : ℝ) / 25000) (η := (2 : ℝ) / 55)
    (s := 0.0020915) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (qOf_nonneg _ (by norm_num) (by norm_num)) (by norm_num) (fun _ => rfl) (fun _ => rfl)
    (AllEdges.midHostRat_ae 1439 25000 2 55 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (lopClaim_of_thinClaim_light hthin (by norm_num) (qOf_nonneg _ (by norm_num) (by norm_num))
      (by norm_num) rfl)
    (by norm_num) (by norm_num) (by norm_num) (by linarith) (by norm_num)

end

private theorem allSolved_main : AllSolved 0.002091 :=
  allSolved_of_explicitFrom AllEdges.claim_bruteForce_ae (by norm_num) (by norm_num)
    (AllEdges.explicitFrom_light_of_ae (by norm_num) explicit_ae_main)

theorem threeSum_pruned : EndStatement.ThreeSum.SolvedInTime 1.99896 :=
  SolvedInTime.endStatement (allSolved_main.threeSum _ (by norm_num)) rfl (by norm_num)

theorem exactTriangle_pruned : EndStatement.ExactTriangle.SolvedInTime 2.99791 :=
  SolvedInTime.endStatement (allSolved_main.exactTriangle _ (by norm_num)) rfl (by norm_num)

private theorem minPlusSolved_main : AllEdges.MinPlusSolved 0.002091 :=
  AllEdges.minPlusSolved_of_explicitFrom AllEdges.CA_nonneg AllEdges.pairsFromAllEdges
    (by norm_num) explicit_ae_main

theorem minPlus_allEdges_pruned : EndStatement.MinPlusProduct.SolvedInTime 2.99791 :=
  SolvedInTime.endStatement (minPlusSolved_main.minPlus _ (by norm_num)) rfl (by norm_num)

theorem apsp_allEdges_pruned : EndStatement.APSP.SolvedInTime 2.99791 :=
  SolvedInTime.endStatement (minPlusSolved_main.apsp _ (by norm_num)) rfl (by norm_num)

end ImprovedExponents
