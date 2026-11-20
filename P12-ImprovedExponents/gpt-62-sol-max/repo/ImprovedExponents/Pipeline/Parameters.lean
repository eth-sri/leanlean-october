module

public import ImprovedExponents.Total.Lop
public import ThreeSumApsp.Programs.Sec3.Corollary15_16.CountAndDetect
public import ImprovedExponents.Pipeline.PrunedClaim
public import ImprovedExponents.Total.Explicit
public import ImprovedExponents.Optimum.NumLog
public import ImprovedExponents.Pipeline.Claims

@[expose] public section

namespace ImprovedExponents

open ThreeSumApsp Light Light.Sec3 Real Set ParamRoutines

/-- A single rational parameter choice suffices for all four bounds. The pruned encoder uses
`c = 22`, `θ = 29009/250000`; the host uses `D = ⌊n^0.05708⌋`, `g = ⌈D^0.036704⌉`. -/
theorem explicitFrom22 (M : DetTimeModel) (hM : M.lopDetect = lightModel.lopDetect)
    (host : MidHostRat M) : ExplicitFrom M 0.002095 1 := by
  have hX : (0.076207 : ℝ) ≤ gammaX 22 0.116036 := le_gammaX 4
  have hQ : qOf (0.116036 : ℝ) ≤ 0.44284475 := qOf_le (-3)
  have hq : 0 ≤ qOf (0.116036 : ℝ) := qOf_nonneg _ (by norm_num) (by norm_num)
  have hA : basePruned 22 ≤ 25.10485 := basePruned_le 4
  have hL := logFour_mem.1
  unfold logTwoLo at hL
  have hε : (0.054986 : ℝ) < RcP 22 0.076206 := by
    have hA0 : 0 < basePruned (22 : ℝ) := basePruned_pos (by norm_num)
    rw [RcP, thinR, lt_div_iff₀ (by linarith : 0 < basePruned 22 + 0.076206 * log 4)]
    linarith
  have ht : ThinClaim lightModel 0.054986 0.076206 (qOf 0.116036) := by
    rw [← show (29009 : ℝ) / 250000 = 0.116036 by norm_num]
    let G : Light.Sec4.RatParams := ⟨22, 1, 29009, 250000, 1, by decide, by decide, by decide,
      by decide, by decide, by decide⟩
    apply thinClaimP_gammaX G (r := 909) (s := 50) <;>
      norm_num [G, Light.Sec4.RatParams.realC, Light.Sec4.RatParams.realTheta,
        show (29009 : ℝ) / 250000 = 0.116036 by norm_num] <;> linarith
  obtain ⟨C, T, hT, hb⟩ := lopClaim_of_thinClaim lightModel (by norm_num) hq (by norm_num) ht
    claim_lopCountFromThinProduct claim_lopDetectFromCount
  refine explicitFrom_mid M (d := 1427 / 25000) (η := 1147 / 31250) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 0.076206) hq (by norm_num) (by norm_num)
    (fun _ => rfl) (fun _ => rfl)
    (host 1427 25000 1147 31250 (by decide) (by decide) (by decide) (by decide))
    ⟨C, T, hM ▸ hT, hb⟩ (by norm_num) ?_
  rw [min_eq_left (show (0.076206 : ℝ) * (1 - 1147 / 31250) ≤
      1 / 2 - qOf 0.116036 * (1 - 1147 / 31250) by linarith)]
  norm_num

end ImprovedExponents
