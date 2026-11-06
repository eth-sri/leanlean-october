/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Programs.LightModel
import ThreeSumApsp.Programs.Sec3.Theorem21b.NegativeTriangle.Host
import ThreeSumApsp.Util.Asymptotics.LogU

/-!
# The claim [VW13, Theorem 3.3] in the light language

The arithmetic that turns the time function of the host (`ntTime`, `isHost_nt`) into the bound
C · T(s, 6U) · log U of the claim. The host's own work, O(n² log U), is at most the time of the
solver, because a good time is at least n².
-/


namespace Light.Sec3

open ThreeSumApsp

/-- The number of levels is O(log U). -/
theorem ntLevels_le {U : ℕ} (hU : 1 ≤ U) {u : ℝ} (hu : (U : ℝ) ≤ u) :
    (ntLevels U : ℝ) ≤ 10 * logU u := by
  have hshift : Nat.log 2 (6 * U) ≤ Nat.log 2 U + 3 := by
    calc Nat.log 2 _ ≤ Nat.log 2 (U * 2 * 2 * 2) := Nat.log_mono_right (by omega)
      _ = Nat.log 2 U + 3 := by
        rw [Nat.log_mul_base (by norm_num) (by omega), Nat.log_mul_base (by norm_num) (by omega),
          Nat.log_mul_base (by norm_num) (by omega)]
  have hfloor := Real.natLog_le_logb U 2
  have hU' : (1 : ℝ) ≤ U := by simp_all
  have hmono :=
    (Real.log_le_log (by linarith) hu).trans log_le_logU
  have hhalf := Real.one_half_lt_log_two
  have hbase : Real.logb (2 : ℕ) U ≤ 2 * Real.log U := by
    have hlog0 := Real.log_nonneg hU'
    rw [Real.logb, Nat.cast_ofNat, div_le_iff₀ (by linarith)]
    nlinarith
  have htwo := log_two_le_logU u
  have hlevels : ntLevels U ≤ (Nat.log 2 U : ℝ) + 4 := by
    exact_mod_cast (by omega : Nat.log 2 _ + 1 ≤ Nat.log 2 U + 4)
  -- `log₂ U + 4 ≤ 2 log U + 8 log 2 ≤ 10 log u`
  linarith

/-- [VW13, Theorem 3.3] for programs of the light language: Negative Triangle from Exact Triangle,
with c = 6. -/
theorem claim_VW13_Theorem_3_3 : Claim.VW13_Theorem_3_3 lightModel := by
  refine ⟨6, 4880, by norm_num, by norm_num, fun T hT hs =>
    isHost_nt.solvedIn hs fun Tn hTn n U u hn hU hu => ?_⟩
  have hτ : Tn n (6 * U) ≤ T n (6 * u) :=
    by grind
  have hg := hT.1 n (6 * u) hn
  have hl := logU_pos (6 * u)
  have hn' : (1 : ℝ) ≤ n := by simp_all
  have hN1 : 1 ≤ (n : ℝ) ^ 2 := by nlinarith
  have hN : n ^ 2 ≤ T n (6 * u) := by nlinarith
  have hL := ntLevels_le hU hu
  have hL1 : (1 : ℝ) ≤ ntLevels U := by
    unfold ntLevels
    simp
  generalize T n _ = τ at *
  unfold ntTime
  push_cast
  generalize ntLevels U = L at *
  generalize Tn n _ = t at *
  have hτ0 : 0 ≤ τ := by linarith
  calc 120 * (n * n) + 120 + L * (154 * (n * n) + 92 + 2 * t)
      ≤ 240 * τ + L * 248 * τ := by
        nlinarith
    _ ≤ 488 * (L * τ) := by nlinarith
    _ ≤ 488 * (10 * logU u * τ) := by
        simp_all [mul_le_mul_of_nonneg_right]
    _ = 4880 * (τ * logU u) := by ring
