/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.LightModel
public import ThreeSumApsp.Programs.Sec3.Theorem21b.Apsp.Host

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp.Spec

noncomputable def apBound (T : ℕ → ℝ → ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  ((Nat.clog 2 n : ℝ) + 1) * (T n (16 * ((n : ℝ) ^ 2 * u)) + 200 * (n : ℝ) ^ 2)

/-- APSP needs logarithmically many products at polynomially enlarged entry bounds. -/
theorem solvedIn_ap_of_mp {T : ℕ → ℝ → ℝ} (h : SolvedIn mpTask T) : SolvedIn apTask (apBound T) := by
  refine isHost_ap.solvedIn h fun Tn hTn n U u hn hU hu => ?_
  have h₁ : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hn)
  have hB : 0 < apspBound n U := by positivity
  have hT := hTn n (apspBound n U) (16 * ((n : ℝ) ^ 2 * u)) hn hB (by
    simp only [apspBound, sentinel]
    push_cast
    nlinarith)
  simp only [apTime, apBound]
  push_cast
  nlinarith

end Light.Sec3
