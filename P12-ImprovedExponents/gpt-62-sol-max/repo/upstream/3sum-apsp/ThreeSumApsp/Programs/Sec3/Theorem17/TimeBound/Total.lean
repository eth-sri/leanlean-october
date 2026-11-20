/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Text
public import ThreeSumApsp.Programs.Sec3.Theorem17.TimeBound.Terms

/-! Running-time bounds for the operations shared by the triangle hosts. -/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-- The exponent that the host's bound on the false positives uses is at most `κ`. -/
private theorem kappaOf_le_of_hyp {θ : CostParams} (hθ : θ.Hyp) : kappaOf θ.n θ.U ≤ θ.κ := by
  rcases Nat.eq_zero_or_pos θ.U with hU | hU
  · simp [kappaOf, hU, hθ.hκ]
  · exact kappaOf_le ((by norm_num : 2 ≤ 16).trans hθ.sixteen_le_n) hU hθ.hκ hθ.hUn

/-- The host's bound on failed scans, taking account of the given weight exponent. -/
private theorem steps_falsePositiveBound :
    Steps (fun θ => falsePositiveBound θ.n θ.U θ.D) fun θ =>
      θ.κ * (θ.n : ℝ) ^ 3 * Real.log θ.n / Real.sqrt θ.D := by
  have hc : 0 ≤ Hashing.falsePositiveConst :=
    zero_le_one.trans Hashing.one_le_falsePositiveConst
  refine Dominated.of_le_const_mul hc fun θ hθ => (Nat.floor_le ?_).trans ?_
  · have := one_le_kappaOf θ.n θ.U
    positivity
  · gcongr
    exact kappaOf_le_of_hyp hθ

/-- Scanning a piece takes linear time in its length. The cost of the failed scans
is within the scan term of the budget. -/
theorem steps_failedScans (a b : ℕ) :
    Steps (fun θ => (a * pieceSizeNat θ.D θ.g + b) * falsePositiveBound θ.n θ.U θ.D) budget := by
  have hp : Steps (fun θ => pieceSizeNat θ.D θ.g) fun θ => Real.sqrt θ.D / θ.g := by
    refine Dominated.of_le_const_mul (C := 2) (by norm_num) fun θ hθ => ?_
    have hlt : (pieceSizeNat θ.D θ.g : ℝ) * θ.g < (Nat.sqrt θ.D : ℝ) + θ.g := by
      exact_mod_cast Nat.ceilDiv_mul_lt (a := Nat.sqrt θ.D) hθ.hg
    rw [← mul_div_assoc, le_div_iff₀ hθ.g_pos]
    linarith [Real.nat_sqrt_le_real_sqrt (a := θ.D), hθ.hgD]
  have hc : Steps (fun _ => b) fun θ => Real.sqrt θ.D / θ.g :=
    .const fun _ hθ => (one_le_div hθ.g_pos).2 hθ.hgD
  refine ((hp.const_mul.add hc).mul steps_falsePositiveBound).mono_right fun θ hθ =>
    (le_of_eq ?_).trans (termScans_le_budget θ)
  have hr := hθ.sqrt_pos
  have hg := hθ.g_pos
  unfold termScans
  field_simp

/-- The bound `4ng` on the number of instances is `O(ng)`. -/
theorem steps_instances : Steps (fun θ => 4 * θ.n * θ.g) fun θ => (θ.n : ℝ) * θ.g :=
  (Steps.const_mul (Dominated.refl _ _)).mul (Dominated.refl _ _)

/-- Writing the two matrices of an instance takes `O(nD)` steps. -/
private theorem steps_tWrites :
    StepsMon (fun θ => tWrites θ.n θ.D (pieceSizeNat θ.D θ.g)) 1 2 0 := by
  unfold tWrites
  growth [steps_tWrite]

/-- Writing the matrices of all instances, `O(ng) · O(nD)`, is within the third term of the bound.
-/
theorem steps_instances_mul_tWrites :
    Steps (fun θ => 4 * θ.n * θ.g * tWrites θ.n θ.D (pieceSizeNat θ.D θ.g)) budget :=
  (steps_instances.mul (steps_of_softO steps_tWrites)).mono_right fun θ hθ =>
    le_trans (le_of_eq (by
      simp only [termBuild, mon_eq, pow_zero, mul_one, pow_one, Real.sq_sqrt θ.D.cast_nonneg]
      ring)) (termBuild_le_budget hθ)

/-- Reading the answers of one instance takes `O(n²/√D)` steps, a constant number for each query
pair. -/
theorem steps_queryRead (a b : ℕ) :
    Steps (fun θ => a * queryCapNat θ.n θ.D + b) fun θ => (θ.n : ℝ) ^ 2 / Real.sqrt θ.D := by
  refine Steps.add (Steps.const_mul (Dominated.of_le fun θ hθ => cast_queryCapNat_le hθ))
    (.const fun θ hθ => ?_)
  rw [one_le_div hθ.sqrt_pos]
  exact hθ.sqrt_le_n.trans (le_self_pow₀ hθ.one_le_n two_ne_zero)

/-- The setup and preparation time before entering the loop over instances. -/
def hostPreparation (tD tG : ℕ → ℕ) (θ : CostParams) : ℕ :=
  hostSetup tD tG θ.n θ.D + chooseTime θ.n θ.U θ.D + tQueryCapNat θ.n θ.D
    + tCeilDiv (Nat.sqrt θ.D) θ.g + tCeilDiv θ.n (pieceSizeNat θ.D θ.g)
    + tBitLen θ.U + tDblTable (bitLen θ.U) + 3 * tResidues (θ.n * θ.n) (bitLen θ.U)
    + tClasses θ.n (Nat.sqrt θ.D) + tChunks (Nat.sqrt θ.D) (4 * θ.n * θ.g)

theorem steps_hostPreparation {tD tG : ℕ → ℕ} (hD : Steps (fun θ => tD θ.n) budget)
    (hG : Steps (fun θ => tG θ.D) budget) : Steps (hostPreparation tD tG) budget :=
  hD.add hG
  |>.add (by growth [steps_sqrt] : StepsMon _ 0 1 0).withinBuild
  |>.add (Scale.SoftO.const _).withinBuild
  |>.add steps_chooseTime
  |>.add steps_tQueryCapNat.withinBuild
  |>.add steps_tCeilDiv_piece.withinBuild
  |>.add steps_tCeilDiv_num.withinBuild
  |>.add steps_tBitLen.withinScans
  |>.add steps_tDblTable.withinScans
  |>.add ((Scale.SoftO.const _).mul steps_tResidues).withinScans
  |>.add steps_tClasses.withinBuild
  |>.add steps_tChunks.withinBuild

end Light.Sec3
