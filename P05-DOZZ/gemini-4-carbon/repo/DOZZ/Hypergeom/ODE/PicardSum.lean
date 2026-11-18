/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.PicardBounds
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! The normally convergent local Picard series and its differential equation. -/

@[expose] public section

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The `n`th holomorphic Picard summand on the disk. -/
noncomputable def holomorphicPicardTerm (c : ℂ) (r : ℝ)
    (H : ℂ → E →L[ℂ] E) (hH : DifferentiableOn ℂ H (Metric.ball c r)) (y : E)
    (n : ℕ) : ℂ → E :=
  (holomorphicPicardIterates c r H hH y n).1

/-- The sum of the holomorphic Picard summands. -/
noncomputable def holomorphicPicardSolution (c : ℂ) (r : ℝ)
    (H : ℂ → E →L[ℂ] E) (hH : DifferentiableOn ℂ H (Metric.ball c r)) (y : E) : ℂ → E :=
  fun z => ∑' n, holomorphicPicardTerm c r H hH y n z




theorem holomorphicPicardSolution_apply_center (c : ℂ) (r : ℝ)
    (H : ℂ → E →L[ℂ] E) (hH : DifferentiableOn ℂ H (Metric.ball c r)) (y : E) :
    holomorphicPicardSolution c r H hH y c = y := by
  have hzero : ∀ n ≠ 0, holomorphicPicardTerm c r H hH y n c = 0 := by
    intro n hn
    cases n with
    | zero => exact False.elim (hn rfl)
    | succ n =>
        simpa [holomorphicPicardTerm] using holomorphicPicardIterates_apply_center c r H hH y (n + 1)
  rw [holomorphicPicardSolution, tsum_eq_single 0 hzero]
  rfl

theorem holomorphicPicardSolution_hasDerivAt (c : ℂ) (r M : ℝ)
    (H : ℂ → E →L[ℂ] E) (hH : DifferentiableOn ℂ H (Metric.ball c r)) (y : E)
    (hM : 0 ≤ M) (hHbound : ∀ z ∈ Metric.ball c r, ‖H z‖ ≤ M)
    {z : ℂ} (hz : z ∈ Metric.ball c r) :
    HasDerivAt (holomorphicPicardSolution c r H hH y)
      (H z (holomorphicPicardSolution c r H hH y z)) z := by
  have holomorphicPicardTerm_norm_le : ∀ n : ℕ, ∀ z ∈ Metric.ball c r,
        ‖holomorphicPicardTerm c r H hH y n z‖ ≤
          ‖y‖ * (M * max r 0) ^ n / (n.factorial : ℝ) := by
    intro n z hz
    have hdist0 : ‖z - c‖ ≤ r := by
      simpa [dist_eq_norm] using (Metric.mem_ball.mp hz).le
    have := hdist0.trans (le_max_left r 0)
    refine (holomorphicPicardIterates_norm_le c r M H hH y hM hHbound n z hz).trans (?_)
    gcongr
  have holomorphicPicardTerm_differentiableOn (n : ℕ) := 
    (holomorphicPicardIterates c r H hH y n).2
  have holomorphicPicardSolution_differentiableOn : DifferentiableOn ℂ (holomorphicPicardSolution c r H hH y) (Metric.ball c r) := by
    let R := max r 0
    let u : ℕ → ℝ := fun n => ‖y‖ * (M * R) ^ n / (n.factorial : ℝ)
    have hu : Summable u := by
      dsimp [u]
      simpa [mul_div_assoc] using
        (Real.summable_pow_div_factorial (M * R)).mul_left ‖y‖
    have hbound : ∀ n z, z ∈ Metric.ball c r →
        ‖holomorphicPicardTerm c r H hH y n z‖ ≤ u n := by
      intro n z hz
      simpa [u, R] using holomorphicPicardTerm_norm_le n z hz
    change DifferentiableOn ℂ (fun z => ∑' n, holomorphicPicardTerm c r H hH y n z)
      (Metric.ball c r)
    exact Complex.differentiableOn_tsum_of_summable_norm hu
      (holomorphicPicardTerm_differentiableOn) Metric.isOpen_ball hbound
  let R := max r 0
  let u : ℕ → ℝ := fun n => ‖y‖ * (M * R) ^ n / (n.factorial : ℝ)
  have hu : Summable u := by
    dsimp [u]
    simpa [mul_div_assoc] using
      (Real.summable_pow_div_factorial (M * R)).mul_left ‖y‖
  have hbound : ∀ n w, w ∈ Metric.ball c r →
      ‖holomorphicPicardTerm c r H hH y n w‖ ≤ u n := by assumption
  have hterms : ∀ n, DifferentiableOn ℂ (holomorphicPicardTerm c r H hH y n)
      (Metric.ball c r) := holomorphicPicardTerm_differentiableOn
  have hderivSum := Complex.hasSum_deriv_of_summable_norm hu hterms
    Metric.isOpen_ball hbound hz
  have hderivZero : deriv (holomorphicPicardTerm c r H hH y 0) z = 0 := by
    simp [holomorphicPicardTerm, holomorphicPicardIterates]
  have hderivSucc (n : ℕ) :
      deriv (holomorphicPicardTerm c r H hH y (n + 1)) z =
        H z (holomorphicPicardTerm c r H hH y n z) := by
    simpa [holomorphicPicardTerm] using (holomorphicPicardIterates_hasDerivAt_succ c r H hH y n hz).deriv
  let g : ℕ → E := fun n => deriv (holomorphicPicardTerm c r H hH y n) z
  have hshift : (∑' n, g (n + 1)) = ∑' n, g n := by
    simpa [g, hderivZero] using hderivSum.summable.sum_add_tsum_nat_add 1
  have htermsSummable : Summable (fun n => holomorphicPicardTerm c r H hH y n z) :=
    hu.of_norm_bounded fun n => hbound n z hz
  have hderivEq :
      deriv (holomorphicPicardSolution c r H hH y) z =
        H z (holomorphicPicardSolution c r H hH y z) := by
    calc
      deriv (holomorphicPicardSolution c r H hH y) z = ∑' n, g n := by
        change deriv (fun w => ∑' n, holomorphicPicardTerm c r H hH y n w) z = _
        exact hderivSum.tsum_eq.symm
      _ = ∑' n, g (n + 1) := hshift.symm
      _ = ∑' n, H z (holomorphicPicardTerm c r H hH y n z) := by
        apply tsum_congr
        exact hderivSucc
      _ = H z (holomorphicPicardSolution c r H hH y z) := by
        change ∑' n, H z (holomorphicPicardTerm c r H hH y n z) =
          H z (∑' n, holomorphicPicardTerm c r H hH y n z)
        exact (H z).map_tsum htermsSummable |>.symm
  have hAt : DifferentiableAt ℂ (holomorphicPicardSolution c r H hH y) z :=
    ((holomorphicPicardSolution_differentiableOn) z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
  have hresult := hAt.hasDerivAt
  rw [hderivEq] at hresult
  exact hresult


end DOZZ.Proofs
