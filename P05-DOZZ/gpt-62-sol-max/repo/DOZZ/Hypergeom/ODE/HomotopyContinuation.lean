/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.HomotopyGridLifts
public import DOZZ.Hypergeom.ODE.PathContinuation

/-! Continuation endpoints agree along fixed-endpoint homotopies in a regular domain. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Two finite-chain continuations from the same initial value have the same endpoint when their
paths are fixed-endpoint homotopic through an open regular domain. -/
theorem homotopy_path_continuation_endpoint_eq
    {Γ : ℝ × ℝ → ℂ} (hΓ : ContinuousOn Γ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (U : Set ℂ) (hU : IsOpen U) (H : ℂ → E →L[ℂ] E)
    (hH : DifferentiableOn ℂ H U)
    (himage : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, Γ p ∈ U)
    (z₀ z₁ : ℂ)
    (hleft : ∀ s ∈ Icc (0 : ℝ) 1, Γ (0, s) = z₀)
    (hright : ∀ s ∈ Icc (0 : ℝ) 1, Γ (1, s) = z₁)
    (y : E)
    (A : PathContinuationLift (fun t => Γ (t, 0)) H y)
    (B : PathContinuationLift (fun t => Γ (t, 1)) H y) :
    A.value 1 = B.value 1 := by
  let G := homotopyPicardGridOf hΓ U hU H hH himage z₀ z₁ hleft hright y
  have hN : (G.N : ℝ) ≠ 0 := by exact_mod_cast G.N_pos.ne'
  obtain ⟨L₀, hL⟩ := exists_homotopyGrid_rowLift G hΓ 0 (Nat.zero_le _)
  obtain ⟨R₀, hR⟩ := exists_homotopyGrid_rowLift G hΓ G.N le_rfl
  let L : PathContinuationLift (fun t => Γ (t, 0)) H y :=
    path_continuation_lift_congr L₀ (fun t _ => by simp)
  let R : PathContinuationLift (fun t => Γ (t, 1)) H y :=
    path_continuation_lift_congr R₀ (fun t _ => by simp [div_self hN])
  have h₁ := path_continuation_lifts_unique (homotopy_row_continuous hΓ (by norm_num)) H y A L 1 (by norm_num)
  have h₂ := path_continuation_lifts_unique (homotopy_row_continuous hΓ (by norm_num)) H y B R 1 (by norm_num)
  exact (h₁.trans hL).trans (G.transfer_eq.trans (hR.symm.trans h₂.symm))

end DOZZ.Proofs
