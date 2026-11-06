module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Dual

/-! The continuous nonconjugate L² pairing, used to express weak-form
linearity without repeating almost-everywhere representative calculations. -/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {φ : α → ℂ}

lemma integral_norm_sq_eq_of  (u : Lp ℂ 2 μ) :
    ∫ w, ‖(u : α → ℂ) w‖ ^ 2 ∂μ = ‖u‖ ^ 2 := by
  have h := congrArg RCLike.re (L2.inner_def (𝕜 := ℂ) u u)
  rw [inner_self_eq_norm_sq, ← integral_re (L2.integrable_inner u u)] at h
  simp_rw [inner_self_eq_norm_sq] at h
  exact h.symm


def lpPair (hφ : MemLp φ 2 μ) : Lp ℂ 2 μ →L[ℂ] ℂ :=
  innerSL ℂ (hφ.star.toLp (star φ))

theorem lpPair_apply (hφ : MemLp φ 2 μ) (u : Lp ℂ 2 μ) :
    lpPair hφ u = ∫ z, u z * φ z ∂μ := by
  apply integral_congr_ae
  filter_upwards [hφ.star.coeFn_toLp] with z hz
  simp [hz]

end PolyaNeumann
