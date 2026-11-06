module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.GeometryHomogeneity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileGeTwoRegularity
import Mathlib.Tactic.Linarith

/-! # Homogeneity of the higher-dimensional profile jets -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Set Filter

/- Positive kinetic dilation preserves nonzero points. -/
theorem dilate_ne_zero {d } (r : ℝ) (hr : 0 < r) (q : XV d) (hq : q ≠ 0) :
    dilate r q ≠ 0 := by
  intro hz
  have he := congrArg (dilate r⁻¹) hz
  rw [dilate_mul, inv_mul_cancel₀ hr.ne', dilate_one] at he
  simp [dilate] at he
  exact hq he

/- The smooth homogeneous profile is differentiable at every nonzero point. -/
theorem differentiableAt_profile_off_origin {d } (H : XV d → ℝ)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d))) (q ) (hq : q ≠ 0) :
    DifferentiableAt ℝ H q :=
  (hs.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hq))).differentiableAt
    (by simp)

/- Differentiating kinetic homogeneity twice gives the Hessian degree alpha minus two. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
