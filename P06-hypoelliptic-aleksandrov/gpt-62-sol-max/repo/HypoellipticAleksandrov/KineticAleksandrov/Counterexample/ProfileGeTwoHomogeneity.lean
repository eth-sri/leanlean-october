module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.GeometryHomogeneity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileGeTwoRegularity
import Mathlib.Tactic.Linarith

/-! # Homogeneity of the higher-dimensional profile jets -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Set Filter

/-- Positive kinetic dilation preserves nonzero points. -/
theorem dilate_ne_zero {d : ℕ} (r : ℝ) (hr : 0 < r) (q : XV d) (hq : q ≠ 0) :
    dilate r q ≠ 0 := by
  intro hz
  have he := congrArg (dilate r⁻¹) hz
  rw [dilate_mul, inv_mul_cancel₀ hr.ne', dilate_one, dilate_zero] at he
  exact hq he

section
variable {d : ℕ} (H : XV d → ℝ)

/-- The smooth homogeneous profile is differentiable at every nonzero point. -/
theorem differentiableAt_profile_off_origin
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d))) (q : XV d) (hq : q ≠ 0) :
    DifferentiableAt ℝ H q :=
  (hs.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hq))).differentiableAt
    (by simp)

/-- Differentiating kinetic homogeneity twice gives the Hessian degree alpha minus two. -/
theorem homogeneous_dvv_off_origin (alpha r : ℝ)
    (hr : 0 < r) (hhom : ∀ q, H (dilate r q) = Real.rpow r alpha * H q)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d)))
    (q : XV d) (hq : q ≠ 0) (i k : Fin d) :
    dvv H (dilate r q) i k = Real.rpow r (alpha - 2) * dvv H q i k := by
  have hg : DifferentiableAt ℝ (fun z => dv H z k) q :=
    (contDiffAt_dv_off_origin H hs q hq k).differentiableAt (by simp)
  have hgr : DifferentiableAt ℝ (fun z => dv H z k) (dilate r q) :=
    (contDiffAt_dv_off_origin H hs _ (dilate_ne_zero r hr q hq) k).differentiableAt (by simp)
  have hloc : (fun z => dv H (dilate r z) k) =ᶠ[nhds q]
      (fun z => Real.rpow r (alpha - 1) * dv H z k) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hq] with z hz
    exact homogeneous_dv_identity H alpha r hr hhom z
      (differentiableAt_profile_off_origin H hs z hz)
      (differentiableAt_profile_off_origin H hs _ (dilate_ne_zero r hr z hz)) k
  simpa only [dvv, show alpha - 1 - 1 = alpha - 2 by ring] using
    homogeneous_velocity_direction (Pi.single i 1) hr hloc hg hgr

end

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
