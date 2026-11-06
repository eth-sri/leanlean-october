module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsFractional
import Mathlib.Tactic

/-! # Signed barrier endpoint differences from the source modulus

The modulus and continuous origin extension are the explicit consumed Bellman
conclusions. This theorem proves an endpoint estimate, not a Green identity.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory Filter


/-- The source modulus controls signed endpoint differences using the actual kernel moments. -/
theorem deterministic_barrier_endpoint_of_modulus
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (alpha B : ℝ) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hB : 0 ≤ B)
    (Phi : Z → ℝ) (hPhi : Continuous Phi)
    (hmod : ∀ z w : Z, |Phi z-Phi w| ≤
      B*(|z.1-w.1|^(alpha/3)+|z.2-w.2|^alpha))
    (A : SmoothAutonomous lam Lam) (z : Z) (T : NNReal) (Y : ℝ) :
    let E := fullSpaceEvolution hH hLE hlam hLam A
    Integrable (fun w : Z => Phi (w.1-Y,w.2)-Phi (z.1-Y,z.2)) (kernelXV E T z) ∧
      (∫ w, |Phi (w.1-Y,w.2)-Phi (z.1-Y,z.2)| ∂kernelXV E T z) ≤
        B*((2*z.2^2*(T : ℝ)^2+4/3*Lam*(T : ℝ)^3)^(alpha/6)+
          (2*Lam*(T : ℝ))^(alpha/2)) := by
  let E := fullSpaceEvolution hH hLE hlam hLam A
  have hx := terminal_position_fractional_moment hH hLE hlam hLam A z T
    (a := alpha/3) (by linarith) (by linarith)
  have hv := terminal_velocity_fractional_moment hH hLE hlam hLam A z T ha0 (by linarith)
  let f := fun w : Z => Phi (w.1-Y,w.2)-Phi (z.1-Y,z.2)
  let g := fun w : Z => B*(|w.1-z.1|^(alpha/3)+|w.2-z.2|^alpha)

  have hb (w : Z) : |f w| ≤ g w := by

    have he : w.1-Y-(z.1-Y) = w.1-z.1 := by ring
    simpa only [f, g, he] using (hmod (w.1-Y,w.2) (z.1-Y,z.2))
  have hgi : Integrable g (kernelXV E T z) := (hx.1.add hv.1).const_mul B
  have hfi : Integrable f (kernelXV E T z) := by
    apply hgi.mono' (show Measurable f by
        apply (hPhi.measurable.comp ((measurable_fst.sub_const Y).prodMk measurable_snd)).sub_const).aestronglyMeasurable
    exact Eventually.of_forall (fun w => hb w)
  refine ⟨hfi, ?_⟩

  have he : alpha/3/2 = alpha/6 := by ring

  change (∫ w, |f w| ∂kernelXV E T z) ≤ _
  apply (integral_mono hfi.abs hgi hb).trans
  change (∫ w, B*(|w.1-z.1|^(alpha/3)+|w.2-z.2|^alpha) ∂kernelXV E T z) ≤ _
  rw [integral_const_mul]


  rw [integral_add hx.1 hv.1]
  simpa only [he] using (mul_le_mul_of_nonneg_left (add_le_add hx.2 hv.2) hB)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
