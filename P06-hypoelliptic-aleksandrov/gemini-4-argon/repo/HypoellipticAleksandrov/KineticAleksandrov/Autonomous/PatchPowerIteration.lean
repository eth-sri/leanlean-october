module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PatchPowerDoubling
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FullCoefficientAdapters
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SmoothAutonomousP6Statement
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.MacroscopicPropagationPhysical
import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationContractionGeometry

/-! # Finite doubling iteration for a positive return patch -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set
open MeasureTheory Holder Holder.Growth

/- The radius after `n` doublings. -/
def returnExpandedRadius (ell : ℝ) (n : ℕ) : ℝ := (2 : ℝ) ^ n * ell

/- The transported centre after `n` doublings, with the geometric time sum evaluated. -/
def returnExpandedCenter (z : Point) (ell : ℝ) (n : ℕ) : Point :=
  let dt := (8 / 3 : ℝ) * ((returnExpandedRadius ell n) ^ 2 - ell ^ 2)
  ⟨z.time + dt, z.position + dt • z.velocity, z.velocity⟩

/- Radius doubling is multiplication by two. -/
theorem returnExpandedRadius_succ (ell : ℝ) (n : ℕ) :
    returnExpandedRadius ell (n + 1) = 2 * returnExpandedRadius ell n := by
  simp only [returnExpandedRadius, pow_succ]
  ring

/- The explicit geometric sum agrees with the one-step transported centre. -/
theorem returnExpandedCenter_succ (z : Point) (ell : ℝ) (n : ℕ) :
    returnExpandedCenter z ell (n + 1) =
      returnDoubleCenter (returnExpandedCenter z ell n) (returnExpandedRadius ell n) := by
  rw [returnExpandedCenter, returnExpandedRadius_succ]
  ext i <;> simp only [returnExpandedCenter, returnDoubleCenter,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

/- The expanded radius never decreases. -/
theorem returnExpandedRadius_mono {ell } (hell : 0 ≤ ell) {m n } (hmn : m ≤ n) :
    returnExpandedRadius ell m ≤ returnExpandedRadius ell n :=  mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hmn) hell

/- All intermediate centres stay later than the initial centre. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
