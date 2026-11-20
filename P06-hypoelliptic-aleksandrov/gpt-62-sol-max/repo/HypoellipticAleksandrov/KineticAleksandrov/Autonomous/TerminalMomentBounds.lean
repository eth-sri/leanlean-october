module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsActual
import Mathlib.Tactic

/-! # Source terminal second moments of the canonical full-space kernel -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory
open scoped ENNReal

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (z : Z) (T : NNReal)
include lam Lam A z T

/-- The exact deterministic second-moment conditions, with constants 2 and 4/3. -/
theorem terminal_second_moments :
    let E := fullSpaceEvolution A
    (∫⁻ w, ENNReal.ofReal ((w.2-z.2)^2) ∂kernelXV E T z) ≤
      ENNReal.ofReal (2*Lam*(T : ℝ)) ∧
    (∫⁻ w, ENNReal.ofReal ((w.1-z.1)^2) ∂kernelXV E T z) ≤
      ENNReal.ofReal (2*z.2^2*(T : ℝ)^2+4/3*Lam*(T : ℝ)^3) := by
  let E := fullSpaceEvolution A
  have hE := fullSpaceEvolution_spec A
  refine ⟨kernelXV_velocity_2_moment A E hE z T, ?_⟩
  apply (kernelXV_position_2_moment A E hE z T).trans
  apply ENNReal.ofReal_le_ofReal
  have hL : 0 ≤ Lam := A.positive.le.trans A.ordered
  have hT := T.property
  have hh : 0 ≤ z.2^2*(T : ℝ)^2+(2/3 : ℝ)*Lam*(T : ℝ)^3 := by positivity
  linarith only [hh]

/-- Both actual real second moments are integrable, rather than merely total integrals. -/
theorem terminal_second_moments_integrable :
    let E := fullSpaceEvolution A
    Integrable (fun w : Z => (w.2-z.2)^2) (kernelXV E T z) ∧
      Integrable (fun w : Z => (w.1-z.1)^2) (kernelXV E T z) := by
  have h := terminal_second_moments A z T
  constructor
  · apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
      (Filter.Eventually.of_forall (fun w : Z => sq_nonneg (w.2-z.2)))).mp
    exact ne_of_lt (h.1.trans_lt ENNReal.ofReal_lt_top)
  · apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
      (Filter.Eventually.of_forall (fun w : Z => sq_nonneg (w.1-z.1)))).mp
    exact ne_of_lt (h.2.trans_lt ENNReal.ofReal_lt_top)

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
