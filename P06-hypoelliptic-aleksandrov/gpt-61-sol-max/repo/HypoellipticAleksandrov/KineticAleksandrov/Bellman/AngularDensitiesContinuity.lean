module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! # Continuity and positivity of actual absolutely continuous angular representatives -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

variable {h : ℝ → ℝ}

/-- Absolute continuity on every compact interval gives global continuity of the
representative. -/
theorem bellman_locallyAC_continuous
    (hh : ∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b) : Continuous h := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have hle : y - 1 ≤ y + 1 := by linarith
  have hc : ContinuousOn h (Icc (y - 1) (y + 1)) := by
    simpa only [uIcc_of_le hle] using (hh (y - 1) (y + 1) hle).continuousOn
  exact hc.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

/-- A continuous angular representative that is nonnegative almost everywhere is nonnegative. -/
theorem bellman_continuous_nonneg_of_ae  (hh : Continuous h)
    (hn : ∀ᵐ y, 0 ≤ h y) : ∀ y : ℝ, 0 ≤ h y := (fun y =>
  Eq.mpr
    (id
      (congrArg (fun _a => y ∈ _a)
        ((IsClosed.ae_eq_univ_iff_eq (isClosed_le continuous_const hh)).mp
          (Filter.mp_mem hn
            (Filter.univ_mem' (id fun y hy => id (propext { mp := fun x => trivial, mpr := fun x => hy })))))))
    True.intro)

/-- Almost everywhere ellipticity gives nonnegativity of the continuous angular density. -/
theorem bellmanAngularDensity_nonneg {f h : ℝ → ℝ}
    (hh : ∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b)
    (hf : ∀ᵐ y, 0 ≤ f y) (hfh : ∀ᵐ y, f y ≤ h y) :
    ∀ y : ℝ, 0 ≤ h y := by
  apply bellman_continuous_nonneg_of_ae (bellman_locallyAC_continuous hh)
  filter_upwards [hf, hfh] with y hy hfy
  exact hy.trans hfy

end HypoellipticAleksandrov.KineticAleksandrov
