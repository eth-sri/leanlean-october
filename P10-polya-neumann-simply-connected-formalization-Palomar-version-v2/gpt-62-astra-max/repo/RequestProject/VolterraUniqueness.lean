module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

/-! A continuous Volterra integral inequality with zero initial data has only zero solution. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set

theorem continuous_eq_zero_of_norm_le_volterra
    {V : Type*} [NormedAddCommGroup V] {h : ℝ → V} (hh : Continuous h)
    {T C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Icc 0 T, ‖h t‖ ≤ C * ∫ s in (0 : ℝ)..t, ‖h s‖) :
    ∀ t ∈ Icc 0 T, h t = 0 := by
  let G  := fun t => ∫ s in 0..t, ‖h s‖
  have hcont : Continuous G :=
    (by fun_prop)
  have hderiv (t : ℝ)  :=
    intervalIntegral.integral_hasDerivAt_right (hh.norm.intervalIntegrable 0 t)
      hh.norm.aestronglyMeasurable.stronglyMeasurableAtFilter hh.norm.continuousAt
  have hG : ∀ t ∈ Icc 0 T, G t = 0 :=
    eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hcont.continuousOn
      (fun t _ => (hderiv t).hasDerivWithinAt) (by simp [G]) (fun t ht => by
        calc
          _ = _ := norm_norm _
          _ ≤ _ := (by grind)
          _ ≤ _ := mul_le_mul_of_nonneg_left (Real.le_norm_self _) hC)
  intro t ht
  apply norm_le_zero_iff.mp
  have htBound := hbound t ht
  change ‖h t‖ ≤ C * G t at htBound
  simpa [hG t ht, mul_zero] using htBound

end PolyaNeumann

end
