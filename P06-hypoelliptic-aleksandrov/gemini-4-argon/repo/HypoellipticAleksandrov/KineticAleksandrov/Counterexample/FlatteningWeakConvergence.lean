module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningWeakJetApprox
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningValues

/-! # Almost-everywhere convergence of the classical flattened approximation jets -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Filter

/- Flattening the smooth approximations keeps the literal profile formula. -/
noncomputable def mollifiedFlatProfile {d alpha}
    (h : CounterProfileStatement d alpha) (r : ℝ) (n : ℕ) : XV d → ℝ :=
  flatProfile (mollifiedProfile h n) flatteningPsi flatteningOffset alpha r

/- Every flattened approximation is globally smooth. -/
theorem contDiff_mollifiedFlatProfile {d alpha}
    (h : CounterProfileStatement d alpha) (r : ℝ) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifiedFlatProfile h r n) := by
  unfold mollifiedFlatProfile flatProfile
  exact contDiff_const.sub (contDiff_const.mul
    (contDiff_flatteningPsi.comp ((contDiff_mollifiedProfile h n).div_const _)))

/- The fixed slope composed with division is continuous. -/
theorem continuous_flatSlope (alpha r : ℝ) :
    Continuous (fun s : ℝ => deriv flatteningPsi (s / Real.rpow r alpha)) := by
  rw [funext deriv_flatteningPsi]
  exact contDiff_flatteningSlope.continuous.comp (continuous_id.div_const _)

/- The fixed second derivative composed with division is continuous. -/
theorem continuous_flatSecond (alpha r : ℝ) :
    Continuous (fun s : ℝ => deriv (deriv flatteningPsi) (s / Real.rpow r alpha)) := by
  rw [funext deriv_flatteningPsi]
  exact (contDiff_flatteningSlope.continuous_deriv (by simp)).comp (continuous_id.div_const _)

/- The flattened approximation values converge almost everywhere to the literal flattening. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
