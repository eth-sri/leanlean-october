module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningWeakJetApprox
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningValues
public import PDEFoundation.Calculus.RegularityOrder


/-! # Almost-everywhere convergence of the classical flattened approximation jets -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Filter

variable {d : ℕ} {alpha : ℝ} (h : CounterProfileStatement d alpha) (r : ℝ) (n : ℕ)

/-- Flattening the smooth approximations keeps the literal profile formula. -/
noncomputable def mollifiedFlatProfile  : XV d → ℝ :=
  flatProfile (mollifiedProfile h n) flatteningPsi flatteningOffset alpha r

/-- Every flattened approximation is globally smooth. -/
theorem contDiff_mollifiedFlatProfile  :
    ContDiff ℝ PDE.smoothOrder (mollifiedFlatProfile h r n) := by
  unfold mollifiedFlatProfile flatProfile
  exact contDiff_const.sub (contDiff_const.mul
    (contDiff_flatteningPsi.comp ((contDiff_mollifiedProfile h n).div_const _)))

variable (alpha r : ℝ)

/-- The fixed slope composed with division is continuous. -/
theorem continuous_flatSlope  :
    Continuous (fun s  => deriv flatteningPsi (s / Real.rpow r alpha)) := by
  rw [funext deriv_flatteningPsi]
  exact contDiff_flatteningSlope.continuous.comp (continuous_id.div_const _)

/-- The fixed second derivative composed with division is continuous. -/
theorem continuous_flatSecond  :
    Continuous (fun s  => deriv (deriv flatteningPsi) (s / Real.rpow r alpha)) := by
  rw [funext deriv_flatteningPsi]
  exact (contDiff_flatteningSlope.continuous_deriv (by simp)).comp (continuous_id.div_const _)

variable {d : ℕ} {alpha : ℝ} (h : CounterProfileStatement d alpha) (r : ℝ)

/-- The flattened approximation values converge almost everywhere to the literal flattening. -/
theorem mollifiedFlatProfile_ae_tendsto  :
    ∀ᵐ q, Tendsto (fun n => mollifiedFlatProfile h r n q) atTop
      (nhds (selectedFlatProfile h r q)) := by

  have hc : Continuous (fun s : ℝ => 1 - flatteningOffset * Real.rpow r alpha -
      Real.rpow r alpha * flatteningPsi (s / Real.rpow r alpha)) :=
    continuous_const.sub (continuous_const.mul
      (contDiff_flatteningPsi.continuous.comp (continuous_id.div_const _)))
  filter_upwards [spatialMollify_ae_tendsto _ ((selectedProfile_spec h).2.2.2.2.2.2.1).locallyIntegrable] with q hq
  exact hc.continuousAt.tendsto.comp hq

variable (hr : 0 < r)

section
variable (i : Fin d)

include hr
/-- The position jets converge to the explicit selected flattened position jet. -/
theorem dx_mollifiedFlatProfile_ae_tendsto    :
    ∀ᵐ q, Tendsto (fun n => dx (mollifiedFlatProfile h r n) q i) atTop
      (nhds (flatProfilePositionJet h r q i)) := by


  filter_upwards [spatialMollify_ae_tendsto _ ((selectedProfile_spec h).2.2.2.2.2.2.1).locallyIntegrable,
    spatialMollify_ae_tendsto _ ((selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i)] with q hq hg

  convert (((continuous_flatSlope alpha r).continuousAt.tendsto.comp hq).neg.mul hg) using 1
  · funext n
    unfold dx mollifiedFlatProfile
    rw [fderiv_flatProfile _ _ _ hr q
      ((contDiff_mollifiedProfile h n).differentiable (by simp) q)]
    change -deriv flatteningPsi (mollifiedProfile h n q / Real.rpow r alpha) *
        dx (mollifiedProfile h n) q i = _
    rw [dx_mollifiedProfile]
    rfl
  · rfl

/-- The velocity jets converge to the explicit selected flattened velocity jet. -/
theorem dv_mollifiedFlatProfile_ae_tendsto    :
    ∀ᵐ q, Tendsto (fun n => dv (mollifiedFlatProfile h r n) q i) atTop
      (nhds (flatProfileVelocityJet h r q i)) := by


  filter_upwards [spatialMollify_ae_tendsto _ ((selectedProfile_spec h).2.2.2.2.2.2.1).locallyIntegrable,
    spatialMollify_ae_tendsto _ ((selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i)] with q hq hg

  convert (((continuous_flatSlope alpha r).continuousAt.tendsto.comp hq).neg.mul hg) using 1
  · funext n
    unfold dv mollifiedFlatProfile
    rw [fderiv_flatProfile _ _ _ hr q
      ((contDiff_mollifiedProfile h n).differentiable (by simp) q)]
    change -deriv flatteningPsi (mollifiedProfile h n q / Real.rpow r alpha) *
        dv (mollifiedProfile h n) q i = _
    rw [dv_mollifiedProfile]
    rfl
  · rfl
end


include hr in
/-- The Hessian jets converge, including the nonlinear product of the two first jets. -/
theorem dvv_mollifiedFlatProfile_ae_tendsto   (i k : Fin d) :
    ∀ᵐ q, Tendsto (fun n => dvv (mollifiedFlatProfile h r n) q i k) atTop
      (nhds (flatProfileHessian h r q i k)) := by
  have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
  have hv := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hh := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i k
  filter_upwards [spatialMollify_ae_tendsto _ hH.locallyIntegrable,
    spatialMollify_ae_tendsto _ (hv i), spatialMollify_ae_tendsto _ (hv k),
    spatialMollify_ae_tendsto _ hh] with q hq hi hk hhq
  have hp := (continuous_flatSlope alpha r).continuousAt.tendsto.comp hq
  have hp2 := (continuous_flatSecond alpha r).continuousAt.tendsto.comp hq
  have hconst : Tendsto (fun _ : ℕ => Real.rpow r (-alpha)) atTop
      (nhds (Real.rpow r (-alpha))) := tendsto_const_nhds

  convert ((hp.neg.mul hhq).sub (((hconst.mul hp2).mul hi).mul hk)) using 1
  · funext n
    rw [mollifiedFlatProfile, dvv_flatProfile_of_contDiffAt _ _ _ hr q
      ((contDiff_mollifiedProfile h n).contDiffAt.of_le (by simp)) i k,
      dvv_mollifiedProfile, dv_mollifiedProfile, dv_mollifiedProfile]
    rfl
  · rfl

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
