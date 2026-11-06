module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsWeightOrigin

/-! # Pointwise extended-weight limits, including the origin -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory Filter
open scoped Topology Convolution

variable (alpha : ℝ)

/-- Away from the physical origin the mollified weight tends to the literal source weight. -/
theorem regularizedBarrierWeight_punctured_tendsto  (q : Z) (hq : q ≠ (0, 0)) :
    Tendsto (fun n => ENNReal.ofReal (regularizedBarrierWeight alpha n q))
      atTop (𝓝 (rhoWeight (gamma alpha) q)) := by
  let sharedTerm_5022fac943 := ((fun X : ℝ => bellmanGauge (X, q.2) ^ (alpha - 2)))
  have hr := bellmanGauge_pos q hq


  have hm : Measurable sharedTerm_5022fac943 :=
    (bellmanGauge_continuous.measurable.comp
      (measurable_id.prodMk measurable_const)).pow_const _
  have hh := ContDiffBump.convolution_tendsto_right (μ := volume)
    (φ := barrierMollifierBump)
    (g := fun _  => sharedTerm_5022fac943)
    (k := fun _  => q.1) barrierMollifierRadius_tendsto
    (Eventually.of_forall (fun _ => hm.aestronglyMeasurable))
    ((show ContinuousAt sharedTerm_5022fac943 q.1 from ((bellmanGauge_continuous.comp (continuous_id.prodMk continuous_const)).continuousAt).rpow_const (Or.inl hr.ne')).tendsto.comp tendsto_snd) tendsto_const_nhds

  have he : rhoWeight (gamma alpha) q = ENNReal.ofReal (bellmanGauge q ^ (alpha - 2)) := by
    change (ENNReal.ofReal (bellmanGauge q)) ^ (-(2 - alpha)) = _
    have he : -(2 - alpha) = alpha - 2 := by ring
    rw [he, ENNReal.ofReal_rpow_of_pos hr]
  rw [he]
  exact (ENNReal.continuous_ofReal.tendsto _).comp (by
      simpa only [regularizedBarrierWeight, positionConvolution_displacement,
        barrierMollifier, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hh)

/-- The extended source weight is the pointwise mollifier limit at every point, including atoms. -/
theorem regularizedBarrierWeight_tendsto  (ha : 0 < alpha) (ha1 : alpha < 1)
    (q : Z) :
    Tendsto (fun n => ENNReal.ofReal (regularizedBarrierWeight alpha n q))
      atTop (𝓝 (rhoWeight (gamma alpha) q)) := by
  by_cases hq : q = (0, 0)
  · subst q
    rw [rhoWeight_origin (by dsimp only [gamma]; linarith : 0 < gamma alpha)]
    exact regularizedBarrierWeight_origin_tendsto alpha ha ha1
  · exact regularizedBarrierWeight_punctured_tendsto alpha q hq

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
