module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionUniformBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSourceIdentity

/-! # Essential bounds uniform in time for the selected extended spatial jets -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Set

variable {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1) (h : CounterProfileStatement d alpha) (r mu R m a b : ℝ) (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2) (hscale : 2 * Real.rpow r alpha ≤ 1) (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m)

include hd ha ha1 hr hmu hR hm hscale hmargin
/-- Each extended first component has a global essential spatial bound uniform on a
compact time interval, using the same selected weak representative as the convolution. -/
theorem construction_extendedGradient_uniform_ae_bound
    (i : Fin (d + d)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b,
      ∀ᵐ q, |constructionExtendedNativeGradient h r mu R m t q i| ≤ C := by

  have hK  := (isCompact_profile_unit_sublevel ha h).image
    (spatialCoordinateCLE d).symm.continuous
  obtain ⟨C, hC, hb⟩ := construction_rawGradient_uniform_bound h r hr mu R a b ((spatialCoordinateCLE d).symm '' {q | profileFunction h q ≤ 1}) hK i
  refine ⟨C, hC, fun t ht => ?_⟩
  have hz := construction_ae_native _
    (construction_extended_jets_zero_outside_profile hd ha ha1 h r mu R m hr hmu hR hm
      hscale (fun q hq => (hmargin q hq).le) t)
  filter_upwards [hz] with q hq
  let x := (spatialCoordinateCLE d).symm q
  by_cases hp : profileFunction h q < 1
  ·
    rw [constructionExtendedNativeGradient,
      (construction_extended_jets_eq_raw_on_profile h r mu R m t hm hmargin x (by
          simpa only [x, ContinuousLinearEquiv.apply_symm_apply] using hp)).1 i]
    exact hb t ht x ⟨q, hp.le, rfl⟩
  ·
    change |constructionExtendedPackedGradient h r mu R m t x i| ≤ C
    rw [(hq (by
        simpa only [x, ContinuousLinearEquiv.apply_symm_apply] using not_lt.mp hp)).1 i, abs_zero]
    exact hC

/-- Each extended second component has a global essential spatial bound uniform on a
compact time interval; the profile boundary contributes no extra representative. -/
theorem construction_extendedHessian_uniform_ae_bound
    (i k : Fin d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b,
      ∀ᵐ q, |constructionExtendedNativeHessian h r mu R m t q i k| ≤ C := by

  have hK  := (isCompact_profile_unit_sublevel ha h).image
    (spatialCoordinateCLE d).symm.continuous
  obtain ⟨C, hC, hb⟩ := construction_rawHessian_uniform_bound h r hr mu R a b ((spatialCoordinateCLE d).symm '' {q | profileFunction h q ≤ 1}) hK i k
  refine ⟨C, hC, fun t ht => ?_⟩
  have hz := construction_ae_native _
    (construction_extended_jets_zero_outside_profile hd ha ha1 h r mu R m hr hmu hR hm
      hscale (fun q hq => (hmargin q hq).le) t)
  filter_upwards [hz] with q hq
  let x := (spatialCoordinateCLE d).symm q
  by_cases hp : profileFunction h q < 1
  ·
    rw [constructionExtendedNativeHessian,
      (construction_extended_jets_eq_raw_on_profile h r mu R m t hm hmargin x (by
          simpa only [x, ContinuousLinearEquiv.apply_symm_apply] using hp)).2 i k]
    exact hb t ht x ⟨q, hp.le, rfl⟩
  ·
    change |constructionExtendedPackedHessian h r mu R m t x i k| ≤ C
    rw [(hq (by
        simpa only [x, ContinuousLinearEquiv.apply_symm_apply] using not_lt.mp hp)).2 i k, abs_zero]
    exact hC

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
