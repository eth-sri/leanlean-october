module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.KillingTests
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SmoothTestOrder
import HypoellipticAleksandrov.KineticAleksandrov.Interval.KillingComparison
import HypoellipticAleksandrov.KineticAleksandrov.Interval.KillingJets
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
import Mathlib.Topology.Order.Compact

/-! # From smooth endpoint tests to killed interval mass -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open Filter Topology
open scoped MatrixOrder

/- Smooth compact tests bounded by one determine an upper bound for supported mass. -/
theorem mass_le_of_interval_smooth_tests {U } (hU : IsOpen U)
    (μ : Measure (PDE.Vec 1)) [IsFiniteMeasure μ] (hμ : μ.restrict U = μ)
    {C } (hC : 0 ≤ C)
    (htest : ∀ φ : PDE.Vec 1 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∀ w, 0 ≤ φ w ∧ φ w ≤ 1) → ∫ w, φ w ∂μ ≤ C) :
    μ.real univ ≤ C := by
  have hbound : μ U ≤ ENNReal.ofReal C := by
    rw [hU.measure_eq_iSup_isCompact μ]
    refine iSup_le fun A => iSup_le fun hAU => iSup_le fun hA => ?_
    obtain ⟨φ, hφ, hφc, hφU, hφr, hφA⟩ := exists_smooth_cutoff hA hU hAU
    have hi := hφ.continuous.integrable_of_hasCompactSupport hφc (μ := μ)
    have hle : μ.real A ≤ ∫ w, φ w ∂μ := by
      rw [← integral_indicator_one hA.measurableSet]
      apply integral_mono ((integrable_const (1 : ℝ)).indicator hA.measurableSet) hi
      intro w
      by_cases hw : w ∈ A
      · simp only [indicator_of_mem hw, hφA w hw, le_refl]
      · simpa only [indicator_of_notMem hw] using (hφr w).1
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ A)]
    exact ENNReal.ofReal_le_ofReal (hle.trans (htest φ hφ hφc hφU hφr))
  have he : μ univ = μ U := by
    conv_lhs => rw [← hμ]
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
  rw [Measure.real, he]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal hC)

/- The endpoint test bound gives the total positive parabolic mass bound. -/
theorem interval_endpoint_mass_bound {a c lam Lam σ τ s e }
    (hac : a < c) (hστ : σ < τ) (hlam : 0 < lam) (hs : s ^ 2 = 1)
    (B ) (hB : IsSectionTwoCoefficient lam Lam B)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hpar : HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) K)
    (hdpos : ∀ w ∈ PDE.oneDimensionalAxisBox a c, 0 < s * (w 0 - e))
    (hdnonneg : ∀ w ∈ closure (PDE.oneDimensionalAxisBox a c), 0 ≤ s * (w 0 - e))
    (v : PDE.Vec 1) (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ) :
    (P K hJ (scalarQuery σ τ hστ.le v hv)).real univ ≤
      intervalHeat lam (τ - σ) (s * (v 0 - e)) := by
  have hvJ : v ∈ PDE.oneDimensionalAxisBox a c := by
    simpa only [movingDomain_stationary] using hv
  apply mass_le_of_interval_smooth_tests
    (isOpen_of_isAdmissibleEvolutionDomain (interval_admissible hac))
    (P K hJ (scalarQuery σ τ hστ.le v hv))
  · apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    exact P_compl_eq_zero_stationary K hJ _
  · exact intervalErf_nonneg (div_nonneg (hdpos v hvJ).le (by positivity))
  · intro φ hφs hφc hφJ hφ
    let μ := P K hJ (scalarQuery σ τ hστ.le v hv)
    obtain ⟨Q, _hfirst, _hid, _hpos, _hsub, _hcomp, hrepr,
      _hmeas, _hend, _hkc, hsolve⟩ := hpar (fun _ _ _ _ => rfl)
    have hscaled : ∀ κ : ℝ, 0 ≤ κ → κ < 1 →
        κ * (∫ w, φ w ∂μ) ≤ intervalHeat lam (τ - σ) (s * (v 0 - e)) := by
      intro κ hκ0 hκ1
      let F : BoundedBorel (PDE.Vec 1) :=
        ⟨fun w => κ * φ w, measurable_const.mul hφs.continuous.measurable,
          ⟨1, zero_le_one, fun w => by
            rw [abs_of_nonneg (mul_nonneg hκ0 (hφ w).1)]
            exact (mul_le_of_le_one_right hκ0 (hφ w).2).trans hκ1.le⟩⟩
      have hFJ : tsupport (fun w => κ * φ w) ⊆ PDE.oneDimensionalAxisBox a c :=
        tsupport_mul_subset_right.trans hφJ
      obtain ⟨V, hV, heval, _hunique⟩ := hsolve τ F
        ⟨contDiff_const.mul hφs, hφc.mul_left, by
          simpa only [movingDomain_stationary] using hFJ⟩
      have hdom : ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
      ∀ v ∈ tsupport φ, κ * φ v ≤ intervalHeat lam ε (s * (v 0 - e)) := by
        have hpos := (fun w hw => hdpos w (hφJ hw))
        by_cases hempty : (tsupport φ).Nonempty
        · have hc : Continuous (fun v : PDE.Vec 1 => s * (v 0 - e)) := by fun_prop
          obtain ⟨v₀, hv₀, hmin⟩ := hφc.exists_isMinOn hempty hc.continuousOn
          have ht := tendsto_intervalHeat_time_zero hlam (hpos v₀ hv₀)
          have he := ht.eventually (eventually_gt_nhds hκ1)
          filter_upwards [he, self_mem_nhdsWithin] with ε hε hεpos v hv
          calc κ * φ v ≤ κ := by
                exact mul_le_of_le_one_right hκ0 (hφ v).2
            _ ≤ intervalHeat lam ε (s * (v₀ 0 - e)) := hε.le
            _ ≤ intervalHeat lam ε (s * (v 0 - e)) :=
              intervalHeat_mono_distance hlam hεpos (hmin hv)
        · exact Eventually.of_forall fun _ v hv => (hempty ⟨v, hv⟩).elim
      have hεbound : ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
          V (σ, v) ≤ intervalHeat lam (τ - σ + ε) (s * (v 0 - e)) := by
        filter_upwards [hdom, self_mem_nhdsWithin] with ε hdomε hε
        have hε0 : 0 < ε := hε
        apply interval_terminal_comparison hac hστ hlam B hB F V
          (endpointHeat lam τ ε s e) hV
        · intro p hp
          exact (contDiffAt_endpointHeat hlam p (by linarith only [hp.1.2, hε0])).continuousAt
            |>.continuousWithinAt
        · intro p hp
          exact (contDiffAt_endpointHeat hlam p (by linarith only [hp.1.2, hε0])).of_le (by simp)
        · intro p hp
          exact endpointHeat_operator_nonpos hlam hs B p (by linarith only [hp.1.2, hε0])
            (hdpos _ hp.2).le (interval_coefficient_lower B hB _ _)
        · intro w hw
          change κ * φ w ≤ intervalHeat lam (τ - τ + ε) (s * (w 0 - e))
          rw [sub_self, zero_add]
          by_cases hwφ : w ∈ tsupport φ
          · exact hdomε w hwφ
          · rw [image_eq_zero_of_notMem_tsupport hwφ, mul_zero]
            exact intervalErf_nonneg (div_nonneg (hdnonneg w hw) (by positivity))
        · intro p hp
          exact intervalErf_nonneg (div_nonneg (hdnonneg _ (frontier_subset_closure hp.2))
            (by positivity))
        · simpa only [movingDomain_stationary] using subset_closure
            (show v ∈ PDE.oneDimensionalAxisBox a c from
              by simpa only [movingDomain_stationary] using hv)
      have hlimit : Tendsto (fun ε => intervalHeat lam (τ - σ + ε) (s * (v 0 - e)))
          (nhdsWithin 0 (Ioi 0)) (𝓝 (intervalHeat lam (τ - σ) (s * (v 0 - e)))) := by
        have hc := (contDiffAt_intervalHeat hlam (τ - σ, s * (v 0 - e))
          (sub_pos.mpr hστ)).continuousAt
        have ht0 : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Ioi 0)) (𝓝 0) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        have ht1 : Tendsto (fun ε : ℝ => τ - σ + ε) (nhdsWithin 0 (Ioi 0))
            (𝓝 (τ - σ)) := by simpa only [add_zero] using ht0.const_add (τ - σ)
        have ht := ht1.prodMk_nhds (tendsto_const_nhds (x := s * (v 0 - e)))
        exact hc.tendsto.comp
          (f := fun ε : ℝ => (τ - σ + ε, s * (v 0 - e))) ht
      have hbound := ge_of_tendsto hlimit hεbound
      have he := heval σ hστ.le ⟨v, hv⟩
      rw [hrepr] at he
      have hi : (∫ w, φ w ∂μ) =
          ∫ w : EvolutionPosition (PDE.oneDimensionalAxisBox a c) stationary τ, φ w.1
            ∂parabolicMarginalKernel K hJ σ τ hστ.le ⟨v, hv⟩ := by
        exact integral_map measurable_subtype_coe.aemeasurable
          hφs.continuous.measurable.aestronglyMeasurable
      rw [hi, ← integral_const_mul]
      exact he ▸ hbound
    have ht : Tendsto (fun κ : ℝ => κ * (∫ w, φ w ∂μ)) (nhdsWithin 1 (Iio 1))
        (𝓝 (∫ w, φ w ∂μ)) := by
      have hκ : Tendsto (fun κ : ℝ => κ) (nhdsWithin 1 (Iio 1)) (𝓝 1) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [one_mul] using hκ.mul_const (∫ w, φ w ∂μ)
    apply le_of_tendsto ht
    filter_upwards [(eventually_gt_nhds (zero_lt_one : (0 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds, self_mem_nhdsWithin] with κ hκ0 hκ1
    exact hscaled κ hκ0.le hκ1

end HypoellipticAleksandrov.KineticAleksandrov.Interval
