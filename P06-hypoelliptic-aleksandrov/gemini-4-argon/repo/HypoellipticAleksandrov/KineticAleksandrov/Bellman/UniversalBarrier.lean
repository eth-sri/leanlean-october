module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.UniversalBarrierPositiveImage
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.UniversalBarrierLowerBound
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalizationGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.UniversalBarrierScaling
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Instances.Real.Lemmas
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierFunctionSpaceLinear
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierSeparation
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierSeparationMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialStationary
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RatioNormalization
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.UniversalBarrierParameters
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureJets
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftIntegrability
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftJets
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftProperties
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.PairSetting
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialMeasures
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialMeasuresComparison
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialMeasuresDegree
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialMeasuresNonzero
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialMeasuresProper
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialMeasuresProperties
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialStationaryIntegrability
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialStationaryMeasureIntegrals
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialStationaryTests
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Maps.Proper.Basic
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RatioNormalizationCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.DegreeGap
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftCalculus
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # The universal homogeneous Bellman barrier with the source adjoint exponent -/

@[expose] public section
noncomputable section
open Set
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory
open Filter Topology

/- One homogeneous barrier and constant work for all punctured points and coefficients. -/
theorem exists_bellman_barrier (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    2 ≤ bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) ∧
    bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) < 3 ∧
    ∀ alpha : ℝ, bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) - 2 < alpha →
      alpha < 1 → ∃ phi : (ℝ × ℝ) → ℝ, ∃ c : ℝ,
        IsBellmanHomogeneous alpha phi ∧ 0 < c ∧
          ∀ q ∈ bellmanPuncturedSet, ∀ b ∈ Icc lam Lam,
            c * bellmanGauge q ^ (alpha - 2) ≤ bellmanOperator b phi q := by
  have hr : 1 ≤ Lam / lam := by
    apply (le_div_iff₀ hlam).2
    simpa only [one_mul] using hLam
  obtain ⟨hlo, hhi⟩ := bellmanAdjointExponent_range (Lam / lam) hr
  refine ⟨hlo, hhi, ?_⟩
  intro alpha ha ha1
  obtain ⟨phi, hhom, hpos⟩ : ∃ phi : (ℝ × ℝ) → ℝ, IsBellmanHomogeneous alpha phi ∧
      ∀ z : BellmanSphere, ∀ b : BellmanCoefficient lam Lam,
        0 < bellmanOperator b.val phi z.val := by
    obtain ⟨hapos, _, hgap⟩ : 0 < alpha ∧ alpha < 1 ∧
      bellmanAdjointExponent (Lam / lam)
        (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) < 2 + alpha := by
      have ht := bellmanAdjointExponent_two_le (Lam / lam)
        (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam)
      exact ⟨by linarith, ha1, by linarith⟩
    by_contra hno
    obtain ⟨pi, hpi, hann⟩ : ∃ pi : Measure (BellmanSphere × BellmanCoefficient lam Lam),
        IsProbabilityMeasure pi ∧
        ∀ phi : (ℝ × ℝ) → ℝ, IsBellmanHomogeneous alpha phi →
          (∫ w, bellmanOperator w.2.val phi w.1.val ∂pi) = 0 := by
      have hd : Disjoint bellmanPositiveCone
          (bellmanImageSpace alpha lam Lam : Set C(BellmanSphere × BellmanCoefficient lam Lam, ℝ)) := by
        refine disjoint_left.mpr ?_
        intro f hf hS
        obtain ⟨phi, hphi, he⟩ := (mem_bellmanImageSpace_iff alpha lam Lam f).mp hS
        apply hno
        refine ⟨phi, hphi, ?_⟩
        intro z b
        have h := hf (z, b)
        rw [← he] at h
        exact h
      obtain ⟨pi, hpi, ht⟩ := exists_bellman_subspace_probability
        (bellmanImageSpace alpha lam Lam) hd
      refine ⟨pi, hpi, ?_⟩
      intro phi hphi
      exact ht (bellmanImage lam Lam phi hphi)
        ((mem_bellmanImageSpace_iff alpha lam Lam _).mpr ⟨phi, hphi, rfl⟩)
    let := hpi
    have hp : IsBellmanAdjointPair lam Lam (2 + alpha) (radialMu alpha pi) (radialEta alpha pi) := by
      obtain ⟨hm, he, hn, hlo, hhi, hdm, hde⟩ : IsBellmanRadon (radialMu alpha pi) ∧ IsBellmanRadon (radialEta alpha pi) ∧
          (radialMu alpha pi ≠ 0 ∨ radialEta alpha pi ≠ 0) ∧
          ENNReal.ofReal lam • radialMu alpha pi ≤ radialEta alpha pi ∧
          radialEta alpha pi ≤ ENNReal.ofReal Lam • radialMu alpha pi ∧
          HasBellmanDensityDegree (2 + alpha) (radialMu alpha pi) ∧
          HasBellmanDensityDegree (2 + alpha) (radialEta alpha pi) := by
        obtain ⟨hm, he⟩ : IsBellmanRadon (radialMu alpha pi) ∧ IsBellmanRadon (radialEta alpha pi) := by
          let : LocallyCompactSpace BellmanPuncturedPlane :=
            isOpen_compl_singleton.locallyCompactSpace
          exact ⟨⟨inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance⟩⟩
        obtain ⟨hlo, hhi⟩ : ENNReal.ofReal lam • radialMu alpha pi ≤ radialEta alpha pi ∧
            radialEta alpha pi ≤ ENNReal.ofReal Lam • radialMu alpha pi := by
          let mu := (bellmanRadiusMeasure alpha).prod pi
          have hlo : ENNReal.ofReal lam • mu ≤
              mu.withDensity (fun w => ENNReal.ofReal w.2.2.val) := by
            rw [← withDensity_const]
            exact withDensity_mono (Filter.Eventually.of_forall
              (fun w => ENNReal.ofReal_le_ofReal w.2.2.property.1))
          have hhi : mu.withDensity (fun w => ENNReal.ofReal w.2.2.val) ≤
              ENNReal.ofReal Lam • mu := by
            rw [← withDensity_const]
            exact withDensity_mono (Filter.Eventually.of_forall
              (fun w => ENNReal.ofReal_le_ofReal w.2.2.property.2))
          have hf := (continuous_sphereRadialPoint lam Lam).measurable
          have hl := Measure.map_mono hlo hf
          have hh := Measure.map_mono hhi hf
          rw [Measure.map_smul _ hf.aemeasurable] at hl hh
          exact ⟨hl, hh⟩
        have _h_xinl_0 : radialMu alpha pi ≠ 0 := by
          intro hz
          have hm : Measure.map bellmanGaugeRadius (radialMu alpha pi) = bellmanRadiusMeasure alpha := by
              unfold radialMu
              rw [Measure.map_map continuous_bellmanGaugeRadius.measurable
                (continuous_sphereRadialPoint lam Lam).measurable]
              have he : bellmanGaugeRadius ∘ (sphereRadialPoint (lam := lam) (Lam := Lam)) =
                  Prod.fst := by
                funext w
                exact Subtype.ext (sphereRadialPoint_gauge w)
              rw [he, Measure.map_fst_prod, measure_univ, one_smul]

            /- A probability on the sphere produces a genuinely nonzero first adjoint measure. -/
          rw [hz, Measure.map_zero] at hm
          exact bellmanRadiusMeasure_ne_zero alpha hm.symm
        exact ⟨hm, he, Or.inl _h_xinl_0, hlo, hhi,
          radialMu_densityDegree alpha pi, radialEta_densityDegree alpha pi⟩
      refine ⟨hm, he, hn, hlo, hhi, ?_, hdm, hde⟩
      intro zeta hz hc hs
      obtain ⟨⟨ht, htc, hts⟩, ⟨hv, hvc, hvs⟩⟩ :=
        bellman_radial_stationary_test_properties zeta hz hc hs
      let FT : BellmanPositiveTime × (BellmanSphere × BellmanCoefficient lam Lam) → ℝ :=
        fun w => w.1.val ^ (1 - alpha) *
          ((sphereRadialPoint w).val.2 * bellmanDx zeta (sphereRadialPoint w).val)
      let FV : BellmanPositiveTime × (BellmanSphere × BellmanCoefficient lam Lam) → ℝ :=
        fun w => w.1.val ^ (1 - alpha) *
          (w.2.2.val * bellmanDvv zeta (sphereRadialPoint w).val)
      have hFT : Integrable FT (bellmanPositiveTimeVolume.prod pi) := by
        simpa only [one_mul] using bellman_radial_test_integrable alpha pi
          (fun q => q.2 * bellmanDx zeta q) ht htc hts (fun _ => 1) continuous_const
      have hFV : Integrable FV (bellmanPositiveTimeVolume.prod pi) :=
        bellman_radial_test_integrable alpha pi (bellmanDvv zeta) hv hvc hvs
          (fun w => w.2.val) (continuous_subtype_val.comp continuous_snd)
      have hMT : (∫ q, q.val.2 * fderiv ℝ zeta q.val (1, 0) ∂radialMu alpha pi) =
          ∫ w, FT w ∂bellmanPositiveTimeVolume.prod pi :=
        integral_radialMu alpha pi (fun q => q.val.2 * bellmanDx zeta q.val)
          (ht.comp continuous_subtype_val)
      have hMV : (∫ q, fderiv ℝ (fun z => fderiv ℝ zeta z (0, 1)) q.val (0, 1)
          ∂radialEta alpha pi) = ∫ w, FV w ∂bellmanPositiveTimeVolume.prod pi :=
        integral_radialEta alpha pi (fun q => bellmanDvv zeta q.val)
          (hv.comp continuous_subtype_val) hlam.le
      rw [hMT, hMV, ← integral_add hFT hFV,
        integral_prod_symm (fun w => FT w + FV w) (hFT.add hFV)]
      have hLift : IsBellmanHomogeneous alpha (lift alpha zeta) :=
        (bellman_test_lift alpha hapos ha1 zeta (hz.of_le (by norm_num)).contDiffOn hc hs).1
      calc
        (∫ w, ∫ r, FT (r, w) + FV (r, w) ∂bellmanPositiveTimeVolume ∂pi) =
            ∫ w, bellmanOperator w.2.val (lift alpha zeta) w.1.val ∂pi := by
          apply integral_congr_ae
          apply ae_of_all
          intro w
          have _h_xinl_0 : bellmanOperator w.2.val (lift alpha zeta) w.1.val =
          ∫ r : BellmanPositiveTime,
            (r.val ^ (1 - alpha) *
              ((bellmanPlaneDilation r.val w.1.val).2 * bellmanDx zeta
                (bellmanPlaneDilation r.val w.1.val))) +
            (r.val ^ (1 - alpha) * (w.2.val * bellmanDvv zeta (bellmanPlaneDilation r.val w.1.val)))
            ∂bellmanPositiveTimeVolume := by
            let q := w.1.val
            have hq := w.1.ne_zero
            let b := w.2.val
            obtain ⟨⟨ht, htc, hts⟩, ⟨hv, hvc, hvs⟩⟩ :=
              bellman_radial_stationary_test_properties zeta hz hc hs
            have hiT := bellman_lift_integrand_integrable (alpha - 2)
              (fun q => q.2 * bellmanDx zeta q) ht htc hts q hq
            have hiV := (bellman_lift_integrand_integrable (alpha - 2)
              (bellmanDvv zeta) hv hvc hvs q hq).const_mul b
            have he : -1 - (alpha - 2) = 1 - alpha := by ring
            rw [he] at hiT hiV
            have hiV' : Integrable (fun r : BellmanPositiveTime => r.val ^ (1 - alpha) *
                (b * bellmanDvv zeta (bellmanPlaneDilation r.val q))) bellmanPositiveTimeVolume :=
              hiV.congr (ae_of_all _ (fun r => by ring))
            rw [integral_add hiT hiV', bellmanOperator,
              bellman_lift_dx alpha zeta (hz.of_le (by norm_num)).contDiffOn hc hs q hq,
              bellman_lift_dvv alpha zeta (hz.of_le (by norm_num)).contDiffOn hc hs q hq]
            unfold lift
            rw [← integral_const_mul, ← integral_const_mul]
            congr 1
            · apply integral_congr_ae
              apply ae_of_all
              intro r
              dsimp only [bellmanPlaneDilation]
              have hp : r.val ^ (-1 - (alpha - 3)) = r.val ^ (1 - alpha) * r.val := by
                calc
                  r.val ^ (-1 - (alpha - 3)) = r.val ^ ((1 - alpha) + 1) := by congr 1; ring
                  _ = r.val ^ (1 - alpha) * r.val ^ (1 : ℝ) := Real.rpow_add r.property _ _
                  _ = r.val ^ (1 - alpha) * r.val := by rw [Real.rpow_one]
              rw [hp]
              ring
            · apply integral_congr_ae
              exact ae_of_all _ (fun r => by rw [he]; ring)
          exact _h_xinl_0.symm
        _ = 0 := hann (lift alpha zeta) hLift
    have hd : 2 + alpha ∈ bellmanDegrees lam Lam := ⟨radialMu alpha pi, radialEta alpha pi, hp⟩
    have _h_xinl_0 : bellmanDegrees lam Lam = bellmanAdmissibleDegrees (Lam / lam) := by
      ext β
      rw [mem_bellmanAdmissibleDegrees_iff]
      constructor
      · rintro ⟨μ, η, hp⟩
        refine ⟨Measure.map (bellmanPositionHomeomorph lam hlam) μ,
          ENNReal.ofReal lam⁻¹ • Measure.map (bellmanPositionHomeomorph lam hlam) η, ?_⟩
        simpa only [div_self hlam.ne'] using hp.rescale_position lam hlam
      · rintro ⟨μ, η, hp⟩
        refine ⟨Measure.map (bellmanPositionHomeomorph lam⁻¹ (inv_pos.mpr hlam)) μ,
          ENNReal.ofReal (lam⁻¹)⁻¹ •
            Measure.map (bellmanPositionHomeomorph lam⁻¹ (inv_pos.mpr hlam)) η, ?_⟩
        have hlow : (1 : ℝ) / lam⁻¹ = lam := by simp
        have hhigh : (Lam / lam) / lam⁻¹ = Lam := by
          simp [div_inv_eq_mul, hlam.ne']
        simpa only [hlow, hhigh] using hp.rescale_position lam⁻¹ (inv_pos.mpr hlam)
    rw [_h_xinl_0] at hd
    have hupper := (bellmanAdjointExponent_characterization (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam)).1.1 hd
    exact (not_le_of_gt hgap) hupper
  obtain ⟨c, hc, hbound⟩ : ∃ c : ℝ, 0 < c ∧ ∀ q ∈ bellmanPuncturedSet, ∀ b ∈ Icc lam Lam,
      c * bellmanGauge q ^ (alpha - 2) ≤ bellmanOperator b phi q := by
    let : Nonempty (BellmanCoefficient lam Lam) := by
        exact (
      ⟨⟨lam, le_rfl, hLam⟩⟩
      )
    have hc := hhom.image_continuous (lam := lam) (Lam := Lam)
    obtain ⟨w0, _, hmin⟩ := (isCompact_univ : IsCompact
      (univ : Set (BellmanSphere × BellmanCoefficient lam Lam))).exists_isMinOn
        univ_nonempty hc.continuousOn
    refine ⟨bellmanOperator w0.2.val phi w0.1.val, hpos w0.1 w0.2, ?_⟩
    intro q hq b hb
    let z := bellmanSpherePoint q hq
    have hminq := hmin (show (z, (⟨b, hb⟩ : BellmanCoefficient lam Lam)) ∈ univ from trivial)
    have hs : bellmanOperator b phi (bellmanPlaneDilation (bellmanGauge q) z.val) =
      (bellmanGauge q) ^ (alpha - 2) * bellmanOperator b phi z.val := by
      let r := (bellmanGauge q)
      have hr := (bellmanGauge_pos q hq)
      let q := z.val
      have hq := z.ne_zero
      have he : (fun z => phi (bellmanPlaneDilation r z)) =ᶠ[𝓝 q]
          fun z => r ^ alpha * phi z := by
        filter_upwards [bellmanPuncturedSet_isOpen.mem_nhds hq] with z hz
        exact hhom.2 r hr z hz
      have hj : r ^ 2 * bellmanOperator b phi (bellmanPlaneDilation r q) =
          r ^ alpha * bellmanOperator b phi q := by
        rw [← bellmanOperator_comp_dilation r hr phi hhom.1 q hq b,
          bellman_operator_germ_eq he b, bellman_operator_mul]
      apply mul_left_cancel₀ (pow_ne_zero 2 hr.ne')
      calc
        r ^ 2 * bellmanOperator b phi (bellmanPlaneDilation r q) =
            r ^ alpha * bellmanOperator b phi q := hj
        _ = r ^ 2 * (r ^ (alpha - 2) * bellmanOperator b phi q) := by
          rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hr]
          congr 2
          ring
    have _h_inl_9 : bellmanPlaneDilation (bellmanGauge q) (bellmanSpherePoint q hq).val = q := by
        rw [bellmanSpherePoint, bellmanPlaneDilation_comp,
          mul_inv_cancel₀ (bellmanGauge_pos q hq).ne']
        simp only [bellmanPlaneDilation, one_pow, one_mul, Prod.mk.eta]

      /- Positivity on the compact sphere and diffusion interval gives the global homogeneous bound. -/
    rw [_h_inl_9] at hs
    rw [hs, mul_comm]
    exact mul_le_mul_of_nonneg_left hminq (Real.rpow_nonneg (bellmanGauge_nonneg q) _)
  exact ⟨phi, c, hhom, hc, hbound⟩

end HypoellipticAleksandrov.KineticAleksandrov
