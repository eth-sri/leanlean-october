module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSourceRecovery
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionStationaryNorm
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionScales
import HypoellipticAleksandrov.Geometry.KineticPointMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionProductNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.BarrierPackedJets
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSourceIdentity
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffClassical
import Mathlib.Tactic.Ring
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileHolds
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ShellSource
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

/-! # Vanishing positive source norms before the spatial smoothing diagonal -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Filter Set
open scoped Topology ENNReal
open HypoellipticAleksandrov.Parabolic
open scoped MatrixOrder

/- Shell domination lifts to the literal spacetime source norm, with the finite time
factor and no change to the selected profile witnesses. -/
theorem construction_indicatorSource_norm_le {d : ℕ} (hd : 1 ≤ d)
    {alpha } (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m T S : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2) (hS : 0 < S)
    (hrate : mu = (d : ℝ) * profileLowerEllipticity h / R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    eLpNorm (fun P : KineticPoint d =>
      max (constructionIndicatorSource h r mu R (KineticPoint.equivProd d P)) 0) p
      (volume.restrict (backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S)) ≤
      (volume (Ioo (T - S ^ 2) T)) ^ (1 / p.toReal) *
        eLpNorm (flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r)
          p (volume.restrict {q | profileFunction h q < 1}) := by
  obtain ⟨_, _, _, _, hAm, _, hH, _, _, _, _, hgv, _⟩ := selectedProfile_spec h
  let f := flatSourceWithJet (profileMatrix h) (profileFunction h)
    (profileVelocityJet h) alpha r
  let D := {q | profileFunction h q < 1}
  have hD : MeasurableSet D := (isOpen_lt hH continuous_const).measurableSet
  have hf : Measurable f := measurable_flatSourceWithJet _ _ _ _ _ hAm hH.measurable hgv
  have hbound := construction_fixed_time_le_ae_spacetime
    (fun z => max (constructionIndicatorSource h r mu R z) 0)
    (fun z => D.indicator f z.2)
    ((construction_indicatorSource_measurable h r mu R).max measurable_const)
    ((hf.indicator hD).comp measurable_snd) ?_
  · have hm := ((construction_indicatorSource_measurable h r mu R).comp
        (KineticPoint.measurable_equivProd d)).max (measurable_const (a := (0 : ℝ)))
    have hn := eLpNorm_mono_ae_real (p := p)
      (g := fun P : KineticPoint d => D.indicator f (P.position, P.velocity))
      (μ := volume.restrict (backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S))
      hm.aestronglyMeasurable.restrict
      (ae_restrict_of_ae (hbound.mono (fun P hP => by
        simpa only [Real.norm_of_nonneg (le_max_right _ _)] using! hP)))
    apply hn.trans
    have he : eLpNorm f p (volume.restrict D) =
        eLpNorm (flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r)
          p (volume.restrict D) :=
      eLpNorm_congr_ae (ae_restrict_of_ae
        (flatSource_ae_eq_jet_of_profile h r).symm)
    have _h_xinl_1 : eLpNorm (fun P : KineticPoint d => D.indicator f (P.position, P.velocity)) p
      (volume.restrict (backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S)) ≤
      (volume (Ioo (T - S ^ 2) T)) ^ (1 / p.toReal) *
        eLpNorm f p (volume.restrict D) := by
      have _h_xinl_0 : eLpNorm (fun P : KineticPoint d => (D.indicator f) (P.position, P.velocity)) p (volume.restrict (backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S)) ≤ (volume (Ioo (T - S ^ 2) T)) ^ (1 / p.toReal) * eLpNorm (D.indicator f) p volume := by
        let f := (D.indicator f)
        have hf := (hf.indicator hD)
        let D : Set (ℝ × XV d) := Ioo (T - S ^ 2) T ×ˢ univ
        let e := KineticPoint.equivProd d
        have hD : MeasurableSet D := measurableSet_Ioo.prod MeasurableSet.univ
        have hsub : backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S ⊆ e ⁻¹' D := by
          intro P hP
          have hh := (construction_mem_cylinder_iff T S hS P).mp hP
          exact ⟨⟨hh.1, hh.2.1⟩, mem_univ _⟩
        apply (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hsub)).trans_eq
        have hmp := (KineticPoint.measurePreserving_equivProd d).restrict_preimage hD
        have he := eLpNorm_comp_measurePreserving (p := p)
          (hf.comp measurable_snd).aestronglyMeasurable.restrict hmp
        change eLpNorm ((fun z : ℝ × XV d => f z.2) ∘ e) p
          (volume.restrict (e ⁻¹' D)) = _
        apply he.trans
        rw [Measure.volume_eq_prod, ← Measure.restrict_prod_eq_prod_univ]
        simpa only [Function.comp_def, Measure.restrict_apply_univ] using
          construction_eLpNorm_snd (volume.restrict (Ioo (T - S ^ 2) T)) volume f hf p hp0 hpTop
      simpa only [eLpNorm_indicator_eq_eLpNorm_restrict hD] using _h_xinl_0
    simpa only [he] using _h_xinl_1
  · intro t
    have _h_xinl_0 : ∀ᵐ q : XV d ∂volume,
      max (constructionExtendedSource h r mu R m (profileMatrix h) ⟨t, q.1, q.2⟩) 0 ≤
        {y | profileFunction h y < 1}.indicator
          (flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r) q := by
      have he := construction_extendedSource_eq_indicator_ae hd ha ha1 h r mu R m
        hr hmu hR hm hscale hmargin t
      have hb : ∀ᵐ q ∂volume,
          timeCutoffSourceRepresentative h r ((d : ℝ) * profileLowerEllipticity h / R ^ 2) R
            ⟨t, q.1, q.2⟩ ≤
            flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q := by
        obtain ⟨hlam, _, _, _, _, hA, _⟩ := selectedProfile_spec h
        let mu := (d : ℝ) * profileLowerEllipticity h / R ^ 2
        have _h_inl_12 : ∀ᵐ q ∂volume,
            timeCutoffSourceRepresentative h r mu R ⟨t, q.1, q.2⟩ =
              deriv timeCutoffTheta (selectedFlatProfile h r q - barrier mu R ⟨t, q.1, q.2⟩) *
                (flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q -
                  backwardOperator (fun _t x v => profileMatrix h (x, v))
                    (barrier mu R) ⟨t, q.1, q.2⟩) -
              deriv (deriv timeCutoffTheta)
                (selectedFlatProfile h r q - barrier mu R ⟨t, q.1, q.2⟩) *
                PDE.vecDot ((profileMatrix h q).mulVec
                  (flatProfileVelocityJet h r q - kineticVelocityGradient (barrier mu R)
                    ⟨t, q.1, q.2⟩))
                  (flatProfileVelocityJet h r q - kineticVelocityGradient (barrier mu R)
                    ⟨t, q.1, q.2⟩) := by
            filter_upwards [flatProfile_representatives_source h r] with q hq
            unfold timeCutoffSourceRepresentative
            dsimp only
            have he := contraction_cutoff_identity (profileMatrix h q)
              (fun i k => flatProfileHessian h r q i k -
                kineticVelocityHessian (barrier mu R) ⟨t, q.1, q.2⟩ i k)
              (flatProfileVelocityJet h r q - kineticVelocityGradient (barrier mu R) ⟨t, q.1, q.2⟩)
              (deriv timeCutoffTheta (selectedFlatProfile h r q - barrier mu R ⟨t, q.1, q.2⟩))
              (deriv (deriv timeCutoffTheta)
                (selectedFlatProfile h r q - barrier mu R ⟨t, q.1, q.2⟩))
            simp only [Pi.sub_apply, Prod.mk.eta] at he ⊢
            rw [he, contraction_sub_right]
            rw [backwardOperator_apply, barrier_positionGradient]
            simp only [PDE.vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero,
              fullKineticCoefficientAt_apply] at hq ⊢
            have hdot (a : ℝ) :
                (∑ i, q.2 i * (a * flatProfilePositionJet h r q i)) =
                  a * ∑ i, q.2 i * flatProfilePositionJet h r q i := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
            rw [hdot, ← hq]
            ring


        filter_upwards [_h_inl_12,
          flatSource_nonneg_ae_of_profile h r hr] with q he hf
        rw [he]
        have hb := barrier_operator_nonneg hd (profileMatrix h) (profileLowerEllipticity h) R
          hlam hR (fun y => (hA y).1) ⟨t, q.1, q.2⟩
        have htheta := timeCutoffTheta_deriv_bounds
          (selectedFlatProfile h r q - barrier mu R ⟨t, q.1, q.2⟩)
        have hquad := quadratic_nonneg_of_loewner _ hlam.le _ (hA q).1
          (flatProfileVelocityJet h r q - kineticVelocityGradient (barrier mu R) ⟨t, q.1, q.2⟩)
        have hterm := mul_nonneg (timeCutoffTheta_deriv2_nonneg
          (selectedFlatProfile h r q - barrier mu R ⟨t, q.1, q.2⟩)) hquad
        exact (sub_le_self _ hterm).trans ((mul_le_mul_of_nonneg_left (sub_le_self (flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q) hb) htheta.1).trans (mul_le_of_le_one_left hf htheta.2))
      filter_upwards [he, hb, (flatSource_nonneg_ae_of_profile h r hr)] with q hq hbq hnq
      rw [hq]
      by_cases hprof : q ∈ {y | profileFunction h y < 1}
      · rw [indicator_of_mem hprof, indicator_of_mem hprof]
        rw [hrate]
        exact max_le hbq hnq
      · rw [indicator_of_notMem hprof, indicator_of_notMem hprof, max_self]
    filter_upwards [_h_xinl_0,
      construction_extendedSource_eq_indicator_ae hd ha ha1 h r mu R m hr hmu hR hm
        hscale hmargin t, flatSource_ae_eq_jet_of_profile h r] with q hb he hjet
    rw [constructionIndicatorSource_apply, ← he]
    by_cases hq : q ∈ D
    · rw [indicator_of_mem hq]
      have hb' := hb
      rw [indicator_of_mem hq, hjet] at hb'
      exact hb'
    · rw [indicator_of_notMem hq]
      change q ∉ {y | profileFunction h y < 1} at hq
      simpa only [indicator_of_notMem hq] using hb

/- Positive selected sources tend to zero on the fixed cylinder as the flattening
scales tend to zero in the full subcritical range. -/
theorem construction_indicatorSource_norm_tendsto {d : ℕ} (hd : 1 ≤ d)
    {alpha } (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (mu R m T S p : ℝ)
    (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2) (hS : 0 < S)
    (hrate : mu = (d : ℝ) * profileLowerEllipticity h / R ^ 2)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m)
    (hp : 1 ≤ p) (he : 0 < alpha - 2 + 4 * (d : ℝ) / p)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hs : ∀ j, 2 * Real.rpow (r j) alpha ≤ 1)
    (hlim : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (fun P : KineticPoint d =>
      max (constructionIndicatorSource h (r j) mu R (KineticPoint.equivProd d P)) 0)
      (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S)))
      atTop (𝓝 0) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr (zero_lt_one.trans_le hp)).ne'
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  let C := (volume (Ioo (T - S ^ 2) T)) ^ (1 / (ENNReal.ofReal p).toReal)
  have hC : C ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg
    (by positivity) (measure_Ioo_lt_top.ne)
  have _h_xinl_0 : Tendsto (fun j => eLpNorm (flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha (r j)) (ENNReal.ofReal p) (volume.restrict {q | profileFunction h q < 1})) atTop (nhds 0) := by
    have hexponent := he
    obtain ⟨C, r0, hC, hr0, hb⟩ : ∃ C r₀ : ℝ, 0 < C ∧ 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
        eLpNorm
          (flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r)
          (ENNReal.ofReal p) (volume.restrict {q | profileFunction h q < 1}) ≤
            ENNReal.ofReal (C * Real.rpow r (alpha - 2 + 4 * (d : ℝ) / p)) := by
      obtain ⟨hlam, hlamLam, hc, hC, hAm, hA, hH, hzero, hhom, hcomp,
        _, hgv, _, _, _, hgrad, _⟩ := selectedProfile_spec h
      have hp0 : 0 < p := zero_lt_one.trans_le hp
      obtain ⟨V, hV, hvol⟩ := shell_volume_bound (profileFunction h) alpha
        (profileLowerComparison h) ha hc hH (fun q => (hcomp q).1) hhom
      obtain ⟨K, hK, hbound⟩ := shell_source_bound (profileMatrix h)
        (profileFunction h) (profileVelocityJet h) alpha
        (profileLowerEllipticity h) (profileUpperEllipticity h)
        (profileUpperComparison h) ha ha1 hlam hlamLam hA hC hzero
        (fun q => (hcomp q).2) hgrad
      refine ⟨K * Real.rpow V (1 / p), 1, mul_pos hK (Real.rpow_pos_of_pos hV _),
        zero_lt_one, ?_⟩
      intro r hr _
      have hf := (measurable_flatSourceWithJet (profileMatrix h)
        (profileFunction h) (profileVelocityJet h) alpha r
        hAm hH.measurable hgv).aestronglyMeasurable (μ := volume)
      have hS : MeasurableSet (profileShell (profileFunction h) alpha r) :=
        ((isClosed_le continuous_const hH).inter (isClosed_le hH continuous_const)).measurableSet
      have hn := eLpNorm_le_shell_bound _ (profileShell (profileFunction h) alpha r)
        p (K * Real.rpow r (alpha - 2)) hp0
        (mul_nonneg hK.le (Real.rpow_pos_of_pos hr _).le) hf hS (hbound r hr)
        (fun q hq => flatSourceWithJet_eq_zero_off_shell _ _ _ alpha r hr q hq)
      have hpow := ENNReal.rpow_le_rpow (hvol r hr) (div_nonneg zero_le_one hp0.le)
      have hn' := hn.trans (mul_le_mul_right hpow (ENNReal.ofReal (K * Real.rpow r (alpha - 2))))
      have _h_xinl_0 : ENNReal.ofReal (K * Real.rpow r (alpha - 2)) *
        ENNReal.ofReal (V * r ^ (4 * d)) ^ (1 / p) =
          ENNReal.ofReal (K * Real.rpow V (1 / p) *
            Real.rpow r (alpha - 2 + 4 * (d : ℝ) / p)) := by
        have hK := hK.le
        simp only [Real.rpow_eq_pow]
        rw [ENNReal.ofReal_rpow_of_nonneg
          (show 0 ≤ V * r ^ (4 * d) from mul_nonneg hV.le (pow_nonneg hr.le _))
          (div_nonneg zero_le_one hp0.le),
          ← ENNReal.ofReal_mul (mul_nonneg hK (Real.rpow_pos_of_pos hr _).le),
          Real.mul_rpow hV.le (pow_nonneg hr.le _), ← Real.rpow_natCast_mul hr.le]
        have he : (4 * d : ℕ) * (1 / p : ℝ) = 4 * (d : ℝ) / p := by
          push_cast
          ring
        rw [he]
        congr 1
        calc
          _ = (K * V ^ (1 / p)) * (r ^ (alpha - 2) * r ^ (4 * (d : ℝ) / p)) := by ring
          _ = _ := by rw [← Real.rpow_add hr]
      rw [_h_xinl_0] at hn'
      apply (eLpNorm_restrict_le _ _ _ _).trans
      rw [eLpNorm_congr_ae (flatSource_ae_eq_jet_of_profile h r)]
      exact hn'
    have he := hlim.eventually (gt_mem_nhds hr0)
    have hpow := (Real.continuous_rpow_const hexponent.le).tendsto (0 : ℝ) |>.comp hlim
    have hpow0 : Tendsto (fun j => Real.rpow (r j) (alpha - 2 + 4 * (d : ℝ) / p))
        atTop (nhds 0) := by
      simpa only [Function.comp_def, Real.rpow_eq_pow, Real.zero_rpow hexponent.ne'] using hpow
    have hup : Tendsto (fun j => ENNReal.ofReal
        (C * Real.rpow (r j) (alpha - 2 + 4 * (d : ℝ) / p))) atTop (nhds 0) := by
      simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (hpow0.const_mul C)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    · exact Eventually.of_forall (fun _ => bot_le)
    · filter_upwards [he] with j hj
      exact hb (r j) (hr j) hj
  have hu := (ENNReal.continuous_const_mul hC).tendsto (0 : ℝ≥0∞) |>.comp
    _h_xinl_0
  have hu0 : Tendsto (fun j => C * eLpNorm
      (flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha (r j))
      (ENNReal.ofReal p) (volume.restrict {q | profileFunction h q < 1}))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using! hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu0
    (fun _ => bot_le) (fun j => construction_indicatorSource_norm_le hd ha ha1 h
      (r j) mu R m T S (hr j) hmu hR hm hS hrate (hs j) hmargin _ hp0 hpTop)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
