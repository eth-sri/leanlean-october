module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSourceRecovery
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionUniformOperator
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SmoothFamilyGeometry
import HypoellipticAleksandrov.Coefficients.ParabolicRegularization

/-! # Positive-source norm recovery on the one fixed kinetic cylinder -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Filter HypoellipticAleksandrov.Parabolic
open scoped Topology ENNReal

/-- Spatial smoothing of each fixed flattened cutoff recovers the positive source in
finite-exponent norm on the fixed cylinder, without an analytic premise. -/
theorem construction_positiveSource_error_tendsto {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m T S : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2) (hS : 0 < S)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    Tendsto (fun n => eLpNorm (fun P =>
      max (backwardOperator (fun _t x v => profileMatrix h (x, v))
        (smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n)) P) 0 -
      max (constructionIndicatorSource h r mu R (KineticPoint.equivProd d P)) 0)
      p (volume.restrict (backwardCylinder (⟨T, 0, 0⟩ ) S)))
      atTop (𝓝 0) := by
  let sharedTerm_c7a04b50f9 := ((⟨T, 0, 0⟩ : KineticPoint d))

  let nu := volume.restrict (backwardCylinder sharedTerm_c7a04b50f9 S)

  have : IsFiniteMeasure nu := ⟨by
    simpa only [nu, Measure.restrict_apply_univ] using
      (backwardCylinder_volume_lt_top sharedTerm_c7a04b50f9 S hS)⟩
  let F := fun n P => backwardOperator (fun _t x v => profileMatrix h (x, v))
    (smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n)) P
  let g := fun P => constructionIndicatorSource h r mu R (KineticPoint.equivProd d P)

  have hF (n : ℕ) : Measurable (F n) :=
    measurable_backwardOperator_of_joint_smooth _ ((selectedProfile_spec h).2.2.2.2.1) _
      (smoothedZeroExtendedProfile_contDiff ha h r mu R hr hmu hR
        (fun q hq => (hmargin q hq).trans hm) _)
  have hg  := (construction_indicatorSource_measurable h r mu R).comp
    (KineticPoint.measurable_equivProd d)


  have hAb q i k  :=
    coefficient_entry_abs_le_of_ellipticity
      ((selectedProfile_spec h).2.2.2.2.2.1 q).1
      ((selectedProfile_spec h).2.2.2.2.2.1 q).2 i k
  obtain ⟨C, hC, hb⟩ := construction_smoothedOperator_uniform_bound hd ha ha1 h
    r mu R m (T - S ^ 2) T S hr hmu hR hm hS.le hscale hmargin
    (profileMatrix h) (3 * (|profileLowerEllipticity h| + |profileUpperEllipticity h|)) (mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) (abs_nonneg _))) hAb
  have hFb (n : ℕ) : ∀ᵐ P ∂nu, |F n P| ≤ C := by
    filter_upwards [ae_restrict_mem ((isOpen_backwardCylinder _ _ hS).measurableSet)] with P hP
    have hh := (construction_mem_cylinder_iff T S hS P).mp hP
    exact hb _ P ⟨hh.1.le, hh.2.1.le⟩
      (fun i => (PDE.abs_apply_le_vecEuclideanNorm P.velocity i).trans hh.2.2.1.le)
  have hl : ∀ᵐ P ∂nu, Tendsto (fun n => F n P) atTop (𝓝 (g P)) :=
    ae_restrict_of_ae (construction_smoothedOperator_tendsto_ae_spacetime hd ha ha1 h
      r mu R m hr hmu hR hm hscale hmargin)

  exact construction_positive_part_error_tendsto nu p hp0 hpTop F g
    (fun n => (hF n).aestronglyMeasurable) hg.aestronglyMeasurable C hC hFb (by
        filter_upwards [hl, ae_all_iff.mpr hFb] with P hP hbP
        exact le_of_tendsto' hP.abs hbP) hl

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
