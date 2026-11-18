/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFFStructure.DirichletCircleVersion

/-!
# Exterior-pinned finite Markov assembly
-/

@[expose] public section
open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped Topology ENNReal NNReal
universe u
namespace DOZZ.Proofs


private lemma ae_mem_ball_circle (c x : ℂ) (ρ r : ℝ) (hx : ‖x - c‖ + Real.exp (-r) < ρ) :
    ∀ᵐ z ∂circleMeasure x r, z ∈ ball c ρ :=
  (ae_mem_sphere_circleMeasure x r).mono fun _ hz =>
    interior_circle_closedBall_subset c x ρ r hx
      (by simpa only [abs_of_pos (Real.exp_pos _)] using sphere_subset_closedBall hz)


/-- The literal double-circle Green integral separates its regular and singular parts. -/
theorem integral_integral_diskGreenKernel (c x y : ℂ) (ρ r s : ℝ) (hρ : 0 < ρ)
    (hx : ‖x - c‖ + Real.exp (-r) < ρ) (hy : ‖y - c‖ + Real.exp (-s) < ρ) :
    (∫ v, ∫ w, diskGreenKernel c ρ hρ v w ∂circleMeasure y s ∂circleMeasure x r) =
      Real.log ‖(ρ : ℂ) ^ 2 - (x - c) * star (y - c)‖ - Real.log ρ -
        (∫ v, Real.log (max (Real.exp (-s)) ‖y - v‖) ∂circleMeasure x r) := by
  have diskGreen_reg_circle (x w : ℂ) (ρ r : ℝ) (hρ : 0 < ρ) (hx : ‖x - c‖ + Real.exp (-r) < ρ) (hw : w ∈ ball c ρ) : Integrable (fun z : ℂ => Real.log ‖(ρ : ℂ) ^ 2 - (z - c) * star (w - c)‖) (circleMeasure x r) ∧
        (∫ z, Real.log ‖(ρ : ℂ) ^ 2 - (z - c) * star (w - c)‖ ∂circleMeasure x r) =
          Real.log ‖(ρ : ℂ) ^ 2 - (x - c) * star (w - c)‖ := by
    have hharm := (harmonicOnNhd_diskGreen_regular c w ρ hρ hw).mono
      ((interior_circle_closedBall_subset c x ρ r hx).trans ball_subset_closedBall)
    refine ⟨integrable_circleMeasure_of_circleIntegrable x r (by fun_prop)
      (hharm.continuousOn.mono sphere_subset_closedBall).circleIntegrable', ?_⟩
    rw [integral_circleMeasure_eq_circleAverage x r _ (by fun_prop)]
    exact hharm.circleAverage_eq
  have norm_diskGreen_num_comm (z w : ℂ) (ρ : ℝ) : ‖(ρ : ℂ) ^ 2 - (z - c) * star (w - c)‖ = ‖(ρ : ℂ) ^ 2 - (w - c) * star (z - c)‖ := by
    rw [show (ρ : ℂ) ^ 2 - (w - c) * star (z - c) = star ((ρ : ℂ) ^ 2 - (z - c) * star (w - c)) by
      simp only [Complex.star_def, map_sub, map_pow, map_mul, Complex.conj_conj, Complex.conj_ofReal]; ring,
      norm_star]
  let _ := circleMeasure_isProbability x r
  have hsingle {u w : ℂ} {t : ℝ} (hu : ‖u - c‖ + Real.exp (-t) < ρ) (hw : w ∈ ball c ρ) :
      (∫ z, diskGreenKernel c ρ hρ w z ∂circleMeasure u t) =
        Real.log ‖(ρ : ℂ) ^ 2 - (w - c) * star (u - c)‖ - Real.log ρ -
          Real.log (max (Real.exp (-t)) ‖u - w‖) := by
    let _ := circleMeasure_isProbability u t
    let _ := circleMeasure_noAtoms u t
    obtain ⟨hi, hval⟩ := diskGreen_reg_circle u w ρ t hρ hu hw
    have hl : Integrable (fun z : ℂ => Real.log ‖w - z‖) (circleMeasure u t) := by
      simpa only [norm_sub_rev w] using integrable_log_norm_sub_circleMeasure u w t
    have he : (fun z => diskGreenKernel c ρ hρ w z) =ᵐ[circleMeasure u t]
        fun z => Real.log ‖(ρ : ℂ) ^ 2 - (z - c) * star (w - c)‖ - Real.log ρ - Real.log ‖w - z‖ := by
      filter_upwards [ae_mem_ball_circle c u ρ t hu, (circleMeasure u t).ae_ne w] with z hz hzw
      rw [diskGreenKernel_eq_log_parts c w z ρ hρ hw hz hzw.symm, norm_diskGreen_num_comm w z ρ]
    have hs1 := integral_sub (hi.sub (integrable_const (Real.log ρ))) hl
    have hs2 := integral_sub hi (integrable_const (Real.log ρ))
    simp only [Pi.sub_apply] at hs1 hs2
    rw [integral_congr_ae he, hs1, hs2, integral_const, probReal_univ, one_smul, hval,
      integral_log_norm_rev_sub_circleMeasure, norm_diskGreen_num_comm u w ρ]
  have hys : y ∈ ball c ρ := mem_ball_iff_norm.2 (by linarith [Real.exp_pos (-s)])
  obtain ⟨hi, hval⟩ := diskGreen_reg_circle x y ρ r hρ hx hys
  have hlog : Continuous fun v : ℂ => Real.log (max (Real.exp (-s)) ‖y - v‖) :=
    (continuous_const.max (continuous_const.sub continuous_id).norm).log
      fun _ => ((Real.exp_pos _).trans_le (le_max_left _ _)).ne'
  have hs1 := integral_sub (hi.sub (integrable_const (Real.log ρ)))
    (integrable_circleMeasure_of_circleIntegrable x r hlog.measurable hlog.continuousOn.circleIntegrable')
  have hs2 := integral_sub hi (integrable_const (Real.log ρ))
  simp only [Pi.sub_apply] at hs1 hs2
  rw [integral_congr_ae ((ae_mem_ball_circle c x ρ r hx).mono fun v hv => hsingle hy hv),
    hs1, hs2, integral_const, probReal_univ, one_smul, hval]

/-- Circle points in an interior disk also lie inside its exterior pin. -/
theorem interior_circle_norm_le_pin (c x : ℂ) (R ρ r : ℝ)
    (hpin : ‖c‖ + ρ ≤ R) (hx : ‖x - c‖ + Real.exp (-r) < ρ) :
    ∀ᵐ z ∂circleMeasure x r, ‖z‖ ≤ R :=
  (ae_mem_ball_circle c x ρ r hx).mono fun z hz => by
    linarith [norm_sub_norm_le z c, mem_ball_iff_norm.1 hz]

/-- Exterior-pin Markov decomposition with all-order uniform harmonic moments. -/
theorem exists_exteriorPinned_markov_uniform
    (n : ℕ) (R ρ a δ : ℝ) (hR : 1 < R) (hρ : 0 < ρ)
    (haρ : a < ρ) (hδ : 0 < δ) :
    ∃ C : ℝ → ℝ, (∀ l, 0 < l → 0 < C l) ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω]
      (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ),
      IsEquatorGFF P X → IsCircleAverage P X Xc →
    ∀ c : Fin n → ℂ,
      (∀ i, ‖c i‖ + ρ + δ ≤ R) →
      (∀ i j, i ≠ j → 2 * ρ + δ ≤ dist (c i) (c j)) →
    ∃ (D : Fin n → Ω → Distr) (H : Ω → Distr)
      (Hi : Fin n → Ω → ℂ → ℝ) (Dc : Fin n → Ω → ℂ → ℝ → ℝ) (ε : ℝ) (q : ℕ → ℝ → ℝ)
      (p : Fin n → ℂ → ℕ → TestFn),
      0 < ε ∧ ε < δ / 2 ∧
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (q k) ∧ HasCompactSupport (q k) ∧
        tsupport (q k) ⊆ Ioo 0 (ε / (k + 1)) ∧
        (∀ t, 0 ≤ q k t) ∧ (∫ t : ℝ, q k t) = 1) ∧
      (∀ i z (hz : z ∈ ball (c i) ρ), ∀ k,
        (∀ w, p i z k w = poissonCollarValue (c i) z ρ hρ hz (q k) w) ∧
        tsupport (p i z k) ⊆ (⋃ j, ball (c j) ρ)ᶜ) ∧
      (∀ i z, z ∈ ball (c i) ρ →
        Tendsto (fun k => eLpNorm
          (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω (p i z k) - Hi i ω z) 2 P)
          atTop (𝓝 0)) ∧
      (∀ i, IsGaussianProcess (fun f : TestFn => fun ω => D i ω f) P ∧
        (∀ f : TestFn, Measurable (fun ω => D i ω f) ∧
          MemLp (fun ω => D i ω f) 2 P ∧ (∫ ω, D i ω f ∂P) = 0) ∧
        (∀ f g : TestFn, covariance (fun ω => D i ω f) (fun ω => D i ω g) P =
          diskGreenCovariance (c i) ρ hρ f g)) ∧
      IsGaussianProcess (fun f : TestFn => fun ω => H ω f) P ∧
      (∀ f : TestFn, Measurable (fun ω => H ω f) ∧
        MemLp (fun ω => H ω f) 2 P ∧ (∫ ω, H ω f ∂P) = 0) ∧
      (∀ i, Measurable (fun w : Ω × ℂ => Hi i w.1 w.2)) ∧
      (∀ i z, z ∈ ball (c i) ρ →
        MemLp (fun ω => Hi i ω z) 2 P ∧ (∫ ω, Hi i ω z ∂P) = 0) ∧
      (∀ i z w, z ∈ ball (c i) ρ → w ∈ ball (c i) ρ →
        covariance (fun ω => Hi i ω z) (fun ω => Hi i ω w) P =
          Real.log R + Real.log ρ -
            Real.log ‖(ρ : ℂ) ^ 2 - (z - c i) * star (w - c i)‖) ∧
      (∀ᵐ ω ∂P,
        (∀ f : TestFn, exteriorPinnedEvaluation X Xc R (by linarith) ω f =
          (∑ i, D i ω f) + H ω f) ∧
          (∀ f : TestFn, X ω f = (∑ i, D i ω f) + H ω f -
          equatorRestorationScalar Xc R (by linarith) ω * (∫ z : ℂ, f z)) ∧
        (∀ i, InnerProductSpace.HarmonicOnNhd (Hi i ω) (ball (c i) ρ) ∧
          ContDiffOn ℝ (⊤ : ℕ∞) (Hi i ω) (ball (c i) ρ)) ∧
        (∀ i (f : TestFn), tsupport f ⊆ ball (c i) ρ →
          H ω f = (∫ z : ℂ, f z * Hi i ω z)) ∧
        (∀ i (f : TestFn), tsupport f ⊆ (closedBall (c i) ρ)ᶜ → D i ω f = 0)) ∧
      iIndepFun (fun j : Option (Fin n) => fun ω => fun f : TestFn =>
        match j with | none => H ω f | some i => D i ω f) P ∧
      IndepFun (fun ω => fun i => fun f : TestFn => D i ω f)
        (fun ω => fun f : {f : TestFn // tsupport f ⊆ (⋃ i, ball (c i) ρ)ᶜ} =>
          exteriorPinnedEvaluation X Xc R (by linarith) ω f.val) P ∧
      (∀ i l, 0 < l →
        ∫⁻ ω, ENNReal.ofReal (Real.exp (l *
            |equatorRestorationScalar Xc R (by linarith) ω|)) *
          ⨆ z ∈ closedBall (c i) a, ENNReal.ofReal (Real.exp (l * |Hi i ω z|)) ∂P
          ≤ ENNReal.ofReal (C l)) ∧
      (∀ i, Measurable[(MeasurableSpace.comap (fun ω => fun f : TestFn => D i ω f)
          MeasurableSpace.pi).prod inferInstance]
        (fun w : Ω × (ℂ × ℝ) => Dc i w.1 w.2.1 w.2.2)) ∧
      (∀ i, IsGaussianProcess (fun p : {p : ℂ × ℝ // ‖p.1 - c i‖ + Real.exp (-p.2) < ρ} =>
        fun ω => Dc i ω p.1.1 p.1.2) P) ∧
      (∀ i (x : ℂ) (r : ℝ), ‖x - c i‖ + Real.exp (-r) < ρ →
        MemLp (fun ω => Dc i ω x r) 2 P ∧ (∫ ω, Dc i ω x r ∂P) = 0 ∧
        (fun ω => Xc ω x r) =ᵐ[P] fun ω =>
          Dc i ω x r + Hi i ω x - equatorRestorationScalar Xc R (by linarith) ω) ∧
      (∀ i (x y : ℂ) (r s : ℝ), ‖x - c i‖ + Real.exp (-r) < ρ →
        ‖y - c i‖ + Real.exp (-s) < ρ →
        covariance (fun ω => Dc i ω x r) (fun ω => Dc i ω y s) P =
          ∫ v, ∫ w, diskGreenKernel (c i) ρ hρ v w ∂circleMeasure y s ∂circleMeasure x r) := by
  classical
  refine ⟨exteriorPinnedHarmonicMomentBound R ρ a,
    fun l _ => exteriorPinnedHarmonicMomentBound_pos R ρ a l hρ haρ, ?_⟩
  intro Ω _ P X Xc hX hc c hmargin hsep
  let _ := hX.1
  let ε := δ / 4
  have hε : 0 < ε := by positivity
  have hεδ2 : ε < δ / 2 := by dsimp [ε]; linarith
  have hεδ : ε < δ := by linarith
  have hRp : 0 < R := by linarith
  have hpin (i : Fin n) : ‖c i‖ + ρ ≤ R := by linarith [hmargin i]
  choose Hi hHim hHih hHiG hHi hHicov using fun i =>
    exists_exteriorPinned_harmonic_poisson_family P X Xc hX hc (c i) R ρ ε δ hR hρ hε hεδ (hmargin i)
  have hHimem i z hz := (hHi i z hz).1
  have hHimean i z hz := (hHi i z hz).2.1
  have hHilim i z hz := (hHi i z hz).2.2
  have hUc (i : Fin n) : ContinuousOn (poissonFamilyL2 P (c i) ρ (Hi i) (hHimem i)) (ball (c i) ρ) := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert continuous_poisson_gaussian_toLp P (c i) R ρ hρ
      (fun z : {z : ℂ // z ∈ ball (c i) ρ} => fun ω => Hi i ω z.1)
      (fun z => hHimem i z.1 z.2) (fun z => hHimean i z.1 z.2)
      (fun z w => hHicov i z.1 w.1 z.2 w.2) using 1
    ext z : 1
    change (if hz : z.1 ∈ ball (c i) ρ then (hHimem i z.1 hz).toLp (fun ω => Hi i ω z.1) else 0) = _
    simp [z.2]
  let T (i : Fin n) (f : TestFn) :=
    dirichletCompletedL2Map P X Xc hX hc (c i) R ρ hRp (Hi i) (hHimem i) (hUc i)
      (diskTestRestrictionL2 (c i) ρ f)
  let D (i : Fin n) := dirichletDistribution P X Xc hX hc (c i) R ρ hRp (Hi i) (hHimem i) (hUc i)
  have hDversion i f := dirichletDistribution_apply_ae_eq P X Xc hX hc (c i) R ρ hRp (Hi i) (hHimem i) (hUc i) f
  have hDm i f := measurable_dirichletDistribution_apply P X Xc hX hc (c i) R ρ hRp (Hi i) (hHimem i) (hUc i) f
  have hDmem i f := dirichletDistribution_apply_memLp P X Xc hX hc (c i) R ρ hRp (Hi i) (hHimem i) (hUc i) f
  have hDmean i f := dirichletDistribution_apply_integral_zero P X Xc hX hc (c i) R ρ ε hR hρ hε (hpin i)
    (Hi i) (hHimem i) (hHimean i) (hUc i) (hHicov i) (hHilim i) f
  have hDcov i f g := dirichletDistribution_covariance P X Xc hX hc (c i) R ρ ε hR hρ hε (hpin i)
    (Hi i) (hHimem i) (hHimean i) (hUc i) (hHicov i) (hHilim i) f g
  have hDG i := dirichletDistribution_isGaussianProcess P X Xc hX hc (c i) R ρ ε hR hρ hε (hpin i)
    (Hi i) (hHimem i) (hHimean i) (hUc i) (hHicov i) (hHilim i)
  have hTspan i f : T i f ∈ gaussianHilbertSpan (gffStructureL2Family X Xc hX hc) :=
    dirichletCompletedL2Map_mem_original_gaussianHilbertSpan P X Xc hX hc (c i) R ρ ε hR hρ hε (hpin i)
      (Hi i) (hHimem i) (hHimean i) (hUc i) (hHicov i) (hHilim i) _
  have hself i f g : covariance (T i f) (exteriorPinnedTestL2 P X Xc hX hc R hRp g) P = covariance (T i f) (T i g) P := by
    rw [dirichletCompletedL2Map_test_covariance P X Xc hX hc (c i) R ρ ε hR hρ hε (hpin i)
        (Hi i) (hHimem i) (hHimean i) (hUc i) (hHicov i) (hHilim i),
      dirichletCompletedL2Map_covariance P X Xc hX hc (c i) R ρ ε hR hρ hε (hpin i)
        (Hi i) (hHimem i) (hHimean i) (hUc i) (hHicov i) (hHilim i)]
  have hcross i j (hij : i ≠ j) f g :=
    dirichletCompletedL2Map_separated_covariance_zero P X Xc hX hc (c i) R ρ ε hR hρ hε (hpin i)
      (Hi i) (hHimem i) (hHimean i) (hUc i) (hHicov i) (hHilim i)
      (c j) (hpin j) δ hδ hεδ (hsep i j hij)
      (Hi j) (hHimem j) (hHimean j) (hUc j) (hHicov j) (hHilim j) f g
  let Y := exteriorPinnedTestL2 P X Xc hX hc R hRp
  let Ufam : Option (Fin n) → TestFn → Ω → ℝ := fun j f ω =>
    match j with | none => finiteMarkovComplement X Xc R hRp D ω f | some i => D i ω f
  have hGfam := finiteMarkovTestL2Family_isGaussianProcess P (gffStructureL2Family X Xc hX hc)
    (gffStructureL2Family_isGaussianProcess X Xc hX hc) Y T
    (exteriorPinnedTestL2_mem_original_gaussianHilbertSpan P X Xc hX hc R hRp) hTspan
  have hUfam (j : Option (Fin n)) (f : TestFn) : Ufam j f =ᵐ[P] ⇑(finiteMarkovTestL2Family P Y T j f) := by
    cases j with
    | none => exact finiteMarkovComplement_apply_ae_eq P X Xc hX hc R hRp D T hDversion f
    | some i => exact hDversion i f
  have hHG := finiteMarkovVersion_block_isGaussianProcess P Y T Ufam hGfam hUfam none
  have hblocks := finiteMarkovVersion_iIndepFun P Y T Ufam hGfam hUfam hself hcross
  let E := {f : TestFn // tsupport f ⊆ (⋃ i, ball (c i) ρ)ᶜ}
  have hexind : IndepFun (fun ω i (f : TestFn) => D i ω f)
      (fun ω (f : E) => exteriorPinnedEvaluation X Xc R hRp ω f.1) P :=
    (finiteDirichletVersion_indep_pinned P (gffStructureL2Family X Xc hX hc)
      (gffStructureL2Family_isGaussianProcess X Xc hX hc) T
      (fun g : E => exteriorPinnedTestL2 P X Xc hX hc R hRp g.1) hTspan
      (fun g => exteriorPinnedTestL2_mem_original_gaussianHilbertSpan P X Xc hX hc R hRp g.1)
      (fun i f ω => D i ω f) (fun g ω => exteriorPinnedEvaluation X Xc R hRp ω g.1)
      hDversion (fun g => (exteriorPinnedTestL2_ae_eq P X Xc hX hc R hRp g.1).symm)
      fun i f g => by
        rw [dirichletCompletedL2Map_test_covariance P X Xc hX hc (c i) R ρ ε hR hρ hε (hpin i)
          (Hi i) (hHimem i) (hHimean i) (hUc i) (hHicov i) (hHilim i)]
        exact diskGreenCovariance_eq_zero_of_exterior_union c ρ hρ i f g.1 g.2).comp
      (Measurable.of_eval fun i => Measurable.of_eval fun f => measurable_pi_apply (i, f)) measurable_id
  have hDext i := ae_dirichletDistribution_exterior_tests_zero P X Xc hX hc (c i) R ρ hRp (Hi i) (hHimem i) (hUc i)
  have hHlocal := ae_finiteMarkovComplement_harmonic_agreement P X Xc R hRp c ρ D Hi
    (separated_interior_test_support_exterior c ρ δ hδ hsep)
    (fun i => ae_dirichletDistribution_interior_harmonic_agreement P X Xc hX hc (c i) R ρ ε hR hρ hε (hpin i)
      (Hi i) (hHimem i) (hHimean i) (hUc i) (hHicov i) (hHilim i) (hHim i)
      ((hHih i).mono fun _ hω => hω.2.continuousOn)) hDext
  choose Dc hDcm hDcG hDc hDce using fun i =>
    exists_dirichletDistribution_circle_gaussian_split P X Xc hX hc (c i) R ρ ε hR hρ hε (hpin i)
      (Hi i) (hHimem i) (hHimean i) (hUc i) (hHicov i) (hHilim i) (hHim i)
      ((hHih i).mono fun _ hω => ⟨hω.1, hω.2.continuousOn⟩)
  have hDccov (i : Fin n) (x y : ℂ) (r s : ℝ) (hx : ‖x - c i‖ + Real.exp (-r) < ρ)
      (hy : ‖y - c i‖ + Real.exp (-s) < ρ) :
      covariance (fun ω => Dc i ω x r) (fun ω => Dc i ω y s) P =
        ∫ v, ∫ w, diskGreenKernel (c i) ρ hρ v w ∂circleMeasure y s ∂circleMeasure x r := by
    rw [covariance_congr_ae (hDce i x r hx) (hDce i y s hy)]
    have hxs : x ∈ ball (c i) ρ := mem_ball_iff_norm.2 (by linarith [Real.exp_pos (-r)])
    have hys : y ∈ ball (c i) ρ := mem_ball_iff_norm.2 (by linarith [Real.exp_pos (-s)])
    have hsub (z : ℂ) (t : ℝ) : dirichletCircleResidualL2 P X Xc hc (c i) R ρ (Hi i) (hHimem i) z t =
        (circleAverageL2 hc (z, t) - circleAverageL2 hc (0, -Real.log R)) -
          poissonFamilyL2 P (c i) ρ (Hi i) (hHimem i) z := by
      unfold dirichletCircleResidualL2; abel
    have hxU := dirichletCircleResidualL2_poisson_covariance_zero P X Xc hX hc (c i) R ρ ε hR hρ hε (hpin i)
      (Hi i) (hHimem i) (hHimean i) (hUc i) (hHicov i) (hHilim i) (hHim i) ((hHih i).mono fun _ h => h.1)
      x r hx y hys
    have hyU := dirichletCircleResidualL2_poisson_covariance_zero P X Xc hX hc (c i) R ρ ε hR hρ hε (hpin i)
      (Hi i) (hHimem i) (hHimean i) (hUc i) (hHicov i) (hHilim i) (hHim i) ((hHih i).mono fun _ h => h.1)
      y s hy x hxs
    rw [hsub] at hxU hyU
    have horth (A B U₀ V₀ : Lp ℝ 2 P) (hAV : covariance (⇑(A - U₀)) V₀ P = 0)
        (hBU : covariance (⇑(B - V₀)) U₀ P = 0) :
        covariance (⇑(A - U₀)) (⇑(B - V₀)) P = covariance A B P - covariance U₀ V₀ P := by
      rw [covariance_L2_sub_left] at hBU
      have hUB : covariance U₀ B P = covariance U₀ V₀ P := by
        rw [covariance_comm U₀ B, covariance_comm U₀ V₀]; exact sub_eq_zero.1 hBU
      rw [covariance_L2_sub_right, covariance_L2_sub_left, hUB, hAV]; ring
    have hpin_cov {u : ℂ} {t : ℝ} (hu : ‖u - c i‖ + Real.exp (-t) < ρ) :
        covariance (circleAverageL2 hc (u, t)) (circleAverageL2 hc (0, -Real.log R)) P =
          ∫ z, Real.log (normPlus z) ∂circleMeasure u t := by
      rw [covariance_congr_ae (circleAverageL2_ae_eq hc (u, t)) (circleAverageL2_ae_eq hc (0, -Real.log R)),
        circleAverage_covariance_integral P X Xc hX hc]
      refine integral_congr_ae ((interior_circle_norm_le_pin (c i) u R ρ t (hpin i) hu).mono fun z hz => ?_)
      dsimp only
      rw [integral_gffKernel_exterior_origin R hR, max_eq_left hz]; ring
    have hxx : covariance (circleAverageL2 hc (x, r)) (circleAverageL2 hc (y, s)) P =
        -(∫ z, Real.log (max (Real.exp (-s)) ‖y - z‖) ∂circleMeasure x r) +
          (∫ z, Real.log (normPlus z) ∂circleMeasure x r) +
          (∫ z, Real.log (normPlus z) ∂circleMeasure y s) := by
      rw [covariance_congr_ae (circleAverageL2_ae_eq hc (x, r)) (circleAverageL2_ae_eq hc (y, s)),
        circleAverage_covariance_integral P X Xc hX hc, integral_integral_gffKernel_eq_logmax]
    have hpp : covariance (circleAverageL2 hc (0, -Real.log R)) (circleAverageL2 hc (0, -Real.log R)) P = Real.log R := by
      rw [covariance_congr_ae (circleAverageL2_ae_eq hc (0, -Real.log R)) (circleAverageL2_ae_eq hc (0, -Real.log R)),
        circleAverage_covariance_self X Xc hX hc, circleSelfEnergy_exterior_origin R hR]
    rw [hsub, hsub, horth _ _ _ _ hxU hyU,
      covariance_L2_sub_left, covariance_L2_sub_right, covariance_L2_sub_right,
      hxx, hpin_cov hx, (covariance_comm _ _).trans (hpin_cov hy), hpp,
      covariance_congr_ae (poissonFamilyL2_ae_eq P (c i) ρ (Hi i) (hHimem i) x hxs)
        (poissonFamilyL2_ae_eq P (c i) ρ (Hi i) (hHimem i) y hys),
      hHicov i x y hxs hys, integral_integral_diskGreenKernel (c i) x y ρ r s hρ hx hy]
    ring
  let p (i : Fin n) (z : ℂ) (k : ℕ) :=
    if hz : z ∈ ball (c i) ρ then canonicalPoissonCollarTest (c i) z ρ ε hρ hε hz k else 0
  have hp i z (hz : z ∈ ball (c i) ρ) k : p i z k = canonicalPoissonCollarTest (c i) z ρ ε hρ hε hz k := dite_eq_left hz
  refine ⟨D, finiteMarkovComplement X Xc R hRp D, Hi, Dc, ε, poissonCollarDensity ε hε, p,
    hε, hεδ2,
    fun k => ⟨poissonCollarDensity_contDiff ε hε k, poissonCollarDensity_hasCompactSupport ε hε k,
      tsupport_poissonCollarDensity_subset ε hε k, poissonCollarDensity_nonneg ε hε k,
      integral_poissonCollarDensity ε hε k⟩,
    fun i z hz k => by
      rw [hp i z hz k]
      exact ⟨fun _ => rfl, tsupport_poissonCollarTest_exterior c ρ (ε / ((k : ℝ) + 1)) δ hρ
        ((poissonCollarWidth_le ε hε k).trans_lt hεδ2) hsep i z hz _
        (poissonCollarDensity_contDiff ε hε k) (tsupport_poissonCollarDensity_subset ε hε k)⟩,
    fun i z hz => by simpa only [hp i z hz] using hHilim i z hz,
    fun i => ⟨hDG i, fun f => ⟨hDm i f, hDmem i f, hDmean i f⟩, hDcov i⟩,
    hHG,
    fun f => ⟨measurable_finiteMarkovComplement_apply P X Xc hX hc R hRp D hDm f,
      finiteMarkovComplement_apply_memLp P X Xc hX hc R hRp D hDmem f,
      finiteMarkovComplement_apply_integral_zero P X Xc hX hc R hRp D hDmem hDmean f⟩,
    hHim,
    fun i z hz => ⟨hHimem i z hz, hHimean i z hz⟩,
    hHicov, ?_, hblocks, hexind,
    fun i l hl => exteriorPinned_harmonic_uniform_moments P X Xc hX hc (c i) R ρ a hR hρ haρ
      (Hi i) (hHim i) (hHih i) (hHiG i) (hHimem i) (hHimean i) (hHicov i) l hl,
    hDcm, hDcG, hDc, hDccov⟩
  filter_upwards [ae_finiteMarkovComplement_restoration P X Xc hc R hRp D,
    ae_all_iff.2 hHih, hHlocal, ae_all_iff.2 hDext] with ω hrestore hh hhl hde
  exact ⟨finiteMarkovComplement_decomposition X Xc R hRp D ω, hrestore, hh, hhl, hde⟩

end DOZZ.Proofs
