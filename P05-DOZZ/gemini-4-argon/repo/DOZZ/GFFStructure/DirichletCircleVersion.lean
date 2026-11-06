/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GFFStructure.DirichletCircleLimits
/-!
# Actual Dirichlet circle versions

Interior smooth test limits identify the circle residual in the original L² carrier.
The raw distribution sigma algebra supports a jointly measurable Gaussian version,
and the completed test and circle variables are orthogonal to the harmonic field.
-/

@[expose] public section
open Filter MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped Topology ENNReal NNReal
namespace DOZZ.Proofs
/-- An interior circle and its closed disk stay in the original harmonic disk. -/
theorem interior_circle_closedBall_subset (c x : ℂ) (ρ r : ℝ)
    (hx : ‖x-c‖+Real.exp (-r) < ρ) : closedBall x |Real.exp (-r)| ⊆ ball c ρ := by
  intro z hz
  have hn := mem_closedBall_iff_norm.mp hz
  rw [abs_of_pos (Real.exp_pos _)] at hn
  exact mem_ball_iff_norm.mpr (by linarith only [(by simpa only [sub_add_sub_cancel] using norm_add_le (z-x) (x-c)),hn,hx])


/-- Circle residuals in the original random L² space, with the literal exterior pin subtracted. -/
noncomputable def dirichletCircleResidualL2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hc : IsCircleAverage P X Xc) (c : ℂ) (R ρ : ℝ)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (x : ℂ) (r : ℝ) : Lp ℝ 2 P :=
  circleAverageL2 hc (x,r)-poissonFamilyL2 P c ρ V hV x-circleAverageL2 hc (0,-Real.log R)

/-- The circle residual has exactly the literal restoration formula. -/
theorem dirichletCircleResidualL2_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    hc c R ρ (hR : 0 < R)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    x r (hx : x ∈ ball c ρ) :
    (⇑(dirichletCircleResidualL2 P X Xc hc c R ρ V hV x r)) =ᵐ[P]
      fun ω => Xc ω x r-V ω x+equatorRestorationScalar Xc R hR ω := by
  filter_upwards [circleAverageL2_ae_eq hc (x,r),circleAverageL2_ae_eq hc (0,-Real.log R),
    poissonFamilyL2_ae_eq P c ρ V hV x hx,equatorRestorationScalar_ae_eq_neg_circle X Xc hc R hR,
    Lp.coeFn_sub (circleAverageL2 hc (x,r)) (poissonFamilyL2 P c ρ V hV x),
    Lp.coeFn_sub (circleAverageL2 hc (x,r)-poissonFamilyL2 P c ρ V hV x) (circleAverageL2 hc (0,-Real.log R))]
    with ω hxc hpin hVx hrest hsub hsub2
  rw [dirichletCircleResidualL2,hsub2,Pi.sub_apply,hsub,Pi.sub_apply,hxc,hVx,hpin,hrest]
  ring


/-- Actual completed Dirichlet test variables converge to the literal interior circle residual. -/
theorem exists_dirichletCompletedL2Map_circle_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    hX hc
    c (R ρ ε : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε) (hpin : ‖c‖+ρ ≤ R)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hmean : ∀ z ∈ ball c ρ, (∫ ω, V ω z ∂P) = 0)
    hU
    (hcov : ∀ z w, z ∈ ball c ρ → w ∈ ball c ρ →
      covariance (fun ω => V ω z) (fun ω => V ω w) P = Real.log R+Real.log ρ-
        Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖)
    (hlim : ∀ z (hz : z ∈ ball c ρ), Tendsto (fun k => eLpNorm
      (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
        (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0))
    (hVm : Measurable (fun p : Ω × ℂ => V p.1 p.2))
    (hVh : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (V ω) (ball c ρ))
    x r (hx : ‖x-c‖+Real.exp (-r) < ρ) :
    ∃ f : ℕ → TestFn, (∀ᶠ n in atTop, tsupport (f n) ⊆ ball c ρ) ∧
      Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0) ∧
      Tendsto (fun n => dirichletCompletedL2Map P X Xc hX hc c R ρ (by linarith) V hV hU
        (diskTestRestrictionL2 c ρ (f n))) atTop
        (𝓝 (dirichletCircleResidualL2 P X Xc hc c R ρ V hV x r)) := by
  have tendsto_exteriorPinnedTestL2_circle (hR : 0 < R) x r (f : ℕ → TestFn) (henergy : Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0)) (hmass : Tendsto (fun n => ∫ z : ℂ, f n z) atTop (𝓝 1)) : Tendsto (fun n => exteriorPinnedTestL2 P X Xc hX hc R hR (f n)) atTop (𝓝 (circleAverageL2 hc (x,r)-circleAverageL2 hc (0,-Real.log R))) := by
    let _ := hX.1
    have he n : exteriorPinnedTestL2 P X Xc hX hc R hR (f n) =
        (equatorGFF_test_memLp X hX (f n)).toLp (fun ω => X ω (f n))-
          (∫ z : ℂ, f n z) • circleAverageL2 hc (0,-Real.log R) := by
      apply Lp.ext
      filter_upwards [exteriorPinnedTestL2_ae_eq P X Xc hX hc R hR (f n),
        (equatorGFF_test_memLp X hX (f n)).coeFn_toLp,circleAverageL2_ae_eq hc (0,-Real.log R),
        Lp.coeFn_smul (∫ z : ℂ, f n z) (circleAverageL2 hc (0,-Real.log R)),
        Lp.coeFn_sub ((equatorGFF_test_memLp X hX (f n)).toLp (fun ω => X ω (f n)))
          ((∫ z : ℂ, f n z) • circleAverageL2 hc (0,-Real.log R))] with ω hy ht hp hs hsub
      rw [hsub,Pi.sub_apply,hs,Pi.smul_apply,smul_eq_mul,ht,hp,hy]
      unfold exteriorPinnedEvaluation
      ring
    simp_rw [he]
    simpa only [circleAverageL2,one_smul] using (tendsto_toLp_of_eLpNorm_sub (fun n => equatorGFF_test_memLp X hX (f n)) (hc.2.1 x r) (hc.2.2 x r f henergy)).sub (hmass.smul (tendsto_const_nhds : Tendsto (fun _ => circleAverageL2 hc (0,-Real.log R)) atTop (𝓝 _)))
  have exists_interior_circle_testFn_poisson_integral_limit (P : Measure Ω) [IsProbabilityMeasure P] c x (ρ : ℝ) (r : ℝ) (hx : ‖x-c‖+Real.exp (-r) < ρ) (V : Ω → ℂ → ℝ) (hVm : Measurable (fun p : Ω × ℂ => V p.1 p.2)) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P) (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ)) (hVh : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (V ω) (ball c ρ)) : ∃ f : ℕ → TestFn, (∀ᶠ n in atTop, tsupport (f n) ⊆ ball c ρ) ∧ Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0) ∧ Tendsto (fun n => ∫ z : ℂ, f n z) atTop (𝓝 1) ∧ Tendsto (fun n => poissonTestIntegralL2 P c ρ V hV (f n)) atTop (𝓝 (poissonFamilyL2 P c ρ V hV x)) := by
    have poissonFamilyL2_circleAverage_eq : Real.circleAverage (poissonFamilyL2 P c ρ V hV) x (Real.exp (-r)) = poissonFamilyL2 P c ρ V hV x := by
      have hsub := interior_circle_closedBall_subset c x ρ r hx
      apply Lp.ext
      filter_upwards [(circleAverage_L2_ae_eq P x (Real.exp (-r)) (Real.exp_pos _).le _ ((hU.mono (sphere_subset_closedBall.trans hsub)).circleIntegrable') (fun z ω => V ω z) (hVm.comp measurable_swap) (fun z hz => poissonFamilyL2_ae_eq P c ρ V hV z (hsub (by simpa only [abs_of_pos (Real.exp_pos _)] using sphere_subset_closedBall hz)))),poissonFamilyL2_ae_eq P c ρ V hV x (mem_ball_iff_norm.mpr (by linarith [Real.exp_pos (-r)])),hVh] with ω hav hxv hω
      rw [hav,hxv]
      exact (hω.mono hsub).circleAverage_eq
    obtain ⟨b,hxb,hbρ⟩ := exists_between hx
    obtain ⟨d,hbd,hdρ⟩ := exists_between hbρ
    let φ : ContDiffBump c := ⟨b,d,((add_pos_of_nonneg_of_pos (norm_nonneg _) (Real.exp_pos _)).trans hxb),hbd⟩
    let ψ : TestFn := ⟨φ,φ.contDiff,φ.hasCompactSupport,subset_univ _⟩
    let U := poissonFamilyL2 P c ρ V hV
    let W : ℂ → Lp ℝ 2 P := fun z => ψ z • U z
    have hW := continuous_testFn_smul_on_disk c ρ U hU ψ (φ.tsupport_eq.subset.trans (closedBall_subset_ball hdρ))
    obtain ⟨M,hM⟩ := (ψ.hasCompactSupport.smul_right).exists_bound_of_continuous hW
    obtain ⟨f,hs,he,hinner⟩ := exists_circleAnnular_testFn_eventually_interior c x b r hxb
    have hδ : Tendsto (fun n : ℕ => 1/((n : ℝ)+2)) atTop (𝓝 (0 : ℝ)) := by
      convert (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 2) using 1
      ext n
      simp only [Function.comp_def,Nat.cast_add,Nat.cast_ofNat]
    have hε : Tendsto (fun n : ℕ => 1/((n : ℝ)+2)^3) atTop (𝓝 (0 : ℝ)) := by
      simpa only [div_pow,one_pow,zero_pow (by norm_num : (3 : ℕ) ≠ 0)] using hδ.pow 3
    have hρs n := (support_circleAnnularDensity_subset x r n).trans
        (closedBall_subset_closedBall (by linarith : ‖x‖+2*Real.exp (-r) ≤ ‖x‖+2*Real.exp (-r)+1))
    have ht := tendsto_integral_testFn_smul_of_circleAnnular_approx x r f _ (fun n => by positivity) hε
      (by positivity : 0 < ‖x‖+2*Real.exp (-r)+1) (fun n => (subset_tsupport _).trans (hs n)) hρs
      (fun n z => (he n z).le) W hW hM
    have hmean : Real.circleAverage W x (Real.exp (-r)) = U x := by
      change Real.circleAverage W x (Real.exp (-r)) = poissonFamilyL2 P c ρ V hV x
      rw [← poissonFamilyL2_circleAverage_eq]
      apply Real.circleAverage_congr_sphere
      intro z hz
      change φ z • U z = U z
      rw [φ.one_of_mem_closedBall (show z ∈ closedBall c b by exact mem_closedBall_iff_norm.mpr (by linarith only [(by simpa only [mem_sphere_iff_norm,abs_of_pos (Real.exp_pos _)] using hz),(by simpa only [sub_add_sub_cancel] using norm_add_le (z-x) (x-c)),hxb])),one_smul]
    rw [hmean] at ht
    have heq : (fun n => ∫ z, f n z • W z) =ᶠ[atTop] fun n => poissonTestIntegralL2 P c ρ V hV (f n) := by
      filter_upwards [hinner] with n hn
      apply congrArg (fun F : ℂ → Lp ℝ 2 P => ∫ z, F z)
      funext z
      by_cases hz : f n z = 0
      · simp only [hz,zero_smul]
      · have hz' := ball_subset_closedBall (hn (subset_closure hz))
        change f n z • (φ z • U z) = f n z • U z
        rw [φ.one_of_mem_closedBall hz',one_smul]
    refine ⟨f,hinner.mono (fun n hn => hn.trans (ball_subset_ball hbρ.le)),
      tendsto_circleEnergyGap_of_cubic_approx x r f hs he,?_,ht.congr' heq⟩
    let _ := circleMeasure_isProbability x r
    simpa only [mul_one,integral_const,probReal_univ,one_smul] using (tendsto_integral_testFn_mul_of_circleAnnular_approx x r f _ (fun n => by positivity) hε (by positivity : 0 < ‖x‖+2*Real.exp (-r)+1) (fun n => (subset_tsupport _).trans (hs n)) hρs (fun n z => (he n z).le) (fun _ => 1) continuous_const)
  let _ := hX.1
  obtain ⟨f,hf,henergy,hmass,hJ⟩ := exists_interior_circle_testFn_poisson_integral_limit
    P c x ρ r hx V hVm hV hU hVh
  have hres : Tendsto (fun n => dirichletResidualL2 P X Xc hX hc c R ρ (by linarith) V hV (f n)) atTop
      (𝓝 (dirichletCircleResidualL2 P X Xc hc c R ρ V hV x r)) := by
    have ht := (tendsto_exteriorPinnedTestL2_circle (by linarith) x r f henergy hmass).sub hJ
    rw [(show (circleAverageL2 hc (x,r)-circleAverageL2 hc (0,-Real.log R))- poissonFamilyL2 P c ρ V hV x = dirichletCircleResidualL2 P X Xc hc c R ρ V hV x r by unfold dirichletCircleResidualL2; abel)] at ht
    exact ht
  refine ⟨f,hf,henergy,hres.congr' ?_⟩
  filter_upwards [hf] with n hn
  exact (dirichletCompletedL2Map_apply_interior P X Xc hX hc c R ρ ε hR hρ hε hpin
    V hV hmean hU hcov hlim (f n) hn).symm

/-- Coordinatewise versions of convergent L² variables satisfy the literal raw error contract. -/
theorem tendsto_eLpNorm_sub_of_L2_versions {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : ℕ → Lp ℝ 2 P) (W : Lp ℝ 2 P)
    (u : ℕ → Ω → ℝ) w
    (hu : ∀ n, u n =ᵐ[P] ⇑(U n)) (hw : w =ᵐ[P] ⇑W)
    (hlim : Tendsto U atTop (𝓝 W)) :
    Tendsto (fun n => eLpNorm (fun ω => u n ω-w ω) 2 P) atTop (𝓝 0) := by
  have he n : eLpNorm (fun ω => u n ω-w ω) 2 P = eLpNorm (⇑(U n)-⇑W) 2 P := by
    apply eLpNorm_congr_ae
    exact (hu n).sub hw
  simp_rw [he]
  exact ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' U W).mp hlim)

/-- The actual Dirichlet distribution admits a joint circle version for its raw evaluation sigma algebra. -/
theorem exists_dirichletDistribution_raw_circle_version {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    hX hc
    c (R ρ ε : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε) (hpin : ‖c‖+ρ ≤ R)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hmean : ∀ z ∈ ball c ρ, (∫ ω, V ω z ∂P) = 0)
    hU
    (hcov : ∀ z w, z ∈ ball c ρ → w ∈ ball c ρ →
      covariance (fun ω => V ω z) (fun ω => V ω w) P = Real.log R+Real.log ρ-
        Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖)
    (hlim : ∀ z (hz : z ∈ ball c ρ), Tendsto (fun k => eLpNorm
      (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
        (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0))
    (hVm : Measurable (fun p : Ω × ℂ => V p.1 p.2))
    (hVh : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (V ω) (ball c ρ) ∧ ContinuousOn (V ω) (ball c ρ)) :
    ∃ Dc : Ω → ℂ → ℝ → ℝ,
      Measurable[(MeasurableSpace.comap
        (fun ω => fun f : TestFn => dirichletDistribution P X Xc hX hc c R ρ (by linarith) V hV hU ω f)
        MeasurableSpace.pi).prod inferInstance] (fun p : Ω × (ℂ × ℝ) => Dc p.1 p.2.1 p.2.2) ∧
      (∀ x r, ‖x-c‖+Real.exp (-r) < ρ → (fun ω => Dc ω x r) =ᵐ[P]
        ⇑(dirichletCircleResidualL2 P X Xc hc c R ρ V hV x r)) := by
  let _ := hX.1
  obtain ⟨Y,hy,hym,hyc,hye⟩ := exists_continuous_circleAverage P X Xc hX hc
  let F : Ω → ℂ → ℝ → ℝ := fun ω x r => Y ω x r-V ω x+equatorRestorationScalar Xc R (by linarith) ω
  let D := dirichletDistribution P X Xc hX hc c R ρ (by linarith) V hV hU
  let m0 := MeasurableSpace.comap (fun ω => fun f => D ω f) MeasurableSpace.pi
  let : MeasurableSpace Ω := mΩ
  have hFae x r (hx : ‖x-c‖+Real.exp (-r) < ρ) :
      (fun ω => F ω x r) =ᵐ[P] ⇑(dirichletCircleResidualL2 P X Xc hc c R ρ V hV x r) := by
    filter_upwards [hye x r,dirichletCircleResidualL2_ae_eq P X Xc hc c R ρ (by linarith) V hV x r (mem_ball_iff_norm.mpr (by linarith [Real.exp_pos (-r)]))]
      with ω hY hC
    change Y ω x r-V ω x+equatorRestorationScalar Xc R (by linarith) ω = _
    rw [hY,hC]
  have hcoord (p : {p : ℂ × ℝ // ‖p.1-c‖+Real.exp (-p.2) < ρ}) :
      ∃ g : Ω → ℝ, Measurable[m0] g ∧ g =ᵐ[P] fun ω => F ω p.1.1 p.1.2 := by
    obtain ⟨f,_hf,_henergy,ht⟩ := exists_dirichletCompletedL2Map_circle_limit P X Xc hX hc c R ρ ε
      hR hρ hε hpin V hV hmean hU hcov hlim hVm (hVh.mono (fun _ h => h.1)) p.1.1 p.1.2 p.2
    apply exists_raw_distribution_limit_version P D f (fun ω => F ω p.1.1 p.1.2)
      (fun n => dirichletDistribution_apply_memLp P X Xc hX hc c R ρ (by linarith) V hV hU (f n)) ((Lp.memLp (dirichletCircleResidualL2 P X Xc hc c R ρ V hV p.1.1 p.1.2)).ae_eq (hFae p.1.1 p.1.2 p.2).symm)
    exact tendsto_eLpNorm_sub_of_L2_versions P _ _ _ _
      (fun n => dirichletDistribution_apply_ae_eq P X Xc hX hc c R ρ (by linarith) V hV hU (f n))
      (hFae p.1.1 p.1.2 p.2) ht
  obtain ⟨Dc,hDcm,hDce⟩ := exists_raw_joint_circle_modification P m0 c ρ F (by filter_upwards [hyc,hVh] with ω hYω hVω; exact ((hYω.comp continuous_subtype_val).sub (hVω.2.comp_continuous (continuous_fst.comp continuous_subtype_val) (fun p => mem_ball_iff_norm.mpr (by linarith [p.2,Real.exp_pos (-p.1.2)])) : Continuous (fun p : {p : ℂ × ℝ // ‖p.1-c‖+Real.exp (-p.2) < ρ} => V ω p.1.1))).add continuous_const) hcoord
  refine ⟨Dc,hDcm,fun x r hx => ?_⟩
  have he : (fun ω => Dc ω x r) =ᵐ[P] fun ω => F ω x r :=
    hDce.mono (fun ω hω => hω x r hx)
  exact he.trans (hFae x r hx)




/-- Actual raw-sigma Dirichlet circle versions retain Gaussianity, centering and the literal restored split. -/
theorem exists_dirichletDistribution_circle_gaussian_split {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    hX hc
    c (R ρ ε : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε) (hpin : ‖c‖+ρ ≤ R)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hmean : ∀ z ∈ ball c ρ, (∫ ω, V ω z ∂P) = 0)
    hU
    (hcov : ∀ z w, z ∈ ball c ρ → w ∈ ball c ρ →
      covariance (fun ω => V ω z) (fun ω => V ω w) P = Real.log R+Real.log ρ-
        Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖)
    (hlim : ∀ z (hz : z ∈ ball c ρ), Tendsto (fun k => eLpNorm
      (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
        (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0))
    (hVm : Measurable (fun p : Ω × ℂ => V p.1 p.2))
    (hVh : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (V ω) (ball c ρ) ∧ ContinuousOn (V ω) (ball c ρ)) :
    ∃ Dc : Ω → ℂ → ℝ → ℝ,
      Measurable[(MeasurableSpace.comap
        (fun ω => fun f : TestFn => dirichletDistribution P X Xc hX hc c R ρ (by linarith) V hV hU ω f)
        MeasurableSpace.pi).prod inferInstance] (fun p : Ω × (ℂ × ℝ) => Dc p.1 p.2.1 p.2.2) ∧
      IsGaussianProcess (fun p : {p : ℂ × ℝ // ‖p.1-c‖+Real.exp (-p.2) < ρ} => fun ω => Dc ω p.1.1 p.1.2) P ∧
      (∀ x r, ‖x-c‖+Real.exp (-r) < ρ → MemLp (fun ω => Dc ω x r) 2 P ∧
        (∫ ω, Dc ω x r ∂P) = 0 ∧
        (fun ω => Xc ω x r) =ᵐ[P] fun ω => Dc ω x r+V ω x-equatorRestorationScalar Xc R (by linarith) ω) ∧
      (∀ x r, ‖x-c‖+Real.exp (-r) < ρ → (fun ω => Dc ω x r) =ᵐ[P]
        ⇑(dirichletCircleResidualL2 P X Xc hc c R ρ V hV x r)) := by
  have dirichletCircleResidualL2_isGaussianProcess (hR : 0 < R) (hρ : 0 < ρ) (hε : 0 < ε) (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P) (hlim : ∀ z (hz : z ∈ ball c ρ), Tendsto (fun k => eLpNorm (fun ω => exteriorPinnedEvaluation X Xc R hR ω (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0)) : IsGaussianProcess (fun p : {p : ℂ × ℝ // ‖p.1-c‖+Real.exp (-p.2) < ρ} => ⇑(dirichletCircleResidualL2 P X Xc hc c R ρ V hV p.1.1 p.1.2)) P := by
    have dirichletCircleResidualL2_mem_original_gaussianHilbertSpan (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ) hX hc c R ρ ε (hR : 0 < R) (hρ : 0 < ρ) (hε : 0 < ε) (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P) (hlim : ∀ z (hz : z ∈ ball c ρ), Tendsto (fun k => eLpNorm (fun ω => exteriorPinnedEvaluation X Xc R hR ω (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0)) x r : dirichletCircleResidualL2 P X Xc hc c R ρ V hV x r ∈ gaussianHilbertSpan (gffStructureL2Family X Xc hX hc) := by
      unfold dirichletCircleResidualL2
      apply Submodule.sub_mem
      · apply Submodule.sub_mem
        · exact mem_gaussianHilbertSpan (gffStructureL2Family X Xc hX hc) (Sum.inl (x,r))
        · exact poissonFamilyL2_mem_original_gaussianHilbertSpan P X Xc hX hc c R ρ ε hR hρ hε V hV hlim x
      · exact mem_gaussianHilbertSpan (gffStructureL2Family X Xc hX hc) (Sum.inl (0,-Real.log R))
    let _ := hX.1
    exact isGaussianProcess_of_mem_gaussianHilbertSpan (gffStructureL2Family_isGaussianProcess X Xc hX hc)
      _ (fun p => dirichletCircleResidualL2_mem_original_gaussianHilbertSpan
        P X Xc hX hc c R ρ ε hR hρ hε V hV hlim p.1.1 p.1.2)
  have dirichletCircleResidualL2_integral_zero x r (hx : x ∈ ball c ρ) : (∫ ω, dirichletCircleResidualL2 P X Xc hc c R ρ V hV x r ω ∂P) = 0 := by
    let _ := hX.1
    have hcircle p : (∫ ω, circleAverageL2 hc p ω ∂P) = 0 := by
      rw [integral_congr_ae (circleAverageL2_ae_eq hc p)]
      exact (circleAverage_isGaussianProcess P X Xc hX hc).2 p.1 p.2
    have integral_sub_L2 (U W : Lp ℝ 2 P) : (∫ ω, (U-W) ω ∂P) = (∫ ω, U ω ∂P)-(∫ ω, W ω ∂P) := by
      rw [integral_congr_ae (Lp.coeFn_sub U W)]
      exact integral_sub (Lp.memLp U |>.integrable (by norm_num)) (Lp.memLp W |>.integrable (by norm_num))
    rw [dirichletCircleResidualL2,integral_sub_L2,integral_sub_L2,hcircle,hcircle,(show (∫ ω, poissonFamilyL2 P c ρ V hV x ω ∂P) = 0 by rw [integral_congr_ae (poissonFamilyL2_ae_eq P c ρ V hV x hx)]; exact hmean x hx),sub_self,sub_self]
  obtain ⟨Dc,hDcm,hDce⟩ := exists_dirichletDistribution_raw_circle_version P X Xc hX hc c R ρ ε
    hR hρ hε hpin V hV hmean hU hcov hlim hVm hVh
  refine ⟨Dc,hDcm,?_,?_,hDce⟩
  · exact (dirichletCircleResidualL2_isGaussianProcess (by linarith) hρ hε V hV hlim).congr
      (fun p => (hDce p.1.1 p.1.2 p.2).symm)
  · intro x r hx
    have hx' : x ∈ ball c ρ := mem_ball_iff_norm.mpr (by linarith [Real.exp_pos (-r)])
    refine ⟨(Lp.memLp (dirichletCircleResidualL2 P X Xc hc c R ρ V hV x r)).ae_eq (hDce x r hx).symm,?_,?_⟩
    · rw [integral_congr_ae (hDce x r hx)]
      exact dirichletCircleResidualL2_integral_zero x r hx'
    · filter_upwards [hDce x r hx,dirichletCircleResidualL2_ae_eq P X Xc hc c R ρ (by linarith) V hV x r hx']
        with ω hDc hC
      rw [hDc,hC]
      ring


/-- Every interior circle residual is orthogonal to all harmonic point variables. -/
theorem dirichletCircleResidualL2_poisson_covariance_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) hc
    c (R ρ ε : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε) (hpin : ‖c‖+ρ ≤ R)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hmean : ∀ z ∈ ball c ρ, (∫ ω, V ω z ∂P) = 0)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ))
    (hcov : ∀ z w, z ∈ ball c ρ → w ∈ ball c ρ →
      covariance (fun ω => V ω z) (fun ω => V ω w) P = Real.log R+Real.log ρ-
        Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖)
    (hlim : ∀ z (hz : z ∈ ball c ρ), Tendsto (fun k => eLpNorm
      (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
        (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0))
    (hVm : Measurable (fun p : Ω × ℂ => V p.1 p.2))
    (hVh : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (V ω) (ball c ρ))
    x r (hx : ‖x-c‖+Real.exp (-r) < ρ) z (hz : z ∈ ball c ρ) :
    covariance (dirichletCircleResidualL2 P X Xc hc c R ρ V hV x r)
      (poissonFamilyL2 P c ρ V hV z) P = 0 := by
  have dirichletCompletedL2Map_poisson_covariance_zero (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P) (hmean : ∀ z ∈ ball c ρ, (∫ ω, V ω z ∂P) = 0) hU (hcov : ∀ z w, z ∈ ball c ρ → w ∈ ball c ρ → covariance (fun ω => V ω z) (fun ω => V ω w) P = Real.log R+Real.log ρ- Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖) (hlim : ∀ z (hz : z ∈ ball c ρ), Tendsto (fun k => eLpNorm (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0)) f z (hz : z ∈ ball c ρ) : covariance (dirichletCompletedL2Map P X Xc hX hc c R ρ (by linarith) V hV hU (diskTestRestrictionL2 c ρ f)) (poissonFamilyL2 P c ρ V hV z) P = 0 := by
    let _ := hX.1
    rw [poissonFamilyL2,dite_eq_left hz]
    apply covariance_L2_limit_right_eq_zero P _ _
      (fun k => exteriorPinnedTestL2 P X Xc hX hc R (by linarith)
        (canonicalPoissonCollarTest c z ρ ε hρ hε hz k))
    · exact tendsto_toLp_of_eLpNorm_sub
        (fun k => exteriorPinnedEvaluation_memLp X Xc hX hc R (by linarith) _) (hV z hz) (hlim z hz)
    · intro k
      apply dirichletCompletedL2Map_exterior_covariance_zero P X Xc hX hc c R ρ ε hR hρ hε hpin
        V hV hmean hU hcov hlim f
      intro w hw hc'
      exact ((tsupport_poissonCollarValue_annulus c z ρ (ε/((k : ℝ)+1)) hρ hz (poissonCollarDensity ε hε k) (tsupport_poissonCollarDensity_subset ε hε k) hw).1.not_ge (mem_closedBall_iff_norm.mp hc'))
  let _ := hX.1
  obtain ⟨f,_hf,_henergy,ht⟩ := exists_dirichletCompletedL2Map_circle_limit P X Xc hX hc c R ρ ε
    hR hρ hε hpin V hV hmean hU hcov hlim hVm hVh x r hx
  rw [covariance_comm]
  apply covariance_L2_limit_right_eq_zero P _ _
    (fun n => dirichletCompletedL2Map P X Xc hX hc c R ρ (by linarith) V hV hU
      (diskTestRestrictionL2 c ρ (f n))) ht
  intro n
  rw [covariance_comm]
  exact dirichletCompletedL2Map_poisson_covariance_zero
    V hV hmean hU hcov hlim (f n) z hz


end DOZZ.Proofs
