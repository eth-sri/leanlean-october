/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GFFStructure.PoissonContracts
public import DOZZ.GFFStructure.DirichletResidual
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Normed.Operator.Extend
/-!
# Completion of the interior Dirichlet field

Compact smooth tests supported inside a disk are dense in its area L² space.
The actual residual of the exterior-pinned field and its Poisson harmonic part
therefore extends to a bounded map on all disk restrictions. Its values retain
the original Gaussian Hilbert span and vanish on exterior tests.
-/

@[expose] public section
open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped Topology ENNReal NNReal
namespace DOZZ.Proofs

/-- A test's actual disk restriction in area L². -/
noncomputable def diskTestRestrictionL2 (c : ℂ) (ρ : ℝ) (f : TestFn) :
    Lp ℝ 2 (volume.restrict (ball c ρ)) :=
  (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).toLp f

/-- The disk restriction representative retains the original test. -/
theorem diskTestRestrictionL2_ae_eq (c : ℂ) (ρ : ℝ) (f : TestFn) :
    diskTestRestrictionL2 c ρ f =ᵐ[volume.restrict (ball c ρ)] (f : ℂ → ℝ) := MemLp.coeFn_toLp _

/-- The norm squared of a disk restriction is the literal area integral. -/
theorem diskTestRestrictionL2_norm_sq (c : ℂ) (ρ : ℝ) (f : TestFn) :
    ‖diskTestRestrictionL2 c ρ f‖^2 = ∫ z in ball c ρ, (f z)^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [diskTestRestrictionL2_ae_eq c ρ f] with z hz
  simp_all

/-- Smooth compactly supported tests entirely inside a disk approximate each test restriction. -/
theorem exists_interior_test_restriction_approx (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (f : TestFn) :
    ∃ g : ℕ → TestFn, (∀ n, tsupport (g n) ⊆ ball c ρ) ∧
      Tendsto (fun n => diskTestRestrictionL2 c ρ (g n)) atTop (𝓝 (diskTestRestrictionL2 c ρ f)) := by
  let d (j : ℕ) := ρ-ρ/((j : ℝ)+2)
  let b (j : ℕ) := (d j+ρ)/2
  have hd j : 0 < d j ∧ d j < b j ∧ b j < ρ := by
    have hj : 1 < (j : ℝ)+2 := by bound
    have hp : 0 < ρ/((j : ℝ)+2) := div_pos hρ (by positivity)
    have hq  := div_lt_self hρ hj
    grind
  let B (j : ℕ) : ContDiffBump c := ⟨d j,b j,(hd j).1,(hd j).2.1⟩
  let g (j : ℕ) : TestFn := ⟨fun z => B j z*f z,(B j).contDiff.mul f.contDiff,
    (B j).hasCompactSupport.mul_right,subset_univ _⟩
  have hs j : tsupport (g j) ⊆ ball c ρ := (tsupport_mul_subset_left (f := B j)).trans (by
      rw [(B j).tsupport_eq]
      exact closedBall_subset_ball (hd j).2.2)
  refine ⟨g,hs,?_⟩
  have hlim : Tendsto d atTop (𝓝 ρ) := by
    have hr : Tendsto (fun j : ℕ => ρ/((j : ℝ)+2)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    simpa only [d,sub_zero] using (tendsto_const_nhds.sub hr :
      Tendsto (fun j : ℕ => ρ-ρ/((j : ℝ)+2)) atTop (𝓝 (ρ-0)))
  let μ := volume.restrict (ball c ρ)
  have hfi : MemLp (f : ℂ → ℝ) 2 μ := f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  have hib  := hfi.integrable_sq
  have hv : Tendsto (fun j => ∫ z, (g j z-f z)^2 ∂μ) atTop (𝓝 0) := by
    have heq : (∫ z, (0 : ℝ) ∂μ) = 0 := by simp only [integral_zero]
    rw [← heq]
    apply tendsto_integral_of_dominated_convergence (fun z => (f z)^2)
    · fun_prop (disch := positivity)
    · exact hib
    · intro j
      apply ae_of_all
      intro z
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hb : (B j z-1)^2 ≤ 1 := by nlinarith [(B j).nonneg' z,(B j).le_one (x := z)]
      have hh := mul_le_mul_of_nonneg_right hb (sq_nonneg (f z))
      change (B j z*f z-f z)^2 ≤ (f z)^2
      nlinarith [hh]
    · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      have he  := hlim.eventually (Ioi_mem_nhds (mem_ball_iff_norm.mp hz))
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with j hj
      have hB  := (B j).one_of_mem_closedBall (mem_closedBall_iff_norm.mpr hj.le)
      change (0 : ℝ) = (B j z*f z-f z)^2
      simp_all
  have hn : Tendsto (fun j => ‖diskTestRestrictionL2 c ρ (g j)-diskTestRestrictionL2 c ρ f‖^2) atTop (𝓝 0) := by
    convert hv using 1
    funext j
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (diskTestRestrictionL2 c ρ (g j)) (diskTestRestrictionL2 c ρ f),
      diskTestRestrictionL2_ae_eq c ρ (g j),diskTestRestrictionL2_ae_eq c ρ f] with z hsub hg hf
    simp_all
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hh

/-- Compact interior test restrictions are dense in the full disk area L² space. -/
theorem dense_interior_diskTestRestrictions (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    Dense {u : Lp ℝ 2 (volume.restrict (ball c ρ)) |
      ∃ f : TestFn, tsupport f ⊆ ball c ρ ∧ u = diskTestRestrictionL2 c ρ f} := by
  let μ := volume.restrict (ball c ρ)
  have hglobal : Dense {u : Lp ℝ 2 μ | ∃ f : TestFn, u = diskTestRestrictionL2 c ρ f} := by
    apply (Lp.dense_hasCompactSupport_contDiff (F := ℝ) (μ := μ) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mono
    rintro u ⟨f,he,hf,hc⟩
    let g : TestFn := ⟨f,hc.of_le (by simp),hf,subset_univ _⟩
    refine ⟨g,?_⟩
    apply Lp.ext
    exact he.trans (diskTestRestrictionL2_ae_eq c ρ g).symm
  have hsub : {u : Lp ℝ 2 μ | ∃ f : TestFn, u = diskTestRestrictionL2 c ρ f} ⊆
      closure {u : Lp ℝ 2 μ | ∃ f : TestFn, tsupport f ⊆ ball c ρ ∧ u = diskTestRestrictionL2 c ρ f} := by
    rintro u ⟨f,rfl⟩
    obtain ⟨g,hs,ht⟩ := exists_interior_test_restriction_approx c ρ hρ f
    apply isClosed_closure.mem_of_tendsto ht
    exact Eventually.of_forall (fun n => subset_closure ⟨g n,hs n,rfl⟩)
  have hh := hglobal.mono hsub
  continuity

/-- Compact tests whose entire support stays inside one disk form a real linear subspace. -/
def diskInteriorTestSpace (c : ℂ) (ρ : ℝ) : Submodule ℝ TestFn where
  carrier := {f | tsupport f ⊆ ball c ρ}
  zero_mem' := by
    simp_all
  add_mem' := by
    intro f g hf hg
    change tsupport (fun z => f z+g z) ⊆ ball c ρ
    exact (tsupport_add f g).trans (union_subset hf hg)
  smul_mem' := by
    intro a f hf
    change tsupport (fun z => a • f z) ⊆ ball c ρ
    exact (tsupport_smul_subset_right (fun _ : ℂ => a) f).trans hf

/-- Restriction of a global test is linear as a map into disk area L². -/
noncomputable def diskTestRestrictionLinearMap (c : ℂ) (ρ : ℝ) :
    TestFn →ₗ[ℝ] Lp ℝ 2 (volume.restrict (ball c ρ)) where
  toFun := diskTestRestrictionL2 c ρ
  map_add' f g := by
    aesop
  map_smul' a f := by
    aesop

/-- The interior test embedding into disk area L² has dense range. -/
theorem denseRange_diskInteriorTestRestriction (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    DenseRange ((diskTestRestrictionLinearMap c ρ).comp (diskInteriorTestSpace c ρ).subtype) := by
  have he : range ((diskTestRestrictionLinearMap c ρ).comp (diskInteriorTestSpace c ρ).subtype) =
      {u : Lp ℝ 2 (volume.restrict (ball c ρ)) | ∃ f : TestFn, tsupport f ⊆ ball c ρ ∧ u = diskTestRestrictionL2 c ρ f} := by
    ext u
    constructor
    · rintro ⟨f,rfl⟩
      exact ⟨f.1,f.2,rfl⟩
    continuity
  change Dense _
  rw [he]
  exact dense_interior_diskTestRestrictions c ρ hρ

/-- The original exterior-pinned test evaluations are linear in their actual L² carrier. -/
noncomputable def exteriorPinnedTestL2LinearMap {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (R : ℝ) (hR : 0 < R) :
    TestFn →ₗ[ℝ] Lp ℝ 2 P where
  toFun := exteriorPinnedTestL2 P X Xc hX hc R hR
  map_add' f g := by
    apply Lp.ext
    filter_upwards [exteriorPinnedTestL2_ae_eq P X Xc hX hc R hR (f+g),
      exteriorPinnedTestL2_ae_eq P X Xc hX hc R hR f,exteriorPinnedTestL2_ae_eq P X Xc hX hc R hR g,
      Lp.coeFn_add (exteriorPinnedTestL2 P X Xc hX hc R hR f) (exteriorPinnedTestL2 P X Xc hX hc R hR g)] with ω hfg hf hg ha
    rw [hfg,ha,Pi.add_apply,hf,hg]
    simp only [exteriorPinnedEvaluation, map_add,FunLike.coe_add,Pi.add_apply]
    rw [integral_add (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
      (g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport)]
    ring
  map_smul' a f := by
    apply Lp.ext
    filter_upwards [exteriorPinnedTestL2_ae_eq P X Xc hX hc R hR (a • f),
      exteriorPinnedTestL2_ae_eq P X Xc hX hc R hR f,Lp.coeFn_smul a (exteriorPinnedTestL2 P X Xc hX hc R hR f)] with ω haf hf ha
    simp only [RingHom.id_apply]
    rw [haf,ha,Pi.smul_apply,smul_eq_mul,hf]
    simp only [exteriorPinnedEvaluation,map_smul,FunLike.coe_smul,Pi.smul_apply,smul_eq_mul]
    rw [integral_const_mul]
    ring

/-- Harmonic test integration is linear on the interior test subspace. -/
noncomputable def poissonInteriorTestIntegralLinearMap {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (c : ℂ) (ρ : ℝ) (V : Ω → ℂ → ℝ)
    (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ)) :
    diskInteriorTestSpace c ρ →ₗ[ℝ] Lp ℝ 2 P where
  toFun := fun f => poissonTestIntegralL2 P c ρ V hV f.1
  map_add' f g := by
    simp only [poissonTestIntegralL2,Submodule.coe_add,FunLike.coe_add,Pi.add_apply,add_smul]
    exact integral_add (integrable_testFn_smul_on_disk c ρ _ hU f.1 f.2)
      (integrable_testFn_smul_on_disk c ρ _ hU g.1 g.2)
  map_smul' a f := by
    simp only [poissonTestIntegralL2,Submodule.coe_smul,FunLike.coe_smul,Pi.smul_apply,RingHom.id_apply,smul_eq_mul]
    rw [← integral_smul a]
    simp only [smul_smul]

/-- The actual interior residual is a linear map, before restriction completion. -/
noncomputable def dirichletInteriorResidualLinearMap {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ : ℝ) (hR : 0 < R) (V : Ω → ℂ → ℝ)
    (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ)) :
    diskInteriorTestSpace c ρ →ₗ[ℝ] Lp ℝ 2 P :=
  (exteriorPinnedTestL2LinearMap P X Xc hX hc R hR).comp (diskInteriorTestSpace c ρ).subtype-
    poissonInteriorTestIntegralLinearMap P c ρ V hV hU

/-- The genuine residual map completed to all disk area L² restrictions. -/
noncomputable def dirichletCompletedL2Map {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ : ℝ) (hR : 0 < R) (V : Ω → ℂ → ℝ)
    (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ)) :
    Lp ℝ 2 (volume.restrict (ball c ρ)) →L[ℝ] Lp ℝ 2 P :=
  (dirichletInteriorResidualLinearMap P X Xc hX hc c R ρ hR V hV hU).extendOfNorm
    ((diskTestRestrictionLinearMap c ρ).comp (diskInteriorTestSpace c ρ).subtype)

/-- An explicit finite residual completion bound from the genuine Green disk energy. -/
noncomputable def diskGreenCompletionConstant (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) : ℝ :=
  Real.sqrt ((∫ p : ℂ × ℂ, ‖diskGreenKernel c ρ hρ p.1 p.2‖^2
    ∂((volume.restrict (ball c ρ)).prod (volume.restrict (ball c ρ))))^(1/2 : ℝ))

variable {Ω : Type*} [_inst1 : MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (c : ℂ) (R ρ ε : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε) (hpin : ‖c‖+ρ ≤ R) (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P) (hmean : ∀ z ∈ ball c ρ, (∫ ω, V ω z ∂P) = 0) (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ)) (hcov : Contract.poissonCovariance P c R ρ V)

include Ω _inst1 P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hcov in
/-- The actual interior residual map is bounded by the area L² norm of its test restriction. -/
theorem dirichletInteriorResidualLinearMap_bound 
    (hlim : Contract.poissonCollarLimit P X Xc c R ρ ε (by linarith) hρ hε V)
    (f : diskInteriorTestSpace c ρ) :
    ‖dirichletInteriorResidualLinearMap P X Xc hX hc c R ρ (by linarith) V hV hU f‖ ≤
      diskGreenCompletionConstant c ρ hρ*‖diskTestRestrictionL2 c ρ f.1‖ := by
  let K := (∫ p : ℂ × ℂ, ‖diskGreenKernel c ρ hρ p.1 p.2‖^2
    ∂((volume.restrict (ball c ρ)).prod (volume.restrict (ball c ρ))))^(1/2 : ℝ)
  have hK : 0 ≤ K := Real.rpow_nonneg (integral_nonneg (fun _ => sq_nonneg _)) _
  have h := dirichletResidualL2_norm_sq_le P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hcov hlim f.1 f.2
  have hfNorm : (∫ z in ball c ρ, ‖f.1 z‖^2) = ‖diskTestRestrictionL2 c ρ f.1‖^2 := by
    rw [diskTestRestrictionL2_norm_sq]
    simp only [Real.norm_eq_abs,sq_abs]
  rw [hfNorm] at h
  change ‖dirichletResidualL2 P X Xc hX hc c R ρ (by linarith) V hV f.1‖ ≤
    Real.sqrt K*‖diskTestRestrictionL2 c ρ f.1‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg K) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt hK]
  exact h

include Ω _inst1 P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hcov in
/-- The bounded completion equals the actual residual on every compact interior test. -/
theorem dirichletCompletedL2Map_apply_interior 
    (hlim : Contract.poissonCollarLimit P X Xc c R ρ ε (by linarith) hρ hε V)
    (f : TestFn) (hf : tsupport f ⊆ ball c ρ) :
    dirichletCompletedL2Map P X Xc hX hc c R ρ (by linarith) V hV hU (diskTestRestrictionL2 c ρ f) =
      dirichletResidualL2 P X Xc hX hc c R ρ (by linarith) V hV f := LinearMap.extendOfNorm_eq (f := dirichletInteriorResidualLinearMap P X Xc hX hc c R ρ (by linarith) V hV hU)
    (e := (diskTestRestrictionLinearMap c ρ).comp (diskInteriorTestSpace c ρ).subtype)
    (denseRange_diskInteriorTestRestriction c ρ hρ)
    ⟨diskGreenCompletionConstant c ρ hρ,fun f => dirichletInteriorResidualLinearMap_bound
      P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hcov hlim f⟩ ⟨f,hf⟩

/-- A global test exterior to the closed disk has zero disk area restriction. -/
theorem diskTestRestrictionL2_eq_zero_of_exterior (c : ℂ) (ρ : ℝ) (f : TestFn)
    (hf : tsupport f ⊆ (closedBall c ρ)ᶜ) : diskTestRestrictionL2 c ρ f = 0 := by
  apply Lp.ext
  filter_upwards [diskTestRestrictionL2_ae_eq c ρ f,Lp.coeFn_zero ℝ 2 (volume.restrict (ball c ρ)),
    ae_restrict_mem measurableSet_ball] with z he hz hball
  rw [he,hz]
  change f z = 0
  by_contra h
  exact hf (subset_closure h) (ball_subset_closedBall hball)

include Ω _inst1 P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hcov in
/-- The full disk completion stays in the original closed Gaussian Hilbert span. -/
theorem dirichletCompletedL2Map_mem_gaussianHilbertSpan 
    (hlim : Contract.poissonCollarLimit P X Xc c R ρ ε (by linarith) hρ hε V)
    (u : Lp ℝ 2 (volume.restrict (ball c ρ))) :
    dirichletCompletedL2Map P X Xc hX hc c R ρ (by linarith) V hV hU u ∈
      gaussianHilbertSpan (poissonTestFamilyL2 P X Xc hX hc c R ρ (by linarith) V hV) := by
  let _ := hX.1
  refine (denseRange_diskInteriorTestRestriction c ρ hρ).induction ?_ ?_ u
  · rintro _ ⟨f,rfl⟩
    change dirichletCompletedL2Map P X Xc hX hc c R ρ (by linarith) V hV hU
      (diskTestRestrictionL2 c ρ f.1) ∈ _
    rw [dirichletCompletedL2Map_apply_interior P X Xc hX hc c R ρ ε hR hρ hε hpin
      V hV hmean hU hcov hlim f.1 f.2]
    exact dirichletResidualL2_mem_gaussianHilbertSpan P X Xc hX hc c R ρ (by linarith) V hV hU f.1 f.2
  · exact (Submodule.isClosed_topologicalClosure _).preimage
      (dirichletCompletedL2Map P X Xc hX hc c R ρ (by linarith) V hV hU).continuous

include Ω _inst1 P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hcov in
/-- Every jointly indexed collection of completed disk restrictions remains Gaussian. -/
theorem dirichletCompletedL2Map_isGaussianProcess 
    (hlim : Contract.poissonCollarLimit P X Xc c R ρ ε (by linarith) hρ hε V) :
    IsGaussianProcess (fun u : Lp ℝ 2 (volume.restrict (ball c ρ)) =>
      ⇑(dirichletCompletedL2Map P X Xc hX hc c R ρ (by linarith) V hV hU u)) P := by
  let _ := hX.1
  exact isGaussianProcess_of_mem_gaussianHilbertSpan
    (poissonTestFamilyL2_isGaussianProcess P X Xc hX hc c R ρ ε (by linarith) hρ hε V hV hlim) _
    (dirichletCompletedL2Map_mem_gaussianHilbertSpan P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hcov hlim)

/-- A complete disk map is centered whenever its values on the dense interior tests are centered. -/
theorem integral_completed_disk_map_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (T : Lp ℝ 2 (volume.restrict (ball c ρ)) →L[ℝ] Lp ℝ 2 P)
    (hT : ∀ f : TestFn, tsupport f ⊆ ball c ρ → (∫ ω, T (diskTestRestrictionL2 c ρ f) ω ∂P) = 0)
    (u : Lp ℝ 2 (volume.restrict (ball c ρ))) : (∫ ω, T u ω ∂P) = 0 := by
  refine (denseRange_diskInteriorTestRestriction c ρ hρ).induction ?_ ?_ u
  · rintro _ ⟨f,rfl⟩
    exact hT f.1 f.2
  · simp_rw [integral_eq_inner_one]
    exact isClosed_eq ((T.continuous).inner continuous_const) continuous_const

end DOZZ.Proofs
