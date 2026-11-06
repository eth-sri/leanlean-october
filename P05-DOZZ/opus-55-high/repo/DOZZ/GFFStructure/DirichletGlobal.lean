/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GFFStructure.DirichletCompletion
/-!
# Global Dirichlet covariance and independence

The disk area L² completion retains exact Green covariance on all global tests.
Density extends the mixed covariance with the given exterior-pinned realization,
so its global complement and all exterior test evaluations are orthogonal.
The jointly Gaussian Hilbert span turns these identities into independence.
-/

@[expose] public section
open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped Topology ENNReal NNReal
namespace DOZZ.Proofs
section
variable (c : ℂ) (ρ : ℝ)

/-- Restriction preserves test subtraction. -/
theorem diskTestRestrictionL2_sub (f g : TestFn) :
    diskTestRestrictionL2 c ρ (f-g) = diskTestRestrictionL2 c ρ f-diskTestRestrictionL2 c ρ g :=
  by rfl
section
variable (hρ : 0 < ρ)

/-- Green pairing is linear under subtraction of the first test. -/
theorem diskGreenCovariance_sub_left (f g h : TestFn) :
    diskGreenCovariance c ρ hρ (f-g) h =
      diskGreenCovariance c ρ hρ f h-diskGreenCovariance c ρ hρ g h := by
  rw [sub_eq_add_neg,diskGreenCovariance_add_left,← neg_one_smul ℝ g,
    diskGreenCovariance_smul_left]
  ring

/-- The Green energy bound in norms of actual disk restrictions. -/
theorem abs_diskGreenCovariance_le_restriction_norms (f g : TestFn) :
    |diskGreenCovariance c ρ hρ f g| ≤
      (diskGreenCompletionConstant c ρ hρ)^2*‖diskTestRestrictionL2 c ρ f‖*‖diskTestRestrictionL2 c ρ g‖ := by
  have h := abs_diskGreenCovariance_le_diskL2 c ρ hρ f g
  have hf : (∫ z in ball c ρ, ‖f z‖^2) = ‖diskTestRestrictionL2 c ρ f‖^2 := by
    rw [diskTestRestrictionL2_norm_sq]; simp
  have hg : (∫ z in ball c ρ, ‖g z‖^2) = ‖diskTestRestrictionL2 c ρ g‖^2 := by
    rw [diskTestRestrictionL2_norm_sq]; simp
  rw [hf,hg,← mul_pow,← Real.sqrt_eq_rpow ((‖diskTestRestrictionL2 c ρ f‖*‖diskTestRestrictionL2 c ρ g‖)^2),Real.sqrt_sq_eq_abs,
    abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] at h
  have hK : (diskGreenCompletionConstant c ρ hρ)^2 =
      (∫ p : ℂ × ℂ, ‖diskGreenKernel c ρ hρ p.1 p.2‖^2
        ∂((volume.restrict (ball c ρ)).prod (volume.restrict (ball c ρ))))^(1/2 : ℝ) := by
    apply Real.sq_sqrt
    positivity
  rw [hK,mul_assoc]
  exact h

/-- Literal Green pairings converge under L² convergence of one disk restriction. -/
theorem tendsto_diskGreenCovariance_of_restriction_left (f : ℕ → TestFn) (g h : TestFn)
    (hf : Tendsto (fun n => diskTestRestrictionL2 c ρ (f n)) atTop
      (𝓝 (diskTestRestrictionL2 c ρ g))) :
    Tendsto (fun n => diskGreenCovariance c ρ hρ (f n) h) atTop (𝓝 (diskGreenCovariance c ρ hρ g h)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb : Tendsto (fun n => (diskGreenCompletionConstant c ρ hρ)^2*
      ‖diskTestRestrictionL2 c ρ (f n)-diskTestRestrictionL2 c ρ g‖*
        ‖diskTestRestrictionL2 c ρ h‖) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_iff_norm_sub_tendsto_zero.mp hf)).mul tendsto_const_nhds
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hb
  rw [Real.norm_eq_abs,← diskGreenCovariance_sub_left]
  simpa only [diskTestRestrictionL2_sub] using abs_diskGreenCovariance_le_restriction_norms c ρ hρ (f n-g) h

end

end
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
section
variable [IsProbabilityMeasure P] (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (T : Lp ℝ 2 (volume.restrict (ball c ρ)) →L[ℝ] Lp ℝ 2 P)

/-- A completed map retains every global mixed Green covariance from its dense interior tests. -/
theorem completed_disk_map_test_covariance (W : Lp ℝ 2 P) (g : TestFn)
    (hT : ∀ f : TestFn, tsupport f ⊆ ball c ρ →
      covariance (T (diskTestRestrictionL2 c ρ f)) W P = diskGreenCovariance c ρ hρ f g)
    (f : TestFn) : covariance (T (diskTestRestrictionL2 c ρ f)) W P =
      diskGreenCovariance c ρ hρ f g := by
  obtain ⟨a,ha,ht⟩ := exists_interior_test_restriction_approx c ρ hρ f
  have hleft := tendsto_covariance_of_tendsto_L2 (T.continuous.tendsto _ |>.comp ht)
    (tendsto_const_nhds (x := W))
  exact tendsto_nhds_unique hleft ((tendsto_diskGreenCovariance_of_restriction_left c ρ hρ a f g ht).congr (fun n => (hT (a n) (ha n)).symm))

/-- Green covariance between completed restrictions extends from the dense interior pairs. -/
theorem completed_disk_map_covariance (hT : ∀ f g : TestFn, tsupport f ⊆ ball c ρ → tsupport g ⊆ ball c ρ →
      covariance (T (diskTestRestrictionL2 c ρ f)) (T (diskTestRestrictionL2 c ρ g)) P =
        diskGreenCovariance c ρ hρ f g)
    (f g : TestFn) : covariance (T (diskTestRestrictionL2 c ρ f))
      (T (diskTestRestrictionL2 c ρ g)) P = diskGreenCovariance c ρ hρ f g := by
  have hfirst : ∀ f g : TestFn, tsupport g ⊆ ball c ρ →
      covariance (T (diskTestRestrictionL2 c ρ f)) (T (diskTestRestrictionL2 c ρ g)) P =
        diskGreenCovariance c ρ hρ f g := by
    intro f g hg
    exact completed_disk_map_test_covariance P c ρ hρ T _ g
      (fun a ha => hT a g ha hg) f
  rw [covariance_comm, diskGreenCovariance_symm c ρ hρ f g]
  exact completed_disk_map_test_covariance P c ρ hρ T _ f
    (fun a ha => by rw [covariance_comm,diskGreenCovariance_symm]; exact hfirst f a ha) g

end
section
variable (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (c : ℂ)
section
variable (R ρ ε : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε) (hpin : ‖c‖+ρ ≤ R) (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P) (hmean : ∀ z ∈ ball c ρ, (∫ ω, V ω z ∂P) = 0) (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ)) (hcov : ∀ z w, z ∈ ball c ρ → w ∈ ball c ρ → covariance (fun ω => V ω z) (fun ω => V ω w) P = Real.log R+Real.log ρ- Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖) (hlim : ∀ z (hz : z ∈ ball c ρ), Tendsto (fun k => eLpNorm (fun ω => exteriorPinnedEvaluation X Xc R (zero_lt_one.trans hR) ω (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0))
include hR hpin hmean hcov hlim
section
variable (f g : TestFn)

/-- The actual completed field has the exact Green covariance with every global pinned test. -/
theorem dirichletCompletedL2Map_test_covariance : covariance (dirichletCompletedL2Map P X Xc hX hc c R ρ (by linarith) V hV hU (diskTestRestrictionL2 c ρ f))
      (exteriorPinnedTestL2 P X Xc hX hc R (by linarith) g) P = diskGreenCovariance c ρ hρ f g := by
  let _ := hX.1
  apply completed_disk_map_test_covariance P c ρ hρ (dirichletCompletedL2Map P X Xc hX hc c R ρ (by linarith) V hV hU) (exteriorPinnedTestL2 P X Xc hX hc R (by linarith) g) g _ f
  intro a ha
  rw [dirichletCompletedL2Map_apply_interior P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hcov hlim a ha]
  exact dirichletResidualL2_test_covariance P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hlim a g ha

/-- The actual globally restricted Dirichlet family has the literal Green covariance
`DOZZ.diskGreenCovariance`. -/
theorem dirichletCompletedL2Map_covariance : covariance (dirichletCompletedL2Map P X Xc hX hc c R ρ (by linarith) V hV hU (diskTestRestrictionL2 c ρ f))
      (dirichletCompletedL2Map P X Xc hX hc c R ρ (by linarith) V hV hU (diskTestRestrictionL2 c ρ g)) P = diskGreenCovariance c ρ hρ f g := by
  let _ := hX.1
  apply completed_disk_map_covariance P c ρ hρ (dirichletCompletedL2Map P X Xc hX hc c R ρ (by linarith) V hV hU) _ f g
  intro a b ha hb
  rw [dirichletCompletedL2Map_apply_interior P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hcov hlim a ha,
    dirichletCompletedL2Map_apply_interior P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hcov hlim b hb]
  exact dirichletResidualL2_covariance P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hcov hlim a b ha hb

end

/-- Every actual completed disk variable is centered. -/
theorem dirichletCompletedL2Map_integral_zero (u : Lp ℝ 2 (volume.restrict (ball c ρ))) :
    (∫ ω, dirichletCompletedL2Map P X Xc hX hc c R ρ (by linarith) V hV hU u ω ∂P) = 0 := by
  let _ := hX.1
  apply integral_completed_disk_map_eq_zero P c ρ hρ (dirichletCompletedL2Map P X Xc hX hc c R ρ (by linarith) V hV hU) _ u
  intro f hf
  rw [dirichletCompletedL2Map_apply_interior P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hcov hlim f hf]
  exact dirichletResidualL2_integral_zero P X Xc hX hc c R ρ (by linarith) V hV hmean hU f hf

end

end

end

/-- Exterior test restrictions have zero Green covariance with every global test. -/
theorem diskGreenCovariance_eq_zero_of_exterior (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (f g : TestFn) (hg : tsupport g ⊆ (closedBall c ρ)ᶜ) : diskGreenCovariance c ρ hρ f g = 0 := by
  rw [diskGreenCovariance_symm]
  apply diskGreenCovariance_eq_zero_of_eqOn_zero
  intro z hz
  change g z = 0
  by_contra hne
  exact hg (subset_closure hne) (ball_subset_closedBall hz)

/-- Every completed Dirichlet test is orthogonal to every exterior pinned test. -/
theorem dirichletCompletedL2Map_exterior_covariance_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ ε : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε) (hpin : ‖c‖+ρ ≤ R)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hmean : ∀ z ∈ ball c ρ, (∫ ω, V ω z ∂P) = 0)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ))
    (hcov : ∀ z w, z ∈ ball c ρ → w ∈ ball c ρ →
      covariance (fun ω => V ω z) (fun ω => V ω w) P = Real.log R+Real.log ρ-
        Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖)
    (hlim : ∀ z (hz : z ∈ ball c ρ), Tendsto (fun k => eLpNorm
      (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
        (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0))
    (f g : TestFn) (hg : tsupport g ⊆ (closedBall c ρ)ᶜ) :
    covariance (dirichletCompletedL2Map P X Xc hX hc c R ρ (by linarith) V hV hU (diskTestRestrictionL2 c ρ f)) (exteriorPinnedTestL2 P X Xc hX hc R (by linarith) g) P = 0 := by
  rw [dirichletCompletedL2Map_test_covariance P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hcov hlim]
  exact diskGreenCovariance_eq_zero_of_exterior c ρ hρ f g hg

end DOZZ.Proofs
