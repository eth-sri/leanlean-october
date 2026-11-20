module
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.WholeSpaceAbsorption
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.PotentialWhole
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.WholeSpaceCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.WholeSpaceGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.SourceProblem.LocalizedBound
public import HypoellipticAleksandrov.Parabolic.ContDiffOnTwoToScalarC12

/-! # The whole-space occupation estimate

Subtract the quadratic barrier directly from the potential. The result is nonpositive on
the ball's parabolic boundary and satisfies the inequality needed for the backward ABP
estimate. At the center the barrier accounts for at most half of the supremum. -/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open Parabolic SectionTwo Set
open scoped Matrix.Norms.Elementwise
variable {d : ℕ}

theorem occupation_whole_space_bound
    (hd : 0 < d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {B : CoefficientField d}, IsSectionTwoCoefficient lam Lam B →
      ∀ (K : WholeKernel d), HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
        MeasurableSet.univ (zIndependentCoefficient B) K →
      ∀ F : TimeVelocity d → ℝ, (∀ q, 0 ≤ F q) → ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        tsupport F ⊆ Ioo (0 : ℝ) 1 ×ˢ univ →
        sSup (parabolicDuhamelPotential K MeasurableSet.univ 1 F '' (Icc (0:ℝ) 1 ×ˢ univ)) ≤ C * parabolicLpNorm d F := by
  obtain ⟨C,hC,Krylov⟩ := backward_ball_estimate hd hlam hLam
  let R := Real.sqrt (max 1 (4 * (d : ℝ) * Lam))
  have hm := le_max_left (1:ℝ) (4 * d * Lam)
  have hR : 0 < R := Real.sqrt_pos.mpr (zero_lt_one.trans_le hm)
  have hRsq : R^2 = max 1 (4 * d * Lam) := Real.sq_sqrt (zero_le_one.trans hm)
  let M := C * R^((d:ℝ)/(d+1))
  have hM : 0 ≤ M := mul_nonneg hC (Real.rpow_nonneg hR.le _)
  refine ⟨2*M, by positivity,?_⟩
  intro B hB K hP F h0 hs hc hsu
  let W := parabolicDuhamelPotential K MeasurableSet.univ 1 F
  let S := Icc (0:ℝ) 1 ×ˢ (univ : Set (PDE.Vec d))
  let H := sSup (W '' S)
  obtain ⟨hW,hbdd,hcont,hterm,hsm,heq⟩ := occupation_potential hB K hP F h0 hs hc hsu
  have hn : (0,0) ∈ S := ⟨⟨le_rfl,zero_le_one⟩,mem_univ _⟩
  have hH0 : 0 ≤ H := (hW (0,0)).trans (le_csSup hbdd ⟨_,hn,rfl⟩)
  have hN : 0 ≤ parabolicLpNorm d F := ENNReal.toReal_nonneg
  rw [mul_assoc]; apply wholeSpace_absorb ⟨_,hn⟩
  intro z hz
  rcases hz.1.2.lt_or_eq with ht | ht
  swap
  · obtain ⟨t,y⟩ := z; dsimp only at ht; subst t
    rw [hterm]; positivity
  let Q := occupationQuadratic Lam z.2
  let c := H/R^2
  have hc0 : 0 ≤ c := div_nonneg hH0 (sq_nonneg R)
  let Ω := PDE.euclideanBall z.2 R
  let D := scalarParabolicOpenCylinder z.1 1 Ω
  let V (w : TimeVelocity d) := W w - (c * Q w + 0)
  have hsQ := contDiff_occupationQuadratic Lam z.2
  have hcQ := (isScalarC12On_of_contDiff_two (hsQ.of_le (by simp)) D).const_mul_add_const c 0
  have hw : IsScalarC12On W D := isScalarC12On_of_isOpen_contDiffOn_two
    (isOpen_Ioo.prod (PDE.isOpen_euclideanBall z.2 R)) ((hsm.of_le (by simp)).mono fun p hp => hp.1.2)
  have bound := Krylov hB hs.continuous (hs.continuous.memLp_of_hasCompactSupport hc) hz.1.1 ht
    (show 1 ≤ R by nlinarith) z.2 V ((hcont.mono fun p hp => hp.1.2).sub
      ((hsQ.continuous.const_mul c).add continuous_const).continuousOn) (isScalarC12On_sub hw hcQ)
    (fun p hp => by
      have sub := scalarParabolicZeroOrderOperator_sub B (fun _ _ => 0) (fun _ _ => 0) hw hcQ hp
      have op := scalarParabolicZeroOrderOperator_const_mul_add_const B (fun _ _ => 0) (fun _ _ => 0) c 0 Q p
      simp only [scalarParabolicZeroOrderOperator, zero_mul, add_zero] at op sub
      change -F p ≤ scalarParabolicOperator B _ (fun w => W w - (c * Q w + 0)) p
      simp only [add_zero]
      rw [sub, op, heq p hp.1.2]
      linarith only [mul_nonpos_of_nonneg_of_nonpos hc0 (scalarParabolicOperator_occupationQuadratic_le B Lam z.2 p (hB.2.2.2.2.2 _ _))])
    (fun p hp => by
      change W p - (c * Q p + 0) ≤ 0; rw [add_zero,sub_nonpos]
      rcases hp with he | hl
      · obtain ⟨t,y⟩ := p; have he := (mem_scalarParabolicTerminalFace_iff.mp he).1; change t = 1 at he; subst t
        rw [show W (1,y) = 0 from hterm y]; apply mul_nonneg hc0
        simp [Q, occupationQuadratic, Finset.sum_nonneg fun _ _ => sq_nonneg _]
      · obtain ⟨hl,ht,hy⟩ := mem_scalarParabolicLateralFace_iff.mp hl
        refine (le_csSup hbdd ⟨p, ⟨⟨hz.1.1.trans hl,ht⟩,mem_univ _⟩, rfl⟩).trans ?_
        rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hR)]
        apply mul_le_mul_of_nonneg_left _ hH0
        exact (radius_sq_le_frontier_sum z.2 R hy).trans (le_add_of_nonneg_right
          (mul_nonneg (by positivity [hlam.le.trans hLam]) (sub_nonneg.mpr ht))))
    z ⟨⟨le_rfl,ht.le⟩,subset_closure (show z.2 ∈ Ω by
      exact PDE.center_mem_euclideanBall z.2 hR)⟩
  have half := mul_le_mul_of_nonneg_left (occupationQuadratic_center_half (hlam.le.trans hLam) hz.1.1 hR hRsq) hH0
  change W z - (H/R^2 * Q z + 0) ≤ M * _ at bound
  simp only [Q, occupationQuadratic, sub_self, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, zero_add,
    add_zero,div_mul_eq_mul_div] at bound
  grind

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
