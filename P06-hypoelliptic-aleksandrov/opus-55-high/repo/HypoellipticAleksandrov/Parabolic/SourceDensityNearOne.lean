module

public import HypoellipticAleksandrov.Measure.SourceDensityNearOneMeasure
public import HypoellipticAleksandrov.Parabolic.DensityNearOneBarrier
public import HypoellipticAleksandrov.Parabolic.DensityNearOneGeometry
public import HypoellipticAleksandrov.Parabolic.SourceDensityToPoint
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Source-aware near-one density-to-point estimate

This module proves the normalized near-one density-to-point implication with
a supplied nonnegative source.  Its density threshold and source coefficient
are selected uniformly before the local coefficient, solution, domain, source,
and terminal velocity.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped MatrixOrder Topology

variable {d : Nat}

private theorem parabolicOperator_add_of_contDiffAt 
    (B : CoefficientField d) (u v : TimeVelocity d → Real)
    (z : TimeVelocity d) (hu : ContDiffAt Real 2 u z)
    (hv : ContDiffAt Real 2 v z) :
    parabolicOperator B (fun y ↦ u y + v y) z =
      parabolicOperator B u z + parabolicOperator B v z := by
  have huDiff : DifferentiableAt Real u z := hu.differentiableAt (by norm_num)
  have hvDiff : DifferentiableAt Real v z := hv.differentiableAt (by norm_num)
  have hfirst :
      fderiv Real (fun y ↦ u y + v y) =ᶠ[nhds z]
        fun y ↦ fderiv Real u y + fderiv Real v y := by
    filter_upwards [hu.eventually (by norm_num), hv.eventually (by norm_num)]
      with y huy hvy
    exact fderiv_fun_add (huy.differentiableAt (by norm_num))
      (hvy.differentiableAt (by norm_num))
  have huFirstDiff : DifferentiableAt Real (fderiv Real u) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hvFirstDiff : DifferentiableAt Real (fderiv Real v) z :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsecond :
      fderiv Real (fderiv Real (fun y ↦ u y + v y)) z =
        fderiv Real (fderiv Real u) z + fderiv Real (fderiv Real v) z := by
    calc
      fderiv Real _ z =
          fderiv Real _ z :=
        hfirst.fderiv_eq
      _ = fderiv Real _ z + fderiv Real _ z :=
        fderiv_fun_add huFirstDiff hvFirstDiff
  have htime : timeDerivative (fun y ↦ u y + v y) z =
      timeDerivative u z + timeDerivative v z := by
    unfold timeDerivative
    rw [fderiv_fun_add huDiff hvDiff]
    rfl
  have hhessian : velocityHessian (fun y ↦ u y + v y) z =
      velocityHessian u z + velocityHessian v z := by
    unfold velocityHessian
    rw [hsecond]
    rfl
  rw [parabolicOperator_apply, parabolicOperator_apply, parabolicOperator_apply,
    htime, hhessian, HypoellipticAleksandrov.matrixContraction_add_right]
  ring

private theorem exists_rho_gt_one_inv_cosh_le
    (a eps : Real) (ha : 0 < a) (heps : 0 < eps) :
    ∃ rho : Real, 1 < rho ∧
      (Real.cosh (a * Real.sqrt rho / 4))⁻¹ ≤ eps := by
  let x  := Real.arcosh (max 1 eps⁻¹)
  let s  := 2 + 4 * x / a
  let rho  := s ^ 2
  have hmax : 1 ≤ max 1 eps⁻¹ := le_max_left _ _
  have hx : 0 ≤ x := Real.arcosh_nonneg hmax
  have hs : 1 < s := by
    have : 0 ≤ 4 * x / a := div_nonneg (mul_nonneg (by norm_num) hx) ha.le
    linarith
  have hs0 : 0 ≤ s := hs.le.trans' zero_le_one
  have hrho : 1 < rho := by
    nlinarith
  have hsqrt : Real.sqrt rho = s := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hs0]
  have harg : x ≤ a * Real.sqrt rho / 4 := by
    rw [hsqrt]
    dsimp only [s]
    field_simp [ha.ne']
    nlinarith [ha]
  have harg0 : 0 ≤ a * Real.sqrt rho / 4 := by positivity
  have hcosh : eps⁻¹ ≤ Real.cosh (a * Real.sqrt rho / 4) := by
    calc
      eps⁻¹ ≤ max 1 _ := le_max_right _ _
      _ = Real.cosh x := (Real.cosh_arcosh hmax).symm
      _ ≤ Real.cosh _ := by
        rw [Real.cosh_le_cosh]
        simpa only [abs_of_nonneg hx, abs_of_nonneg harg0] using harg
  refine ⟨rho, hrho, ?_⟩
  exact (inv_le_comm₀ (Real.cosh_pos _) heps).2 hcosh

private theorem exists_eta_for_near_one_error
    (d : Nat) (C rho eps : Real)
    (hC : 0 < C) (hrho : 0 < rho) (heps : 0 < eps) :
    ∃ eta : Real, 0 < eta ∧ eta < 1 ∧
      C * (1 / 2 : Real) ^ ((d : Real) / ((d : Real) + 1)) * rho *
        Real.rpow (eta * (2 : Real) ^ d) (1 / ((d : Real) + 1)) ≤ eps := by
  let n  := d + 1
  let K  :=
    C * (1 / 2) ^ (d / ((d : Real) + 1)) * rho
  let q  := (2 : Real) ^ d
  let x  := eps / K
  let eta0  := x ^ n / q
  let eta  := min (1 / 2) eta0
  have hK : 0 < K := by
    positivity
  have hq : 0 < q := by
    positivity
  have hx : 0 < x := by
    positivity
  have hn : n ≠ 0 := by
    omega
  have heta0 : 0 < eta0 := by
    positivity
  have heta : 0 < eta := lt_min (by norm_num) heta0
  have heta_lt_one : eta < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have heta_bound : eta * q ≤ x ^ n := by
    have := mul_le_mul_of_nonneg_right (min_le_right (1 / 2) eta0) hq.le
    dsimp only [eta0] at this
    field_simp [hq.ne'] at this
    simpa only [eta, mul_comm] using this
  have hp : 0 ≤ 1 / ((d : Real) + 1) := by positivity
  have hbase : 0 ≤ eta * q := mul_nonneg heta.le hq.le
  have hrpow : Real.rpow (eta * q) (1 / (d + 1)) ≤ x := by
    calc
      Real.rpow _ _ ≤
          Real.rpow _ _ :=
        Real.rpow_le_rpow hbase heta_bound hp
      _ = x := by
        have hcast : n = (d : Real) + 1 := by
          dsimp only [n]
          norm_num
        rw [show 1 / ((d : Real) + 1) = ((n : Real))⁻¹ by
          rw [hcast]
          exact one_div _]
        exact Real.pow_rpow_inv_natCast hx.le hn
  refine ⟨eta, heta, heta_lt_one, ?_⟩
  calc
    K * Real.rpow _ _ ≤ K * x :=
      mul_le_mul_of_nonneg_left hrpow hK.le
    _ = eps := by
      dsimp only [x]
      field_simp [hK.ne']

private theorem sub_center_mem_velocityCube_of_mem_localABPInterior
     {v0 : PDE.Vec d} {z : TimeVelocity d}
    (hz : z ∈ localABPInterior v0) : z.2 - v0 ∈ velocityCube 0 1 := by
  rcases hz with ⟨w, hw, rfl⟩
  have hwv := (mem_parabolicInterior_iff.mp hw).2.2
  have hwcube := euclideanBall_subset_velocityCube (by norm_num) hwv
  have heq : (localABPAffine v0 w).2 - v0 = (1 / 2 : Real) • w.2 := by
    simp [localABPAffine, parabolicAffine]
  rw [heq]
  intro i
  have hi := hwcube i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_zero] at hi ⊢
  rw [abs_mul]
  nlinarith [abs_nonneg (w.2 i)]

private theorem nonneg_on_localABPForwardBoundary
     (U : Set (TimeVelocity d)) (u : TimeVelocity d → Real)
    (hU : IsOpen U)
    (hclosed : parabolicClosedBox 1 1 0 (0 : PDE.Vec d) ⊆ U)
    (hu : ContDiffOn Real 2 u U)
    (hnonneg : IsNonnegativeOn u (parabolicBox 1 1 0 0))
    (v0 : PDE.Vec d) (hv0 : v0 ∈ velocityClosedCube 0 (1 / 2 : Real)) :
    ∀ z ∈ localABPForwardBoundary v0, 0 ≤ u z := by
  intro z hz
  have hzK  :=
    localABPForwardBoundary_subset_closure v0 hz
  have hzU  :=
    hclosed (localABPClosure_subset_parabolicClosedBox_one hv0 hzK)
  have hzClosure  :=
    localABPForwardBoundary_subset_closure_interior v0 hz
  have hmaps : MapsTo u (localABPInterior v0) (Ici 0) := by
    intro y hy
    exact hnonneg y (localABPInterior_subset_parabolicBox_one hv0 hy)
  have hcont : ContinuousAt u z :=
    (contDiffAt_of_contDiffOn_of_isOpen hU hu hzU).continuousAt
  have hzImage  :=
    hcont.continuousWithinAt.mem_closure hzClosure hmaps
  simpa using hzImage

/-- For every target value strictly between zero and one, a sufficiently
near-one superlevel density gives the source-aware terminal lower bound. -/
theorem exists_sourceDensityToPoint_near_one
    (d : Nat) (hd : 0 < d) (lam : Real) (hlam : 0 < lam)
    (Lam : Real) (hlamLam : lam ≤ Lam) (g : Real)
    (hg0 : 0 < g) (hg1 : g < 1) :
    ∃ beta : Real, 0 < beta ∧ beta < 1 ∧
      ∃ C : Real, 0 < C ∧
        SourceDensityToPoint d lam Lam beta g C := by
  obtain ⟨CABP, hCABP, hABP⟩ :=
    exists_local_abp_inner_cylinder_of_lower_ellipticity_on_closure
      d hd lam hlam
  obtain ⟨a, ha, hbarrier⟩ :=
    exists_normalizedTranslatedResolventBarrier_strict_sign
      lam Lam hlam hlamLam
  let Csource : Real :=
    CABP * (1 / 2 : Real) ^ ((d : Real) / ((d : Real) + 1))
  have hCsource : 0 < Csource := by
    positivity
  let eps : Real := (1 - g) / 4
  have heps : 0 < eps := by
    have hone : 0 < (1 : Real) := hg0.trans hg1
    have hfour : 0 < (4 : Real) := hone.trans (by norm_num)
    exact div_pos (sub_pos.mpr hg1) hfour
  obtain ⟨rho, hrho, htargetBarrier⟩ :=
    exists_rho_gt_one_inv_cosh_le a eps ha heps
  have hrhoPos : 0 < rho := zero_lt_one.trans hrho
  obtain ⟨eta, heta, hetaOne, herror⟩ :=
    exists_eta_for_near_one_error d CABP rho eps hCABP hrhoPos heps
  let beta : Real := 1 - eta
  have hbeta : 0 < beta := by
    linarith
  have hbetaOne : beta < 1 := by
    linarith
  refine ⟨beta, hbeta, hbetaOne, Csource, hCsource, ?_⟩
  intro U B Fsrc u hU hclosed hB hu hFsrc hu_nonneg hFsrc_nonneg
    hlower hupper hsuper hdensity v0 hv0
  let psi : TimeVelocity d → Real :=
    normalizedTranslatedResolventBarrier a rho v0
  let w : TimeVelocity d → Real := fun z ↦ -(u z + psi z - 1 + eps)
  let Ftot : TimeVelocity d → Real :=
    fun z ↦ Fsrc z + rho * max (1 - u z) 0
  have hQU : parabolicBox 1 1 0 (0 : PDE.Vec d) ⊆ U := by
    intro z hz
    apply hclosed
    rcases hz with ⟨⟨ht0, ht1⟩, hzv⟩
    exact ⟨⟨ht0.le, ht1.le⟩, fun i ↦ (hzv i).le⟩
  have hKU : localABPClosure v0 ⊆ U :=
    (localABPClosure_subset_parabolicClosedBox_one hv0).trans hclosed
  have hpsi : ContDiffOn Real 2 psi U := (contDiff_normalizedTranslatedResolventBarrier a rho v0).contDiffOn
  have hw : ContDiffOn Real 2 w U := by
    fun_prop
  have hFtot : ContinuousOn Ftot U := hFsrc.add (continuousOn_const.mul
      ((continuousOn_const.sub hu.continuousOn).sup continuousOn_const))
  have hlowClosure : HasLowerEllipticityOn lam B (localABPClosure v0) :=
    hasLowerEllipticityOn_localABPClosure hclosed hB hlower hv0
  have hFtot_nonneg : IsNonnegativeOn Ftot (localABPInterior v0) := by
    intro z hz
    have hzQ : z ∈ parabolicBox 1 1 0 (0 : PDE.Vec d) :=
      localABPInterior_subset_parabolicBox_one hv0 hz
    exact add_nonneg (hFsrc_nonneg z hzQ)
      (mul_nonneg hrhoPos.le (le_max_right _ _))
  have hineq : ∀ z ∈ localABPInterior v0,
      parabolicOperator B w z + rho * w z ≤ Ftot z := by
    intro z hz
    have hzQ : z ∈ parabolicBox 1 1 0 (0 : PDE.Vec d) :=
      localABPInterior_subset_parabolicBox_one hv0 hz
    have hzU : z ∈ U := hQU hzQ
    have huAt : ContDiffAt Real 2 u z :=
      contDiffAt_of_contDiffOn_of_isOpen hU hu hzU
    have hpsiAt : ContDiffAt Real 2 psi z :=
      contDiffAt_of_contDiffOn_of_isOpen hU hpsi hzU
    have hadd : parabolicOperator B (fun y ↦ u y + psi y) z =
        parabolicOperator B u z + parabolicOperator B psi z :=
      parabolicOperator_add_of_contDiffAt B u psi z huAt hpsiAt
    have hconst :
        parabolicOperator B (fun y ↦ u y + psi y - 1 + eps) z =
          parabolicOperator B (fun y ↦ u y + psi y) z := by
      calc
        parabolicOperator B _ z =
            parabolicOperator B _ z := by
          congr 2
          funext y
          ring
        _ = parabolicOperator B _ z :=
          parabolicOperator_add_const B _ (-1 + eps) z
    have hop : parabolicOperator B w z + rho * w z =
        -parabolicOperator B u z -
            (parabolicOperator B psi z + rho * psi z) +
          rho * (1 - u z - eps) := by
      rw [parabolicOperator_neg, hconst, hadd]
      ring
    have hsourceOperator : -parabolicOperator B u z ≤ Fsrc z := by
      have hsup := hsuper z hzQ
      linarith
    have hpsiOperator :
        0 < parabolicOperator B psi z + rho * psi z := by
      apply hbarrier rho hrho B z v0
      · exact sub_center_mem_velocityCube_of_mem_localABPInterior hz
      · exact hlower z hzQ
      · exact hupper z hzQ
    have hscalar : rho * (1 - u z - eps) ≤ rho * max (1 - u z) 0 := by
      apply mul_le_mul_of_nonneg_left _ hrhoPos.le
      exact (sub_le_self _ heps.le).trans (le_max_left _ _)
    rw [hop]
    linarith only [hsourceOperator, hpsiOperator, hscalar]
  have hboundary : ∀ z ∈ localABPForwardBoundary v0, w z ≤ 0 := by
    intro z hz
    have huz  :=
      nonneg_on_localABPForwardBoundary U u hU hclosed hu hu_nonneg v0 hv0 z hz
    have hpsiz : 1 ≤ psi z := one_le_normalizedTranslatedResolventBarrier_on_localABPForwardBoundary
        ha hrho hz
    linarith
  have habp := hABP U B w Ftot v0 rho hU hKU hB hw hFtot hlowClosure
    hFtot_nonneg hineq hboundary
  let E  :=
    parabolicBox 1 1 0 0 ∩ {z | u z < 1}
  have hnorm :=
    exp_neg_quarter_mul_parabolicLpNormOn_localABP_weighted_source_add_one_sub_le
      d hd rho hrhoPos.le U Fsrc u hclosed hu hFsrc hu_nonneg hFsrc_nonneg v0 hv0
  have habpLow : w (1, v0) ≤
      Csource * parabolicLpNormOn d Fsrc (parabolicBox 1 1 0 0) +
        Csource * rho *
          Real.rpow (volume E).toReal (1 / (d + 1)) := by
    calc
      w _ ≤ Csource *
          (Real.exp _ *
            parabolicLpNormOn d
              _
              _) := by
        simpa only [Csource, mul_assoc] using habp
      _ ≤ Csource *
          (parabolicLpNormOn d Fsrc _ +
            rho * Real.rpow _
              _) := by
        apply mul_le_mul_of_nonneg_left
        · simpa only [Ftot, E] using hnorm
        · exact hCsource.le
      _ = Csource * parabolicLpNormOn d Fsrc _ +
          Csource * rho *
            Real.rpow _ _ := by
        ring
  have hvolume := volume_parabolicBox_inter_lt_one_toReal_le_one_sub_mul
    d beta U u hQU hu hdensity
  have hEvolume : (volume E).toReal ≤ eta * (2) ^ d := by
    rw [volume_parabolicBox_one_toReal] at hvolume
    simpa only [beta, sub_sub_cancel] using hvolume
  have hexponent : 0 ≤ 1 / ((d : Real) + 1) := by positivity
  have hrpowVolume :
      Real.rpow _ _ ≤
        Real.rpow _ _ :=
    Real.rpow_le_rpow ENNReal.toReal_nonneg hEvolume hexponent
  have hsourcePref : 0 ≤ Csource * rho :=
    mul_nonneg hCsource.le hrhoPos.le
  have habpError : w (1, v0) ≤
      Csource * parabolicLpNormOn d Fsrc (parabolicBox 1 1 0 0) + eps := by
    calc
      w _ ≤ Csource * parabolicLpNormOn d Fsrc
          _ + Csource * rho *
            Real.rpow _ _ := habpLow
      _ ≤ Csource * parabolicLpNormOn d Fsrc
          _ + Csource * rho *
            Real.rpow _ _ :=
        by simpa [add_comm] using
          (add_le_add_left (mul_le_mul_of_nonneg_left hrpowVolume hsourcePref)
            (Csource * parabolicLpNormOn d Fsrc _))
      _ ≤ Csource * parabolicLpNormOn d Fsrc
          _ + eps := by
        simpa [add_comm] using
          (add_le_add_left (by
              dsimp only [Csource]
              simpa only [mul_assoc, one_div, Real.rpow_eq_pow] using herror)
            (Csource * parabolicLpNormOn d Fsrc (parabolicBox 1 1 0 0)))
  have hpsiTarget : psi (1, v0) ≤ eps := by
    dsimp only [psi]
    rw [normalizedTranslatedResolventBarrier_target]
    exact htargetBarrier
  have hepsFormula : 4 * eps = 1 - g := by
    ring
  linarith

end HypoellipticAleksandrov.Parabolic
