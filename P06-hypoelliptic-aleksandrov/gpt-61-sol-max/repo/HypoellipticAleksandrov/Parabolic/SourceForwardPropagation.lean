module

public import HypoellipticAleksandrov.Parabolic.ForwardPropagation
public import HypoellipticAleksandrov.Parabolic.MovingLensSourceComparison
public import HypoellipticAleksandrov.Parabolic.ScalingMeasure
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith



/-!
# Source-aware forward propagation

This module upgrades classical forward propagation to a nonnegative supplied
source.  The private norm bridge treats the closed moving-lens time faces by
an almost-everywhere product-measure identity; it does not assert a false
literal inclusion in the open physical rectangle.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal MatrixOrder Topology

variable {d : Nat} {xi eps tLens tau : Real} {y lower upper : PDE.Vec d}

private theorem parabolicELpNormOn_movingLensClosed_le_rectangle
     {F : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hLens :
      movingLensClosed xi eps tLens y ⊆
        parabolicClosedRectangle tau lower upper)
    (hLensVel : ∀ z ∈ movingLensClosed xi eps tLens y,
      z.2 ∈ velocityRectangle lower upper) :
    parabolicELpNormOn d F (movingLensClosed xi eps tLens y) ≤
      parabolicELpNormOn d F (parabolicRectangle tau lower upper) := by
  let L := movingLensClosed xi eps tLens y
  let V := velocityRectangle lower upper
  let C  := Icc (0 : Real) tau ×ˢ V
  let Q := parabolicRectangle tau lower upper



  have hrestrict  :=
    Measure.restrict_congr_set (show L =ᵐ[volume] Set.inter L Q by
        filter_upwards [(show C =ᵐ[volume] Q by
            change (Icc (0 : Real) tau ×ˢ V ) =ᵐ[volume]
              (Ioo 0 tau ×ˢ V )
            rw [volume_timeVelocity_eq_prod]
            exact Measure.set_prod_ae_eq Ioo_ae_eq_Icc.symm (EventuallyEq.rfl))] with z hzCQ
        apply propext
        constructor
        · intro hzL
          refine ⟨hzL, ?_⟩
          change z ∈ Q
          rw [← hzCQ]
          exact (show L ⊆ C by
              intro z hz
              rcases (mem_parabolicClosedRectangle_iff.mp (hLens hz)) with
                ⟨hz0, hztau, _⟩
              exact ⟨⟨hz0, hztau⟩, hLensVel z hz⟩) hzL
        · rintro ⟨hzL, _⟩
          exact hzL)
  unfold parabolicELpNormOn
  rw [hrestrict]
  exact eLpNorm_mono_measure F
    (Measure.restrict_mono_set volume Set.inter_subset_right)

private theorem parabolicLpNormOn_movingLensClosed_le_rectangle

    {U : HypoellipticAleksandrov.Parabolic.Region d} {F : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hF : ContinuousOn F U)
    (hclosedU : parabolicClosedRectangle tau lower upper ⊆ U)
    (hLens :
      movingLensClosed xi eps tLens y ⊆
        parabolicClosedRectangle tau lower upper)
    (hLensVel : ∀ z ∈ movingLensClosed xi eps tLens y,
      z.2 ∈ velocityRectangle lower upper) :
    parabolicLpNormOn d F (movingLensClosed xi eps tLens y) ≤
      parabolicLpNormOn d F (parabolicRectangle tau lower upper) := by
  let K := parabolicClosedRectangle tau lower upper


  have hFK  := hF.mono hclosedU
  have hKcompact  :=
    isCompact_parabolicClosedRectangle tau lower upper
  have hKmeas  := hKcompact.measurableSet
  letI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact hKcompact.measure_lt_top⟩
  obtain ⟨B, hB⟩ := hKcompact.exists_bound_of_continuousOn hFK
  have hKmem : MemLp F (parabolicExponent d) (volume.restrict K) := by
    refine MemLp.of_bound (hFK.aestronglyMeasurable hKmeas) B ?_
    filter_upwards [ae_restrict_mem hKmeas] with z hz
    exact hB z hz

  have hQmem  :=
    hKmem.mono_measure (Measure.restrict_mono_set volume (show (parabolicRectangle tau lower upper) ⊆ K by
        rintro ⟨t, v⟩ ⟨⟨ht0, httau⟩, hv⟩
        exact ⟨⟨ht0.le, httau.le⟩,
          fun i => ⟨(hv i).1.le, (hv i).2.le⟩⟩))




  unfold parabolicLpNormOn
  exact (ENNReal.toReal_le_toReal ((hKmem.mono_measure (Measure.restrict_mono_set volume hLens)).eLpNorm_ne_top) (hQmem.eLpNorm_ne_top)).mpr (parabolicELpNormOn_movingLensClosed_le_rectangle hLens hLensVel)

private def sourceForwardInteriorTime (kappa tau : Real) (j : Nat) : Real :=
  tau - (tau - kappa) / (j + 1 : Real)

section
variable {kappa tau : Real} (htau : kappa < tau)

include htau
private theorem kappa_lt_sourceForwardInteriorTime
     {j : Nat} (hj : 0 < j) :
    kappa < sourceForwardInteriorTime kappa tau j := by
  unfold sourceForwardInteriorTime
  have hjone : 1 < (j + 1 : Real) := by
    exact_mod_cast Nat.succ_lt_succ hj

  have hdiv : (tau - kappa) / (j + 1 : Real) < tau - kappa :=
    (div_lt_iff₀ (by positivity)).2 (by nlinarith [sub_pos.mpr htau])
  nlinarith

private theorem sourceForwardInteriorTime_lt_tau
     (j : Nat) :
    sourceForwardInteriorTime kappa tau j < tau := by
  unfold sourceForwardInteriorTime
  rw [sub_lt_iff_lt_add]
  exact lt_add_of_pos_right _ (div_pos (sub_pos.mpr htau) (by positivity))
end


private theorem tendsto_sourceForwardInteriorTime (kappa tau : Real) :
    Tendsto (sourceForwardInteriorTime kappa tau) atTop (𝓝 tau) := by
  unfold sourceForwardInteriorTime

  simpa using tendsto_const_nhds.sub (show Tendsto (fun j : Nat => (tau - kappa) / (j + 1 : Real)) atTop
      (𝓝 0) by
      simpa only [div_eq_mul_inv, one_mul, mul_zero] using
        (Tendsto.const_mul (tau - kappa)
          (tendsto_one_div_add_atTop_nhds_zero_nat )))

private theorem small_source_seed_radius_lt_kappa {rho kappa : Real}
    (hrho : 0 < rho) (hkappa : 0 < kappa)
    (hsmall : 2 * rho ^ 2 < kappa ^ 2) : rho < kappa := by
  nlinarith [sq_nonneg (rho + kappa)]

private theorem large_source_seed_radius_le {eps kappa : Real}
    (heps : 0 < eps) (hkappa : 0 < kappa)
    (hlarge : ¬ 2 * eps ^ 2 < kappa ^ 2) : kappa / 2 ≤ eps := by
  nlinarith

private theorem source_half_kappa_small {kappa : Real} (hkappa : 0 < kappa) :
    2 * (kappa / 2) ^ 2 < kappa ^ 2 := by
  nlinarith [sq_pos_of_pos hkappa]

private theorem source_seed_lower_bound_on_ball
    {d : Nat} {lower upper : PDE.Vec d} {kappa rho eps ell : Real}
    {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hrho : 0 < rho) (hrhoEps : rho ≤ eps) (hrhoKappa : rho < kappa)
    (hbase : ∀ i, lower i + kappa ≤ 0 ∧ 0 < upper i - kappa)
    (hseed : ∀ v ∈ velocityClosedRectangle lower upper,
      v ∈ velocityCube (0 : PDE.Vec d) eps -> ell ≤ u (0, v)) :
    ∀ v : PDE.Vec d, PDE.vecNormSq v < rho ^ 2 -> ell ≤ u (0, v) := by
  intro v hv

  have hcontain := euclideanBall_subset_velocityCube_inter_velocityRectangle
    hrho hrhoEps hrhoKappa (fun i => ⟨(hbase i).1, (hbase i).2.le⟩) (show v ∈ PDE.euclideanBall (0 : PDE.Vec d) rho by
        simpa only [PDE.euclideanBall, Set.mem_setOf_eq, PDE.euclideanSqDist, sub_zero] using hv)
  apply hseed v
  · intro i
    exact ⟨(hcontain.2 i).1.le, (hcontain.2 i).2.le⟩
  · exact hcontain.1

private abbrev SourceMovingLensComparison
    (d : Nat) (lam Lam kappa C : Real) : Prop :=
  ∀ (A : CoefficientField d) (U : HypoellipticAleksandrov.Parabolic.Region d)
    (F u : HypoellipticAleksandrov.Parabolic.ScalarField d) (tau eps ell : Real) (y : PDE.Vec d),
    0 < tau -> tau <= kappa⁻¹ -> 0 < eps ->
    2 * eps ^ 2 < kappa ^ 2 -> 0 < ell ->
    PDE.vecNormSq y <= (d : Real) * kappa ^ (-4 : Int) ->
    IsOpen U -> movingLensClosed (movingLensSignXi kappa) eps tau y ⊆ U ->
    IsContinuousCoefficientOn A U -> ContinuousOn F U ->
    ContinuousOn u (movingLensClosed (movingLensSignXi kappa) eps tau y) ->
    (∀ z ∈ movingLensActive (movingLensSignXi kappa) eps tau y,
      ContDiffAt Real 2 u z) ->
    IsNonnegativeOn u (movingLensClosed (movingLensSignXi kappa) eps tau y) ->
    HasLowerEllipticityOn lam A (movingLensActive (movingLensSignXi kappa) eps tau y) ->
    HasUpperEllipticityOn Lam A (movingLensActive (movingLensSignXi kappa) eps tau y) ->
    IsNonnegativeOn F (movingLensActive (movingLensSignXi kappa) eps tau y) ->
    IsParabolicSupersolutionOn A (fun z => -F z) u
      (movingLensActive (movingLensSignXi kappa) eps tau y) ->
    (∀ v : PDE.Vec d, PDE.vecNormSq v < eps ^ 2 -> ell <= u (0, v)) ->
    ell * eps ^ (2 * movingLensSignExponent d lam Lam kappa) /
        kappa ^ (2 * movingLensSignExponent d lam Lam kappa) <
      u (tau, tau • y) + C * parabolicLpNormOn d F
        (movingLensClosed (movingLensSignXi kappa) eps tau y)

variable (d : Nat)

private theorem source_forward_propagation_normalized_interior
     (lam Lam kappa : Real) (hkappa : 0 < kappa)
    (hkappa_one : kappa <= 1)
    (C : Real) (hC : 0 < C)
    (hsource : SourceMovingLensComparison d lam Lam kappa C)
    (A : CoefficientField d) (lower upper : PDE.Vec d) (tau : Real)
    (U : HypoellipticAleksandrov.Parabolic.Region d) (F u : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (eps ell tStar : Real) (vStar : PDE.Vec d)
    (htauLower : kappa < tau) (htauUpper : tau <= kappa⁻¹)
    (hwidth : ∀ i, 2 * kappa < upper i - lower i ∧
      upper i - lower i <= kappa⁻¹)
    (hbase : ∀ i, lower i + kappa <= 0 ∧ 0 < upper i - kappa)
    (hU : IsOpen U) (hclosedU : parabolicClosedRectangle tau lower upper ⊆ U)
    (hA : IsContinuousCoefficientOn A U) (hu : ContDiffOn Real 2 u U)
    (hF : ContinuousOn F U)
    (hnonneg : IsNonnegativeOn u (parabolicRectangle tau lower upper))
    (hlower : HasLowerEllipticityOn lam A (parabolicRectangle tau lower upper))
    (hupper : HasUpperEllipticityOn Lam A (parabolicRectangle tau lower upper))
    (hFnonneg : IsNonnegativeOn F (parabolicRectangle tau lower upper))
    (hsuper : IsParabolicSupersolutionOn A (fun z => -F z) u
      (parabolicRectangle tau lower upper))
    (heps : 0 < eps) (hepsOne : eps <= 1) (hell : 0 < ell)
    (hseed : ∀ v ∈ velocityClosedRectangle lower upper,
      v ∈ velocityCube (0 : PDE.Vec d) eps -> ell <= u (0, v))
    (htStarLower : kappa < tStar) (htStarUpper : tStar < tau)
    (htarget : ∀ i, lower i + kappa < vStar i ∧
      vStar i < upper i - kappa) :
    (1 / 4 : Real) ^ movingLensSignExponent d lam Lam kappa *
        eps ^ forwardPropagationExponent d lam Lam kappa * ell <
      u (tStar, vStar) + C * parabolicLpNormOn d F
        (parabolicRectangle tau lower upper) := by
  let sharedTerm_0fa79dda09 := (movingLensClosed (movingLensSignXi kappa) eps tStar (tStar⁻¹ • vStar))
  let n := movingLensSignExponent d lam Lam kappa
  have hn : 0 < n := by
    dsimp only [n]
    unfold movingLensSignExponent
    omega
  have htStarPos  := hkappa.trans htStarLower
  have htauPos  := hkappa.trans htauLower



  have hy  :=
    vecNormSq_inv_smul_le_of_mem_rectangle hkappa htStarLower.le
      (fun i => (hwidth i).2) (show (0 : PDE.Vec d) ∈ velocityClosedRectangle lower upper by
          intro i
          simpa only [Pi.zero_apply] using
            ⟨by nlinarith [(hbase i).1], by nlinarith [(hbase i).2]⟩) (show vStar ∈ velocityClosedRectangle lower upper by
          intro i
          exact ⟨by nlinarith [(htarget i).1], by nlinarith [(htarget i).2]⟩)
  have hrectNonneg : IsNonnegativeOn u
      (parabolicClosedRectangle tau lower upper) := by
    apply IsNonnegativeOn.parabolicClosedRectangle htauPos (show ∀ i, lower i < upper i by
        intro i
        nlinarith [(hwidth i).1])
      (hu.continuousOn.mono hclosedU) hnonneg

  have hbasePow : 0 < eps ^ (2 * n) * ell := by positivity
  by_cases hsmall : 2 * eps ^ 2 < kappa ^ 2
  · have hepsKappa  :=
      small_source_seed_radius_lt_kappa heps hkappa hsmall
    have hclosedLens : sharedTerm_0fa79dda09 ⊆ parabolicClosedRectangle tau lower upper :=
      movingLensClosed_subset_parabolicClosedRectangle hkappa heps hsmall
        htStarPos htStarUpper.le htauUpper
        (fun i => ⟨(hbase i).1, (hbase i).2.le⟩)
        (fun i => ⟨(htarget i).1.le, (htarget i).2.le⟩)
    have hactiveLens  :=
      movingLensActive_subset_parabolicRectangle hkappa heps hsmall
        htStarPos htStarUpper htauUpper
        (fun i => ⟨(hbase i).1, (hbase i).2.le⟩)
        (fun i => ⟨(htarget i).1.le, (htarget i).2.le⟩)
    have hsourceBound := hsource A U F u tStar eps ell (tStar⁻¹ • vStar)
      htStarPos (htStarUpper.le.trans htauUpper) heps hsmall hell hy hU
      (hclosedLens.trans hclosedU)
      hA hF (hu.continuousOn.mono (hclosedLens.trans hclosedU))
      (fun z hz => contDiffAt_of_contDiffOn_of_isOpen hU hu
        (hclosedU (hclosedLens
          (movingLensActive_subset_movingLensClosed _ _ _ _ hz))))
      (hrectNonneg.mono hclosedLens) (hlower.mono hactiveLens)
      (hupper.mono hactiveLens) (hFnonneg.mono hactiveLens)
      (hsuper.mono hactiveLens)
      (source_seed_lower_bound_on_ball heps le_rfl hepsKappa hbase hseed)
    have hnorm := parabolicLpNormOn_movingLensClosed_le_rectangle hF hclosedU
      hclosedLens (fun z hz => movingLensClosed_velocity_mem_velocityRectangle
        hkappa heps hsmall htStarPos htStarUpper.le htauUpper
        (fun i => ⟨(hbase i).1, (hbase i).2.le⟩)
        (fun i => ⟨(htarget i).1.le, (htarget i).2.le⟩) hz)

    have hmain : (1 / 4 : Real) ^ n * (eps ^ (2 * n) * ell) <
        ell * eps ^ (2 * n) / kappa ^ (2 * n) := by
      let sharedTerm_4e764ca6a2 := (eps ^ (2 * n) * ell)


      exact (show (1 / 4 : Real) ^ n * (eps ^ (2 * n) * ell) <
          eps ^ (2 * n) * ell by
          calc
            (1 / 4 : Real) ^ n * (sharedTerm_4e764ca6a2) <
                1 * (sharedTerm_4e764ca6a2) :=
              mul_lt_mul_of_pos_right (by
                  apply pow_lt_one₀ (by norm_num) (by norm_num)
                  omega) hbasePow
            _ = sharedTerm_4e764ca6a2 := one_mul _).trans_le (by
          rw [mul_comm ell]
          exact (le_div_iff₀ (pow_pos hkappa _)).2
            (by simpa only [mul_assoc, mul_one] using
              mul_le_mul_of_nonneg_left (pow_le_one₀ hkappa.le hkappa_one) hbasePow.le))
    rw [forwardPropagationExponent]

    have hnorm'  :=
      mul_le_mul_of_nonneg_left hnorm hC.le
    simpa only [n, mul_comm, mul_assoc] using
      hmain.trans ((show ell * eps ^ (2 * n) / kappa ^ (2 * n) <
        u (tStar, vStar) + C * parabolicLpNormOn d F
          sharedTerm_0fa79dda09 by
          simpa only [smul_smul, mul_inv_cancel₀ htStarPos.ne', one_smul] using
            hsourceBound).trans_le (add_le_add_right hnorm' _))
  · let rho : Real := kappa / 2
    have hrho : 0 < rho := by dsimp only [rho]; positivity
    have hrhoEps  :=
      large_source_seed_radius_le heps hkappa hsmall
    have hrhoSmall : 2 * rho ^ 2 < kappa ^ 2 := by
      dsimp only [rho]
      exact source_half_kappa_small hkappa

    have hclosedLens  :=
      movingLensClosed_subset_parabolicClosedRectangle hkappa hrho hrhoSmall
        htStarPos htStarUpper.le htauUpper
        (fun i => ⟨(hbase i).1, (hbase i).2.le⟩)
        (fun i => ⟨(htarget i).1.le, (htarget i).2.le⟩)
    have hactiveLens  :=
      movingLensActive_subset_parabolicRectangle hkappa hrho hrhoSmall
        htStarPos htStarUpper htauUpper
        (fun i => ⟨(hbase i).1, (hbase i).2.le⟩)
        (fun i => ⟨(htarget i).1.le, (htarget i).2.le⟩)
    have hsourceBound := hsource A U F u tStar rho ell (tStar⁻¹ • vStar)
      htStarPos (htStarUpper.le.trans htauUpper) hrho hrhoSmall hell hy hU
      (hclosedLens.trans hclosedU)
      hA hF (hu.continuousOn.mono (hclosedLens.trans hclosedU))
      (fun z hz => contDiffAt_of_contDiffOn_of_isOpen hU hu
        (hclosedU (hclosedLens
          (movingLensActive_subset_movingLensClosed _ _ _ _ hz))))
      (hrectNonneg.mono hclosedLens) (hlower.mono hactiveLens)
      (hupper.mono hactiveLens) (hFnonneg.mono hactiveLens)
      (hsuper.mono hactiveLens)
      (source_seed_lower_bound_on_ball hrho hrhoEps (show rho < kappa by
          dsimp only [rho]
          linarith) hbase hseed)
    have hnorm := parabolicLpNormOn_movingLensClosed_le_rectangle hF hclosedU
      hclosedLens (fun z hz => movingLensClosed_velocity_mem_velocityRectangle
        hkappa hrho hrhoSmall htStarPos htStarUpper.le htauUpper
        (fun i => ⟨(hbase i).1, (hbase i).2.le⟩)
        (fun i => ⟨(htarget i).1.le, (htarget i).2.le⟩) hz)
    have hhalfPow : (1 / 4 : Real) ^ n = (1 / 2 : Real) ^ (2 * n) := by
      calc
        (1 / 4 : Real) ^ n = ((1 / 2 : Real) ^ 2) ^ n := by norm_num
        _ = (1 / 2 : Real) ^ (2 * n) := by rw [pow_mul]
    have hepsPow : eps ^ (2 * n) <= 1 := pow_le_one₀ heps.le hepsOne
    have hlargeBound : (1 / 4 : Real) ^ n * eps ^ (2 * n) * ell <=
        ell * rho ^ (2 * n) / kappa ^ (2 * n) := by
      calc
        (1 / 4 : Real) ^ n * eps ^ (2 * n) * ell <=
            (1 / 4 : Real) ^ n * 1 * ell := by gcongr
        _ = ell * rho ^ (2 * n) / kappa ^ (2 * n) := by
          dsimp only [rho]
          rw [hhalfPow]
          field_simp [pow_ne_zero _ hkappa.ne']
          ring
    rw [forwardPropagationExponent]

    have hnorm'  :=
      mul_le_mul_of_nonneg_left hnorm hC.le
    simpa only [n, mul_comm] using hlargeBound.trans_lt ((show ell * rho ^ (2 * n) / kappa ^ (2 * n) <
        u (tStar, vStar) + C * parabolicLpNormOn d F
          (movingLensClosed (movingLensSignXi kappa) rho tStar (tStar⁻¹ • vStar)) by
        simpa only [smul_smul, mul_inv_cancel₀ htStarPos.ne', one_smul] using
          hsourceBound).trans_le (add_le_add_right hnorm' _))

variable (hd : 0 < d) (lam Lam kappa : Real) (hlam : 0 < lam) (hlamLam : lam <= Lam) (hkappa : 0 < kappa) (hkappa_one : kappa <= 1)

include hd hlam hlamLam hkappa hkappa_one
/-- Uniform normalized forward-propagation constants with a nonnegative
supplied source on the open physical rectangle. -/
theorem exists_forward_propagation_source_constants_normalized
      :
    ∃ delta : Real, 0 < delta ∧ ∃ m : Nat, 0 < m ∧ ∃ C : Real, 0 < C ∧
      ∀ (A : CoefficientField d) (lower upper : PDE.Vec d) (tau : Real)
        (U : HypoellipticAleksandrov.Parabolic.Region d) (F u : HypoellipticAleksandrov.Parabolic.ScalarField d)
        (eps ell tStar : Real) (vStar : PDE.Vec d),
        kappa < tau -> tau <= kappa⁻¹ ->
        (∀ i, 2 * kappa < upper i - lower i ∧
          upper i - lower i <= kappa⁻¹) ->
        (∀ i, lower i + kappa <= 0 ∧ 0 < upper i - kappa) ->
        IsOpen U -> parabolicClosedRectangle tau lower upper ⊆ U ->
        IsContinuousCoefficientOn A U ->
        ContDiffOn Real 2 u U -> ContinuousOn F U ->
        IsNonnegativeOn u (parabolicRectangle tau lower upper) ->
        HasLowerEllipticityOn lam A (parabolicRectangle tau lower upper) ->
        HasUpperEllipticityOn Lam A (parabolicRectangle tau lower upper) ->
        IsNonnegativeOn F (parabolicRectangle tau lower upper) ->
        IsParabolicSupersolutionOn A (fun z => -F z) u
          (parabolicRectangle tau lower upper) ->
        0 < eps -> eps <= 1 -> 0 < ell ->
        (∀ v ∈ velocityClosedRectangle lower upper,
          v ∈ velocityCube (0 : PDE.Vec d) eps -> ell <= u (0, v)) ->
        kappa < tStar -> tStar <= tau ->
        (∀ i, lower i + kappa < vStar i ∧
          vStar i < upper i - kappa) ->
        delta * eps ^ m * ell < u (tStar, vStar) +
          C * parabolicLpNormOn d F (parabolicRectangle tau lower upper) := by
  let sharedTerm_6dd49da6a1 := ((1 / 4 : Real) ^ movingLensSignExponent d lam Lam kappa)
  let sharedTerm_063d985d10 := ((2 * movingLensSignExponent d lam Lam kappa))
  obtain ⟨C, hC, hsource⟩ :=
    exists_movingLens_source_terminal_lower_bound d hd lam Lam kappa
      hlam hlamLam hkappa hkappa_one
  refine ⟨forwardPropagationDelta d lam Lam kappa,
    forwardPropagationDelta_pos d lam Lam kappa,
    forwardPropagationExponent d lam Lam kappa,
    forwardPropagationExponent_pos d lam Lam kappa, C, hC, ?_⟩
  intro A lower upper tau U F u eps ell tStar vStar
    htauLower htauUpper hwidth hbase hU hclosedU hA hu hF hnonneg hlower
    hupper hFnonneg hsuper heps hepsOne hell hseed htStarLower htStarUpper
    htarget
  rcases htStarUpper.lt_or_eq with hinterior | rfl
  · have hsharp := source_forward_propagation_normalized_interior d lam Lam
      kappa hkappa hkappa_one C hC hsource A lower upper tau U F u
      eps ell tStar vStar htauLower htauUpper hwidth hbase hU hclosedU hA hu hF
      hnonneg hlower hupper hFnonneg hsuper heps hepsOne hell hseed htStarLower
      hinterior htarget
    unfold forwardPropagationDelta forwardPropagationExponent
    have hhalf : (1 / 2 : Real) * (sharedTerm_6dd49da6a1 * eps ^
          sharedTerm_063d985d10 * ell) <
        sharedTerm_6dd49da6a1 * eps ^
          sharedTerm_063d985d10 * ell := by
      have hq : 0 < sharedTerm_6dd49da6a1 *
          eps ^ sharedTerm_063d985d10 * ell := by
        positivity
      nlinarith
    simpa only [mul_assoc] using hhalf.trans hsharp
  ·
    let q : Real := sharedTerm_6dd49da6a1 *
      eps ^ forwardPropagationExponent d lam Lam kappa * ell
    let N : Real := C * parabolicLpNormOn d F
      (parabolicRectangle tStar lower upper)
    have hq : 0 < q := by
      dsimp only [q]
      positivity
    have htopClosed : (tStar, vStar) ∈
        parabolicClosedRectangle tStar lower upper := by
      rw [mem_parabolicClosedRectangle_iff]
      exact ⟨(hkappa.trans htauLower).le, le_rfl,
        fun i => ⟨by nlinarith [(htarget i).1],
          by nlinarith [(htarget i).2]⟩⟩


    have hzu : Tendsto (fun j  =>
        u (sourceForwardInteriorTime kappa tStar j, vStar) + N) atTop
        (𝓝 (u (tStar, vStar) + N)) :=
      (contDiffAt_of_contDiffOn_of_isOpen hU hu (hclosedU htopClosed)).continuousAt.tendsto.comp
        ((tendsto_sourceForwardInteriorTime kappa tStar).prodMk_nhds
          tendsto_const_nhds) |>.add tendsto_const_nhds
    have hinterior : ∀ j : Nat, 0 < j -> q <
        u (sourceForwardInteriorTime kappa tStar j, vStar) + N := by
      intro j hj
      have hjprop := source_forward_propagation_normalized_interior d lam Lam
        kappa hkappa hkappa_one C hC hsource A lower upper tStar U F u
        eps ell (sourceForwardInteriorTime kappa tStar j) vStar
        htauLower htauUpper hwidth hbase hU hclosedU hA hu hF hnonneg hlower hupper
        hFnonneg hsuper heps hepsOne hell hseed
        (kappa_lt_sourceForwardInteriorTime htauLower hj)
        (sourceForwardInteriorTime_lt_tau htauLower j) htarget
      exact hjprop
    have hsharpTop  :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hzu (by
        filter_upwards [eventually_gt_atTop (0 )] with j hj
        exact (hinterior j hj).le)
    unfold forwardPropagationDelta
    linarith

/-- Uniform positive-scale forward propagation with the exact scaled source
norm factor. -/
theorem exists_forward_propagation_source_constants
      :
    ∃ delta : Real, 0 < delta ∧ ∃ m : Nat, 0 < m ∧ ∃ C : Real, 0 < C ∧
      ∀ (R : Real) (A : CoefficientField d)
        (v0 lower upper : PDE.Vec d) (tau : Real)
        (U : HypoellipticAleksandrov.Parabolic.Region d) (F u : HypoellipticAleksandrov.Parabolic.ScalarField d)
        (eps ell tStar : Real) (vStar : PDE.Vec d),
        0 < R -> R <= 2 ->
        kappa * R ^ 2 < tau -> tau <= kappa⁻¹ * R ^ 2 ->
        (∀ i, 2 * kappa * R < upper i - lower i ∧
          upper i - lower i <= kappa⁻¹ * R) ->
        (∀ i, lower i + kappa * R <= v0 i ∧
          v0 i < upper i - kappa * R) ->
        IsOpen U -> parabolicClosedRectangle tau lower upper ⊆ U ->
        IsContinuousCoefficientOn A U ->
        ContDiffOn Real 2 u U -> ContinuousOn F U ->
        IsNonnegativeOn u (parabolicRectangle tau lower upper) ->
        HasLowerEllipticityOn lam A (parabolicRectangle tau lower upper) ->
        HasUpperEllipticityOn Lam A (parabolicRectangle tau lower upper) ->
        IsNonnegativeOn F (parabolicRectangle tau lower upper) ->
        IsParabolicSupersolutionOn A (fun z => -F z) u
          (parabolicRectangle tau lower upper) ->
        0 < eps -> eps <= 1 -> 0 < ell ->
        (∀ v ∈ velocityClosedRectangle lower upper,
          v ∈ velocityCube v0 (eps * R) -> ell <= u (0, v)) ->
        kappa * R ^ 2 < tStar -> tStar <= tau ->
        (∀ i, lower i + kappa * R < vStar i ∧
          vStar i < upper i - kappa * R) ->
        delta * eps ^ m * ell < u (tStar, vStar) +
          C * R ^ ((d : Real) / ((d : Real) + 1)) *
            parabolicLpNormOn d F (parabolicRectangle tau lower upper) := by
  obtain ⟨delta, hdelta, m, hm, C, hC, hnorm⟩ :=
    exists_forward_propagation_source_constants_normalized d hd lam Lam kappa
      hlam hlamLam hkappa hkappa_one
  refine ⟨delta, hdelta, m, hm, C, hC, ?_⟩
  intro R A v0 lower upper tau U F u eps ell tStar vStar
    hR _hRtwo htauLower htauUpper hwidth hbase hU hclosedU hA hu hF hnonneg
    hlower hupper hFnonneg hsuper heps hepsOne hell hseed htStarLower
    htStarUpper htarget
  let tauHat : Real := tau / R ^ 2
  let tStarHat : Real := tStar / R ^ 2
  let lowerHat  := pullbackRectangleLower v0 lower R
  let upperHat  := pullbackRectangleUpper v0 upper R
  let vStarHat  := R⁻¹ • (vStar - v0)
  let UHat  := parabolicAffine 0 v0 R ⁻¹' U
  let AHat  := pullbackCoefficient A 0 v0 R
  let uHat  := pullbackScalar u 0 v0 R
  let FHat  := fun z => R ^ 2 * F (parabolicAffine 0 v0 R z)
  have hRsq  := sq_pos_of_pos hR




  have hwidthScale (i : Fin d) :
      upperHat i - lowerHat i = R⁻¹ * (upper i - lower i) := by
    dsimp only [upperHat, lowerHat, pullbackRectangleUpper,
      pullbackRectangleLower]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring



  have hmapU : MapsTo (parabolicAffine 0 v0 R) UHat U := fun _ hz => hz



  have hmapQ : MapsTo (parabolicAffine 0 v0 R)
      (parabolicRectangle tauHat lowerHat upperHat)
      (parabolicRectangle tau lower upper) := by
    intro z hz
    exact mapsTo_parabolicAffine_parabolicRectangle hR
      (hz)








  have hHat := hnorm AHat lowerHat upperHat tauHat UHat FHat uHat eps ell
    tStarHat vStarHat ((id ((lt_div_iff₀ hRsq).mpr htauLower))) ((id ((div_le_iff₀ hRsq).mpr htauUpper))) (by
        intro i
        rw [hwidthScale i]
        constructor
        · exact (lt_inv_mul_iff₀ hR).2 (by
            simpa only [mul_comm, mul_left_comm] using (hwidth i).1)
        · exact (inv_mul_le_iff₀ hR).2 (by
            simpa only [mul_comm] using (hwidth i).2)) (by
        intro i
        constructor
        · dsimp only [lowerHat, pullbackRectangleLower]
          simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          apply le_of_mul_le_mul_left ?_ hR
          calc
            R * (R⁻¹ * (lower i - v0 i) + kappa) =
                lower i - v0 i + kappa * R := by field_simp [hR.ne']
            _ <= 0 := by nlinarith [(hbase i).1]
            _ = R * 0 := by ring
        · dsimp only [upperHat, pullbackRectangleUpper]
          simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          apply lt_of_mul_lt_mul_left ?_ hR.le
          calc
            R * 0 = 0 := by ring
            _ < upper i - v0 i - kappa * R := by nlinarith [(hbase i).2]
            _ = R * (R⁻¹ * (upper i - v0 i) - kappa) := by field_simp [hR.ne']) (by
        dsimp only [UHat]
        exact hU.preimage (contDiff_parabolicAffine 0 v0 R).continuous)
    (by
        intro z hz
        exact hclosedU (mapsTo_parabolicAffine_parabolicClosedRectangle hR
          (hz))) (hA.pullback hmapU) ((id (ContDiffOn.pullbackScalar hu hmapU))) (by
        dsimp only [FHat]
        apply continuousOn_const.mul
        simpa only [Function.comp_def] using hF.comp
          (contDiff_parabolicAffine 0 v0 R).continuous.continuousOn hmapU) ((id (IsNonnegativeOn.pullbackScalar hnonneg hmapQ))) ((id (HasLowerEllipticityOn.pullback hlower hmapQ))) ((id (HasUpperEllipticityOn.pullback hupper hmapQ)))
    (by
        intro z hz
        dsimp only [FHat]
        exact mul_nonneg (sq_nonneg R) (hFnonneg _ (hmapQ hz))) (by
        dsimp only [AHat, uHat, FHat]
        simpa only [mul_neg] using IsParabolicSupersolutionOn.pullback


          (isOpen_parabolicRectangle tau lower upper) (hu.mono (by
              intro z hz
              apply hclosedU
              rw [mem_parabolicRectangle_iff] at hz
              rw [mem_parabolicClosedRectangle_iff]
              exact ⟨hz.1.le, hz.2.1.le,
                fun i => ⟨(hz.2.2 i).1.le, (hz.2.2 i).2.le⟩⟩)) hsuper hmapQ) heps hepsOne hell (by
        intro v hvRect hvCube
        have hvPhysicalRect  :=
          (mem_affineVelocity_velocityClosedRectangle_iff hR).2
            (hvRect)

        simpa only [uHat, pullbackScalar_apply, parabolicAffine, mul_zero, zero_add] using
          hseed (v0 + R • v) hvPhysicalRect ((mem_affineVelocity_velocityCube_iff hR).2 hvCube)) ((id ((lt_div_iff₀ hRsq).mpr htStarLower))) ((id ((div_le_div_iff₀ hRsq hRsq).mpr (mul_le_mul_of_nonneg_right htStarUpper (LT.lt.le hRsq)))))
    (by
        intro i
        constructor
        · dsimp only [lowerHat, vStarHat, pullbackRectangleLower]
          simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          apply lt_of_mul_lt_mul_left ?_ hR.le
          calc
            R * (R⁻¹ * (lower i - v0 i) + kappa) =
                lower i - v0 i + kappa * R := by field_simp [hR.ne']
            _ < vStar i - v0 i := by nlinarith [(htarget i).1]
            _ = R * (R⁻¹ * (vStar i - v0 i)) := by field_simp [hR.ne']
        · dsimp only [upperHat, vStarHat, pullbackRectangleUpper]
          simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          apply lt_of_mul_lt_mul_left ?_ hR.le
          calc
            R * (R⁻¹ * (vStar i - v0 i)) = vStar i - v0 i := by field_simp [hR.ne']
            _ < upper i - v0 i - kappa * R := by nlinarith [(htarget i).2]
            _ = R * (R⁻¹ * (upper i - v0 i) - kappa) := by field_simp [hR.ne'])
  have heval : parabolicAffine 0 v0 R (tStarHat, vStarHat) = (tStar, vStar) := by
    dsimp only [parabolicAffine, tStarHat, vStarHat]
    ext
    · field_simp [hR.ne']
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]
      ring
  have hscale : parabolicLpNormOn d FHat
      (parabolicRectangle tauHat lowerHat upperHat) =
      R ^ ((d : Real) / ((d : Real) + 1)) *
        parabolicLpNormOn d F (parabolicRectangle tau lower upper) := by
    dsimp only [FHat]
    rw [parabolicLpNormOn_pullback 0 v0 hR F]
    rw [parabolicAffine_image_parabolicRectangle hR]
  rw [hscale] at hHat
  simpa only [uHat, pullbackScalar_apply, heval, mul_assoc] using hHat

end HypoellipticAleksandrov.Parabolic
