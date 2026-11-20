module

import HypoellipticAleksandrov.Analysis.CompactLp

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

/-- Restricted real source norms are ordered by their restricted measures when the
larger measure has finite source norm. -/
theorem parabolicLpNormOn_mono_measure {d : ℕ} {F : TimeVelocity d → ℝ}
    {S T : Set (TimeVelocity d)} (hST : volume.restrict S ≤ volume.restrict T)
    (hF : MemLp F (parabolicExponent d) (volume.restrict T)) :
    parabolicLpNormOn d F S ≤ parabolicLpNormOn d F T :=
  ENNReal.toReal_mono hF.eLpNorm_ne_top (eLpNorm_mono_measure F hST)

private theorem parabolicLpNormOn_movingLensClosed_le_rectangle
    {d : Nat} {xi eps tLens tau : Real}
    {y lower upper : PDE.Vec d}
    {U : Set (TimeVelocity d)} {F : TimeVelocity d -> Real}
    (hF : ContinuousOn F U)
    (hclosedU : parabolicClosedRectangle tau lower upper ⊆ U)
    (hLens : movingLensClosed xi eps tLens y ⊆ parabolicClosedRectangle tau lower upper)
    (hLensVel : ∀ z ∈ movingLensClosed xi eps tLens y, z.2 ∈ velocityRectangle lower upper) :
    parabolicLpNormOn d F (movingLensClosed xi eps tLens y) ≤
      parabolicLpNormOn d F (parabolicRectangle tau lower upper) := by
  have heq : (Icc (0 : ℝ) tau ×ˢ velocityRectangle lower upper : Set (TimeVelocity d))
      =ᵐ[volume] parabolicRectangle tau lower upper := by
    rw [volume_timeVelocity_eq_prod]
    exact Measure.set_prod_ae_eq Ioo_ae_eq_Icc.symm EventuallyEq.rfl
  apply parabolicLpNormOn_mono_measure
  · apply Measure.restrict_mono_ae
    filter_upwards [heq] with z hz
    intro hzL
    exact hz ▸ ⟨(hLens hzL).1, hLensVel z hzL⟩
  · have hsub : parabolicRectangle tau lower upper ⊆ parabolicClosedRectangle tau lower upper := by
      rintro ⟨t, v⟩ ⟨⟨ht0, htτ⟩, hv⟩
      exact ⟨⟨ht0.le, htτ.le⟩, fun i => ⟨(hv i).1.le, (hv i).2.le⟩⟩
    exact (Analysis.memLp_restrict_of_isCompact (isCompact_parabolicClosedRectangle _ _ _)
      (hF.mono hclosedU) _).mono_measure (Measure.restrict_mono_set volume hsub)

private theorem source_seed_lower_bound_on_ball
    {d : Nat} {lower upper : PDE.Vec d} {kappa rho eps ell : Real}
    {u : TimeVelocity d -> Real}
    (hrho : 0 < rho) (hrhoEps : rho ≤ eps) (hrhoKappa : rho < kappa)
    (hbase : ∀ i, lower i + kappa ≤ 0 ∧ 0 < upper i - kappa)
    (hseed : ∀ v ∈ velocityClosedRectangle lower upper,
      v ∈ velocityCube (0 : PDE.Vec d) eps -> ell ≤ u (0, v)) :
    ∀ v : PDE.Vec d, PDE.vecNormSq v < rho ^ 2 -> ell ≤ u (0, v) := by
  intro v hv
  have hvBall : v ∈ PDE.euclideanBall (0 : PDE.Vec d) rho := by
    simpa only [PDE.euclideanBall, Set.mem_setOf_eq, PDE.euclideanSqDist, sub_zero] using hv
  have hcontain := euclideanBall_subset_velocityCube_inter_velocityRectangle
    hrho hrhoEps hrhoKappa (fun i => ⟨(hbase i).1, (hbase i).2.le⟩) hvBall
  apply hseed v
  · intro i
    exact ⟨(hcontain.2 i).1.le, (hcontain.2 i).2.le⟩
  · exact hcontain.1

private theorem source_forward_propagation_normalized_interior
    (d : Nat) (lam Lam kappa : Real) (hkappa : 0 < kappa)
    (hkappa_one : kappa <= 1)
    (C : Real) (hC : 0 < C)
    (hsource : SourceMovingLensComparison d lam Lam kappa C)
    (A : CoefficientField d) (lower upper : PDE.Vec d) (tau : Real)
    (U : Set (TimeVelocity d)) (F u : TimeVelocity d -> Real)
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
  let n := movingLensSignExponent d lam Lam kappa
  have htStarPos : 0 < tStar := hkappa.trans htStarLower
  have htauPos : 0 < tau := hkappa.trans htauLower
  have hfaces : ∀ i, lower i < upper i := by
    intro i
    nlinarith [(hwidth i).1]
  have hzero : (0 : PDE.Vec d) ∈ velocityClosedRectangle lower upper := by
    intro i
    simpa only [Pi.zero_apply] using
      ⟨by nlinarith [(hbase i).1], by nlinarith [(hbase i).2]⟩
  have hvStar : vStar ∈ velocityClosedRectangle lower upper := by
    intro i
    exact ⟨by nlinarith [(htarget i).1], by nlinarith [(htarget i).2]⟩
  have hy : PDE.vecNormSq (tStar⁻¹ • vStar) <=
      (d : Real) * kappa ^ (-4 : Int) :=
    vecNormSq_inv_smul_le_of_mem_rectangle hkappa htStarLower.le
      (fun i => (hwidth i).2) hzero hvStar
  have hrectNonneg : IsNonnegativeOn u
      (parabolicClosedRectangle tau lower upper) := by
    apply IsNonnegativeOn.parabolicClosedRectangle htauPos hfaces
      (hu.continuousOn.mono hclosedU) hnonneg
  let rho := min eps (kappa / 2)
  have hrho : 0 < rho := lt_min heps (by positivity)
  have hrhoEps : rho ≤ eps := min_le_left _ _
  have hrhoHalf : rho ≤ kappa / 2 := min_le_right _ _
  have hrhoSmall : 2 * rho ^ 2 < kappa ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrhoHalf) (show 0 ≤ kappa / 2 + rho by positivity),
      sq_pos_of_pos hkappa]
  have hrhoKappa : rho < kappa := by linarith
  have hbase' (i : Fin d) : lower i + kappa ≤ 0 ∧ 0 ≤ upper i - kappa := ⟨(hbase i).1, (hbase i).2.le⟩
  have htarget' (i : Fin d) : lower i + kappa ≤ vStar i ∧ vStar i ≤ upper i - kappa := ⟨(htarget i).1.le, (htarget i).2.le⟩
  have hclosedLens := movingLensClosed_subset_parabolicClosedRectangle hkappa hrho hrhoSmall
    htStarPos htStarUpper.le htauUpper hbase' htarget'
  have hactiveLens := movingLensActive_subset_parabolicRectangle hkappa hrho hrhoSmall
    htStarPos htStarUpper htauUpper hbase' htarget'
  have hsourceBound := hsource A U F u tStar rho ell (tStar⁻¹ • vStar)
    htStarPos (htStarUpper.le.trans htauUpper) hrho hrhoSmall hell hy hU
    (hclosedLens.trans hclosedU) hA hF (hu.continuousOn.mono (hclosedLens.trans hclosedU))
    (fun z hz => contDiffAt_of_contDiffOn_of_isOpen hU hu (hclosedU (hclosedLens
      (movingLensActive_subset_movingLensClosed _ _ _ _ hz))))
    (hrectNonneg.mono hclosedLens) (hlower.mono hactiveLens) (hupper.mono hactiveLens)
    (hFnonneg.mono hactiveLens) (hsuper.mono hactiveLens)
    (source_seed_lower_bound_on_ball hrho hrhoEps hrhoKappa hbase hseed)
  have hnorm := parabolicLpNormOn_movingLensClosed_le_rectangle hF hclosedU hclosedLens
    (fun z => movingLensClosed_velocity_mem_velocityRectangle hkappa hrho hrhoSmall
      htStarPos htStarUpper.le htauUpper hbase' htarget')
  have hratio : eps / 2 ≤ rho / kappa := by
    rw [le_div_iff₀ hkappa, le_min_iff]
    constructor <;> nlinarith [mul_nonneg heps.le (sub_nonneg.mpr hkappa_one),
      mul_nonneg hkappa.le (sub_nonneg.mpr hepsOne)]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ eps / 2) hratio (2 * n)
  have hmain : (1 / 4 : Real) ^ n * eps ^ (2 * n) * ell ≤
      ell * rho ^ (2 * n) / kappa ^ (2 * n) := by
    rw [show (1 / 4 : Real) = (2 : ℝ)⁻¹ ^ 2 by norm_num, ← pow_mul, ← mul_pow,
      mul_comm (2 : ℝ)⁻¹, ← div_eq_mul_inv, mul_div_assoc, ← div_pow, mul_comm ell]
    exact mul_le_mul_of_nonneg_right hpow hell.le
  rw [forwardPropagationExponent]
  refine hmain.trans_lt (lt_of_lt_of_le ?_ (add_le_add_right (mul_le_mul_of_nonneg_left hnorm hC.le) _))
  simpa only [smul_smul, mul_inv_cancel₀ htStarPos.ne', one_smul] using hsourceBound

/-- A source-aware forward estimate at all admissible scales and rectangles. -/
abbrev ForwardPropagationSourceEstimate (d : ℕ) (lam Lam kappa delta : ℝ) (m : ℕ) (C : ℝ) : Prop :=
  ∀ (R : Real) (A : CoefficientField d)
    (v0 lower upper : PDE.Vec d) (tau : Real)
    (U : Set (TimeVelocity d)) (F u : TimeVelocity d -> Real)
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
        parabolicLpNormOn d F (parabolicRectangle tau lower upper)

section
variable (d : Nat) (hd : 0 < d) (lam Lam kappa : Real) (hlam : 0 < lam) (hlamLam : lam <= Lam)
  (hkappa : 0 < kappa) (hkappa_one : kappa <= 1)
include hd hlam hlamLam hkappa hkappa_one

/-- Uniform normalized forward-propagation constants with a nonnegative
supplied source on the open physical rectangle. -/
theorem exists_forward_propagation_source_constants_normalized :
    ∃ delta : Real, 0 < delta ∧ ∃ m : Nat, 0 < m ∧ ∃ C : Real, 0 < C ∧
      ∀ (A : CoefficientField d) (lower upper : PDE.Vec d) (tau : Real)
        (U : Set (TimeVelocity d)) (F u : TimeVelocity d -> Real)
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
  let q := (1 / 4 : Real) ^ movingLensSignExponent d lam Lam kappa *
    eps ^ forwardPropagationExponent d lam Lam kappa * ell
  let N := C * parabolicLpNormOn d F (parabolicRectangle tau lower upper)
  have hq : 0 < q := by dsimp [q]; positivity
  have htopMem : (tStar, vStar) ∈ U := hclosedU <| mem_parabolicClosedRectangle_iff.mpr
    ⟨(hkappa.trans htStarLower).le, htStarUpper,
      fun i => ⟨by linarith [(htarget i).1], by linarith [(htarget i).2]⟩⟩
  have hc : ContinuousAt (fun t => u (t, vStar)) tStar :=
    ContinuousAt.comp_of_eq (hu.continuousOn.continuousAt (hU.mem_nhds htopMem))
      (show ContinuousAt (fun t : ℝ => (t, vStar)) tStar from by fun_prop) rfl
  have hmem : tStar ∈ closure (Ioo kappa tau) := by
    rw [closure_Ioo htauLower.ne]
    exact ⟨htStarLower.le, htStarUpper⟩
  have hsharp : q ≤ u (tStar, vStar) + N := ContinuousWithinAt.closure_le hmem
    (f := fun _ => q) (g := fun t => u (t, vStar) + N)
    continuousWithinAt_const (hc.add continuousAt_const).continuousWithinAt (fun t ht =>
      (source_forward_propagation_normalized_interior d lam Lam kappa hkappa hkappa_one
        C hC hsource A lower upper tau U F u eps ell t vStar htauLower htauUpper hwidth hbase
        hU hclosedU hA hu hF hnonneg hlower hupper hFnonneg hsuper heps hepsOne hell hseed
        ht.1 ht.2 htarget).le)
  have hhalf : (1 / 2 : ℝ) * q < q := by linarith
  simpa only [forwardPropagationDelta, q, N, mul_assoc] using hhalf.trans_le hsharp

/-- Uniform positive-scale forward propagation with the exact scaled source
norm factor. -/
theorem exists_forward_propagation_source_constants :
    ∃ delta : Real, 0 < delta ∧ ∃ m : Nat, 0 < m ∧ ∃ C : Real, 0 < C ∧
      ForwardPropagationSourceEstimate d lam Lam kappa delta m C := by
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
  let lowerHat : PDE.Vec d := pullbackRectangleLower v0 lower R
  let upperHat : PDE.Vec d := pullbackRectangleUpper v0 upper R
  let vStarHat : PDE.Vec d := R⁻¹ • (vStar - v0)
  let UHat : Set (TimeVelocity d) := parabolicAffine 0 v0 R ⁻¹' U
  let AHat : CoefficientField d := pullbackCoefficient A 0 v0 R
  let uHat : TimeVelocity d -> Real := pullbackScalar u 0 v0 R
  let FHat : TimeVelocity d -> Real := fun z => R ^ 2 * F (parabolicAffine 0 v0 R z)
  have hRsq : 0 < R ^ 2 := sq_pos_of_pos hR
  have htauLowerHat : kappa < tauHat := by
    dsimp only [tauHat]
    exact (lt_div_iff₀ hRsq).2 htauLower
  have htauUpperHat : tauHat <= kappa⁻¹ := by
    dsimp only [tauHat]
    exact (div_le_iff₀ hRsq).2 htauUpper
  have htStarLowerHat : kappa < tStarHat := by
    dsimp only [tStarHat]
    exact (lt_div_iff₀ hRsq).2 htStarLower
  have htStarUpperHat : tStarHat <= tauHat := by
    dsimp only [tStarHat, tauHat]
    exact (div_le_div_iff_of_pos_right hRsq).mpr htStarUpper
  have hwidthScale (i : Fin d) :
      upperHat i - lowerHat i = R⁻¹ * (upper i - lower i) := by
    dsimp only [upperHat, lowerHat, pullbackRectangleUpper,
      pullbackRectangleLower]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hwidthHat : ∀ i, 2 * kappa < upperHat i - lowerHat i ∧
      upperHat i - lowerHat i <= kappa⁻¹ := by
    intro i
    rw [hwidthScale i]
    constructor
    · exact (lt_inv_mul_iff₀ hR).2 (by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using (hwidth i).1)
    · exact (inv_mul_le_iff₀ hR).2 (by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using (hwidth i).2)
  have hcancel (x : ℝ) : R * (R⁻¹ * x) = x := by
    rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]
  have hbaseHat (i : Fin d) : lowerHat i + kappa ≤ 0 ∧ 0 < upperHat i - kappa := by
    simp only [lowerHat, upperHat, pullbackRectangleLower, pullbackRectangleUpper,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    constructor
    · apply le_of_mul_le_mul_left ?_ hR
      simp only [mul_add, hcancel, mul_zero]
      linarith [(hbase i).1]
    · apply lt_of_mul_lt_mul_left ?_ hR.le
      simp only [mul_sub, hcancel, mul_zero]
      linarith [(hbase i).2]
  have htargetHat (i : Fin d) : lowerHat i + kappa < vStarHat i ∧
      vStarHat i < upperHat i - kappa := by
    simp only [lowerHat, upperHat, vStarHat, pullbackRectangleLower, pullbackRectangleUpper,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    constructor <;> apply lt_of_mul_lt_mul_left ?_ hR.le <;>
      simp only [mul_add, mul_sub, hcancel] <;> linarith [(htarget i).1, (htarget i).2]
  have hmapU : MapsTo (parabolicAffine 0 v0 R) UHat U := fun _ hz => hz
  have hUHat : IsOpen UHat := by
    dsimp only [UHat]
    exact hU.preimage (contDiff_parabolicAffine 0 v0 R).continuous
  have hclosedUHat :
      parabolicClosedRectangle tauHat lowerHat upperHat ⊆ UHat := by
    intro z hz
    exact hclosedU (mapsTo_parabolicAffine_parabolicClosedRectangle hR
      (by simpa only [tauHat, lowerHat, upperHat] using hz))
  have hmapQ : MapsTo (parabolicAffine 0 v0 R)
      (parabolicRectangle tauHat lowerHat upperHat)
      (parabolicRectangle tau lower upper) := by
    intro z hz
    exact mapsTo_parabolicAffine_parabolicRectangle hR
      (by simpa only [tauHat, lowerHat, upperHat] using hz)
  have hFHat : ContinuousOn FHat UHat := by
    dsimp only [FHat]
    apply continuousOn_const.mul
    simpa only [Function.comp_def] using hF.comp
      (contDiff_parabolicAffine 0 v0 R).continuous.continuousOn hmapU
  have hFnonnegHat : IsNonnegativeOn FHat
      (parabolicRectangle tauHat lowerHat upperHat) := by
    intro z hz
    dsimp only [FHat]
    exact mul_nonneg (sq_nonneg R) (hFnonneg _ (hmapQ hz))
  have hQsubU : parabolicRectangle tau lower upper ⊆ U := by
    intro z hz
    apply hclosedU
    rw [mem_parabolicRectangle_iff] at hz
    rw [mem_parabolicClosedRectangle_iff]
    exact ⟨hz.1.le, hz.2.1.le,
      fun i => ⟨(hz.2.2 i).1.le, (hz.2.2 i).2.le⟩⟩
  have hsuperHat : IsParabolicSupersolutionOn AHat (fun z => -FHat z) uHat
      (parabolicRectangle tauHat lowerHat upperHat) := by
    dsimp only [AHat, uHat, FHat]
    simpa only [mul_neg] using IsParabolicSupersolutionOn.pullback
      (U := parabolicRectangle tau lower upper)
      (V := parabolicRectangle tauHat lowerHat upperHat)
      (isOpen_parabolicRectangle tau lower upper) (hu.mono hQsubU) hsuper hmapQ
  have hseedHat : ∀ v ∈ velocityClosedRectangle lowerHat upperHat,
      v ∈ velocityCube (0 : PDE.Vec d) eps -> ell <= uHat (0, v) := by
    intro v hvRect hvCube
    have hvPhysicalRect : v0 + R • v ∈ velocityClosedRectangle lower upper :=
      (mem_affineVelocity_velocityClosedRectangle_iff hR).2
        (by simpa only [lowerHat, upperHat] using hvRect)
    have hvPhysicalCube : v0 + R • v ∈ velocityCube v0 (eps * R) :=
      (mem_affineVelocity_velocityCube_iff hR).2 hvCube
    simpa only [uHat, pullbackScalar_apply, parabolicAffine, mul_zero, zero_add] using
      hseed (v0 + R • v) hvPhysicalRect hvPhysicalCube
  have hHat := hnorm AHat lowerHat upperHat tauHat UHat FHat uHat eps ell
    tStarHat vStarHat htauLowerHat htauUpperHat hwidthHat hbaseHat hUHat
    hclosedUHat (hA.pullback hmapU) (ContDiffOn.pullbackScalar hu hmapU) hFHat
    (hnonneg.pullbackScalar hmapQ) (hlower.pullback hmapQ) (hupper.pullback hmapQ)
    hFnonnegHat hsuperHat heps hepsOne hell hseedHat htStarLowerHat htStarUpperHat htargetHat
  have heval : parabolicAffine 0 v0 R (tStarHat, vStarHat) = (tStar, vStar) := by
    dsimp only [parabolicAffine, tStarHat, vStarHat]
    ext
    · field_simp [hR.ne']
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [hcancel]
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

end

end HypoellipticAleksandrov.Parabolic
