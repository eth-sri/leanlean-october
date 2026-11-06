module

public import HypoellipticAleksandrov.Analysis.BoundedMultiplierLp
public import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
public import HypoellipticAleksandrov.Parabolic.GenericPreLiftSpatialDifferenceQuotientEnergyIdentity
public import HypoellipticAleksandrov.Parabolic.GenericPreLiftSpatialDifferenceQuotientSafeCarrierBridge
public import HypoellipticAleksandrov.Parabolic.IntermediateSpatialCutoffCollar
public import HypoellipticAleksandrov.Parabolic.OriginalTimePlateau
public import HypoellipticAleksandrov.Parabolic.SpatialCoordinateDerivatives
public import HypoellipticAleksandrov.Parabolic.SpatialSliceDifferenceQuotientBound
public import HypoellipticAleksandrov.Parabolic.WeakDerivativeSpatialDifferenceQuotientL2Bound
public import HypoellipticAleksandrov.Parabolic.WeakJetProduct
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import all HypoellipticAleksandrov.Parabolic.GenericPreLiftSpatialDifferenceQuotientPointwiseCoercivity
import all HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
import all HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
public import PDEFoundation.Calculus.RegularityOrder


open private HypoellipticAleksandrov.Parabolic.mul_le_lambda_eighth_sq_add from HypoellipticAleksandrov.Parabolic.GenericPreLiftSpatialDifferenceQuotientPointwiseCoercivity
open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_tsupport_subset from HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_contDiff_infty from HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport from HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
section
open private HypoellipticAleksandrov.Parabolic.timeDerivative_tsupport from HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
private alias _sharedProof_83_3 := HypoellipticAleksandrov.Parabolic.timeDerivative_tsupport
end


/-!
# Fixed-direction generic spatial difference-quotient estimate

This module supplies the non-circular fixed-direction Caccioppoli estimate used by
the generic pre-lift spatial difference-quotient estimate.  The private
infrastructure below records the signed collar geometry, product-cutoff
calculus, locally square-integrable fluxes, and coefficient quotient bounds.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped Convex ENNReal MatrixOrder

variable {d : ℕ}

variable {f : TimeVelocity d → ℝ}









private theorem fixedCore_timeDerivative_tsupport_subset
      :
    tsupport (timeDerivative f) ⊆ tsupport f := (_sharedProof_83_3 f)


/-- A selected weak spatial derivative on an outer open carrier uniformly
controls the corresponding quotient on any carrier whose full directed
segments remain in the outer carrier.  Applying this helper to `q` and then
to a gradient component supplies the two bounds used in assembly. -/
private theorem exists_spatialDifferenceQuotient_memLp_norm_le_on_inner
     {U V : HypoellipticAleksandrov.Parabolic.Region d}
    (k : Fin d)
    (hU : IsOpen U) (q Gk : TimeVelocity d → ℝ)
    (hq : ParabolicMemLpOn U 2 q) (hGk : ParabolicMemLpOn U 2 Gk)
    (hweak : HasWeakVelocityPartialDerivOn U k q Gk)
    (h : ℝ) (hh : h ≠ 0)
    (hseg : ∀ z ∈ V, [z -[ℝ] spatialShift k h z] ⊆ U) : type_of% (hweak.exists_spatialDifferenceQuotient_memLp_norm_le
    U hU V k h hh q Gk hq hGk hseg) := hweak.exists_spatialDifferenceQuotient_memLp_norm_le
    U hU V k h hh q Gk hq hGk hseg

/-- Localizing a quotient weak jet by a smooth compactly supported cutoff
produces global `L²` representatives with the exact ambient weak derivative
and with support retained in the local carrier. -/
private theorem localized_spatialDifferenceQuotient_weakJet_global
     {V : HypoellipticAleksandrov.Parabolic.Region d} (hV : IsOpen V)
    (qh : TimeVelocity d → ℝ) (H : Fin d → TimeVelocity d → ℝ)
    (hqh : ParabolicMemLpOn V 2 qh) (hH : ∀ i, ParabolicMemLpOn V 2 (H i))
    (hweak : ∀ i, HasWeakVelocityPartialDerivOn V i qh (H i))
    (w : TimeVelocity d → ℝ) (hw : ContDiff ℝ PDE.smoothOrder w)
    (hwCompact : HasCompactSupport w) (hwSupport : tsupport w ⊆ V) :
    let psi : TimeVelocity d → ℝ := fun z ↦ w z * qh z
    let Dpsi : Fin d → TimeVelocity d → ℝ := fun i z ↦
      velocityGradient w z i * qh z + w z * H i z
    MemLp psi 2  ∧ (∀ i, MemLp (Dpsi i) 2 ) ∧
      (∀ i, HasWeakVelocityPartialDerivOn Set.univ i psi (Dpsi i)) ∧
      tsupport psi ⊆ V ∧ ∀ i, tsupport (Dpsi i) ⊆ V := by
  let psi  := fun z ↦ w z * qh z
  let Dpsi  := fun i z ↦
    velocityGradient w z i * qh z + w z * H i z
  have hwTop : ParabolicMemLpOn V ∞ w :=
    (hw.continuous.memLp_of_hasCompactSupport hwCompact).restrict V
  have hdwTop (i : Fin d) : ParabolicMemLpOn V ∞
      (fun z ↦ velocityGradient w z i) :=
    ((_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_contDiff_infty (i := i) hw).continuous.memLp_of_hasCompactSupport
      (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport  hwCompact)).restrict V

  have hDpsiV (i : Fin d) : ParabolicMemLpOn V 2 (Dpsi i) := by


    simpa only [Dpsi, Pi.add_def] using ((hdwTop i).mul' hqh).add (hwTop.mul' (hH i))
  have hpsiWeakV (i : Fin d) : HasWeakVelocityPartialDerivOn V i psi (Dpsi i) := by
    have hp := (hweak i).mul_contDiff hw
      (hqh.locallyIntegrableOn (by norm_num))
      ((hH i).locallyIntegrableOn (by norm_num))
    convert hp using 1
    funext z
    simp only [Dpsi]
    ring
  have hpsiSupport : tsupport psi ⊆ V :=
    (tsupport_mul_subset_left (f := w) (g := qh)).trans hwSupport
  have hDpsiSupport (i : Fin d) : tsupport (Dpsi i) ⊆ V := by
    refine (tsupport_add _ _).trans (union_subset ?_ ?_)
    · exact (tsupport_mul_subset_left
        (f := fun z ↦ velocityGradient w z i) (g := qh)).trans
          (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_tsupport_subset.trans hwSupport)
    · exact (tsupport_mul_subset_left (f := w) (g := H i)).trans hwSupport
  have hpsiGlobal  :=
    (show ParabolicMemLpOn V 2 psi by
        simpa only [psi, mul_comm] using (hwTop.mul' hqh)).memLp_of_support_subset hV.measurableSet
      ((subset_tsupport psi).trans hpsiSupport)
  have hDpsiGlobal (i : Fin d)  :=
    (hDpsiV i).memLp_of_support_subset hV.measurableSet
      ((subset_tsupport (Dpsi i)).trans (hDpsiSupport i))
  have hpsiWeakGlobal (i : Fin d)  :=
    (hpsiWeakV i).univ_of_tsupport_subset hV hpsiSupport (hDpsiSupport i)
  exact ⟨hpsiGlobal, hDpsiGlobal, hpsiWeakGlobal, hpsiSupport, hDpsiSupport⟩

section
variable (k : Fin d) (h : ℝ) (hh : h ≠ 0)

include hh
/-- The global weak derivative of a localized quotient controls its signed
backward spatial difference quotient with no inverse-step loss. -/
private theorem exists_backward_spatialDifferenceQuotient_memLp_norm_le

    (psi Dpsi : TimeVelocity d → ℝ)
    (hpsi : ParabolicMemLpOn Set.univ 2 psi)
    (hDpsi : ParabolicMemLpOn Set.univ 2 Dpsi)
    (hweak : HasWeakVelocityPartialDerivOn Set.univ k psi Dpsi) :
    ∃ hback : ParabolicMemLpOn Set.univ 2
        (spatialDifferenceQuotient k (-h) psi),
      ‖hback.toLp (spatialDifferenceQuotient k (-h) psi)‖ ≤ ‖hDpsi.toLp Dpsi‖ := (HasWeakVelocityPartialDerivOn.exists_spatialDifferenceQuotient_memLp_norm_le univ isOpen_univ univ k (-h)
  (neg_ne_zero.mpr hh) psi Dpsi hpsi hDpsi hweak fun z hz => subset_univ [z -[ℝ] spatialShift k (-h) z])

/-- `L²` Cauchy--Schwarz bounds the undifferenced source paired with the
backward quotient of a localized test by the localized derivative norm. -/
private theorem abs_integral_source_mul_backwardQuotient_le

    (R psi Dpsi : TimeVelocity d → ℝ)
    (hR : MemLp R 2 ) (hpsi : MemLp psi 2 )
    (hDpsi : MemLp Dpsi 2 )
    (hweak : HasWeakVelocityPartialDerivOn Set.univ k psi Dpsi) :
    |∫ z, R z * spatialDifferenceQuotient k (-h) psi z| ≤
      ‖hR.toLp R‖ * ‖hDpsi.toLp Dpsi‖ := by
  let sharedTerm_a3e4cfe86e := (∫ z, R z * spatialDifferenceQuotient k (-h) psi z)


  obtain ⟨hback, hbackNorm⟩ :=
    exists_backward_spatialDifferenceQuotient_memLp_norm_le k h hh psi Dpsi
      (by
          exact hpsi.mono_measure Measure.restrict_le_self) (by
          exact hDpsi.mono_measure Measure.restrict_le_self) hweak
  have hbackGlobal  := hback.memLp_of_support_subset MeasurableSet.univ (subset_univ _)

  have hR' : MemLp R (ENNReal.ofReal (2 ))  := by simpa using hR
  have hbackGlobal' : MemLp (spatialDifferenceQuotient k (-h) psi)
      (ENNReal.ofReal (2 ))  := by simpa using hbackGlobal
  have hcs := integral_mul_norm_le_Lp_mul_Lq (by
      constructor <;> norm_num) hR' hbackGlobal'
  have hRNorm : (eLpNorm R 2 ).toReal =
      (∫ z, ‖R z‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    have heq := congrArg ENNReal.toReal
      (hR.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top)
    simp only [ENNReal.toReal_ofNat] at heq
    rw [ENNReal.toReal_ofReal (by positivity)] at heq
    convert heq using 1
    norm_num
  have hbackNormEq :
      (eLpNorm (spatialDifferenceQuotient k (-h) psi) 2 ).toReal =
        (∫ z, ‖spatialDifferenceQuotient k (-h) psi z‖ ^ (2 : ℝ)) ^
          (1 / (2 : ℝ)) := by
    have heq := congrArg ENNReal.toReal
      (hbackGlobal.eLpNorm_eq_integral_rpow_norm
        (by norm_num) ENNReal.ofNat_ne_top)
    simp only [ENNReal.toReal_ofNat] at heq
    rw [ENNReal.toReal_ofReal (by positivity)] at heq
    convert heq using 1
    norm_num
  calc
    |sharedTerm_a3e4cfe86e| =
        ‖sharedTerm_a3e4cfe86e‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ ∫ z, ‖R z‖ * ‖spatialDifferenceQuotient k (-h) psi z‖ := (norm_integral_le_integral_norm _).trans_eq <| by
        norm_num
    _ ≤ ‖hR.toLp R‖ * ‖hbackGlobal.toLp (spatialDifferenceQuotient k (-h) psi)‖ := by
      rw [Lp.norm_toLp, Lp.norm_toLp, hRNorm, hbackNormEq]
      exact hcs
    _ ≤ ‖hR.toLp R‖ * ‖hDpsi.toLp Dpsi‖ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [Lp.norm_toLp, timeVelocityVolumeOn, Measure.restrict_univ] using hbackNorm
end


/-- The square integral of a real-valued `L²` function is the square of the
norm of its canonical `Lp` representative. -/
private theorem fixedCore_integral_sq_eq_norm_sq_toLp
    {alpha : Type*} [MeasurableSpace alpha] {mu : Measure alpha}
    (f : alpha → ℝ) (hf : MemLp f (2 ) mu) :
    (∫ x, f x ^ 2 ∂mu) = ‖hf.toLp f‖ ^ 2 := by
  rw [Lp.norm_toLp, hf.eLpNorm_eq_integral_rpow_norm
    (by norm_num) ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofReal (Real.rpow_nonneg
    (integral_nonneg fun _ ↦ sq_nonneg _) _), ENNReal.toReal_ofNat,
    Real.norm_eq_abs, Real.rpow_two, sq_abs]
  exact (Real.rpow_inv_natCast_pow
    (integral_nonneg fun _ ↦ sq_nonneg _) (by norm_num)).symm

variable {d : ℕ} {V : HypoellipticAleksandrov.Parabolic.Region d}

/-- Multiplication by a cutoff in `[0,1]` has squared `L²` norm bounded by
the corresponding singly weighted energy. -/
private theorem exists_weightedMultiplier_memLp_norm_sq_le_integral

    (w H : TimeVelocity d → ℝ)
    (hH : ParabolicMemLpOn V 2 H)
    (hwMeas : AEStronglyMeasurable w (timeVelocityVolumeOn V))
    (hwNonneg : ∀ᵐ z ∂timeVelocityVolumeOn V, 0 ≤ w z)
    (hwLe : ∀ᵐ z ∂timeVelocityVolumeOn V, w z ≤ 1) :
    ∃ hwH : ParabolicMemLpOn V 2 (fun z ↦ w z * H z),
      ‖hwH.toLp (fun z ↦ w z * H z)‖ ^ 2 ≤
        ∫ z in V, w z * H z ^ 2 := by

  obtain ⟨hwH, _⟩ :=
    HypoellipticAleksandrov.Analysis.memLp_mul_eLpNorm_toReal_le_of_ae_abs_le
      (by norm_num : (0 : ℝ) ≤ 1) hwMeas hH (by
          filter_upwards [hwNonneg, hwLe] with z hz0 hz1
          simpa only [abs_of_nonneg hz0] using hz1)

  refine ⟨hwH, ?_⟩
  rw [← fixedCore_integral_sq_eq_norm_sq_toLp _ hwH]
  apply integral_mono_ae hwH.integrable_sq (by
      refine Integrable.mono' hH.integrable_sq (hwMeas.mul hH.integrable_sq.1) ?_
      filter_upwards [hwNonneg, hwLe] with z hz0 hz1
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hz0,
        abs_of_nonneg (sq_nonneg (H z))]
      exact mul_le_of_le_one_left (sq_nonneg (H z)) hz1)
  filter_upwards [hwNonneg, hwLe] with z hz0 hz1

  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg (H z))

section
variable (hV : MeasurableSet V) (k : Fin d)

include hV
/-- The cutoff-gradient multiplier has the sharp scale `2 * Keta`, with no
difference-quotient step in the bound. -/
private theorem exists_cutoffGradientMultiplier_memLp_norm_le


    (w qh : TimeVelocity d → ℝ) (Keta : ℝ)
    (hKeta : 0 ≤ Keta) (hqh : ParabolicMemLpOn V 2 qh)
    (hDwMeas : AEStronglyMeasurable (fun z ↦ velocityGradient w z k)
      (timeVelocityVolumeOn V))
    (hDwBound : ∀ z ∈ V, |velocityGradient w z k| ≤ 2 * Keta) :
    ∃ hterm : ParabolicMemLpOn V 2
        (fun z ↦ velocityGradient w z k * qh z),
      ‖hterm.toLp (fun z ↦ velocityGradient w z k * qh z)‖ ≤
        2 * Keta * ‖hqh.toLp qh‖ := by

  obtain ⟨hterm, htermNorm⟩ :=
    HypoellipticAleksandrov.Analysis.memLp_mul_eLpNorm_toReal_le_of_ae_abs_le
      (mul_nonneg (by norm_num) hKeta) hDwMeas hqh (show ∀ᵐ z ∂timeVelocityVolumeOn V,
      |velocityGradient w z k| ≤ 2 * Keta by
          filter_upwards [ae_restrict_mem hV] with z hz
          exact hDwBound z hz)
  refine ⟨hterm, ?_⟩
  simpa only [Lp.norm_toLp] using htermNorm

/-- The localized product-rule derivative retains the singly weighted
gradient energy in its `L²` bound. -/
private theorem exists_localizedDerivative_memLp_norm_le_weighted
      (qh Hk w : TimeVelocity d → ℝ) (Keta : ℝ)
    (hKeta : 0 ≤ Keta)
    (hqh : ParabolicMemLpOn V 2 qh) (hHk : ParabolicMemLpOn V 2 Hk)
    (hwMeas : AEStronglyMeasurable w (timeVelocityVolumeOn V))
    (hDwMeas : AEStronglyMeasurable (fun z ↦ velocityGradient w z k)
      (timeVelocityVolumeOn V))
    (hwNonneg : ∀ z ∈ V, 0 ≤ w z) (hwLe : ∀ z ∈ V, w z ≤ 1)
    (hDwBound : ∀ z ∈ V, |velocityGradient w z k| ≤ 2 * Keta)
    (hSupport : tsupport (fun z ↦
      velocityGradient w z k * qh z + w z * Hk z) ⊆ V) :
    ∃ hD : MemLp (fun z ↦
        velocityGradient w z k * qh z + w z * Hk z) 2 ,
      ‖hD.toLp (fun z ↦
          velocityGradient w z k * qh z + w z * Hk z)‖ ≤
        2 * Keta * ‖hqh.toLp qh‖ +
          Real.sqrt (∫ z in V, w z * Hk z ^ 2) := by
  let sharedTerm_d772a924db := ((∫ z in V, w z * Hk z ^ 2))
  have hwNonnegAE : ∀ᵐ z ∂timeVelocityVolumeOn V, 0 ≤ w z := by
    filter_upwards [ae_restrict_mem hV] with z hz
    exact hwNonneg z hz

  obtain ⟨hfirst, hfirstNorm⟩ := exists_cutoffGradientMultiplier_memLp_norm_le
    hV k w qh Keta hKeta hqh hDwMeas hDwBound
  obtain ⟨hsecond, hsecondSq⟩ :=
    exists_weightedMultiplier_memLp_norm_sq_le_integral
      w Hk hHk hwMeas hwNonnegAE (show ∀ᵐ z ∂timeVelocityVolumeOn V, w z ≤ 1 by
          filter_upwards [ae_restrict_mem hV] with z hz
          exact hwLe z hz)
  let D  := fun z ↦
    velocityGradient w z k * qh z + w z * Hk z
  have hDV : ParabolicMemLpOn V 2 D := hfirst.add hsecond
  have hDglobal  :=
    hDV.memLp_of_support_subset hV
      ((subset_tsupport D).trans (hSupport))

  have hsecondNorm :
      ‖hsecond.toLp (fun z ↦ w z * Hk z)‖ ≤
        Real.sqrt sharedTerm_d772a924db := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    simpa only [Real.sq_sqrt (show 0 ≤ sharedTerm_d772a924db by
        apply integral_nonneg_of_ae
        filter_upwards [hwNonnegAE] with z hz
        exact mul_nonneg hz (sq_nonneg _))] using hsecondSq
  refine ⟨hDglobal, ?_⟩
  rw [Lp.norm_toLp]
  rw [← eLpNorm_restrict_eq_of_support_subset hDglobal.aestronglyMeasurable
    ((subset_tsupport D).trans ((id hSupport)))]

  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hfirst.eLpNorm_ne_top, hsecond.eLpNorm_ne_top⟩) (show eLpNorm D 2 (timeVelocityVolumeOn V) ≤
      eLpNorm (fun z ↦ velocityGradient w z k * qh z) 2
          (timeVelocityVolumeOn V) +
        eLpNorm (fun z ↦ w z * Hk z) 2 (timeVelocityVolumeOn V) by
        simpa only [D, Pi.add_def] using
          (eLpNorm_add_le (f := fun z ↦ velocityGradient w z k * qh z)
            (g := fun z ↦ w z * Hk z) (μ := timeVelocityVolumeOn V) (by norm_num : 1 ≤ (2 : ℝ≥0∞))))
  rw [ENNReal.toReal_add hfirst.eLpNorm_ne_top hsecond.eLpNorm_ne_top] at hreal
  rw [Lp.norm_toLp] at hfirstNorm hsecondNorm
  exact hreal.trans (add_le_add hfirstNorm hsecondNorm)

/-- The source pairing bound used for absorption, with the gradient factor
measured by its cutoff-weighted energy rather than its unweighted norm. -/
private theorem abs_integral_source_mul_backwardQuotient_le_localized_weighted
      (h : ℝ) (hh : h ≠ 0)
    (R psi qh Hk w : TimeVelocity d → ℝ) (Keta : ℝ)
    (hKeta : 0 ≤ Keta) (hR : MemLp R 2 ) (hpsi : MemLp psi 2 )
    (hqh : ParabolicMemLpOn V 2 qh) (hHk : ParabolicMemLpOn V 2 Hk)
    (hwMeas : AEStronglyMeasurable w (timeVelocityVolumeOn V))
    (hDwMeas : AEStronglyMeasurable (fun z ↦ velocityGradient w z k)
      (timeVelocityVolumeOn V))
    (hwNonneg : ∀ z ∈ V, 0 ≤ w z) (hwLe : ∀ z ∈ V, w z ≤ 1)
    (hDwBound : ∀ z ∈ V, |velocityGradient w z k| ≤ 2 * Keta)
    (hSupport : tsupport (fun z ↦
      velocityGradient w z k * qh z + w z * Hk z) ⊆ V)
    (hweak : HasWeakVelocityPartialDerivOn Set.univ k psi (fun z ↦
      velocityGradient w z k * qh z + w z * Hk z)) :
    |∫ z, R z * spatialDifferenceQuotient k (-h) psi z| ≤
      ‖hR.toLp R‖ * (2 * Keta * ‖hqh.toLp qh‖ +
        Real.sqrt (∫ z in V, w z * Hk z ^ 2)) := by
  obtain ⟨hD, hDnorm⟩ := exists_localizedDerivative_memLp_norm_le_weighted
    hV k qh Hk w Keta hKeta hqh hHk hwMeas hDwMeas hwNonneg hwLe
      hDwBound hSupport
  exact (abs_integral_source_mul_backwardQuotient_le k h hh R psi _
    hR hpsi hD hweak).trans
      (mul_le_mul_of_nonneg_left hDnorm (norm_nonneg _))
end





variable {d : ℕ}

/-- The weighted source pairing is split and absorbed into the weighted
gradient energy and quotient norm, leaving only the undifferenced source
norm with a coarse coefficient depending on `lam` and `Keta`. -/
private theorem abs_integral_source_mul_backwardQuotient_le_absorbed_weighted
     {V : HypoellipticAleksandrov.Parabolic.Region d} (hV : MeasurableSet V)
    (k : Fin d) (h : ℝ) (hh : h ≠ 0)
    (R psi qh Hk w : TimeVelocity d → ℝ) (lam Keta : ℝ)
    (hlam : 0 < lam) (hKeta : 0 ≤ Keta)
    (hR : MemLp R 2 ) (hpsi : MemLp psi 2 )
    (hqh : ParabolicMemLpOn V 2 qh) (hHk : ParabolicMemLpOn V 2 Hk)
    (hwMeas : AEStronglyMeasurable w (timeVelocityVolumeOn V))
    (hDwMeas : AEStronglyMeasurable (fun z ↦ velocityGradient w z k)
      (timeVelocityVolumeOn V))
    (hwNonneg : ∀ z ∈ V, 0 ≤ w z) (hwLe : ∀ z ∈ V, w z ≤ 1)
    (hDwBound : ∀ z ∈ V, |velocityGradient w z k| ≤ 2 * Keta)
    (hSupport : tsupport (fun z ↦
      velocityGradient w z k * qh z + w z * Hk z) ⊆ V)
    (hweak : HasWeakVelocityPartialDerivOn Set.univ k psi (fun z ↦
      velocityGradient w z k * qh z + w z * Hk z))
    (henergyNonneg : 0 ≤ ∫ z in V, w z * Hk z ^ 2) :
    |∫ z, R z * spatialDifferenceQuotient k (-h) psi z| ≤
      (lam / 8) * (∫ z in V, w z * Hk z ^ 2) +
        (1 / 8) * ‖hqh.toLp qh‖ ^ 2 +
        (2 / lam + 8 * Keta ^ 2) * ‖hR.toLp R‖ ^ 2 := by
  let sharedTerm_7ffea24077 := ((∫ z in V, w z * Hk z ^ 2))
  have hsource := abs_integral_source_mul_backwardQuotient_le_localized_weighted
    hV k h hh R psi qh Hk w Keta hKeta hR hpsi hqh hHk hwMeas hDwMeas
      hwNonneg hwLe hDwBound hSupport hweak
  have hquotient := _root_.HypoellipticAleksandrov.Parabolic.mul_le_lambda_eighth_sq_add (1 )
    (2 * Keta * ‖hR.toLp R‖) ‖hqh.toLp qh‖ (by norm_num)
  have henergy := _root_.HypoellipticAleksandrov.Parabolic.mul_le_lambda_eighth_sq_add lam ‖hR.toLp R‖
    (Real.sqrt sharedTerm_7ffea24077) hlam
  rw [Real.sq_sqrt henergyNonneg] at henergy
  calc
    |∫ z, R z * spatialDifferenceQuotient k (-h) psi z| ≤
        ‖hR.toLp R‖ * (2 * Keta * ‖hqh.toLp qh‖ +
          Real.sqrt sharedTerm_7ffea24077) := hsource
    _ = (2 * Keta * ‖hR.toLp R‖) * ‖hqh.toLp qh‖ +
        ‖hR.toLp R‖ * Real.sqrt sharedTerm_7ffea24077 := by ring
    _ ≤ ((1 : ℝ) / 8) * ‖hqh.toLp qh‖ ^ 2 +
          (2 / (1 : ℝ)) * (2 * Keta * ‖hR.toLp R‖) ^ 2 +
        ((lam / 8) * (sharedTerm_7ffea24077) +
          (2 / lam) * ‖hR.toLp R‖ ^ 2) := by linarith
    _ = (lam / 8) * (sharedTerm_7ffea24077) +
        (1 / 8) * ‖hqh.toLp qh‖ ^ 2 +
        (2 / lam + 8 * Keta ^ 2) * ‖hR.toLp R‖ ^ 2 := by ring

section
variable {I : Set ℝ} {O₀ O₂ : PDE.VelocityRegion d} {δ h : ℝ} (hcarrier : Dirichlet.spatialCoordinateShiftCarrier (closure O₂) δ ⊆ O₀) (hh : |h| ≤ δ) (k : Fin d)

include hcarrier hh
/-- A spatial coordinate-shift collar contains every full signed spacetime
segment starting in its intermediate cylinder. -/
private theorem segment_spatialShift_subset_prod_of_carrier
      :
    ∀ z ∈ I ×ˢ O₂, [z -[ℝ] spatialShift k h z] ⊆ I ×ˢ O₀ := by
  rintro ⟨r, y⟩ ⟨hr, hy⟩ w hw
  rw [segment_eq_image] at hw
  rcases hw with ⟨s, hs, rfl⟩
  constructor
  · simp only [spatialShift_apply]
    change (1 - s) * r + s * r ∈ I
    rwa [show (1 - s) * r + s * r = r by ring]
  · apply hcarrier
    change (1 - s) • y + s • (y + h • PDE.basisVec k) ∈
      Dirichlet.spatialCoordinateShiftCarrier (closure O₂) δ
    rw [show (1 - s) • y + s • (y + h • PDE.basisVec k) =
        y + (s * h) • PDE.basisVec k by module]
    apply Dirichlet.mem_spatialCoordinateShiftCarrier_of_mem_of_abs_le
      (subset_closure hy)
    have hs01 : 0 ≤ s ∧ s ≤ 1 := by exact hs
    simpa only [abs_mul, abs_of_nonneg hs01.1] using
      (mul_le_of_le_one_left (abs_nonneg h) hs01.2).trans hh

/-- The signed collar also supplies the endpoint translation required by the
quotient-test energy identity. -/
private theorem mapsTo_spatialShift_prod_of_carrier
      :
    MapsTo (spatialShift k h) (I ×ˢ O₂) (I ×ˢ O₀) := by
  rintro ⟨r, y⟩ ⟨hr, hy⟩
  refine ⟨?_, hcarrier ?_⟩
  · simpa using hr
  exact Dirichlet.mem_spatialCoordinateShiftCarrier_of_mem_of_abs_le
    (subset_closure hy) hh
end


/-- The spatial projection of the signed collar contains the coordinate
segment needed by the fixed-time mean-value estimate. -/
private theorem segment_add_smul_basisVec_subset_of_carrier
     {O₀ O₂ : PDE.VelocityRegion d} {δ h : ℝ}
    (hcarrier :
      Dirichlet.spatialCoordinateShiftCarrier (closure O₂) δ ⊆ O₀)
    (hh : |h| ≤ δ) (k : Fin d) :
    ∀ y ∈ O₂, [y -[ℝ] y + h • PDE.basisVec k] ⊆ O₀ := by
  intro y hy w hw
  rw [segment_eq_image] at hw
  rcases hw with ⟨s, hs, rfl⟩
  apply hcarrier
  change (1 - s) • y + s • (y + h • PDE.basisVec k) ∈
    Dirichlet.spatialCoordinateShiftCarrier (closure O₂) δ
  rw [show (1 - s) • y + s • (y + h • PDE.basisVec k) =
      y + (s * h) • PDE.basisVec k by module]
  apply Dirichlet.mem_spatialCoordinateShiftCarrier_of_mem_of_abs_le
    (subset_closure hy)
  have hs01 : 0 ≤ s ∧ s ≤ 1 := by exact hs
  simpa only [abs_mul, abs_of_nonneg hs01.1] using
    (mul_le_of_le_one_left (abs_nonneg h) hs01.2).trans hh

variable (zeta : ℝ → ℝ) (eta : PDE.Vec d → ℝ)

/-- The separated product cutoff is globally smooth. -/
private theorem productCutoff_contDiff

    (hzeta : ContDiff ℝ PDE.smoothOrder zeta)
    (heta : ContDiff ℝ PDE.smoothOrder eta) :
    ContDiff ℝ PDE.smoothOrder
      (fun z : TimeVelocity d ↦ zeta z.1 * eta z.2 ^ 2) := by
  fun_prop

/-- Compact support of both separated factors gives compact support of their
spacetime product. -/
private theorem productCutoff_hasCompactSupport

    (hzeta : HasCompactSupport zeta) (heta : HasCompactSupport eta) :
    HasCompactSupport
      (fun z : TimeVelocity d ↦ zeta z.1 * eta z.2 ^ 2) := by

  apply HasCompactSupport.of_support_subset_isCompact (hzeta.isCompact.prod heta.isCompact)
  intro z hz


  exact ⟨subset_tsupport zeta (Function.mem_support.mpr (by
      intro hzero
      exact hz (by simp [hzero]))),
    subset_tsupport eta (Function.mem_support.mpr (by
        intro hzero
        exact hz (by simp [hzero])))⟩

/-- The topological support of a separated product cutoff lies in the product
of the topological supports of its factors. -/
private theorem productCutoff_tsupport_subset
      :
    tsupport (fun z : TimeVelocity d ↦ zeta z.1 * eta z.2 ^ 2) ⊆
      tsupport zeta ×ˢ tsupport eta := by
  rw [tsupport]
  apply closure_minimal
  · intro z hz


    exact ⟨subset_tsupport zeta (Function.mem_support.mpr (by
        intro hzero
        exact hz (by simp [hzero]))),
      subset_tsupport eta (Function.mem_support.mpr (by
          intro hzero
          exact hz (by simp [hzero])))⟩
  · exact (isClosed_tsupport zeta).prod (isClosed_tsupport eta)

section
variable (hzeta : ContDiff ℝ PDE.smoothOrder zeta) (heta : ContDiff ℝ PDE.smoothOrder eta)

include hzeta heta
/-- Exact time derivative of the separated squared spatial cutoff. -/
private theorem timeDerivative_productCutoff


    (z : TimeVelocity d) :
    timeDerivative (fun x : TimeVelocity d ↦ zeta x.1 * eta x.2 ^ 2) z =
      _root_.deriv zeta z.1 * eta z.2 ^ 2 := by
  let sharedTerm_838a6a745d := ((fun x : TimeVelocity d ↦ zeta x.1))
  unfold timeDerivative
  have hzetaDiff : DifferentiableAt ℝ sharedTerm_838a6a745d z :=
    (hzeta.comp (contDiff_fst (𝕜 := ℝ))).differentiable (by simp) z
  have hetaDiff : DifferentiableAt ℝ (fun x : TimeVelocity d ↦ eta x.2) z :=
    (heta.comp (contDiff_snd (𝕜 := ℝ))).differentiable (by simp) z
  rw [show (fun x : TimeVelocity d ↦ zeta x.1 * eta x.2 ^ 2) =
      (fun x ↦ zeta x.1) * (fun x ↦ eta x.2) ^ 2 by rfl]
  rw [fderiv_mul hzetaDiff (hetaDiff.pow 2)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  change zeta z.1 * fderiv ℝ (fun x : TimeVelocity d ↦ eta x.2 ^ 2) z (1, 0) +
      eta z.2 ^ 2 * fderiv ℝ sharedTerm_838a6a745d z (1, 0) = _
  rw [fderiv_fun_pow 2 hetaDiff]
  have hetaZero : fderiv ℝ (fun x : TimeVelocity d ↦ eta x.2) z (1, 0) = 0 := by
    change fderiv ℝ (eta ∘ Prod.snd) z (1, 0) = 0
    rw [fderiv_comp z (heta.differentiable (by simp) z.2)
      (differentiableAt_snd ), fderiv_snd]
    simp
  have hzetaEval : fderiv ℝ sharedTerm_838a6a745d z (1, 0) =
      _root_.deriv zeta z.1 := by
    change fderiv ℝ (zeta ∘ Prod.fst) z (1, 0) = _
    rw [fderiv_comp z (hzeta.differentiable (by simp) z.1)
      (differentiableAt_fst ), fderiv_fst]
    rfl
  rw [hzetaEval]
  simp only [ContinuousLinearMap.smul_apply, Nat.reduceSub, pow_one,
    nsmul_eq_mul, Nat.cast_ofNat, hetaZero, mul_zero, smul_zero, zero_add]
  ring

/-- Exact velocity gradient of the separated squared spatial cutoff. -/
private theorem velocityGradient_productCutoff


    (i : Fin d) (z : TimeVelocity d) :
    velocityGradient (fun x : TimeVelocity d ↦ zeta x.1 * eta x.2 ^ 2) z i =
      zeta z.1 * (2 * eta z.2 * spatialPartial i eta z.2) := by
  let sharedTerm_55ee46674d := ((fun x : TimeVelocity d ↦ zeta x.1))
  unfold velocityGradient
  have hzetaDiff : DifferentiableAt ℝ sharedTerm_55ee46674d z :=
    (hzeta.comp (contDiff_fst (𝕜 := ℝ))).differentiable (by simp) z
  have hetaDiff : DifferentiableAt ℝ (fun x : TimeVelocity d ↦ eta x.2) z :=
    (heta.comp (contDiff_snd (𝕜 := ℝ))).differentiable (by simp) z
  rw [show (fun x : TimeVelocity d ↦ zeta x.1 * eta x.2 ^ 2) =
      (fun x ↦ zeta x.1) * (fun x ↦ eta x.2) ^ 2 by rfl]
  rw [fderiv_mul hzetaDiff (hetaDiff.pow 2)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  change zeta z.1 * fderiv ℝ (fun x : TimeVelocity d ↦ eta x.2 ^ 2) z
      (0, Pi.single i 1) + eta z.2 ^ 2 *
      fderiv ℝ sharedTerm_55ee46674d z
        (0, Pi.single i 1) = _
  rw [fderiv_fun_pow 2 hetaDiff]
  have hzetaZero : fderiv ℝ sharedTerm_55ee46674d z
      (0, Pi.single i 1) = 0 := by
    change fderiv ℝ (zeta ∘ Prod.fst) z (0, Pi.single i 1) = 0
    rw [fderiv_comp z (hzeta.differentiable (by simp) z.1)
      (differentiableAt_fst ), fderiv_fst]
    simp
  have hetaEval : fderiv ℝ (fun x : TimeVelocity d ↦ eta x.2) z
      (0, Pi.single i 1) = spatialPartial i eta z.2 := by
    change fderiv ℝ (eta ∘ Prod.snd) z (0, Pi.single i 1) = _
    rw [fderiv_comp z (heta.differentiable (by simp) z.2)
      (differentiableAt_snd ), fderiv_snd]
    rfl
  simp_all
end


/-- On the inner product cylinder the two plateau factors make the product
cutoff exactly one. -/
private theorem productCutoff_eq_one_on_inner
     {t₁ t₂ : ℝ} {O₁ : PDE.VelocityRegion d}
    (zeta : ℝ → ℝ) (eta : PDE.Vec d → ℝ)
    (hzeta : ∀ t ∈ Icc t₁ t₂, zeta t = 1)
    (heta : ∀ y ∈ closure O₁, eta y = 1) :
    ∀ z ∈ Ioo t₁ t₂ ×ˢ O₁,
      zeta z.1 * eta z.2 ^ 2 = 1 := by
  intro z hz
  rw [hzeta z.1 ⟨hz.1.1.le, hz.1.2.le⟩, heta z.2 (subset_closure hz.2)]
  norm_num

/-- The constructed product cutoff has the exact support, shift, derivative,
and plateau properties consumed by the fixed-step energy argument. -/
private theorem productCutoff_data
     {s₀ t₁ t₂ s₁ δ Keta Kzeta : ℝ}
    {O₀ O₁ O₂ : PDE.VelocityRegion d}
    (hO₂O₀ : closure O₂ ⊆ O₀)
    (hcarrier :
      Dirichlet.spatialCoordinateShiftCarrier (closure O₂) δ ⊆ O₀)
    (eta : PDE.QuantitativeSmoothCutoff (closure O₁) O₂ Keta)
    (zeta : ℝ → ℝ)
    (hzetaSmooth : ContDiff ℝ PDE.smoothOrder zeta)
    (hzetaCompact : HasCompactSupport zeta)
    (hzetaNonneg : ∀ t, 0 ≤ zeta t)
    (hzetaLe : ∀ t, zeta t ≤ 1)
    (hzetaOne : ∀ t ∈ Icc t₁ t₂, zeta t = 1)
    (hzetaSupport : tsupport zeta ⊆ Ioo s₀ s₁)
    (hzetaDeriv : ∀ t, |_root_.deriv zeta t| ≤ Kzeta) :
    let w : TimeVelocity d → ℝ := fun z ↦ zeta z.1 * eta z.2 ^ 2
    ContDiff ℝ PDE.smoothOrder w ∧
      HasCompactSupport w ∧
      tsupport w ⊆ Ioo s₀ s₁ ×ˢ O₀ ∧
      (∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
        MapsTo (spatialShift k h) (tsupport w)
          (Ioo s₀ s₁ ×ˢ O₀)) ∧
      (∀ z, timeDerivative w z = _root_.deriv zeta z.1 * eta z.2 ^ 2) ∧
      (∀ i z, velocityGradient w z i =
        zeta z.1 * (2 * eta z.2 * spatialPartial i eta z.2)) ∧
      (∀ z, |timeDerivative w z| ≤ Kzeta) ∧
      (∀ i z, |velocityGradient w z i| ≤ 2 * Keta) ∧
      (∀ z, 0 ≤ w z ∧ w z ≤ 1) ∧
      (∀ i z, (velocityGradient w z i) ^ 2 ≤
        4 * Keta ^ 2 * w z) ∧
      (∀ z, w z ^ 2 ≤ w z) ∧
      (∀ z ∈ Ioo t₁ t₂ ×ˢ O₁, w z = 1) := by
  classical

  have hsupp : tsupport (show TimeVelocity d → ℝ from fun z ↦ zeta z.1 * eta z.2 ^ 2) ⊆ tsupport zeta ×ˢ tsupport eta :=
    productCutoff_tsupport_subset zeta eta


  refine ⟨productCutoff_contDiff zeta eta hzetaSmooth eta.smooth,
    productCutoff_hasCompactSupport zeta eta hzetaCompact eta.hasCompactSupport,
    (by
        intro z hz
        exact ⟨hzetaSupport (hsupp hz).1,
          hO₂O₀ (subset_closure (eta.tsupport_subset (hsupp hz).2))⟩), (by
        intro k h hh z hz
        exact mapsTo_spatialShift_prod_of_carrier hcarrier hh k
          ⟨hzetaSupport (hsupp hz).1, eta.tsupport_subset (hsupp hz).2⟩), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (timeDerivative_productCutoff zeta eta hzetaSmooth eta.smooth)
  · exact (velocityGradient_productCutoff zeta eta hzetaSmooth eta.smooth)
  · intro z
    rw [timeDerivative_productCutoff zeta eta hzetaSmooth eta.smooth z, abs_mul]
    have hetaAbs : |eta z.2| ≤ 1 := by
      rw [abs_of_nonneg (eta.nonneg z.2)]
      exact eta.le_one z.2
    have hetaSq : |eta z.2 ^ 2| ≤ 1 := by
      rw [abs_pow]
      nlinarith [abs_nonneg (eta z.2)]
    nlinarith [hzetaDeriv z.1, abs_nonneg (_root_.deriv zeta z.1)]
  · intro i z
    rw [velocityGradient_productCutoff zeta eta hzetaSmooth eta.smooth i z]
    have hzetaAbs : |zeta z.1| ≤ 1 := by
      rw [abs_of_nonneg (hzetaNonneg z.1)]
      exact hzetaLe z.1
    have hetaAbs : |eta z.2| ≤ 1 := by
      rw [abs_of_nonneg (eta.nonneg z.2)]
      exact eta.le_one z.2
    have hpartial : |spatialPartial i eta z.2| ≤ Keta := by
      exact eta.abs_classicalGradient_apply_le z.2 i
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      |zeta z.1| * (2 * |eta z.2| * |spatialPartial i eta z.2|) ≤
          1 * (2 * 1 * Keta) := by
        gcongr
      _ = 2 * Keta := by ring
  · intro z
    constructor
    · exact mul_nonneg (hzetaNonneg z.1) (sq_nonneg (eta z.2))
    · have hetaSq : eta z.2 ^ 2 ≤ 1 := by
        nlinarith [eta.nonneg z.2, eta.le_one z.2]
      exact (mul_le_mul (hzetaLe z.1) hetaSq (sq_nonneg _) zero_le_one).trans_eq
        (one_mul 1)
  · intro i z
    rw [velocityGradient_productCutoff zeta eta hzetaSmooth eta.smooth i z]
    have hpartial : |spatialPartial i eta z.2| ≤ Keta := by
      exact eta.abs_classicalGradient_apply_le z.2 i


    have hetaSq : 0 ≤ eta z.2 ^ 2 := sq_nonneg _

    calc
      (zeta z.1 * (2 * eta z.2 * spatialPartial i eta z.2)) ^ 2 =
          4 * zeta z.1 ^ 2 * eta z.2 ^ 2 *
            (spatialPartial i eta z.2) ^ 2 := by ring
      _ ≤ 4 * zeta z.1 * eta z.2 ^ 2 * Keta ^ 2 := by

        exact (mul_le_mul_of_nonneg_right (by
            have h := mul_le_mul_of_nonneg_left (show zeta z.1 ^ 2 ≤ zeta z.1 by
                nlinarith [hzetaNonneg z.1, hzetaLe z.1])
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hetaSq)
            nlinarith) (sq_nonneg _)).trans
          (mul_le_mul_of_nonneg_left (by
              simpa only [sq_abs] using
                (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hpartial)).2 hpartial) (mul_nonneg (mul_nonneg (by norm_num) (hzetaNonneg z.1)) hetaSq))
      _ = 4 * Keta ^ 2 * (zeta z.1 * eta z.2 ^ 2) := by ring
  · intro z
    have hw0 : 0 ≤ zeta z.1 * eta z.2 ^ 2 :=
      mul_nonneg (hzetaNonneg z.1) (sq_nonneg _)
    have hw1 : zeta z.1 * eta z.2 ^ 2 ≤ 1 := by
      have hetaSq : eta z.2 ^ 2 ≤ 1 := by
        nlinarith [eta.nonneg z.2, eta.le_one z.2]
      nlinarith [mul_le_mul (hzetaLe z.1) hetaSq
        (sq_nonneg (eta z.2)) zero_le_one]
    nlinarith
  · exact productCutoff_eq_one_on_inner zeta eta hzetaOne eta.eq_one_on_inner

/-- Two-sided Loewner control makes each local coefficient flux entry square
integrable on compact subsets of the outer cylinder. -/
private theorem fluxEntry_parabolicMemLpOn_compact
     {U K : HypoellipticAleksandrov.Parabolic.Region d} {lam Lam : ℝ}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (A : TimeVelocity d → PDE.Mat d)
    (hEll : ∀ z ∈ U,
      lam • (1 : PDE.Mat d) ≤ A z ∧ A z ≤ Lam • (1 : PDE.Mat d))
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun z  ↦ A z i j) U)
    (G : Fin d → TimeVelocity d → ℝ)
    (hG : ∀ j, ParabolicMemLpOn U 2 (G j))
    (i j : Fin d) :
    ParabolicMemLpOn K 2 (fun z ↦ A z i j * G j z) := ((Analysis.memLp_mul_eLpNorm_toReal_le_of_ae_abs_le (LE.le.trans (LT.lt.le hlam) hlamLam)
    (ContinuousOn.aestronglyMeasurable (ContinuousOn.mono (ContDiffOn.continuousOn (hA i j)) hKU)
      (IsCompact.measurableSet hK))
    (ParabolicMemLpOn.mono (hG j) hKU)
    (Filter.mp_mem (ae_restrict_mem (IsCompact.measurableSet hK))
      (Filter.univ_mem'
        (id fun z hz => abs_apply_le_of_loewner hlam (hEll z (hKU hz)).left (hEll z (hKU hz)).right i j)))).left)

/-- Joint `C¹` coefficient regularity and the signed collar convert the
displayed spatial derivative bound into a uniform coefficient quotient bound. -/
private theorem coefficient_spatialDifferenceQuotient_bound
     {s₀ s₁ : ℝ} {O₀ O₂ : PDE.VelocityRegion d} {δ h Ma : ℝ}
    (hO₀ : IsOpen O₀)
    (hcarrier :
      Dirichlet.spatialCoordinateShiftCarrier (closure O₂) δ ⊆ O₀)
    (hh : |h| ≤ δ)
    (A : TimeVelocity d → PDE.Mat d)
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun z  ↦ A z i j)
      (Ioo s₀ s₁ ×ˢ O₀))
    (hbound : ∀ i j k z, z ∈ Ioo s₀ s₁ ×ˢ O₀ →
      |spatialPartial k (fun y  ↦ A (z.1, y) i j) z.2| ≤ Ma) :
    ∀ i j k z, z ∈ Ioo s₀ s₁ ×ˢ O₂ →
      |spatialDifferenceQuotient k h (fun x ↦ A x i j) z| ≤ Ma := by
  intro i j k z hz
  exact abs_spatialDifferenceQuotient_le_of_spatialSliceFDeriv_bound
    (f := fun x ↦ A x i j) (δ := δ)
    (fun ell g y hg hy ↦
      segment_add_smul_basisVec_subset_of_carrier hcarrier hg ell y hy)
    (fun r hr y hy ↦ by
      have hjoint : DifferentiableAt ℝ (fun z : TimeVelocity d ↦ A z i j) (r, y) :=
        ((hA i j (r, y) ⟨hr, hy⟩).differentiableWithinAt (by norm_num)).differentiableAt
          ((isOpen_Ioo.prod hO₀).mem_nhds ⟨hr, hy⟩)
      exact hjoint.comp y
        ((differentiableAt_const (c := r)).prodMk differentiableAt_id))
    (fun r hr ell y hy ↦ hbound i j ell (r, y) ⟨hr, hy⟩)
    k h z hh hz

/-- Exact forward product expansion of one row of the principal flux. -/
private theorem spatialDifferenceQuotient_principalFluxRow
     (A : TimeVelocity d → PDE.Mat d)
    (G : Fin d → TimeVelocity d → ℝ) (i k : Fin d) (h : ℝ) :
    spatialDifferenceQuotient k h (fun x ↦ ∑ j : Fin d, A x i j * G j x) =
      fun z ↦ ∑ j : Fin d, (
        spatialTranslate k h (fun x ↦ A x i j) z *
            spatialDifferenceQuotient k h (G j) z +
          spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j z) := by
  funext z
  simp only [spatialDifferenceQuotient_apply, spatialTranslate_apply]
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The absorbed source estimate only needs square integrability of the source
on the carrier on which the energy identity is integrated. -/
private theorem abs_setIntegral_source_mul_backwardQuotient_le_absorbed_weighted
     {S V : HypoellipticAleksandrov.Parabolic.Region d}
    (hS : MeasurableSet S) (hV : MeasurableSet V)
    (k : Fin d) (h : ℝ) (hh : h ≠ 0)
    (R psi qh Hk w : TimeVelocity d → ℝ) (lam Keta : ℝ)
    (hlam : 0 < lam) (hKeta : 0 ≤ Keta)
    (hR : ParabolicMemLpOn S 2 R) (hpsi : MemLp psi 2 )
    (hqh : ParabolicMemLpOn V 2 qh) (hHk : ParabolicMemLpOn V 2 Hk)
    (hwMeas : AEStronglyMeasurable w (timeVelocityVolumeOn V))
    (hDwMeas : AEStronglyMeasurable (fun z ↦ velocityGradient w z k)
      (timeVelocityVolumeOn V))
    (hwNonneg : ∀ z ∈ V, 0 ≤ w z) (hwLe : ∀ z ∈ V, w z ≤ 1)
    (hDwBound : ∀ z ∈ V, |velocityGradient w z k| ≤ 2 * Keta)
    (hSupport : tsupport (fun z ↦
      velocityGradient w z k * qh z + w z * Hk z) ⊆ V)
    (hweak : HasWeakVelocityPartialDerivOn Set.univ k psi (fun z ↦
      velocityGradient w z k * qh z + w z * Hk z))
    (henergyNonneg : 0 ≤ ∫ z in V, w z * Hk z ^ 2) :
    |∫ z in S, R z * spatialDifferenceQuotient k (-h) psi z| ≤
      (lam / 8) * (∫ z in V, w z * Hk z ^ 2) +
        (1 / 8) * ‖hqh.toLp qh‖ ^ 2 +
        (2 / lam + 8 * Keta ^ 2) * ‖hR.toLp R‖ ^ 2 := by
  let R0  := S.indicator R
  have hR0 : MemLp R0 2  := (memLp_indicator_iff_restrict hS).2 hR
  have hmain := abs_integral_source_mul_backwardQuotient_le_absorbed_weighted
    hV k h hh R0 psi qh Hk w lam Keta hlam hKeta hR0 hpsi hqh hHk
      hwMeas hDwMeas hwNonneg hwLe hDwBound hSupport hweak henergyNonneg
  have hnorm : ‖hR0.toLp R0‖ = ‖hR.toLp R‖ := by
    simp only [Lp.norm_toLp, R0, eLpNorm_indicator_eq_eLpNorm_restrict hS]
  rw [hnorm] at hmain
  have heq : (∫ z, R0 z * spatialDifferenceQuotient k (-h) psi z) =
      ∫ z in S, R z * spatialDifferenceQuotient k (-h) psi z := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    exact ae_of_all _ fun z ↦ by
      by_cases hz : z ∈ S <;> simp [R0, hz]
  rwa [heq] at hmain

/-- A bounded time-cutoff derivative controls the absolute time contribution;
no sign of the derivative is required. -/
private theorem abs_setIntegral_timeDerivative_mul_sq_le
     {V : HypoellipticAleksandrov.Parabolic.Region d} (hV : MeasurableSet V)
    (Q w : TimeVelocity d → ℝ) (Kzeta : ℝ)
    (hQ : ParabolicMemLpOn V 2 Q)
    (hint : Integrable (fun z ↦ timeDerivative w z * Q z ^ 2)
      (timeVelocityVolumeOn V))
    (hbound : ∀ z ∈ V, |timeDerivative w z| ≤ Kzeta)
    (hKzeta : 0 ≤ Kzeta) :
    |∫ z in V, timeDerivative w z * Q z ^ 2| ≤
      Kzeta * ‖hQ.toLp Q‖ ^ 2 := by
  let sharedTerm_5f775f620c := (∫ z in V, timeDerivative w z * Q z ^ 2)

  rw [abs_le]
  constructor
  · calc
      -(Kzeta * ‖hQ.toLp Q‖ ^ 2) =
          ∫ z in V, -(Kzeta * Q z ^ 2) := by
            rw [integral_neg, integral_const_mul,
              fixedCore_integral_sq_eq_norm_sq_toLp Q hQ]
      _ ≤ sharedTerm_5f775f620c := by
        apply integral_mono_ae
        · exact hQ.integrable_sq.const_mul Kzeta |>.neg
        · exact hint
        filter_upwards [ae_restrict_mem hV] with z hz
        have hzbound := hbound z hz
        rw [abs_le] at hzbound
        simpa only [neg_mul] using
          mul_le_mul_of_nonneg_right hzbound.1 (sq_nonneg (Q z))
  · calc
      sharedTerm_5f775f620c ≤
          ∫ z in V, Kzeta * Q z ^ 2 := by
        apply integral_mono_ae hint (hQ.integrable_sq.const_mul Kzeta)
        filter_upwards [ae_restrict_mem hV] with z hz
        exact mul_le_mul_of_nonneg_right
          ((le_abs_self _).trans (hbound z hz)) (sq_nonneg (Q z))
      _ = Kzeta * ‖hQ.toLp Q‖ ^ 2 := by
        rw [integral_const_mul, fixedCore_integral_sq_eq_norm_sq_toLp Q hQ]

/-- Restriction to a plateau carrier preserves every component's `L²`
membership and bounds the sum of its squared norms by the weighted outer
energy. -/
private theorem memLpOn_inner_and_sum_norm_sq_le_weighted
    {d n : ℕ} {outer inner : HypoellipticAleksandrov.Parabolic.Region d}
    (hOuter : MeasurableSet outer) (hInner : MeasurableSet inner)
    (hInnerOuter : inner ⊆ outer)
    (H : Fin n → TimeVelocity d → ℝ) (w : TimeVelocity d → ℝ)
    (hH : ∀ i, ParabolicMemLpOn outer 2 (H i))
    (hwMeas : AEStronglyMeasurable w (timeVelocityVolumeOn outer))
    (hwNonneg : ∀ z ∈ outer, 0 ≤ w z) (hwLe : ∀ z ∈ outer, w z ≤ 1)
    (hwOne : ∀ z ∈ inner, w z = 1) :
    (∀ i, ParabolicMemLpOn inner 2 (H i)) ∧
      ∑ i, ‖((hH i).mono hInnerOuter).toLp (H i)‖ ^ 2 ≤
        ∫ z in outer, w z * ∑ i, H i z ^ 2 := by
  let hHi (i : Fin n)  :=
    (hH i).mono hInnerOuter
  have hsumInt : Integrable (fun z ↦ ∑ i, H i z ^ 2)
      (timeVelocityVolumeOn outer) :=
    integrable_finset_sum _ fun i _ ↦ (hH i).integrable_sq

  refine ⟨hHi, ?_⟩
  calc
    ∑ i, ‖(hHi i).toLp (H i)‖ ^ 2 =
        ∫ z in inner, ∑ i, H i z ^ 2 := by
      rw [integral_finset_sum]
      · simp_rw [fixedCore_integral_sq_eq_norm_sq_toLp (H _) (hHi _)]
      · exact fun i _ ↦ (hHi i).integrable_sq
    _ = ∫ z in inner, w z * ∑ i, H i z ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hInner] with z hz
      rw [hwOne z hz, one_mul]
    _ ≤ ∫ z in outer, w z * ∑ i, H i z ^ 2 := by
      apply integral_mono_measure
      · exact Measure.restrict_mono hInnerOuter le_rfl
      · filter_upwards [ae_restrict_mem hOuter] with z hz
        exact mul_nonneg (hwNonneg z hz)
          (Finset.sum_nonneg fun i _ ↦ sq_nonneg (H i z))
      · exact (by
          refine Integrable.mono' hsumInt (hwMeas.mul hsumInt.1) ?_
          filter_upwards [ae_restrict_mem hOuter] with z hz
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hwNonneg z hz),
            abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ sq_nonneg (H i z))]
          exact mul_le_of_le_one_left
            (Finset.sum_nonneg fun i _ ↦ sq_nonneg (H i z)) (hwLe z hz))

/-- Scalar assembly for the Caccioppoli estimate.  Its equality and inequality
premises are outputs of the energy, coercivity, time, and source lemmas; this
private helper is not an admissible replacement for any of those PDE steps. -/
private theorem caccioppoli_combination_of_energy_bounds
    (lam Gamma Kzeta Keta E Ek flux time source qSq gSq rSq qNormSq gNormSq rNormSq : ℝ)
    (hlam : 0 < lam) (hE : 0 ≤ E) (hEkE : Ek ≤ E)
    (henergy : flux = -(1 / 2) * time + source)
    (hcoercive : (lam / 2) * E ≤ flux + Gamma * (qSq + gSq))
    (htime : |time| ≤ Kzeta * qSq)
    (hsource : |source| ≤ (lam / 8) * Ek + (1 / 8) * qSq +
      (2 / lam + 8 * Keta ^ 2) * rSq)
    (hqSq : qSq = qNormSq) (hgSq : gSq = gNormSq) (hrSq : rSq = rNormSq) :
    (lam / 4) * E ≤
      (Gamma + Kzeta / 2 + 1 / 8) * qNormSq + Gamma * gNormSq +
        (2 / lam + 8 * Keta ^ 2) * rNormSq := by
  have htimeUpper : -(1 / 2) * time ≤ (Kzeta / 2) * qSq := by
    have hnegTime : -time ≤ Kzeta * qSq := (neg_le_abs time).trans htime
    nlinarith
  have hsourceUpper : source ≤ (lam / 8) * Ek + (1 / 8) * qSq +
      (2 / lam + 8 * Keta ^ 2) * rSq :=
    (le_abs_self source).trans hsource
  rw [hqSq, hgSq] at hcoercive
  rw [hqSq] at htimeUpper
  rw [hqSq, hrSq] at hsourceUpper
  rw [henergy] at hcoercive
  nlinarith [mul_nonneg (le_of_lt hlam) hE]

private theorem caccioppoli_final_constant_bound
    (scale A beta qSq gSq rSq : ℝ)
    (hscale : 0 ≤ scale) (hA : 0 ≤ A) (hbeta : 0 ≤ beta)
    (hq : 0 ≤ qSq) (hg : 0 ≤ gSq) (hr : 0 ≤ rSq) :
    scale * (A * gSq + beta * rSq) ≤
      (scale * (A + beta + 1)) * (qSq + gSq + rSq) := by

  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hscale
  calc
    A * gSq + beta * rSq ≤ A * (qSq + gSq + rSq) +
        beta * (qSq + gSq + rSq) := by
      gcongr <;> linarith
    _ = (A + beta) * (qSq + gSq + rSq) := by ring
    _ ≤ (A + beta + 1) * (qSq + gSq + rSq) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- Uniform one-direction spatial difference-quotient control for the gradient
in a tested divergence-form equation. -/
theorem exists_fixedDirection_gradient_spatialDifferenceQuotient_estimate_of_testedEquation
    (d : ℕ) (s₀ t₁ t₂ s₁ : ℝ)
    (hs₀t₁ : s₀ < t₁) (ht₁t₂ : t₁ < t₂) (ht₂s₁ : t₂ < s₁)
    (O₀ O₁ : PDE.VelocityRegion d)
    (hO₀ : IsOpen O₀) (hO₁ : IsOpen O₁) (hO₁ne : O₁.Nonempty)
    (hO₁compact : IsCompact (closure O₁))
    (hO₁O₀ : closure O₁ ⊆ O₀)
    (lam Lam Ma : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hMa : 0 ≤ Ma) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ (A : TimeVelocity d → PDE.Mat d) (q : TimeVelocity d → ℝ)
        (G : Fin d → TimeVelocity d → ℝ) (R : TimeVelocity d → ℝ),
        (∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O₀, (A z).IsSymm) →
        (∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O₀,
          lam • (1 : PDE.Mat d) ≤ A z ∧ A z ≤ Lam • (1 : PDE.Mat d)) →
        (∀ i j, ContDiffOn ℝ 1 (fun z  => A z i j)
          (Set.Ioo s₀ s₁ ×ˢ O₀)) →
        (∀ i j k z, z ∈ Set.Ioo s₀ s₁ ×ˢ O₀ →
          |spatialPartial k
              (fun y  => A (z.1, y) i j) z.2| ≤ Ma) →
        ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O₀) 2 q →
        (∀ j, ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O₀) 2 (G j)) →
        ParabolicMemLpOn (Set.Ioo s₀ s₁ ×ˢ O₀) 2 R →
        (∀ j, HasWeakVelocityPartialDerivOn
          (Set.Ioo s₀ s₁ ×ˢ O₀) j q (G j)) →
        (∀ φ : TimeVelocity d → ℝ,
          ContDiff ℝ PDE.smoothOrder φ → HasCompactSupport φ →
          tsupport φ ⊆ Set.Ioo s₀ s₁ ×ˢ O₀ →
          -(∫ z in Set.Ioo s₀ s₁ ×ˢ O₀,
              q z * timeDerivative φ z) -
              (∑ i, ∑ j, ∫ z in Set.Ioo s₀ s₁ ×ˢ O₀,
                A z i j * G j z * velocityGradient φ z i) =
            ∫ z in Set.Ioo s₀ s₁ ×ˢ O₀, R z * φ z) →
        ∀ k : Fin d, ∀ h : ℝ, 0 < h → h < δ →
          (∀ j, ParabolicMemLpOn (Set.Ioo t₁ t₂ ×ˢ O₁) 2
            (spatialDifferenceQuotient k h (G j))) ∧
          (∑ j, (ENNReal.toReal (eLpNorm
            (spatialDifferenceQuotient k h (G j)) 2
            (timeVelocityVolumeOn (Set.Ioo t₁ t₂ ×ˢ O₁)))) ^ 2) ≤
            C * ((ENNReal.toReal (eLpNorm q 2
              (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O₀)))) ^ 2 +
              (∑ j, (ENNReal.toReal (eLpNorm (G j) 2
                (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O₀)))) ^ 2) +
              (ENNReal.toReal (eLpNorm R 2
                (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O₀)))) ^ 2) := by
  classical
  obtain ⟨O₂, Keta, eta, δ, hO₂, hO₂compact, hO₁O₂, hO₂O₀,
      hKeta, hδ, hcarrier⟩ :=
    exists_intermediateSpatialCutoff_signedCollar O₀ O₁ hO₀ hO₁compact hO₁O₀
  obtain ⟨zeta, Kzeta, hzetaSmooth, hzetaCompact, hKzeta, hzetaNonneg,
      hzetaLe, hzetaOne, hzetaSupport, hzetaDeriv⟩ :=
    exists_smooth_timePlateau_with_deriv_bound s₀ t₁ t₂ s₁
      hs₀t₁ ht₁t₂.le ht₂s₁
  let Gamma : ℝ :=
    8 * (d : ℝ) ^ 3 / lam * Lam ^ 2 * Keta ^ 2 +
      2 * (d : ℝ) ^ 2 / lam * Ma ^ 2 +
      ((d : ℝ) ^ 2 + (d : ℝ)) * Ma * Keta
  let beta : ℝ := 2 / lam + 8 * Keta ^ 2
  let C : ℝ := (4 / lam) * (2 * Gamma + Kzeta / 2 + 1 / 8 + beta + 1)



  refine ⟨C, δ, (by
      dsimp [C]
      positivity), hδ, ?_⟩
  intro A q G R hSymm hEll hA hAbound hq hG hR hWeak hEq k h hh hhd
  let S : HypoellipticAleksandrov.Parabolic.Region d := Ioo s₀ s₁ ×ˢ O₀
  let V : HypoellipticAleksandrov.Parabolic.Region d := Ioo s₀ s₁ ×ˢ O₂
  let inner : HypoellipticAleksandrov.Parabolic.Region d := Ioo t₁ t₂ ×ˢ O₁
  let w : TimeVelocity d → ℝ := fun z ↦ zeta z.1 * eta z.2 ^ 2
  let Q  := spatialDifferenceQuotient k h q
  let H  := fun i ↦ spatialDifferenceQuotient k h (G i)
  have hSopen : IsOpen S := isOpen_Ioo.prod hO₀
  have hVopen : IsOpen V := isOpen_Ioo.prod hO₂
  have hSmeas  := hSopen.measurableSet
  have hVmeas  := hVopen.measurableSet

  have hVS : V ⊆ S := prod_mono_right (subset_closure.trans hO₂O₀)

  have habsh : |h| ≤ δ := by rw [abs_of_pos hh]; exact hhd.le

  have hshiftV : MapsTo (spatialShift k h) V S :=
    mapsTo_spatialShift_prod_of_carrier hcarrier habsh k
  obtain ⟨hQ, hQnorm⟩ :=
    exists_spatialDifferenceQuotient_memLp_norm_le_on_inner k hSopen q (G k)
      hq (hG k) (hWeak k) h hh.ne' (segment_spatialShift_subset_prod_of_carrier hcarrier habsh k)
  have hH (i : Fin d) : ParabolicMemLpOn V 2 (H i) := (hG i).spatialDifferenceQuotient_of_subset_mapsTo k h hVS hshiftV
  have hQweak (i : Fin d) : HasWeakVelocityPartialDerivOn V i Q (H i) := (hWeak i).spatialDifferenceQuotient_of_subset_mapsTo
      (hq.locallyIntegrableOn (by norm_num))
      ((hG i).locallyIntegrableOn (by norm_num)) k h hVS hshiftV
  obtain ⟨hwSmooth, hwCompact, hwSupportS, hwShiftS, hwTime, hwGrad,
      hwTimeBound, hwGradBound, hwBounds, hwGradSq, hwSq, hwOne⟩ :=
    productCutoff_data hO₂O₀ hcarrier eta zeta hzetaSmooth hzetaCompact
      hzetaNonneg hzetaLe hzetaOne hzetaSupport hzetaDeriv
  have hwSupportV : tsupport w ⊆ V := by
    refine (productCutoff_tsupport_subset zeta eta).trans ?_
    intro z hz
    exact ⟨hzetaSupport hz.1, eta.tsupport_subset hz.2⟩
  obtain ⟨hpsi, hDpsi, hpsiWeak, hpsiSupport, hDpsiSupport⟩ :=
    localized_spatialDifferenceQuotient_weakJet_global hVopen Q H hQ hH hQweak
      w hwSmooth hwCompact hwSupportV
  have hFlux (i j : Fin d) (K : HypoellipticAleksandrov.Parabolic.Region d)
      (hK : IsCompact K) (hKS : K ⊆ S)  :=
    fluxEntry_parabolicMemLpOn_compact hK hKS hlam hlamLam A hEll hA G hG i j
  obtain ⟨htimeInt, hfluxInt, hsourceInt, henergy⟩ :=
    integral_spatialDifferenceQuotient_energyIdentity_of_testedEquation d S hSopen
      A q R G hq hR hG hFlux hWeak hEq w hwSmooth hwCompact hwSupportS
      k h hh.ne' (hwShiftS k h habsh)
  have hrow (i : Fin d) := spatialDifferenceQuotient_principalFluxRow A G i k h
  have hfluxInt' (i : Fin d) : Integrable (fun z ↦
      (∑ j : Fin d,
        (spatialTranslate k h (fun x ↦ A x i j) z * H j z +
          spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j z)) *
        (velocityGradient w z i * Q z + w z * H i z))
      (timeVelocityVolumeOn S) := by
    simpa only [Q, H, hrow i, IntegrableOn, timeVelocityVolumeOn] using hfluxInt i
  have hOff : ∀ z ∈ S, z ∉ V →
      w z = 0 ∧ ∀ i, velocityGradient w z i = 0 := by
    intro z hzS hzV
    constructor
    · by_contra hn
      exact hzV (hwSupportV (subset_tsupport w hn))
    · intro i
      by_contra hn
      exact hzV ((_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_tsupport_subset.trans hwSupportV)
        (subset_tsupport _ hn))


  have hdpos : 0 < d := Nat.pos_of_ne_zero (by
    intro hd0
    subst d
    exact Fin.elim0 k)
  have hcoercive :=
    setIntegral_fixedDirection_fluxPairing_coercive_absorbed_on_safeCarrier
      hSmeas hVmeas hVS A G H w Q k h lam Lam Ma Keta hdpos hlam hMa hKeta
      hwSmooth.continuous.aestronglyMeasurable (fun z hz ↦ (hwBounds z).1)
      (fun z hz ↦ (hwBounds z).2) hOff (by
          intro z hz
          exact hEll _ (hshiftV hz)) (by
          intro z hz i j
          exact coefficient_spatialDifferenceQuotient_bound hO₀ hcarrier habsh A hA
            hAbound i j k z hz)
      (fun z hz i ↦ hwGradSq i z) hQ (fun j ↦ (hG j).mono hVS) hH
      hDpsiSupport hfluxInt'
  have hsource := abs_setIntegral_source_mul_backwardQuotient_le_absorbed_weighted
    hSmeas hVmeas k h hh.ne' R (fun z ↦ w z * Q z) Q (H k) w lam Keta
    hlam hKeta hR hpsi hQ (hH k)
    hwSmooth.continuous.aestronglyMeasurable
    (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_contDiff_infty hwSmooth).continuous.aestronglyMeasurable
    (fun z hz ↦ (hwBounds z).1) (fun z hz ↦ (hwBounds z).2)
    (fun z hz ↦ hwGradBound k z) (hDpsiSupport k) (hpsiWeak k)
    (integral_nonneg_of_ae (ae_of_all _ fun z ↦
      mul_nonneg (hwBounds z).1 (sq_nonneg (H k z))))

  have htime := abs_setIntegral_timeDerivative_mul_sq_le hVmeas Q w Kzeta hQ
    (htimeInt.mono_set hVS)
    (fun z hz ↦ hwTimeBound z) hKzeta
  have htimeSV : (∫ z in S, timeDerivative w z * Q z ^ 2) =
      ∫ z in V, timeDerivative w z * Q z ^ 2 := by
    rw [← integral_indicator hSmeas, ← integral_indicator hVmeas]
    apply integral_congr_ae
    exact ae_of_all _ fun z ↦ by
      by_cases hzV : z ∈ V
      · simp [hzV, hVS hzV]
      · by_cases hzS : z ∈ S
        · have hzero : timeDerivative w z = 0 := by
            by_contra hn
            exact hzV ((fixedCore_timeDerivative_tsupport_subset.trans hwSupportV)
              (subset_tsupport _ hn))
          simp [hzV, hzS, hzero]
        · simp [hzV, hzS]
  have henergy' :
      (∑ i, ∫ z in S,
        (∑ j : Fin d,
          (spatialTranslate k h (fun x ↦ A x i j) z * H j z +
            spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j z)) *
          (velocityGradient w z i * Q z + w z * H i z)) =
        -(1 / 2) * (∫ z in S, timeDerivative w z * Q z ^ 2) +
          (∫ z in S, R z * spatialDifferenceQuotient k (-h)
            (fun x ↦ w x * Q x) z) := by

    simp only [Q, H, hrow] at henergy ⊢
    linarith
  have hEV : (∫ z in S, w z * ∑ i, H i z ^ 2) =
      ∫ z in V, w z * ∑ i, H i z ^ 2 := by
    rw [← integral_indicator hSmeas, ← integral_indicator hVmeas]
    apply integral_congr_ae
    exact ae_of_all _ fun z ↦ by
      by_cases hzV : z ∈ V
      · simp [hzV, hVS hzV]
      · by_cases hzS : z ∈ S
        · simp [hzV, hzS, (hOff z hzS hzV).1]
        · simp [hzV, hzS]
  rw [hEV] at hcoercive
  have hqSq : (∫ z in V, Q z ^ 2) = ‖hQ.toLp Q‖ ^ 2 :=
    fixedCore_integral_sq_eq_norm_sq_toLp Q hQ

  have hrSq : (∫ z in S, R z ^ 2) = ‖hR.toLp R‖ ^ 2 :=
    fixedCore_integral_sq_eq_norm_sq_toLp R hR


  have hwMeasV : AEStronglyMeasurable w (timeVelocityVolumeOn V) :=
    hwSmooth.continuous.aestronglyMeasurable


  have hcomb := caccioppoli_combination_of_energy_bounds lam Gamma Kzeta Keta
    (∫ z in V, w z * ∑ i, H i z ^ 2)
    (∫ z in V, w z * H k z ^ 2)
    (∑ i, ∫ z in S,
      (∑ j : Fin d,
        (spatialTranslate k h (fun x ↦ A x i j) z * H j z +
          spatialDifferenceQuotient k h (fun x ↦ A x i j) z * G j z)) *
        (velocityGradient w z i * Q z + w z * H i z))
    (∫ z in S, timeDerivative w z * Q z ^ 2)
    (∫ z in S, R z * spatialDifferenceQuotient k (-h)
      (fun x ↦ w x * Q x) z)
    (∫ z in V, Q z ^ 2) (∑ j, ∫ z in V, G j z ^ 2) (∫ z in S, R z ^ 2)
    (‖hQ.toLp Q‖ ^ 2) (∑ j, ‖((hG j).mono hVS).toLp (G j)‖ ^ 2)
    (‖hR.toLp R‖ ^ 2) hlam
    (integral_nonneg_of_ae (ae_of_all _ fun z ↦ mul_nonneg (hwBounds z).1
      (Finset.sum_nonneg fun i _ ↦ sq_nonneg (H i z))))
    (integral_mono_ae (by
        refine Integrable.mono' (hH k).integrable_sq
          (hwMeasV.mul (hH k).integrable_sq.1) ?_
        filter_upwards [ae_restrict_mem hVmeas] with z hz
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hwBounds z).1,
          abs_of_nonneg (sq_nonneg (H k z))]
        exact mul_le_of_le_one_left (sq_nonneg _) (hwBounds z).2) (by
        have hsumInt : Integrable (fun z ↦ ∑ i, H i z ^ 2)
            (timeVelocityVolumeOn V) :=
          integrable_finset_sum _ fun i _ ↦ (hH i).integrable_sq
        refine Integrable.mono' hsumInt (hwMeasV.mul hsumInt.1) ?_
        filter_upwards [ae_restrict_mem hVmeas] with z hz
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hwBounds z).1,
          abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ sq_nonneg (H i z))]
        exact mul_le_of_le_one_left
          (Finset.sum_nonneg fun i _ ↦ sq_nonneg (H i z)) (hwBounds z).2) (by
      filter_upwards [ae_restrict_mem hVmeas] with z hz
      exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun i _ ↦ sq_nonneg (H i z)) (Finset.mem_univ k))
        (hwBounds z).1)) henergy' hcoercive (by
            rw [htimeSV, hqSq]
            exact htime) (by
            rw [hqSq, hrSq]
            exact hsource) hqSq (by
            apply Finset.sum_congr rfl
            intro j _
            exact fixedCore_integral_sq_eq_norm_sq_toLp (G j) _) hrSq
  obtain ⟨hinnerH, hplateau⟩ := memLpOn_inner_and_sum_norm_sq_le_weighted
    hVmeas ((isOpen_Ioo.prod hO₁).measurableSet) (by
        rintro z ⟨hztime, hzspace⟩
        exact ⟨⟨hs₀t₁.trans hztime.1, hztime.2.trans ht₂s₁⟩,
          hO₁O₂ (subset_closure hzspace)⟩) H w hH
    hwSmooth.continuous.aestronglyMeasurable (fun z hz ↦ (hwBounds z).1)
    (fun z hz ↦ (hwBounds z).2) hwOne
  refine ⟨hinnerH, ?_⟩
  have hGmonoSq (j : Fin d) :
      ‖((hG j).mono hVS).toLp (G j)‖ ^ 2 ≤ ‖(hG j).toLp (G j)‖ ^ 2 := by
    rw [← fixedCore_integral_sq_eq_norm_sq_toLp (G j) ((hG j).mono hVS),
      ← fixedCore_integral_sq_eq_norm_sq_toLp (G j) (hG j)]
    exact integral_mono_measure (Measure.restrict_mono_set volume hVS)
      (ae_of_all _ fun z ↦ sq_nonneg (G j z)) (hG j).integrable_sq

  have hGkSum : ‖(hG k).toLp (G k)‖ ^ 2 ≤
      ∑ j, ‖(hG j).toLp (G j)‖ ^ 2 :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖(hG j).toLp (G j)‖)
      (Finset.mem_univ k)
  have hscaled : ∑ j, ‖(hinnerH j).toLp (H j)‖ ^ 2 ≤
      (4 / lam) * ((2 * Gamma + Kzeta / 2 + 1 / 8) *
        (∑ j, ‖(hG j).toLp (G j)‖ ^ 2) + beta * ‖hR.toLp R‖ ^ 2) := by
    calc
      _ ≤ ∫ z in V, w z * ∑ i, H i z ^ 2 := hplateau
      _ ≤ (4 / lam) * ((Gamma + Kzeta / 2 + 1 / 8) * ‖hQ.toLp Q‖ ^ 2 +
          Gamma * (∑ j, ‖((hG j).mono hVS).toLp (G j)‖ ^ 2) +
          beta * ‖hR.toLp R‖ ^ 2) := by
        calc
          _ = (4 / lam) * ((lam / 4) *
              ∫ z in V, w z * ∑ i, H i z ^ 2) := by
                field_simp [ne_of_gt hlam]
          _ ≤ _ := mul_le_mul_of_nonneg_left (hcomb)
            (by positivity)
      _ ≤ _ := by
        let sharedTerm_d025fb7cf9 := (∑ j, ‖(hG j).toLp (G j)‖ ^ 2)
        let sharedTerm_2f633e22f6 := (Gamma + Kzeta / 2 + 1 / 8)

        have hA : 0 ≤ sharedTerm_2f633e22f6 := by positivity

        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          (sharedTerm_2f633e22f6) * ‖hQ.toLp Q‖ ^ 2 +
                Gamma * (∑ j, ‖((hG j).mono hVS).toLp (G j)‖ ^ 2) +
                beta * ‖hR.toLp R‖ ^ 2
              ≤ (sharedTerm_2f633e22f6) * ‖(hG k).toLp (G k)‖ ^ 2 +
                Gamma * (sharedTerm_d025fb7cf9) +
                beta * ‖hR.toLp R‖ ^ 2 := add_le_add (add_le_add (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hQnorm) hA)
              (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ ↦ hGmonoSq j) (by
                  dsimp [Gamma]
                  positivity))) le_rfl
          _ ≤ (sharedTerm_2f633e22f6) *
                (sharedTerm_d025fb7cf9) +
                Gamma * (sharedTerm_d025fb7cf9) +
                beta * ‖hR.toLp R‖ ^ 2 := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hGkSum hA)
              le_rfl) le_rfl
          _ = (2 * Gamma + Kzeta / 2 + 1 / 8) *
                (sharedTerm_d025fb7cf9) +
                beta * ‖hR.toLp R‖ ^ 2 := by ring
  have hfinal := caccioppoli_final_constant_bound (4 / lam)
    (2 * Gamma + Kzeta / 2 + 1 / 8) beta
    ((ENNReal.toReal (eLpNorm q 2 (timeVelocityVolumeOn S))) ^ 2)
    (∑ j, (ENNReal.toReal (eLpNorm (G j) 2 (timeVelocityVolumeOn S))) ^ 2)
    ((ENNReal.toReal (eLpNorm R 2 (timeVelocityVolumeOn S))) ^ 2)
    (by positivity) (by positivity) (by
        dsimp [beta]
        positivity) (sq_nonneg _)
    (Finset.sum_nonneg fun j _ ↦ sq_nonneg _) (sq_nonneg _)
  have hscaled' : ∑ j, (ENNReal.toReal (eLpNorm
      (spatialDifferenceQuotient k h (G j)) 2
      (timeVelocityVolumeOn inner))) ^ 2 ≤
      (4 / lam) * ((2 * Gamma + Kzeta / 2 + 1 / 8) *
        (∑ j, (ENNReal.toReal (eLpNorm (G j) 2
          (timeVelocityVolumeOn S))) ^ 2) + beta *
        (ENNReal.toReal (eLpNorm R 2 (timeVelocityVolumeOn S))) ^ 2) := by
    simpa only [H, Lp.norm_toLp] using hscaled
  simpa only [C, S, inner] using hscaled'.trans hfinal

end HypoellipticAleksandrov.Parabolic
