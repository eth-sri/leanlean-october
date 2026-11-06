module

public import RequestProject.PhysicalDrivenHardyRegularity


public import RequestProject.PlanarTypes
public import RequestProject.CirclePeriod

public import RequestProject.PlanarGeometry

public import RequestProject.RoughVekuaTransport
public import RequestProject.PhysicalDrivenReconstruction

/-
The factorial gauge of the genuine rough driven vector.  Only its zeroth
row contains the L2 primitive.  The entire regular correction is retained,
and the positive-row AC equations give the actual moment recurrence.
This module is part of the verified dependency chain.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open AbsolutelyContinuousOnInterval
open scoped Topology ComplexConjugate


local notation "μB" => volume.restrict boundaryHalfOpenInterval

theorem common_roughGauge_continuous_mul_memLp {a f : ComplexCurve}
    (ha : Continuous a) (hf : MemLp f 2 μB) : MemLp (fun θ => a θ * f θ) 2 μB := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn ha.continuousOn
  apply hf.of_le_mul (c := C) (ha.aestronglyMeasurable.restrict.mul hf.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  change ‖a θ * f θ‖ ≤ C * ‖f θ‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC θ (Ioc_subset_Icc_self hθ)) (norm_nonneg _)

section GenuineGauge

variable {γ : ComplexCurve} {E : ℝ} {W : ℝ → ComplexEnd Ell2}
local notation "gaugeFixed" => physicalDrivenGauge γ E

local notation "gaugePartialFixedHere" => physicalDrivenGaugePartial γ E

local notation "gaugeTermFixed" => physicalDrivenGaugeTerm γ E

local notation "regularCorrectionFixedHere" => roughVekuaRegularCorrection γ E W


section
variable (p : BoundaryL2) (m α : ℂ)
local notation "drivenVectorFixedHere" => roughVekuaDrivenVector γ E W p m α

include p m α

theorem roughVekuaGauge_scaledRow_zero_split θ :
    physicalDrivenScaledRow E (drivenVectorFixedHere) 0 θ =
      -Complex.I * p θ +
        physicalDrivenScaledRow E (regularCorrectionFixedHere p m α) 0 θ := by
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp_all
  simp only [physicalDrivenScaledRow, physicalDrivenRow, if_true, roughVekuaDrivenVector, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, basisVec_coord]
  field_simp 

theorem roughVekuaGauge_scaledRow_succ_eq n θ :
    physicalDrivenScaledRow E (drivenVectorFixedHere) (n + 1) θ =
      physicalDrivenScaledRow E (regularCorrectionFixedHere p m α) (n + 1) θ := by
  simp  [physicalDrivenScaledRow, physicalDrivenRow, roughVekuaDrivenVector_positive_coord]

theorem roughVekuaGauge_partial_succ_eq j N θ :
    gaugePartialFixedHere (drivenVectorFixedHere) (j + 1) N θ =
      gaugePartialFixedHere (regularCorrectionFixedHere p m α) (j + 1) N θ := by
  apply Finset.sum_congr rfl
  grind only [physicalDrivenGaugeTerm, roughVekuaGauge_scaledRow_succ_eq]

theorem roughVekuaGauge_succ_eq j θ :
    gaugeFixed (drivenVectorFixedHere) (j + 1) θ =
      gaugeFixed (regularCorrectionFixedHere p m α) (j + 1) θ := by
  apply tsum_congr
  grind only [physicalDrivenGaugeTerm, roughVekuaGauge_scaledRow_succ_eq]

/-- The full zeroth gauge includes the actual rough primitive, with its
original scalar and its entire regular correction. -/
theorem roughVekuaGauge_zero_split θ :
    gaugeFixed (drivenVectorFixedHere) 0 θ =
      -Complex.I * p θ + gaugeFixed
        (regularCorrectionFixedHere p m α) 0 θ := by
  have hs := (summable_norm_physicalDrivenGaugeTerm γ E
    (drivenVectorFixedHere) 0 θ).of_norm
  have ht := (summable_norm_physicalDrivenGaugeTerm γ E
    (regularCorrectionFixedHere p m α) 0 θ).of_norm
  rw [physicalDrivenGauge, hs.tsum_eq_zero_add, physicalDrivenGauge, ht.tsum_eq_zero_add]
  simp_all [physicalDrivenGaugeTerm,   roughVekuaGauge_scaledRow_succ_eq, physicalDrivenPower, roughVekuaGauge_scaledRow_zero_split] <;> ring

theorem roughVekuaGauge_partial_zero_split N θ :
    gaugePartialFixedHere (drivenVectorFixedHere) 0 N θ =
      -Complex.I * p θ + gaugePartialFixedHere
        (regularCorrectionFixedHere p m α) 0 N θ := by
  induction N with
  | zero =>
    simp_all [physicalDrivenGaugePartial, physicalDrivenGaugeTerm, physicalDrivenPower, roughVekuaGauge_scaledRow_zero_split]
  | succ N ih =>
    simp  [physicalDrivenGaugePartial, Finset.sum_range_succ] at ih ⊢
    grind only [physicalDrivenGaugeTerm, roughVekuaGauge_scaledRow_succ_eq]

end


variable {K } (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    (hW : IsTransport γ E W)

section
variable (p : BoundaryL2) (m α : ℂ)
local notation "drivenVectorFixed" => roughVekuaDrivenVector γ E W p m α

local notation "gaugePartialFixed" => gaugePartialFixedHere

local notation "momentPartialFixed" => physicalDrivenMomentPartial γ E

include p m α

section
include hK hγ hW

theorem roughVekuaGauge_regular_memLp j :
    MemLp (gaugeFixed (regularCorrectionFixedHere p m α) j) 2 μB := driven_realization_continuousOn_memLp (physicalDrivenGauge_continuousOn γ hγ.continuous E _
    (roughVekuaRegularCorrection_continuousOn hK hγ hW p m α) j)

theorem roughVekuaGauge_zero_memLp :
    MemLp (gaugeFixed drivenVectorFixed 0) 2 μB := by
  have h := ((Lp.memLp p).const_smul (-Complex.I)).add
    (roughVekuaGauge_regular_memLp hK hγ hW p m α 0)
  exact MemLp.ae_eq (Eventually.of_forall fun θ => by
    change (-Complex.I) * (p θ) +
      gaugeFixed (regularCorrectionFixedHere p m α) 0 θ = _
    rw [roughVekuaGauge_zero_split]) h

private theorem roughGauge_regular_row_ac n :
    AbsolutelyContinuousOnInterval
      (physicalDrivenScaledRow E (regularCorrectionFixedHere p m α) n)
      0 circlePeriod := by
  have hc := absolutelyContinuousOnInterval_clm_comp (innerSL ℂ (basisVec n))
    (roughVekuaRegularCorrection_absolutelyContinuous hK hγ hW p m α)
  by_cases hn : n = 0
  · subst n
    convert hc.const_smul (Real.sqrt 2) using 1 <;>
      ext θ <;>
      simp  [physicalDrivenScaledRow, physicalDrivenRow, inner_basisVec]
  · convert hc.const_smul (physicalDrivenQ E ^ n) using 1 <;>
      ext θ <;>
      simp  [physicalDrivenScaledRow, physicalDrivenRow, hn, inner_basisVec]

private theorem roughGauge_regular_partial_ac j N :
    AbsolutelyContinuousOnInterval
      (gaugePartialFixed (regularCorrectionFixedHere p m α) j N)
      0 circlePeriod := by
  have ht (l : ℕ) : AbsolutelyContinuousOnInterval
      (gaugeTermFixed (regularCorrectionFixedHere p m α) j l)
      0 circlePeriod := by
    have hp : ContDiff ℝ 1 (physicalDrivenPower γ l) := by
      unfold physicalDrivenPower physicalDrivenCentered
      fun_prop
    unfold physicalDrivenGaugeTerm
    simpa  [Pi.mul_def] using
      (common_driven_c1_absolutelyContinuous hp).smul (roughGauge_regular_row_ac hK hγ hW p m α (l + j))
  induction N with
  | zero =>
    have he : gaugePartialFixed (regularCorrectionFixedHere p m α) j 0 =
        gaugeTermFixed (regularCorrectionFixedHere p m α) j 0 := by
      funext θ
      exact Finset.sum_range_one _
    rw [he]
    exact ht 0
  | succ N ih =>
    have he : gaugePartialFixed (regularCorrectionFixedHere p m α)
        j (N + 1) = ((gaugePartialFixed (regularCorrectionFixedHere p m α) j N + gaugeTermFixed (regularCorrectionFixedHere p m α) j (N + 1))) := by
      funext θ
      exact Finset.sum_range_succ _ _
    rw [he]
    exact ih.add (ht (N + 1))

private theorem roughGauge_partial_succ_ac j N :
    AbsolutelyContinuousOnInterval
      (gaugePartialFixed drivenVectorFixed (j + 1) N)
      0 circlePeriod := by
  have he : gaugePartialFixed drivenVectorFixed (j + 1) N =
      gaugePartialFixed (regularCorrectionFixedHere p m α) (j + 1) N :=
    funext (roughVekuaGauge_partial_succ_eq p m α j N)
  grind only [roughGauge_regular_partial_ac]

theorem roughVekuaGauge_partial_succ_ae_hasDerivAt j N :
    ∀ᵐ θ, θ ∈ Ioo 0 circlePeriod →
      HasDerivAt
        (gaugePartialFixed drivenVectorFixed (j + 1) N)
        (physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
          gaugePartialFixed drivenVectorFixed j N θ +
          deriv γ θ * physicalDrivenPower γ N θ * physicalDrivenScaledRow E
            drivenVectorFixed (N + j + 2) θ) θ := by
  induction N with
  | zero =>
    filter_upwards [roughVekuaDrivenScaledRow_succ_ae_hasDerivAt hK hγ hW p m α j]
      with θ hθ hmem
    convert hθ hmem using 1
    · ext <;> simp_all [physicalDrivenGaugePartial, physicalDrivenGaugeTerm, physicalDrivenPower, physicalDrivenScaledRow, physicalDrivenRow]
    · simp [physicalDrivenGaugePartial, physicalDrivenGaugeTerm, physicalDrivenPower]
      ring
  | succ N ih =>
    filter_upwards [ih, roughVekuaDrivenScaledRow_succ_ae_hasDerivAt hK hγ hW p m α
      (N + j + 1)] with θ hθ hd hmem
    have hp := physicalDrivenPower_hasDerivAt_succ hγ N θ
    have he (k : ℕ) : gaugePartialFixed
        drivenVectorFixed k (N + 1) = fun s =>
          gaugePartialFixed drivenVectorFixed k N s +
            gaugeTermFixed drivenVectorFixed k (N + 1) s := by
      funext s
      exact Finset.sum_range_succ _ _
    rw [he]
    convert (hθ hmem).add (hp.mul (hd hmem)) using 1
    · funext s
      simp  [physicalDrivenGaugeTerm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Pi.add_apply, Pi.mul_apply]
    grind only [physicalDrivenGaugeTerm, PolyaNeumann.physicalDrivenQ, PolyaNeumann.physicalDrivenPower]

private theorem roughGauge_partial_memLp j N :
    MemLp (gaugePartialFixed drivenVectorFixed j N) 2 μB := by
  have hv := roughVekuaRegularCorrection_continuousOn hK hγ hW p m α
  have hc := physicalDrivenGaugePartial_continuousOn γ hγ.continuous E _ hv j N
  cases j with
  | zero =>
    exact MemLp.ae_eq (Eventually.of_forall fun θ => by
      change (-Complex.I) * (p θ) +
        gaugePartialFixed (regularCorrectionFixedHere p m α) 0 N θ = _
      rw [roughVekuaGauge_partial_zero_split])
      (((Lp.memLp p).const_smul (-Complex.I)).add (driven_realization_continuousOn_memLp hc))
  | succ j =>
    exact MemLp.ae_eq (Eventually.of_forall fun θ => by
      rw [roughVekuaGauge_partial_succ_eq]) (driven_realization_continuousOn_memLp hc)

end


include hW in
private theorem roughGauge_partial_succ_zero j N :
    gaugePartialFixed drivenVectorFixed (j + 1) N 0 = 0 := by
  apply Finset.sum_eq_zero
  intro l _
  rw [physicalDrivenGaugeTerm, show l + (j + 1) = (l + j) + 1 by omega,
    physicalDrivenScaledRow, roughVekuaDrivenRow_succ_zero hW]
  simp

private theorem roughGauge_partial_succ_endpoint
    (hα : regularCorrectionFixedHere p m α circlePeriod = α • basisVec 0)
    (j N : ℕ) :
    gaugePartialFixed drivenVectorFixed (j + 1) N
      circlePeriod = 0 := by
  apply Finset.sum_eq_zero
  intro l _
  rw [physicalDrivenGaugeTerm, show l + (j + 1) = (l + j) + 1 by omega,
    physicalDrivenScaledRow, roughVekuaDrivenRow_succ_endpoint p m α hα]
  simp

section
include hK hγ hW

/-- Actual AC integration by parts for the positive finite gauge. The
zeroth gauge is used only as an L2 integrand, and the finite tail remains. -/
theorem roughVekuaGauge_momentPartial_recurrence
    (hα : regularCorrectionFixedHere p m α circlePeriod = α • basisVec 0)
    (j N k : ℕ) :
    physicalDrivenQ E ^ 2 * momentPartialFixed
      drivenVectorFixed j N k +
      (k : ℂ) * momentPartialFixed
        drivenVectorFixed (j + 1) N (k - 1) =
      -physicalDrivenTailMoment γ E drivenVectorFixed j N k := by
  let f := drivenVectorFixed
  let z  := fun θ => conj (physicalDrivenCentered γ θ)
  let s := gaugePartialFixed f (j + 1) N
  let a  := fun θ => conj (deriv γ θ) * gaugePartialFixed f j N θ * z θ ^ k
  let b  := fun θ => conj (deriv γ θ) * s θ * z θ ^ (k - 1)
  let t  := fun θ => deriv γ θ * physicalDrivenPower γ N θ *
    physicalDrivenScaledRow E f (N + j + 2) θ * z θ ^ k
  let r  := fun θ => physicalDrivenQ E ^ 2 * a θ + k * b θ + t θ
  have hz1 : ContDiff ℝ 1 z :=
    Complex.conjCLE.contDiff.comp (hγ.sub contDiff_const)
  have hsz := (roughGauge_partial_succ_ac hK hγ hW p m α j N).smul
    (common_driven_c1_absolutelyContinuous (hz1.pow k))
  have hsz' : AbsolutelyContinuousOnInterval (fun θ => s θ * z θ ^ k) 0 circlePeriod := by
    assumption
  have ha : MemLp a 2 μB := by
    have hw : Continuous (fun θ => conj (deriv γ θ) * z θ ^ k) :=
      (Complex.continuous_conj.comp hγ.continuous_deriv_one).mul (hz1.continuous.pow k)
    simpa only [a, f, mul_assoc, mul_left_comm, mul_comm] using
      common_roughGauge_continuous_mul_memLp hw (roughGauge_partial_memLp hK hγ hW p m α j N)
  have hb : MemLp b 2 μB := by
    have hw : Continuous (fun θ => conj (deriv γ θ) * z θ ^ (k - 1)) :=
      (Complex.continuous_conj.comp hγ.continuous_deriv_one).mul (hz1.continuous.pow (k - 1))
    simpa only [b, s, f, mul_assoc, mul_left_comm, mul_comm] using
      common_roughGauge_continuous_mul_memLp hw (roughGauge_partial_memLp hK hγ hW p m α (j + 1) N)
  have ht : MemLp t 2 μB := by
    have hv := roughVekuaRegularCorrection_continuousOn hK hγ hW p m α
    have hc : ContinuousOn t boundaryInterval := by
      have hp : Continuous (physicalDrivenPower γ N) := by
        unfold physicalDrivenPower physicalDrivenCentered
        fun_prop
      have hd : ContinuousOn
          (physicalDrivenScaledRow E (regularCorrectionFixedHere p m α) (N + j + 2))
          boundaryInterval := continuousOn_const.mul
        (physicalDrivenRow_continuousOn _ hv (N + j + 2))
      have he : ((physicalDrivenScaledRow E f (N + j + 2))) =
          physicalDrivenScaledRow E (regularCorrectionFixedHere p m α) (N + j + 2) := by
        funext θ
        solve_by_elim (maxDepth := 2) [roughVekuaGauge_scaledRow_succ_eq]
      dsimp only [t]
      have hcont := ((hγ.continuous_deriv_one.mul hp).continuousOn.mul hd).mul
        (hz1.continuous.pow k).continuousOn
      convert hcont using 1
      ext <;> simp_all
    exact driven_realization_continuousOn_memLp hc
  have hr : MemLp r 2 μB := by
    simpa only [r, smul_eq_mul, Pi.add_def, Pi.smul_def] using
      ((ha.const_smul (physicalDrivenQ E ^ 2)).add (hb.const_smul (k : ℂ))).add ht
  have hd : ∀ᵐ θ, θ ∈ Ioo 0 circlePeriod →
      HasDerivAt (fun θ => s θ * z θ ^ k) (r θ) θ := by
    filter_upwards [roughVekuaGauge_partial_succ_ae_hasDerivAt hK hγ hW p m α j N]
      with θ hθ hmem
    have hdz : HasDerivAt z (conj (deriv γ θ)) θ := by
      simpa only [z, physicalDrivenCentered, Complex.star_def] using
        ((hγ.differentiable_one θ).hasDerivAt.sub_const (γ 0)).star
    convert (hθ hmem).mul (hdz.pow k) using 1
    · dsimp only [r, a, b, t, s, f]
      simp only [Pi.pow_apply]
      ring
  have hri : IntegrableOn r boundaryInterval := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact hr.integrable (by norm_num)
  have he := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    hsz' hri hd circlePeriod ⟨Real.two_pi_pos.le, le_rfl⟩
  have hs0 : s 0 = 0 := roughGauge_partial_succ_zero hW p m α j N
  have hsT : s circlePeriod = 0 := roughGauge_partial_succ_endpoint p m α hα j N
  simp only [hs0, hsT, zero_mul, zero_add] at he
  have hia := intervalIntegrable_boundary_of_memLp a ha
  have hib := intervalIntegrable_boundary_of_memLp b hb
  have hit := intervalIntegrable_boundary_of_memLp t ht
  dsimp only [r] at he
  rw [intervalIntegral.integral_add ((hia.const_mul _).add (hib.const_mul _)) hit,
    intervalIntegral.integral_add (hia.const_mul _) (hib.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at he
  change 0 = physicalDrivenQ E ^ 2 * momentPartialFixed f j N k +
    k * momentPartialFixed f (j + 1) N (k - 1) +
      physicalDrivenTailMoment γ E f j N k at he
  exact eq_neg_of_add_eq_zero_left he.symm

theorem roughVekuaGauge_momentPartial_tendsto j k :
    Tendsto (fun N : ℕ => momentPartialFixed
      drivenVectorFixed j N k) atTop
      (𝓝 (physicalDrivenMoment γ E drivenVectorFixed j k)) := by
  let v := regularCorrectionFixedHere p m α
  have hv := roughVekuaRegularCorrection_continuousOn hK hγ hW p m α
  cases j with
  | succ j =>
    have he (N : ℕ) : momentPartialFixed
        drivenVectorFixed (j + 1) N k =
        momentPartialFixed v (j + 1) N k := by
      apply intervalIntegral.integral_congr
      intro θ _
      grind only [roughVekuaGauge_partial_succ_eq, PolyaNeumann.physicalDrivenCentered]
    have he' : physicalDrivenMoment γ E drivenVectorFixed (j + 1) k =
        physicalDrivenMoment γ E v (j + 1) k := by
      apply intervalIntegral.integral_congr
      intro θ _
      grind only [roughVekuaGauge_succ_eq, PolyaNeumann.physicalDrivenCentered]
    simpa only [he, he'] using physicalDrivenMomentPartial_tendsto γ hγ E v hv (j + 1) k
  | zero =>
    let w  := fun θ => conj (deriv γ θ) * conj (physicalDrivenCentered γ θ) ^ k
    let c  := ∫ θ in (0)..circlePeriod, w θ * (-Complex.I * p θ)
    have hw : Continuous w := (Complex.continuous_conj.comp hγ.continuous_deriv_one).mul
      ((Complex.continuous_conj.comp (hγ.continuous.sub continuous_const)).pow k)
    have hbase : MemLp (fun θ : ℝ => w θ * (-Complex.I * p θ)) 2 μB := by
      simpa only [Pi.smul_def, smul_eq_mul, mul_left_comm] using
        (common_roughGauge_continuous_mul_memLp hw (Lp.memLp p)).const_smul (-Complex.I)
    have hi := intervalIntegrable_boundary_of_memLp _ hbase
    have he (N : ℕ) : momentPartialFixed
        drivenVectorFixed 0 N k = c + momentPartialFixed v 0 N k := by
      have ht := intervalIntegrable_boundary_of_memLp _ (common_roughGauge_continuous_mul_memLp hw
        (driven_realization_continuousOn_memLp (physicalDrivenGaugePartial_continuousOn γ hγ.continuous E v hv 0 N)))
      calc
        _ = ∫ θ in (0)..circlePeriod, w θ * (-Complex.I * p θ) +
            w θ * gaugePartialFixed v 0 N θ := by
          apply intervalIntegral.integral_congr
          intro θ _
          grind only [roughVekuaGauge_partial_zero_split, PolyaNeumann.physicalDrivenCentered]
        _ = c + momentPartialFixed v 0 N k := by
          rw [intervalIntegral.integral_add hi ht]
          congr 1
          apply intervalIntegral.integral_congr
          grind [Set.EqOn]
    have he' : physicalDrivenMoment γ E drivenVectorFixed 0 k =
        c + physicalDrivenMoment γ E v 0 k := by
      have ht := intervalIntegrable_boundary_of_memLp _ (common_roughGauge_continuous_mul_memLp hw
        (roughVekuaGauge_regular_memLp hK hγ hW p m α 0))
      calc
        _ = ∫ θ in (0)..circlePeriod, w θ * (-Complex.I * p θ) +
            w θ * gaugeFixed v 0 θ := by
          apply intervalIntegral.integral_congr
          intro θ _
          grind only [roughVekuaGauge_zero_split, PolyaNeumann.physicalDrivenCentered]
        _ = c + physicalDrivenMoment γ E v 0 k := by
          rw [intervalIntegral.integral_add hi ht]
          congr 1
          apply intervalIntegral.integral_congr
          grind [Set.EqOn]
    simpa only [he, he'] using
      (physicalDrivenMomentPartial_tendsto γ hγ E v hv 0 k).const_add c

theorem roughVekuaGauge_tailMoment_tendsto_zero j k :
    Tendsto (fun N : ℕ => physicalDrivenTailMoment γ E
      drivenVectorFixed j N k) atTop (𝓝 0) := by
  have he (N : ℕ) : physicalDrivenTailMoment γ E drivenVectorFixed j N k =
      physicalDrivenTailMoment γ E (regularCorrectionFixedHere p m α) j N k := by
    apply intervalIntegral.integral_congr
    intro θ _
    grind only [physicalDrivenPower, physicalDrivenScaledRow, roughVekuaDrivenVector, physicalDrivenCentered, roughVekuaGauge_scaledRow_succ_eq, PolyaNeumann.physicalDrivenPower, PolyaNeumann.physicalDrivenCentered]
  simpa  [he] using physicalDrivenTailMoment_tendsto_zero γ hγ E _
    (roughVekuaRegularCorrection_continuousOn hK hγ hW p m α) j k

theorem roughVekuaGauge_moment_recurrence
    (hα : regularCorrectionFixedHere p m α circlePeriod = α • basisVec 0)
    (j k : ℕ) :
    physicalDrivenQ E ^ 2 * physicalDrivenMoment γ E drivenVectorFixed j k +
      (k : ℂ) * physicalDrivenMoment γ E drivenVectorFixed (j + 1) (k - 1) = 0 := by
  have hl := ((roughVekuaGauge_momentPartial_tendsto hK hγ hW p m α j k).const_mul (physicalDrivenQ E ^ 2)).add
      ((roughVekuaGauge_momentPartial_tendsto hK hγ hW p m α (j + 1) (k - 1)).const_mul (k : ℂ))
  have hr : Tendsto (fun N => physicalDrivenQ E ^ 2 * momentPartialFixed
      drivenVectorFixed j N k + (k : ℂ) * momentPartialFixed
        drivenVectorFixed (j + 1) N (k - 1)) atTop (𝓝 0) := by
    simpa  [roughVekuaGauge_momentPartial_recurrence hK hγ hW p m α hα] using
      (roughVekuaGauge_tailMoment_tendsto_zero hK hγ hW p m α j k).neg
  exact tendsto_nhds_unique hl hr

end


end


section
include hK hγ hW

/-- Every original physical moment vanishes, including all moments of
the rough zeroth gauge. No trace point value of its primitive is used. -/
theorem roughVekuaGauge_physicalMoment_eq_zero (hE : 0 < E) (p : BoundaryL2) (m α : ℂ)
    (hα : regularCorrectionFixedHere p m α circlePeriod = α • basisVec 0)
    (j k : ℕ) :
    physicalDrivenMoment γ E (roughVekuaDrivenVector γ E W p m α) j k = 0 := by
  induction k generalizing j with
  | zero =>
    have h := roughVekuaGauge_moment_recurrence hK hγ hW p m α hα j 0
    simp only [Nat.cast_zero, zero_mul, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (physicalDrivenQ_sq_ne_zero hE)
  | succ k ih =>
    have h := roughVekuaGauge_moment_recurrence hK hγ hW p m α hα j (k + 1)
    rw [Nat.add_sub_cancel, ih (j + 1), mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (physicalDrivenQ_sq_ne_zero hE)

private theorem roughGauge_regular_zero_ae_hasDerivAt p m α :
    ∀ᵐ θ, θ ∈ Ioo 0 circlePeriod →
      HasDerivAt (physicalDrivenScaledRow E (regularCorrectionFixedHere p m α) 0)
        (2 * deriv γ θ * physicalDrivenScaledRow E
          (regularCorrectionFixedHere p m α) 1 θ - Complex.I * m) θ := by
  filter_upwards [roughVekuaRegularCorrection_ae_hasDerivAt hK hγ hW p m α]
    with θ hθ hmem
  have hd := (((innerSL ℂ (basisVec 0)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt θ (hθ hmem)).const_mul (Real.sqrt 2 : ℂ)
  change HasDerivAt
    (fun t : ℝ => (Real.sqrt 2) * inner ℂ (basisVec 0)
      (regularCorrectionFixedHere p m α t))
    ((Real.sqrt 2) * inner ℂ (basisVec 0)
      (transportCoeff γ E θ (regularCorrectionFixedHere p m α θ) +
        (-(Complex.I / (Real.sqrt 2))) • roughVekuaRegularForce γ E p m θ)) θ at hd
  rw [roughVekuaRegularCorrection_derivative_eq_transportCoeff] at hd
  simp only [inner_basisVec] at hd
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num)
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp_all
  have hcoup (a b c : ℂ) :
      (Real.sqrt 2 : ℂ) * (a * (b * ((Real.sqrt 2 : ℂ) * c))) =
        2 * b * (a * c) := by
    calc
      _ = (Real.sqrt 2) ^ 2 * (b * (a * c)) := by ring
      _ = _ := by rw [hs]; ring
  have hforce : (Real.sqrt 2 : ℂ) * (-(Complex.I / (Real.sqrt 2 : ℂ)) * m) =
      -Complex.I * m := by
    field_simp
  have he : physicalDrivenScaledRow E (regularCorrectionFixedHere p m α) 0 =
      fun t : ℝ => (Real.sqrt 2 : ℂ) *
        (regularCorrectionFixedHere p m α t : ComplexSeq) 0 := by
    ext <;> simp_all [physicalDrivenScaledRow, physicalDrivenRow]
  rw [he]
  apply hd.congr_deriv
  simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, basisVec_coord, if_true, mul_one]
  rw [transportCoeff_apply_coord, shiftN_apply_zero,
    roughVekuaDrivenVector_positive_coord]
  simp only [physicalDrivenScaledRow, physicalDrivenRow, pow_one, physicalDrivenQ,
    Nat.one_ne_zero, if_false, shiftWeight, if_true, mul_zero, add_zero]
  rw [mul_add, hcoup, hforce]
  ring

private theorem roughGauge_regular_positive_ae_hasDerivAt
    p m α n :
    ∀ᵐ θ, θ ∈ Ioo 0 circlePeriod →
      HasDerivAt
        (physicalDrivenScaledRow E (regularCorrectionFixedHere p m α) (n + 1))
        (deriv γ θ * physicalDrivenScaledRow E (regularCorrectionFixedHere p m α) (n + 2) θ +
          physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
            ((if n = 0 then -Complex.I * p θ else 0) +
              physicalDrivenScaledRow E (regularCorrectionFixedHere p m α) n θ)) θ := by
  filter_upwards [roughVekuaDrivenScaledRow_succ_ae_hasDerivAt hK hγ hW p m α n]
    with θ hθ hmem
  have he : physicalDrivenScaledRow E (roughVekuaDrivenVector γ E W p m α) (n + 1) =
      physicalDrivenScaledRow E (regularCorrectionFixedHere p m α) (n + 1) :=
    funext (roughVekuaGauge_scaledRow_succ_eq p m α n)
  rw [he] at hθ
  convert hθ hmem using 1
  cases n with
  | zero => simp_all [roughVekuaGauge_scaledRow_succ_eq, roughVekuaGauge_scaledRow_zero_split]
  | succ n => simp_all [roughVekuaGauge_scaledRow_succ_eq]

end


/-- The actual L2 derivative of the continuous correction gauge. The
rough primitive occurs only multiplied by a true continuous coefficient. -/
def roughVekuaGaugeRegularDerivative γ E
    W p m α θ  :=
  physicalDrivenGaugeZeroContinuousPart γ E (roughVekuaRegularCorrection γ E W p m α) θ -
    Complex.I * m - Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
      physicalDrivenPower γ 1 θ * p θ

section
variable (p : BoundaryL2) (m α : ℂ)
local notation "regularCorrectionFixed" => regularCorrectionFixedHere p m α

local notation "shiftedGaugeTermFixed" => physicalDrivenShiftedGaugeTerm γ E

include p m α

section
include hK hγ hW

theorem roughVekuaGauge_regular_derivative_memLp :
    MemLp (roughVekuaGaugeRegularDerivative γ E W p m α) 2 μB := by
  have hc := physicalDrivenGaugeZeroContinuousPart_continuousOn hγ E _
    (roughVekuaRegularCorrection_continuousOn hK hγ hW p m α)
  have ha : Continuous (fun θ => Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
      physicalDrivenPower γ 1 θ) := by
    have hp : Continuous (physicalDrivenPower γ 1) := by
      unfold physicalDrivenPower physicalDrivenCentered
      fun_prop
    fun_prop
  exact ((driven_realization_continuousOn_memLp hc).sub (memLp_const (Complex.I * m))).sub
    (common_roughGauge_continuous_mul_memLp ha (Lp.memLp p))

private theorem roughGauge_regular_partial_zero_ae_hasDerivAt N :
    ∀ᵐ θ, θ ∈ Ioo 0 circlePeriod →
      HasDerivAt
        (gaugePartialFixedHere regularCorrectionFixed 0 (N + 1))
        (deriv γ θ * physicalDrivenScaledRow E regularCorrectionFixed 1 θ -
          Complex.I * m + deriv γ θ * gaugeTermFixed
            regularCorrectionFixed 1 (N + 1) θ +
          physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
            ∑ l ∈ Finset.range (N + 1), shiftedGaugeTermFixed
              regularCorrectionFixed l θ -
          Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ θ) * physicalDrivenPower γ 1 θ * p θ) θ := by
  induction N with
  | zero =>
    filter_upwards [roughGauge_regular_zero_ae_hasDerivAt hK hγ hW p m α,
      roughGauge_regular_positive_ae_hasDerivAt hK hγ hW p m α 0] with θ h0 h1 hmem
    have hd := (h0 hmem).add ((physicalDrivenPower_hasDerivAt_succ hγ 0 θ).mul (h1 hmem))
    convert hd using 1
    · funext s
      norm_num [physicalDrivenGaugePartial, Finset.sum_range_succ, physicalDrivenGaugeTerm, physicalDrivenPower]
    · simp [physicalDrivenGaugeTerm, physicalDrivenShiftedGaugeTerm, physicalDrivenPower] ; ring
  | succ N ih =>
    filter_upwards [ih, roughGauge_regular_positive_ae_hasDerivAt hK hγ hW p m α (N + 1)]
      with θ hθ hd hmem
    have he : gaugePartialFixedHere regularCorrectionFixed
        0 (N + 2) = ((gaugePartialFixedHere regularCorrectionFixed 0 (N + 1) + gaugeTermFixed regularCorrectionFixed 0 (N + 2))) := by
      funext t
      exact Finset.sum_range_succ _ _
    rw [show N + 1 + 1 = N + 2 by omega, he]
    have hsum :
        (∑ l ∈ Finset.range (N + 2), shiftedGaugeTermFixed
          regularCorrectionFixed l θ) =
        (∑ l ∈ Finset.range (N + 1), shiftedGaugeTermFixed
          regularCorrectionFixed l θ) +
          shiftedGaugeTermFixed
            regularCorrectionFixed (N + 1) θ := by
      rw [show N + 2 = (N + 1) + 1 by omega, Finset.sum_range_succ]
    have hweighted := congrArg
      (fun q : ℂ => physicalDrivenQ E ^ 2 * conj (deriv γ θ) * q) hsum
    have hweighted' :
        physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
            (∑ l ∈ Finset.range (N + 2), shiftedGaugeTermFixed
              regularCorrectionFixed l θ) =
          physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
            ((∑ l ∈ Finset.range (N + 1), shiftedGaugeTermFixed
              regularCorrectionFixed l θ) +
              shiftedGaugeTermFixed
                regularCorrectionFixed (N + 1) θ) := by
      simpa only using hweighted
    convert (hθ hmem).add ((physicalDrivenPower_hasDerivAt_succ hγ (N + 1) θ).mul (hd hmem)) using 1
    · rfl
    grind only [physicalDrivenGaugeTerm, physicalDrivenShiftedGaugeTerm, physicalDrivenPower, physicalDrivenCentered, physicalDrivenScaledRow, physicalDrivenRow, PolyaNeumann.physicalDrivenQ, PolyaNeumann.physicalDrivenPower]

end


private theorem roughGauge_regular_partial_at_initial_vector (N : ℕ) {θ : ℝ}
    (hv : regularCorrectionFixed θ = α • basisVec 0) :
    gaugePartialFixedHere regularCorrectionFixed 0 N θ =
      (Real.sqrt 2 : ℂ) * α := by
  induction N with
  | zero => simp [physicalDrivenGaugePartial, physicalDrivenGaugeTerm, physicalDrivenPower,
      physicalDrivenScaledRow, physicalDrivenRow, hv, basisVec_coord]
  | succ N ih =>
    rw [physicalDrivenGaugePartial, Finset.sum_range_succ]
    change gaugePartialFixedHere regularCorrectionFixed 0 N θ + _ = _
    rw [ih]
    simp [physicalDrivenGaugeTerm, physicalDrivenScaledRow, physicalDrivenRow,
      hv, basisVec_coord]

section
include hK hγ hW

private theorem roughGauge_regular_partial_zero_primitive N  (hθ : θ ∈ boundaryInterval) :
    gaugePartialFixedHere regularCorrectionFixed 0 (N + 1) θ =
      (Real.sqrt 2 : ℂ) * α +
      (∫ s in (0 : ℝ)..θ,
        deriv γ s * physicalDrivenScaledRow E regularCorrectionFixed 1 s -
          Complex.I * m - Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ s) *
            physicalDrivenPower γ 1 s * p s) +
      (∫ s in (0 : ℝ)..θ, deriv γ s * gaugeTermFixed
        regularCorrectionFixed 1 (N + 1) s) +
      physicalDrivenQ E ^ 2 * (∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
        ∑ l ∈ Finset.range (N + 1), shiftedGaugeTermFixed
          regularCorrectionFixed l s) := by
  let v := regularCorrectionFixed
  let a  := fun s => deriv γ s * physicalDrivenScaledRow E v 1 s - Complex.I * m -
    Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ s) * physicalDrivenPower γ 1 s * p s
  let t  := fun s => deriv γ s * gaugeTermFixed v 1 (N + 1) s
  let b  := fun s => conj (deriv γ s) *
    ∑ l ∈ Finset.range (N + 1), shiftedGaugeTermFixed v l s
  have hv := roughVekuaRegularCorrection_continuousOn hK hγ hW p m α
  have ha : MemLp a 2 μB := by
    have hc : ContinuousOn (((deriv γ * physicalDrivenScaledRow E v 1)))
        boundaryInterval := hγ.continuous_deriv_one.continuousOn.mul
      (continuousOn_const.mul (physicalDrivenRow_continuousOn v hv 1))
    have hp : Continuous (fun s => Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ s) *
        physicalDrivenPower γ 1 s) := by
      have hp' : Continuous (physicalDrivenPower γ 1) := by
        unfold physicalDrivenPower physicalDrivenCentered
        fun_prop
      fun_prop
    exact ((driven_realization_continuousOn_memLp hc).sub (memLp_const (Complex.I * m))).sub
      (common_roughGauge_continuous_mul_memLp hp (Lp.memLp p))
  have ht : ContinuousOn t boundaryInterval :=
    hγ.continuous_deriv_one.continuousOn.mul
      (physicalDrivenGaugeTerm_continuousOn γ hγ.continuous E v hv 1 (N + 1))
  have hb : ContinuousOn b boundaryInterval :=
    (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn.mul
      (continuousOn_finset_sum _ fun l _ =>
        physicalDrivenShiftedGaugeTerm_continuousOn γ hγ.continuous E v hv l)
  have hr : MemLp (fun s => a s + t s + physicalDrivenQ E ^ 2 * b s) 2 μB := by
    simpa only [smul_eq_mul, Pi.add_def, Pi.smul_def] using (ha.add (driven_realization_continuousOn_memLp ht)).add
      ((driven_realization_continuousOn_memLp hb).const_smul (physicalDrivenQ E ^ 2))
  have hd : ∀ᵐ s, s ∈ Ioo 0 circlePeriod →
      HasDerivAt (gaugePartialFixedHere v 0 (N + 1))
        (a s + t s + physicalDrivenQ E ^ 2 * b s) s := by
    filter_upwards [roughGauge_regular_partial_zero_ae_hasDerivAt hK hγ hW p m α N]
      with s hs hmem
    convert hs hmem using 1
    · dsimp only [a, t, b, v]
      ring
  have hri : IntegrableOn (fun s => a s + t s + physicalDrivenQ E ^ 2 * b s)
      boundaryInterval := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact hr.integrable (by norm_num)
  have he := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    (roughGauge_regular_partial_ac hK hγ hW p m α 0 (N + 1)) hri hd θ hθ
  rw [roughGauge_regular_partial_at_initial_vector p m α (N + 1)
    (roughVekuaRegularCorrection_zero hW p m α)] at he
  have hsub : uIcc 0 θ ⊆ boundaryInterval := by
    rw [uIcc_of_le hθ.1]
    exact Icc_subset_Icc le_rfl hθ.2
  have hai : IntervalIntegrable a volume 0 θ := by
    have hI : IntegrableOn a boundaryInterval := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact ha.integrable (by norm_num)
    exact (hI.mono_set hsub).intervalIntegrable
  have hti : IntervalIntegrable t volume 0 θ := (ht.mono hsub).intervalIntegrable
  have hbi : IntervalIntegrable b volume 0 θ := (hb.mono hsub).intervalIntegrable
  rw [intervalIntegral.integral_add (hai.add hti) (hbi.const_mul _),
    intervalIntegral.integral_add hai hti, intervalIntegral.integral_const_mul] at he
  simpa only [a, t, b, v, add_assoc] using he

/-- The correction gauge is an actual primitive of the computed L2
derivative. The factorial tail and the shifted series are integrated
before taking their genuine limits. -/
theorem roughVekuaGauge_regular_primitive
     (hθ : θ ∈ boundaryInterval) :
    gaugeFixed regularCorrectionFixed 0 θ =
      (Real.sqrt 2 : ℂ) * α +
        ∫ s in (0 : ℝ)..θ, roughVekuaGaugeRegularDerivative γ E W p m α s := by
  classical
  let v := regularCorrectionFixed
  let a  := fun s => deriv γ s * physicalDrivenScaledRow E v 1 s - Complex.I * m -
    Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ s) * physicalDrivenPower γ 1 s * p s
  let b  := fun s => conj (deriv γ s) * physicalDrivenShiftedGauge γ E v s
  have hv := roughVekuaRegularCorrection_continuousOn hK hγ hW p m α
  have hp : Tendsto (fun N : ℕ => gaugePartialFixedHere v 0 (N + 1) θ) atTop
      (𝓝 (gaugeFixed v 0 θ)) := by
    simpa [physicalDrivenGaugePartial, physicalDrivenGauge, Function.comp_def] using
      ((summable_norm_physicalDrivenGaugeTerm γ E v 0 θ).of_norm.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 2)
  have ht := ((physicalDrivenGauge_weightedIntegral_hasSum_to γ hγ.continuous E v hv 1
    (deriv γ) hγ.continuous_deriv_one.continuousOn hθ).summable.tendsto_atTop_zero).comp (tendsto_add_atTop_nat 1)
  have hs := physicalDrivenShiftedGauge_weightedIntegral_hasSum_to γ hγ.continuous E v hv
    (fun s => conj (deriv γ s))
    (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn hθ
  have hsub : uIcc 0 θ ⊆ boundaryInterval := by
    rw [uIcc_of_le hθ.1]
    exact Icc_subset_Icc le_rfl hθ.2
  have he (N : ℕ) : (∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
      ∑ l ∈ Finset.range (N + 1), shiftedGaugeTermFixed v l s) =
      ∑ l ∈ Finset.range (N + 1), ∫ s in (0 : ℝ)..θ,
        conj (deriv γ s) * shiftedGaugeTermFixed v l s := by
    simp_rw [Finset.mul_sum]
    apply intervalIntegral.integral_finset_sum
    intro l _
    exact (((Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn.mul
      (physicalDrivenShiftedGaugeTerm_continuousOn γ hγ.continuous E v hv l)).mono hsub).intervalIntegrable
  have hb : Tendsto (fun N : ℕ => ∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
      ∑ l ∈ Finset.range (N + 1), shiftedGaugeTermFixed v l s) atTop
      (𝓝 (∫ s in (0 : ℝ)..θ, b s)) := by
    have h := hs.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    exact h.congr' (Eventually.of_forall fun N => (he N).symm)
  have hr : Tendsto (fun N : ℕ => (Real.sqrt 2 : ℂ) * α +
      (∫ s in (0 : ℝ)..θ, a s) +
      (∫ s in (0 : ℝ)..θ, deriv γ s * gaugeTermFixed v 1 (N + 1) s) +
      physicalDrivenQ E ^ 2 * (∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
        ∑ l ∈ Finset.range (N + 1), shiftedGaugeTermFixed v l s)) atTop
      (𝓝 ((Real.sqrt 2 : ℂ) * α + (∫ s in (0 : ℝ)..θ, a s) +
        physicalDrivenQ E ^ 2 * (∫ s in (0 : ℝ)..θ, b s))) := by
    simpa only [add_zero, Function.comp_apply] using
      ((tendsto_const_nhds (x := (Real.sqrt 2) * α + ∫ s in (0)..θ, a s)).add ht).add
        (hb.const_mul (physicalDrivenQ E ^ 2))
  have hlim :=
    tendsto_nhds_unique hp (hr.congr' (Eventually.of_forall fun N =>
      (roughGauge_regular_partial_zero_primitive hK hγ hW p m α N hθ).symm))
  have ha : MemLp a 2 μB := by
    have hc : ContinuousOn (((deriv γ * physicalDrivenScaledRow E v 1)))
        boundaryInterval := hγ.continuous_deriv_one.continuousOn.mul
      (continuousOn_const.mul (physicalDrivenRow_continuousOn v hv 1))
    have hco : Continuous (fun s => Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ s) *
        physicalDrivenPower γ 1 s) := by
      have hp' : Continuous (physicalDrivenPower γ 1) := by
        unfold physicalDrivenPower physicalDrivenCentered
        fun_prop
      fun_prop
    exact ((driven_realization_continuousOn_memLp hc).sub (memLp_const (Complex.I * m))).sub
      (common_roughGauge_continuous_mul_memLp hco (Lp.memLp p))
  have hai : IntervalIntegrable a volume 0 θ := by
    have hI : IntegrableOn a boundaryInterval := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact ha.integrable (by norm_num)
    exact (hI.mono_set hsub).intervalIntegrable
  have hbi : IntervalIntegrable b volume 0 θ :=
    (((Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn.mul
      (physicalDrivenShiftedGauge_continuousOn γ hγ.continuous E v hv)).mono hsub).intervalIntegrable
  rw [hlim, ← intervalIntegral.integral_const_mul, add_assoc,
    ← intervalIntegral.integral_add hai (hbi.const_mul _)]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only [a, b, roughVekuaGaugeRegularDerivative, physicalDrivenGaugeZeroContinuousPart, v]
  ring

theorem roughVekuaGauge_regular_absolutelyContinuous :
    AbsolutelyContinuousOnInterval
      (gaugeFixed regularCorrectionFixed 0)
      0 circlePeriod := by
  have hi := intervalIntegrable_boundary_of_memLp _
    (roughVekuaGauge_regular_derivative_memLp hK hγ hW p m α)
  have hconst : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => (Real.sqrt 2 : ℂ) * α) 0 circlePeriod := by
    simpa  [AbsolutelyContinuousOnInterval] using
      tendsto_const_nhds
  have hp := hconst.add (absolutelyContinuousOnInterval_intervalIntegral_banach hi
    (by rw [uIcc_of_le Real.two_pi_pos.le]; exact ⟨le_rfl, Real.two_pi_pos.le⟩))
  apply common_driven_ac_congr hp
  intro θ hθ
  exact (roughVekuaGauge_regular_primitive hK hγ hW p m α hθ).symm

theorem roughVekuaGauge_regular_ae_hasDerivAt :
    ∀ᵐ θ, θ ∈ Ioo 0 circlePeriod →
      HasDerivAt (gaugeFixed regularCorrectionFixed 0)
        (roughVekuaGaugeRegularDerivative γ E W p m α θ) θ := by
  have hi := intervalIntegrable_boundary_of_memLp _
    (roughVekuaGauge_regular_derivative_memLp hK hγ hW p m α)
  filter_upwards [ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le hi]
    with θ hθ hmem
  refine ((hθ hmem).const_add ((Real.sqrt 2) * α)).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with t ht
  exact roughVekuaGauge_regular_primitive hK hγ hW p m α (Ioo_subset_Icc_self ht)

end


private theorem roughGauge_regular_at_initial_vector
    {θ : ℝ} (hv : regularCorrectionFixed θ = α • basisVec 0) :
    gaugeFixed regularCorrectionFixed 0 θ =
      (Real.sqrt 2 : ℂ) * α := by
  have hs := (summable_norm_physicalDrivenGaugeTerm γ E
    regularCorrectionFixed 0 θ).of_norm
  rw [physicalDrivenGauge, hs.tsum_eq_zero_add]
  have ht : (fun l : ℕ => gaugeTermFixed
      regularCorrectionFixed 0 (l + 1) θ) = fun _ => (0 : ℂ) := by
    funext l
    simp [physicalDrivenGaugeTerm, physicalDrivenScaledRow, physicalDrivenRow,
      hv, basisVec_coord]
  rw [ht, tsum_zero, add_zero]
  simp [physicalDrivenGaugeTerm, physicalDrivenPower, physicalDrivenScaledRow,
    physicalDrivenRow, hv, basisVec_coord]

include hK hγ hW in
/-- The regular factorial gauge has true H1 Fourier coefficients. Both
endpoints are sqrt(2) α by the computed vector endpoints; no endpoint or
derivative of the rough primitive is assumed. -/
theorem roughVekuaGauge_regular_isSobolevSeq_one
    (hα : regularCorrectionFixed circlePeriod = α • basisVec 0) :
    IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos
      (gaugeFixed regularCorrectionFixed 0)) := isSobolevSeq_one_fourierCoeffOn_of_ac_ae_hasDerivAt
    (roughVekuaGauge_regular_absolutelyContinuous hK hγ hW p m α)
    (roughVekuaGauge_regular_derivative_memLp hK hγ hW p m α)
    (roughVekuaGauge_regular_ae_hasDerivAt hK hγ hW p m α)
    ((roughGauge_regular_at_initial_vector p m α (roughVekuaRegularCorrection_zero hW p m α)).trans (roughGauge_regular_at_initial_vector p m α hα).symm)

end


end GenuineGauge

end PolyaNeumann

end
