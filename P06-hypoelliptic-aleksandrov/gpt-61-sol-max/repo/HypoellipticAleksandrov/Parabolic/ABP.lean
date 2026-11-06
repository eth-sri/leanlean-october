module

public import HypoellipticAleksandrov.Parabolic.AreaFormula
public import HypoellipticAleksandrov.Parabolic.ContactCoverage
public import PDEFoundation.Measure.LpPower
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity



/-!
# Smooth determinant-weighted parabolic ABP estimate

This module combines first-contact coverage, the one-sided area formula, and
the pointwise Jacobian bound into the exact power-form smooth parabolic
Aleksandrov--Bakelman--Pucci estimate on a unit velocity ball.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal MatrixOrder

variable {d : ℕ}

variable (A : CoefficientField d) (f : HypoellipticAleksandrov.Parabolic.ScalarField d)

private def weightedDensity   (z : TimeVelocity d) : ℝ :=
  (max (f z) 0) ^ (d + 1) / (coefficientAt A z).det

private theorem continuousOn_weightedDensity   (hAcont : IsContinuousCoefficient A)
    (hfcont : Continuous f) {T : ℝ} {y₀ : PDE.Vec d}
    (hA : ∀ z ∈ closedParabolicCylinder T y₀, (coefficientAt A z).PosDef) :
    ContinuousOn (weightedDensity A f) (closedParabolicCylinder T y₀) := by
  unfold weightedDensity
  refine ((hfcont.max continuous_const).pow _).continuousOn.div
    hAcont.matrix_det.continuousOn ?_
  intro z hz
  exact (hA z hz).det_pos.ne'

private theorem weightedDensity_nonneg   {T : ℝ} {y₀ : PDE.Vec d}
    (hA : ∀ z ∈ closedParabolicCylinder T y₀, (coefficientAt A z).PosDef)
    {z : TimeVelocity d} (hz : z ∈ closedParabolicCylinder T y₀) :
    0 ≤ weightedDensity A f z := by
  unfold weightedDensity
  exact div_nonneg (pow_nonneg (le_max_right _ _) _) (hA z hz).det_pos.le

section
variable (hAcont : IsContinuousCoefficient A) (hfcont : Continuous f) {T : ℝ} {y₀ : PDE.Vec d} (hA : ∀ z ∈ closedParabolicCylinder T y₀, (coefficientAt A z).PosDef)

include hAcont hfcont hA
private theorem integrableOn_weightedDensity    :
    IntegrableOn (weightedDensity A f) (closedParabolicCylinder T y₀)  :=
  (continuousOn_weightedDensity A f hAcont hfcont hA).integrableOn_compact
    (isCompact_closedParabolicCylinder T y₀)

private theorem integrableOn_weightedDensity_interior    :
    IntegrableOn (weightedDensity A f) (parabolicInterior T y₀)  :=
  (integrableOn_weightedDensity A f hAcont hfcont hA).mono_set
    (parabolicInterior_subset_closedParabolicCylinder T y₀)
end


/-- The exact real power-form smooth parabolic ABP estimate on the unit
velocity ball. -/
theorem parabolic_abp_unit_pow
     (hd : 0 < d)
    {T : ℝ} (hT : 0 < T) (hT_le_one : T ≤ 1)
    (y₀ : PDE.Vec d) (A : CoefficientField d)
    (f u : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hAcont : IsContinuousCoefficient A) (hfcont : Continuous f)
    (hu : ContDiff ℝ 2 u)
    (hA : ∀ z ∈ closedParabolicCylinder T y₀,
      (coefficientAt A z).PosDef)
    (hsub : IsParabolicSubsolutionOn A f u (parabolicInterior T y₀))
    (hboundary : ∀ z ∈ forwardParabolicBoundary T y₀, u z ≤ 0)
    {zStar : TimeVelocity d}
    (hzStar : zStar ∈ closedParabolicCylinder T y₀) :
    (volume (PDE.euclideanBall (0 : PDE.Vec d) 1)).toReal *
        (max (u zStar) 0) ^ (d + 1) ≤
      (4 / ((d : ℝ) + 1)) ^ (d + 1) *
        ∫ z in parabolicInterior T y₀,
          (max (f z) 0) ^ (d + 1) /
            (coefficientAt A z).det := by
  let sharedTerm_0573ee8980 := ((volume (PDE.euclideanBall (0 : PDE.Vec d) 1)).toReal)
  let sharedTerm_b027d2651d := (∫⁻ z in parabolicSignSet T y₀ u, ENNReal.ofReal |((fderiv ℝ (parabolicNormalMap u y₀) z).det)| ∂volume)
  let M : ℝ := max (u zStar) 0
  let density  := weightedDensity A f
  have hT_unit : T ∈ Set.Ioc (0 : ℝ) 1 := ⟨hT, hT_le_one⟩
  have hd_one : (1 : ℝ) ≤ d := by
    exact_mod_cast (Nat.succ_le_iff.mpr hd)
  have hExponent_pos : 0 < (d : ℝ) + 1 := by linarith

  have hDensity_integrable  := integrableOn_weightedDensity_interior A f hAcont hfcont hA
  have hDensity_nonneg : ∀ z ∈ parabolicInterior T y₀, 0 ≤ density z := by
    intro z hz
    exact weightedDensity_nonneg A f hA
      (parabolicInterior_subset_closedParabolicCylinder T y₀ hz)

  have hDensity_integral_eq :
      (∫ z in parabolicInterior T y₀, density z) =
        (∫⁻ z in parabolicInterior T y₀, ENNReal.ofReal (density z)).toReal := by
    refine integral_eq_lintegral_of_nonneg_ae ?_
      hDensity_integrable.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (measurableSet_parabolicInterior T y₀)] with z hz
    exact hDensity_nonneg z hz
  by_cases hM_zero : M = 0
  · rw [show max (u zStar) 0 = M by rfl, hM_zero]
    simp
    have hright_nonneg : 0 ≤ ∫ z in parabolicInterior T y₀, density z := by
      rw [hDensity_integral_eq]
      exact ENNReal.toReal_nonneg
    exact mul_nonneg (pow_nonneg (by positivity) _) hright_nonneg

  have hzPositive : 0 < u zStar := by
    by_contra hnot

    have : M = 0 := by dsimp [M]; exact max_eq_right (le_of_not_gt hnot)
    exact hM_zero this
  have hcoverage := slopeInterceptWedge_subset_image_parabolicSignSet hu hT_unit.1 hboundary
    hzStar hzPositive





  let q : ℝ := ((d : ℝ) + 1) ^ (d + 1)
  let qE  := ENNReal.ofReal q
  have hq_pos : 0 < q := pow_pos hExponent_pos _



  have hwedge_enn :
      volume (slopeInterceptWedge d (u zStar)) ≤
        (∫⁻ z in parabolicInterior T y₀, ENNReal.ofReal (density z)) / qE := by
    calc
      volume (slopeInterceptWedge d (u zStar)) ≤
          volume (parabolicNormalMap u y₀ '' parabolicSignSet T y₀ u) := (measure_mono hcoverage)
      _ ≤ sharedTerm_b027d2651d := (volume_parabolicNormalMap_image_le_lintegral_abs_det_fderiv hu T y₀)
      _ ≤ ∫⁻ z in parabolicSignSet T y₀ u,
          ENNReal.ofReal (density z) / qE := (show _ by
              apply setLIntegral_mono_ae
              · apply AEMeasurable.div_const
                apply AEMeasurable.ennreal_ofReal
                apply ContinuousOn.aemeasurable
                  ((continuousOn_weightedDensity A f hAcont hfcont hA).mono
                    (fun z hz => parabolicInterior_subset_closedParabolicCylinder T y₀ hz.1))
                exact measurableSet_parabolicSignSet hu T y₀
              · exact ae_of_all _ (by
                  intro z hz
                  have hsource := abs_det_fderiv_parabolicNormalMap_le_source hu hz
                    (hA z (parabolicInterior_subset_closedParabolicCylinder T y₀ hz.1))
                    (hsub z hz.1)

                  rw [← ENNReal.ofReal_div_of_pos (pow_pos hExponent_pos _)]
                  exact ENNReal.ofReal_le_ofReal (by
                    simpa only [density, weightedDensity, div_div, mul_comm] using hsource)))
      _ ≤ ∫⁻ z in parabolicInterior T y₀,
          ENNReal.ofReal (density z) / qE := (lintegral_mono_set (fun z hz => hz.1))
      _ = _ := (by
          simp_rw [div_eq_mul_inv]
          rw [lintegral_mul_const'' qE⁻¹ (show _ by
              apply AEMeasurable.ennreal_ofReal
              apply ContinuousOn.aemeasurable
                ((continuousOn_weightedDensity A f hAcont hfcont hA).mono
                  (parabolicInterior_subset_closedParabolicCylinder T y₀))
              exact measurableSet_parabolicInterior T y₀)])

  have hwedge_real := ENNReal.toReal_mono (by
      apply ENNReal.div_ne_top (show _ by
          have hfinite := (MeasureTheory.hasFiniteIntegral_iff_norm _).mp
            hDensity_integrable.integrable.hasFiniteIntegral
          apply ne_of_lt
          refine (lintegral_congr_ae ?_).symm ▸ hfinite
          filter_upwards [ae_restrict_mem (measurableSet_parabolicInterior T y₀)] with z hz
          rw [Real.norm_eq_abs, abs_of_nonneg (hDensity_nonneg z hz)])
      exact ne_of_gt (ENNReal.ofReal_pos.mpr hq_pos)) hwedge_enn
  have hM_eq : M = u zStar := by
    dsimp [M]
    exact max_eq_left hzPositive.le

  rw [(volume_slopeInterceptWedge_eq (d := d) hzPositive), ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (pow_nonneg (div_nonneg hzPositive.le (by norm_num)) _),
    ENNReal.toReal_ofReal hq_pos.le] at hwedge_real
  rw [← hDensity_integral_eq] at hwedge_real
  change sharedTerm_0573ee8980 * M ^ (d + 1) ≤ _
  rw [hM_eq]
  change sharedTerm_0573ee8980 * (u zStar) ^ (d + 1) ≤
    (4 / ((d : ℝ) + 1)) ^ (d + 1) *
      ∫ z in parabolicInterior T y₀, density z


  calc
    sharedTerm_0573ee8980 * (u zStar) ^ (d + 1) =
        (4 / ((d : ℝ) + 1)) ^ (d + 1) *
          ((u zStar / 4) ^ (d + 1) *
            sharedTerm_0573ee8980 * q) := by
      dsimp [q]
      rw [div_pow, div_pow]
      field_simp [hExponent_pos.ne']
    _ ≤ (4 / ((d : ℝ) + 1)) ^ (d + 1) *
        ∫ z in parabolicInterior T y₀, density z :=
      mul_le_mul_of_nonneg_left (((le_div_iff₀ hq_pos).mp hwedge_real)) (by positivity)

/-- Raising the quotient-form ABP root bound to a positive natural power. -/
private theorem abp_root_constant_mul_rpow_pow {n : ℕ} (hn : n ≠ 0)
    {a omega B : ℝ} (homega : 0 < omega) (hB : 0 ≤ B) :
    omega *
        ((a / omega ^ ((n : ℝ)⁻¹)) * B ^ ((n : ℝ)⁻¹)) ^ n =
      a ^ n * B := by
  let sharedTerm_8279b25460 := (((n : ℝ)⁻¹))


  calc
    omega * ((a / omega ^ sharedTerm_8279b25460) * B ^ sharedTerm_8279b25460) ^ n =
        omega * ((a / omega ^ sharedTerm_8279b25460) ^ n *
          (B ^ sharedTerm_8279b25460) ^ n) := by
      rw [mul_pow]
    _ = omega * ((a ^ n / (omega ^ sharedTerm_8279b25460) ^ n) *
          (B ^ sharedTerm_8279b25460) ^ n) := by
      rw [div_pow]
    _ = omega * ((a ^ n / omega) * B) := by
      rw [(Real.rpow_inv_natCast_pow homega.le hn), (Real.rpow_inv_natCast_pow hB hn)]
    _ = a ^ n * B := by
      field_simp [homega.ne']

/-- The determinant-weighted smooth parabolic ABP estimate in root form. -/
theorem parabolic_abp_unit (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T : ℝ}, 0 < T → T ≤ 1 →
      ∀ (y₀ : PDE.Vec d) (A : CoefficientField d)
        (f u : HypoellipticAleksandrov.Parabolic.ScalarField d),
        IsContinuousCoefficient A → Continuous f → ContDiff ℝ 2 u →
        (∀ z ∈ closedParabolicCylinder T y₀,
          (coefficientAt A z).PosDef) →
        IsParabolicSubsolutionOn A f u (parabolicInterior T y₀) →
        (∀ z ∈ forwardParabolicBoundary T y₀, u z ≤ 0) →
        ∀ zStar ∈ closedParabolicCylinder T y₀,
          u zStar ≤ C *
            (∫ z in parabolicInterior T y₀,
              (max (f z) 0) ^ (d + 1) /
                (coefficientAt A z).det) ^
              (1 / ((d : ℝ) + 1) : ℝ) := by
  let sharedTerm_d983397396 := (4 / ((d : ℝ) + 1))
  let omega : ℝ :=
    (volume (PDE.euclideanBall (0 : PDE.Vec d) 1)).toReal
  have homega : 0 < omega := by
    dsimp [omega]
    exact PDE.volume_euclideanBall_toReal_pos (0 : PDE.Vec d) (by norm_num)

  have hrecip :
      1 / ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ)⁻¹ := by
    norm_num [Nat.cast_add, one_div]
  refine ⟨(sharedTerm_d983397396) /
      omega ^ (1 / ((d : ℝ) + 1) : ℝ), ?_, ?_⟩
  · positivity
  · intro T hT hT_le_one y₀ A f u hAcont hfcont hu hA hsub hboundary zStar hzStar
    let B : ℝ := ∫ z in parabolicInterior T y₀,
      (max (f z) 0) ^ (d + 1) / (coefficientAt A z).det
    have hB : 0 ≤ B := by
      dsimp [B]
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem (measurableSet_parabolicInterior T y₀)] with z hz
      exact div_nonneg (pow_nonneg (le_max_right _ _) _)
        (hA z (parabolicInterior_subset_closedParabolicCylinder T y₀ hz)).det_pos.le


    have hroot_nonneg :
        0 ≤ ((sharedTerm_d983397396) /
              omega ^ (1 / ((d : ℝ) + 1) : ℝ)) *
            B ^ (1 / ((d : ℝ) + 1) : ℝ) :=
      mul_nonneg
        (le_of_lt (div_pos (div_pos (by norm_num) (by positivity))
          (Real.rpow_pos_of_pos homega _)))
        (Real.rpow_nonneg hB _)
    have hroot :
        max (u zStar) 0 ≤
          ((sharedTerm_d983397396) /
              omega ^ (1 / ((d : ℝ) + 1) : ℝ)) *
            B ^ (1 / ((d : ℝ) + 1) : ℝ) :=
      le_of_pow_le_pow_left₀ (Nat.succ_ne_zero d) hroot_nonneg (by
          apply le_of_mul_le_mul_left ?_ homega
          calc
            omega * (max (u zStar) 0) ^ (d + 1) ≤
                (sharedTerm_d983397396) ^ (d + 1) * B := (parabolic_abp_unit_pow hd hT hT_le_one y₀ A f u hAcont hfcont hu hA hsub
                        hboundary hzStar)
            _ = omega *
                (((sharedTerm_d983397396) /
                    omega ^ (1 / ((d : ℝ) + 1) : ℝ)) *
                  B ^ (1 / ((d : ℝ) + 1) : ℝ)) ^ (d + 1) := by
              rw [hrecip]
              symm
              exact abp_root_constant_mul_rpow_pow (Nat.succ_ne_zero d) homega hB)
    calc
      u zStar ≤ max (u zStar) 0 := le_max_left _ _
      _ ≤ ((sharedTerm_d983397396) /
              omega ^ (1 / ((d : ℝ) + 1) : ℝ)) *
            B ^ (1 / ((d : ℝ) + 1) : ℝ) := hroot
      _ = ((sharedTerm_d983397396) /
              omega ^ (1 / ((d : ℝ) + 1) : ℝ)) *
            (∫ z in parabolicInterior T y₀,
              (max (f z) 0) ^ (d + 1) /
                (coefficientAt A z).det) ^
              (1 / ((d : ℝ) + 1) : ℝ) := rfl

section
variable {d : ℕ} {lam : ℝ} {T : ℝ} {y₀ : PDE.Vec d} {A : CoefficientField d} (hlam : 0 < lam) (hlo : ∀ z ∈ closedParabolicCylinder T y₀, lam • (1 : PDE.Mat d) ≤ coefficientAt A z)

include hlam hlo
private theorem lower_loewner_posDef_on  :
    ∀ z ∈ closedParabolicCylinder T y₀, (coefficientAt A z).PosDef := by
  intro z hz
  exact posDef_of_loewner_lower hlam (hlo z hz)

private theorem lower_loewner_det_on  :
    ∀ z ∈ closedParabolicCylinder T y₀, lam ^ d ≤ (coefficientAt A z).det := by
  intro z hz
  exact det_lower_of_loewner hlam (hlo z hz)
end


private theorem parabolicExponent_eq_ofReal (d : ℕ) :
    parabolicExponent d = ENNReal.ofReal ((d : ℝ) + 1) := by
  rw [show ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) by norm_num]
  simpa only [parabolicExponent, Nat.cast_add, Nat.cast_one] using
    (ENNReal.ofReal_natCast (d + 1)).symm

private theorem norm_positive_part (x : ℝ) : ‖max x 0‖ = max x 0 := by
  simp_all

variable {d : ℕ}

variable {T : ℝ} {y₀ : PDE.Vec d} {f : HypoellipticAleksandrov.Parabolic.ScalarField d}

private theorem source_memLp_on_parabolicInterior   (hf : Continuous f) :
    MemLp (fun z => max (f z) 0) (parabolicExponent d)
      (volume.restrict (parabolicInterior T y₀)) := by
  let sharedTerm_b6dc4bbe5e := ((volume (parabolicInterior T y₀ ) < ∞))
  have hmeasure : sharedTerm_b6dc4bbe5e :=
    (measure_mono (parabolicInterior_subset_closedParabolicCylinder T y₀)).trans_lt
      (isCompact_closedParabolicCylinder T y₀).measure_lt_top
  letI : Fact sharedTerm_b6dc4bbe5e :=
    ⟨hmeasure⟩

  have hg : Continuous (fun z => max (f z) 0) := hf.max continuous_const
  obtain ⟨C, hC⟩ :=
    (isCompact_closedParabolicCylinder T y₀).exists_bound_of_continuousOn hg.continuousOn
  refine MemLp.of_bound hg.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' (measurableSet_parabolicInterior T y₀)]
  exact Eventually.of_forall fun z hz =>
    hC z (parabolicInterior_subset_closedParabolicCylinder T y₀ hz)

private theorem parabolicLpNormOn_eq_integral_pow
    (hf : MemLp (fun z => max (f z) 0) (parabolicExponent d)
      (volume.restrict (parabolicInterior T y₀))) :
    parabolicLpNormOn d (fun z => max (f z) 0) (parabolicInterior T y₀) =
      (∫ z in parabolicInterior T y₀,
        (max (f z) 0) ^ (d + 1)) ^
          (1 / ((d : ℝ) + 1) : ℝ) := by
  let sharedTerm_49e94c391f := ((1 / ((d : ℝ) + 1) : ℝ))


  rw [parabolicLpNormOn, parabolicELpNormOn, parabolicExponent_eq_ofReal]
  calc
    (eLpNorm (fun z => max (f z) 0) (ENNReal.ofReal ((d : ℝ) + 1)
      ) (volume.restrict (parabolicInterior T y₀))).toReal =
        (∫ z in parabolicInterior T y₀,
          ‖max (f z) 0‖ ^ ((d : ℝ) + 1)) ^
            sharedTerm_49e94c391f :=
      PDE.toReal_eLpNorm_ofReal_eq_integral_rpow_norm_rpow_inv (by positivity) (by
          rw [← parabolicExponent_eq_ofReal]
          exact hf)
    _ = (∫ z in parabolicInterior T y₀,
          (max (f z) 0) ^ (d + 1)) ^
            sharedTerm_49e94c391f := by
      congr 1
      apply integral_congr_ae
      filter_upwards with z
      rw [norm_positive_part,
        show ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]

private theorem source_integrableOn  {lam : ℝ} {T : ℝ}
    {y₀ : PDE.Vec d} {f : HypoellipticAleksandrov.Parabolic.ScalarField d} (hlam : 0 < lam)
    (hf : Continuous f) :
    IntegrableOn (fun z => (max (f z) 0) ^ (d + 1) / lam ^ d)
      (parabolicInterior T y₀)  := (IntegrableOn.mono_set
  (ContinuousOn.integrableOn_compact (isCompact_closedParabolicCylinder T y₀)
    (Continuous.continuousOn
      (Continuous.div (Continuous.pow (Continuous.max hf continuous_const) (d + 1)) continuous_const fun x =>
        LT.lt.ne' (pow_pos hlam d))))
  (parabolicInterior_subset_closedParabolicCylinder T y₀))

private theorem weighted_integrableOn  {T : ℝ}
    {y₀ : PDE.Vec d} {A : CoefficientField d} {f : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hAcont : IsContinuousCoefficient A) (hf : Continuous f)
    (hA : ∀ z ∈ closedParabolicCylinder T y₀, (coefficientAt A z).PosDef) :
    IntegrableOn (fun z =>
      (max (f z) 0) ^ (d + 1) / (coefficientAt A z).det)
      (parabolicInterior T y₀)  := (IntegrableOn.mono_set
  (ContinuousOn.integrableOn_compact (isCompact_closedParabolicCylinder T y₀)
    (ContinuousOn.div (Continuous.continuousOn (Continuous.pow (Continuous.max hf continuous_const) (d + 1)))
      (Continuous.continuousOn (Continuous.matrix_det hAcont)) fun z hz => LT.lt.ne' (Matrix.PosDef.det_pos (hA z hz))))
  (parabolicInterior_subset_closedParabolicCylinder T y₀))

private theorem weighted_integral_le_of_lower  {lam : ℝ} {T : ℝ}
    {y₀ : PDE.Vec d} {A : CoefficientField d} {f : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hlam : 0 < lam)
    (hlo : ∀ z ∈ closedParabolicCylinder T y₀,
      lam • (1 : PDE.Mat d) ≤ coefficientAt A z)
    (hweighted : IntegrableOn (fun z =>
      (max (f z) 0) ^ (d + 1) / (coefficientAt A z).det)
      (parabolicInterior T y₀) )
    (hsource : IntegrableOn (fun z => (max (f z) 0) ^ (d + 1) / lam ^ d)
      (parabolicInterior T y₀) ) :
    (∫ z in parabolicInterior T y₀,
      (max (f z) 0) ^ (d + 1) / (coefficientAt A z).det) ≤
      ∫ z in parabolicInterior T y₀,
        (max (f z) 0) ^ (d + 1) / lam ^ d := by
  refine setIntegral_mono_on hweighted hsource
    (measurableSet_parabolicInterior T y₀) fun z hz => ?_
  refine div_le_div_of_nonneg_left (pow_nonneg (le_max_right _ _) _)
    (pow_pos hlam d) ?_
  exact lower_loewner_det_on hlam hlo z
    (parabolicInterior_subset_closedParabolicCylinder T y₀ hz)

private theorem scalar_root_bound  {lam C W I : ℝ}
    (hC : 0 ≤ C) (hlam : 0 < lam) (hW : 0 ≤ W)
    (hWI : W ≤ I / lam ^ d) (hI : 0 ≤ I) :
    C * W ^ (1 / ((d : ℝ) + 1) : ℝ) ≤
      (C / (lam ^ d) ^ (1 / ((d : ℝ) + 1) : ℝ)) *
        I ^ (1 / ((d : ℝ) + 1) : ℝ) := by
  let sharedTerm_bebe20be3e := ((1 / ((d : ℝ) + 1) : ℝ))



  calc
    C * W ^ sharedTerm_bebe20be3e ≤
        C * (I / lam ^ d) ^ sharedTerm_bebe20be3e :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hW hWI (by positivity)) hC
    _ = C * (I ^ sharedTerm_bebe20be3e /
        (lam ^ d) ^ sharedTerm_bebe20be3e) := by
      rw [Real.div_rpow hI ((pow_pos hlam d).le)]
    _ = (C / (lam ^ d) ^ sharedTerm_bebe20be3e) *
        I ^ sharedTerm_bebe20be3e := by ring

/-- The smooth parabolic ABP estimate under lower Loewner ellipticity, with
the exact restricted `L^(d + 1)` norm. -/
theorem parabolic_abp_unit_of_lower_ellipticity
    (d : ℕ) (hd : 0 < d) (lam : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T : ℝ}, 0 < T → T ≤ 1 →
      ∀ (y₀ : PDE.Vec d) (A : CoefficientField d)
        (f u : HypoellipticAleksandrov.Parabolic.ScalarField d),
        IsContinuousCoefficient A → Continuous f → ContDiff ℝ 2 u →
        (∀ z ∈ closedParabolicCylinder T y₀,
          lam • (1 : PDE.Mat d) ≤ coefficientAt A z) →
        IsParabolicSubsolutionOn A f u (parabolicInterior T y₀) →
        (∀ z ∈ forwardParabolicBoundary T y₀, u z ≤ 0) →
        ∀ zStar ∈ closedParabolicCylinder T y₀,
          u zStar ≤ C *
            parabolicLpNormOn d (fun z => max (f z) 0)
              (parabolicInterior T y₀) := by
  let sharedTerm_2f19de3390 := ((1 / ((d : ℝ) + 1) : ℝ))
  obtain ⟨C_d, hC_d, hABP⟩ := parabolic_abp_unit d hd
  refine ⟨C_d / (lam ^ d) ^ sharedTerm_2f19de3390,
    div_pos hC_d (Real.rpow_pos_of_pos (pow_pos hlam d) _), ?_⟩
  intro T hT hT_le_one y₀ A f u hAcont hf hu hlo hsub hboundary zStar hzStar
  have hpos := lower_loewner_posDef_on hlam hlo




  have hcomparison := weighted_integral_le_of_lower hlam hlo (weighted_integrableOn hAcont hf hpos) (source_integrableOn (d := d) (lam := lam) (T := T) (y₀ := y₀) hlam hf)
  let W : ℝ := ∫ z in parabolicInterior T y₀,
    (max (f z) 0) ^ (d + 1) / (coefficientAt A z).det
  let I : ℝ := ∫ z in parabolicInterior T y₀, (max (f z) 0) ^ (d + 1)



  calc
    u zStar ≤ C_d * W ^ sharedTerm_2f19de3390 := (hABP hT hT_le_one y₀ A f u hAcont hf hu hpos hsub hboundary zStar hzStar)
    _ ≤ (C_d / (lam ^ d) ^ sharedTerm_2f19de3390) *
        I ^ sharedTerm_2f19de3390 :=
      scalar_root_bound hC_d.le hlam (by
          dsimp [W]
          apply integral_nonneg_of_ae
          filter_upwards [ae_restrict_mem (measurableSet_parabolicInterior T y₀)] with z hz
          exact div_nonneg (pow_nonneg (le_max_right _ _) _)
            (hpos z (parabolicInterior_subset_closedParabolicCylinder T y₀ hz)).det_pos.le) (by
          dsimp [W, I]
          rw [integral_div] at hcomparison
          exact hcomparison) (by
          dsimp [I]
          exact integral_nonneg fun z => pow_nonneg (le_max_right _ _) _)
    _ = (C_d / (lam ^ d) ^ sharedTerm_2f19de3390) *
        parabolicLpNormOn d (fun z => max (f z) 0)
          (parabolicInterior T y₀) := by
      rw [parabolicLpNormOn_eq_integral_pow (source_memLp_on_parabolicInterior hf (d := d) (T := T) (y₀ := y₀))]

end HypoellipticAleksandrov.Parabolic
