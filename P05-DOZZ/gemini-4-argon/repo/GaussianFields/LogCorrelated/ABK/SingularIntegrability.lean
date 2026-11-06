/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import GaussianFields.LogCorrelated.ABK.KernelPairing

/-!
# GaussianFields.LogCorrelated/ABK/SingularIntegrability

Port of the corresponding GaussianFields source module.
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace GaussianFields

/-- The one-dimensional singular exponent used for a concrete integrable majorant. -/
@[expose]
noncomputable def abkSingularMajorantExponent : ℝ := -(3 / 4 : ℝ)



/-- The one-dimensional function `|x|^{-3/4}`, restricted to a symmetric interval. -/
@[expose]
noncomputable def abkOneDimensionalSingularMajorant (R x : ℝ) : ℝ :=
  (Set.Icc (-R) R).indicator (fun t : ℝ => |t| ^ abkSingularMajorantExponent) x

/-- A coordinate-box majorant with one singular coordinate and bounded indicators in all other
coordinates. -/
@[expose]
noncomputable def abkCoordinateBoxSingularMajorant {d : Nat} (i : Fin d) (R : ℝ)
    (x : Vec d) : ℝ :=
  ∏ j : Fin d,
    if j = i then
      abkOneDimensionalSingularMajorant R (x j)
    else
      (Set.Icc (-R) R).indicator (fun _ : ℝ => (1 : ℝ)) (x j)

/-- Indicator of the coordinate box `[-R,R]^d`, written as a product of one-dimensional
indicators. -/
@[expose]
noncomputable def abkBoxIndicatorVec {d : Nat} (R : ℝ) (x : Vec d) : ℝ :=
  ∏ j : Fin d, (Set.Icc (-R) R).indicator (fun _ : ℝ => (1 : ℝ)) (x j)

/-- Pair-space singular majorant after the additive shear `(x,y) ↦ (x-y,y)`. -/
@[expose]
noncomputable def abkPairDifferenceBoxSingularMajorant {d : Nat} (i : Fin d) (R : ℝ)
    (p : Vec d × Vec d) : ℝ :=
  abkCoordinateBoxSingularMajorant i (2 * R) (p.1 - p.2) *
    abkBoxIndicatorVec R p.2

/-- Pair-space bounded box majorant after the additive shear `(x,y) ↦ (x-y,y)`. -/
@[expose]
noncomputable def abkPairDifferenceBoxMajorant {d : Nat} (R : ℝ)
    (p : Vec d × Vec d) : ℝ :=
  abkBoxIndicatorVec (2 * R) (p.1 - p.2) *
    abkBoxIndicatorVec R p.2

/-- The coordinate-box indicator is one on the coordinate box. -/
theorem abkBoxIndicatorVec_eq_one_of_forall_abs_apply_le {d}
    {R} {x} (hx : ∀ j : Fin d, |x j| ≤ R) :
    abkBoxIndicatorVec R x = 1 := by
  unfold abkBoxIndicatorVec
  refine Finset.prod_eq_one ?_
  intro j _hj
  have hj : x j ∈ Set.Icc (-R) R := (abs_le.mp (hx j))
  rw [Set.indicator_of_mem hj]

/-- The one-dimensional singular majorant equals `|x|^{-3/4}` inside the box. -/
theorem abkOneDimensionalSingularMajorant_eq_rpow_of_abs_le
    {R x} (hx : |x| ≤ R) :
    abkOneDimensionalSingularMajorant R x =
      |x| ^ abkSingularMajorantExponent := by
  unfold abkOneDimensionalSingularMajorant
  have hxmem : x ∈ Set.Icc (-R) R := abs_le.mp hx
  rw [Set.indicator_of_mem hxmem]

/-- The coordinate-box singular majorant reduces to the singular coordinate inside the box. -/
theorem abkCoordinateBoxSingularMajorant_eq_abs_apply_rpow_of_forall_abs_apply_le
    {d} i {R} {x}
    (hx : ∀ j : Fin d, |x j| ≤ R) :
    abkCoordinateBoxSingularMajorant i R x =
      |x i| ^ abkSingularMajorantExponent := by
  unfold abkCoordinateBoxSingularMajorant
  rw [Fintype.prod_eq_single i]
  · rw [ite_eq_left rfl]
    exact abkOneDimensionalSingularMajorant_eq_rpow_of_abs_le (hx i)
  · intro j hji
    rw [ite_eq_right hji]
    have hj : x j ∈ Set.Icc (-R) R := abs_le.mp (hx j)
    rw [Set.indicator_of_mem hj]







/-- The pair-space singular box majorant is the singular coordinate inside the pair box. -/
theorem abkPairDifferenceBoxSingularMajorant_eq_abs_apply_rpow_of_forall_abs_apply_le
    {d} i {R} {p : Vec d × Vec d}
    (hdiff : ∀ j : Fin d, |(p.1 - p.2) j| ≤ 2 * R)
    (hy : ∀ j : Fin d, |p.2 j| ≤ R) :
    abkPairDifferenceBoxSingularMajorant i R p =
      |(p.1 - p.2) i| ^ abkSingularMajorantExponent := by
  unfold abkPairDifferenceBoxSingularMajorant
  rw [abkCoordinateBoxSingularMajorant_eq_abs_apply_rpow_of_forall_abs_apply_le i hdiff,
    abkBoxIndicatorVec_eq_one_of_forall_abs_apply_le hy, mul_one]

/-- The one-dimensional singular majorant is integrable on every bounded symmetric interval. -/
theorem integrableOn_abs_rpow_abkSingularMajorantExponent_Icc R (hR : 0 ≤ R) :
    IntegrableOn
      (fun x : ℝ => |x| ^ abkSingularMajorantExponent)
      (Set.Icc (-R) R) (volume : Measure ℝ) := by
  have hpos_interval :
      IntervalIntegrable
        (fun x => x ^ abkSingularMajorantExponent)
        volume 0 R :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num [abkSingularMajorantExponent])
  have hpos :
      IntegrableOn
        (fun x => |x| ^ abkSingularMajorantExponent)
        (Set.Icc 0 R) (volume : Measure ℝ) := by
    refine ((intervalIntegrable_iff_integrableOn_Icc_of_le hR).mp hpos_interval).congr_fun ?_ measurableSet_Icc
    intro x hx
    simp [abs_of_nonneg hx.1]
  have hneg :
      IntegrableOn
        (fun x => |x| ^ abkSingularMajorantExponent)
        (Set.Icc (-R) 0) (volume : Measure ℝ) := by
    refine ((intervalIntegrable_iff_integrableOn_Icc_of_le (neg_nonpos.mpr hR)).mp (show IntervalIntegrable (fun x => (-x) ^ abkSingularMajorantExponent) volume (-R) 0 by exact ((show -0 = (0 : ℝ) by norm_num) ▸ (IntervalIntegrable.iff_comp_neg (f := fun x => x ^ abkSingularMajorantExponent) (a := 0) (b := R)).mp hpos_interval).symm)).congr_fun ?_ measurableSet_Icc
    intro x hx
    simp [abs_of_nonpos hx.2]
  have hcover : Set.Icc (-R) R = Set.Icc (-R) 0 ∪ Set.Icc 0 R := by
    ext x
    constructor
    · intro hx
      rcases le_total x 0 with hx0 | h0x
      · exact Or.inl ⟨hx.1, hx0⟩
      · exact Or.inr ⟨h0x, hx.2⟩
    · intro hx
      rcases hx with hx | hx
      · exact ⟨hx.1, hx.2.trans hR⟩
      · exact ⟨(neg_nonpos.mpr hR).trans hx.1, hx.2⟩
  rw [hcover]
  exact hneg.union hpos

/-- The one-dimensional singular majorant, extended by zero off the box, is integrable. -/
theorem integrable_abkOneDimensionalSingularMajorant R (hR : 0 ≤ R) :
    Integrable (abkOneDimensionalSingularMajorant R) (volume : Measure ℝ) := by
  unfold abkOneDimensionalSingularMajorant
  exact (integrableOn_abs_rpow_abkSingularMajorantExponent_Icc R hR).integrable_indicator
    measurableSet_Icc

/-- The bounded one-dimensional box indicator is integrable. -/
theorem integrable_indicator_Icc_one R (_hR : 0 ≤ R) :
    Integrable
      ((Set.Icc (-R) R).indicator (fun _ : ℝ => (1 : ℝ)))
      (volume : Measure ℝ) := by
  exact continuousOn_const.integrableOn_Icc.integrable_indicator measurableSet_Icc

/-- The coordinate-box singular majorant is integrable on `Vec d`. -/
theorem integrable_abkCoordinateBoxSingularMajorant {d} i
    R (hR : 0 ≤ R) :
    Integrable (abkCoordinateBoxSingularMajorant i R)
      (volume : Measure (Vec d)) := by
  let f : Fin d → ℝ → ℝ := fun j x =>
    if j = i then
      abkOneDimensionalSingularMajorant R x
    else
      (Set.Icc (-R) R).indicator (fun _ : ℝ => (1 : ℝ)) x
  have hf : ∀ j : Fin d, Integrable (f j) (volume : Measure ℝ) := fun j => by
    by_cases hji : j = i
    · subst hji
      simpa [f] using integrable_abkOneDimensionalSingularMajorant R hR
    · simpa [f, hji] using integrable_indicator_Icc_one R hR
  rw [MeasureTheory.volume_pi]
  unfold abkCoordinateBoxSingularMajorant
  simpa only [f] using (Integrable.fintype_prod hf)

/-- The coordinate-box indicator is integrable on `Vec d`. -/
theorem integrable_abkBoxIndicatorVec {d : Nat} R (hR : 0 ≤ R) :
    Integrable (abkBoxIndicatorVec (d := d) R) (volume : Measure (Vec d)) := by
  let f : Fin d → ℝ → ℝ := fun _ x =>
    (Set.Icc (-R) R).indicator (fun _ : ℝ => (1 : ℝ)) x
  rw [MeasureTheory.volume_pi]
  unfold abkBoxIndicatorVec
  simpa only [f] using (Integrable.fintype_prod (fun _ => integrable_indicator_Icc_one R hR : ∀ j : Fin d, Integrable (f j) (volume : Measure ℝ)))

/-- The pair-space difference singular majorant is integrable. -/
theorem integrable_abkPairDifferenceBoxSingularMajorant {d} i
    R (hR : 0 ≤ R) :
    Integrable (abkPairDifferenceBoxSingularMajorant i R)
      ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) := by
  let μ := (volume : Measure (Vec d)).prod (volume : Measure (Vec d))
  let T : Vec d × Vec d → Vec d × Vec d := fun p => (p.1 - p.2, p.2)
  unfold abkPairDifferenceBoxSingularMajorant
  change Integrable
    (fun p : Vec d × Vec d =>
      abkCoordinateBoxSingularMajorant i (2 * R) (p.1 - p.2) *
        abkBoxIndicatorVec R p.2) μ
  exact (show MeasurePreserving T μ μ by simpa [T, μ] using (measurePreserving_sub_prod (volume : Measure (Vec d)) (volume : Measure (Vec d)))).integrable_comp_of_integrable (by simpa [μ] using (integrable_abkCoordinateBoxSingularMajorant i (2 * R) (mul_nonneg (by norm_num) hR)).mul_prod (integrable_abkBoxIndicatorVec (d := d) R hR))

/-- The pair-space bounded box majorant is integrable. -/
theorem integrable_abkPairDifferenceBoxMajorant {d : Nat}
    R (hR : 0 ≤ R) :
    Integrable (abkPairDifferenceBoxMajorant (d := d) R)
      ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) := by
  let μ := (volume : Measure (Vec d)).prod (volume : Measure (Vec d))
  let T : Vec d × Vec d → Vec d × Vec d := fun p => (p.1 - p.2, p.2)
  unfold abkPairDifferenceBoxMajorant
  change Integrable
    (fun p : Vec d × Vec d =>
      abkBoxIndicatorVec (2 * R) (p.1 - p.2) * abkBoxIndicatorVec R p.2) μ
  exact (show MeasurePreserving T μ μ by simpa [T, μ] using (measurePreserving_sub_prod (volume : Measure (Vec d)) (volume : Measure (Vec d)))).integrable_comp_of_integrable (by simpa [μ] using (integrable_abkBoxIndicatorVec (d := d) (2 * R) (mul_nonneg (by norm_num) hR)).mul_prod (integrable_abkBoxIndicatorVec (d := d) R hR))

/-- After the additive shear, any fixed coordinate of the difference is nonzero a.e. -/
theorem ae_sub_apply_ne_zero_volume_prod {d} i :
    ∀ᵐ p : Vec d × Vec d
      ∂((volume : Measure (Vec d)).prod (volume : Measure (Vec d))),
      (p.1 - p.2) i ≠ 0 := by
  let μ := (volume : Measure (Vec d)).prod (volume : Measure (Vec d))
  let T : Vec d × Vec d → Vec d × Vec d := fun p => (p.1 - p.2, p.2)
  have hcoord : ∀ᵐ v : Vec d ∂(volume : Measure (Vec d)), v i ≠ 0 := by
    simpa [MeasureTheory.volume_pi] using
      (Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) i (0 : ℝ))
  have hprod : ∀ᵐ q : Vec d × Vec d ∂μ, q.1 i ≠ 0 := by
    have hmeas : MeasurableSet {q : Vec d × Vec d | q.1 i ≠ 0} := (isClosed_eq ((continuous_apply i).comp continuous_fst) continuous_const).measurableSet.compl
    rw [Measure.ae_prod_iff_ae_ae hmeas]
    filter_upwards [hcoord] with v hv
    exact Filter.Eventually.of_forall fun _ => hv
  simpa [T, μ] using (show MeasurePreserving T μ μ by simpa [T, μ] using (measurePreserving_sub_prod (volume : Measure (Vec d)) (volume : Measure (Vec d)))).quasiMeasurePreserving.ae hprod

/-- The centered Riesz slope integrand is a.e. strongly measurable for nonzero `α`. -/
theorem aestronglyMeasurable_abkCenteredRieszSlopeKernel_integrand_of_ne
    {d} (hd : 0 < d) (ψ φ : MeanZeroTestFunction d) {α : ℝ}
    (hα : α ≠ 0) :
    AEStronglyMeasurable
      (fun p : Vec d × Vec d =>
        ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2)
      ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) := by
  let μ := (volume : Measure (Vec d)).prod (volume : Measure (Vec d))
  let s : Set (Vec d × Vec d) := {p | p.1 ≠ p.2}
  have hpow :
      ContinuousOn
        (fun p : Vec d × Vec d => (euclideanNorm (p.1 - p.2)) ^ (-α)) s := by
    refine (((continuous_euclideanNorm (d := d)).comp (continuous_fst.sub continuous_snd)).continuousOn).rpow_const ?_
    intro p hp
    left
    exact ne_of_gt (abkEuclideanNorm_pos_of_ne_zero (by intro hzero; exact hp (sub_eq_zero.mp hzero)))
  have hcont :
      ContinuousOn
        (fun p : Vec d × Vec d =>
          ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2) s := (((ψ.continuous.comp continuous_fst).continuousOn).mul
      ((φ.continuous.comp continuous_snd).continuousOn)).mul (by unfold abkCenteredRieszSlopeKernel; exact (hpow.sub continuousOn_const).div continuousOn_const (fun _ _ => hα))
  have hsm := hcont.aestronglyMeasurable (μ := μ) ((isClosed_eq continuous_fst continuous_snd).measurableSet.compl)
  rw [Measure.restrict_eq_self_of_ae_mem (show ∀ᵐ p : Vec d × Vec d ∂μ, p ∈ s by simpa [s, μ] using ae_fst_ne_snd_volume_prod hd)] at hsm
  simpa [μ] using hsm


/-- Pointwise domination of the centered Riesz slope integrand by the concrete pair-box
majorant, assuming explicit support and uniform bounds for the two test functions. -/
theorem norm_abkCenteredRieszSlopeKernel_integrand_le_pair_majorant
    {d : Nat} i ψ φ
    {R Mψ Mφ α : ℝ}
    (hR : 1 ≤ R)
    (hMψ_nonneg : 0 ≤ Mψ) (hMφ_nonneg : 0 ≤ Mφ)
    (hψ_bound : ∀ x : Vec d, |ψ x| ≤ Mψ)
    (hφ_bound : ∀ x : Vec d, |φ x| ≤ Mφ)
    (hψ_support : Function.support ψ ⊆ {x : Vec d | euclideanNorm x ≤ R})
    (hφ_support : Function.support φ ⊆ {x : Vec d | euclideanNorm x ≤ R})
    (hα_pos : 0 < α) (hα_le : α ≤ 1 / 2)
    {p : Vec d × Vec d} (hp_coord : (p.1 - p.2) i ≠ 0) :
    ‖ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2‖ ≤
      (Mψ * Mφ * (4 + Real.log (2 * R))) *
        (abkPairDifferenceBoxMajorant R p +
          abkPairDifferenceBoxSingularMajorant i R p) := by
  have abkBoxIndicatorVec_nonneg {d : Nat} (R : ℝ) (x : Vec d) : 0 ≤ abkBoxIndicatorVec R x := by
    unfold abkBoxIndicatorVec
    refine Finset.prod_nonneg ?_
    intro j _hj
    by_cases hx : x j ∈ Set.Icc (-R) R
    · rw [Set.indicator_of_mem hx]
      norm_num
    · rw [Set.indicator_of_notMem hx]
  have abkPairDifferenceBoxMajorant_eq_one_of_forall_abs_apply_le {d} {R} {p : Vec d × Vec d} (hdiff : ∀ j : Fin d, |(p.1 - p.2) j| ≤ 2 * R) (hy : ∀ j : Fin d, |p.2 j| ≤ R) : abkPairDifferenceBoxMajorant R p = 1 := by
    unfold abkPairDifferenceBoxMajorant
    rw [abkBoxIndicatorVec_eq_one_of_forall_abs_apply_le hdiff,
      abkBoxIndicatorVec_eq_one_of_forall_abs_apply_le hy, mul_one]
  have abkPairDifferenceBoxSingularMajorant_nonneg : 0 ≤ abkPairDifferenceBoxSingularMajorant i R p := by
    have abkCoordinateBoxSingularMajorant_nonneg (R : ℝ) x : 0 ≤ abkCoordinateBoxSingularMajorant i R x := by
      have abkOneDimensionalSingularMajorant_nonneg x : 0 ≤ abkOneDimensionalSingularMajorant R x := by
        unfold abkOneDimensionalSingularMajorant
        by_cases hx : x ∈ Set.Icc (-R) R
        · rw [Set.indicator_of_mem hx]
          exact Real.rpow_nonneg (abs_nonneg x) _
        · rw [Set.indicator_of_notMem hx]
      unfold abkCoordinateBoxSingularMajorant
      refine Finset.prod_nonneg ?_
      intro j _hj
      by_cases hji : j = i
      · rw [ite_eq_left hji]
        exact abkOneDimensionalSingularMajorant_nonneg (x j)
      · rw [ite_eq_right hji]
        by_cases hx : x j ∈ Set.Icc (-R) R
        · rw [Set.indicator_of_mem hx]
          norm_num
        · rw [Set.indicator_of_notMem hx]
    unfold abkPairDifferenceBoxSingularMajorant
    exact mul_nonneg
      (abkCoordinateBoxSingularMajorant_nonneg (2 * R) (p.1 - p.2))
      (abkBoxIndicatorVec_nonneg R p.2)
  have abkPairDifferenceBoxMajorant_nonneg : 0 ≤ abkPairDifferenceBoxMajorant (d := d) R p := by
    unfold abkPairDifferenceBoxMajorant
    exact mul_nonneg (abkBoxIndicatorVec_nonneg (2 * R) (p.1 - p.2))
      (abkBoxIndicatorVec_nonneg R p.2)
  have abs_rpow_neg_sub_one_div_le_abkSingularMajorant {α : ℝ} {ρ} {R : ℝ} (hα_pos : 0 < α) (hα_le : α ≤ 1 / 2) (hρ_pos : 0 < ρ) (hρR : ρ ≤ R) (hR : 1 ≤ R) : |(ρ ^ (-α) - 1) / α| ≤ (4 + Real.log R) * (1 + ρ ^ abkSingularMajorantExponent) := by
    have real_exp_sub_one_le_mul_exp_of_nonneg {t} (_ht : 0 ≤ t) : Real.exp t - 1 ≤ t * Real.exp t := by
      have := Real.add_one_le_exp (-t)
      calc
        Real.exp t - 1 = Real.exp t * (1 - Real.exp (-t)) := by
          rw [mul_sub, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
        _ ≤ Real.exp t * t := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using (mul_le_mul_of_nonneg_right (show 1 - Real.exp (-t) ≤ t by linarith) (le_of_lt (Real.exp_pos t)))
        _ = t * Real.exp t := by ring_nf
    have := Real.log_nonneg hR
    have hcoef_nonneg : 0 ≤ 4 + Real.log R := by linarith
    have hsing_nonneg : 0 ≤ ρ ^ abkSingularMajorantExponent :=
      Real.rpow_nonneg hρ_pos.le _
    by_cases hρ_le_one : ρ ≤ 1
    · let u : ℝ := ρ⁻¹
      have hu_pos : 0 < u := inv_pos.mpr hρ_pos
      have hu_one : 1 ≤ u := by
        dsimp [u]
        exact (one_le_inv₀ hρ_pos).mpr hρ_le_one
      have hdiv :
          (u ^ α - 1) / α ≤ Real.log u * u ^ α := by
        rw [div_le_iff₀ hα_pos]
        calc
          u ^ α - 1 ≤ (α * Real.log u) * u ^ α := (by rw [Real.rpow_def_of_pos hu_pos]; simpa [mul_comm, mul_left_comm, mul_assoc] using real_exp_sub_one_le_mul_exp_of_nonneg (mul_nonneg hα_pos.le (Real.log_nonneg hu_one)))
          _ = α * (Real.log u * u ^ α) := by ring_nf
          _ = Real.log u * u ^ α * α := by ring_nf
      have hlog_bound : Real.log u ≤ 4 * u ^ (1 / 4 : ℝ) := by
        calc
          Real.log u ≤ u ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) := (Real.log_le_rpow_div hu_pos.le (by norm_num : (0 : ℝ) < 1 / 4))
          _ = 4 * u ^ (1 / 4 : ℝ) := by ring_nf
      have hmain :
          |(ρ ^ (-α) - 1) / α| ≤ 4 * ρ ^ abkSingularMajorantExponent := by
        rw [(show |(ρ ^ (-α) - 1) / α| = (u ^ α - 1) / α by rw [abs_of_nonneg (show 0 ≤ (ρ ^ (-α) - 1) / α by rw [Real.rpow_neg_eq_inv_rpow]; exact div_nonneg (sub_nonneg.mpr (Real.one_le_rpow hu_one hα_pos.le)) hα_pos.le), Real.rpow_neg_eq_inv_rpow])]
        calc
          (u ^ α - 1) / α ≤ Real.log u * u ^ α := hdiv
          _ ≤ (4 * u ^ (1 / 4 : ℝ)) * u ^ (1 / 2 : ℝ) := by
            exact mul_le_mul hlog_bound (Real.rpow_le_rpow_of_exponent_le hu_one hα_le)
              (Real.rpow_nonneg hu_pos.le _)
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
                (Real.rpow_nonneg hu_pos.le _))
          _ = 4 * u ^ (3 / 4 : ℝ) := by
            calc
              (4 * u ^ (1 / 4 : ℝ)) * u ^ (1 / 2 : ℝ)
                  = 4 * (u ^ (1 / 4 : ℝ) * u ^ (1 / 2 : ℝ)) := by ring_nf
              _ = 4 * u ^ ((1 / 4 : ℝ) + (1 / 2 : ℝ)) := by
                rw [Real.rpow_add hu_pos]
              _ = 4 * u ^ (3 / 4 : ℝ) := by ring_nf
          _ = 4 * ρ ^ abkSingularMajorantExponent := by
            rw [(show u ^ (3 / 4 : ℝ) = ρ ^ abkSingularMajorantExponent by dsimp [u, abkSingularMajorantExponent]; rw [← Real.rpow_neg_eq_inv_rpow])]
      calc
        |(ρ ^ (-α) - 1) / α| ≤ 4 * ρ ^ abkSingularMajorantExponent := hmain
        _ ≤ (4 + Real.log R) * ρ ^ abkSingularMajorantExponent := by
          exact mul_le_mul_of_nonneg_right (by linarith) hsing_nonneg
        _ ≤ (4 + Real.log R) * (1 + ρ ^ abkSingularMajorantExponent) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hcoef_nonneg
    · have hρ_ge_one : 1 ≤ ρ := le_of_not_ge hρ_le_one
      have hpow_le_one := Real.rpow_le_one_of_one_le_of_nonpos hρ_ge_one (neg_nonpos.mpr hα_pos.le)
      have := Real.log_nonneg hρ_ge_one
      have hsub_le :
          1 - ρ ^ (-α) ≤ α * Real.log ρ := by
        have :=
          Real.add_one_le_exp (-(α * Real.log ρ))
        have : ρ ^ (-α) = Real.exp (-(α * Real.log ρ)) := by
          rw [Real.rpow_def_of_pos hρ_pos]
          congr 1
          ring_nf
        linarith
      have hdiv :
          (1 - ρ ^ (-α)) / α ≤ Real.log ρ := by
        rw [div_le_iff₀ hα_pos]
        calc
          1 - ρ ^ (-α) ≤ α * Real.log ρ := hsub_le
          _ = Real.log ρ * α := by ring_nf
      have hlog_le := Real.log_le_log hρ_pos hρR
      calc
        |(ρ ^ (-α) - 1) / α| = (1 - ρ ^ (-α)) / α := (by rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hpow_le_one) hα_pos.le)]; ring_nf)
        _ ≤ Real.log ρ := hdiv
        _ ≤ Real.log R := hlog_le
        _ ≤ 4 + Real.log R := by linarith
        _ ≤ (4 + Real.log R) * (1 + ρ ^ abkSingularMajorantExponent) := by
          calc
            4 + Real.log R = (4 + Real.log R) * 1 := by ring_nf
            _ ≤ (4 + Real.log R) * (1 + ρ ^ abkSingularMajorantExponent) := by
              exact mul_le_mul_of_nonneg_left (by linarith) hcoef_nonneg
  let C := Mψ * Mφ * (4 + Real.log (2 * R))
  have h2R : 1 ≤ 2 * R := by nlinarith
  have hcoef_nonneg : 0 ≤ 4 + Real.log (2 * R) := by
    have := Real.log_nonneg h2R
    linarith
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg hMψ_nonneg hMφ_nonneg) hcoef_nonneg
  have hsum_nonneg := add_nonneg (abkPairDifferenceBoxMajorant_nonneg)
      (abkPairDifferenceBoxSingularMajorant_nonneg)
  by_cases hψ_zero : ψ p.1 = 0
  · calc
      ‖ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2‖ = 0 := by
        simp [hψ_zero]
      _ ≤ C *
          (abkPairDifferenceBoxMajorant R p +
            abkPairDifferenceBoxSingularMajorant i R p) :=
        mul_nonneg hC_nonneg hsum_nonneg
  by_cases hφ_zero : φ p.2 = 0
  · calc
      ‖ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2‖ = 0 := by
        simp [hφ_zero]
      _ ≤ C *
          (abkPairDifferenceBoxMajorant R p +
            abkPairDifferenceBoxSingularMajorant i R p) :=
        mul_nonneg hC_nonneg hsum_nonneg
  have hy_norm := hφ_support hφ_zero
  have hy_box : ∀ j : Fin d, |p.2 j| ≤ R := by
    intro j
    exact (abs_apply_le_euclideanNorm p.2 j).trans hy_norm
  have hρ_le : euclideanNorm (p.1 - p.2) ≤ 2 * R := by
    have hsub : p.1 - p.2 = p.1 + (-p.2) := by
      ext j
      simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
      ring_nf
    calc
      euclideanNorm (p.1 - p.2) = euclideanNorm (p.1 + (-p.2)) := by rw [hsub]
      _ ≤ euclideanNorm p.1 + euclideanNorm (-p.2) := euclideanNorm_add_le p.1 (-p.2)
      _ = euclideanNorm p.1 + euclideanNorm p.2 := by rw [euclideanNorm_neg]
      _ ≤ R + R := add_le_add (hψ_support hψ_zero) hy_norm
      _ = 2 * R := by ring_nf
  have hdiff_box : ∀ j : Fin d, |(p.1 - p.2) j| ≤ 2 * R := by
    intro j
    exact (abs_apply_le_euclideanNorm (p.1 - p.2) j).trans hρ_le
  calc
    ‖ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2‖
        ≤ ‖ψ p.1‖ * ‖φ p.2‖ *
            ‖abkCenteredRieszSlopeKernel α p.1 p.2‖ := norm_mul₃_le
    _ ≤ (Mψ * Mφ) *
          ((4 + Real.log (2 * R)) *
            (1 + (euclideanNorm (p.1 - p.2)) ^ abkSingularMajorantExponent)) := by
          exact mul_le_mul (mul_le_mul (show ‖ψ p.1‖ ≤ Mψ by simpa [Real.norm_eq_abs] using hψ_bound p.1) (show ‖φ p.2‖ ≤ Mφ by simpa [Real.norm_eq_abs] using hφ_bound p.2) (norm_nonneg _) hMψ_nonneg) (by rw [abkCenteredRieszSlopeKernel, Real.norm_eq_abs]; exact (abs_rpow_neg_sub_one_div_le_abkSingularMajorant (α := α) (ρ := euclideanNorm (p.1 - p.2)) (R := 2 * R) hα_pos hα_le (abkEuclideanNorm_pos_of_ne_zero (by intro hzero; exact hp_coord (by rw [hzero]; rfl))) hρ_le h2R)) (norm_nonneg _)
            (mul_nonneg hMψ_nonneg hMφ_nonneg)
    _ = C * (1 + (euclideanNorm (p.1 - p.2)) ^ abkSingularMajorantExponent) := by
          dsimp [C]
          ring_nf
    _ ≤ C * (1 + |(p.1 - p.2) i| ^ abkSingularMajorantExponent) := by
          exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (Real.rpow_le_rpow_of_nonpos (abs_pos.mpr hp_coord) (abs_apply_le_euclideanNorm (p.1 - p.2) i) (by norm_num [abkSingularMajorantExponent]))) hC_nonneg
    _ = C *
          (abkPairDifferenceBoxMajorant R p +
            abkPairDifferenceBoxSingularMajorant i R p) := by
          rw [(abkPairDifferenceBoxMajorant_eq_one_of_forall_abs_apply_le hdiff_box hy_box), (abkPairDifferenceBoxSingularMajorant_eq_abs_apply_rpow_of_forall_abs_apply_le i hdiff_box hy_box)]

/-- Concrete integrable dominated-convergence majorant for the centered Riesz slope
integrands associated to two ABK test functions. -/
theorem exists_integrable_bound_abkCenteredRieszSlopeKernel_integrand
    {d} (hd : 0 < d) (ψ φ : MeanZeroTestFunction d) :
    ∃ bound : Vec d × Vec d → ℝ,
      Integrable bound
        ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) ∧
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        ∀ᵐ p : Vec d × Vec d
          ∂((volume : Measure (Vec d)).prod (volume : Measure (Vec d))),
          ‖ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2‖ ≤ bound p := by
  let i : Fin d := ⟨0, hd⟩
  rcases exists_support_subset_euclideanClosedBall_meanZeroTestFunction ψ with
    ⟨Rψ, _hRψ_nonneg, hψ_support₀⟩
  rcases exists_support_subset_euclideanClosedBall_meanZeroTestFunction φ with
    ⟨Rφ, _hRφ_nonneg, hφ_support₀⟩
  rcases exists_abs_meanZeroTestFunction_le ψ with
    ⟨Mψ, hMψ_nonneg, hψ_bound⟩
  rcases exists_abs_meanZeroTestFunction_le φ with
    ⟨Mφ, hMφ_nonneg, hφ_bound⟩
  let R := max 1 (max Rψ Rφ)
  have hR : 1 ≤ R := le_max_left _ _
  have hR_nonneg := zero_le_one.trans hR
  let C := Mψ * Mφ * (4 + Real.log (2 * R))
  let bound : Vec d × Vec d → ℝ := fun p =>
    C * (abkPairDifferenceBoxMajorant R p +
      abkPairDifferenceBoxSingularMajorant i R p)
  refine ⟨bound, ?_, ?_⟩
  · have hsum :
        Integrable
          (fun p =>
            abkPairDifferenceBoxMajorant R p +
              abkPairDifferenceBoxSingularMajorant i R p)
          ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) :=
      (integrable_abkPairDifferenceBoxMajorant (d := d) R hR_nonneg).add
        (integrable_abkPairDifferenceBoxSingularMajorant i R hR_nonneg)
    simpa [bound, C] using hsum.const_mul C
  · filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with α hα
    filter_upwards [ae_sub_apply_ne_zero_volume_prod i] with p hp_coord
    simpa [bound, C] using
      norm_abkCenteredRieszSlopeKernel_integrand_le_pair_majorant
        i ψ φ hR hMψ_nonneg hMφ_nonneg hψ_bound hφ_bound
        (by intro x hx; exact (hψ_support₀ hx).trans ((le_max_left Rψ Rφ).trans (le_max_right 1 (max Rψ Rφ)))) (by intro x hx; exact (hφ_support₀ hx).trans ((le_max_right Rψ Rφ).trans (le_max_right 1 (max Rψ Rφ)))) hα.1 hα.2 hp_coord

/-- For each fixed small positive `α`, the centered Riesz slope integrand is integrable. -/
theorem integrable_abkCenteredRieszSlopeKernel_integrand_of_pos_le_half
    {d} (hd : 0 < d) (ψ φ : MeanZeroTestFunction d) {α : ℝ}
    (hα_pos : 0 < α) (hα_le : α ≤ 1 / 2) :
    Integrable
      (fun p : Vec d × Vec d =>
        ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2)
      ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) := by
  let i : Fin d := ⟨0, hd⟩
  rcases exists_support_subset_euclideanClosedBall_meanZeroTestFunction ψ with
    ⟨Rψ, _hRψ_nonneg, hψ_support₀⟩
  rcases exists_support_subset_euclideanClosedBall_meanZeroTestFunction φ with
    ⟨Rφ, _hRφ_nonneg, hφ_support₀⟩
  rcases exists_abs_meanZeroTestFunction_le ψ with
    ⟨Mψ, hMψ_nonneg, hψ_bound⟩
  rcases exists_abs_meanZeroTestFunction_le φ with
    ⟨Mφ, hMφ_nonneg, hφ_bound⟩
  let R := max 1 (max Rψ Rφ)
  have hR : 1 ≤ R := le_max_left _ _
  have hR_nonneg := zero_le_one.trans hR
  let C := Mψ * Mφ * (4 + Real.log (2 * R))
  let bound : Vec d × Vec d → ℝ := fun p =>
    C * (abkPairDifferenceBoxMajorant R p +
      abkPairDifferenceBoxSingularMajorant i R p)
  refine (show Integrable bound ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) by simpa [bound, C] using ((integrable_abkPairDifferenceBoxMajorant (d := d) R hR_nonneg).add (integrable_abkPairDifferenceBoxSingularMajorant i R hR_nonneg)).const_mul C).mono' (aestronglyMeasurable_abkCenteredRieszSlopeKernel_integrand_of_ne hd ψ φ hα_pos.ne') ?_
  filter_upwards [ae_sub_apply_ne_zero_volume_prod i] with p hp_coord
  simpa [bound, C] using
    norm_abkCenteredRieszSlopeKernel_integrand_le_pair_majorant
      i ψ φ hR hMψ_nonneg hMφ_nonneg hψ_bound hφ_bound
      (by intro x hx; exact (hψ_support₀ hx).trans ((le_max_left Rψ Rφ).trans (le_max_right 1 (max Rψ Rφ)))) (by intro x hx; exact (hφ_support₀ hx).trans ((le_max_right Rψ Rφ).trans (le_max_right 1 (max Rψ Rφ)))) hα_pos hα_le hp_coord

/-- For each fixed small positive `α`, the Riesz kernel integrand is integrable. -/
theorem integrable_abkRieszKernel_integrand_of_pos_le_half
    {d} (hd : 0 < d) (ψ φ : MeanZeroTestFunction d) {α : ℝ}
    (hα_pos : 0 < α) (hα_le : α ≤ 1 / 2) :
    Integrable
      (fun p : Vec d × Vec d => ψ p.1 * φ p.2 * abkRieszKernel α p.1 p.2)
      ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) := by
  refine (((integrable_abkCenteredRieszSlopeKernel_integrand_of_pos_le_half hd ψ φ hα_pos hα_le).const_mul α).add (integrable_abkKernelPairing_const_one ψ φ)).congr ?_
  filter_upwards with p
  simp [abkCenteredRieszSlopeKernel, abkRieszKernel]
  field_simp [hα_pos.ne']
  ring_nf

/-- The ABK reciprocal normalization times the centered Riesz difference pairing converges to
the logarithmic covariance pairing with the `M₀` prefactor. -/
theorem tendsto_abkMAlphaInv_mul_centeredRieszDifferencePairing
    {d} (hd : 0 < d) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) :
    Tendsto
      (fun α : ℝ =>
        abkMAlphaInv ζ α * abkCenteredRieszDifferencePairing ψ φ α)
      (𝓝[>] (0 : ℝ))
      (𝓝 (abkM0 ζ * abkLogCovariancePairing ψ φ)) := by
  rcases exists_integrable_bound_abkCenteredRieszSlopeKernel_integrand hd ψ φ with
    ⟨bound, hbound_int, hbound⟩
  exact tendsto_abkMAlphaInv_mul_centeredRieszDifferencePairing_of_dominated
    hd ζ ψ φ bound
    ((by filter_upwards [self_mem_nhdsWithin] with α hα; exact aestronglyMeasurable_abkCenteredRieszSlopeKernel_integrand_of_ne hd ψ φ hα.ne'))
    hbound hbound_int

end GaussianFields

end
