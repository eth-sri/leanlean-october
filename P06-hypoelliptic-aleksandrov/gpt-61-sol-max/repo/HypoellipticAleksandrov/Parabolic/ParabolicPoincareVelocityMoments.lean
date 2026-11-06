module

public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareSlices
public import PDEFoundation.Sobolev.Mean
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Pi
import Aesop
import Batteries.Tactic.Alias



/-!
# Unit-velocity moment-affine projection

This module gives the canonical factor-three affine projection on the literal
unit velocity cube.  It proves its slice compatibility, affine reproduction,
subtraction algebra, and an extended-real `L^p` bound with no finiteness
premise on the input norm.

The first- and second-moment computations are kept private.  They are local to
the unit velocity cube and deliberately do not use the full parabolic-box
moment module.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators ENNReal

/-- The canonical factor-three affine moment projection on the literal unit
velocity cube. -/
def parabolicMorreyUnitVelocityAffineProjection {d : Nat}
    (g : PDE.Vec d -> Real) : PDE.Vec d -> Real :=
  fun v =>
    PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1) g +
      ∑ i : Fin d,
        (3 * PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
          (fun w => g w * w i)) * v i

private theorem unit_velocity_cube_measure (d : ℕ) :
    volume.restrict (velocityCube (0 : PDE.Vec d) 1) =
      Measure.pi (fun _ : Fin d => volume.restrict (Set.Ioo (-1 : ℝ) 1)) := by
  rw [velocityCube_eq_pi]
  simp only [Pi.zero_apply, zero_sub, zero_add]
  change (Measure.pi (fun _ : Fin d => volume)).restrict
    (Set.univ.pi fun _ : Fin d => Set.Ioo (-1 : ℝ) 1) = _
  rw [Measure.restrict_pi_pi]

private theorem unit_interval_integral_id :
    ∫ x in Set.Ioo (-1 : ℝ) 1, x = 0 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  norm_num [integral_id]

private theorem unit_interval_integral_sq :
    ∫ x in Set.Ioo (-1 : ℝ) 1, x * x = 2 / 3 := by
  rw [show (fun x : ℝ => x * x) = fun x => x ^ 2 by ext x; ring,
    ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  norm_num [integral_pow]

variable {d : ℕ}

private theorem unit_velocity_cube_integral_eval  (i : Fin d) :
    ∫ v in velocityCube (0 : PDE.Vec d) 1, v i = 0 := by
  rw [unit_velocity_cube_measure]
  let q : Fin d → ℝ → ℝ := fun k x => if k = i then x else 1
  have hq : (fun v : PDE.Vec d => v i) = fun v => ∏ k, q k (v k) := by
    ext v
    simp [q]
  rw [hq, integral_fintype_prod_eq_prod]
  simp only [q]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simpa [q] using unit_interval_integral_id

private theorem unit_velocity_cube_integral_eval_mul_eval  (i j : Fin d) :
    ∫ v in velocityCube (0 : PDE.Vec d) 1, v i * v j =
      if i = j then (2 : ℝ) ^ d / 3 else 0 := by
  classical
  rw [unit_velocity_cube_measure]
  by_cases hij : i = j
  · subst j
    let q : Fin d → ℝ → ℝ := fun k x => if k = i then x * x else 1
    have hq : (fun v : PDE.Vec d => v i * v i) = fun v => ∏ k, q k (v k) := by
      ext v
      simp [q]
    rw [hq, integral_fintype_prod_eq_prod]
    have hqint : (fun k : Fin d => ∫ x in Set.Ioo (-1 : ℝ) 1, q k x) =
        fun k => if k = i then 2 / 3 else 2 := by
      funext k
      by_cases hki : k = i
      · subst k
        simpa [q] using unit_interval_integral_sq
      · simp [q, hki]
        norm_num
    rw [hqint, if_pos rfl]
    have hfactor : (fun k : Fin d => if k = i then (2 / 3 : ℝ) else 2) =
        fun k => 2 * (if k = i then (1 / 3 : ℝ) else 1) := by
      funext k
      by_cases hki : k = i
      · simp [hki]
        norm_num
      · simp [hki]
    rw [hfactor, Finset.prod_mul_distrib, Finset.prod_const, Fintype.prod_ite_eq']
    simp only [Finset.card_univ, Fintype.card_fin]
    ring
  · let q : Fin d → ℝ → ℝ := fun k x =>
      if k = i then x else if k = j then x else 1
    have hq : (fun v : PDE.Vec d => v i * v j) = fun v => ∏ k, q k (v k) := by
      ext v
      calc
        v i * v j = q i (v i) * q j (v j) := by simp [q]
        _ = q i (v i) * (q j (v j) *
            ∏ k ∈ (Finset.univ.erase i).erase j, q k (v k)) := by
          congr 1
          have hprod : ∏ k ∈ (Finset.univ.erase i).erase j, q k (v k) = 1 := by
            apply Finset.prod_eq_one
            intro k hk
            rcases Finset.mem_erase.mp hk with ⟨hkj, hki_mem⟩
            exact by simp [q, hkj, (Finset.mem_erase.mp hki_mem).1]
          rw [hprod, mul_one]
        _ = ∏ k, q k (v k) := by
          rw [Finset.mul_prod_erase (Finset.univ.erase i) (fun k => q k (v k))]
          · rw [Finset.mul_prod_erase Finset.univ (fun k => q k (v k))]
            exact Finset.mem_univ _
          · aesop
    rw [hq, integral_fintype_prod_eq_prod]
    rw [if_neg hij]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa [q, hij] using unit_interval_integral_id

private theorem unit_velocity_average_one (d : ℕ) :
    PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
      (fun _ : PDE.Vec d => (1 )) = 1 := by
  rw [PDE.integralAverage, MeasureTheory.integral_const,
    Measure.real, Measure.restrict_apply_univ,
    volume_velocityCube_toReal (v₀ := (0 : PDE.Vec d)) (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [smul_eq_mul]
  field_simp

private theorem unit_velocity_average_eval {d : ℕ} (i : Fin d) :
    PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
      (fun v : PDE.Vec d => v i) = 0 := by
  rw [PDE.integralAverage, unit_velocity_cube_integral_eval]
  ring_nf

/-- Every velocity coordinate has zero normalized average on the literal unit velocity cube. -/
alias parabolicMorreyUnitVelocityAverage_eval := _root_.HypoellipticAleksandrov.Parabolic.unit_velocity_average_eval


variable {d : ℕ}

private theorem unit_velocity_average_eval_mul_eval  (i j : Fin d) :
    PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
      (fun v : PDE.Vec d => v i * v j) =
      if i = j then (1 / 3 : ℝ) else 0 := by
  rw [PDE.integralAverage, unit_velocity_cube_integral_eval_mul_eval,
    volume_velocityCube_toReal (v₀ := (0 : PDE.Vec d)) (by norm_num : (0 : ℝ) ≤ 1)]
  by_cases hij : i = j
  · simp [hij]
    field_simp
  · simp [hij]

private theorem continuous_integrable_unit_velocity_cube
    {f : PDE.Vec d → ℝ} (hf : Continuous f) :
    Integrable f (volume.restrict (velocityCube (0 ) 1)) := (hf.continuousOn.integrableOn_compact (isCompact_velocityClosedCube (0 : PDE.Vec d) 1)).mono_set ((fun ⦃v⦄ => id fun hv => id fun i => LT.lt.le (hv i)))

section
variable (f g : PDE.Vec d → ℝ) (hf : Integrable f (volume.restrict (velocityCube (0 ) 1))) (hg : Integrable g (volume.restrict (velocityCube (0 ) 1)))

include hf hg
private theorem unit_velocity_average_add   :
    PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1) (f + g) =
      PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1) f +
        PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1) g := by
  unfold PDE.integralAverage
  simp only [Pi.add_apply]
  rw [integral_add hf hg]
  ring

private theorem unit_velocity_average_sub   :
    PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1) (f - g) =
      PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1) f -
        PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1) g := by
  unfold PDE.integralAverage
  simp only [Pi.sub_apply]
  rw [integral_sub hf hg]
  ring
end


private theorem unit_velocity_average_smul  (c : ℝ) (f : PDE.Vec d → ℝ) :
    PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1) (c • f) =
      c • PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1) f := by
  let sharedTerm_32a53d706b := ((volume (velocityCube (0 : PDE.Vec d) 1)).toReal⁻¹)
  unfold PDE.integralAverage
  change sharedTerm_32a53d706b *
      ∫ v in velocityCube (0 : PDE.Vec d) 1, c • f v = c •
        (sharedTerm_32a53d706b *
          ∫ v in velocityCube (0 : PDE.Vec d) 1, f v)
  rw [integral_smul]
  simp only [smul_eq_mul]
  ring

private theorem unit_velocity_average_finset_sum {d ι : ℕ} (s : Finset (Fin ι))
    (f : Fin ι → PDE.Vec d → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i)
      (volume.restrict (velocityCube (0 ) 1))) :
    PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
        (fun v => ∑ i ∈ s, f i v) =
      ∑ i ∈ s, PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1) (f i) := by
  unfold PDE.integralAverage
  rw [integral_finset_sum s hf, Finset.mul_sum]

variable {d : ℕ} (a : ℝ) (b : Fin d → ℝ)

private theorem unit_velocity_average_affine  :
    PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
        (fun v : PDE.Vec d => a + ∑ i : Fin d, b i * v i) = a := by
  let sharedTerm_fdaa66b061 := ((velocityCube (0 : PDE.Vec d) 1))
  let f : Fin d → PDE.Vec d → ℝ := fun i v => b i * v i

  have hf : ∀ i : Fin d, Integrable (f i)
      (volume.restrict sharedTerm_fdaa66b061) := by
    intro i
    apply continuous_integrable_unit_velocity_cube
    fun_prop

  rw [show (fun v : PDE.Vec d => a + ∑ i : Fin d, b i * v i) =
      (fun _ => a) + fun v => ∑ i : Fin d, f i v by
        ext v
        rfl
    , unit_velocity_average_add _ _ (by
        apply continuous_integrable_unit_velocity_cube
        fun_prop) (integrable_finset_sum _ fun i _ => hf i),
      unit_velocity_average_finset_sum Finset.univ f (fun i _ => hf i)]
  have hconst_avg : PDE.integralAverage sharedTerm_fdaa66b061
      (fun _ : PDE.Vec d => a) = a := by
    rw [show (fun _ : PDE.Vec d => a) = a • (fun _ => (1 : ℝ)) by
      ext v
      simp
      , unit_velocity_average_smul, unit_velocity_average_one]
    simp
  rw [hconst_avg]
  simp_rw [show f = fun i => b i • (fun v : PDE.Vec d => v i) by
    funext i v
    rfl]
  simp_rw [unit_velocity_average_smul, unit_velocity_average_eval]
  simp only [smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero]

private theorem unit_velocity_affine_coefficient
    (j : Fin d) :
    3 * PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
        (fun v : PDE.Vec d => (a + ∑ i : Fin d, b i * v i) * v j) = b j := by
  let sharedTerm_b8e6763934 := ((velocityCube (0 : PDE.Vec d) 1))
  let g : Fin d → PDE.Vec d → ℝ := fun i v => b i * (v i * v j)

  have hg : ∀ i : Fin d, Integrable (g i)
      (volume.restrict sharedTerm_b8e6763934) := by
    intro i
    apply continuous_integrable_unit_velocity_cube
    fun_prop

  rw [show (fun v : PDE.Vec d => (a + ∑ i : Fin d, b i * v i) * v j) =
      (fun v => a * v j) + fun v => ∑ i : Fin d, g i v by
        ext v
        simp only [Pi.add_apply, g]
        rw [add_mul, Finset.sum_mul]
        ring_nf
    , unit_velocity_average_add _ _ (by
        apply continuous_integrable_unit_velocity_cube
        fun_prop) (integrable_finset_sum _ fun i _ => hg i),
      unit_velocity_average_finset_sum Finset.univ g (fun i _ => hg i)]
  have hfirst_avg : PDE.integralAverage sharedTerm_b8e6763934
      (fun v : PDE.Vec d => a * v j) = 0 := by
    rw [show (fun v : PDE.Vec d => a * v j) =
        a • (fun v : PDE.Vec d => v j) by
          ext v
          rfl
      , unit_velocity_average_smul, unit_velocity_average_eval]
    simp
  rw [hfirst_avg]
  simp_rw [show g = fun i => b i • (fun v : PDE.Vec d => v i * v j) by
    funext i v
    rfl]
  simp_rw [unit_velocity_average_smul, unit_velocity_average_eval_mul_eval]
  simp only [smul_eq_mul, zero_add]
  have hnormalization : 3 * (1 / 3 : ℝ) = 1 := by norm_num
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ _)]
  · simp only [ite_true]
    calc
      _ = b j * (3 * (1 / 3)) := by ring
      _ = b j := by rw [hnormalization, mul_one]
  · intro i _ hij
    simp [hij]

variable {d : Nat}

/-- The time-slice projection is exactly the shared velocity-only projection
applied to that slice. -/
theorem parabolicMorreyUnitSpatialAffineProjection_eq_velocityAffineProjection
     (u : TimeVelocity d -> Real) (t : Real) :
    (fun v : PDE.Vec d => parabolicMorreyUnitSpatialAffineProjection u (t, v)) =
      parabolicMorreyUnitVelocityAffineProjection (fun v => u (t, v)) := by
  funext v
  simp only [parabolicMorreyUnitSpatialAffineProjection,
    parabolicMorreyUnitVelocityAffineProjection,
    parabolicMorreyUnitVelocityAverage, parabolicMorreyUnitVelocityCoeffAt,
    PDE.integralAverage]
  ring_nf

/-- The unit-velocity moment projection exactly reproduces every affine scalar
field in the velocity variables. -/
theorem parabolicMorreyUnitVelocityAffineProjection_reproduces_affine
     (a : Real) (b : Fin d -> Real) :
    parabolicMorreyUnitVelocityAffineProjection
        (fun v : PDE.Vec d => a + ∑ i : Fin d, b i * v i) =
      fun v => a + ∑ i : Fin d, b i * v i := by
  funext v
  rw [parabolicMorreyUnitVelocityAffineProjection, unit_velocity_average_affine]
  simp_rw [unit_velocity_affine_coefficient]

/-- The unit-velocity moment projection commutes with subtraction when the
value and all first moments of both inputs are integrable. -/
theorem parabolicMorreyUnitVelocityAffineProjection_sub
     (f g : PDE.Vec d -> Real)
    (hf : Integrable f (volume.restrict (velocityCube (0 ) 1)))
    (hg : Integrable g (volume.restrict (velocityCube (0 ) 1)))
    (hfv : ∀ i : Fin d, Integrable (fun v => f v * v i)
      (volume.restrict (velocityCube (0 ) 1)))
    (hgv : ∀ i : Fin d, Integrable (fun v => g v * v i)
      (volume.restrict (velocityCube (0 ) 1))) :
    parabolicMorreyUnitVelocityAffineProjection (f - g) =
      parabolicMorreyUnitVelocityAffineProjection f -
        parabolicMorreyUnitVelocityAffineProjection g := by
  funext v
  have hmoment : ∀ i : Fin d,
      PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
          (fun w => (f - g) w * w i) =
        PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
          (fun w => f w * w i) -
          PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
          (fun w => g w * w i) := by
    intro i
    rw [show (fun w : PDE.Vec d => (f - g) w * w i) =
        (fun w => f w * w i) - fun w => g w * w i by
          ext w
          simp only [Pi.sub_apply]
          ring
      , unit_velocity_average_sub _ _ (hfv i) (hgv i)]
  unfold parabolicMorreyUnitVelocityAffineProjection
  rw [unit_velocity_average_sub _ _ hf hg]
  simp_rw [hmoment]
  simp only [Pi.sub_apply, sub_mul, mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

variable (d : ℕ)

private theorem unit_velocity_cube_measure_pos  :
    0 < volume (velocityCube (0 : PDE.Vec d) 1) := by
  apply (ENNReal.toReal_pos_iff.mp ?_).1
  simpa only [volume_velocityCube_toReal (v₀ := (0 : PDE.Vec d)) (by norm_num : (0 : ℝ) ≤ 1),
    mul_one] using (pow_pos (by norm_num : (0 : ℝ) < 2) d)

private theorem unit_velocity_cube_measure_lt_top  :
    volume (velocityCube (0 : PDE.Vec d) 1) < ∞ := by

  calc
    volume (velocityCube (0 : PDE.Vec d) 1) ≤
        volume (velocityClosedCube (0 : PDE.Vec d) 1) := measure_mono (by
            intro v hv
            change ∀ i : Fin d, |v i - (0 : PDE.Vec d) i| < 1 at hv
            change ∀ i : Fin d, |v i - (0 : PDE.Vec d) i| ≤ 1
            intro i
            exact (hv i).le)
    _ < ∞ := (isCompact_velocityClosedCube (0 : PDE.Vec d) 1).measure_lt_top

variable {d : Nat} (g : PDE.Vec d -> Real) (hg : AEStronglyMeasurable g (volume.restrict (velocityCube (0 ) 1)))

include hg
private theorem eLpMeanNormOn_unit_velocity_affine_projection_le
     :
    PDE.eLpMeanNormOn (velocityCube (0 : PDE.Vec d) 1) (parabolicExponent d)
      (parabolicMorreyUnitVelocityAffineProjection g) <=
      ENNReal.ofReal (1 + 3 * (d : Real)) *
        PDE.eLpMeanNormOn (velocityCube (0 : PDE.Vec d) 1)
          (parabolicExponent d) g := by
  let V  := velocityCube (0 : PDE.Vec d) 1
  let μ  := PDE.normalizedVolumeOn V
  let p  := parabolicExponent d


  letI : IsProbabilityMeasure μ :=
    PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top (show _ by
        exact unit_velocity_cube_measure_pos d) (show _ by
        exact unit_velocity_cube_measure_lt_top d)
  have hp : (1 : ℝ≥0∞) ≤ p := by
    simpa only [p, parabolicExponent] using
      (le_add_of_nonneg_left (show (0 : ℝ≥0∞) ≤ d from bot_le))

  have hgm : AEStronglyMeasurable g μ := by
    change AEStronglyMeasurable g
      ((volume V)⁻¹ • volume.restrict V)
    simpa only [μ] using hg.smul_measure ((volume V)⁻¹)
  have hmem : ∀ᵐ v ∂μ, v ∈ V := by
    change ∀ᵐ v ∂((volume V)⁻¹ • volume.restrict V), v ∈ V
    exact Measure.ae_smul_measure
      ((ae_restrict_mem (measurableSet_velocityCube 0 1)))
      ((volume V)⁻¹)
  have hmoment : ∀ (h : PDE.Vec d → ℝ), AEStronglyMeasurable h μ →
      ‖PDE.integralAverage V h‖ₑ ≤ eLpNorm h p μ := by
    intro h hh
    rw [← PDE.integral_normalizedVolumeOn_eq_integralAverage V h]
    calc
      ‖∫ v, h v ∂μ‖ₑ ≤ ∫⁻ v, ‖h v‖ₑ ∂μ := enorm_integral_le_lintegral_enorm h
      _ = eLpNorm h 1 μ := by
        symm
        exact eLpNorm_one_eq_lintegral_enorm hh
      _ ≤ eLpNorm h p μ := eLpNorm_le_eLpNorm_of_exponent_le hp
  have hcoordinate : ∀ i : Fin d,
      eLpNorm (fun v => g v * v i) p μ ≤ eLpNorm g p μ := by
    intro i
    apply eLpNorm_mono_ae (hgm.mul (continuous_apply i).aestronglyMeasurable)
    filter_upwards [hmem] with v hv
    have hvi : |v i| ≤ 1 := by
      change ∀ j : Fin d, |v j - (0 : PDE.Vec d) j| < 1 at hv
      simpa using (hv i).le
    calc
      ‖g v * v i‖ = |g v| * |v i| := by
        rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |g v| := mul_le_of_le_one_right (abs_nonneg _) hvi
      _ = ‖g v‖ := (Real.norm_eq_abs _).symm
  have hweighted_measurable : ∀ i : Fin d,
      AEStronglyMeasurable (fun v => g v * v i) μ := by
    intro i
    exact hgm.mul (continuous_apply i).aestronglyMeasurable
  have hconstant : ∀ c : ℝ, eLpNorm (fun _ : PDE.Vec d => c) p μ = ‖c‖ₑ := by
    intro c
    rw [eLpNorm_const c (show _ by
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) (IsProbabilityMeasure.ne_zero μ), measure_univ,
      ENNReal.one_rpow, mul_one]



  have hfactor : ENNReal.ofReal (1 + 3 * (d : Real)) =
      1 + 3 * (d : ℝ≥0∞) := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity),
      ENNReal.ofReal_mul (by norm_num)]
    norm_num
  change eLpNorm (parabolicMorreyUnitVelocityAffineProjection g) p μ ≤
    ENNReal.ofReal (1 + 3 * (d : Real)) * eLpNorm g p μ
  change eLpNorm (fun v => PDE.integralAverage V g + ∑ i : Fin d,
      (3 * PDE.integralAverage V (fun w => g w * w i)) * v i) p μ ≤ _



  calc
    eLpNorm (fun v => PDE.integralAverage V g + ∑ i : Fin d,
        (3 * PDE.integralAverage V (fun w => g w * w i)) * v i) p μ ≤
        eLpNorm (fun _ : PDE.Vec d => PDE.integralAverage V g) p μ +
          eLpNorm (fun v => ∑ i : Fin d,
            (3 * PDE.integralAverage V (fun w => g w * w i)) * v i) p μ := (eLpNorm_add_le hp)
    _ ≤ eLpNorm (fun _ : PDE.Vec d => PDE.integralAverage V g) p μ +
          ∑ i : Fin d, eLpNorm (fun v =>
            (3 * PDE.integralAverage V (fun w => g w * w i)) * v i) p μ := add_le_add_right (show _ by
                rw [← Finset.sum_fn]
                exact eLpNorm_sum_le hp) _
    _ ≤ eLpNorm g p μ + ∑ i : Fin d, 3 * eLpNorm g p μ := add_le_add (show _ by
        rw [hconstant]
        exact hmoment g hgm) (by
            exact Finset.sum_le_sum fun i _ => (show ∀ i : Fin d,
              eLpNorm (fun v =>
                (3 * PDE.integralAverage V (fun w => g w * w i)) * v i) p μ ≤
                3 * eLpNorm g p μ by
                intro i
                calc
                  eLpNorm (fun v =>
                      (3 * PDE.integralAverage V (fun w => g w * w i)) * v i) p μ ≤
                      eLpNorm (fun _ : PDE.Vec d =>
                        3 * PDE.integralAverage V (fun w => g w * w i)) p μ := by
                    let sharedTerm_9b560fabfa := (3 * PDE.integralAverage V (fun w => g w * w i))
                    apply eLpNorm_mono_ae
                      (aestronglyMeasurable_const.mul (continuous_apply i).aestronglyMeasurable)
                    filter_upwards [hmem] with v hv
                    have hvi : |v i| ≤ 1 := by
                      change ∀ j : Fin d, |v j - (0 : PDE.Vec d) j| < 1 at hv
                      simpa using (hv i).le
                    calc
                      ‖(sharedTerm_9b560fabfa) * v i‖ =
                          |sharedTerm_9b560fabfa| * |v i| := by
                        rw [Real.norm_eq_abs, abs_mul]
                      _ ≤ |sharedTerm_9b560fabfa| :=
                        mul_le_of_le_one_right (abs_nonneg _) hvi
                      _ = ‖sharedTerm_9b560fabfa‖ :=
                        (Real.norm_eq_abs _).symm
                  _ = ‖3 * PDE.integralAverage V (fun w => g w * w i)‖ₑ := hconstant _
                  _ = 3 * ‖PDE.integralAverage V (fun w => g w * w i)‖ₑ := by
                    rw [enorm_mul]
                    have hthree : ‖(3 : ℝ)‖ₑ = (3 : ℝ≥0∞) := Real.enorm_natCast 3
                    rw [hthree]
                  _ ≤ 3 * eLpNorm (fun v => g v * v i) p μ := by
                    gcongr
                    exact hmoment _ (hweighted_measurable i)
                  _ ≤ 3 * eLpNorm g p μ := by
                    gcongr
                    exact hcoordinate i) i)
    _ = (1 + 3 * (d : ℝ≥0∞)) * eLpNorm g p μ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [add_mul, one_mul, ← mul_assoc, mul_comm (d : ℝ≥0∞) 3, mul_assoc]
    _ = ENNReal.ofReal (1 + 3 * (d : Real)) * eLpNorm g p μ := by
      rw [hfactor]

/-- The canonical unit-velocity moment projection has the exact finite-free
extended-real norm bound needed by the spatial and temporal Poincare layers. -/
theorem eLpNormOn_parabolicMorreyUnitVelocityAffineProjection_le
     :
    PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1) (parabolicExponent d)
        (parabolicMorreyUnitVelocityAffineProjection g) <=
      ENNReal.ofReal (1 + 3 * (d : Real)) *
        PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
          (parabolicExponent d) g := by
  let sharedTerm_1848914a28 := (ENNReal.ofReal (1 + 3 * (d : Real)))
  let V  := velocityCube (0 : PDE.Vec d) 1
  let p  := parabolicExponent d
  have hVpos : 0 < volume V := by
    exact unit_velocity_cube_measure_pos d
  have hVtop : volume V < ∞ := by
    exact unit_velocity_cube_measure_lt_top d
  have hmean := eLpMeanNormOn_unit_velocity_affine_projection_le g hg
  change PDE.eLpNormOn V p (parabolicMorreyUnitVelocityAffineProjection g) ≤
    sharedTerm_1848914a28 * PDE.eLpNormOn V p g
  rw [PDE.eLpNormOn_eq_volume_rpow_mul_eLpMeanNormOn hVpos hVtop,
    PDE.eLpNormOn_eq_volume_rpow_mul_eLpMeanNormOn hVpos hVtop]
  calc
    volume V ^ (1 / p).toReal *
        PDE.eLpMeanNormOn V p (parabolicMorreyUnitVelocityAffineProjection g) ≤
        volume V ^ (1 / p).toReal *
          (sharedTerm_1848914a28 * PDE.eLpMeanNormOn V p g) := by
      gcongr
    _ = sharedTerm_1848914a28 *
        (volume V ^ (1 / p).toReal * PDE.eLpMeanNormOn V p g) := by
      ac_rfl

end HypoellipticAleksandrov.Parabolic
