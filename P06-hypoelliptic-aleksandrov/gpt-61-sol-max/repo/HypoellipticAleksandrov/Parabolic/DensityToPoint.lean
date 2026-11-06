module

public import HypoellipticAleksandrov.Parabolic.Scaling
public import HypoellipticAleksandrov.Measure.TimeVelocity
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.ScalingMeasure
public import HypoellipticAleksandrov.Measure.TimeVelocity


open private HypoellipticAleksandrov.Parabolic.parabolicLinear_det_ne_zero from HypoellipticAleksandrov.Parabolic.ScalingMeasure


/-!
# Density-to-point relations for parabolic boxes

This file defines the transparent density-to-point relation used in the
parabolic Krylov--Safonov argument and proves its elementary monotonicity API.
The local sign, ellipticity, and supersolution hypotheses are imposed on the
open box itself, while continuity and `C²` regularity hold on a neighborhood of
its closed counterpart.
-/

@[expose] public section

open MeasureTheory Set


namespace HypoellipticAleksandrov.Parabolic

noncomputable section



variable {d : ℕ}



/-- Parabolic affine scaling sends the closed reference box into its translated counterpart. -/
theorem mapsTo_parabolicAffine_parabolicClosedBox  {vartheta r t₀ : ℝ}
    {v₀ : PDE.Vec d} (hr : 0 < r) :
    MapsTo (parabolicAffine t₀ v₀ r) (parabolicClosedBox vartheta 1 0 0)
      (parabolicClosedBox vartheta r t₀ v₀) := by
  intro z hz
  rcases hz with ⟨⟨hz₀, hz₁⟩, hzv⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · dsimp [parabolicAffine]
    nlinarith [sq_pos_of_pos hr]
  · dsimp [parabolicAffine]
    nlinarith [sq_pos_of_pos hr]
  · intro i

    dsimp [parabolicAffine]

    rw [add_sub_cancel_left, abs_mul, abs_of_pos hr]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (show |z.2 i| ≤ 1 by
        simpa only [Pi.zero_apply, sub_zero] using (hzv i)) hr.le

/-- Multiplying a scalar function by a constant scales the parabolic operator by that constant. -/
theorem parabolicOperator_const_smul  (B : CoefficientField d)
    (c : ℝ) (u : HypoellipticAleksandrov.Parabolic.ScalarField d) (z : TimeVelocity d) :
    parabolicOperator B (c • u) z = c * parabolicOperator B u z := by

  have htime : timeDerivative (c • u) z = c * timeDerivative u z := by
    unfold timeDerivative
    rw [fderiv_const_smul_field]
    rfl
  have hhessian : velocityHessian (c • u) z = c • velocityHessian u z := by
    have hsecond : fderiv ℝ (fderiv ℝ (c • u)) z =
        c • fderiv ℝ (fderiv ℝ u) z := by
      rw [(fderiv_const_smul_field c)]
      exact congrFun (fderiv_const_smul_field (f := fderiv ℝ u) c) z
    ext i j
    unfold velocityHessian
    rw [hsecond]
    rfl
  rw [parabolicOperator_apply, parabolicOperator_apply, htime, hhessian,
    HypoellipticAleksandrov.matrixContraction_smul_right]
  ring





/-- The determinant of the positive-radius parabolic linear part is nonzero. -/
alias parabolicLinear_det_ne_zero := _root_.HypoellipticAleksandrov.Parabolic.parabolicLinear_det_ne_zero


/-- Positive-radius parabolic affine scaling is surjective. -/
theorem parabolicAffine_surjective  {t₀ r : ℝ} {v₀ : PDE.Vec d}
    (hr : 0 < r) : Function.Surjective (parabolicAffine t₀ v₀ r) := by
  intro z
  refine ⟨((z.1 - t₀) / r ^ 2, r⁻¹ • (z.2 - v₀)), ?_⟩
  ext
  · dsimp [parabolicAffine]
    field_simp [hr.ne']
    ring
  · dsimp [parabolicAffine]
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
    ring

/-- The affine image of any set has the determinant factor of its parabolic linear part. -/
theorem volume_parabolicAffine_image  (t₀ : ℝ) (v₀ : PDE.Vec d) (r : ℝ)
    (s : HypoellipticAleksandrov.Parabolic.Region d) :
    (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) (parabolicAffine t₀ v₀ r '' s) =
      ENNReal.ofReal |LinearMap.det (parabolicLinear (d := d) r :
        TimeVelocity d →ₗ[ℝ] TimeVelocity d)| * volume s := by
  let q  := (t₀, v₀)
  have ha : parabolicAffine t₀ v₀ r = fun z ↦ q + parabolicLinear r z := by
    funext z
    ext <;> rfl
  calc
    (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) (parabolicAffine t₀ v₀ r '' s) =
        volume ((fun z ↦ q + z) '' (parabolicLinear r '' s)) := by
      rw [ha, Set.image_image]
    _ = volume ((fun z ↦ -q + z) ⁻¹' (parabolicLinear r '' s)) := by
      rw [Set.image_add_left]
    _ = volume (parabolicLinear r '' s) := by
      rw [measure_preimage_add]
    _ = ENNReal.ofReal |LinearMap.det (parabolicLinear (d := d) r :
        TimeVelocity d →ₗ[ℝ] TimeVelocity d)| * volume s := by
      simp_all

/-- The normalized and translated open boxes are exact affine images. -/
theorem parabolicAffine_image_parabolicBox  {vartheta r t₀ : ℝ}
    {v₀ : PDE.Vec d} (hr : 0 < r) :
    parabolicAffine t₀ v₀ r '' parabolicBox vartheta 1 0 0 =
      parabolicBox vartheta r t₀ v₀ := by
  calc
    parabolicAffine t₀ v₀ r '' parabolicBox vartheta 1 0 0 =
        parabolicAffine t₀ v₀ r ''
          (parabolicAffine t₀ v₀ r ⁻¹' parabolicBox vartheta r t₀ v₀) := by
      congr 1
      ext z
      exact (mem_parabolicAffine_preimage_parabolicBox_iff hr).symm
    _ = parabolicBox vartheta r t₀ v₀ :=
      Set.image_preimage_eq _ (parabolicAffine_surjective hr)

/-- Superlevel sets in a translated box are exact affine images after amplitude normalization. -/
theorem parabolicAffine_image_normalizedSuperlevel  {r t₀ eps : ℝ}
    {v₀ : PDE.Vec d} {u : HypoellipticAleksandrov.Parabolic.ScalarField d} (hr : 0 < r) (heps : 0 < eps) :
    parabolicAffine t₀ v₀ r ''
        (parabolicBox 1 1 0 0 ∩ {z | 1 ≤ eps⁻¹ • pullbackScalar u t₀ v₀ r z}) =
      parabolicBox 1 r t₀ v₀ ∩ {z | eps ≤ u z} := by
  let sharedTerm_e9cec68864 := ((parabolicBox 1 r t₀ v₀ ∩ {z | eps ≤ u z}))
  calc
    parabolicAffine t₀ v₀ r ''
        (parabolicBox 1 1 0 0 ∩ {z | 1 ≤ eps⁻¹ • pullbackScalar u t₀ v₀ r z}) =
      parabolicAffine t₀ v₀ r ''
        (parabolicAffine t₀ v₀ r ⁻¹'
          sharedTerm_e9cec68864) := by
      congr 1
      ext z
      constructor
      · rintro ⟨hzbox, hzlevel⟩
        refine ⟨(mem_parabolicAffine_preimage_parabolicBox_iff hr).mpr hzbox, ?_⟩
        have hlevel : 1 ≤ u (parabolicAffine t₀ v₀ r z) / eps := by
          simpa [div_eq_mul_inv, mul_comm, pullbackScalar_apply] using hzlevel
        simpa using (le_div_iff₀ heps).mp hlevel
      · rintro ⟨hzbox, hzlevel⟩
        refine ⟨(mem_parabolicAffine_preimage_parabolicBox_iff hr).mp hzbox, ?_⟩
        change eps ≤ u (parabolicAffine t₀ v₀ r z) at hzlevel
        have hlevel : 1 ≤ u (parabolicAffine t₀ v₀ r z) / eps :=
          (le_div_iff₀ heps).mpr (by simpa using hzlevel)
        simpa [div_eq_mul_inv, mul_comm, pullbackScalar_apply] using hlevel
    _ = sharedTerm_e9cec68864 :=
      Set.image_preimage_eq _ (parabolicAffine_surjective hr)

end

end HypoellipticAleksandrov.Parabolic
