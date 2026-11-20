module

public import HypoellipticAleksandrov.Parabolic.Scaling
public import HypoellipticAleksandrov.Measure.TimeVelocity

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
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

section
variable {d : ℕ} {vartheta r t₀ : ℝ} {lam Lam beta g : ℝ} {v₀ : PDE.Vec d}
    (hr : 0 < r) (U : Set (TimeVelocity d))
    (B : CoefficientField d) (c : ℝ) (u : TimeVelocity d → ℝ)

include hr in
/-- Parabolic affine scaling sends the closed reference box into its translated counterpart. -/
theorem mapsTo_parabolicAffine_parabolicClosedBox :
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
    have hi := hzv i
    dsimp [parabolicAffine]
    have hi' : |z.2 i| ≤ 1 := by
      simpa using hi
    rw [add_sub_cancel_left, abs_mul, abs_of_pos hr]
    simpa using mul_le_mul_of_nonneg_left hi' hr.le

/-- Multiplying a scalar function by a constant scales the parabolic operator by that constant. -/
theorem parabolicOperator_const_smul (z : TimeVelocity d) :
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

/-- The linear part of positive-radius parabolic scaling is injective. -/
theorem parabolicLinear_injective {r : ℝ} (hr : 0 < r) :
    Function.Injective (parabolicLinear (d := d) r) := by
  intro z w hzw
  have htime := congrArg Prod.fst hzw
  have hvelocity := congrArg Prod.snd hzw
  rw [parabolicLinear_apply, parabolicLinear_apply] at htime hvelocity
  apply Prod.ext
  · nlinarith [sq_pos_of_pos hr]
  · ext i
    have hi := congrFun hvelocity i
    simp only [Pi.smul_apply, smul_eq_mul] at hi
    nlinarith

/-- The determinant of the positive-radius parabolic linear part is nonzero. -/
theorem parabolicLinear_det_ne_zero {r : ℝ} (hr : 0 < r) :
    LinearMap.det (parabolicLinear (d := d) r : TimeVelocity d →ₗ[ℝ] TimeVelocity d) ≠ 0 := by
  intro hdet
  exact ((LinearMap.det_eq_zero_iff_ker_ne_bot).mp hdet) (LinearMap.ker_eq_bot_of_injective (parabolicLinear_injective hr))

/-- Positive-radius parabolic affine scaling is surjective. -/
theorem parabolicAffine_surjective {t₀ r : ℝ} {v₀ : PDE.Vec d}
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
theorem volume_parabolicAffine_image (t₀ : ℝ) (v₀ : PDE.Vec d) (r : ℝ)
    (s : Set (TimeVelocity d)) :
    (volume : Measure (TimeVelocity d)) (parabolicAffine t₀ v₀ r '' s) =
      ENNReal.ofReal |LinearMap.det (parabolicLinear (d := d) r :
        TimeVelocity d →ₗ[ℝ] TimeVelocity d)| * volume s := by
  let q := (t₀, v₀)
  have ha : parabolicAffine t₀ v₀ r = fun z ↦ q + parabolicLinear r z := by
    funext z
    ext <;> simp [q, parabolicAffine, parabolicLinear]
  calc
    volume (parabolicAffine t₀ v₀ r '' s) =
        volume ((fun z ↦ q + z) '' (parabolicLinear r '' s)) := by
      rw [ha, Set.image_image]
    _ = volume ((fun z ↦ -q + z) ⁻¹' (parabolicLinear r '' s)) := by
      rw [Set.image_add_left]
    _ = volume (parabolicLinear r '' s) := by
      rw [measure_preimage_add]
    _ = ENNReal.ofReal |LinearMap.det (parabolicLinear (d := d) r :
        TimeVelocity d →ₗ[ℝ] TimeVelocity d)| * volume s := Measure.addHaar_image_continuousLinearMap volume (parabolicLinear r) s

include hr in
/-- The normalized and translated open boxes are exact affine images. -/
theorem parabolicAffine_image_parabolicBox :
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

end

/-- Superlevel sets in a translated box are exact affine images after amplitude normalization. -/
theorem parabolicAffine_image_normalizedSuperlevel {d : ℕ} {r t₀ eps : ℝ}
    {v₀ : PDE.Vec d} {u : TimeVelocity d → ℝ} (hr : 0 < r) (heps : 0 < eps) :
    parabolicAffine t₀ v₀ r ''
        (parabolicBox 1 1 0 0 ∩ {z | 1 ≤ eps⁻¹ • pullbackScalar u t₀ v₀ r z}) =
      parabolicBox 1 r t₀ v₀ ∩ {z | eps ≤ u z} := by
  calc
    parabolicAffine t₀ v₀ r ''
        (parabolicBox 1 1 0 0 ∩ {z | 1 ≤ eps⁻¹ • pullbackScalar u t₀ v₀ r z}) =
      parabolicAffine t₀ v₀ r ''
        (parabolicAffine t₀ v₀ r ⁻¹'
          (parabolicBox 1 r t₀ v₀ ∩ {z | eps ≤ u z})) := by
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
        have hlevel : 1 ≤ u (parabolicAffine t₀ v₀ r z) / eps :=
          (le_div_iff₀ heps).mpr (by simpa using hzlevel)
        simpa [div_eq_mul_inv, mul_comm, pullbackScalar_apply] using hlevel
    _ = parabolicBox 1 r t₀ v₀ ∩ {z | eps ≤ u z} :=
      Set.image_preimage_eq _ (parabolicAffine_surjective hr)

end

end HypoellipticAleksandrov.Parabolic
