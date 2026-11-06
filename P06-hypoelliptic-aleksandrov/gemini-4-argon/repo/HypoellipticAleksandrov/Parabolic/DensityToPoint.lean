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

/- A relative superlevel-set bound on the unit parabolic box forces a lower
bound on its closed terminal half-cube. -/
theorem mapsTo_parabolicAffine_parabolicClosedBox {d vartheta r t₀}
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
    have hi := hzv i
    dsimp [parabolicAffine]
    have hi' : |z.2 i| ≤ 1 := by
      simpa only [Pi.zero_apply, sub_zero] using hi
    rw [add_sub_cancel_left, abs_mul, abs_of_pos hr]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hi' hr.le

/- Multiplying a scalar function by a constant scales the parabolic operator by that constant. -/
theorem parabolicOperator_const_smul {d : ℕ} (B : CoefficientField d)
    (c : ℝ) (u : TimeVelocity d → ℝ) (z : TimeVelocity d) :
    parabolicOperator B (c • u) z = c * parabolicOperator B u z := by
  have hfirst : fderiv ℝ (c • u) = c • fderiv ℝ u :=
    fderiv_const_smul_field c
  have htime : timeDerivative (c • u) z = c * timeDerivative u z := by
    unfold timeDerivative
    rw [fderiv_const_smul_field]
    rfl
  have hhessian : velocityHessian (c • u) z = c • velocityHessian u z := by
    have hsecond : fderiv ℝ (fderiv ℝ (c • u)) z =
        c • fderiv ℝ (fderiv ℝ u) z := by
      rw [hfirst]
      exact congrFun (fderiv_const_smul_field (f := fderiv ℝ u) c) z
    ext i j
    unfold velocityHessian
    rw [hsecond]
    rfl
  rw [parabolicOperator_apply, parabolicOperator_apply, htime, hhessian,
    HypoellipticAleksandrov.matrixContraction_smul_right]
  ring

/- A positive constant multiple of a local zero-source supersolution is again one. -/
theorem parabolicLinear_det_ne_zero {d r} (hr : 0 < r) :
    LinearMap.det (parabolicLinear (d := d) r : TimeVelocity d →ₗ[ℝ] TimeVelocity d) ≠ 0 := by
  intro hdet
  have hker : LinearMap.ker (parabolicLinear (d := d) r : TimeVelocity d →ₗ[ℝ]
      TimeVelocity d) ≠ ⊥ :=
    (LinearMap.det_eq_zero_iff_ker_ne_bot).mp hdet
  have _h_inl_10 : Function.Injective (parabolicLinear (d := d) r) := by
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

    /- The determinant of the positive-radius parabolic linear part is nonzero. -/
  exact hker (LinearMap.ker_eq_bot_of_injective _h_inl_10)

/- Positive-radius parabolic affine scaling is surjective. -/
theorem parabolicAffine_surjective {d t₀ r} {v₀ : PDE.Vec d}
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

/- The affine image of any set has the determinant factor of its parabolic linear part. -/
theorem volume_parabolicAffine_image {d } (t₀ : ℝ) (v₀ : PDE.Vec d) (r : ℝ)
    (s : Set (TimeVelocity d)) :
    (volume : Measure (TimeVelocity d)) (parabolicAffine t₀ v₀ r '' s) =
      ENNReal.ofReal |LinearMap.det (parabolicLinear (d := d) r :
        TimeVelocity d →ₗ[ℝ] TimeVelocity d)| * volume s := by
  let q : TimeVelocity d := (t₀, v₀)
  have ha : parabolicAffine t₀ v₀ r = fun z ↦ q + parabolicLinear r z := by
    funext z
    ext <;> simp [q, parabolicAffine, parabolicLinear]
  calc
    (volume : Measure (TimeVelocity d)) (parabolicAffine t₀ v₀ r '' s) =
        volume ((fun z ↦ q + z) '' (parabolicLinear r '' s)) := by
      rw [ha, Set.image_image]
    _ = volume ((fun z ↦ -q + z) ⁻¹' (parabolicLinear r '' s)) := by
      rw [Set.image_add_left]
    _ = volume (parabolicLinear r '' s) := by
      rw [measure_preimage_add]
    _ = ENNReal.ofReal |LinearMap.det (parabolicLinear (d := d) r :
        TimeVelocity d →ₗ[ℝ] TimeVelocity d)| * volume s := by
      exact Measure.addHaar_image_continuousLinearMap volume (parabolicLinear r) s

/- The normalized and translated open boxes are exact affine images. -/
theorem parabolicAffine_image_parabolicBox {d vartheta r t₀}
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

/- Superlevel sets in a translated box are exact affine images after amplitude normalization. -/
end

end HypoellipticAleksandrov.Parabolic
