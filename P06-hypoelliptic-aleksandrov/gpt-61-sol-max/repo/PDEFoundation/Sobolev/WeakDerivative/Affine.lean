module

public import PDEFoundation.Measure.AffineVolume
public import PDEFoundation.Sobolev.WeakDerivative
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Affine transport of weak first derivatives

Translation is exact: precomposing values and gradients by `x ↦ x - z`
transports a weak derivative from `U` to `z + U`.
-/

 public section

open scoped Pointwise

namespace PDE

namespace HasWeakPartialDerivOn

/-- Translate a weak partial derivative from `U` to `z + U`. -/
theorem translate {d : ℕ} {U : Set (Vec d)} {i : Fin d}
    {u gi : Vec d → ℝ} (h : HasWeakPartialDerivOn U i u gi)
    (z : Vec d) :
    HasWeakPartialDerivOn (translateSet z U) i
      (fun x => u (x - z)) (fun x => gi (x - z)) := by
  intro φ hφSmooth hφCompact hφSubset
  let V  := translateSet z U
  let ψ  := fun x => φ (x + z)



  have hWeak := h ψ (by
      simpa [ψ] using!
        hφSmooth.comp (contDiff_id.add contDiff_const)) (by
      show HasCompactSupport (φ ∘ Homeomorph.addRight z)
      simpa [ψ, Function.comp] using
        hφCompact.comp_homeomorph (Homeomorph.addRight z)) (by
            intro x hx

            have hxV  := hφSubset (by
                rw [show ψ = φ ∘ Homeomorph.addRight z by rfl,
                  tsupport_comp_eq_preimage φ (Homeomorph.addRight z)] at hx
                exact hx)
            simpa [V, mem_translateSet_iff_sub_mem, sub_eq_add_neg,
              add_assoc] using hxV)


  have hChangeRight :
      ∫ x in U, gi x * φ (x + z) ∂MeasureTheory.volume =
        ∫ x in V, gi (x - z) * φ x ∂MeasureTheory.volume := by
    simpa [V, sub_eq_add_neg, add_assoc] using
      (setIntegral_comp_addRight_translateSet  z U
        (fun x => gi (x - z) * φ x))
  calc
    ∫ x in V, u (x - z) * (fderiv ℝ φ x) (basisVec i)
        ∂MeasureTheory.volume =
        ∫ x in U, u x * (fderiv ℝ φ (x + z)) (basisVec i)
          ∂MeasureTheory.volume := (by
              symm
              simpa [V, sub_eq_add_neg, add_assoc] using
                (setIntegral_comp_addRight_translateSet  z U
                  (fun x => u (x - z) * (fderiv ℝ φ x) (basisVec i))))
    _ = -∫ x in U, gi x * φ (x + z)
        ∂MeasureTheory.volume := (by
            have hfun :
                (fun x => u x * (fderiv ℝ φ (x + z)) (basisVec i)) =
                  fun x => u x * (fderiv ℝ ψ x) (basisVec i) := by
              funext x
              have hderiv :
                  fderiv ℝ (fun y  => φ (y + z)) x =
                    fderiv ℝ φ (x + z) := by
                simpa using
                  (fderiv_comp_add_right (𝕜 := ℝ) (f := φ) (x := x) z)
              simp [ψ, hderiv]
            calc
              ∫ x in U, u x * (fderiv ℝ φ (x + z)) (basisVec i)
                  ∂MeasureTheory.volume =
                  ∫ x in U, u x * (fderiv ℝ ψ x) (basisVec i)
                    ∂MeasureTheory.volume := by
                      rw [hfun]
              _ = -∫ x in U, gi x * ψ x ∂MeasureTheory.volume := hWeak
              _ = -∫ x in U, gi x * φ (x + z)
                  ∂MeasureTheory.volume := rfl)
    _ = -∫ x in V, gi (x - z) * φ x
        ∂MeasureTheory.volume := by rw [hChangeRight]

/-- Push a weak partial derivative to `a • U` by the amplitude-normalized
dilation

`v(x) = a * u(a⁻¹ • x)`, `Dᵢv(x) = gi(a⁻¹ • x)`.

The positivity hypothesis fixes the geometric orientation and every
change-of-variables factor. -/
theorem dilate_of_pos {d : ℕ} {U : Set (Vec d)} {i : Fin d}
    {u gi : Vec d → ℝ} (h : HasWeakPartialDerivOn U i u gi)
    {a : ℝ} (ha : 0 < a) :
    HasWeakPartialDerivOn (a • U) i
      (fun x => a * u (a⁻¹ • x))
      (fun x => gi (a⁻¹ • x)) := by
  intro φ hφSmooth hφCompact hφSubset
  let V  := a • U
  let T : Vec d → Vec d := fun x => a⁻¹ • x
  have haNe  := ha.ne'
  let ψ  := fun y => φ (a • y)



  have hWeak := h ψ (show ContDiff ℝ PDE.smoothOrder ψ by
      simpa [ψ] using! hφSmooth.comp (contDiff_const_smul a)) (show HasCompactSupport ψ by
      show HasCompactSupport (φ ∘ Homeomorph.smulOfNeZero a haNe)
      exact hφCompact.comp_homeomorph (Homeomorph.smulOfNeZero a haNe)) (by
      intro y hy

      have hyV  := hφSubset (by
          rw [show ψ = φ ∘ Homeomorph.smulOfNeZero a haNe by rfl,
            tsupport_comp_eq_preimage φ
              (Homeomorph.smulOfNeZero a haNe)] at hy
          exact hy)
      simpa [V, Set.mem_smul_set_iff_inv_smul_mem, haNe] using hyV)
  have hDerivψ :
      ∀ y : Vec d,
        (fderiv ℝ ψ y) (basisVec i) =
          a * (fderiv ℝ φ (a • y)) (basisVec i) := by
    intro y

    simpa [smul_eq_mul] using
      congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec i)) (show fderiv ℝ (fun z  => φ (a • z)) y =
          a • fderiv ℝ φ (a • y) by
          simpa [ψ] using
            (fderiv_comp_smul (𝕜 := ℝ) (f := φ) (x := y) a))
  have hWeakScaled :
      a * ∫ y in U,
          u y * (fderiv ℝ φ (a • y)) (basisVec i)
            ∂MeasureTheory.volume =
        -∫ y in U, gi y * φ (a • y) ∂MeasureTheory.volume := by
    have hfun :
        (fun y => u y * (fderiv ℝ ψ y) (basisVec i)) =
          fun y =>
            a * (u y * (fderiv ℝ φ (a • y)) (basisVec i)) := by
      funext y
      rw [hDerivψ y]
      ring
    rw [hfun, MeasureTheory.integral_const_mul] at hWeak
    exact hWeak
  have hChangeLeft :
      ∫ y in U,
          a * (u y * (fderiv ℝ φ (a • y)) (basisVec i))
            ∂MeasureTheory.volume =
        (a ^ d)⁻¹ * ∫ x in V,
          a * u (T x) * (fderiv ℝ φ x) (basisVec i)
            ∂MeasureTheory.volume := by
    simpa only [V, T, smul_smul, inv_mul_cancel₀ haNe, one_smul,
      smul_eq_mul, Module.finrank_fin_fun, mul_assoc] using
      (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
        (μ := MeasureTheory.volume)
        (f := fun x  =>
          a * u (T x) * (fderiv ℝ φ x) (basisVec i))
        (s := U) ha)
  have hChangeRight :
      ∫ y in U, gi y * φ (a • y) ∂MeasureTheory.volume =
        (a ^ d)⁻¹ * ∫ x in V, gi (T x) * φ x
          ∂MeasureTheory.volume := by
    simpa only [V, T, smul_smul, inv_mul_cancel₀ haNe, one_smul,
      smul_eq_mul, Module.finrank_fin_fun] using
      (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
        (μ := MeasureTheory.volume)
        (f := fun x  => gi (T x) * φ x)
        (s := U) ha)
  have hScaleLeft :
      ∫ y in U,
          a * (u y * (fderiv ℝ φ (a • y)) (basisVec i))
            ∂MeasureTheory.volume =
        a * ∫ y in U,
          u y * (fderiv ℝ φ (a • y)) (basisVec i)
            ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_const_mul]
  calc
    ∫ x in V, a * u (T x) * (fderiv ℝ φ x) (basisVec i)
        ∂MeasureTheory.volume =
        (a ^ d) * ∫ y in U,
          a * (u y * (fderiv ℝ φ (a • y)) (basisVec i))
            ∂MeasureTheory.volume := by
          have hpow  := (pow_pos ha d).ne'
          rw [hChangeLeft]
          field_simp [hpow]
    _ = (a ^ d) *
        (a * ∫ y in U,
          u y * (fderiv ℝ φ (a • y)) (basisVec i)
            ∂MeasureTheory.volume) := by
          rw [hScaleLeft]
    _ = (a ^ d) *
        (-∫ y in U, gi y * φ (a • y)
          ∂MeasureTheory.volume) := by
          rw [hWeakScaled]
    _ = -((a ^ d) * ∫ y in U, gi y * φ (a • y)
          ∂MeasureTheory.volume) := by
          ring
    _ = -∫ x in V, gi (T x) * φ x
        ∂MeasureTheory.volume := by
          have hpow  := (pow_pos ha d).ne'
          rw [hChangeRight]
          field_simp [hpow]

end HasWeakPartialDerivOn



end PDE
