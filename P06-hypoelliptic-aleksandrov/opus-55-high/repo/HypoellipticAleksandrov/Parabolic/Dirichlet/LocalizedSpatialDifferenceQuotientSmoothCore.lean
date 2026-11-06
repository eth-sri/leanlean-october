module

public import HypoellipticAleksandrov.Measure.HilbertVectorLpAssembly
public import HypoellipticAleksandrov.Parabolic.Dirichlet.GalerkinDense
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientSmoothGraph
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolevNorm

/-!
# Bounded localized quotients on the actual smooth `H¹₀` core

This module constructs the cutoff-localized forward spatial difference
quotient only on bundled smooth compactly supported tests and records its
quotient-level value, gradient, and relative graph-norm bound.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The localized difference quotient as a linear map on bundled smooth tests. -/
def localizedSpatialDifferenceQuotientWeakTestLinearMap
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω) :
    PDE.WeakTestFunction Ω →ₗ[ℝ] PDE.WeakTestFunction Ω where
  toFun φ := localizedSpatialDifferenceQuotientWeakTest η k h φ hηΩ
  map_add' φ ψ := by
    apply PDE.WeakTestFunction.ext
    funext y
    simp only [localizedSpatialDifferenceQuotientWeakTest_apply,
      PDE.WeakTestFunction.add_toFun]
    ring
  map_smul' c φ := by
    apply PDE.WeakTestFunction.ext
    funext y
    simp only [localizedSpatialDifferenceQuotientWeakTest_apply,
      PDE.WeakTestFunction.smul_toFun, RingHom.id_apply]
    ring

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

theorem norm_hilbertVectorLpCoord_le
     (j : Fin d)
    (G : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞)) :
    ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j G‖ ≤ ‖G‖ := by
  calc
    ‖(PiLp.proj (𝕜 := ℝ) 2 _ j).compLpL
        _ _ G‖ ≤
        ‖PiLp.proj (𝕜 := ℝ) 2 _ j‖ * ‖G‖ := ContinuousLinearMap.norm_compLp_le _ _
    _ ≤ 1 * ‖G‖ := by
      gcongr
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      simpa using
        PiLp.norm_apply_le x j
    _ = ‖G‖ := one_mul _

theorem norm_h10HilbertGraph_le_value_add_gradient
     (hΩ : IsOpen Ω)
    (u : H10HilbertGraph hΩ) :
    ‖u‖ ≤ ‖valueCLM hΩ u‖ + ‖gradientCLM hΩ u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  calc
    ‖u‖ ^ 2 = ‖valueCLM hΩ u‖ ^ 2 + ‖gradientCLM hΩ u‖ ^ 2 :=
      norm_sq_h10HilbertGraph hΩ u
    _ ≤ ‖valueCLM hΩ u‖ ^ 2 + ‖gradientCLM hΩ u‖ ^ 2 +
        2 * (‖valueCLM hΩ u‖ * ‖gradientCLM hΩ u‖) := by
      apply le_add_of_nonneg_right
      exact mul_nonneg (by norm_num) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (‖valueCLM hΩ u‖ + ‖gradientCLM hΩ u‖) ^ 2 := by ring

/-- The cutoff-localized forward spatial quotient as a linear map from
actual bundled smooth tests into the zero-boundary Sobolev graph. -/
def localizedSpatialDifferenceQuotientSmoothCoreLinearMap
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω) :
    PDE.WeakTestFunction Ω →ₗ[ℝ] H10HilbertGraph hΩ :=
  (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ).comp
    (localizedSpatialDifferenceQuotientWeakTestLinearMap η k h hηΩ)

/-- The quotient-safe vector `L²` expression for the gradient of the
localized quotient on the actual smooth core. -/
def localizedSpatialDifferenceQuotientSmoothGradientCLM
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) :
    H10HilbertGraph hΩ →L[ℝ]
      PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
  PDE.hilbertVectorLpAssemble fun j =>
    (cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h).comp
        (valueCLM hΩ) +
      (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h).comp
        ((PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j).comp
          (gradientCLM hΩ))

variable {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ} (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d)

/-- The smooth-core value class is the quotient-level localized value
operator applied to the exact dense-core inclusion. -/
theorem valueCLM_localizedSpatialDifferenceQuotientSmoothCoreLinearMap_apply
     (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    valueCLM hΩ
      (localizedSpatialDifferenceQuotientSmoothCoreLinearMap
        hΩ η k h hηΩ φ) =
      localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
        (valueCLM hΩ
          (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)) := by
  have hcore :
      localizedSpatialDifferenceQuotientSmoothCoreLinearMap hΩ η k h hηΩ φ =
        smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
          (localizedSpatialDifferenceQuotientWeakTest η k h φ hηΩ) := by
    apply Subtype.ext
    rfl
  have hinputEq :
      smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ =
        smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ := by
    apply Subtype.ext
    rfl
  rw [hcore, hinputEq]
  apply MeasureTheory.Lp.ext
  have hleft := ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ
    (localizedSpatialDifferenceQuotientWeakTest η k h φ hηΩ)
  have hinput := ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ φ
  have hright := localizedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    hΩ.measurableSet η k h
    _
    φ hinput hηshift
  filter_upwards [hleft, hright] with y hleft hright
  rw [hleft, hright]
  rfl

/-- The smooth-core gradient class is the assembled quotient-safe vector
operator applied to the exact dense-core inclusion. -/
theorem gradientCLM_localizedSpatialDifferenceQuotientSmoothCoreLinearMap_apply
     (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    gradientCLM hΩ
      (localizedSpatialDifferenceQuotientSmoothCoreLinearMap
        hΩ η k h hηΩ φ) =
      localizedSpatialDifferenceQuotientSmoothGradientCLM hΩ η k h
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) := by
  let e  :=
    smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ
  let L  := fun j =>
    (cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h).comp
        (valueCLM hΩ) +
      (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h).comp
        ((PDE.hilbertVectorLpCoord Ω _ j).comp (gradientCLM hΩ))
  have hcore :
      localizedSpatialDifferenceQuotientSmoothCoreLinearMap hΩ η k h hηΩ φ =
        smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
          (localizedSpatialDifferenceQuotientWeakTest η k h φ hηΩ) := by
    apply Subtype.ext
    rfl
  have hinput :
      smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ =
        smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ := by
    apply Subtype.ext
    rfl
  have hcoord (j : Fin d) :
      PDE.hilbertVectorLpCoord Ω _ j
          (gradientCLM hΩ
            (localizedSpatialDifferenceQuotientSmoothCoreLinearMap hΩ η k h hηΩ φ)) =
        L j (e φ) := localizedSpatialDifferenceQuotientWeakTest_gradientCoord_eq
      hΩ η k h φ hηΩ hηshift j
  have hgradientDef :
      localizedSpatialDifferenceQuotientSmoothGradientCLM hΩ η k h _ =
        PDE.hilbertVectorLpAssemble L (e φ) := rfl
  rw [hgradientDef]
  apply MeasureTheory.Lp.ext
  have hcoords : ∀ᵐ y : PDE.Vec d ∂PDE.volumeOn Ω, ∀ j : Fin d,
      gradientCLM hΩ
        (localizedSpatialDifferenceQuotientSmoothCoreLinearMap hΩ η k h hηΩ φ) y j =
        L j (e φ) y := by
    apply ae_all_iff.mpr
    intro j
    have hleft := PDE.coeFn_hilbertVectorLpCoord Ω _ j
      (gradientCLM hΩ
        (localizedSpatialDifferenceQuotientSmoothCoreLinearMap hΩ η k h hηΩ φ))
    filter_upwards [hleft] with y hleft
    exact hleft.symm.trans (congrArg (fun z : PDE.ScalarLp Ω _ => z y)
      (hcoord j))
  have hassemble := PDE.hilbertVectorLpAssemble_apply_ae L (e φ)
  filter_upwards [hcoords, hassemble] with y hcoords hassemble
  rw [hassemble]
  apply (PiLp.continuousLinearEquiv 2 ℝ _).injective
  ext j
  simpa using hcoords j

/-- The actual smooth localized quotient is bounded relative to the exact
dense-core inclusion, with a totalized dimension/cutoff/step witness. -/
theorem norm_localizedSpatialDifferenceQuotientSmoothCoreLinearMap_apply_le
     (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    ‖localizedSpatialDifferenceQuotientSmoothCoreLinearMap
        hΩ η k h hηΩ φ‖ ≤
      (2 * (1 + (d : ℝ) * (K + 1)) / |h|) *
        ‖smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ‖ := by
  let x  :=
    smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ
  let q  :=
    localizedSpatialDifferenceQuotientSmoothCoreLinearMap hΩ η k h hηΩ φ
  have hvalue : valueCLM hΩ q =
      localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h (valueCLM hΩ x) := by
    simpa only [q, x] using
      valueCLM_localizedSpatialDifferenceQuotientSmoothCoreLinearMap_apply
        hΩ η k h φ hηΩ hηshift
  have hgradient : gradientCLM hΩ q =
      localizedSpatialDifferenceQuotientSmoothGradientCLM hΩ η k h x := by
    simpa using
      gradientCLM_localizedSpatialDifferenceQuotientSmoothCoreLinearMap_apply
        hΩ η k h φ hηΩ hηshift
  have hvalueInput : ‖valueCLM hΩ x‖ ≤ ‖x‖ := by
    let z  := (x : PDE.H1HilbertGraph Ω).1
    exact WithLp.norm_fst_le _ z
  have hgradientInput : ‖gradientCLM hΩ x‖ ≤ ‖x‖ := by
    let z  := (x : PDE.H1HilbertGraph Ω).1
    exact WithLp.norm_snd_le _ z
  have hvalueBound : ‖valueCLM hΩ q‖ ≤ (2 / |h|) * ‖x‖ := by
    rw [hvalue]
    exact (norm_localizedSpatialDifferenceQuotientL2_apply_le
      hΩ.measurableSet η k h _).trans
      (mul_le_mul_of_nonneg_left hvalueInput
        (div_nonneg (by norm_num) (abs_nonneg h)))
  let L  := fun j =>
    (cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h).comp
        (valueCLM hΩ) +
      (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h).comp
        ((PDE.hilbertVectorLpCoord Ω _ j).comp (gradientCLM hΩ))
  have hcoordinateBound (j : Fin d) :
      ‖L j x‖ ≤
        ((2 * K / |h|) + (2 / |h|)) * ‖x‖ := by
    calc
      _ ≤ ‖(cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h).comp
          _ x‖ +
          ‖(localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h).comp
            _ x‖ := norm_add_le _ _
      _ ≤ (2 * K / |h|) * ‖valueCLM hΩ x‖ +
          (2 / |h|) * ‖PDE.hilbertVectorLpCoord Ω _ j
            _‖ := by
        apply add_le_add
        · exact norm_cutoffGradientSpatialDifferenceQuotientL2_apply_le
            hΩ.measurableSet η j k h _
        · exact norm_localizedSpatialDifferenceQuotientL2_apply_le
            hΩ.measurableSet η k h
              _
      _ ≤ (2 * K / |h|) * ‖x‖ + (2 / |h|) * ‖x‖ := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left hvalueInput
          exact div_nonneg (mul_nonneg (by norm_num) η.gradient_bound_nonneg) (abs_nonneg h)
        · apply mul_le_mul_of_nonneg_left
            ((norm_hilbertVectorLpCoord_le j (gradientCLM hΩ x)).trans hgradientInput)
          exact div_nonneg (by norm_num) (abs_nonneg h)
      _ = ((2 * K / |h|) + (2 / |h|)) * ‖x‖ := by ring
  have hgradientBound : ‖gradientCLM hΩ q‖ ≤
      d * ((2 * K / |h|) + (2 / |h|)) * ‖x‖ := by
    rw [hgradient]
    calc
      _ ≤ ∑ j, ‖L j x‖ := PDE.norm_hilbertVectorLpAssemble_apply_le L x
      _ ≤ ∑ _ : Fin d, ((2 * K / |h|) + (2 / |h|)) * ‖x‖ := by
        apply Finset.sum_le_sum
        intro j _
        exact hcoordinateBound j
      _ = d * ((2 * K / |h|) + (2 / |h|)) * ‖x‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
  calc
    ‖localizedSpatialDifferenceQuotientSmoothCoreLinearMap hΩ η k h hηΩ φ‖ = ‖q‖ := rfl
    _ ≤ ‖valueCLM hΩ q‖ + ‖gradientCLM hΩ q‖ :=
      norm_h10HilbertGraph_le_value_add_gradient hΩ q
    _ ≤ (2 / |h|) * ‖x‖ +
        (d * ((2 * K / |h|) + (2 / |h|))) * ‖x‖ := add_le_add hvalueBound hgradientBound
    _ = (2 * (1 + d * (K + 1)) / |h|) * ‖x‖ := by ring

end HypoellipticAleksandrov.Parabolic.Dirichlet
