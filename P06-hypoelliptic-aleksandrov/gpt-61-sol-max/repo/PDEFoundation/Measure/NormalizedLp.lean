module

public import PDEFoundation.Ambient.EuclideanNorm
public import PDEFoundation.Measure.AffineVolume
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Restricted and normalized `L^p` norms

This file defines raw extended-real `L^p` norms on restricted volume and on
normalized restricted volume. Real-valued facades require a `MemLp` proof, so
an infinite extended-real norm can never be silently converted to zero.

Vector-field norms are scalarized with `PDE.vecEuclideanNorm`; they do not use
the inherited finite-product supremum norm on `PDE.Vec`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

variable {d : ℕ}

/-- Volume restricted to `U`, rescaled by the inverse volume of `U`.

The definition is total. It is a probability measure only when `U` has
positive finite volume; those hypotheses are explicit in the corresponding
theorems.
-/
noncomputable def normalizedVolumeOn  (U : Set (Vec d)) :
    Measure (Vec d) :=
  (volume U)⁻¹ • volumeOn U

/-- Integrability on a positive-volume set implies integrability against its
normalized restricted volume. -/
theorem integrable_normalizedVolumeOn_of_integrableOn
     {E : Type*}
    [TopologicalSpace E] [ESeminormedAddMonoid E]
    {U : Set (Vec d)} {f : Vec d → E}
    (hf : IntegrableOn f U )
    (hUPos : 0 < volume U) :
    Integrable f (normalizedVolumeOn U) := by
  rw [normalizedVolumeOn]
  exact hf.integrable.smul_measure
    (ENNReal.inv_ne_top.mpr hUPos.ne')

section
variable {U : Set (Vec d)} (hUPos : 0 < volume U) (hUTop : volume U < ∞)

include hUPos hUTop
theorem normalizedVolumeOn_apply_univ_of_pos_of_lt_top
      :
    normalizedVolumeOn U Set.univ = 1 := by
  rw [normalizedVolumeOn, Measure.smul_apply, volumeOn,
    Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hUPos.ne' hUTop.ne

theorem isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top
      :
    IsProbabilityMeasure (normalizedVolumeOn U) :=
  ⟨normalizedVolumeOn_apply_univ_of_pos_of_lt_top hUPos hUTop⟩

/-- On a positive finite-volume domain, multiplying normalized volume by the
domain volume recovers restricted volume exactly. -/
theorem volume_smul_normalizedVolumeOn_eq_volumeOn
      :
    volume U • normalizedVolumeOn U = volumeOn U := by
  rw [normalizedVolumeOn, smul_smul,
    ENNReal.mul_inv_cancel hUPos.ne' hUTop.ne, one_smul]
end


variable {E : Type*}

/-- The raw extended-real `L^p` norm with respect to volume restricted to `U`. -/
noncomputable def eLpNormOn
      [NormedAddCommGroup E]
    (U : Set (Vec d)) (p : ℝ≥0∞) (f : Vec d → E) : ℝ≥0∞ :=
  eLpNorm f p (volumeOn U)

/-- The raw extended-real normalized `L^p` norm on `U`. -/
noncomputable def eLpMeanNormOn
      [NormedAddCommGroup E]
    (U : Set (Vec d)) (p : ℝ≥0∞) (f : Vec d → E) : ℝ≥0∞ :=
  eLpNorm f p (normalizedVolumeOn U)

/-- Exact conversion from the normalized to the unnormalized extended
`L^p` norm. -/
theorem eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn
      [NormedAddCommGroup E]
    {U : Set (Vec d)} (hUTop : volume U < ∞)
    (p : ℝ≥0∞) (f : Vec d → E) :
    eLpMeanNormOn U p f =
      (volume U)⁻¹ ^ (1 / p).toReal *
        eLpNormOn U p f := by

  rw [eLpMeanNormOn, normalizedVolumeOn,
    eLpNorm_smul_measure_of_ne_zero (ENNReal.inv_ne_zero.mpr hUTop.ne)]
  rfl

/-- Exact conversion from the unnormalized to the normalized extended
`L^p` norm on a positive finite-volume domain. -/
theorem eLpNormOn_eq_volume_rpow_mul_eLpMeanNormOn
      [NormedAddCommGroup E]
    {U : Set (Vec d)}
    (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (p : ℝ≥0∞) (f : Vec d → E) :
    eLpNormOn U p f =
      volume U ^ (1 / p).toReal *
        eLpMeanNormOn U p f := by

  calc
    eLpNormOn U p f =
        eLpNorm f p (volume U • normalizedVolumeOn U) := by
      rw [volume_smul_normalizedVolumeOn_eq_volumeOn hUPos hUTop]
      rfl
    _ = volume U ^ (1 / p).toReal *
        eLpMeanNormOn U p f := by
      rw [eLpNorm_smul_measure_of_ne_zero hUPos.ne']
      rfl

theorem eLpNormOn_congr_ae
      [NormedAddCommGroup E]
    {U : Set (Vec d)} {p : ℝ≥0∞} {f g : Vec d → E}
    (hfg : f =ᵐ[volumeOn U] g) :
    eLpNormOn U p f = eLpNormOn U p g := (id (eLpNorm_congr_ae hfg))

variable (U : Set (Vec d)) (p : ℝ≥0∞) (F : Vec d → Vec d)

/-- The raw restricted `L^p` norm of the Euclidean magnitude of a vector field. -/
noncomputable def euclideanFieldELpNormOn
      : ℝ≥0∞ :=
  eLpNormOn U p (fun x => vecEuclideanNorm (F x))

/-- The raw normalized `L^p` norm of the Euclidean magnitude of a vector field. -/
noncomputable def euclideanFieldELpMeanNormOn
      : ℝ≥0∞ :=
  eLpMeanNormOn U p (fun x => vecEuclideanNorm (F x))

variable {U : Set (Vec d)}

theorem euclideanFieldELpMeanNormOn_eq_volume_inv_rpow_mul
      (hUTop : volume U < ∞)
    (p : ℝ≥0∞) (F : Vec d → Vec d) :
    euclideanFieldELpMeanNormOn U p F =
      (volume U)⁻¹ ^ (1 / p).toReal *
        euclideanFieldELpNormOn U p F := eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn
      hUTop p (fun x => vecEuclideanNorm (F x))

theorem euclideanFieldELpNormOn_eq_volume_rpow_mul

    (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (p : ℝ≥0∞) (F : Vec d → Vec d) :
    euclideanFieldELpNormOn U p F =
      volume U ^ (1 / p).toReal *
        euclideanFieldELpMeanNormOn U p F := by
  solve_by_elim (maxDepth := 4) [eLpNormOn_eq_volume_rpow_mul_eLpMeanNormOn, vecEuclideanNorm]

theorem euclideanFieldELpNormOn_congr_ae
      {p : ℝ≥0∞}
    {F G : Vec d → Vec d} (hFG : F =ᵐ[volumeOn U] G) :
    euclideanFieldELpNormOn U p F =
      euclideanFieldELpNormOn U p G := by
  apply eLpNormOn_congr_ae
  exact hFG.fun_comp vecEuclideanNorm

end PDE
