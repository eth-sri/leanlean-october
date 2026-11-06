module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.DiskAreaGram

/-!
# Bessel estimates for physical area moments on the disk

The holomorphic and antiholomorphic monomials form two separate
orthogonal families in the actual area L² space. Their normalization
gives the weighted mass-moment estimate used in the Neumann equation.
The two zero modes are not combined into one orthonormal family.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real
open scoped ComplexConjugate InnerProductSpace

def diskHolomorphicArea m  :=
  ((diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m)).memLp'
    2 (μ := volume.restrict unitDisk)).toLp
      (diskHarmonicCutoff (diskHolomorphicMode m))

def diskAntiholomorphicArea m  :=
  ((diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)).memLp'
    2 (μ := volume.restrict unitDisk)).toLp
      (diskHarmonicCutoff (diskAntiholomorphicMode m))

theorem diskHolomorphicArea_ae m :
    (diskHolomorphicArea m : PlaneMap) =ᵐ[volume.restrict unitDisk]
      fun z => z ^ m := by
  filter_upwards [((diskHarmonicCutoff_testFunction
    (contDiff_diskHolomorphicMode m)).memLp'
      2 (μ := volume.restrict (ball 0 1))).coeFn_toLp,
    ae_restrict_mem measurableSet_ball] with z hz hzD
  change (diskHolomorphicArea m) z = diskHarmonicCutoff (diskHolomorphicMode m) z at hz
  rw [hz, diskHarmonicCutoff_eq_closedDisk _ (ball_subset_closedBall hzD)]
  rfl

theorem diskAntiholomorphicArea_ae m :
    (diskAntiholomorphicArea m : PlaneMap) =ᵐ[volume.restrict unitDisk]
      fun z => conj z ^ m := by
  filter_upwards [((diskHarmonicCutoff_testFunction
    (contDiff_diskAntiholomorphicMode m)).memLp'
      2 (μ := volume.restrict (ball 0 1))).coeFn_toLp,
    ae_restrict_mem measurableSet_ball] with z hz hzD
  change (diskAntiholomorphicArea m) z = diskHarmonicCutoff (diskAntiholomorphicMode m) z at hz
  rw [hz, diskHarmonicCutoff_eq_closedDisk _ (ball_subset_closedBall hzD)]
  rfl

theorem inner_diskHolomorphicArea m n :
    ⟪diskHolomorphicArea m, diskHolomorphicArea n⟫_ℂ =
      if m = n then (π : ℂ) / ((m + 1 : ℕ) : ℂ) else 0 := by
  calc
    _ = ∫ z in unitDisk, z ^ n * conj z ^ m := by
      apply integral_congr_ae
      filter_upwards [diskHolomorphicArea_ae m, diskHolomorphicArea_ae n] with z hm hn
      simp_all
    _ = _ := by
      rw [integral_disk_area_monomials]
      aesop

theorem inner_diskAntiholomorphicArea m n :
    ⟪diskAntiholomorphicArea m, diskAntiholomorphicArea n⟫_ℂ =
      if m = n then (π : ℂ) / ((m + 1 : ℕ) : ℂ) else 0 := by
  calc
    _ = ∫ z in ball 0 1, z ^ m * conj z ^ n := by
      apply integral_congr_ae
      filter_upwards [diskAntiholomorphicArea_ae m, diskAntiholomorphicArea_ae n]
        with z hm hn
      simp only [RCLike.inner_apply', hm, hn, map_pow, Complex.conj_conj]
    _ = _ := integral_disk_area_monomials m n

section
variable (m : ℕ) (v : L2 unitDisk)
include m v

theorem inner_diskHolomorphicArea_eq_integral :
    ⟪diskHolomorphicArea m, v⟫_ℂ =
      ∫ z in unitDisk, (v : PlaneMap) z * conj z ^ m := by
  apply integral_congr_ae
  filter_upwards [diskHolomorphicArea_ae m] with z hz
  simp_all

theorem inner_diskAntiholomorphicArea_eq_integral :
    ⟪diskAntiholomorphicArea m, v⟫_ℂ =
      ∫ z in unitDisk, (v : PlaneMap) z * z ^ m := by
  apply integral_congr_ae
  filter_upwards [diskAntiholomorphicArea_ae m] with z hz
  simp_all

end


def diskAreaScale (m : ℕ) : ℂ := (Real.sqrt (((m + 1 : ℕ) : ℝ) / π) : ℝ)

private theorem diskAreaScale_normalizes (m : ℕ) :
    conj (diskAreaScale m) *
      (diskAreaScale m * ((π : ℂ) / ((m + 1 : ℕ) : ℂ))) = 1 := by
  have hm : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hsq := Real.sq_sqrt
    (show 0 ≤ ((m + 1 : ℕ)) / π by positivity)
  have hr : Real.sqrt (((m + 1 : ℕ) : ℝ) / π) *
      (Real.sqrt (((m + 1 : ℕ) : ℝ) / π) * (π / ((m + 1 : ℕ) : ℝ))) = 1 := by
    calc
      _ = (Real.sqrt (((m + 1 : ℕ)) / π) ^ 2 * π) /
          ((m + 1 : ℕ)) := by ring
      _ = 1 := by simp_all
  simp  [diskAreaScale]
  exact_mod_cast hr

def diskNormalizedHolomorphicArea m  :=
  diskAreaScale m • diskHolomorphicArea m

def diskNormalizedAntiholomorphicArea m  :=
  diskAreaScale m • diskAntiholomorphicArea m

private theorem orthonormal_of_diskAreaGram
    (v : ℕ → L2 unitDisk)
    (hv : ∀ m n, ⟪v m, v n⟫_ℂ =
      if m = n then (π : ℂ) / ((m + 1 : ℕ) : ℂ) else 0) :
    Orthonormal ℂ (fun m => diskAreaScale m • v m) := by
  rw [orthonormal_iff_ite]
  intro m n
  by_cases hmn : m = n
  · subst n
    simp only [inner_smul_left, inner_smul_right, hv, ite_true]
    grind only [diskAreaScale, diskAreaScale_normalizes, PolyaNeumann.diskAreaScale]
  · simp [inner_smul_left, inner_smul_right, hv, hmn]

theorem orthonormal_diskNormalizedHolomorphicArea :
    Orthonormal ℂ diskNormalizedHolomorphicArea :=
  orthonormal_of_diskAreaGram diskHolomorphicArea inner_diskHolomorphicArea

theorem orthonormal_diskNormalizedAntiholomorphicArea :
    Orthonormal ℂ diskNormalizedAntiholomorphicArea :=
  orthonormal_of_diskAreaGram diskAntiholomorphicArea inner_diskAntiholomorphicArea

private theorem norm_sq_diskArea_scaled_inner m
    (v w : L2 unitDisk) :
    π * ‖⟪diskAreaScale m • v, w⟫_ℂ‖ ^ 2 =
      ((m + 1 : ℕ) : ℝ) * ‖⟪v, w⟫_ℂ‖ ^ 2 := by
  rw [inner_smul_left, norm_mul, Complex.norm_conj]
  simp only [diskAreaScale, Complex.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (show 0 ≤ ((m + 1 : ℕ)) / π by positivity)]
  field_simp

private theorem diskArea_bessel
    (v : ℕ → L2 unitDisk)
    (hv : Orthonormal ℂ (fun m => diskAreaScale m • v m))
    w :
    Summable (fun m => ((m + 1 : ℕ) : ℝ) * ‖⟪v m, w⟫_ℂ‖ ^ 2) ∧
      (∑' m : ℕ, ((m + 1 : ℕ) : ℝ) * ‖⟪v m, w⟫_ℂ‖ ^ 2) ≤ π * ‖w‖ ^ 2 := by
  have hs := hv.inner_products_summable w
  have he (m : ℕ) := norm_sq_diskArea_scaled_inner m (v m) w
  refine ⟨(hs.mul_left π).congr he, ?_⟩
  calc
    _ = π * ∑' m : ℕ, ‖⟪diskAreaScale m • v m, w⟫_ℂ‖ ^ 2 := by
      rw [← tsum_mul_left]
      exact tsum_congr (fun m => (he m).symm)
    _ ≤ _ := mul_le_mul_of_nonneg_left (hv.tsum_inner_products_le w) Real.pi_pos.le

theorem disk_area_holomorphic_bessel (v : L2 unitDisk) :
    Summable (fun m => ((m + 1 : ℕ) : ℝ) *
      ‖∫ z in unitDisk, (v : PlaneMap) z * conj z ^ m‖ ^ 2) ∧
    (∑' m : ℕ, ((m + 1 : ℕ) : ℝ) *
      ‖∫ z in unitDisk, (v : PlaneMap) z * conj z ^ m‖ ^ 2) ≤ π * ‖v‖ ^ 2 := by
  simpa  [inner_diskHolomorphicArea_eq_integral] using
    diskArea_bessel diskHolomorphicArea orthonormal_diskNormalizedHolomorphicArea v

theorem disk_area_antiholomorphic_bessel (v : L2 unitDisk) :
    Summable (fun m => ((m + 1 : ℕ) : ℝ) *
      ‖∫ z in unitDisk, (v : PlaneMap) z * z ^ m‖ ^ 2) ∧
    (∑' m : ℕ, ((m + 1 : ℕ) : ℝ) *
      ‖∫ z in unitDisk, (v : PlaneMap) z * z ^ m‖ ^ 2) ≤ π * ‖v‖ ^ 2 := by
  simpa  [inner_diskAntiholomorphicArea_eq_integral] using
    diskArea_bessel diskAntiholomorphicArea orthonormal_diskNormalizedAntiholomorphicArea v

end PolyaNeumann

end
