module

public import RequestProject.DiskAreaGram
public import RequestProject.PlanarNotation

/-!
# Bessel estimates for physical area moments on the disk

The holomorphic and antiholomorphic monomials form two separate
orthogonal families in the actual area L² space. Their normalization
gives the weighted mass-moment estimate used in the Neumann equation.
The two zero modes are not combined into one orthonormal family.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real
open scoped ComplexConjugate InnerProductSpace

section

variable (m n : ℕ) (v : L2 unitDisk)
include m

def diskHolomorphicArea : L2 unitDisk :=
  ((diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m)).memLp'
    2 ).toLp
      (diskHarmonicCutoff (diskHolomorphicMode m))

def diskAntiholomorphicArea : L2 unitDisk :=
  ((diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)).memLp'
    2 ).toLp
      (diskHarmonicCutoff (diskAntiholomorphicMode m))

theorem diskHolomorphicArea_ae :
    (diskHolomorphicArea m : ℂ → ℂ) =ᵐ[volume.restrict unitDisk]
      fun z => z ^ m := by
  filter_upwards [((diskHarmonicCutoff_testFunction
    (contDiff_diskHolomorphicMode m)).memLp'
      2 ).coeFn_toLp,
    ae_restrict_mem measurableSet_ball] with z hz hzD
  change (diskHolomorphicArea m) z = diskHarmonicCutoff (diskHolomorphicMode m) z at hz
  rw [hz, diskHarmonicCutoff_eq_closedDisk _ (ball_subset_closedBall hzD)]
  rfl

theorem diskAntiholomorphicArea_ae :
    (diskAntiholomorphicArea m : ℂ → ℂ) =ᵐ[volume.restrict unitDisk]
      fun z => conj z ^ m := by
  filter_upwards [((diskHarmonicCutoff_testFunction
    (contDiff_diskAntiholomorphicMode m)).memLp'
      2 ).coeFn_toLp,
    ae_restrict_mem measurableSet_ball] with z hz hzD
  change (diskAntiholomorphicArea m) z = diskHarmonicCutoff (diskAntiholomorphicMode m) z at hz
  rw [hz, diskHarmonicCutoff_eq_closedDisk _ (ball_subset_closedBall hzD)]
  rfl

theorem inner_diskHolomorphicArea :
    ⟪diskHolomorphicArea m, diskHolomorphicArea n⟫_ℂ =
      if m = n then (π : ℂ) / ((m + 1 : ℕ) : ℂ) else 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ z in unitDisk, z ^ n * conj z ^ m := by
      apply integral_congr_ae
      filter_upwards [diskHolomorphicArea_ae m, diskHolomorphicArea_ae n] with z hm hn
      simp [hm, hn]
    _ = _ := by
      rw [integral_disk_area_monomials]
      grind

theorem inner_diskAntiholomorphicArea :
    ⟪diskAntiholomorphicArea m, diskAntiholomorphicArea n⟫_ℂ =
      if m = n then (π : ℂ) / ((m + 1 : ℕ) : ℂ) else 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ z in unitDisk, z ^ m * conj z ^ n := by
      apply integral_congr_ae
      filter_upwards [diskAntiholomorphicArea_ae m, diskAntiholomorphicArea_ae n]
        with z hm hn
      simp only [RCLike.inner_apply', hm, hn, map_pow, Complex.conj_conj]
    _ = _ := integral_disk_area_monomials m n

theorem inner_diskHolomorphicArea_eq_integral :
    ⟪diskHolomorphicArea m, v⟫_ℂ =
      ∫ z in unitDisk, (v : ℂ → ℂ) z * conj z ^ m := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [diskHolomorphicArea_ae m] with z hz
  simp [hz]

theorem inner_diskAntiholomorphicArea_eq_integral :
    ⟪diskAntiholomorphicArea m, v⟫_ℂ =
      ∫ z in unitDisk, (v : ℂ → ℂ) z * z ^ m := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [diskAntiholomorphicArea_ae m] with z hz
  simp [hz]

def diskAreaScale : ℂ := (Real.sqrt (((m + 1 : ℕ) : ℝ) / π) : ℝ)

private theorem diskAreaScale_normalizes :
    conj (diskAreaScale m) *
      (diskAreaScale m * ((π : ℂ) / ((m + 1 : ℕ) : ℂ))) = 1 := by
  have hm : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hsq := Real.sq_sqrt
    (show 0 ≤ ((m + 1 : ℕ) : ℝ) / π by positivity)
  
  simp only [diskAreaScale, Complex.conj_ofReal]
  exact_mod_cast (calc
    _ = (Real.sqrt (((m + 1 : ℕ) : ℝ) / π) ^ 2 * π) /
        ((m + 1 : ℕ) : ℝ) := by ring
    _ = 1 := by rw [(eq_div_iff Real.pi_ne_zero).mp hsq, div_self hm])

def diskNormalizedHolomorphicArea : L2 unitDisk :=
  diskAreaScale m • diskHolomorphicArea m

def diskNormalizedAntiholomorphicArea : L2 unitDisk :=
  diskAreaScale m • diskAntiholomorphicArea m

end

section

variable (v : ℕ → L2 unitDisk)

private theorem orthonormal_of_diskAreaGram
    (hv : ∀ m n, ⟪v m, v n⟫_ℂ =
      if m = n then (π : ℂ) / ((m + 1 : ℕ) : ℂ) else 0) :
    Orthonormal ℂ (fun m => diskAreaScale m • v m) := by
  rw [orthonormal_iff_ite]
  intro m n
  by_cases hmn : m = n
  · subst n
    simp only [inner_smul_left, inner_smul_right, hv, ite_true]
    calc
      _ = conj (diskAreaScale m) *
        (diskAreaScale m * ((π : ℂ) / ((m + 1 : ℕ) : ℂ))) := by ring
      _ = 1 := diskAreaScale_normalizes m
  · simp [inner_smul_left, inner_smul_right, hv, hmn]

theorem orthonormal_diskNormalizedHolomorphicArea :
    Orthonormal ℂ diskNormalizedHolomorphicArea :=
  orthonormal_of_diskAreaGram diskHolomorphicArea inner_diskHolomorphicArea

theorem orthonormal_diskNormalizedAntiholomorphicArea :
    Orthonormal ℂ diskNormalizedAntiholomorphicArea :=
  orthonormal_of_diskAreaGram diskAntiholomorphicArea inner_diskAntiholomorphicArea

private theorem norm_sq_diskArea_scaled_inner (m : ℕ)
    (v w : L2 unitDisk) :
    π * ‖⟪diskAreaScale m • v, w⟫_ℂ‖ ^ 2 =
      ((m + 1 : ℕ) : ℝ) * ‖⟪v, w⟫_ℂ‖ ^ 2 := by
  rw [inner_smul_left, norm_mul, Complex.norm_conj]
  simp only [diskAreaScale, Complex.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (show 0 ≤ ((m + 1 : ℕ) : ℝ) / π by positivity)]
  field_simp [Real.pi_ne_zero]

private theorem diskArea_bessel
    (hv : Orthonormal ℂ (fun m => diskAreaScale m • v m))
    (w : L2 unitDisk) :
    Summable (fun m => ((m + 1 : ℕ) : ℝ) * ‖⟪v m, w⟫_ℂ‖ ^ 2) ∧
      (∑' m : ℕ, ((m + 1 : ℕ) : ℝ) * ‖⟪v m, w⟫_ℂ‖ ^ 2) ≤ π * ‖w‖ ^ 2 := by
  
  have he (m : ℕ) := norm_sq_diskArea_scaled_inner m (v m) w
  refine ⟨((hv.inner_products_summable w).mul_left π).congr he, ?_⟩
  calc
    _ = π * ∑' m : ℕ, ‖⟪diskAreaScale m • v m, w⟫_ℂ‖ ^ 2 := by
      rw [← tsum_mul_left]
      simp [*]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hv.tsum_inner_products_le w) Real.pi_pos.le

end

theorem disk_area_holomorphic_bessel (v : L2 unitDisk) :
    Summable (fun m => ((m + 1 : ℕ) : ℝ) *
      ‖∫ z in unitDisk, (v : ℂ → ℂ) z * conj z ^ m‖ ^ 2) ∧
    (∑' m : ℕ, ((m + 1 : ℕ) : ℝ) *
      ‖∫ z in unitDisk, (v : ℂ → ℂ) z * conj z ^ m‖ ^ 2) ≤ π * ‖v‖ ^ 2 := by
  simpa only [inner_diskHolomorphicArea_eq_integral] using
    diskArea_bessel diskHolomorphicArea orthonormal_diskNormalizedHolomorphicArea v

theorem disk_area_antiholomorphic_bessel (v : L2 unitDisk) :
    Summable (fun m => ((m + 1 : ℕ) : ℝ) *
      ‖∫ z in unitDisk, (v : ℂ → ℂ) z * z ^ m‖ ^ 2) ∧
    (∑' m : ℕ, ((m + 1 : ℕ) : ℝ) *
      ‖∫ z in unitDisk, (v : ℂ → ℂ) z * z ^ m‖ ^ 2) ≤ π * ‖v‖ ^ 2 := by
  simpa only [inner_diskAntiholomorphicArea_eq_integral] using
    diskArea_bessel diskAntiholomorphicArea orthonormal_diskNormalizedAntiholomorphicArea v

end PolyaNeumann

end
