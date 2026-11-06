module
public import DensityEnergyGM.RealScaleSecondMoment
public import DensityEnergyGM.FiveTermEnergyUniform
public import DensityEnergyGM.EnergyCenteredReflection

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset GuthMaynard.NativeMoment GuthMaynard.Improvement
namespace Montgomery.RationalMoment

theorem norm_gmR_translateSet (c : ℝ) (W : Finset ℝ) {r : ℝ} (hr : 0 < r) :
    ‖gmR (translateSet c W) r‖ = ‖gmR W r‖ := by
  rw [native_ratio_sum_eq_phase _ hr, native_ratio_sum_eq_phase _ hr]
  have hsum : (∑ t ∈ translateSet c W, phase r t) =
      (∑ t ∈ W, phase r t) * star (phase r c) := by
    unfold translateSet
    rw [sum_image (by intro x hx y hy h; change x-c=y-c at h; linarith), sum_mul]
    exact sum_congr rfl (fun t _ => (phase_time_difference r t c).symm)
  rw [hsum, norm_mul, norm_star]
  have hunit : ‖phase r c‖ = 1 := by
    rw [← exponentialPhase_log, exponentialPhase_norm]
  rw [hunit, mul_one]

theorem finiteRatioSecond_translateSet (A : Finset ℕ)
    (hA : ∀ n ∈ A, 0 < n) (c : ℝ) (W : Finset ℝ) :
    finiteRatioSecond A (translateSet c W) = finiteRatioSecond A W := by
  unfold finiteRatioSecond
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro m hm
  rw [norm_gmR_translateSet c W (div_pos
    (by exact_mod_cast hA n hn) (by exact_mod_cast hA m hm))]



/-- The reflected dyadic polynomial differs from the positive-frequency sum
only by a common unit phase; the complete W x W energy is unchanged. -/
theorem completePairEnergy_eq_phase_difference {M : ℕ} (hM : 0 < M) (W : Finset ℝ) :
    MathCollab.Density.completePairEnergy M W =
      ∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ Ico M (2*M), phase n (t-u)‖^2 := by
  have hNorm (v : ℝ) : ‖MathCollab.Density.dyadicPolynomial M v‖ =
      ‖∑ n ∈ Ico M (2*M), phase n v‖ := by
    have hEq : MathCollab.Density.dyadicPolynomial M v =
        (∑ n ∈ Ico M (2*M), phase n v)*star (phase M v) := by
      unfold MathCollab.Density.dyadicPolynomial
      rw [sum_mul]
      apply sum_congr rfl
      intro n hn
      rw [density_phase_eq,phase_frequency_ratio
        (by exact_mod_cast hM.trans_le (mem_Ico.mp hn).1) (by exact_mod_cast hM)]
    rw [hEq,norm_mul,norm_star]
    have hUnit : ‖phase M v‖=1 := by rw [← exponentialPhase_log,exponentialPhase_norm]
    rw [hUnit,mul_one]
  unfold MathCollab.Density.completePairEnergy
  simp_rw [hNorm]



