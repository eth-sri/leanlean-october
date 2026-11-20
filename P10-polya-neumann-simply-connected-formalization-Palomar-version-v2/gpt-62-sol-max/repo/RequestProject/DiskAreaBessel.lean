module

public import RequestProject.DiskAreaGram

/-!
# Bessel estimates for physical area moments on the disk

Use the constant once, positive holomorphic powers and negative antiholomorphic powers.
The area Gram matrix gives the normalizations in physical area measure.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real
open scoped ComplexConjugate InnerProductSpace

def diskSmoothArea {f : ℂ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    L2 (ball (0 : ℂ) 1) := (diskHarmonicCutoff_testFunction hf).memLp' 2 |>.toLp _

private theorem diskSmoothArea_ae {f : ℂ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    (diskSmoothArea hf : ℂ → ℂ) =ᵐ[volume.restrict (ball (0 : ℂ) 1)] f := by
  filter_upwards [(diskHarmonicCutoff_testFunction hf).memLp' 2 |>.coeFn_toLp,
    ae_restrict_mem measurableSet_ball] with z hz hzD
  exact hz.trans (diskHarmonicCutoff_eq_closedDisk _ (ball_subset_closedBall hzD))

def diskHolomorphicArea (m : ℕ) : L2 (ball (0 : ℂ) 1) :=
  diskSmoothArea (contDiff_diskHolomorphicMode m)

def diskAntiholomorphicArea (m : ℕ) : L2 (ball (0 : ℂ) 1) :=
  diskSmoothArea (contDiff_diskAntiholomorphicMode m)

theorem diskHolomorphicArea_ae (m : ℕ) :
    (diskHolomorphicArea m : ℂ → ℂ) =ᵐ[volume.restrict (ball (0 : ℂ) 1)]
      fun z => z ^ m := diskSmoothArea_ae _

theorem diskAntiholomorphicArea_ae (m : ℕ) :
    (diskAntiholomorphicArea m : ℂ → ℂ) =ᵐ[volume.restrict (ball (0 : ℂ) 1)]
      fun z => conj z ^ m := diskSmoothArea_ae _

theorem inner_diskHolomorphicArea (m n : ℕ) :
    ⟪diskHolomorphicArea m, diskHolomorphicArea n⟫_ℂ =
      if m = n then (π : ℂ) / ((m + 1 : ℕ) : ℂ) else 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ z in ball (0 : ℂ) 1, z ^ n * conj z ^ m := by
      apply integral_congr_ae
      filter_upwards [diskHolomorphicArea_ae m, diskHolomorphicArea_ae n] with x; simp_all
    _ = _ := by
      rw [integral_disk_area_monomials]
      lia

theorem inner_diskAntiholomorphicArea (m n : ℕ) :
    ⟪diskAntiholomorphicArea m, diskAntiholomorphicArea n⟫_ℂ =
      if m = n then (π : ℂ) / ((m + 1 : ℕ) : ℂ) else 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ z in ball (0 : ℂ) 1, z ^ m * conj z ^ n := by
      apply integral_congr_ae
      filter_upwards [diskAntiholomorphicArea_ae m, diskAntiholomorphicArea_ae n] with x; simp_all [mul_assoc, mul_comm, mul_left_comm]
    _ = _ := integral_disk_area_monomials m n

/-- The area test for the signed Fourier mode. -/
def diskAreaMode : ℤ → L2 (ball (0 : ℂ) 1)
  | Int.ofNat m => diskHolomorphicArea m
  | Int.negSucc m => diskAntiholomorphicArea (m + 1)

private lemma inner_diskArea_cross (m n : ℕ) :
    ⟪diskHolomorphicArea m, diskAntiholomorphicArea (n + 1)⟫_ℂ = 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ z in ball (0 : ℂ) 1, z ^ (0 : ℕ) * conj z ^ (m + (n + 1)) := by
      apply integral_congr_ae
      filter_upwards [diskHolomorphicArea_ae m, diskAntiholomorphicArea_ae (n + 1)] with z hm hn
      simp [hm, hn, ← pow_add, Nat.add_comm]
    _ = _ := by rw [integral_disk_area_monomials]; simp

def diskAreaWeight (n : ℤ) : ℝ := (n.natAbs : ℝ) + 1

private theorem inner_diskAreaMode (m n : ℤ) :
    ⟪diskAreaMode m, diskAreaMode n⟫_ℂ = if m = n then (π : ℂ) / (diskAreaWeight m : ℂ) else 0 := by
  cases m <;> cases n
  · simp [diskAreaMode, inner_diskHolomorphicArea, diskAreaWeight]
  · simp [diskAreaMode, inner_diskArea_cross]
  · rw [← inner_conj_symm]; simp [diskAreaMode, inner_diskArea_cross]
  · simp [diskAreaMode, inner_diskAntiholomorphicArea, diskAreaWeight, Int.natAbs_negSucc]

private def diskAreaScale (n : ℤ) : ℂ := (Real.sqrt (diskAreaWeight n / π) : ℝ)

private theorem orthonormal_diskAreaMode :
    Orthonormal ℂ (fun n : ℤ => diskAreaScale n • diskAreaMode n) := by
  rw [orthonormal_iff_ite]
  intro m n
  by_cases h : m = n
  · subst n
    simp only [inner_smul_left, inner_smul_right, inner_diskAreaMode, ite_true, diskAreaScale,
      Complex.conj_ofReal]
    have hh : (Real.sqrt (diskAreaWeight m / π) : ℂ)^2 = (diskAreaWeight m / π : ℝ) := by
      exact_mod_cast Real.sq_sqrt (by unfold diskAreaWeight; positivity : 0 ≤ diskAreaWeight m / π)
    rw [← mul_assoc, ← sq, hh]
    norm_cast
    field_simp [Real.pi_ne_zero, show diskAreaWeight m ≠ 0 by unfold diskAreaWeight; positivity]
  · simp [inner_smul_left, inner_smul_right, inner_diskAreaMode, h]

/-- The weighted area-moment bound for the whole signed family. -/
theorem diskAreaMode_bessel (v : L2 (ball (0 : ℂ) 1)) :
    Summable (fun n : ℤ => diskAreaWeight n * ‖⟪diskAreaMode n, v⟫_ℂ‖ ^ 2) ∧
      (∑' n : ℤ, diskAreaWeight n * ‖⟪diskAreaMode n, v⟫_ℂ‖ ^ 2) ≤ π * ‖v‖ ^ 2 := by
  have he (n : ℤ) : π * ‖⟪diskAreaScale n • diskAreaMode n, v⟫_ℂ‖ ^ 2 =
      diskAreaWeight n * ‖⟪diskAreaMode n, v⟫_ℂ‖ ^ 2 := by
    simp only [inner_smul_left, norm_mul, Complex.norm_conj, diskAreaScale,
      Complex.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (by unfold diskAreaWeight; positivity : 0 ≤ diskAreaWeight n / π)]
    field_simp [Real.pi_ne_zero]
  exact ⟨((orthonormal_diskAreaMode.inner_products_summable v).mul_left π).congr he,
    calc
      _ = π * ∑' n : ℤ, ‖⟪diskAreaScale n • diskAreaMode n, v⟫_ℂ‖ ^ 2 := by
        simp only [← tsum_mul_left, he]
      _ ≤ _ := mul_le_mul_of_nonneg_left (orthonormal_diskAreaMode.tsum_inner_products_le v) Real.pi_pos.le⟩

end PolyaNeumann

end
