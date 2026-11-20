module

public import RequestProject.DiskAreaBessel
public import RequestProject.SobolevMultiplier
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# One full Sobolev derivative from physical disk mass forcing

The nonzero-mode coefficient has multiplier sqrt(1+|n|)/(sqrt(2π)|n|).
The area Bessel estimate bounds the entire H¹ Fourier norm, rather than
only the individual coefficients. Frequency zero is removed explicitly.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real
open scoped ComplexConjugate

/-- The zero mode vanishes since its scale has denominator zero. -/
def diskMassForcingCoeff (v : L2 (ball (0 : ℂ) 1)) (n : ℤ) : ℂ :=
  (↑(Real.sqrt (sobWeight n) / (Real.sqrt (2 * π) * |(n : ℝ)|)) : ℂ) * inner ℂ (diskAreaMode n) v

private lemma diskMassForcing_weight (v : L2 (ball (0 : ℂ) 1)) (n : ℤ) :
    (sobWeight n * ‖diskMassForcingCoeff v n‖)^2 ≤
      (2 / π) * (sobWeight n * ‖inner ℂ (diskAreaMode n) v‖^2) := by
  by_cases hn : n = 0
  · subst n
    simpa [diskMassForcingCoeff] using show 0 ≤
      (2 / π) * (sobWeight 0 * ‖inner ℂ (diskAreaMode 0) v‖^2) by have := sobWeight_pos 0; positivity
  have h : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
  have hratio : sobWeight n / |(n : ℝ)| ≤ 2 :=
    (div_le_iff₀ (by linarith)).mpr (by unfold sobWeight; linarith)
  have hsq := (sq_le_sq₀ (div_nonneg (sobWeight_pos n).le (abs_nonneg _)) (by norm_num)).mpr hratio
  rw [diskMassForcingCoeff, norm_mul, Complex.norm_of_nonneg (by positivity), mul_pow, mul_pow,
    div_pow, mul_pow, Real.sq_sqrt (sobWeight_pos n).le, Real.sq_sqrt two_pi_pos.le]
  calc
    _ = (sobWeight n / |(n : ℝ)|)^2 *
        ((sobWeight n / (2 * π)) * ‖inner ℂ (diskAreaMode n) v‖^2) := by ring
    _ ≤ 2^2 * ((sobWeight n / (2 * π)) * ‖inner ℂ (diskAreaMode n) v‖^2) := by have := sobWeight_pos n; gcongr
    _ = _ := by ring

private theorem diskMassForcingCoeff_h1 (v : L2 (ball (0 : ℂ) 1)) :
    IsSobolevSeq 1 (diskMassForcingCoeff v) ∧
      sobNormSq 1 (diskMassForcingCoeff v) ≤ 4 * ‖v‖ ^ 2 := by
  have hw (n : ℤ) : sobWeight n = diskAreaWeight n := by
    rw [sobWeight, diskAreaWeight, ← Int.cast_abs, add_comm, ← Int.natCast_natAbs, Int.cast_natCast]
  obtain ⟨hs, hb⟩ := diskAreaMode_bessel v
  simp_rw [← hw] at hs hb
  have hsum := hs.mul_left (2 / π)
  have h := Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (diskMassForcing_weight v) hsum
  refine ⟨by simpa only [IsSobolevSeq, Real.rpow_one] using h, ?_⟩
  simp only [sobNormSq, Real.rpow_one]
  calc
    _ ≤ (2 / π) * ∑' n : ℤ, sobWeight n * ‖inner ℂ (diskAreaMode n) v‖^2 := by
      rw [← tsum_mul_left]; exact h.tsum_le_tsum (diskMassForcing_weight v) hsum
    _ ≤ (2 / π) * (π * ‖v‖^2) := by gcongr
    _ = 2 * ‖v‖^2 := by field_simp [Real.pi_ne_zero]
    _ ≤ _ := by nlinarith [sq_nonneg ‖v‖]

theorem diskMassForcingCoeff_add (v w : L2 (ball (0 : ℂ) 1)) (n : ℤ) :
    diskMassForcingCoeff (v + w) n = diskMassForcingCoeff v n + diskMassForcingCoeff w n := by
  simp [diskMassForcingCoeff, inner_add_right, mul_add]

theorem diskMassForcingCoeff_smul (c : ℂ) (v : L2 (ball (0 : ℂ) 1)) (n : ℤ) :
    diskMassForcingCoeff (c • v) n = c * diskMassForcingCoeff v n := by
  simp [diskMassForcingCoeff, inner_smul_right, mul_left_comm]

def diskMassForcingH1Lin : L2 (ball (0 : ℂ) 1) →ₗ[ℂ] L2Z where
  toFun v := ⟨fun n => (sobWeight n : ℂ) * diskMassForcingCoeff v n,
    memℓp_two_iff_summable.mpr (by
      simpa only [IsSobolevSeq, Real.rpow_one, norm_mul,
        Complex.norm_of_nonneg (sobWeight_pos _).le] using (diskMassForcingCoeff_h1 v).1)⟩
  map_add' v w := by
    apply lp.ext
    funext n
    change (sobWeight n : ℂ) * diskMassForcingCoeff (v + w) n = _
    simp only [diskMassForcingCoeff_add, lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' c v := by
    apply lp.ext
    funext n
    change (sobWeight n : ℂ) * diskMassForcingCoeff (c • v) n =
      c * ((sobWeight n : ℂ) * diskMassForcingCoeff v n)
    rw [diskMassForcingCoeff_smul]
    ring

theorem norm_diskMassForcingH1Lin_le (v : L2 (ball (0 : ℂ) 1)) :
    ‖diskMassForcingH1Lin v‖ ≤ 2 * ‖v‖ := by
  have hsq : ‖diskMassForcingH1Lin v‖ ^ 2 ≤ (2 * ‖v‖) ^ 2 := by
    rw [norm_sq_L2Z]
    change (∑' n : ℤ, ‖(sobWeight n : ℂ) * diskMassForcingCoeff v n‖ ^ 2) ≤ _
    simp only [norm_mul, Complex.norm_of_nonneg (sobWeight_pos _).le]
    have h := (diskMassForcingCoeff_h1 v).2
    grind [sobNormSq, Real.rpow_one]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

def diskMassForcingH1 : L2 (ball (0 : ℂ) 1) →L[ℂ] L2Z :=
  diskMassForcingH1Lin.mkContinuous 2 norm_diskMassForcingH1Lin_le


end PolyaNeumann

end
