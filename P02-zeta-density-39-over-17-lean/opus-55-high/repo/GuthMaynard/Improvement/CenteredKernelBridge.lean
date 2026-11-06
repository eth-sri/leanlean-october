module
public import GuthMaynard.Improvement.CenteredTruncation
import WeylPort.Analytic.RealLaplace

public section
open MeasureTheory Set
open scoped ContDiff FourierTransform
namespace GuthMaynard.Improvement

theorem logModulated_eq_phase (a : ℝ → ℂ) (s x : ℝ) :
    logModulated a s x = a x*phase (s*mellinFrequency x) := by
  pm_8451 mellinFrequency_phase logModulated

theorem logModulated_fourier_integral (a : ℝ → ℂ) (s ξ : ℝ) :
    𝓕 (logModulated a s) ξ = ∫ x, a x*phase (s*mellinFrequency x-ξ*x) := by
  rw [fourier_eq_phase_integral]
  apply integral_congr_ae
  filter_upwards with x
  rw [logModulated_eq_phase]
  calc
    _ = a x*(phase (-ξ*x)*phase (s*mellinFrequency x)) := by ring
    _ = _ := by rw [← phase_add]; congr 2; ring

section
variable {a : ℝ → ℂ}
include a
/-- The actual retained kernel on the cutoff interval is the finite Fourier
sum used by centeredKernel_truncation, including its exact L factor. -/
theorem retainedPoissonKernel_fourier {l u : ℝ}
    (ha : Measurable a) {B : ℝ} (hb : ∀ x, ‖a x‖ ≤ B)
    (hs : ∀ x, x ∉ Icc l u → a x = 0) (L : ℝ) (S : Finset ℤ) (s : ℝ) :
    retainedPoissonKernel (volume.restrict (Icc l u)) a L S s =
      (L:ℂ)*∑ m ∈ S, 𝓕 (logModulated a s) (L*(m:ℝ)) := by
  rw [retainedPoissonKernel_expanded _ ha hb]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [logModulated_fourier_integral]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  grind

/-- Joint measurability before integrating the continuous centered term. -/
theorem logModulated_measurable (ha : Measurable a) :
    Measurable (fun z : ℝ × ℝ => logModulated a z.1 z.2) := by
  unfold logModulated
  fun_prop

theorem centeredKernel_measurable (ha : Measurable a) (l u L : ℝ) :
    Measurable (centeredKernel a l u L) := by
  have hi : Measurable (fun s : ℝ => ∫ x, logModulated a s x) :=
    (logModulated_measurable ha).stronglyMeasurable.integral_prod_right'.measurable
  have hf : ∀ x : ℝ, Measurable (fun s => logModulated a s x) := by
    intro x
    unfold logModulated
    fun_prop
  unfold centeredKernel
  fun_prop
end

theorem centeredKernel_count {l u L : ℝ} (hl : 0 < l) (hL : 1 ≤ L) :
    ((Finset.Icc ⌈l*L⌉ ⌊u*L⌋).card:ℝ) ≤ (max 0 u+1)*L := by
  have hLp : 0 < L := by linarith
  by_cases h : ⌈l*L⌉ ≤ ⌊u*L⌋
  · have hz : 0 ≤ ⌊u*L⌋+1-⌈l*L⌉ := by omega
    have he : ((Finset.Icc ⌈l*L⌉ ⌊u*L⌋).card:ℤ) = ⌊u*L⌋+1-⌈l*L⌉ := by
      rw [Int.card_Icc,Int.toNat_of_nonneg hz]
    have her : ((Finset.Icc ⌈l*L⌉ ⌊u*L⌋).card:ℝ) = (⌊u*L⌋:ℝ)+1-(⌈l*L⌉:ℝ) := by exact_mod_cast he
    rw [her]
    have hc : 0 ≤ (⌈l*L⌉:ℝ) := le_trans (by positivity) (Int.le_ceil _)
    have hf := Int.floor_le (u*L)
    nlinarith [le_max_right 0 u,mul_le_mul_of_nonneg_right (le_max_right 0 u) hLp.le]
  · rw [Finset.Icc_eq_empty_of_lt (lt_of_not_ge h)]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

/-- Uniform O(L) bound for the actual centered kernel, derived from the
literal finite sum and compactly supported continuous integral. -/
theorem centeredKernel_uniform_bound {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hs : ∀ x, x ∉ Icc l u → a x = 0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L s : ℝ, 1 ≤ L → ‖centeredKernel a l u L s‖ ≤ D*L := by
  pm_8601 B hB ha.continuous.continuousOn C
  pm_4918 hC C le_max_left
  have hb : ∀ x, ‖a x‖ ≤ C := by
    intro x
    pm_4540 hB
    · simp only [hs x hx,norm_zero]; exact hC
  refine ⟨((max 0 u+1)+(u-l))*C,by positivity,?_⟩
  intro L s hL
  have hLp : 0 < L := by linarith
  have hn : ∀ x, ‖logModulated a s x‖ ≤ C := by
    intro x
    rw [logModulated_eq_phase,norm_mul,phase_norm,mul_one]
    exact hb x
  pm_4579
  have hInt : ‖∫ x, logModulated a s x‖ ≤ C*(u-l) := by
    have hh := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := Icc l u) isCompact_Icc.measure_lt_top (fun x _ => hn x)
    rwa [setIntegral_eq_integral_of_forall_compl_eq_zero hz,Real.volume_real_Icc_of_le hlu] at hh
  unfold centeredKernel
  calc
    _ ≤ ‖∑ d ∈ Finset.Icc ⌈l*L⌉ ⌊u*L⌋, logModulated a s ((d:ℝ)/L)‖ +
        ‖(L:ℂ)*(∫ x, logModulated a s x)‖ := norm_sub_le _ _
    _ ≤ (∑ _d ∈ Finset.Icc ⌈l*L⌉ ⌊u*L⌋, C) + L*(C*(u-l)) := by
      apply add_le_add
      · exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun d _ => hn _))
      · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hLp]
        exact mul_le_mul_of_nonneg_left hInt hLp.le
    _ ≤ ((max 0 u+1)*L)*C+L*(C*(u-l)) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      gcongr
      exact centeredKernel_count hl hL
    _ = _ := by ring

end GuthMaynard.Improvement
