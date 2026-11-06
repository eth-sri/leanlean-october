module
import Mathlib
public import DiscreteEnergyGcdReduction
public import GuthMaynard.Improvement.SamplingFourier
public import Mathlib.Analysis.Fourier.Convolution

@[expose] public section

noncomputable section
open Finset MeasureTheory Set
open scoped FourierTransform Convolution
namespace Montgomery.RationalMoment

section
variable {ι : Type*}
include ι

section
variable (S : Finset ι) (c : ι → ℝ)
include S c

/-- A finite sum of translated compact kernels. The indices may have repeated centers. -/
def finiteSmooth  (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑ i ∈ S, f (t-c i)

section
variable {f : ℝ → ℂ}
include f

theorem finite_smooth_integrable  (hi : Integrable f) : Integrable (finiteSmooth S c f) :=
  integrable_finsetSum _ (fun i _ => hi.comp_sub_right (c i))

theorem finite_smooth_bound  {B : ℝ} (hb : ∀ t, ‖f t‖ ≤ B) (t : ℝ) :
    ‖finiteSmooth S c f t‖ ≤ S.card*B :=
  (norm_sum_le _ _).trans ((sum_le_sum (fun i _ => hb (t-c i))).trans_eq (by simp))

theorem finite_smooth_memLp_two  (hi : Integrable f) {B : ℝ} (hb : ∀ t, ‖f t‖ ≤ B) :
    MemLp (finiteSmooth S c f) 2 := by
  have hs := finite_smooth_integrable S c hi
  apply (memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).mpr
  have hh := hs.norm.mul_bdd hs.norm.aestronglyMeasurable
    (c := (S.card:ℝ)*B) (Filter.Eventually.of_forall (fun t => by
      simpa only [Real.norm_eq_abs,abs_norm] using finite_smooth_bound S c hb t))
  simpa only [pow_two] using hh
end
end


/-- A compact kernel can overlap only when its two centers are close.
This works for arbitrary complex kernels, including the nonsmooth box kernel. -/
theorem finite_smooth_l2_energy  [DecidableEq ι]
    (S : Finset ι) (c : ι → ℝ) {f : ℝ → ℂ} (hi : Integrable f)
    {a B : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hb : ∀ t, ‖f t‖ ≤ B) (hs : ∀ t, a < |t| → f t=0) :
    (∫ t, ‖finiteSmooth S c f t‖^2) ≤
      (2*a*B^2)*(∑ i ∈ S, ∑ j ∈ S, if |c i-c j| ≤ 2*a then (1:ℝ) else 0) := by
  classical
  let bound : ι → ι → ℝ → ℝ := fun i j t =>
    if |c i-c j| ≤ 2*a then
      (Icc (c i-a) (c i+a)).indicator (fun _ => B^2) t else 0
  have hbi (i j : ι) : Integrable (bound i j) := by
    dsimp [bound]
    split_ifs
    · apply (integrable_indicator_iff measurableSet_Icc).mpr
      exact integrableOn_const isCompact_Icc.measure_lt_top.ne
    · exact integrable_zero ℝ ℝ volume
  have hp (i j : ι) (t : ℝ) : ‖f (t-c i)‖*‖f (t-c j)‖ ≤ bound i j t := by
    by_cases hti : a < |t-c i|
    · simp only [hs _ hti,norm_zero,zero_mul]
      simp only [bound,indicator_apply]
      split_ifs <;> positivity
    have hti' : t ∈ Icc (c i-a) (c i+a) := by
      have hh := abs_le.mp (le_of_not_gt hti)
      constructor <;> linarith
    by_cases htj : a < |t-c j|
    · simp only [hs _ htj,norm_zero,mul_zero]
      simp only [bound,indicator_apply]
      split_ifs <;> positivity
    have hc : |c i-c j| ≤ 2*a := by grind
    simp only [bound,ite_eq_left hc,indicator_of_mem hti']
    simpa only [pow_two] using mul_le_mul (hb (t-c i)) (hb (t-c j)) (norm_nonneg _) hB
  have hpoint (t : ℝ) : ‖finiteSmooth S c f t‖^2 ≤ ∑ i ∈ S, ∑ j ∈ S, bound i j t := by
    calc
      _ ≤ (∑ i ∈ S, ‖f (t-c i)‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ = ∑ i ∈ S, ∑ j ∈ S, ‖f (t-c i)‖*‖f (t-c j)‖ := by
        rw [pow_two,sum_mul]
        apply sum_congr rfl
        intro i _
        rw [mul_sum]
      _ ≤ _ := sum_le_sum (fun i _ => sum_le_sum (fun j _ => hp i j t))
  have hnorm := (memLp_two_iff_integrable_sq_norm
    (finite_smooth_integrable S c hi).aestronglyMeasurable).mp (finite_smooth_memLp_two S c hi hb)
  calc
    _ ≤ ∫ t, ∑ i ∈ S, ∑ j ∈ S, bound i j t :=
      integral_mono hnorm (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hbi i j))) hpoint
    _ = ∑ i ∈ S, ∑ j ∈ S, ∫ t, bound i j t := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hbi i j))]
      exact sum_congr rfl (fun i _ => integral_finsetSum _ (fun j _ => hbi i j))
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      dsimp only [bound]
      split_ifs
      · rw [integral_indicator measurableSet_Icc,setIntegral_const,
          Real.volume_real_Icc_of_le (by linarith : c i-a ≤ c i+a)]
        simp only [smul_eq_mul,mul_one]
        ring
      · simp

section
variable (S : Finset ι) (c : ι → ℝ)
    {f : ℝ → ℂ}
include S c f

/-- Exact Fourier transform of the finite smoothing, with the translation
phases kept before taking absolute values. -/
theorem finite_smooth_fourier  (hi : Integrable f) (ξ : ℝ) :
    𝓕 (finiteSmooth S c f) ξ =
      (∑ i ∈ S, GuthMaynard.Improvement.phase (-ξ*c i))*𝓕 f ξ := by
  rw [GuthMaynard.Improvement.fourier_eq_phase_integral]
  simp_rw [finiteSmooth,mul_sum]
  rw [integral_finsetSum _ (fun i _ =>
    GuthMaynard.Improvement.integrable_phase_mul (hi.comp_sub_right (c i)) ξ),sum_mul]
  apply sum_congr rfl
  intro i _
  have hh := GuthMaynard.Improvement.source_kernel_phase_integral f (-ξ) (c i)
  calc
    _ = ∫ t, f (t-c i)*GuthMaynard.Improvement.phase (t*(-ξ)) := by grind
    _ = _ := by simpa only [neg_neg,mul_comm (c i) (-ξ)] using hh

/-- Compact support survives the finite translated smoothing at its literal scale. -/
theorem finite_smooth_support  {a R : ℝ} (hs : ∀ t, a < |t| → f t=0)
    (hc : ∀ i ∈ S, |c i|+a ≤ R) :
    Function.support (finiteSmooth S c f) ⊆ Icc (-R) R := by
  intro t ht
  by_contra hn
  have hab : R < |t| := by
    by_contra hh
    exact hn (abs_le.mp (le_of_not_gt hh))
  apply ht
  apply sum_eq_zero
  grind
end
end



