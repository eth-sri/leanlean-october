module
public import TraceAlternatives.CubeSecondMoment
public import DensityEnergyGM.SharpReflectionSecond

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset GuthMaynard.NativeMoment GuthMaynard.Improvement
namespace Montgomery.RationalMoment


/-- Integer scaling preserves the literal positive ratio-kernel moment. -/
theorem finiteRatioSecond_scale_two (A : Finset ℕ) (W : Finset ℝ) :
    finiteRatioSecond (A.image (fun n => 2*n)) W = finiteRatioSecond A W := by
  classical
  have hinj : Set.InjOn (fun n : ℕ => 2*n) A := by
    intro n hn m hm he
    change 2*n=2*m at he
    omega
  unfold finiteRatioSecond
  rw [sum_image hinj]
  apply sum_congr rfl
  intro n hn
  rw [sum_image hinj]
  apply sum_congr rfl
  intro m hm
  simp only [Nat.cast_mul, Nat.cast_ofNat, mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)]

/-- Doubling embeds Ico M(2M) in the genuine dyadic interval
Ioc(2M-1)(2(2M-1)), including M=1 exactly. -/
theorem completePairEnergy_le_doubled_ratio {M : ℕ} (hM : 0 < M) (W : Finset ℝ) :
    MathCollab.Density.completePairEnergy M W ≤
      finiteRatioSecond (Ioc (2*M-1) (2*(2*M-1))) W := by
  have hA : ∀ n ∈ Ico M (2*M), 0<n := fun n hn => hM.trans_le (mem_Ico.mp hn).1
  rw [completePairEnergy_eq_phase_difference hM]
  have h := dirichlet_difference_energy_le (Ico M (2*M)) hA W (fun _ => 1) (by simp)
  simp only [one_mul] at h
  have he : (∑ n ∈ Ico M (2*M), ∑ m ∈ Ico M (2*M),
      ‖∑ t ∈ W, phase ((n:ℝ)/m) t‖^2) = finiteRatioSecond (Ico M (2*M)) W := by
    unfold finiteRatioSecond
    apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro m hm
    rw [native_ratio_sum_eq_phase W (div_pos
      (by exact_mod_cast hA n hn) (by exact_mod_cast hA m hm))]
  rw [he, ← finiteRatioSecond_scale_two (Ico M (2*M)) W] at h
  apply h.trans
  apply finiteRatioSecond_mono
  intro n hn
  obtain ⟨m,hm,rfl⟩ := mem_image.mp hn
  obtain ⟨hl,hu⟩ := mem_Ico.mp hm
  apply mem_Ioc.mpr
  omega


