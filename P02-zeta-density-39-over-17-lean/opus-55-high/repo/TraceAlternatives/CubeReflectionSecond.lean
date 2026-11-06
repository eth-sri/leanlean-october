module
public import TraceAlternatives.CubeSecondMoment
public import DensityEnergyGM.SharpReflectionSecond
import WeylPort.Analytic.RealLaplace

public section

set_option maxHeartbeats 1600000
open Finset GuthMaynard.NativeMoment GuthMaynard.Improvement
namespace Montgomery.RationalMoment

/-- Fixed height dilations and arbitrary translates cost only an upfront
constant in the actual integer-scale cube source moment. -/
theorem ratio_second_cube_uniform_translate (ε B : ℝ)
    (hε : 0 < ε) (_hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ : ℝ, 2 ≤ T → ∀ M : ℕ,
      0 < M → (M : ℝ)^2 ≤ B*T → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      finiteRatioSecond (Ioc M (2*M)) W ≤
        C*T^ε*((M:ℝ)^2+T^(1/3:ℝ)*M)*
          (W.card:ℝ)^(2/3:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/3:ℝ) := by
  pm_69 C hC hBound actual_second_moment_cube_native ε hε
  let D : ℝ := max 1 B
  pm_4884 hD1 D
  have hBD : B ≤ D := le_max_right _ _
  have hD : 0 < D := by linarith
  let q : ℝ := D^(1/3:ℝ)
  pm_792
  intro T t₀ hT M hM hMT W hW
  have hTp : 0 < T := by linarith
  have hDT : T ≤ D*T := le_mul_of_one_le_left hTp.le hD1
  have hBase : InBaseInterval (D*T) (translateSet t₀ W) := by
    pm_4115
    exact ⟨by linarith,by linarith⟩
  pm_2737
  rw [coefficient_one_difference_eq_ratio_second, ← finiteRatioSecond_dyadic,
    finiteRatioSecond_translateSet _ (fun n hn => by have := (mem_Ioc.mp hn).1; omega),
    translateSet_card, discrete_energy_translateSet] at h
  pm_7775
  have hBudget : (M:ℝ)^2 + q*T^(1/3:ℝ)*M ≤ q*((M:ℝ)^2+T^(1/3:ℝ)*M) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ q-1) (sq_nonneg (M:ℝ))]
  calc
    _ ≤ C*(D^ε*T^ε)*((M:ℝ)^2+q*T^(1/3:ℝ)*M)*
        (W.card:ℝ)^(2/3:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/3:ℝ) := h
    _ ≤ C*(D^ε*T^ε)*(q*((M:ℝ)^2+T^(1/3:ℝ)*M))*
        (W.card:ℝ)^(2/3:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/3:ℝ) := by gcongr
    _ = _ := by ring

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
  pm_793
  pm_4117
  pm_4116
  rw [he, ← finiteRatioSecond_scale_two (Ico M (2*M)) W] at h
  apply h.trans
  apply finiteRatioSecond_mono
  pm_67 n hn m hm mem_image.mp
  obtain ⟨hl,hu⟩ := mem_Ico.mp hm
  apply mem_Ioc.mpr
  omega

/-- The actual reflected complete-pair energy with the cube source.
The fixed dilation64 accounts for the exact doubled support. -/
theorem reflection_complete_pair_energy_cube {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ,0<C ∧ ∀ T t₀ : ℝ,2≤T → ∀ M : ℕ,0<M → (M:ℝ)≤4*Real.sqrt T →
      ∀ W : Finset ℝ,(∀ t∈W,t∈Set.Icc t₀ (t₀+T)) →
        MathCollab.Density.completePairEnergy M W ≤
          C*T^η*((M:ℝ)^2+T^(1/3:ℝ)*M)*
            (W.card:ℝ)^(2/3:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/3:ℝ) := by
  pm_7403 ratio_second_cube_uniform_translate
  refine ⟨4*C,by positivity,?_⟩
  intro T t₀ hT M hM hMT W hW
  have hTp : 0 < T := by linarith
  let Q := 2*M-1
  pm_4647 hQ Q
  have hQM : (Q:ℝ) ≤ 2*(M:ℝ) := by
    exact_mod_cast Nat.sub_le (2*M) 1
  have hQ2 : (Q:ℝ)^2 ≤ 64*T := by
    pm_491 hQnon Q
    have hs := Real.sq_sqrt hTp.le
    nlinarith [Real.sqrt_nonneg T]
  have hShape : (Q:ℝ)^2+T^(1/3:ℝ)*Q ≤ 4*((M:ℝ)^2+T^(1/3:ℝ)*M) := by
    have hQsq : (Q:ℝ)^2 ≤ 4*(M:ℝ)^2 := by
      have hh := pow_le_pow_left₀ (Nat.cast_nonneg Q : (0:ℝ)≤Q) hQM 2
      nlinarith
    pm_7684 hQM
    nlinarith [mul_nonneg (Real.rpow_nonneg hTp.le (1/3:ℝ)) (Nat.cast_nonneg M)]
  calc
    _ ≤ finiteRatioSecond (Ioc Q (2*Q)) W := completePairEnergy_le_doubled_ratio hM W
    _ ≤ C*T^η*((Q:ℝ)^2+T^(1/3:ℝ)*Q)*
        (W.card:ℝ)^(2/3:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/3:ℝ) := hBound T t₀ hT Q hQ hQ2 W hW
    _ ≤ C*T^η*(4*((M:ℝ)^2+T^(1/3:ℝ)*M))*
        (W.card:ℝ)^(2/3:ℝ)*(discreteAdditiveEnergy W:ℝ)^(1/3:ℝ) := by gcongr
    _ = _ := by ring

end Montgomery.RationalMoment
