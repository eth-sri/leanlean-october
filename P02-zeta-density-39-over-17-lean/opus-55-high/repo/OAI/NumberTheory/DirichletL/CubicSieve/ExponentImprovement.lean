module
public import OAI.NumberTheory.DirichletL.CubicSieve.FullImprovement
public import OAI.NumberTheory.DirichletL.HeathBrownIteration
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section

def enlargementExponent (ξ : ℝ) : ℝ := (6*ξ-5)/(3*ξ-1)

lemma enlargement_bounds (ξ : ℝ) (hξ : (4/3 : ℝ) ≤ ξ) :
    1 ≤ enlargementExponent ξ ∧ enlargementExponent ξ ≤ SevenEighths.HeathBrownIteration.step ξ := by
  have hd : 0 < 3*ξ-1 := by linarith
  constructor
  · unfold enlargementExponent
    apply (one_le_div hd).mpr
    linarith
  · unfold enlargementExponent SevenEighths.HeathBrownIteration.step
    exact div_le_div_of_nonneg_right (by linarith) hd.le

section
variable (ξ : ℝ) (hξ : (4/3 : ℝ) ≤ ξ)
include ξ hξ
lemma enlargement_cross_identity :
    (enlargementExponent ξ+1)*(2/3 : ℝ) = SevenEighths.HeathBrownIteration.step ξ := by
  pm_3788

lemma enlargement_secondary_identity :
    enlargementExponent ξ*(1-ξ)+(2*ξ-1) = SevenEighths.HeathBrownIteration.step ξ := by
  pm_3788
end

theorem enlarged_improved_shape (M N ξ : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hξ : (4/3 : ℝ) ≤ ξ) :
    let T := max M (N^(enlargementExponent ξ))
    T+(T*N)^(2/3 : ℝ)+T^(1-ξ)*N^(2*ξ-1) ≤
      3*(M+N^(SevenEighths.HeathBrownIteration.step ξ)+(M*N)^(2/3 : ℝ)) := by
  let α := enlargementExponent ξ
  let β := SevenEighths.HeathBrownIteration.step ξ
  let T := max M (N^α)
  pm_3779
  have hαβ : α ≤ β := (enlargement_bounds ξ hξ).2
  pm_6316 hNb N β hN0.le
  pm_5605 hcross
  have ht : T ≤ M+N^β := by
    apply max_le
    grind
    · exact (Real.rpow_le_rpow_of_exponent_le hN hαβ).trans (le_add_of_nonneg_left hM0.le)
  have hnx : (N^α*N)^(2/3 : ℝ) = N^β := by
    conv_lhs => arg 1; arg 2; rw [← Real.rpow_one N]
    rw [← Real.rpow_add hN0, ← Real.rpow_mul hN0.le, enlargement_cross_identity ξ hξ]
  have htc : (T*N)^(2/3 : ℝ) ≤ (M*N)^(2/3 : ℝ)+N^β := by
    by_cases hm : M ≤ N^α
    grind
    grind
  have hts : T^(1-ξ)*N^(2*ξ-1) ≤ N^β := by
    have hp := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN0 α)
      (le_max_right M (N^α)) (show 1-ξ ≤ 0 by linarith)
    calc
      _ ≤ (N^α)^(1-ξ)*N^(2*ξ-1) :=
        mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hN0.le _)
      _ = N^β := by
        rw [← Real.rpow_mul hN0.le, ← Real.rpow_add hN0, enlargement_secondary_identity ξ hξ]
  change T+(T*N)^(2/3 : ℝ)+T^(1-ξ)*N^(2*ξ-1) ≤ 3*(M+N^β+(M*N)^(2/3 : ℝ))
  linarith

theorem HasCubicExponent.improve {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) < ξ) (hξ2 : ξ ≤ 2) :
    HasCubicExponent (SevenEighths.HeathBrownIteration.step ξ) := by
  intro ε hε
  let θ := min (ε/14) (1/4 : ℝ)
  pm_251 hθ θ
  have hθsmall : θ < 1/2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hθε : 7*θ ≤ ε := by
    have hh : θ ≤ ε/14 := min_le_left _ _
    linarith
  pm_3547 C hC hb h.full_improved hξ.le hξ2 θ hθ hθsmall
  refine ⟨3*C, by positivity, ?_⟩
  intro M N hM hN
  let T := max M (N^(enlargementExponent ξ))
  pm_5105 hT T hM.trans
  pm_3779
  have hp : N^(7*θ) ≤ (M*N)^ε :=
    (Real.rpow_le_rpow_of_exponent_le hN hθε).trans
      (Real.rpow_le_rpow hN0.le (by nlinarith) hε.le)
  have ht := enlarged_improved_shape M N ξ hM hN hξ.le
  have hshape : 0 ≤ M+N^(SevenEighths.HeathBrownIteration.step ξ)+(M*N)^(2/3 : ℝ) := by positivity
  calc
    _ ≤ sieveNorm T N := sieveNorm_mono (le_max_left _ _) le_rfl
    _ ≤ elementSieveNorm T N := sieveNorm_le_elementSieveNorm T N
    _ ≤ C*N^(7*θ)*(T+(T*N)^(2/3 : ℝ)+T^(1-ξ)*N^(2*ξ-1)) := hb T N hT hN
    _ ≤ C*N^(7*θ)*(3*(M+N^(SevenEighths.HeathBrownIteration.step ξ)+(M*N)^(2/3 : ℝ))) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ ≤ C*(M*N)^ε*(3*(M+N^(SevenEighths.HeathBrownIteration.step ξ)+(M*N)^(2/3 : ℝ))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC.le) (by positivity)
    _ = _ := by ring

end
end SevenEighths.CubicSieve

end OAI
