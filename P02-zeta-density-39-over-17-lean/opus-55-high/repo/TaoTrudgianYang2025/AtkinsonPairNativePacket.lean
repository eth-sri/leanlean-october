module
public import TaoTrudgianYang2025.AtkinsonPairCutoff
public import GenericMeanCounting
public import MathCollab.Density.Stronger.Atkinson.AtkinsonNativeLocalMean
public import MathCollab.Density.Stronger.Atkinson.AtkinsonDyadicGramBudget
import WeylPort.Analytic.RealLaplace

public section
open Finset
namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Atkinson
theorem ExponentPair.atkinson_physical_gram_budget_all_lengths {k l δ ν : ℝ}
    (hpair : ExponentPair k l) (hδ : 0 < δ) (hν : 0 < ν) :
    ∃ F : ℝ, 0 < F ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ (H G L : ℝ) (W : Finset ℝ), H₀ ≤ H →
        H^δ ≤ G → G ≤ Real.sqrt (2*H) → 0 < L →
        Peaks.separatedAt G W → (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, ∀ u ∈ W, |u-t| ≤ L) →
        G^2*H^(-(1/2:ℝ))*
          atkinsonDyadicGramBudget (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W ≤
          F*H^ν*((W.card : ℝ)*H/G+
            (W.card : ℝ)^2*L^k*H^(l-k)*G^(1+k-2*l)) := by
  pm_107 F hF A hA hbudget hpair.atkinson_physical_gram_budget hδ hν
  refine ⟨F,hF,A,hA,?_⟩
  intro H G L W hH hwidth hupper hL hsep hrange hdiam
  have hH0 : 0 < H := by linarith [hA.trans hH]
  pm_650 hG G Real.rpow_pos_of_pos hH0 δ hwidth
  have hmin : 0 < min L H := lt_min hL hH0
  have hd : ∀ t ∈ W, ∀ u ∈ W, |u-t| ≤ min L H := by
    intro t ht u hu
    apply le_min (hdiam t ht u hu)
    pm_5092 hrange
  have hb := hbudget H G (min L H) W hH hwidth hupper hmin
    (min_le_right _ _) hsep hrange hd
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hmin.le (min_le_left _ _) hpair.inTriangle.1) (sq_nonneg _)


/-- The actual native zeta source supplies the full general-pair local packet. -/
theorem ExponentPair.localMeanPacket_native {k l : ℝ} (hpair : ExponentPair k l) :
    Montgomery.CriticalPeak.PairLocalMeanPacket k l := by
  intro δ κ ν hδ hκ hν
  obtain ⟨C,hC,T₀,hT₀,hsource⟩ :=
    localMeanSourceToPrefix_of_stationary localMeanStationaryInput_native δ κ hδ hκ
  obtain ⟨F,hF,H₁,hH₁,hgram⟩ :=
    hpair.atkinson_physical_gram_budget_all_lengths hδ hν
  refine ⟨C,hC,C^2*F,by positivity,max T₀ H₁,hT₀.trans (le_max_left _ _),?_⟩
  intro H G L W hH hG hL hsep hrange hdiam
  by_cases hW : W.Nonempty
  · have hTH : T₀ ≤ H := (le_max_left _ _).trans hH
    pm_207 h1H H₁ H le_max_right hH
    pm_4387
    have hp := sum_atkinsonUndampedDyadicPhaseBound_sq_le_budget N W
    have hphys := hgram H G L W h1H hwidth.1 hwidth.2 hL hsep
      (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1⟩) hdiam
    pm_4388
    calc
      _ ≤ ((C*G*H^(-(1/4:ℝ)))*(∑ t ∈ W, B t))^2 :=
        pow_le_pow_left₀ hsumpos hsum 2
      _ = C^2*G^2*H^(-(1/2:ℝ))*(∑ t ∈ W, B t)^2 := by
        rw [mul_pow,mul_pow,mul_pow,he]
      _ ≤ C^2*G^2*H^(-(1/2:ℝ))*atkinsonDyadicGramBudget N W :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = C^2*(G^2*H^(-(1/2:ℝ))*atkinsonDyadicGramBudget N W) := by ring
      _ ≤ C^2*(F*H^ν*((W.card:ℝ)*H/G+(W.card:ℝ)^2*L^k*H^(l-k)*G^(1+k-2*l))) :=
        mul_le_mul_of_nonneg_left hphys (by positivity)
      _ = _ := by ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hW]
    simp
end TaoTrudgianYang2025
