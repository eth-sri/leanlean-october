module
public import AdjacentLargeGcd
public import DiscreteAdditiveEnergy
import WeylPort.Analytic.RealLaplace

public section

set_option maxHeartbeats 1600000
open Finset
namespace Montgomery.RationalMoment

section
variable {η : ℝ} (hη : 0 < η)
include η hη
/-- Four-term energy with all analytic inputs supplied, initially on the
cardinality band handled by moments two through four. -/
theorem discrete_energy_adjacent_band :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N : ℝ, 1 < T → 0 < N → N ≤ T →
      ∀ (a : ℕ → ℂ) (W : Finset ℝ) (V : ℝ),
      T^((5:ℝ)/9) ≤ W.card → (W.card:ℝ)^3 ≤ T^2 →
      (∀ n ∈ GuthMaynard.Improvement.sourceRatioIndices N, ‖a n‖ ≤ 1) →
      0 < V → (∀ t ∈ W, V ≤ ‖GuthMaynard.Improvement.boundedPolynomial N a t‖) →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (discreteAdditiveEnergy W:ℝ) ≤ C*T^η*(N^4*(W.card:ℝ)/V^4+
        (N*(W.card:ℝ)^3+T*(W.card:ℝ)^((5:ℝ)/2)+
          N*T^((1:ℝ)/4)*(W.card:ℝ)^((31:ℝ)/12))/V^2) := by
  pm_418 large_gcd_adjacent_pair
  pm_7049 hRT hlargeW ht
  have hr : (0:ℝ) < W.card := (Real.rpow_pos_of_pos ht _).trans_le hR
  pm_2724
  pm_284
  pm_61 hB B
  pm_2723
  pm_125
  have hlarge' := hlarge T t₀ N hT hN hNT Q (by
    pm_4584 p hp hd
    pm_6
    exact ⟨h1,h2,hl1,hu1,hl2,hu2,hd⟩) W hR hRT hW hsep
  pm_60
  pm_85

/-- Four-term energy on the full cardinality range needed for the missing
second branch. Large cardinalities use the already proved two-term energy;
the remaining band uses the new adjacent rational moments. -/
theorem discrete_additive_energy_adjacent :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ N : ℝ, 1 < T → T^((2:ℝ)/3) ≤ N → N ≤ T →
      ∀ (a : ℕ → ℂ) (W : Finset ℝ) (V : ℝ),
      T^((5:ℝ)/9) ≤ W.card →
      (∀ n ∈ GuthMaynard.Improvement.sourceRatioIndices N, ‖a n‖ ≤ 1) →
      0 < V → (∀ t ∈ W, V ≤ ‖GuthMaynard.Improvement.boundedPolynomial N a t‖) →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (discreteAdditiveEnergy W:ℝ) ≤ C*T^η*(N^4*(W.card:ℝ)/V^4+
        (N*(W.card:ℝ)^3+T*(W.card:ℝ)^((5:ℝ)/2)+
          N*T^((1:ℝ)/4)*(W.card:ℝ)^((31:ℝ)/12))/V^2) := by
  obtain ⟨C,hC,hb⟩ := discrete_energy_adjacent_band hη
  obtain ⟨D,hD,hd⟩ := discrete_additive_energy_two_term (K:=2) (by norm_num) hη
  refine ⟨C+D,by positivity,?_⟩
  intro T t₀ N hT hN hNT a W V hR ha hV hl hW hsep
  pm_438 ht hn N hN
  pm_491 hRn W.card
  by_cases hcap : (W.card:ℝ)^3 ≤ T^2
  · exact (hb T t₀ N hT hn hNT a W V hR hcap ha hV hl hW hsep).trans
      (mul_le_mul_of_nonneg_right (by
        have hh : C ≤ C+D := by linarith
        exact mul_le_mul_of_nonneg_right hh (by positivity)) (by positivity))
  · have hrange : T^((2:ℝ)/3) ≤ W.card := by
      apply (pow_le_pow_iff_left₀ (by positivity) hRn (by norm_num : (3:ℕ) ≠ 0)).mp
      rw [adjacent_rpow_nat ht.le]
      norm_num
      exact (lt_of_not_ge hcap).le
    have hr3 : T^(((2:ℝ)+1)/(2*2+1)) ≤ W.card :=
      (Real.rpow_le_rpow_of_exponent_le hT.le (by norm_num)).trans hrange
    have hdiv : T/N ≤ T^((1:ℝ)/3) := by
      calc
        _ ≤ T/(T^((2:ℝ)/3)) := div_le_div_of_nonneg_left ht.le (by positivity) hN
        _ = T^((1:ℝ)/3) := by
          nth_rw 1 [← Real.rpow_one T]
          rw [← Real.rpow_sub ht]
          congr 1
          norm_num
    have hlen : (T/N)^2 ≤ W.card := by
      calc
        _ ≤ (T^((1:ℝ)/3))^2 := pow_le_pow_left₀ (by positivity) hdiv 2
        _ = T^((2:ℝ)/3) := by rw [adjacent_rpow_nat ht.le]; norm_num
        _ ≤ _ := hrange
    have hh := hd T t₀ N hT hn hNT a W V hr3 hlen ha hV hl hW hsep
    calc
      _ ≤ D*T^η*(N^4*(W.card:ℝ)/V^4+N*(W.card:ℝ)^3/V^2) := hh
      _ ≤ (C+D)*T^η*(N^4*(W.card:ℝ)/V^4+N*(W.card:ℝ)^3/V^2) := by gcongr; linarith
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hx : N*(W.card:ℝ)^3 ≤ N*(W.card:ℝ)^3+T*(W.card:ℝ)^((5:ℝ)/2)+
            N*T^((1:ℝ)/4)*(W.card:ℝ)^((31:ℝ)/12) := by
          have h1 : 0 ≤ T*(W.card:ℝ)^((5:ℝ)/2) := by positivity
          have h2 : 0 ≤ N*T^((1:ℝ)/4)*(W.card:ℝ)^((31:ℝ)/12) := by positivity
          linarith
        have hh := div_le_div_of_nonneg_right hx (sq_nonneg V)
        linarith only [hh]
end

end Montgomery.RationalMoment
