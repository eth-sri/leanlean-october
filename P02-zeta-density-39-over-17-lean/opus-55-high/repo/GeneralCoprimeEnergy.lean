module
public import GeneralRationalEnergy
public import RationalLargeGcdEnergy
import WeylPort.Analytic.RealLaplace

public section

set_option maxHeartbeats 1600000
open Finset
namespace Montgomery.RationalMoment

theorem coprime_dyadic_adjacent_general {K : ℕ} (hK : 1 ≤ K) {η B : ℝ} (hη : 0 < η) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ M : ℝ, 1 < T → 0 ≤ M → M ≤ B*T →
      ∀ Q : Finset (ℕ × ℕ),
      (∀ q ∈ Q, 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2 ∧
        M < q.1 ∧ (q.1:ℝ) ≤ 2*M ∧ M < q.2 ∧ (q.2:ℝ) ≤ 2*M) →
      ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ q ∈ Q, ‖∑ t ∈ W, phase (pairRatio q) t‖^2) ≤
        C*T^η*(M*(W.card:ℝ)^2+M^2*(W.card:ℝ)^(2-1/(K:ℝ))+
          M*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := by
  obtain ⟨C,hC,hb⟩ := rational_energy_adjacent_unrestricted hK hη (B:=2*B) (by linarith)
  refine ⟨4*C,by positivity,?_⟩
  intro T t₀ M hT hM hMT Q hQ W hW hsep
  by_cases he : Q.Nonempty
  · obtain ⟨q,hq⟩ := he
    pm_238
    have hrat : ∀ r ∈ Q.image pairRatio,
        0 < r ∧ r.den ≤ ⌊2*M⌋₊ ∧ |Real.log (r:ℝ)| ≤ 1 := by
      pm_67 r hr p hp mem_image.mp
      pm_303
    pm_1320 p hp
    have hh := hb T t₀ hT ⌊2*M⌋₊ hH (hf.trans (by linarith))
      (Q.image pairRatio) hrat W hW hsep
    calc
      _ ≤ C*T^η*((⌊2*M⌋₊:ℝ)*(W.card:ℝ)^2+
          (⌊2*M⌋₊:ℝ)^2*(W.card:ℝ)^(2-1/(K:ℝ))+
          (⌊2*M⌋₊:ℝ)*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := hh
      _ ≤ C*T^η*((2*M)*(W.card:ℝ)^2+(2*M)^2*(W.card:ℝ)^(2-1/(K:ℝ))+
          (2*M)*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := by gcongr
      _ ≤ _ := by
        pm_2720 M
        have hi : (2*M)*(W.card:ℝ)^2+(2*M)^2*(W.card:ℝ)^(2-1/(K:ℝ))+
            (2*M)*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1))) ≤
            4*(M*(W.card:ℝ)^2+M^2*(W.card:ℝ)^(2-1/(K:ℝ))+
              M*T^(1/(2*(K:ℝ)))*(W.card:ℝ)^(2-(2*(K:ℝ)+1)/(2*K*(K+1)))) := by nlinarith
        pm_328 mul_le_mul_of_nonneg_left hi
  · rw [not_nonempty_iff_eq_empty.mp he,sum_empty]
    positivity


end Montgomery.RationalMoment
