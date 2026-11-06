module
public import AdjacentRationalEnergy
public import RationalLargeGcdEnergy
import WeylPort.Analytic.RealLaplace

public section

set_option maxHeartbeats 1600000
open Finset
namespace Montgomery.RationalMoment

section
variable {η : ℝ} (hη : 0 < η)
include η hη
theorem coprime_dyadic_adjacent_second :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ M : ℝ, 1 < T → 0 ≤ M → M ≤ T →
      ∀ Q : Finset (ℕ × ℕ),
      (∀ q ∈ Q, 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2 ∧
        M < q.1 ∧ (q.1:ℝ) ≤ 2*M ∧ M < q.2 ∧ (q.2:ℝ) ≤ 2*M) →
      ∀ W : Finset ℝ, T^((5:ℝ)/9) ≤ W.card → (W.card:ℝ)^3 ≤ T^2 →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ q ∈ Q, ‖∑ t ∈ W, phase (pairRatio q) t‖^2) ≤
        C*T^η*(M*(W.card:ℝ)^2+M^2*(W.card:ℝ)^((3:ℝ)/2)+
          M*T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12)) := by
  pm_7077 rational_energy_adjacent_second hη
  intro T t₀ M hT hM hMT Q hQ W hR hRT hW hsep
  by_cases he : Q.Nonempty
  · obtain ⟨q,hq⟩ := he
    pm_238
    have hrat : ∀ r ∈ Q.image pairRatio,
        0 < r ∧ r.den ≤ ⌊2*M⌋₊ ∧ |Real.log (r:ℝ)| ≤ 1 := by
      pm_67 r hr p hp mem_image.mp
      pm_303
    pm_1320 p hp
    have hh := hb T t₀ hT ⌊2*M⌋₊ hH (hf.trans (by linarith))
      (Q.image pairRatio) hrat W hR hRT hW hsep
    calc
      _ ≤ C*T^η*((⌊2*M⌋₊:ℝ)*(W.card:ℝ)^2+
          (⌊2*M⌋₊:ℝ)^2*(W.card:ℝ)^((3:ℝ)/2)+
          (⌊2*M⌋₊:ℝ)*T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12)) := hh
      _ ≤ C*T^η*((2*M)*(W.card:ℝ)^2+(2*M)^2*(W.card:ℝ)^((3:ℝ)/2)+
          (2*M)*T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12)) := by gcongr
      _ ≤ _ := by
        have h1 : 0 ≤ M*(W.card:ℝ)^2 := by positivity
        have h3 : 0 ≤ M*T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12) := by positivity
        have hi : (2*M)*(W.card:ℝ)^2+(2*M)^2*(W.card:ℝ)^((3:ℝ)/2)+
            (2*M)*T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12) ≤
            4*(M*(W.card:ℝ)^2+M^2*(W.card:ℝ)^((3:ℝ)/2)+
              M*T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12)) := by nlinarith
        pm_328 mul_le_mul_of_nonneg_left hi
  · rw [not_nonempty_iff_eq_empty.mp he,sum_empty]
    positivity

/-- Large-gcd pair energy with the two extra adjacent-moment terms. The
short-range height condition (T/X)^K<=R is absent. -/
theorem large_gcd_adjacent_pair :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ X : ℝ, 1 < T → 0 < X → X ≤ T →
      ∀ P : Finset (ℕ × ℕ),
      (∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
        X < p.1 ∧ (p.1:ℝ) ≤ 2*X ∧ X < p.2 ∧ (p.2:ℝ) ≤ 2*X ∧
        X^2/T ≤ (pairGcd p:ℝ)) →
      ∀ W : Finset ℝ, T^((5:ℝ)/9) ≤ W.card → (W.card:ℝ)^3 ≤ T^2 →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ p ∈ P, ‖∑ t ∈ W, phase (pairRatio p) t‖^2) ≤
        C*T^η*X*((W.card:ℝ)^2+(T/X)*(W.card:ℝ)^((3:ℝ)/2)+
          T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12)) := by
  obtain ⟨C,hC,hb⟩ := coprime_dyadic_adjacent_second (show 0 < η/2 by positivity)
  pm_4
  refine ⟨C*L,by positivity,?_⟩
  intro T t₀ X hT hX hXT P hP W hR hRT hW hsep
  have ht : 0 < T := by linarith
  have hgeom : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
      X < p.1 ∧ (p.1:ℝ) ≤ 2*X ∧ X < p.2 ∧ (p.2:ℝ) ≤ 2*X := by
    pm_3
  have hblock : ∀ d ∈ gcdValues P,
      (∑ q ∈ reducedFiber P d, ‖∑ t ∈ W, phase (pairRatio q) t‖^2) ≤
        (C*T^(η/2)*((W.card:ℝ)^2+(T/X)*(W.card:ℝ)^((3:ℝ)/2)+
          T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12)))*(X/d) := by
    pm_86
    have hh := hb T t₀ (X/d) hT (by positivity) hdivT (reducedFiber P d) hQ
      W hR hRT hW hsep
    pm_147
  pm_109
  pm_5
  pm_75
end

end Montgomery.RationalMoment
