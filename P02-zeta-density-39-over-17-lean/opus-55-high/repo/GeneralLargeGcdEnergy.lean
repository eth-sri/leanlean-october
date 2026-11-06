module
public import GeneralCoprimeEnergy
public import RationalLargeGcdEnergy
import WeylPort.Analytic.RealLaplace

public section

set_option maxHeartbeats 1600000
open Finset
namespace Montgomery.RationalMoment

/-- Large-gcd pair energy with the two extra adjacent-moment terms. The
short-range height condition (T/X)^K<=R is absent. -/
theorem large_gcd_adjacent_general {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ X : ℝ, 1 < T → 0 < X → X ≤ T →
      ∀ P : Finset (ℕ × ℕ),
      (∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
        X < p.1 ∧ (p.1:ℝ) ≤ 2*X ∧ X < p.2 ∧ (p.2:ℝ) ≤ 2*X ∧
        X^2/T ≤ (pairGcd p:ℝ)) →
      ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∑ p ∈ P, ‖∑ t ∈ W, phase (pairRatio p) t‖^2) ≤
        C*T^η*X*((W.card:ℝ)^2+(T/X)*(W.card:ℝ)^((3:ℝ)/2)+
          T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12)) := by
  obtain ⟨C,hC,hb⟩ := coprime_dyadic_adjacent_general (K:=2) (by norm_num) (show 0 < η/2 by positivity) (B:=1) (by norm_num)
  pm_4
  refine ⟨C*L,by positivity,?_⟩
  intro T t₀ X hT hX hXT P hP W hW hsep
  have ht : 0 < T := by linarith
  have hgeom : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
      X < p.1 ∧ (p.1:ℝ) ≤ 2*X ∧ X < p.2 ∧ (p.2:ℝ) ≤ 2*X := by
    pm_3
  have hblock : ∀ d ∈ gcdValues P,
      (∑ q ∈ reducedFiber P d, ‖∑ t ∈ W, phase (pairRatio q) t‖^2) ≤
        (C*T^(η/2)*((W.card:ℝ)^2+(T/X)*(W.card:ℝ)^((3:ℝ)/2)+
          T^((1:ℝ)/4)*(W.card:ℝ)^((19:ℝ)/12)))*(X/d) := by
    pm_86
    have hh := hb T t₀ (X/d) hT (by positivity) (by simpa using hdivT) (reducedFiber P d) hQ
      W hW hsep
    norm_num at hh
    pm_147
  pm_109
  pm_5
  pm_75

end Montgomery.RationalMoment
