module
/- Generalized from the attributed verified physical-width argument. -/
public import PeakWidthPowers
public import MathCollab.Density.Stronger.Peaks.WidthRanges
import WeylPort.Analytic.RealLaplace

public section
open Filter Finset
open MathCollab.Density MathCollab.Density.Stronger MathCollab.Density.Stronger.Peaks
namespace Montgomery.CriticalPeak
theorem exists_pointValue_card_le_source_range
    {a g b : ℝ} (hb : 2 ≤ b) (hCount : LocalMeanCount a g b)
    {δ κ ν : ℝ} (hδ : 0 < δ) (hδUpper : δ ≤ 1/4)
    (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ K D H₀ : ℝ, 0 < K ∧ 0 < D ∧ 40000 ≤ H₀ ∧
      ∀ (H V : ℝ) (W : Finset ℝ),
        H₀ ≤ H → 0 < V →
        K*(Real.log (3*H))^2*(2*H)^(1/4+κ) ≤ V^2 →
        V^2 ≤ K*(Real.log (3*H))^2*H^(1/2-δ) →
        oneSeparated W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ D*H^ν*
          (H*(Real.log (3*H))^4/V^6 + H^a*(Real.log (3*H))^(2*g+b)/V^(2*g+2*b)) := by
  pm_5010 B hB exists_pointValue_card_le_with_width hb hCount
  pm_4481
  let D₁ : ℝ := D*(K*(16*P)^2+K^g*(16*P)^b)
  pm_4480
  change (W.card:ℝ) ≤ D*H^ν*(H/(G*(V^2/(16*P*L))^2)+
    H^a/(G^g*(V^2/(16*P*L))^b)) at hc
  have he1 := width_first_term (H := H) hK hP hL hV
  have he2 := width_second_term (a := a) (g := g) (b := b) (H := H) hK hP hL hV
  change H/(G*(V^2/(16*P*L))^2) = _ at he1
  change H^a/(G^g*(V^2/(16*P*L))^b) = _ at he2
  rw [he1,he2] at hc
  pm_5225 hx H L V
  have hy : 0 ≤ H^a*L^(2*g+b)/V^(2*g+2*b) := by positivity
  pm_6448
  have hky : 0 ≤ K^g*(16*P)^b := by positivity
  calc
    (W.card:ℝ) ≤ D*H^ν*
        (K*(16*P)^2*(H*L^4/V^6)+K^g*(16*P)^b*(H^a*L^(2*g+b)/V^(2*g+2*b)))  := by convert hc using 1; ring
    _ ≤ D*H^ν*((K*(16*P)^2+K^g*(16*P)^b)*
        (H*L^4/V^6+H^a*L^(2*g+b)/V^(2*g+2*b))) := by
      pm_6449
    _ = D₁*H^ν*(H*(Real.log (3*H))^4/V^6+H^a*(Real.log (3*H))^(2*g+b)/V^(2*g+2*b)) := by
      dsimp only [D₁,L]
      ring




end Montgomery.CriticalPeak
