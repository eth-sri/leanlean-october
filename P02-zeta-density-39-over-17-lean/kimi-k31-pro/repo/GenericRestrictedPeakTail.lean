module
public import GenericPeakWidth
public import TaoTrudgianYang2025.AtkinsonPairNativePacket
public import LaterPairs.RestrictedPeakTail

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Finset
open MathCollab.Density MathCollab.Density.Stronger MathCollab.Density.Stronger.Peaks
namespace Montgomery.CriticalPeak

/-- Restricted actual critical-line peak count with every physical width condition discharged. -/
theorem restricted_peak_tail_of_count {a g b η ε : ℝ}
    (hb : 2 ≤ b) (hlogpow : 2*g+b ≤ 7)
    (hCount : LocalMeanCount a g b) (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ V : ℝ, 0 < V → H^(1/8+η) ≤ V →
      ∀ W : Finset ℝ, oneSeparated W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ H^ε*(H/V^6+H^a/V^(2*g+2*b)) :=
  restricted_peak_tail_of_count_general hb hCount hη hε
end Montgomery.CriticalPeak

namespace TaoTrudgianYang2025
open Montgomery.CriticalPeak
/-- The actual analytic exponent pair and both native zeta sources supply the restricted tail. -/
theorem ExponentPair.restricted_critical_peak_tail {k l η ε : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k) (hlogpow : 2+4*l/k ≤ 7)
    (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ V : ℝ, 0 < V → H^(1/8+η) ≤ V →
      ∀ W : Finset ℝ, oneSeparated W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ H^ε*(H/V^6+H^(1+l/k)/V^(4+(2+4*l)/k)) :=
  hpair.restricted_critical_peak_tail_general hk hη hε
end TaoTrudgianYang2025
