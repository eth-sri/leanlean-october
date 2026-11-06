module
public import GenericPeakWidth
public import TaoTrudgianYang2025.AtkinsonPairNativePacket
import WeylPort.Analytic.RealLaplace

public section
open Filter Finset
open MathCollab.Density MathCollab.Density.Stronger MathCollab.Density.Stronger.Peaks
namespace Montgomery.CriticalPeak

/-- Restricted actual critical-line peak count with arbitrary fixed natural log cap. -/
theorem restricted_peak_tail_of_count_log_cap {a g b η ε : ℝ} (m : ℕ)
    (hm : 4 ≤ m) (hb : 2 ≤ b) (hlogpow : 2*g+b ≤ (m : ℝ))
    (hCount : LocalMeanCount a g b) (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ V : ℝ, 0 < V → H^(1/8+η) ≤ V →
      ∀ W : Finset ℝ, oneSeparated W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ H^ε*(H/V^6+H^a/V^(2*g+2*b)) := by
  pm_127
  have hbudget := TaoTrudgianYang2025.eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := D) (a := ε/2) (b := ε) hD.le m (by linarith)
  pm_237
  pm_4484
  pm_5989
  · simp only [Finset.card_empty,Nat.cast_zero]
    positivity
  have hVgrowth : V ≤ H^(1/6+κ) :=
    (hlarge t ht).trans (hg t (by
      pm_4482
      exact (hrange t ht).2)).le
  pm_4483 κ hH
  pm_897
  have h4 : (Real.log (3*H))^4 ≤ (Real.log (3*H))^m :=
    pow_le_pow_right₀ hL1 hm
  have hr : (Real.log (3*H))^(2*g+b) ≤ (Real.log (3*H))^m := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hL1 hlogpow
  calc
    (W.card:ℝ) ≤ D*H^(ε/2)*
        (H*(Real.log (3*H))^4/V^6+H^a*(Real.log (3*H))^(2*g+b)/V^(2*g+2*b)) := hc
    _ ≤ D*H^(ε/2)*
        (H*(Real.log (3*H))^m/V^6+H^a*(Real.log (3*H))^m/V^(2*g+2*b)) := by
      gcongr
    _ = (D*(Real.log (3*H))^m*H^(ε/2))*(H/V^6+H^a/V^(2*g+2*b)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbud (by positivity)
/-- Every fixed logarithmic exponent can be absorbed into the height loss. -/
theorem restricted_peak_tail_of_count_general {a g b η ε : ℝ}
    (hb : 2 ≤ b) (hCount : LocalMeanCount a g b) (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ V : ℝ, 0 < V → H^(1/8+η) ≤ V →
      ∀ W : Finset ℝ, oneSeparated W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ H^ε*(H/V^6+H^a/V^(2*g+2*b)) := by
  obtain ⟨m, hm⟩ := exists_nat_ge (max (4:ℝ) (2*g+b))
  have hm4 : (4:ℝ) ≤ (m:ℝ) := (le_max_left _ _).trans hm
  exact restricted_peak_tail_of_count_log_cap m (by exact_mod_cast hm4) hb
    ((le_max_right _ _).trans hm) hCount hη hε
end Montgomery.CriticalPeak

namespace TaoTrudgianYang2025
open Montgomery.CriticalPeak
/-- The actual analytic exponent pair and both native zeta sources supply the restricted tail. -/
theorem ExponentPair.restricted_critical_peak_tail_general {k l η ε : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k)
    (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ V : ℝ, 0 < V → H^(1/8+η) ≤ V →
      ∀ W : Finset ℝ, oneSeparated W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ H^ε*(H/V^6+H^(1+l/k)/V^(4+(2+4*l)/k)) := by
  pm_5800
  pm_452
  have hh := restricted_peak_tail_of_count_general hb
    (a := 1+l/k) (g := (2*l-1)/k) (b := 2+2/k)
    (localMeanCount_of_pair_packet hk hpair.localMeanPacket_native) hη hε
  simpa only [hf] using hh
end TaoTrudgianYang2025
