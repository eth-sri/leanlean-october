module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosNormalizedFrequency
public import LaterPairs.Native.RobertSargosPrimitiveCount
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                                            

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_robertSargos_gcd_fiber_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosPoint) (R H Q δ : ℝ) (j k : ℕ),
      1 ≤ R → 1 ≤ H → 1 ≤ Q → 0 ≤ δ → R ≤ H/2 →
      (∀ p ∈ S, RobertSargosReducedSystem R H Q δ p) →
      (∀ p ∈ S, j = robertSargosCoefficientGcd p) →
      (∀ p ∈ S, k = robertSargosFrequencyGcd p) →
      (S.card:ℝ) ≤ C*((R/j)*(H/j)*(max 1 (Q/k)))^(1+ε)*
        (1+δ*max 1 (Q/k)) := by
  classical
  pm_1657 C hC hbound exists_robertSargos_primitive_count ε hε
  intro S R H Q δ j k hR hH hQ hδ hRH hmem hj hk
  by_cases hs : S.Nonempty
  · obtain ⟨p₀,hp₀⟩ := hs
    have hjp : 0 < j := hj p₀ hp₀ ▸ (hmem p₀ hp₀).coefficient_gcd_pos
    have hjR : (j:ℝ) ≤ R := by
      rw [hj p₀ hp₀]
      exact (hmem p₀ hp₀).coefficient_gcd_le
    have hsc := robertSargos_normalized_scale_conditions (Q := Q) k hjp hjR hRH
    let T := S.image (robertSargosNormalize j k)
    have hcard : T.card = S.card :=
      Finset.card_image_of_injOn (robertSargos_normalize_injective_on_gcd_fiber S hj hk)
    have hT : ∀ p ∈ T, RobertSargosPrimitiveSystem (R/j) (H/j) (max 1 (Q/k)) δ p := by
      pm_2532 q hq p hp
      exact (hmem p hp).normalized_primitive (by linarith) (by linarith) hδ
        (hj p hp) (hk p hp)
    have hb := hbound T (R/j) (H/j) (max 1 (Q/k)) δ
      hsc.1 hsc.2.1 hsc.2.2.1 hδ hsc.2.2.2 hT
    rwa [hcard] at hb
  pm_257 hs Finset.card_empty

end TaoTrudgianYang2025

