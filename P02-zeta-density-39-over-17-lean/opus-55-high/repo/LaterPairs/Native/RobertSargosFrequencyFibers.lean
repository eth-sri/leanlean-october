module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosFixedDisplacementLoss
public import LaterPairs.Native.RobertSargosFrequencyCoordinates
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                        

noncomputable section
namespace TaoTrudgianYang2025

section
variable (ε : ℝ) (hε : 0 < ε)
include ε hε
theorem exists_robertSargos_frequency_fiber_conic_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosPoint) (R H Q δ : ℝ) (z : ℤ × ℤ × ℤ),
      0 < H → 0 < Q → 0 ≤ δ →
      (∀ p ∈ S, RobertSargosPrimitiveSystem R H Q δ p) →
      (∀ p ∈ S, robertSargosFrequencyKey p = z) →
      (S.card:ℝ) ≤ C*(z.1.natAbs:ℝ)^ε*(1+8*H^2*δ/z.1.natAbs) := by
  classical
  pm_1657 C hC hbound exists_robertSargos_fixed_displacement_conic_bound ε hε
  intro S R H Q δ z hH hQ hδ hmem hfix
  by_cases hs : S.Nonempty
  · obtain ⟨p₀,hp₀⟩ := hs
    pm_914
    have hb := hbound T z.1 z.2.1 z.2.2 H Q δ
      h₀.coordinate_primitive h₀.d_ne_zero hH hQ hδ
      h₀.q₁_support.1 h₀.q₂_support.1 h₀.same_sign
      (fun t ht => (hT t ht).h₁_support)
      (fun t ht => (hT t ht).h₂_support)
      (fun t ht => (hT t ht).coefficient_primitive)
      (fun t ht => by
        pm_6931
        nlinarith only [hl])
      (fun t ht => (hT t ht).near)
    pm_6678
  pm_257 hs Finset.card_empty

theorem exists_robertSargos_frequency_fiber_linear_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosPoint) (R H Q δ : ℝ) (z : ℤ × ℤ × ℤ),
      0 ≤ R → 0 < H → 0 < Q → δ ≤ 1 →
      (∀ p ∈ S, RobertSargosPrimitiveSystem R H Q δ p) →
      (∀ p ∈ S, robertSargosFrequencyKey p = z) →
      (S.card:ℝ) ≤ C*(z.1.natAbs:ℝ)^ε*(1+72*H*R/z.1.natAbs) := by
  classical
  pm_1657 C hC hbound exists_robertSargos_fixed_displacement_linear_bound ε hε
  intro S R H Q δ z hR hH hQ hδ hmem hfix
  by_cases hs : S.Nonempty
  · obtain ⟨p₀,hp₀⟩ := hs
    pm_914
    have hb := hbound T z.1 z.2.1 z.2.2 R H Q δ
      h₀.coordinate_primitive h₀.d_ne_zero hR hH hQ hδ
      h₀.q₁_support h₀.q₂_support h₀.same_sign
      (fun t ht => (hT t ht).h₁_support)
      (fun t ht => (hT t ht).h₂_support)
      (fun t ht => (hT t ht).r_bound)
      (fun t ht => (hT t ht).coefficient_primitive)
      (fun t ht => by
        pm_6931
        nlinarith only [hl])
      (fun t ht => (hT t ht).near)
    pm_6678
  pm_257 hs Finset.card_empty
end

end TaoTrudgianYang2025

