module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.IntegerProductCount
public import LaterPairs.Native.RobertSargosProductProjection
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                                            

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_robertSargos_product_fiber_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosPoint) (R H Q δ : ℝ)
      (z : (ℤ × ℤ × ℤ) × ℤ), 0 < H → 0 < Q →
      (∀ p ∈ S, RobertSargosPrimitiveSystem R H Q δ p) →
      (∀ p ∈ S, robertSargosProductKey p = z) →
      (S.card:ℝ) ≤ C*(4*H*Q)^ε := by
  classical
  pm_1657 C hC hbound exists_positive_integer_product_pairs_bound ε hε
  intro S R H Q δ z hH hQ hmem hfix
  by_cases hs : S.Nonempty
  · obtain ⟨p₀,hp₀⟩ := hs
    let m : ℤ := z.1.2.1*z.1.2.2+z.1.1*z.2
    pm_6176 RobertSargosPoint
    have hprod : ∀ p ∈ S, p.h₂*p.q₂ = m := by
      intro p hp
      have hr : p.r = z.1.1 :=
        congrArg (fun w : (ℤ × ℤ × ℤ) × ℤ => w.1.1) (hfix p hp)
      pm_296
      have hd : p.d = z.2 :=
        congrArg (fun w : (ℤ × ℤ × ℤ) × ℤ => w.2) (hfix p hp)
      dsimp [m]
      rw [← hr,← hh,← hq,← hd]
      nlinarith only [(hmem p hp).linear]
    pm_84
    have hinj : Set.InjOn f S := by
      intro p hp q hq he
      exact robertSargos_product_key_injective ((hfix p hp).trans (hfix q hq).symm)
        (congrArg (fun x : ℤ × ℤ => x.1) he)
        (congrArg (fun x : ℤ × ℤ => x.2) he)
    pm_216
  pm_257 hs Finset.card_empty

end TaoTrudgianYang2025
