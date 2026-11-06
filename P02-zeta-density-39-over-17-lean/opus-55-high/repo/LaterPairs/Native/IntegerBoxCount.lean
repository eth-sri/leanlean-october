module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.IntegerIntervalCount
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                     

noncomputable section
namespace TaoTrudgianYang2025

theorem integer_box_triples_card_le
    (S : Finset (ℤ × ℤ × ℤ)) {a₁ b₁ a₂ b₂ a₃ b₃ : ℝ}
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃)
    (hx : ∀ p ∈ S, (p.1:ℝ) ∈ Set.Icc a₁ b₁)
    (hy : ∀ p ∈ S, (p.2.1:ℝ) ∈ Set.Icc a₂ b₂)
    (hz : ∀ p ∈ S, (p.2.2:ℝ) ∈ Set.Icc a₃ b₃) :
    (S.card:ℝ) ≤ (b₁-a₁+1)*(b₂-a₂+1)*(b₃-a₃+1) := by
  classical
  let X := S.image (fun p => p.1)
  let Y := S.image (fun p => p.2.1)
  let Z := S.image (fun p => p.2.2)
  pm_1061 hX X.card b₁ a₁ X h₁ x hx' hx
  pm_1061 hY Y.card b₂ a₂ Y h₂ y hy' hy
  pm_1061 hZ Z.card b₃ a₃ Z h₃ z hz' hz
  have hsub : S ⊆ X ×ˢ (Y ×ˢ Z) := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,
      Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,
        Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩⟩
  have hc : S.card ≤ X.card*(Y.card*Z.card) := by
    simpa only [Finset.card_product] using Finset.card_le_card hsub
  have hcR : (S.card:ℝ) ≤ (X.card:ℝ)*((Y.card:ℝ)*(Z.card:ℝ)) := by exact_mod_cast hc
  calc
    _ ≤ (X.card:ℝ)*((Y.card:ℝ)*(Z.card:ℝ)) := hcR
    _ ≤ (b₁-a₁+1)*((b₂-a₂+1)*(b₃-a₃+1)) :=
      mul_le_mul hX (mul_le_mul hY hZ (by positivity) (by linarith))
        (by positivity) (by linarith)
    _ = _ := by ring

end TaoTrudgianYang2025

