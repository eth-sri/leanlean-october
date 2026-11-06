module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.AdditiveEnergy
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                           

noncomputable section
namespace TaoTrudgianYang2025

theorem integer_card_le_interval_length_add_one (S : Finset ℤ) {a b : ℝ}
    (hab : a ≤ b) (hmem : ∀ n ∈ S, a ≤ (n:ℝ) ∧ (n:ℝ) ≤ b) :
    (S.card:ℝ) ≤ b-a+1 := by
  classical
  let W := S.image (fun n : ℤ => (n:ℝ))
  have hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x-y| := by
    intro x hx y hy hxy
    pm_2533 m hm hx n hn hy
    have hmn : m-n ≠ 0 := by
      intro he
      apply hxy
      grind
    have hpos : 0 < |m-n| := abs_pos.mpr hmn
    have hbound : (1:ℤ) ≤ |m-n| := by omega
    exact_mod_cast hbound
  have hW : ∀ x ∈ W, a ≤ x ∧ x ≤ b := by
    pm_2532 x hx n hn
    grind
  have hb := oneSeparated_card_cast_le_interval_length_add_one W hsep
    (sub_nonneg.mpr hab) hW
  have hcard : W.card = S.card :=
    Finset.card_image_of_injective S (fun _ _ h => Int.cast_injective h)
  grind

theorem integer_card_le_of_abs_sub_le (S : Finset ℤ) {a B : ℝ}
    (hB : 0 ≤ B) (hmem : ∀ n ∈ S, |(n:ℝ)-a| ≤ B) :
    (S.card:ℝ) ≤ 2*B+1 := by
  have hb := integer_card_le_interval_length_add_one S (by linarith : a-B ≤ a+B)
    (fun n hn => by grind)
  linarith

end TaoTrudgianYang2025

