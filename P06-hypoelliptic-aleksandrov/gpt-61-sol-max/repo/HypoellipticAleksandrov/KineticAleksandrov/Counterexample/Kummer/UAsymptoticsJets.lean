module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.UAsymptoticsDerivatives
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MAsymptotics
import Mathlib.Tactic

/-!
# First two derivative remainders for the transformed U solution

Product differentiation is applied to the actual integral remainder. Each term is
estimated by the independently proved shifted-integral expansions.
-/

@[expose] public noncomputable section

open Set Filter Asymptotics
open scoped Topology

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

/-- Multiplication by a real power adds its exponent to an existing remainder bound. -/
theorem rpow_mul_isBigO (f : ℝ → ℝ) (p r : ℝ)
    (h : IsBigO atTop f (fun z => z ^ r)) :
    IsBigO atTop (fun z => z ^ p * f z) (fun z => z ^ (p + r)) := by

  apply ((isBigO_refl (fun z : ℝ => z ^ p) atTop).mul h).congr' EventuallyEq.rfl _
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with z hz
  exact (Real.rpow_add hz p r).symm

/-- A version with an explicitly identified sum of exponents. -/
theorem rpow_mul_isBigO_of_add_eq (f : ℝ → ℝ) (p r e : ℝ)
    (h : IsBigO atTop f (fun z => z ^ r)) (he : p + r = e) :
    IsBigO atTop (fun z => z ^ p * f z) (fun z => Real.rpow z e) := by
  simp only [Real.rpow_eq_pow, ← he]
  exact rpow_mul_isBigO f p r h

variable (a : NegThird) (N : ℕ)

/-- The transformed remainder is a power times the positive integral remainder. -/
theorem UNr_remainder_eq_power  (z : ℝ) (hz : 0 < z) :
    UNr a z - uExpansion a.1 (2 / 3) N z =
      z ^ (1 / 3 : ℝ) *
        (UIr ⟨a.1 + 1 / 3, by linarith only [a.2.1]⟩ (4 / 3) z -
          uExpansion (a.1 + 1 / 3) (4 / 3) N z) := by
  rw [mul_sub, uExpansion_transform a N z hz]
  rfl

/-- The first derivative remainder has one additional inverse power. -/
theorem UNr_expansion_deriv  :
    IsBigO atTop (deriv (fun z => UNr a z - uExpansion a.1 (2 / 3) N z))
      (fun z => Real.rpow z (-a.1 - (N : ℝ) - 1)) := by
  let c : Pos := ⟨a.1 + 1 / 3, by linarith only [a.2.1]⟩
  let f  := fun z => UIr c (4 / 3) z - uExpansion c.1 (4 / 3) N z




  have ha' : IsBigO atTop (fun z => (1 / 3 : ℝ) * (z ^ (1 / 3 - 1 : ℝ) * f z))
      (fun z => Real.rpow z (-a.1 - (N : ℝ) - 1)) := by
    apply ((rpow_mul_isBigO f (1 / 3 - 1) _ (UIr_expansion c (4 / 3) N)).const_mul_left (1 / 3 : ℝ)).congr' EventuallyEq.rfl _
    filter_upwards with z
    rw [Real.rpow_eq_pow]
    congr 1
    dsimp only [c]
    ring

  apply (ha'.add (by
      apply (rpow_mul_isBigO (deriv f) (1 / 3) _ (UIr_expansion_deriv c (4 / 3) N)).congr' EventuallyEq.rfl _
      filter_upwards with z
      rw [Real.rpow_eq_pow]
      congr 1
      dsimp only [c]
      ring)).congr' _ EventuallyEq.rfl
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with z hz


  have hd := ((hasDerivAt_power_mul f (1 / 3) z hz ((hasDerivAt_UIr_remainder c (4 / 3) N z hz).differentiableAt.hasDerivAt)).congr_of_eventuallyEq (by
      filter_upwards [Ioi_mem_nhds hz] with w hw
      exact UNr_remainder_eq_power a N w hw)).deriv
  exact (by convert hd.symm using 1; ring)

/-- The second derivative remainder has two additional inverse powers. -/
theorem UNr_expansion_deriv2  :
    IsBigO atTop (deriv (deriv (fun z => UNr a z - uExpansion a.1 (2 / 3) N z)))
      (fun z => Real.rpow z (-a.1 - (N : ℝ) - 2)) := by
  let sharedTerm_26daa1db31 := ((-a.1 - (N : ℝ) - 2))
  let c : Pos := ⟨a.1 + 1 / 3, by linarith only [a.2.1]⟩
  let f  := fun z => UIr c (4 / 3) z - uExpansion c.1 (4 / 3) N z



  have ha := (rpow_mul_isBigO_of_add_eq f (1 / 3 - 2) (-c.1 - (N : ℝ))
    sharedTerm_26daa1db31 (UIr_expansion c (4 / 3) N) (by dsimp only [c]; ring)).const_mul_left
      ((1 / 3 : ℝ) * (1 / 3 - 1))
  have hb := (rpow_mul_isBigO_of_add_eq (deriv f) (1 / 3 - 1) (-c.1 - (N : ℝ) - 1)
    sharedTerm_26daa1db31 (UIr_expansion_deriv c (4 / 3) N) (by dsimp only [c]; ring)).const_mul_left (2 * (1 / 3 : ℝ))
  have hc := rpow_mul_isBigO_of_add_eq (deriv (deriv f)) (1 / 3) (-c.1 - (N : ℝ) - 2)
    sharedTerm_26daa1db31 (UIr_expansion_deriv2 c (4 / 3) N) (by dsimp only [c]; ring)
  apply ((ha.add hb).add hc).congr' _ EventuallyEq.rfl
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with z hz



  have hd := deriv_deriv_power_mul f (1 / 3) z hz (by
      intro w hw
      exact (hasDerivAt_UIr_remainder c (4 / 3) N w hw).differentiableAt.hasDerivAt) ((hasDerivAt_deriv_UIr_remainder c (4 / 3) N z hz).differentiableAt.hasDerivAt)
  have hder := (show (fun w => UNr a w - uExpansion a.1 (2 / 3) N w) =ᶠ[𝓝 z]
      fun w => w ^ (1 / 3 : ℝ) * f w by
      filter_upwards [Ioi_mem_nhds hz] with w hw
      exact UNr_remainder_eq_power a N w hw).deriv.deriv_eq
  rw [hd] at hder
  exact (by convert hder.symm using 1; ring)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
