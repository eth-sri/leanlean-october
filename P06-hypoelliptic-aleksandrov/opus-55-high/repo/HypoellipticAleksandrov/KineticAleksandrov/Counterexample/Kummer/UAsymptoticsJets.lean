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

variable (f : ℝ → ℝ) (a : NegThird) (N : ℕ)

/-- Multiplication by a real power adds its exponent to an existing remainder bound. -/
theorem rpow_mul_isBigO  (p r : ℝ)
    (h : IsBigO atTop f (fun z => z ^ r)) :
    IsBigO atTop (fun z => z ^ p * f z) (fun z => z ^ (p + r)) := by
  have hh := (isBigO_refl (fun z : ℝ => z ^ p) atTop).mul h
  apply hh.congr' EventuallyEq.rfl _
  filter_upwards [Ioi_mem_atTop (0)] with z hz
  exact (Real.rpow_add hz p r).symm

/-- A version with an explicitly identified sum of exponents. -/
theorem rpow_mul_isBigO_of_add_eq  (p r e : ℝ)
    (h : IsBigO atTop f (fun z => z ^ r)) (he : p + r = e) :
    IsBigO atTop (fun z => z ^ p * f z) (fun z => Real.rpow z e) := by
  simp only [← he]
  exact rpow_mul_isBigO f p r h

/-- The transformed remainder is a power times the positive integral remainder. -/
theorem UNr_remainder_eq_power  (z : ℝ) (hz : 0 < z) :
    UNr a z - uExpansion a.1 (2 / 3) N z =
      z ^ (1 / 3 : ℝ) *
        (UIr ⟨a.1 + 1 / 3, by grind⟩ (4 / 3) z -
          uExpansion (a.1 + 1 / 3) (4 / 3) N z) := by
  rw [mul_sub, uExpansion_transform a N z hz]
  rfl

/-- The first derivative remainder has one additional inverse power. -/
theorem UNr_expansion_deriv  :
    IsBigO atTop (deriv (fun z => UNr a z - uExpansion a.1 (2 / 3) N z))
      (fun z => Real.rpow z (-a.1 - (N : ℝ) - 1)) := by
  let c : Pos := ⟨a.1 + 1 / 3, by grind⟩
  let f  := fun z => UIr c (4 / 3) z - uExpansion c.1 (4 / 3) N z
  have h0 : IsBigO atTop f (fun z => z ^ (-c.1 - N)) := by
    simpa using UIr_expansion c _ N
  have h1 : IsBigO atTop (deriv f) (fun z => z ^ (-c.1 - N - 1)) := by
    simpa using UIr_expansion_deriv c _ N
  have ha := (rpow_mul_isBigO f (1 / 3 - 1) _ h0).const_mul_left (1 / 3)
  have hb := rpow_mul_isBigO _ (1 / 3) _ h1
  have ha' : IsBigO atTop (fun z => (1 / 3) * (z ^ (1 / 3 - 1 : ℝ) * f z))
      (fun z => Real.rpow z (-a.1 - N - 1)) := by
    apply ha.congr' EventuallyEq.rfl _
    filter_upwards with z
    congr 1
    ring
  have hb' : IsBigO atTop (fun z => z ^ (1 / 3 : ℝ) * deriv f z)
      (fun z => Real.rpow z (-a.1 - N - 1)) := by
    apply hb.congr' EventuallyEq.rfl _
    filter_upwards with z
    congr 1
    ring
  apply (ha'.add hb').congr' _ EventuallyEq.rfl
  filter_upwards [Ioi_mem_atTop (0)] with z hz
  have heq : (fun w => UNr a w - uExpansion a.1 (2 / 3) N w) =ᶠ[𝓝 z]
      fun w => w ^ (1 / 3 : ℝ) * f w := by
    filter_upwards [Ioi_mem_nhds hz] with w hw
    exact UNr_remainder_eq_power a N w hw
  have hf := (hasDerivAt_UIr_remainder c (4 / 3) N z hz).differentiableAt.hasDerivAt
  have hd := ((hasDerivAt_power_mul f _ z hz hf).congr_of_eventuallyEq heq).deriv
  linarith

/-- The second derivative remainder has two additional inverse powers. -/
theorem UNr_expansion_deriv2  :
    IsBigO atTop (deriv (deriv (fun z => UNr a z - uExpansion a.1 (2 / 3) N z)))
      (fun z => Real.rpow z (-a.1 - (N : ℝ) - 2)) := by
  let c : Pos := ⟨a.1 + 1 / 3, by grind⟩
  let f  := fun z => UIr c (4 / 3) z - uExpansion c.1 (4 / 3) N z
  have h0 : IsBigO atTop f (fun z => z ^ (-c.1 - N)) := by
    simpa using UIr_expansion c _ N
  have h1 : IsBigO atTop (deriv f) (fun z => z ^ (-c.1 - N - 1)) := by
    simpa using UIr_expansion_deriv c _ N
  have h2 : IsBigO atTop (deriv (deriv f)) (fun z => z ^ (-c.1 - N - 2)) := by
    simpa using UIr_expansion_deriv2 c _ N
  have ha := (rpow_mul_isBigO_of_add_eq f (1 / 3 - 2) _
    (-a.1 - N - 2) h0 (by ring)).const_mul_left
      ((1 / 3) * (1 / 3 - 1))
  have hb := (rpow_mul_isBigO_of_add_eq _ (1 / 3 - 1) _
    (-a.1 - N - 2) h1 (by ring)).const_mul_left (2 * (1 / 3))
  have hc := rpow_mul_isBigO_of_add_eq _ (1 / 3) _
    (-a.1 - N - 2) h2 (by ring)
  apply ((ha.add hb).add hc).congr' _ EventuallyEq.rfl
  filter_upwards [Ioi_mem_atTop (0)] with z hz
  have heq : (fun w => UNr a w - uExpansion a.1 (2 / 3) N w) =ᶠ[𝓝 z]
      fun w => w ^ (1 / 3 : ℝ) * f w := by
    filter_upwards [Ioi_mem_nhds hz] with w hw
    exact UNr_remainder_eq_power a N w hw
  have hf : ∀ w ∈ Ioi (0), HasDerivAt f (deriv f w) w := by
    intro w hw
    exact (hasDerivAt_UIr_remainder c _ N w hw).differentiableAt.hasDerivAt
  have hf' := (hasDerivAt_deriv_UIr_remainder c (4 / 3) N z hz).differentiableAt.hasDerivAt
  have hd := deriv_deriv_power_mul f (1 / 3) z hz hf hf'
  have hder := heq.deriv.deriv_eq
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
