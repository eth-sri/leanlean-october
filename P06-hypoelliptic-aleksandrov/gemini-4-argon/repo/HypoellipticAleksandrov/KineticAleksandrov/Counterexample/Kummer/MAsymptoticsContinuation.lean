module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.MAsymptoticsPositive
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Continuation of the negative-axis expansion

A proved contiguous relation raises the first parameter above zero without changing the theorem.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open Filter Asymptotics

/- The second contiguous coefficient after Gamma cancellation. -/
theorem expansionCoeff_contiguous_second (a : ℝ) (b : Pos) (hab : a < b.1) (n : ℕ) :
    -((a - b.1) / (b.1 * (b.1 + 1))) *
      expansionCoeff (a + 1) (b.1 + 2) n =
      Real.Gamma b.1 / Real.Gamma (b.1 - a) *
        poch (a + 1) n * poch (a - b.1) n / (n.factorial : ℝ) := by
  have hb := ne_of_gt b.2
  have hb1 : b.1 + 1 ≠ 0 := ne_of_gt (next b).2
  have hc := ne_of_gt (sub_pos.mpr hab)
  have hG := ne_of_gt (Real.Gamma_pos_of_pos (sub_pos.mpr hab))
  rw [expansionCoeff, show b.1 + 2 = (b.1 + 1) + 1 by ring,
    Real.Gamma_add_one hb1, Real.Gamma_add_one hb,
    show (b.1 + 1 + 1) - (a + 1) = (b.1 - a) + 1 by ring,
    Real.Gamma_add_one hc, show a + 1 - (b.1 + 1 + 1) + 1 = a - b.1 by ring]
  field_simp
  ring

/- The constant coefficient of the contiguous expansion. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
