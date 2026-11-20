module

public import Erdos821.Blueprint.Graph
public import Erdos821.Blueprint.Analytic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

open scoped BigOperators
open Filter

attribute [local instance] Classical.propDecidable

namespace Erdos821.GraphLemmas

end Erdos821.GraphLemmas

namespace Erdos821.Blueprint.Analytic

end Erdos821.Blueprint.Analytic

namespace Erdos821.Blueprint.Graph

/-- §2 omission injection: at most one U per pending index (field argument). -/
theorem omission_congruence_unique (p : ℕ) (hp : Nat.Prime p)
    (r A : ZMod p) (hA : A ≠ 0) (U₁ U₂ : ℕ)
    (h₁ : 0 < U₁) (h₁p : U₁ < p) (h₂ : 0 < U₂) (h₂p : U₂ < p)
    (hc₁ : r * (U₁ : ZMod p) + A = 0) (hc₂ : r * (U₂ : ZMod p) + A = 0) :
    U₁ = U₂ := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have _h₁ : 0 < U₁ := h₁
  have _h₂ : 0 < U₂ := h₂
  have hr : r ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_add] at hc₁
    exact hA hc₁
  have e1 : r * (U₁ : ZMod p) = -A := eq_neg_of_add_eq_zero_left hc₁
  have e2 : r * (U₂ : ZMod p) = -A := eq_neg_of_add_eq_zero_left hc₂
  have hmul : r * (U₁ : ZMod p) = r * (U₂ : ZMod p) := by rw [e1, e2]
  have hcast : (U₁ : ZMod p) = (U₂ : ZMod p) := mul_left_cancel₀ hr hmul
  have hv1 : ((U₁ : ZMod p).val) = U₁ := ZMod.val_natCast_of_lt h₁p
  have hv2 : ((U₂ : ZMod p).val) = U₂ := ZMod.val_natCast_of_lt h₂p
  have hval : ((U₁ : ZMod p).val) = ((U₂ : ZMod p).val) := congrArg ZMod.val hcast
  rw [hv1, hv2] at hval
  exact hval

end Erdos821.Blueprint.Graph
