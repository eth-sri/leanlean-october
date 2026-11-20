module

public import NearlyMinimax.HighObservationReal


@[expose] public section

/-! Borel decoding of the actual three response atoms. -/
noncomputable section
open MeasureTheory Set
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {d n : ℕ} (a : ℝ)

def decodeTernaryResponse (y : ℝ) : Fin 3 :=
  if y = -a then 0 else if y = 0 then 1 else 2

theorem decodeTernaryResponse_measurable : Measurable (decodeTernaryResponse a) := by
  apply Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const
  exact Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const measurable_const

theorem decodeTernaryResponse_value (ha : 0 < a) (y : Fin 3) :
    decodeTernaryResponse a (ternaryValue a y) = y := by
  have han : a ≠ -a := by linarith
  fin_cases y <;> simp [decodeTernaryResponse, ternaryValue, (neg_ne_zero.mpr ha.ne'), ha.ne', han]

def decodeDesignResponse (z : Fin n → Observation d) :
    IndexedSample d n :=
  (fun i => (z i).1, fun i => decodeTernaryResponse a (z i).2)

theorem decodeDesignResponse_measurable :
    Measurable (decodeDesignResponse (d := d) (n := n) a) := by
  apply Measurable.prodMk
  · fun_prop
  · apply measurable_pi_lambda
    intro i
    exact (decodeTernaryResponse_measurable a).comp (by fun_prop)

theorem decodeDesignResponse_encode {a : ℝ} (ha : 0 < a)
    (z : IndexedSample d n) :
    decodeDesignResponse a (encodeDesignResponse a z) = z := by
  apply Prod.ext
  · rfl
  · funext i
    solve_by_elim [decodeTernaryResponse_value]

end NearlyMinimax
