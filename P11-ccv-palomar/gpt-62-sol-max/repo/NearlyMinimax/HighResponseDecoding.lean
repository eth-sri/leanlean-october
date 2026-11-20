module

public import NearlyMinimax.HighObservationReal


@[expose] public section

/-! Borel decoding of the actual three response atoms. -/
noncomputable section
open MeasureTheory Set
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def decodeTernaryResponse (a y : ℝ) : Fin 3 :=
  if y = -a then 0 else if y = 0 then 1 else 2

section
variable (a : ℝ)

theorem decodeTernaryResponse_measurable : Measurable (decodeTernaryResponse a) := by
  apply Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const
  apply Measurable.ite <;> simp_all

theorem decodeTernaryResponse_value (ha : 0 < a) (y : Fin 3) :
    decodeTernaryResponse a (ternaryValue a y) = y := by
  have hna : -a ≠ 0 := neg_ne_zero.mpr ha.ne'
  have han : a ≠ -a := by linarith
  fin_cases y <;> simp [decodeTernaryResponse, ternaryValue, ha.ne', han]

end

def decodeDesignResponse {d n : ℕ} (a : ℝ) (z : ObservedSample d n) :
    TernarySample d n :=
  (fun i => (z i).1, fun i => decodeTernaryResponse a (z i).2)

section
variable {d n : ℕ} (a : ℝ)

theorem decodeDesignResponse_measurable :
    Measurable (decodeDesignResponse (d := d) (n := n) a) := by
  apply Measurable.prodMk
  · fun_prop
  · apply measurable_pi_lambda
    intro i
    exact (decodeTernaryResponse_measurable a).comp (measurable_snd.comp (measurable_pi_apply i))

theorem decodeDesignResponse_encode (ha : 0 < a)
    (z : TernarySample d n) :
    decodeDesignResponse a (encodeDesignResponse a z) = z := by
  apply Prod.ext
  · rfl
  · funext i
    apply decodeTernaryResponse_value <;> assumption

end

end NearlyMinimax
