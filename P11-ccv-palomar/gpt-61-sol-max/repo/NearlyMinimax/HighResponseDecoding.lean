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

theorem decodeTernaryResponse_measurable a : Measurable (decodeTernaryResponse a) := by
  apply Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const
  simp_all [Measurable.ite]

theorem decodeTernaryResponse_value a (ha : 0 < a) y :
    decodeTernaryResponse a (ternaryValue a y) = y := by
  have hna  := neg_ne_zero.mpr ha.ne'
  have han : a ≠ -a := by linarith
  fin_cases y <;> simp [decodeTernaryResponse, ternaryValue, hna, ha.ne', han]

section
variable {d n : ℕ}

def decodeDesignResponse  a (z : Fin n → Observation d)  :=
  (fun i => (z i).1, fun i => decodeTernaryResponse a (z i).2)

theorem decodeDesignResponse_measurable  a :
    Measurable (decodeDesignResponse (d := d) (n := n) a) := by
  apply Measurable.prodMk
  · fun_prop
  · apply measurable_pi_lambda
    intro i
    exact (decodeTernaryResponse_measurable a).comp (measurable_snd.comp (measurable_pi_apply i))

theorem decodeDesignResponse_encode  a (ha : 0 < a)
    (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    decodeDesignResponse a (encodeDesignResponse a z) = z := by
  apply Prod.ext
  · rfl
  · funext i
    exact decodeTernaryResponse_value a ha (z.2 i)
end


end NearlyMinimax
