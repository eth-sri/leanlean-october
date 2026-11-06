module

public import NearlyMinimax.HighObservationReal
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Borel decoding of the actual three response atoms. -/
𝚫
𝚨
𝚩
𝚬

def decodeTernaryResponse (a y : ℝ) : Fin 3 :=
  if y = -a then 0 else if y = 0 then 1 else 2

theorem decodeTernaryResponse_measurable a : Measurable $ decodeTernaryResponse a := by
  apply Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const
  exact Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const measurable_const

theorem decodeTernaryResponse_value a (ha : 𝙆) y :
    decodeTernaryResponse a 𝗐₂ = y := by
  have han : a ≠ -a := 𝖡₄
  fin_cases y <;> simp [decodeTernaryResponse, ternaryValue, ha.ne', han]

def decodeDesignResponse (a : ℝ) (z : 𝙌) :
    𝙇 × 𝙈 :=
  (fun i => 𝚄₁, fun i => decodeTernaryResponse a (z i).2)

theorem decodeDesignResponse_measurable a :
    Measurable $ decodeDesignResponse (d := d) (n := n) a := by
  apply Measurable.prodMk
  · fun_prop
  · apply measurable_pi_lambda
    intro i
    exact (decodeTernaryResponse_measurable a).comp $ measurable_snd.comp $ measurable_pi_apply i

theorem decodeDesignResponse_encode a (ha : 𝙆)
    (z : 𝙇 × 𝙈) :
    decodeDesignResponse a 𝗟₁ = z := by
  apply Prod.ext
  · rfl
  · funext i
    exact decodeTernaryResponse_value a ha $ z.2 i
