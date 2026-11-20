module

public import Mathlib

@[expose] public section

/-! # The three-point response law

This file formalizes the finite response law in Section 6.1 of the paper.
Index 0 represents `-a`, index 1 represents `0`, and index 2 represents `a`.
Expectations are actual finite sums against the specified masses.
-/

namespace NearlyMinimax

open scoped Topology

noncomputable section

/-- The finite index vector for a ternary sample or activation configuration. -/
abbrev TernaryVector (n : ℕ) := Fin n → Fin 3

section
variable (a f V : ℝ) {X : Type*}

/-- The support of the paper's three-point response law. -/
def ternaryValue : Fin 3 → ℝ := ![-a, 0, a]

/-- The three probability masses; positivity is proved separately. -/
def ternaryMass : Fin 3 → ℝ :=
  ![(V + f ^ 2 - a * f) / (2 * a ^ 2),
    1 - (V + f ^ 2) / a ^ 2,
    (V + f ^ 2 + a * f) / (2 * a ^ 2)]

/-- The response mass is continuous in the regression and variance, with fixed support. -/
@[fun_prop] theorem continuous_ternaryMass [TopologicalSpace X] (a : ℝ)
    {f V : X → ℝ} (y : Fin 3) (hf : Continuous f) (hV : Continuous V) :
    Continuous (fun x => ternaryMass a (f x) (V x) y) := by
  fin_cases y <;> simp [ternaryMass] <;> fun_prop

/-- In a measured experiment the finite response index may also vary. -/
@[fun_prop] theorem measurable_ternaryMass [MeasurableSpace X] (a : ℝ)
    {f V : X → ℝ} {y : X → Fin 3} (hf : Measurable f) (hV : Measurable V) (hy : Measurable y) :
    Measurable (fun x => ternaryMass a (f x) (V x) (y x)) := by
  have hm : Measurable (fun z : (ℝ × ℝ) × Fin 3 => ternaryMass a z.1.1 z.1.2 z.2) :=
    measurable_from_prod_countable_left fun j => (continuous_ternaryMass a j continuous_fst continuous_snd).measurable
  exact hm.comp ((hf.prodMk hV).prodMk hy)

/-- Integration against the finite response law. -/
def ternaryExpectation (g : ℝ → ℝ) : ℝ :=
  ∑ y, ternaryMass a f V y * g (ternaryValue a y)

theorem ternary_normalized {a : ℝ} (f V : ℝ) (ha : a ≠ 0) :
    ∑ y, ternaryMass a f V y = 1 := by
  simp [Fin.sum_univ_succ, ternaryMass]
  ring

theorem ternary_mean (ha : a ≠ 0) :
    ternaryExpectation a f V id = f := by
  simp [ternaryExpectation, Fin.sum_univ_succ, ternaryMass, ternaryValue]
  field_simp [ha]
  ring

theorem ternary_variance (ha : a ≠ 0) :
    ternaryExpectation a f V (fun y => (y - f) ^ 2) = V := by
  simp [ternaryExpectation, Fin.sum_univ_succ, ternaryMass, ternaryValue]
  field_simp [ha]
  ring

/-- The exact centered fourth moment appearing in the paper. -/
theorem ternary_fourth_central_moment (ha : a ≠ 0) :
    ternaryExpectation a f V (fun y => (y - f) ^ 4) =
      a ^ 2 * V + (6 * V - 3 * a ^ 2) * f ^ 2 + 3 * f ^ 4 := by
  simp [ternaryExpectation, Fin.sum_univ_succ, ternaryMass, ternaryValue]
  field_simp [ha]
  ring

/-- Explicit sufficient conditions for all masses to be strictly positive. -/
theorem ternary_mass_positive (ha : 0 < a)
    (hupper : V + f ^ 2 < a ^ 2)
    (hlower : a * |f| < V + f ^ 2) :
    ∀ y, 0 < ternaryMass a f V y := by
  have ha2  := sq_pos_of_pos ha
  have hleft  := mul_le_mul_of_nonneg_left (le_abs_self f) ha.le
  have hright : -(a * f) ≤ a * |f| := by
    have := mul_le_mul_of_nonneg_left (neg_le_abs f) ha.le
    nlinarith
  intro y
  fin_cases y
  · exact div_pos (by linarith) (by positivity)
  · exact sub_pos.mpr ((div_lt_one ha2).mpr hupper)
  · exact div_pos (by linarith) (by positivity)

end

/-- Every nonnegative normalized mass is at most one. -/
theorem ternary_mass_le_one {a : ℝ} (f V : ℝ) (ha : a ≠ 0)
    (hnonneg : ∀ y, 0 ≤ ternaryMass a f V y) (y : Fin 3) :
    ternaryMass a f V y ≤ 1 := by
  rw [← ternary_normalized f V ha]
  exact Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ y)

/-- All response constraints hold uniformly in a rectangular neighborhood
of an interior zero-regression law, exactly as in Section 6.1. -/
theorem ternary_admissible_neighborhood {a v vMinus vPlus C4 : ℝ}
    (ha : 0 < a) (hv : 0 < v) (hva : v < a ^ 2)
    (hvMinus : vMinus < v) (hvPlus : v < vPlus) (hC4 : a ^ 2 * v < C4) :
    ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧
      ∀ f V, |f| ≤ ρ → |V - v| ≤ ρ →
        vMinus < V ∧ V < vPlus ∧
        (∀ y, c ≤ ternaryMass a f V y) ∧
        ternaryExpectation a f V (fun y => (y - f) ^ 4) ≤ C4 := by
  let p  := v / (2 * a ^ 2)
  let q  := 1 - v / a ^ 2
  let c  := min p q / 2
  have ha2  := sq_pos_of_pos ha
  have hp : 0 < p := by positivity
  have hq  := sub_pos.mpr ((div_lt_one ha2).mpr hva)
  have hc : 0 < c := by positivity
  have hcp : c < p := by grind
  have hcq : c < q := by grind
  have hmass0 : ∀ y, c < ternaryMass a 0 v y := by
    intro y
    fin_cases y
    · simpa [ternaryMass, p] using hcp
    · simpa [ternaryMass, q] using hcq
    · simpa [ternaryMass, p] using hcp
  have hmassCont : ∀ y,
      Continuous (fun x : ℝ × ℝ => ternaryMass a x.1 x.2 y) := by
    intro y
    fin_cases y <;> simp <;> fun_prop
  have hmassEvent : ∀ᶠ x in nhds (0, v),
      ∀ y, c < ternaryMass a x.1 x.2 y := Filter.eventually_all.mpr (fun y =>
      continuousAt_const.eventually_lt (hmassCont y).continuousAt (hmass0 y))
  have hVMinus : ∀ᶠ x : ℝ × ℝ in nhds (0, v), vMinus < x.2 :=
    continuousAt_const.eventually_lt continuous_snd.continuousAt hvMinus
  have hVPlus : ∀ᶠ x : ℝ × ℝ in nhds (0, v), x.2 < vPlus :=
    continuous_snd.continuousAt.eventually_lt continuousAt_const hvPlus
  have hfourthCont : Continuous (fun x : ℝ × ℝ =>
      a ^ 2 * x.2 + (6 * x.2 - 3 * a ^ 2) * x.1 ^ 2 + 3 * x.1 ^ 4) := by
    fun_prop
  have hfourth : ∀ᶠ x in nhds (0, v),
      a ^ 2 * x.2 + (6 * x.2 - 3 * a ^ 2) * x.1 ^ 2 + 3 * x.1 ^ 4 < C4 := by
    apply hfourthCont.continuousAt.eventually_lt continuousAt_const
    simpa using hC4
  have hevent : ∀ᶠ x in nhds (0, v),
      vMinus < x.2 ∧ x.2 < vPlus ∧
      (∀ y, c < ternaryMass a x.1 x.2 y) ∧
      a ^ 2 * x.2 + (6 * x.2 - 3 * a ^ 2) * x.1 ^ 2 + 3 * x.1 ^ 4 < C4 := by
    filter_upwards [hVMinus, hVPlus, hmassEvent, hfourth] with x hm hp hq hf
    exact ⟨hm, hp, hq, hf⟩
  obtain ⟨ε, hε, hbound⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨ε / 2, c, by positivity, hc, ?_⟩
  intro f V hf hV
  have hdist : dist (f, V) (0, v) < ε := by
    simp [Prod.dist_eq, Real.dist_eq, sub_zero]
    bound
  obtain ⟨hm, hp, hq, hfourth⟩ := hbound hdist
  refine ⟨hm, hp, fun y => (hq y).le, ?_⟩
  rw [ternary_fourth_central_moment a f V (ne_of_gt ha)]
  exact hfourth.le

variable (a f V : ℝ) (y : Fin 3)

/-- The mass derivative in the variance direction. -/
def ternaryVarianceDerivative : Fin 3 → ℝ :=
  ![1 / (2 * a ^ 2), -1 / a ^ 2, 1 / (2 * a ^ 2)]

/-- The mass derivative in the regression direction. -/
def ternaryMeanDerivative : Fin 3 → ℝ :=
  ![(2 * f - a) / (2 * a ^ 2), -(2 * f) / a ^ 2,
    (2 * f + a) / (2 * a ^ 2)]

/-- The second mass derivative in the regression direction. -/
def ternaryMeanSecondDerivative : Fin 3 → ℝ :=
  ![1 / a ^ 2, -2 / a ^ 2, 1 / a ^ 2]

/-- Differentiate the scalar polynomial in each of the three response cells,
then normalize the resulting derivative. -/
local macro "response_diff" : tactic => `(tactic|
  (apply HasDerivAt.congr_deriv
   · solve_by_elim (maxDepth := 12) only [hasDerivAt_id', hasDerivAt_const, HasDerivAt.div_const,
       HasDerivAt.add, HasDerivAt.sub, HasDerivAt.pow, HasDerivAt.mul, HasDerivAt.neg]
   · simp [npowRec] <;> ring))

/-- The displayed variance derivative is the actual derivative of every mass. -/
theorem ternary_hasDerivAt_variance :
    HasDerivAt (fun W => ternaryMass a f W y) (ternaryVarianceDerivative a y) V := by
  fin_cases y <;> simp [ternaryMass, ternaryVarianceDerivative] <;> response_diff

/-- The displayed regression derivative is the actual derivative. -/
theorem ternary_hasDerivAt_mean :
    HasDerivAt (fun g => ternaryMass a g V y) (ternaryMeanDerivative a f y) f := by
  fin_cases y <;> simp [ternaryMass, ternaryMeanDerivative] <;> response_diff

/-- The displayed second regression derivative is the actual derivative. -/
theorem ternary_hasDerivAt_mean_derivative :
    HasDerivAt (fun g => ternaryMeanDerivative a g y)
      (ternaryMeanSecondDerivative a y) f := by
  fin_cases y <;> simp [ternaryMeanDerivative, ternaryMeanSecondDerivative] <;> response_diff

/-- The exact heat identity for the quadratic masses. -/
theorem ternary_heat_identity :
    ternaryMeanSecondDerivative a y = 2 * ternaryVarianceDerivative a y := by
  fin_cases y <;> simp [ternaryMeanSecondDerivative, ternaryVarianceDerivative] <;> ring

/-- The exact finite-difference identity used in the small-smoothness lower bound. -/
theorem ternary_finite_difference (g V η w : ℝ) (ha : a ≠ 0) (y : Fin 3) :
    (1 / 2) * ternaryMass a (g + η * w) V y +
      (1 / 2) * ternaryMass a (g - η * w) V y - ternaryMass a g V y =
      η ^ 2 * w ^ 2 * ternaryVarianceDerivative a y := by
  fin_cases y <;> simp [ternaryMass, ternaryVarianceDerivative] <;>
    field_simp [ha] <;> ring

end

end NearlyMinimax
