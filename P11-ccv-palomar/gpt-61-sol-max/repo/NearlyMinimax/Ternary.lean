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

/-- The support of the paper's three-point response law. -/
def ternaryValue (a : ℝ) : Fin 3 → ℝ := ![-a, 0, a]

section
variable (a f V : ℝ)
include a f V

/-- The three probability masses; positivity is proved separately. -/
def ternaryMass  : Fin 3 → ℝ :=
  ![(V + f ^ 2 - a * f) / (2 * a ^ 2),
    1 - (V + f ^ 2) / a ^ 2,
    (V + f ^ 2 + a * f) / (2 * a ^ 2)]

/-- Integration against the finite response law. -/
def ternaryExpectation  (g : ℝ → ℝ)  :=
  ∑ y : Fin 3, ternaryMass a f V y * g (ternaryValue a y)

section
variable (ha : a ≠ 0)
include ha

theorem ternary_normalized   :
    ∑ y : Fin 3, ternaryMass a f V y = 1 := by
  simp [Fin.sum_univ_succ, ternaryMass]
  field_simp [ha]
  ring

theorem ternary_mean   :
    ternaryExpectation a f V id = f := by
  simp [ternaryExpectation, Fin.sum_univ_succ, ternaryMass, ternaryValue]
  field_simp [ha]
  ring

theorem ternary_variance   :
    ternaryExpectation a f V (fun y => (y - f) ^ 2) = V := by
  simp [ternaryExpectation, Fin.sum_univ_succ, ternaryMass, ternaryValue]
  field_simp [ha]
  ring

/-- The exact centered fourth moment appearing in the paper. -/
theorem ternary_fourth_central_moment   :
    ternaryExpectation a f V (fun y => (y - f) ^ 4) =
      a ^ 2 * V + (6 * V - 3 * a ^ 2) * f ^ 2 + 3 * f ^ 4 := by
  simp [ternaryExpectation, Fin.sum_univ_succ, ternaryMass, ternaryValue]
  field_simp [ha]
  ring
end


/-- Explicit sufficient conditions for all masses to be strictly positive. -/
theorem ternary_mass_positive  (ha : 0 < a)
    (hupper : V + f ^ 2 < a ^ 2)
    (hlower : a * |f| < V + f ^ 2) :
    ∀ y , 0 < ternaryMass a f V y := by
  have ha2  := sq_pos_of_pos ha
  have hleft  := mul_le_mul_of_nonneg_left (le_abs_self f) ha.le
  have hright : -(a * f) ≤ a * |f| := by
    have := mul_le_mul_of_nonneg_left (neg_le_abs f) ha.le
    nlinarith
  intro y
  fin_cases y
  · exact div_pos (by linarith) (by positivity)
  · dsimp [ternaryMass]
    exact sub_pos.mpr ((div_lt_one ha2).mpr hupper)
  · exact div_pos (by linarith) (by positivity)

/-- Every nonnegative normalized mass is at most one. -/
theorem ternary_mass_le_one  (ha : a ≠ 0)
    (hnonneg : ∀ y, 0 ≤ ternaryMass a f V y) y :
    ternaryMass a f V y ≤ 1 := by
  linarith [ternary_normalized a f V ha, Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ y)]
end


/-- All response constraints hold uniformly in a rectangular neighborhood
of an interior zero-regression law, exactly as in Section 6.1. -/
theorem ternary_admissible_neighborhood a v vMinus vPlus C4
    (ha : 0 < a) (hv : 0 < v) (hva : v < a ^ 2)
    (hvMinus : vMinus < v) (hvPlus : v < vPlus) (hC4 : a ^ 2 * v < C4) :
    ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧
      ∀ f V , |f| ≤ ρ → |V - v| ≤ ρ →
        vMinus < V ∧ V < vPlus ∧
        (∀ y , c ≤ ternaryMass a f V y) ∧
        ternaryExpectation a f V (fun y => (y - f) ^ 4) ≤ C4 := by
  let p  := v / (2 * a ^ 2)
  let q  := 1 - v / a ^ 2
  let c  := min p q / 2
  have ha2  := sq_pos_of_pos ha
  have hp : 0 < p := div_pos hv (by positivity)
  have hq  := sub_pos.mpr ((div_lt_one ha2).mpr hva)
  have hc : 0 < c := div_pos (lt_min hp hq) (by norm_num)
  have hcp : c < p := by dsimp [c]; linarith [min_le_left p q]
  have hcq : c < q := by dsimp [c]; linarith [min_le_right p q]
  have hmass0 : ∀ y : Fin 3, c < ternaryMass a 0 v y := by
    intro y
    fin_cases y
    · simpa [ternaryMass, p] using hcp
    · simpa [ternaryMass, q] using hcq
    · simpa [ternaryMass, p] using hcp
  have hmassCont : ∀ y : Fin 3,
      Continuous (fun x : ℝ × ℝ => ternaryMass a x.1 x.2 y) := by
    intro y
    fin_cases y <;> simp [ternaryMass] <;> fun_prop
  have hmassEvent : ∀ᶠ x : ℝ × ℝ in nhds (0, v),
      ∀ y : Fin 3, c < ternaryMass a x.1 x.2 y := Filter.eventually_all.mpr (fun y =>
      continuousAt_const.eventually_lt (hmassCont y).continuousAt (hmass0 y))
  have hVMinus : ∀ᶠ x : ℝ × ℝ in nhds (0, v), vMinus < x.2 :=
    continuousAt_const.eventually_lt continuous_snd.continuousAt hvMinus
  have hVPlus : ∀ᶠ x : ℝ × ℝ in nhds (0, v), x.2 < vPlus :=
    continuous_snd.continuousAt.eventually_lt continuousAt_const hvPlus
  have hfourthCont : Continuous (fun x : ℝ × ℝ =>
      a ^ 2 * x.2 + (6 * x.2 - 3 * a ^ 2) * x.1 ^ 2 + 3 * x.1 ^ 4) := by
    fun_prop
  have hfourth : ∀ᶠ x : ℝ × ℝ in nhds (0, v),
      a ^ 2 * x.2 + (6 * x.2 - 3 * a ^ 2) * x.1 ^ 2 + 3 * x.1 ^ 4 < C4 := by
    apply hfourthCont.continuousAt.eventually_lt continuousAt_const
    simpa using hC4
  have hevent : ∀ᶠ x : ℝ × ℝ in nhds (0, v),
      vMinus < x.2 ∧ x.2 < vPlus ∧
      (∀ y : Fin 3, c < ternaryMass a x.1 x.2 y) ∧
      a ^ 2 * x.2 + (6 * x.2 - 3 * a ^ 2) * x.1 ^ 2 + 3 * x.1 ^ 4 < C4 := by
    filter_upwards [hVMinus, hVPlus, hmassEvent, hfourth] with x hm hp hq hf
    exact ⟨hm, hp, hq, hf⟩
  obtain ⟨ε, hε, hbound⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨ε / 2, c, by positivity, hc, ?_⟩
  intro f V hf hV
  have hdist : dist (f, V) (0, v) < ε := by
    simp only [Prod.dist_eq, Real.dist_eq, sub_zero]
    exact max_lt (by linarith) (by linarith)
  obtain ⟨hm, hp, hq, hfourth⟩ := hbound hdist
  grind only [ternary_fourth_central_moment]

/-- The mass derivative in the variance direction. -/
def ternaryVarianceDerivative (a : ℝ) : Fin 3 → ℝ :=
  ![1 / (2 * a ^ 2), -1 / a ^ 2, 1 / (2 * a ^ 2)]

/-- The mass derivative in the regression direction. -/
def ternaryMeanDerivative (a f : ℝ) : Fin 3 → ℝ :=
  ![(2 * f - a) / (2 * a ^ 2), -(2 * f) / a ^ 2,
    (2 * f + a) / (2 * a ^ 2)]

/-- The second mass derivative in the regression direction. -/
def ternaryMeanSecondDerivative (a : ℝ) : Fin 3 → ℝ :=
  ![1 / a ^ 2, -2 / a ^ 2, 1 / a ^ 2]

/-- The displayed variance derivative is the actual derivative of every mass. -/
theorem ternary_hasDerivAt_variance a f V y :
    HasDerivAt (fun W => ternaryMass a f W y) (ternaryVarianceDerivative a y) V := by
  fin_cases y
  · change HasDerivAt (fun W => (W + f ^ 2 - a * f) / (2 * a ^ 2))
      (1 / (2 * a ^ 2)) V
    exact ((((hasDerivAt_id V).add_const (f ^ 2)).sub_const (a * f)).div_const
      (2 * a ^ 2)).congr_deriv (by ring)
  · change HasDerivAt (fun W => 1 - (W + f ^ 2) / a ^ 2) (-1 / a ^ 2) V
    exact ((hasDerivAt_const V (1 : ℝ)).sub
      (((hasDerivAt_id V).add_const (f ^ 2)).div_const (a ^ 2))).congr_deriv (by ring)
  · change HasDerivAt (fun W => (W + f ^ 2 + a * f) / (2 * a ^ 2))
      (1 / (2 * a ^ 2)) V
    exact ((((hasDerivAt_id V).add_const (f ^ 2)).add_const (a * f)).div_const
      (2 * a ^ 2)).congr_deriv (by ring)

/-- The displayed regression derivative is the actual derivative. -/
theorem ternary_hasDerivAt_mean a f V y :
    HasDerivAt (fun g => ternaryMass a g V y) (ternaryMeanDerivative a f y) f := by
  fin_cases y
  · change HasDerivAt (fun g => (V + g ^ 2 - a * g) / (2 * a ^ 2))
      ((2 * f - a) / (2 * a ^ 2)) f
    exact ((((hasDerivAt_const f V).add ((hasDerivAt_id f).pow 2)).sub
      ((hasDerivAt_const f a).mul (hasDerivAt_id f))).div_const
      (2 * a ^ 2)).congr_deriv (by simp only [id_eq]; ring)
  · change HasDerivAt (fun g => 1 - (V + g ^ 2) / a ^ 2) (-(2 * f) / a ^ 2) f
    exact ((hasDerivAt_const f (1 : ℝ)).sub
      (((hasDerivAt_const f V).add ((hasDerivAt_id f).pow 2)).div_const
      (a ^ 2))).congr_deriv (by simp only [id_eq]; ring)
  · change HasDerivAt (fun g => (V + g ^ 2 + a * g) / (2 * a ^ 2))
      ((2 * f + a) / (2 * a ^ 2)) f
    exact ((((hasDerivAt_const f V).add ((hasDerivAt_id f).pow 2)).add
      ((hasDerivAt_const f a).mul (hasDerivAt_id f))).div_const
      (2 * a ^ 2)).congr_deriv (by simp only [id_eq]; ring)

/-- The displayed second regression derivative is the actual derivative. -/
theorem ternary_hasDerivAt_mean_derivative a f y :
    HasDerivAt (fun g => ternaryMeanDerivative a g y)
      (ternaryMeanSecondDerivative a y) f := by
  fin_cases y
  · change HasDerivAt (fun g => (2 * g - a) / (2 * a ^ 2)) (1 / a ^ 2) f
    exact ((((hasDerivAt_id f).const_mul 2).sub_const a).div_const
      (2 * a ^ 2)).congr_deriv (by simp [div_eq_mul_inv]; ring)
  · change HasDerivAt (fun g => -(2 * g) / a ^ 2) (-2 / a ^ 2) f
    exact (((hasDerivAt_id f).const_mul 2).neg.div_const
      (a ^ 2)).congr_deriv (by ring)
  · change HasDerivAt (fun g => (2 * g + a) / (2 * a ^ 2)) (1 / a ^ 2) f
    exact ((((hasDerivAt_id f).const_mul 2).add_const a).div_const
      (2 * a ^ 2)).congr_deriv (by simp [div_eq_mul_inv]; ring)

/-- The exact heat identity for the quadratic masses. -/
theorem ternary_heat_identity a y :
    ternaryMeanSecondDerivative a y = 2 * ternaryVarianceDerivative a y := by
  fin_cases y <;> simp [ternaryMeanSecondDerivative, ternaryVarianceDerivative] <;> ring

/-- The exact finite-difference identity used in the small-smoothness lower bound. -/
theorem ternary_finite_difference a g V η w (ha : a ≠ 0) y :
    (1 / 2) * ternaryMass a (g + η * w) V y +
      (1 / 2) * ternaryMass a (g - η * w) V y - ternaryMass a g V y =
      η ^ 2 * w ^ 2 * ternaryVarianceDerivative a y := by
  fin_cases y <;> simp [ternaryMass, ternaryVarianceDerivative] <;>
    field_simp [ha] <;> ring

end

end NearlyMinimax
