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

/-- The three probability masses; positivity is proved separately. -/
def ternaryMass (a f V : ℝ) : Fin 3 → ℝ :=
  ![(V + f ^ 2 - a * f) / (2 * a ^ 2),
    1 - (V + f ^ 2) / a ^ 2,
    (V + f ^ 2 + a * f) / (2 * a ^ 2)]

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

def ternaryLinearTerm (a : ℝ) : Fin 3 → ℝ := ![-a / (2 * a ^ 2), 0, a / (2 * a ^ 2)]

/-- The response mass is a single quadratic in the regression and affine in the variance. -/
theorem ternary_mass_quadratic (a f V : ℝ) (y : Fin 3) :
    ternaryMass a f V y = ![0,1,0] y +
      (V + f ^ 2) * ternaryVarianceDerivative a y + f * ternaryLinearTerm a y := by
  fin_cases y <;> simp [ternaryMass, ternaryVarianceDerivative, ternaryLinearTerm, div_eq_mul_inv] <;> ring

theorem ternary_mean_affine (a f : ℝ) (y : Fin 3) :
    ternaryMeanDerivative a f y = 2 * f * ternaryVarianceDerivative a y + ternaryLinearTerm a y := by
  fin_cases y <;> simp [ternaryMeanDerivative, ternaryVarianceDerivative, ternaryLinearTerm, div_eq_mul_inv] <;> ring

@[fun_prop] theorem ternaryMass_joint_continuous (a : ℝ) (y : Fin 3) :
    Continuous (fun z : ℝ × ℝ => ternaryMass a z.1 z.2 y) := by
  simp_rw [ternary_mass_quadratic a _ _ y]
  fun_prop

@[fun_prop] theorem ternaryMass_measurable {α : Type*} [MeasurableSpace α] (a : ℝ)
    {f V : α → ℝ} {y : α → Fin 3} (hf : Measurable f) (hV : Measurable V) (hy : Measurable y) :
    Measurable (fun x => ternaryMass a (f x) (V x) (y x)) := by
  have hm : Measurable (fun z : (ℝ × ℝ) × Fin 3 => ternaryMass a z.1.1 z.1.2 z.2) :=
    measurable_from_prod_countable_left fun y => (ternaryMass_joint_continuous a y).measurable
  exact hm.comp ((hf.prodMk hV).prodMk hy)

/-- Integration against the finite response law. -/
def ternaryExpectation (a f V : ℝ) (g : ℝ → ℝ) : ℝ :=
  ∑ y : Fin 3, ternaryMass a f V y * g (ternaryValue a y)

section
variable (a f V : ℝ)

section
variable (ha : a ≠ 0)
include ha

omit ha in
theorem ternary_normalized :
    ∑ y : Fin 3, ternaryMass a f V y = 1 := by
  simp [Fin.sum_univ_succ, ternaryMass]
  ring

theorem ternary_mean :
    ternaryExpectation a f V id = f := by
  simp [ternaryExpectation, Fin.sum_univ_succ, ternaryMass, ternaryValue]
  field_simp [ha]
  ring

theorem ternary_variance :
    ternaryExpectation a f V (fun y => (y - f) ^ 2) = V := by
  simp [ternaryExpectation, Fin.sum_univ_succ, ternaryMass, ternaryValue]
  field_simp [ha]
  ring

/-- The exact centered fourth moment appearing in the paper. -/
theorem ternary_fourth_central_moment :
    ternaryExpectation a f V (fun y => (y - f) ^ 4) =
      a ^ 2 * V + (6 * V - 3 * a ^ 2) * f ^ 2 + 3 * f ^ 4 := by
  simp [ternaryExpectation, Fin.sum_univ_succ, ternaryMass, ternaryValue]
  field_simp [ha]
  ring

end

/-- Explicit sufficient conditions for all masses to be strictly positive. -/
theorem ternary_mass_positive (ha : 0 < a)
    (hupper : V + f ^ 2 < a ^ 2)
    (hlower : a * |f| < V + f ^ 2) :
    ∀ y : Fin 3, 0 < ternaryMass a f V y := by
  have ha2 := sq_pos_of_pos ha
  have hleft := mul_le_mul_of_nonneg_left (le_abs_self f) ha.le
  have hright : -(a * f) ≤ a * |f| := by
    have := mul_le_mul_of_nonneg_left (neg_le_abs f) ha.le
    nlinarith
  intro y
  fin_cases y
  · exact div_pos (by linarith) (by positivity)
  · exact sub_pos.mpr ((div_lt_one ha2).mpr hupper)
  · exact div_pos (by linarith) (by positivity)

/-- Every nonnegative normalized mass is at most one. -/
theorem ternary_mass_le_one (ha : a ≠ 0)
    (hnonneg : ∀ y, 0 ≤ ternaryMass a f V y) (y : Fin 3) :
    ternaryMass a f V y ≤ 1 := by
  rw [← ternary_normalized a f V]
  apply Finset.single_le_sum <;> simp_all

end

/-- All response constraints hold uniformly in a rectangular neighborhood
of an interior zero-regression law, exactly as in Section 6.1. -/
theorem ternary_admissible_neighborhood (a v vMinus vPlus C4 : ℝ)
    (ha : 0 < a) (hv : 0 < v) (hva : v < a ^ 2)
    (hvMinus : vMinus < v) (hvPlus : v < vPlus) (hC4 : a ^ 2 * v < C4) :
    ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧
      ∀ f V : ℝ, |f| ≤ ρ → |V - v| ≤ ρ →
        vMinus < V ∧ V < vPlus ∧
        (∀ y : Fin 3, c ≤ ternaryMass a f V y) ∧
        ternaryExpectation a f V (fun y => (y - f) ^ 4) ≤ C4 := by
  let p := v / (2 * a ^ 2)
  let q := 1 - v / a ^ 2
  let c := min p q / 2
  have ha2 := sq_pos_of_pos ha
  have hp : 0 < p := div_pos hv (by positivity)
  have hq := sub_pos.mpr ((div_lt_one ha2).mpr hva)
  have hc : 0 < c := div_pos (lt_min hp hq) (by norm_num)
  have hcp : c < p := by grind
  have hcq : c < q := by grind
  have hmass0 : ∀ y : Fin 3, c < ternaryMass a 0 v y := by
    intro y
    fin_cases y
    · simpa [ternaryMass, p] using hcp
    · simpa [ternaryMass, q] using hcq
    · simpa [ternaryMass, p] using hcp
  have hmassEvent : ∀ᶠ x : ℝ × ℝ in nhds (0, v),
      ∀ y : Fin 3, c < ternaryMass a x.1 x.2 y := by
    exact Filter.eventually_all.mpr (fun y =>
      continuousAt_const.eventually_lt (ternaryMass_joint_continuous a y).continuousAt (hmass0 y))
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
    linarith
  have hevent : ∀ᶠ x : ℝ × ℝ in nhds (0, v),
      vMinus < x.2 ∧ x.2 < vPlus ∧
      (∀ y : Fin 3, c < ternaryMass a x.1 x.2 y) ∧
      a ^ 2 * x.2 + (6 * x.2 - 3 * a ^ 2) * x.1 ^ 2 + 3 * x.1 ^ 4 < C4 := by
    filter_upwards [hVMinus, hVPlus, hmassEvent, hfourth] with x hm hp hq hf
    tauto
  obtain ⟨ε, hε, hbound⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨ε / 2, c, by positivity, hc, ?_⟩
  intro f V hf hV
  have hdist : dist (f, V) (0, v) < ε := by
    simp only [Prod.dist_eq, Real.dist_eq, sub_zero]
    exact max_lt (by linarith) (by linarith)
  obtain ⟨hm, hp, hq, hfourth⟩ := hbound hdist
  grind [ternary_fourth_central_moment]

section
variable (a f V : ℝ) (y : Fin 3)

/-- The displayed variance derivative is the actual derivative of every mass. -/
theorem ternary_hasDerivAt_variance :
    HasDerivAt (fun W => ternaryMass a f W y) (ternaryVarianceDerivative a y) V := by
  simp_rw [ternary_mass_quadratic a f _ y]
  convert ((((hasDerivAt_id V).add_const (f ^ 2)).mul_const
    (ternaryVarianceDerivative a y)).const_add (![0,1,0] y)).add_const
      (f * ternaryLinearTerm a y) using 1 <;> (try funext W) <;> (try simp only [id_eq]) <;> ring

/-- The displayed regression derivative is the actual derivative. -/
theorem ternary_hasDerivAt_mean :
    HasDerivAt (fun g => ternaryMass a g V y) (ternaryMeanDerivative a f y) f := by
  simp_rw [ternary_mass_quadratic a _ V y]
  rw [ternary_mean_affine a f y]
  exact ((((((hasDerivAt_id f).pow 2).const_add V).mul_const
    (ternaryVarianceDerivative a y)).const_add (![0,1,0] y)).add
      ((hasDerivAt_id f).mul_const (ternaryLinearTerm a y))).congr_deriv (by simp only [id_eq]; ring)

end

/-- The exact heat identity for the quadratic masses. -/
theorem ternary_heat_identity (a : ℝ) (y : Fin 3) :
    ternaryMeanSecondDerivative a y = 2 * ternaryVarianceDerivative a y := by
  fin_cases y <;> simp [ternaryMeanSecondDerivative, ternaryVarianceDerivative] <;> ring

/-- The displayed second regression derivative is the actual derivative. -/
theorem ternary_hasDerivAt_mean_derivative (a f : ℝ) (y : Fin 3) :
    HasDerivAt (fun g => ternaryMeanDerivative a g y)
      (ternaryMeanSecondDerivative a y) f := by
  simp_rw [ternary_mean_affine, ternary_heat_identity]
  exact ((((hasDerivAt_id f).const_mul 2).mul_const (ternaryVarianceDerivative a y)).add_const
    (ternaryLinearTerm a y)).congr_deriv (by ring)

/-- Directional derivatives along an affine regression path. -/
theorem ternary_hasDerivAt_line (a f V δ z : ℝ) (y : Fin 3) :
    HasDerivAt (fun t => ternaryMass a (f + t * δ) V y)
      (δ * ternaryMeanDerivative a (f + z * δ) y) z := by
  have h := (ternary_hasDerivAt_mean a (f + z * δ) V y).comp z
    (((hasDerivAt_id z).mul_const δ).const_add f)
  exact h.congr_deriv (by ring)

theorem ternary_hasDerivAt_line_first (a f δ z : ℝ) (y : Fin 3) :
    HasDerivAt (fun t => δ * ternaryMeanDerivative a (f + t * δ) y)
      (δ ^ 2 * ternaryMeanSecondDerivative a y) z := by
  have h := ((ternary_hasDerivAt_mean_derivative a (f + z * δ) y).comp z
    (((hasDerivAt_id z).mul_const δ).const_add f)).const_mul δ
  exact h.congr_deriv (by ring)

/-- The exact finite-difference identity used in the small-smoothness lower bound. -/
theorem ternary_finite_difference (a g V η w : ℝ) (y : Fin 3) :
    (1 / 2 : ℝ) * ternaryMass a (g + η * w) V y +
      (1 / 2 : ℝ) * ternaryMass a (g - η * w) V y - ternaryMass a g V y =
      η ^ 2 * w ^ 2 * ternaryVarianceDerivative a y := by
  simp_rw [ternary_mass_quadratic a _ V y]
  ring

end

end NearlyMinimax
