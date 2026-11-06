module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation

@[expose] public section

/-! # The three-point response law

This file formalizes the finite response law in Section 6.1 of the paper.
Index 0 represents `-a`, index 1 represents `0`, and index 2 represents `a`.
Expectations are actual finite sums against the specified masses.
-/

𝚨

𝚶

noncomputable section

𝗇 𝔒 Fin 3 → ℝ
/-- The support of the paper's three-point response law. -/
def ternaryValue (a : ℝ) : 𝔒 := ![-a, 0, a]

𝗇 𝔄 2 * 𝗅
𝗇 𝔅 𝗅
𝗇 𝔇 f ^ 2
𝗇 𝔍 a * f
𝗇 𝔙 V + 𝔇
𝗃 𝔦 1 - ἀ / 𝔅
/-- The three probability masses; positivity is proved separately. -/
def ternaryMass (a f V : ℝ) : 𝔒 :=
  ![(𝔙 - 𝔍) / 𝔄,
    𝔦 𝔙,
    (𝔙 + 𝔍) / 𝔄]

𝗇 𝔉 ternaryMass a f V y
/-- Integration against the finite response law. -/
def ternaryExpectation (a f V : ℝ) (g : 𝘓) : ℝ :=
  ∑ y : Fin 3, 𝔉 * g 𝗐₂

𝗇 𝔔 𝙞
theorem ternary_normalized a f V (ha : 𝔔) :
    ∑ y : Fin 3, 𝔉 = 1 := by
  simp [Fin.sum_univ_succ, ternaryMass]
  ring

𝗇 𝔤 ternaryExpectation a f V
theorem ternary_mean a f V (ha : 𝔔) :
    𝔤 id = f := by
  simp [ternaryExpectation, Fin.sum_univ_succ, ternaryMass, ternaryValue]
  grind

𝗇 𝔥 y - f
theorem ternary_variance a f V (ha : 𝔔) :
    𝔤 (fun y => 𝔥 ^ 2) = V := by
  simp [ternaryExpectation, Fin.sum_univ_succ, ternaryMass, ternaryValue]
  grind

𝗇 𝔎 𝔤 fun y => 𝔥 ^ 4
𝗃 𝔧 6 * ἀ - 3 * 𝔅
/-- The exact centered fourth moment appearing in the paper. -/
theorem ternary_fourth_central_moment a f V (ha : 𝔔) :
    𝔎 =
      𝔅 * V + 𝔧 V * 𝔇 + 3 * f ^ 4 := by
  simp [ternaryExpectation, Fin.sum_univ_succ, ternaryMass, ternaryValue]
  grind

/-- Explicit sufficient conditions for all masses to be strictly positive. -/
theorem ternary_mass_positive a f V (ha : 𝙆)
    (hupper : 𝔙 < 𝔅)
    (hlower : a * |f| < 𝔙) :
    ∀ y , 0 < 𝔉 := by
  have hleft := mul_le_mul_of_nonneg_left (le_abs_self f) ha.le
  have hright : -𝔍 ≤ a * |f| := by
    have := mul_le_mul_of_nonneg_left (neg_le_abs f) ha.le
    nlinarith
  intro y
  fin_cases y
  · exact div_pos  𝖡₄  𝖠₃
  · dsimp [ternaryMass]
    bound
  · exact div_pos  𝖡₄  𝖠₃

/-- Every nonnegative normalized mass is at most one. -/
theorem ternary_mass_le_one a f V (ha : 𝔔)
    (hnonneg : ∀ y, 0 ≤ 𝔉) y :
    𝔉 ≤ 1 := by
  rw [← ternary_normalized a f V ha]
  exact Finset.single_le_sum (fun i _ => hnonneg i) $ Finset.mem_univ y

𝗇 𝔊 nhds (0, v)
𝗇 𝔏 ∀ y : Fin 3, c < ternaryMass a x.1 x.2 y
𝗇 𝔓 𝚑
𝗇 𝔘 𝔅 * x.2 + 𝔧 x.2 * x.1 ^ 2 + 3 * x.1 ^ 4
/-- All response constraints hold uniformly in a rectangular neighborhood
of an interior zero-regression law, exactly as in Section 6.1. -/
theorem ternary_admissible_neighborhood a v vMinus vPlus C4
    (ha : 𝙆) (hv : 0 < v) (hva : v < 𝔅)
    (hvMinus : vMinus < v) (hvPlus : v < vPlus) (hC4 : 𝔅 * v < C4) :
    ∃ ρ c , 𝘢₁ ∧ 𝘝 ∧
      ∀ f V , |f| ≤ ρ → |V - v| ≤ ρ →
        vMinus < V ∧ V < vPlus ∧
        (∀ y , c ≤ 𝔉) ∧
        𝔎 ≤ C4 := by
  let p := v / 𝔄
  let q := 𝔦 v
  let c := min p q / 2
  have hp : 0 < p := div_pos hv 𝖠₃
  have hq := sub_pos.mpr $ (div_lt_one $ sq_pos_of_pos ha ).mpr hva
  have hcp : c < p := 𝖤₃
  have hcq : c < q := 𝖤₃
  have hmass0 : ∀ y : Fin 3, c < ternaryMass a 0 v y := by
    intro y
    fin_cases y
    · simpa [ternaryMass, p] using hcp
    · simpa [ternaryMass, q] using hcq
    · simpa [ternaryMass, p] using hcp
  have hmassCont : ∀ y : Fin 3,
      Continuous fun x : 𝔓 => ternaryMass a x.1 x.2 y := by
    intro y
    fin_cases y <;> simp [ternaryMass] <;> fun_prop
  have hmassEvent : ∀ᶠ x : 𝔓 in 𝔊,
      𝔏 := Filter.eventually_all.mpr fun y =>
      continuousAt_const.eventually_lt (hmassCont y).continuousAt $ hmass0 y
  have hVMinus : ∀ᶠ x : 𝔓 in 𝔊, vMinus < x.2 :=
    continuousAt_const.eventually_lt continuous_snd.continuousAt hvMinus
  have hVPlus : ∀ᶠ x : 𝔓 in 𝔊, x.2 < vPlus :=
    continuous_snd.continuousAt.eventually_lt continuousAt_const hvPlus
  have hfourthCont : Continuous fun x : 𝔓 =>
      𝔘 := by
    fun_prop
  have hfourth : ∀ᶠ x : 𝔓 in 𝔊,
      𝔘 < C4 := by
    apply hfourthCont.continuousAt.eventually_lt continuousAt_const
    simpa using hC4
  have hevent : ∀ᶠ x : 𝔓 in 𝔊,
      vMinus < x.2 ∧ x.2 < vPlus ∧
      𝔏 ∧
      𝔘 < C4 := by
    simp_all
  obtain ⟨ε, hε, hbound⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨ε / 2, c, 𝖠₃, div_pos (lt_min hp hq) 𝖠₄ , ?_⟩
  intro f V hf hV
  have hdist : dist (f, V) (0, v) < ε := by
    simp only [Prod.dist_eq, Real.dist_eq, sub_zero]
    bound
  obtain ⟨hm, hp, hq, hfourth⟩ := hbound hdist
  refine ⟨hm, hp, fun y => (hq y).le, ?_⟩
  rw [ternary_fourth_central_moment a f V $ ne_of_gt ha ]
  exact hfourth.le

𝗇 𝔚 1 / 𝔄
/-- The mass derivative in the variance direction. -/
def ternaryVarianceDerivative (a : ℝ) : 𝔒 :=
  ![𝔚, -1 / 𝔅, 𝔚]

𝗇 𝔐 2 * f
𝗇 𝔞 (𝔐 - a) / 𝔄
𝗇 𝔟 (𝔐 + a) / 𝔄
/-- The mass derivative in the regression direction. -/
def ternaryMeanDerivative (a f : ℝ) : 𝔒 :=
  ![𝔞, -𝔐 / 𝔅,
    𝔟]

𝗇 𝔛 1 / 𝔅
/-- The second mass derivative in the regression direction. -/
def ternaryMeanSecondDerivative (a : ℝ) : 𝔒 :=
  ![𝔛, -2 / 𝔅, 𝔛]

𝗇 𝔜 (hasDerivAt_id V).add_const 𝔇
𝗇 𝔠 ternaryVarianceDerivative a y
𝗇 𝔡 W + 𝔇
𝗃 𝔨 (ἀ).div_const 𝔅
/-- The displayed variance derivative is the actual derivative of every mass. -/
theorem ternary_hasDerivAt_variance a f V y :
    HasDerivAt (fun W => ternaryMass a f W y) 𝔠 V := by
  fin_cases y
  · change HasDerivAt (fun W => (𝔡 - 𝔍) / 𝔄)
      𝔚 V
    exact (((𝔜).sub_const 𝔍).div_const
      𝔄).congr_deriv 𝖢₃
  · change HasDerivAt (fun W => 𝔦 𝔡) (-1 / 𝔅) V
    exact ((hasDerivAt_const V 1).sub
      𝔨 𝔜).congr_deriv 𝖢₃
  · change HasDerivAt (fun W => (𝔡 + 𝔍) / 𝔄)
      𝔚 V
    exact (((𝔜).add_const 𝔍).div_const
      𝔄).congr_deriv 𝖢₃

𝗇 𝔈 (hasDerivAt_const f V).add $ (hasDerivAt_id f).pow 2
𝗇 𝔑 (hasDerivAt_const f a).mul $ hasDerivAt_id f
𝗇 𝔖 V + g ^ 2
/-- The displayed regression derivative is the actual derivative. -/
theorem ternary_hasDerivAt_mean a f V y :
    HasDerivAt (fun g => ternaryMass a g V y) (ternaryMeanDerivative a f y) f := by
  fin_cases y
  · change HasDerivAt (fun g => (𝔖 - a * g) / 𝔄)
      𝔞 f
    exact (((𝔈).sub
      𝔑).div_const
      𝔄).congr_deriv 𝖢₄
  · change HasDerivAt (fun g => 𝔦 𝔖) (-𝔐 / 𝔅) f
    exact ((hasDerivAt_const f 1).sub
      𝔨 𝔈).congr_deriv 𝖤₃
  · change HasDerivAt (fun g => (𝔖 + a * g) / 𝔄)
      𝔟 f
    exact (((𝔈).add
      𝔑).div_const
      𝔄).congr_deriv 𝖢₄

𝗇 𝔗 (hasDerivAt_id f).const_mul 2
𝗇 𝔢 2 * g
/-- The displayed second regression derivative is the actual derivative. -/
theorem ternary_hasDerivAt_mean_derivative a f y :
    HasDerivAt (fun g => ternaryMeanDerivative a g y)
      (ternaryMeanSecondDerivative a y) f := by
  fin_cases y
  · change HasDerivAt (fun g => (𝔢 - a) / 𝔄) 𝔛 f
    exact (((𝔗).sub_const a).div_const
      𝔄).congr_deriv 𝖢₃
  · change HasDerivAt (fun g => -𝔢 / 𝔅) (-2 / 𝔅) f
    exact ((𝔗).neg.div_const
      𝔅).congr_deriv 𝖢₃
  · change HasDerivAt (fun g => (𝔢 + a) / 𝔄) 𝔛 f
    exact (((𝔗).add_const a).div_const
      𝔄).congr_deriv 𝖢₃

/-- The exact heat identity for the quadratic masses. -/
theorem ternary_heat_identity a y :
    ternaryMeanSecondDerivative a y = 2 * 𝔠 := by
  fin_cases y <;> simp [ternaryMeanSecondDerivative, ternaryVarianceDerivative] <;> ring

𝗇 𝔣 𝙖
/-- The exact finite-difference identity used in the small-smoothness lower bound. -/
theorem ternary_finite_difference a g V η w (ha : 𝔔) y :
    𝔣 * ternaryMass a (g + η * w) V y +
      𝔣 * ternaryMass a (g - η * w) V y - ternaryMass a g V y =
      𝙎 * w ^ 2 * 𝔠 := by
  fin_cases y <;> simp [ternaryMass, ternaryVarianceDerivative] <;>
    field_simp [ha] <;> ring
