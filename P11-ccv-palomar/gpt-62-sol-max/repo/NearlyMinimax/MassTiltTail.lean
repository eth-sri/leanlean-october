module

public import NearlyMinimax.HighMassTilt


@[expose] public section

/-!
# Genuine mass-power tilt tail from an exponential moment bound
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace NearlyMinimax

variable {Ω : Type*} [MeasurableSpace Ω]

section
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m)
include hm

section
variable (n : ℕ) (l b : ℝ) (hl : 0 < l)
    (hbound : ∀ ω, l ≤ m ω ∧ m ω ≤ b)
include hl hbound

/-- The source mean-one power normalizer is at least one, by the actual tangent inequality. -/
theorem massPowerNormalizer_one_le (hmean : ∫ ω, m ω ∂μ = 1) :
    1 ≤ massPowerNormalizer μ m n := by
  have hi := massPower_integrable μ m hm 1 l b hl hbound
  have him : Integrable m μ := by simpa only [pow_one] using hi
  have hip := massPower_integrable μ m hm n l b hl hbound
  have hh : (∫ ω, 1 + (n : ℝ) * (m ω - 1) ∂μ) ≤ ∫ ω, m ω ^ n ∂μ :=
    integral_mono ((integrable_const 1).add ((him.sub (integrable_const 1)).const_mul (n : ℝ))) hip
      (fun ω => one_add_mul_sub_le_pow ((by norm_num : (-1 : ℝ) ≤ 0).trans (hl.le.trans (hbound ω).1)) n)
  have he : (∫ ω, 1 + (n : ℝ) * (m ω - 1) ∂μ) = 1 := by
    calc
      _ = (∫ _ : Ω, (1 : ℝ) ∂μ) + ∫ ω, (n : ℝ) * (m ω - 1) ∂μ :=
        integral_add (integrable_const 1) ((him.sub (integrable_const 1)).const_mul (n : ℝ))
      _ = 1 := by simp [integral_const_mul, integral_sub him (integrable_const 1), hmean]
  rw [he] at hh
  exact hh

/-- The true mass-power tilt of a measurable event is its normalized weighted indicator integral. -/
theorem massPowerTilt_real_apply (S : Set Ω) (hS : MeasurableSet S) :
    (massPowerTilt μ m n).real S =
      ∫ ω, S.indicator (fun ω => m ω ^ n / massPowerNormalizer μ m n) ω ∂μ := by
  let := massPowerTilt_isProbability μ m hm n l b hl hbound
  have hG := massPowerNormalizer_pos μ m hm n l b hl hbound
  rw [← integral_indicator_one hS, massPowerTilt,
    integral_realDensity ((hm.pow_const n).div_const _)
      (fun ω => div_nonneg (pow_nonneg (hl.le.trans (hbound ω).1) _) hG.le)]
  refine integral_congr_ae (.of_forall fun ω => ?_)
  by_cases hω : ω ∈ S <;> simp [hω]

end

/-- A positive bounded mass has an integrable exponential at every real parameter. -/
theorem boundedMass_exp_integrable (l b : ℝ) (hl : 0 < l)
    (hbound : ∀ ω, l ≤ m ω ∧ m ω ≤ b) (u : ℝ) :
    Integrable (fun ω => Real.exp (u * (m ω - 1))) μ := by
  apply Integrable.of_bound (Real.measurable_exp.comp (measurable_const.mul (hm.sub measurable_const))).aestronglyMeasurable
    (Real.exp (|u| * (|b| + 1)))
  apply Eventually.of_forall
  intro ω
  change ‖Real.exp (u * (m ω - 1))‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  exact (le_abs_self _).trans (by grind [mul_le_mul_of_nonneg_left])

/-- Bound a tilted event by a pointwise exponential majorant of its mass power. -/
private theorem massPowerTilt_event_le (n : ℕ) (l b : ℝ) (hl : 0 < l)
    (hbound : ∀ ω, l ≤ m ω ∧ m ω ≤ b) (hmean : ∫ ω, m ω ∂μ = 1)
    (S : Set Ω) (hS : MeasurableSet S) (t k : ℝ)
    (hpow : ∀ ω ∈ S, m ω ^ n ≤ Real.exp (t * (m ω - 1) + k)) :
    (massPowerTilt μ m n).real S ≤
      Real.exp k * ∫ ω, Real.exp (t * (m ω - 1)) ∂μ := by
  rw [massPowerTilt_real_apply μ m hm n l b hl hbound S hS, ← integral_const_mul]
  apply integral_mono ((massPower_integrable μ m hm n l b hl hbound).div_const _ |>.indicator hS)
    ((boundedMass_exp_integrable μ m hm l b hl hbound t).const_mul _)
  intro ω
  by_cases hω : ω ∈ S
  · simp only [indicator_of_mem hω, ← Real.exp_add, add_comm k]
    exact (div_le_self (pow_nonneg (hl.le.trans (hbound ω).1) n)
      (massPowerNormalizer_one_le μ m hm n l b hl hbound hmean)).trans (hpow ω hω)
  · rw [indicator_of_notMem hω]
    positivity

end

section
variable (a ε : ℝ)

/-- The exact source ε≥8an guard controls the positive-side tilted exponent. -/
theorem massTilt_exponent_right (n : ℕ) (ha : 0 < a)
    (hε : 8 * a * (n : ℝ) ≤ ε) :
    0 ≤ ε / (2 * a) - (n : ℝ) ∧
      -(ε / (2 * a) - (n : ℝ)) * ε + a * ((n : ℝ) + (ε / (2 * a) - (n : ℝ))) ^ 2 ≤
        -ε ^ 2 / (8 * a) := by
  have he0 := (by positivity : (0 : ℝ) ≤ 8 * a * (n : ℝ)).trans hε
  have hu : 0 ≤ ε / (2 * a) - (n : ℝ) := by
    field_simp <;> linarith
  have he : (n : ℝ) * ε ≤ ε ^ 2 / (8 * a) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * a)).2
    nlinarith [mul_nonneg he0 (sub_nonneg.2 hε)]
  have hid : -(ε / (2 * a) - (n : ℝ)) * ε + a * ((n : ℝ) + (ε / (2 * a) - (n : ℝ))) ^ 2 =
      (n : ℝ) * ε - 2 * (ε ^ 2 / (8 * a)) := by field_simp; ring
  grind

/-- The exact source lower-tail exponent before weakening its constant. -/
theorem massTilt_exponent_left (ha : 0 < a) :
    -(ε / (2 * a)) * ε + a * (-(ε / (2 * a))) ^ 2 ≤ -ε ^ 2 / (8 * a) := by
  have hid : -(ε / (2 * a)) * ε + a * (-(ε / (2 * a))) ^ 2 =
      -2 * (ε ^ 2 / (8 * a)) := by field_simp; ring
  rw [hid]
  simp only [neg_div]
  have hn : 0 ≤ ε ^ 2 / (8 * a) := div_nonneg (sq_nonneg _) (by positivity)
  linarith

end

/-- The source mass-power tilted exceptional tail follows from its actual mean-one MGF.
This is a probability lemma; the history MGF is established independently from finite label blocks. -/
theorem massPowerTilt_abs_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m) (n : ℕ) (l b : ℝ) (hl : 0 < l)
    (hbound : ∀ ω, l ≤ m ω ∧ m ω ≤ b) (hmean : ∫ ω, m ω ∂μ = 1)
    (a ε : ℝ) (ha : 0 < a)
    (hmgf : ∀ u : ℝ, (∫ ω, Real.exp (u * (m ω - 1)) ∂μ) ≤ Real.exp (a * u ^ 2))
    (hε : 8 * a * (n : ℝ) ≤ ε) :
    (massPowerTilt μ m n).real {ω | ε < |m ω - 1|} ≤ 2 * Real.exp (-ε ^ 2 / (8 * a)) := by
  let := massPowerTilt_isProbability μ m hm n l b hl hbound
  have he0 := (by positivity : (0 : ℝ) ≤ 8 * a * (n : ℝ)).trans hε
  have hr : (massPowerTilt μ m n).real {ω | ε < m ω - 1} ≤ Real.exp (-ε ^ 2 / (8 * a)) := by
    have hs := massTilt_exponent_right a ε n ha hε
    calc
      _ ≤ Real.exp (-(ε / (2 * a) - (n : ℝ)) * ε) *
          ∫ ω, Real.exp (((n : ℝ) + (ε / (2 * a) - (n : ℝ))) * (m ω - 1)) ∂μ :=
        by
          apply massPowerTilt_event_le μ m hm n l b hl hbound hmean _
            (measurableSet_lt measurable_const (hm.sub measurable_const))
          intro ω hω
          have hb : m ω ≤ Real.exp (m ω - 1) := by linarith [Real.add_one_le_exp (m ω - 1)]
          apply (pow_le_pow_left₀ (hl.le.trans (hbound ω).1) hb n).trans
          change ε < m ω - 1 at hω
          rw [← Real.exp_nat_mul]
          exact Real.exp_le_exp.2 (by nlinarith [mul_nonneg hs.1 (sub_nonneg.2 hω.le)])
      _ ≤ Real.exp (-(ε / (2 * a) - (n : ℝ)) * ε) *
          Real.exp (a * ((n : ℝ) + (ε / (2 * a) - (n : ℝ))) ^ 2) :=
        mul_le_mul_of_nonneg_left (hmgf _) (Real.exp_pos _).le
      _ ≤ _ := by simp_all [← Real.exp_add]
  have hlower : (massPowerTilt μ m n).real {ω | m ω - 1 < -ε} ≤ Real.exp (-ε ^ 2 / (8 * a)) := by
    calc
      _ ≤ Real.exp (-(ε / (2 * a)) * ε) * ∫ ω, Real.exp ((-(ε / (2 * a))) * (m ω - 1)) ∂μ :=
        by
          apply massPowerTilt_event_le μ m hm n l b hl hbound hmean _
            (measurableSet_lt (hm.sub measurable_const) measurable_const)
          intro ω hω
          change m ω - 1 < -ε at hω
          refine (pow_le_one₀ (hl.le.trans (hbound ω).1) (by linarith)).trans (Real.one_le_exp_iff.2 ?_)
          nlinarith [mul_nonneg (div_nonneg he0 (by positivity : 0 ≤ 2 * a)) (sub_nonneg.2 hω.le)]
      _ ≤ Real.exp (-(ε / (2 * a)) * ε) * Real.exp (a * (-(ε / (2 * a))) ^ 2) :=
        mul_le_mul_of_nonneg_left (hmgf _) (Real.exp_pos _).le
      _ ≤ _ := by rw [← Real.exp_add]; exact Real.exp_le_exp.2 (massTilt_exponent_left a ε ha)
  have hset : {ω | ε < |m ω - 1|} = {ω | ε < m ω - 1} ∪ {ω | m ω - 1 < -ε} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, lt_abs]
    refine or_congr Iff.rfl ?_
    constructor <;> intro h <;> linarith
  rw [hset]
  exact (measureReal_union_le _ _).trans (by linarith)

end NearlyMinimax
