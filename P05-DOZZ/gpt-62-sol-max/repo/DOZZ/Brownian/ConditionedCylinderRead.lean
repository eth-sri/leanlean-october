/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedFutureKernelMarkov
import Mathlib.Order.Fin.Tuple

/-! Reading the omitted coordinates of a Brownian cylinder from its initial and terminal states. -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace DOZZ.Proofs

/-- Restore the coordinates outside the ordered filtered subsequence using `fallback`. -/
def readFiltered {ι : Type*} [LinearOrder ι] (I : Finset ι) (p : ι → Prop) [DecidablePred p]
    (values : Fin (I.filter p).card → ℝ) (fallback : I → ℝ) : I → ℝ :=
  fun i => if hi : p i then
    values ((I.filter p).orderIsoOfFin rfl |>.symm ⟨i, Finset.mem_filter.mpr ⟨i.2, hi⟩⟩)
  else fallback i

theorem measurable_readFiltered {ι X : Type*} [LinearOrder ι] [MeasurableSpace X]
    (I : Finset ι) (p : ι → Prop) [DecidablePred p]
    {v : X → Fin (I.filter p).card → ℝ} {d : X → I → ℝ}
    (hv : Measurable v) (hd : Measurable d) : Measurable fun x => readFiltered I p (v x) (d x) := by
  refine measurable_pi_iff.mpr fun i => ?_
  by_cases hi : p i <;> simp only [readFiltered, hi, dite_true, dite_false] <;>
    exact (measurable_pi_apply _).comp (by assumption)

theorem readFiltered_restrict {ι : Type*} [LinearOrder ι] (I : Finset ι) (p : ι → Prop)
    [DecidablePred p] (f : ι → ℝ) (d : I → ℝ) (hd : ∀ i : I, ¬ p i → d i = f i) :
    readFiltered I p (fun j => f ((I.filter p).orderEmbOfFin rfl j)) d = I.restrict f := by
  funext i
  by_cases hi : p i
  · simp [readFiltered, hi, ← Finset.coe_orderIsoOfFin_apply]
  · simpa [readFiltered, hi] using hd i hi

/-- Apply the same readout to two equal finite marginals, allowing a.e. reconstruction. -/
theorem map_eq_of_read {X Y Z W : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [MeasurableSpace W] {μ : Measure X} {ν : Measure Y}
    {f : X → Z} {g : Y → Z} {r : Z → W} (hf : Measurable f) (hg : Measurable g)
    (hr : Measurable r) {a : X → W} {b : Y → W} (ha : r ∘ f =ᵐ[μ] a) (hb : r ∘ g =ᵐ[ν] b)
    (heq : μ.map f = ν.map g) : μ.map a = ν.map b := by
  rw [← Measure.map_congr ha, ← Measure.map_congr hb, ← Measure.map_map hr hf,
    ← Measure.map_map hr hg, heq]

theorem rationalFutureSchedule {n : ℕ} (t : ℝ≥0) (r : Fin n → ℚ)
    (hp : ∀ i, 0 < (r i : ℝ)) (hm : StrictMono r) :
    StrictMono (fun i => t + (r i : ℝ).toNNReal) ∧
      ∀ i, t < t + (r i : ℝ).toNNReal := by
  constructor
  · intro i j hij
    exact add_lt_add_right ((Real.toNNReal_lt_toNNReal_iff (hp j)).mpr (show (r i : ℝ) < (r j : ℝ) by exact_mod_cast hm hij)) _
  · exact fun i => lt_add_of_pos_right _ (Real.toNNReal_pos.mpr (hp i))

theorem strictMono_finAppend_endpoint {n : ℕ} {t : ℝ≥0} {s : Fin n → ℝ≥0}
    (hm : StrictMono s) (hs : ∀ i, t < s i) :
    StrictMono (Fin.append (fun _ : Fin 1 => t) s) :=
  strictMono_finAppend_of_cross _ _ (Subsingleton.strictMono _) hm (fun _ => hs)

theorem measurableSet_agree_nonpos {X : Type*} [MeasurableSpace X] {f : X → ℚ → ℝ}
    {e : X → ℝ} (hf : Measurable f) (he : Measurable e) :
    MeasurableSet {x | ∀ q : ℚ, (q : ℝ) ≤ 0 → f x q = e x} := by
  have h : {x | ∀ q : ℚ, (q : ℝ) ≤ 0 → f x q = e x} =
      ⋂ q : {q : ℚ // (q : ℝ) ≤ 0}, {x | f x q.1 = e x} := by ext; simp
  rw [h]
  exact MeasurableSet.iInter fun q => measurableSet_eq_fun ((measurable_pi_apply q.1).comp hf) he

@[simp] theorem conditionedPositiveFutureRationalEvals_nonpos (t : ℝ≥0) (p : BrownianPath)
    {q : ℚ} (hq : (q : ℝ) ≤ 0) :
    conditionedPositiveFutureRationalEvals t p q = conditionedPositiveStateAt t p := by
  change -(p (t + (q : ℝ).toNNReal)) = -(p t)
  rw [Real.toNNReal_eq_zero.mpr hq, add_zero]

end DOZZ.Proofs
