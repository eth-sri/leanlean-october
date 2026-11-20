module

public import Mathlib
public import PottsDiscontinuity.FK.Expectation

/-! # Disintegration of a finite probability mass function over an observation -/

@[expose] public section

open MeasureTheory Set
open scoped Classical BigOperators
namespace PottsDiscontinuity.FK.FiniteProbability

variable {α β : Type*}

/-- Exact disintegration of a PMF over the fibers of an observation. -/
theorem pmf_eq_bind_fiber_filter (p : PMF α) (f : α → β)
    (hf : ∀ b, ∃ a ∈ {x | f x = b}, a ∈ p.support) :
    p = (p.map f).bind (fun b => p.filter {x | f x = b} (hf b)) := by
  classical
  have hden (b : β) : (∑' x, ({x | f x = b} : Set α).indicator p x) = (p.map f) b := by
    simp [Set.indicator, eq_comm]
  ext a
  symm
  rw [PMF.bind_apply]
  have hterm (b : β) : (p.map f) b * (p.filter {x | f x = b} (hf b)) a =
      if b = f a then p a else 0 := by
    rw [PMF.filter_apply, hden]
    by_cases hb : b = f a
    · subst b
      obtain ⟨x, hx, hxp⟩ := hf (f a)
      have hpos : (p.map f) (f a) ≠ 0 := (PMF.mem_support_map_iff f p (f a)).2 ⟨x, hxp, hx⟩
      simp only [Set.indicator_of_mem (show a ∈ {x | f x = f a} from rfl), ite_true]
      calc
        (p.map f) (f a) * (p a * ((p.map f) (f a))⁻¹) =
            p a * ((p.map f) (f a) * ((p.map f) (f a))⁻¹) := by ac_rfl
        _ = p a := by rw [ENNReal.mul_inv_cancel hpos ((p.map f).apply_ne_top (f a)), mul_one]
    · have hab : a ∉ {x | f x = b} := fun h => hb h.symm
      simp [Set.indicator_of_notMem hab, hb]
  simp_rw [hterm]
  simp

variable [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem pmf_measureReal_eq_expectation (p : PMF α) (A : Set α) :
    (p.toMeasure A).toReal = expectation p (A.indicator (fun _ => (1 : ℝ))) := by
  classical
  rw [PMF.toMeasure_apply_fintype]
  rw [ENNReal.toReal_sum (fun a _ => by
    by_cases ha : a ∈ A <;> simp [Set.indicator, ha, p.apply_ne_top])]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases ha : a ∈ A <;> simp [Set.indicator, ha]

variable {p : PMF α} (f : α → β) (hf : ∀ b, ∃ a ∈ {x | f x = b}, a ∈ p.support) (S : Set α)
    (T : Set β) (c : ℝ)

/-- A joint event is the average of its conditional probabilities, restricted
to the selected observed states. -/
theorem pmf_joint_fiber_sum {f : α → β}
    (hf : ∀ b, ∃ a ∈ {x | f x = b}, a ∈ p.support) (S : Set α) (T : Set β) :
    (p.toMeasure (S ∩ f ⁻¹' T)).toReal =
      ∑ b, ((p.map f) b).toReal *
        (if b ∈ T then ((p.filter {x | f x = b} (hf b)).toMeasure S).toReal else 0) := by
  classical
  rw [pmf_measureReal_eq_expectation]
  conv_lhs => rw [pmf_eq_bind_fiber_filter p f hf, expectation_bind]
  apply Finset.sum_congr rfl
  intro b hb
  congr 1
  change expectation (p.filter {x | f x = b} (hf b))
      ((S ∩ f ⁻¹' T).indicator (fun _ => (1 : ℝ))) = _
  rw [← pmf_measureReal_eq_expectation]
  by_cases hbT : b ∈ T
  · simp only [hbT, ite_true]
    apply congrArg ENNReal.toReal
    apply PMF.toMeasure_apply_eq_of_inter_support_eq _
      (Set.toFinite _).measurableSet (Set.toFinite _).measurableSet
    ext a
    simp_all
  · simp only [hbT, ite_false]
    rw [ENNReal.toReal_eq_zero_iff]
    left
    apply (PMF.toMeasure_apply_eq_zero_iff _ (Set.toFinite _).measurableSet).2
    apply Set.disjoint_left.mpr
    simp_all

theorem pmf_preimage_mass (p : PMF α) (f : α → β) (T : Set β) :
    (p.toMeasure (f ⁻¹' T)).toReal =
      ∑ b, ((p.map f) b).toReal * (if b ∈ T then (1 : ℝ) else 0) := by
  rw [pmf_measureReal_eq_expectation]
  simpa [expectation, Set.indicator] using (expectation_map p f (T.indicator (fun _ => (1 : ℝ)))).symm

theorem pmf_joint_le_of_fiber_le_on_T
    (h : ∀ b ∈ T, ((p.filter {x | f x = b} (hf b)).toMeasure S).toReal ≤ c) :
    (p.toMeasure (S ∩ f ⁻¹' T)).toReal ≤ c * (p.toMeasure (f ⁻¹' T)).toReal := by
  classical
  rw [pmf_joint_fiber_sum hf S T]
  rw [pmf_preimage_mass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  by_cases hbT : b ∈ T
  · simp only [hbT, ite_true, mul_one]
    calc
      _ ≤ ((p.map f) b).toReal * c :=
        mul_le_mul_of_nonneg_left (h b hbT)
          (ENNReal.toReal_nonneg (a := (p.map f) b))
      _ = c * ((p.map f) b).toReal := by ring
  · simp [hbT]

theorem pmf_joint_ge_of_fiber_ge
    (h : ∀ b, c ≤ ((p.filter {x | f x = b} (hf b)).toMeasure S).toReal) :
    c * (p.toMeasure (f ⁻¹' T)).toReal ≤ (p.toMeasure (S ∩ f ⁻¹' T)).toReal := by
  classical
  rw [pmf_joint_fiber_sum hf S T]
  rw [pmf_preimage_mass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  by_cases hbT : b ∈ T
  · simp only [hbT, ite_true, mul_one]
    nlinarith [mul_le_mul_of_nonneg_left (h b) (ENNReal.toReal_nonneg (a := (p.map f) b))]
  · simp [hbT]

end PottsDiscontinuity.FK.FiniteProbability
