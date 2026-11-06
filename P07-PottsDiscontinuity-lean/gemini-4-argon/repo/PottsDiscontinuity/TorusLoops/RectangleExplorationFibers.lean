module

public import Mathlib
public import PottsDiscontinuity.FK.Expectation

/-!
# Joint finite-FK estimates over frozen edge states

A conditional upper comparison can be integrated over any selected set of
frozen exterior states. This is the weighted form needed when the explored
cluster region is fixed before the next root is tested.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open MeasureTheory
open PottsDiscontinuity.FK
open PottsDiscontinuity.FK.FiniteProbability

noncomputable section

section FinitePMF

open scoped Classical

variable {α β : Type*} [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]

private theorem pmf_measureReal_eq_expectation (p : PMF α) (A : Set α) :
    (p.toMeasure A).toReal = expectation p (A.indicator (fun _ => (1 : ℝ))) := by
  classical
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum (fun a _ => by
    by_cases ha : a ∈ A <;> simp [Set.indicator, ha, p.apply_ne_top])]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : a ∈ A <;> simp [Set.indicator, ha]

omit [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
private theorem pmf_eq_bind_fiber_filter (p : PMF α) (f : α → β)
    (hf : ∀ b, ∃ a ∈ {x | f x = b}, a ∈ p.support) :
    p = (p.map f).bind (fun b => p.filter {x | f x = b} (hf b)) := by
  classical
  have hden (b : β) : (∑' x, ({x | f x = b} : Set α).indicator p x) = (p.map f) b := by
    rw [PMF.map_apply]; exact tsum_congr fun x => by simp [Set.indicator, eq_comm]
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
      rw [mul_left_comm, ENNReal.mul_inv_cancel hpos ((p.map f).apply_ne_top (f a)), mul_one]
    · have hab : a ∉ {x | f x = b} := fun h => hb h.symm
      simp [Set.indicator_of_notMem hab, hb]
  simp_rw [hterm]; simp

omit [MeasurableSpace β] [MeasurableSingletonClass β] in
private theorem pmf_joint_fiber_sum (p : PMF α) (f : α → β)
    (hf : ∀ b, ∃ a ∈ {x | f x = b}, a ∈ p.support) (S : Set α) (T : Set β) :
    (p.toMeasure (S ∩ f ⁻¹' T)).toReal =
      ∑ b, ((p.map f) b).toReal *
        (if b ∈ T then ((p.filter {x | f x = b} (hf b)).toMeasure S).toReal else 0) := by
  classical
  rw [pmf_measureReal_eq_expectation]
  conv_lhs => rw [pmf_eq_bind_fiber_filter p f hf, expectation_bind]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  change expectation (p.filter {x | f x = b} (hf b))
      ((S ∩ f ⁻¹' T).indicator (fun _ => (1 : ℝ))) = _
  rw [← pmf_measureReal_eq_expectation]
  by_cases hbT : b ∈ T
  · simp only [hbT, ite_true]
    refine congrArg ENNReal.toReal <| PMF.toMeasure_apply_eq_of_inter_support_eq _
      (Set.toFinite _).measurableSet (Set.toFinite _).measurableSet ?_
    ext a
    exact ⟨fun ⟨⟨ha, _⟩, hp⟩ => ⟨ha, hp⟩,
      fun ⟨ha, hp⟩ => ⟨⟨ha, show f a ∈ T from ((PMF.mem_support_filter_iff _).mp hp).1.symm ▸ hbT⟩, hp⟩⟩
  · simp only [hbT, ite_false, ENNReal.toReal_eq_zero_iff]
    left
    refine (PMF.toMeasure_apply_eq_zero_iff _ (Set.toFinite _).measurableSet).2
      (Set.disjoint_left.mpr fun a hp ha => hbT (((PMF.mem_support_filter_iff _).mp hp).1 ▸ ha.2))

omit [MeasurableSpace β] [MeasurableSingletonClass β] in
private theorem pmf_preimage_toReal_eq_sum (p : PMF α) (f : α → β) (T : Set β) :
    (p.toMeasure (f ⁻¹' T)).toReal =
      ∑ b, ((p.map f) b).toReal * (if b ∈ T then (1 : ℝ) else 0) := by
  classical
  rw [pmf_measureReal_eq_expectation]
  simpa [expectation, Set.indicator] using (expectation_map p f (T.indicator fun _ => (1 : ℝ))).symm

omit [MeasurableSpace β] [MeasurableSingletonClass β] in
/-- A joint event is bounded by a uniform conditional estimate on every selected fiber.
Only fibers whose index belongs to `T` need satisfy the conditional bound. -/
theorem pmf_joint_le_of_fiber_le_on_T (p : PMF α) (f : α → β)
    (hf : ∀ b, ∃ a ∈ {x | f x = b}, a ∈ p.support)
    (S : Set α) (T : Set β) (c : ℝ)
    (h : ∀ b ∈ T, ((p.filter {x | f x = b} (hf b)).toMeasure S).toReal ≤ c) :
    (p.toMeasure (S ∩ f ⁻¹' T)).toReal ≤ c * (p.toMeasure (f ⁻¹' T)).toReal := by
  classical
  rw [pmf_joint_fiber_sum p f hf S T, pmf_preimage_toReal_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  by_cases hbT : b ∈ T
  · simp only [hbT, ite_true, mul_one]
    exact (mul_le_mul_of_nonneg_left (h b hbT) ENNReal.toReal_nonneg).trans_eq (mul_comm _ _)
  · simp [hbT]

omit [MeasurableSpace β] [MeasurableSingletonClass β] in
/-- A joint event estimate can be summed directly from unnormalized fiber
estimates. -/
theorem pmf_joint_le_of_joint_fiber_le_on_T (p : PMF α) (f : α → β)
    (hf : ∀ b, ∃ a ∈ {x | f x = b}, a ∈ p.support)
    (S : Set α) (T : Set β) (c : ℝ)
    (h : ∀ b ∈ T,
      (p.toMeasure (S ∩ {x | f x = b})).toReal ≤
        c * (p.toMeasure {x | f x = b}).toReal) :
    (p.toMeasure (S ∩ f ⁻¹' T)).toReal ≤
      c * (p.toMeasure (f ⁻¹' T)).toReal := by
  classical
  rw [pmf_joint_fiber_sum p f hf S T, pmf_preimage_toReal_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  by_cases hbT : b ∈ T
  · simp only [hbT, ite_true, mul_one]
    have hsingle : (p.toMeasure (S ∩ {x | f x = b})).toReal =
        ((p.map f) b).toReal * ((p.filter {x | f x = b} (hf b)).toMeasure S).toReal := by
      simpa [show (S ∩ {x | f x = b}) = S ∩ f ⁻¹' ({b} : Set β) by ext; simp] using
        pmf_joint_fiber_sum p f hf S {b}
    have hmassSingle : (p.toMeasure {x | f x = b}).toReal = ((p.map f) b).toReal := by
      rw [PMF.toMeasure_apply_fintype, PMF.map_apply, tsum_fintype]
      congr 1; simp [Set.indicator, eq_comm]
    rw [← hsingle, ← hmassSingle]
    exact h b hbT
  · simp [hbT]

end FinitePMF


end

end PottsDiscontinuity.TorusLoops
