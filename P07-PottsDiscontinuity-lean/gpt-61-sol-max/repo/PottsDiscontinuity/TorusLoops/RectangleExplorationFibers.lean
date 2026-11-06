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



open PottsDiscontinuity.FK.FiniteProbability

noncomputable section

section

open scoped Classical

variable {α β : Type*} [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]

private theorem pmf_measureReal_eq_expectation (p : PMF α) (A : Set α) :
    (p.toMeasure A).toReal = expectation p (A.indicator  fun _ => (1 : ℝ) ) := by
  
  rw [PMF.toMeasure_apply_fintype]
  rw [ENNReal.toReal_sum  fun a _ => by
    by_cases ha : a ∈ A <;> simp [ha, p.apply_ne_top] ]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases ha : a ∈ A <;> simp [ha]

omit [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
private theorem pmf_eq_bind_fiber_filter (p : PMF α) (f : α → β)
    (hf : ∀ b, ∃ a ∈ {x | f x = b}, a ∈ p.support) :
    p = (p.map f).bind  fun b => p.filter {x | f x = b} (hf b)  := by
  classical
  have hden (b : β) :  ∑' x, ({x | f x = b} ).indicator p x  = (p.map f) b := by
    rw [PMF.map_apply]
    apply tsum_congr
    intro x
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
      
      simp only [Set.indicator_of_mem (show a ∈ {x | f x = f a} from rfl)]
      calc
        (p.map f) (f a) * (p a * ((p.map f) (f a))⁻¹) =
            p a * ((p.map f) (f a) * ((p.map f) (f a))⁻¹) := by ac_rfl
        _ = p a := by rw [ENNReal.mul_inv_cancel ((PMF.mem_support_map_iff f p (f a)).2 ⟨x, hxp, hx⟩) ((p.map f).apply_ne_top (f a)), mul_one]
    · aesop
  simp_rw [hterm]
  simp

omit [MeasurableSpace β] [MeasurableSingletonClass β] in
private theorem pmf_joint_fiber_sum (p : PMF α) (f : α → β)
    (hf : ∀ b, ∃ a ∈ {x | f x = b}, a ∈ p.support) (S : Set α) (T : Set β) :
    (p.toMeasure (S ∩ f ⁻¹' T)).toReal =
      ∑ b, ((p.map f) b).toReal *
         if b ∈ T then ((p.filter {x | f x = b} (hf b)).toMeasure S).toReal else 0  := by
  classical
  rw [pmf_measureReal_eq_expectation]
  conv_lhs => rw [pmf_eq_bind_fiber_filter p f hf, expectation_bind]
  unfold expectation
  apply Finset.sum_congr rfl
  intro b hb
  congr 1
  change expectation (p.filter {x | f x = b} (hf b))
      ((S ∩ f ⁻¹' T).indicator  fun _ => 1 ) = _
  rw [← pmf_measureReal_eq_expectation]
  by_cases hbT : b ∈ T
  · simp only [hbT]
    apply congrArg ENNReal.toReal
    apply PMF.toMeasure_apply_eq_of_inter_support_eq _
      (Set.toFinite _).measurableSet (Set.toFinite _).measurableSet
    all_goals aesop
  · simp only [hbT, ite_false]
    rw [ENNReal.toReal_eq_zero_iff]
    left
    apply (PMF.toMeasure_apply_eq_zero_iff _ (Set.toFinite _).measurableSet).2
    apply Set.disjoint_left.mpr
    all_goals simp_all

omit [MeasurableSpace β] [MeasurableSingletonClass β] in
/-- A joint event is bounded by a uniform conditional estimate on every selected fiber.
Only fibers whose index belongs to `T` need satisfy the conditional bound. -/
theorem pmf_joint_le_of_fiber_le_on_T (p : PMF α) (f : α → β)
    (hf : ∀ b, ∃ a ∈ {x | f x = b}, a ∈ p.support)
    (S : Set α) (T : Set β) (c : ℝ)
    (h : ∀ b ∈ T, ((p.filter {x | f x = b} (hf b)).toMeasure S).toReal ≤ c) :
    (p.toMeasure (S ∩ f ⁻¹' T)).toReal ≤ c * (p.toMeasure (f ⁻¹' T)).toReal := by
  classical
  rw [pmf_joint_fiber_sum p f hf S T]
  have hmass : (p.toMeasure (f ⁻¹' T)).toReal =
      ∑ b, ((p.map f) b).toReal *  if b ∈ T then (1 : ℝ) else 0  := by
    rw [pmf_measureReal_eq_expectation]
    
    simpa [expectation, Set.indicator] using (expectation_map p f (T.indicator  fun _ => 1 )).symm
  rw [hmass, Finset.mul_sum]
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

omit [MeasurableSpace β] [MeasurableSingletonClass β] in
private theorem pmf_single_fiber_joint_sum (p : PMF α) (f : α → β)
    (hf : ∀ b, ∃ a ∈ {x | f x = b}, a ∈ p.support) (S : Set α) (b : β) :
    (p.toMeasure (S ∩ {x | f x = b})).toReal =
      ((p.map f) b).toReal *
        ((p.filter {x | f x = b} (hf b)).toMeasure S).toReal := by
  have hset :  S ∩ {x | f x = b}  = S ∩ f ⁻¹'  {b}  := by
    ext x
    simp
  rw [hset, pmf_joint_fiber_sum p f hf S {b}]
  simp

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
  rw [pmf_joint_fiber_sum p f hf S T]
  have hmass : (p.toMeasure (f ⁻¹' T)).toReal =
      ∑ b, ((p.map f) b).toReal *  if b ∈ T then (1 : ℝ) else 0  := by
    rw [pmf_measureReal_eq_expectation]
    
    simpa [expectation, Set.indicator] using (expectation_map p f (T.indicator  fun _ => 1 )).symm
  rw [hmass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  by_cases hbT : b ∈ T
  · simp only [hbT, ite_true, mul_one]
    
    have hmassSingle : (p.toMeasure {x | f x = b}).toReal =
        ((p.map f) b).toReal := by
      rw [PMF.toMeasure_apply_fintype]
      rw [PMF.map_apply]
      congr 1
      simp [Set.indicator, eq_comm]
    calc
      ((p.map f) b).toReal *
          ((p.filter {x | f x = b} (hf b)).toMeasure S).toReal =
        (p.toMeasure (S ∩ {x | f x = b})).toReal := (pmf_single_fiber_joint_sum p f hf S b).symm
      _ ≤ c * (p.toMeasure {x | f x = b}).toReal := h b hbT
      _ = c * ((p.map f) b).toReal := by rw [hmassSingle]
  · simp [hbT]

end


end

end PottsDiscontinuity.TorusLoops
