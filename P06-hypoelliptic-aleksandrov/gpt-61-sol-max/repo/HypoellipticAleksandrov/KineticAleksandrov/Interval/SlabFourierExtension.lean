module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.Occupation
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.Decay

/-! # Literal zero extension of the interval transition kernel

The extension is zero for starting velocities outside the interval. It is a
measure-theoretic carrier adapter, not a whole-space PDE realization.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

/-- The whole-space carrier used by the adapter is measurable. -/
theorem intervalWholeSpace_measurable : MeasurableSet (wholeSpace 1) := MeasurableSet.univ

variable {a c : ℝ}

/-- Include a literal interval query in the stationary whole-space query carrier. -/
def intervalQueryInclusion  :
    EvolutionQuery (PDE.oneDimensionalAxisBox a c) stationary →
      EvolutionQuery (wholeSpace 1) (fun _ => (0 )) :=
  fun q => ⟨q.1, q.2.1, by rw [movingDomain_wholeSpace]; trivial, q.2.2.2⟩

variable (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))

include hJ in
/-- Inclusion of interval queries is a measurable embedding. -/
theorem intervalQueryInclusion_measurableEmbedding
     :
    MeasurableEmbedding (intervalQueryInclusion (a := a) (c := c)) := by
  let sharedTerm_72b8c21a86 := (EvolutionQuery (wholeSpace 1) (fun _ => (0 )))

  have he := MeasurableEmbedding.subtype_coe (show MeasurableSet {q : RawEvolutionQuery 1 |
      q.1 ≤ q.2.1 ∧ q.2.2.1 ∈ movingDomain (PDE.oneDimensionalAxisBox a c)
        stationary q.1 ∧ q.2.2.2 ∈ (univ : PDE.VelocityRegion 1)} by
      simp only [movingDomain_stationary, mem_univ, and_true]
      exact (measurableSet_le
        (show Measurable (fun q : RawEvolutionQuery 1 => q.1) from by fun_prop)
        (show Measurable (fun q : RawEvolutionQuery 1 => q.2.1) from by fun_prop)).inter
        (hJ.preimage (show Measurable (fun q : RawEvolutionQuery 1 => q.2.2.1) from
          by fun_prop)))
  refine ⟨?_, ?_, ?_⟩
  · intro p q hpq
    apply Subtype.ext
    exact congrArg (fun r : sharedTerm_72b8c21a86 => r.1) hpq
  · apply Measurable.subtype_mk
    exact measurable_subtype_coe
  · intro A hA

    have heq : intervalQueryInclusion '' A =
        (Subtype.val : sharedTerm_72b8c21a86 →
          RawEvolutionQuery 1) ⁻¹' (Subtype.val '' A) := by
      ext q
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p, hp, rfl⟩
      · rintro ⟨p, hp, he⟩
        exact ⟨p, hp, Subtype.ext he⟩
    rw [heq]
    exact (he.measurableSet_image.2 hA).preimage measurable_subtype_coe

variable (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)

/-- Zero-extended master kernel, with the same ambient terminal state measure. -/
def intervalExtensionMaster

     :
    ProbabilityTheory.Kernel
      (EvolutionQuery (wholeSpace 1) (fun _ => (0 ))) (EvolutionAmbientState 1) where
  toFun := Function.extend intervalQueryInclusion K.master (fun _ => 0)
  measurable' := (intervalQueryInclusion_measurableEmbedding hJ).measurable_extend
    K.master.measurable measurable_const

/-- The zero extension agrees exactly with the interval master at interior queries. -/
theorem intervalExtensionMaster_inside


    (q : EvolutionQuery (PDE.oneDimensionalAxisBox a c) stationary) :
    intervalExtensionMaster hJ K (intervalQueryInclusion q) = K.master q := (id
  (Function.Injective.extend_apply (intervalQueryInclusion_measurableEmbedding hJ).injective (⇑K.master) (fun x => 0) q))

/-- The adapted kernel has whole-space carriers and zero transitions outside the interval. -/
def intervalExtension

     :
    MovingFiberKernel (wholeSpace 1) (fun _ => (0 )) where
  master := intervalExtensionMaster hJ K
  terminal_support := by
    intro q
    simp only [evolutionStateSet, movingDomain_wholeSpace, univ_prod_univ,
      Measure.restrict_univ]
  mass_le_one := by
    intro q
    by_cases hq : ∃ p : EvolutionQuery (PDE.oneDimensionalAxisBox a c) stationary,
      intervalQueryInclusion p = q
    · obtain ⟨p, rfl⟩ := hq
      rw [intervalExtensionMaster_inside]
      exact K.mass_le_one p
    · change (Function.extend intervalQueryInclusion K.master (fun _ => 0) q) univ ≤ 1
      rw [Function.extend_apply' _ _ _ hq]
      exact zero_le

end HypoellipticAleksandrov.KineticAleksandrov.Interval
