module

public import HypoellipticAleksandrov.Measure.ParabolicDyadicFiltration
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Grind



/-!
# Generation by the finite parabolic dyadic filtration

This file proves that the scheduled finite parabolic dyadic filtration
generates the actual measurable space on the half-open reference-cell subtype.
The proof recovers the time and velocity coordinates from countable unions of
addressed half-open cells whose dyadic widths shrink to zero.
-/

@[expose] public section

open Filter MeasureTheory Set

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

private theorem measurableSet_parabolicDyadicRestrictedCell_iSup
    (d n : ℕ) (index : ParabolicDyadicIndex d n) :
    MeasurableSet[⨆ k : ℕ, parabolicDyadicFiltration d k]
      (parabolicDyadicRestrictedCell index) := by
  let sharedTerm_d04d6babf7 := (((d + 2) * n))
  obtain ⟨z, hz⟩ := parabolicDyadicHalfOpenCell_nonempty index
  let z' : ParabolicDyadicReferenceSpace d :=
    ⟨z, parabolicDyadicHalfOpenCell_subset_reference index hz⟩

  have hatom  :=
    ProbabilityTheory.measurableSet_partitionFiltration_memPartitionSet
      (measurableSet_parabolicDyadicGenerator d) sharedTerm_d04d6babf7 z'
  rw [memPartitionSet_parabolicDyadicFiltration_checkpoint_eq_cell index z' ((id hz))] at hatom
  exact (le_iSup (fun k  => parabolicDyadicFiltration d k)
    sharedTerm_d04d6babf7) _ hatom

variable (d : ℕ)

variable (q : ℝ)

private def parabolicDyadicTimeLowerUnion   :
    Set (ParabolicDyadicReferenceSpace d) := by
  classical
  exact ⋃ n : ℕ, ⋃ index : ParabolicDyadicIndex d n,
    if ∀ z ∈ parabolicDyadicRestrictedCell index, z.val.1 < q then
      parabolicDyadicRestrictedCell index
    else ∅

private theorem measurableSet_parabolicDyadicTimeLowerUnion   :
    MeasurableSet[⨆ k : ℕ, parabolicDyadicFiltration d k]
      (parabolicDyadicTimeLowerUnion d q) := by
  classical
  unfold parabolicDyadicTimeLowerUnion
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro index
  let M  :=
    ⨆ k : ℕ, parabolicDyadicFiltration d k
  change @MeasurableSet _ M (if ∀ z ∈ parabolicDyadicRestrictedCell index,
    z.val.1 < q then parabolicDyadicRestrictedCell index else ∅)
  exact @MeasurableSet.ite' _ M _ _ _
    (fun _ => measurableSet_parabolicDyadicRestrictedCell_iSup d n index)
    (fun _ => @MeasurableSet.empty _ M)

private theorem parabolicDyadicTimeLowerUnion_eq_preimage_Iio   :
    parabolicDyadicTimeLowerUnion d q =
      {z : ParabolicDyadicReferenceSpace d | z.val.1 < q} := by
  classical
  ext z
  constructor
  · intro hz
    change z.val.1 < q
    obtain ⟨n, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨index, hz⟩ := Set.mem_iUnion.mp hz
    by_cases hcell : ∀ y ∈ parabolicDyadicRestrictedCell index, y.val.1 < q
    · rw [if_pos hcell] at hz
      exact hcell z hz
    · grind
  · intro hz
    have hgap  := sub_pos.mpr hz

    obtain ⟨n, hn⟩ := eventually_atTop.mp (tendsto_parabolicDyadicTimeWidth_atTop.eventually_lt_const hgap)


    obtain ⟨index, hzindex⟩ := Set.mem_iUnion.mp (show (z : TimeVelocity d) ∈
        ⋃ index : ParabolicDyadicIndex d n, parabolicDyadicHalfOpenCell index by
        rw [iUnion_parabolicDyadicHalfOpenCell_eq_reference]
        exact z.property)


    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    refine Set.mem_iUnion.mpr ⟨index, ?_⟩
    rw [if_pos (by
        intro y hy
        change (y : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index at hy
        rw [mem_parabolicDyadicHalfOpenCell_iff] at hzindex hy

        linarith [hzindex.1.1, hy.1.2, (parabolicDyadicTimeCell_width index), (hn n le_rfl)])]
    exact (show z ∈ parabolicDyadicRestrictedCell index by
        change (z : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index
        exact hzindex)

private theorem measurableSet_time_preimage_Iio_iSup   :
    MeasurableSet[⨆ k : ℕ, parabolicDyadicFiltration d k]
      {z : ParabolicDyadicReferenceSpace d | z.val.1 < q} := by
  rw [← parabolicDyadicTimeLowerUnion_eq_preimage_Iio]
  exact measurableSet_parabolicDyadicTimeLowerUnion d q

variable (coordinate : Fin d) (q : ℝ)

private def parabolicDyadicVelocityLowerUnion
     : Set (ParabolicDyadicReferenceSpace d) := by
  classical
  exact ⋃ n : ℕ, ⋃ index : ParabolicDyadicIndex d n,
    if ∀ z ∈ parabolicDyadicRestrictedCell index, z.val.2 coordinate < q then
      parabolicDyadicRestrictedCell index
    else ∅

private theorem measurableSet_parabolicDyadicVelocityLowerUnion
     :
    MeasurableSet[⨆ k : ℕ, parabolicDyadicFiltration d k]
      (parabolicDyadicVelocityLowerUnion d coordinate q) := by
  classical
  unfold parabolicDyadicVelocityLowerUnion
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro index
  let M  :=
    ⨆ k : ℕ, parabolicDyadicFiltration d k
  change @MeasurableSet _ M (if ∀ z ∈ parabolicDyadicRestrictedCell index,
    z.val.2 coordinate < q then parabolicDyadicRestrictedCell index else ∅)
  exact @MeasurableSet.ite' _ M _ _ _
    (fun _ => measurableSet_parabolicDyadicRestrictedCell_iSup d n index)
    (fun _ => @MeasurableSet.empty _ M)

private theorem parabolicDyadicVelocityLowerUnion_eq_preimage_Iio
     :
    parabolicDyadicVelocityLowerUnion d coordinate q =
      {z : ParabolicDyadicReferenceSpace d | z.val.2 coordinate < q} := by
  classical
  ext z
  constructor
  · intro hz
    change z.val.2 coordinate < q
    obtain ⟨n, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨index, hz⟩ := Set.mem_iUnion.mp hz
    by_cases hcell : ∀ y ∈ parabolicDyadicRestrictedCell index, y.val.2 coordinate < q
    · rw [if_pos hcell] at hz
      exact hcell z hz
    · grind
  · intro hz
    have hgap  := sub_pos.mpr hz

    obtain ⟨n, hn⟩ := eventually_atTop.mp (tendsto_parabolicDyadicVelocityWidth_atTop.eventually_lt_const hgap)


    obtain ⟨index, hzindex⟩ := Set.mem_iUnion.mp (show (z : TimeVelocity d) ∈
        ⋃ index : ParabolicDyadicIndex d n, parabolicDyadicHalfOpenCell index by
        rw [iUnion_parabolicDyadicHalfOpenCell_eq_reference]
        exact z.property)


    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    refine Set.mem_iUnion.mpr ⟨index, ?_⟩
    rw [if_pos (by
        intro y hy
        change (y : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index at hy
        rw [mem_parabolicDyadicHalfOpenCell_iff,
          mem_parabolicDyadicVelocityCell_iff] at hzindex hy

        linarith [hzindex.2 coordinate |>.1, hy.2 coordinate |>.2, (parabolicDyadicVelocityCell_width index coordinate), (hn n le_rfl)])]
    exact (show z ∈ parabolicDyadicRestrictedCell index by
        change (z : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index
        exact hzindex)

private theorem measurableSet_velocity_preimage_Iio_iSup
     :
    MeasurableSet[⨆ k : ℕ, parabolicDyadicFiltration d k]
      {z : ParabolicDyadicReferenceSpace d | z.val.2 coordinate < q} := by
  rw [← parabolicDyadicVelocityLowerUnion_eq_preimage_Iio]
  exact measurableSet_parabolicDyadicVelocityLowerUnion d coordinate q

/-- The scheduled finite parabolic dyadic filtration generates exactly the
ambient subtype measurable space of the half-open reference cell. -/
theorem iSup_parabolicDyadicFiltration_eq_referenceMeasurableSpace  :
    (⨆ k : ℕ, parabolicDyadicFiltration d k) =
      (inferInstance : MeasurableSpace (ParabolicDyadicReferenceSpace d)) := by
  let sharedTerm_4b8d7df0a8 := (⨆ k : ℕ, parabolicDyadicFiltration d k)
  apply le_antisymm
  · apply iSup_le
    intro k
    exact (parabolicDyadicFiltration d).le k
  ·
    have htime  :=
      measurable_of_Iio fun q => (id (measurableSet_time_preimage_Iio_iSup d q))
    have hvelocity  :=
      measurable_pi_iff.mpr fun coordinate =>
        measurable_of_Iio fun q => (id (measurableSet_velocity_preimage_Iio_iSup d coordinate q))

    change MeasurableSpace.comap Subtype.val
      (inferInstance : MeasurableSpace (TimeVelocity d)) ≤ sharedTerm_4b8d7df0a8
    exact (htime.prodMk hvelocity).comap_le

end

end HypoellipticAleksandrov.Parabolic
