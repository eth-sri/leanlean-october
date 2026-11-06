module

public import HypoellipticAleksandrov.Measure.ParabolicDyadicFiltration
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Tactic.Linarith

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
  obtain ⟨z, hz⟩ := parabolicDyadicHalfOpenCell_nonempty index
  let z' : ParabolicDyadicReferenceSpace d :=
    ⟨z, parabolicDyadicHalfOpenCell_subset_reference index hz⟩
  have hz' : z' ∈ parabolicDyadicRestrictedCell index := hz
  have hatom : MeasurableSet[parabolicDyadicFiltration d _]
      _ :=
    ProbabilityTheory.measurableSet_partitionFiltration_memPartitionSet
      _ ((d + 2) * n) z'
  rw [memPartitionSet_parabolicDyadicFiltration_checkpoint_eq_cell index z' hz'] at hatom
  exact (le_iSup (fun k : ℕ => parabolicDyadicFiltration d k)
    _) _ hatom

private noncomputable def parabolicDyadicTimeLowerUnion (d : ℕ) (q : ℝ) :
    Set (ParabolicDyadicReferenceSpace d) := by
  classical
  exact ⋃ n : ℕ, ⋃ index : ParabolicDyadicIndex d n,
    if ∀ z ∈ parabolicDyadicRestrictedCell index, z.val.1 < q then
      parabolicDyadicRestrictedCell index
    else ∅

variable (d : ℕ) (q : ℝ)

private theorem measurableSet_parabolicDyadicTimeLowerUnion  :
    MeasurableSet[⨆ k : ℕ, parabolicDyadicFiltration d k]
      (parabolicDyadicTimeLowerUnion d q) := by
  classical
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro index
  let M  :=
    ⨆ k : ℕ, parabolicDyadicFiltration d k
  exact @MeasurableSet.ite' _ M _ _ _
    (fun _ => measurableSet_parabolicDyadicRestrictedCell_iSup d n index)
    (fun _ => @MeasurableSet.empty _ M)

private theorem parabolicDyadicTimeLowerUnion_eq_preimage_Iio  :
    parabolicDyadicTimeLowerUnion d q =
      {z : ParabolicDyadicReferenceSpace d | z.val.1 < q} := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨n, hz⟩ := Set.mem_iUnion.mp hz
    aesop
  · intro hz
    have hgap : 0 < q - z.val.1 := sub_pos.mpr hz
    have hwidth_eventually : ∀ᶠ n in atTop, parabolicDyadicTimeWidth n < q - z.val.1 :=
      tendsto_parabolicDyadicTimeWidth_atTop.eventually_lt_const hgap
    obtain ⟨n, hn⟩ := eventually_atTop.mp hwidth_eventually
    have hwidth : parabolicDyadicTimeWidth n < q - z.val.1 := hn n le_rfl
    have hzcover : (z : TimeVelocity d) ∈
        ⋃ index : ParabolicDyadicIndex d n, parabolicDyadicHalfOpenCell index := by
      rw [iUnion_parabolicDyadicHalfOpenCell_eq_reference]
      simp
    obtain ⟨index, hzindex⟩ := Set.mem_iUnion.mp hzcover
    have hzindex' : z ∈ parabolicDyadicRestrictedCell index := hzindex
    have hcell : ∀ y ∈ parabolicDyadicRestrictedCell index, y.val.1 < q := by
      intro y hy
      have hcell_width := parabolicDyadicTimeCell_width index
      linarith [hzindex.1.1, hy.1.2, hcell_width, hwidth]
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    aesop

private theorem measurableSet_time_preimage_Iio_iSup  :
    MeasurableSet[⨆ k : ℕ, parabolicDyadicFiltration d k]
      {z : ParabolicDyadicReferenceSpace d | z.val.1 < q} := by
  rw [← parabolicDyadicTimeLowerUnion_eq_preimage_Iio]
  exact measurableSet_parabolicDyadicTimeLowerUnion d q

private noncomputable def parabolicDyadicVelocityLowerUnion (d : ℕ)
    (coordinate : Fin d) (q : ℝ) : Set (ParabolicDyadicReferenceSpace d) := by
  classical
  exact ⋃ n : ℕ, ⋃ index : ParabolicDyadicIndex d n,
    if ∀ z ∈ parabolicDyadicRestrictedCell index, z.val.2 coordinate < q then
      parabolicDyadicRestrictedCell index
    else ∅

variable (d : ℕ) (coordinate : Fin d) (q : ℝ)

private theorem measurableSet_parabolicDyadicVelocityLowerUnion  :
    MeasurableSet[⨆ k : ℕ, parabolicDyadicFiltration d k]
      (parabolicDyadicVelocityLowerUnion d coordinate q) := by
  classical
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro index
  let M  :=
    ⨆ k : ℕ, parabolicDyadicFiltration d k
  exact @MeasurableSet.ite' _ M _ _ _
    (fun _ => measurableSet_parabolicDyadicRestrictedCell_iSup d n index)
    (fun _ => @MeasurableSet.empty _ M)

private theorem parabolicDyadicVelocityLowerUnion_eq_preimage_Iio  :
    parabolicDyadicVelocityLowerUnion d coordinate q =
      {z : ParabolicDyadicReferenceSpace d | z.val.2 coordinate < q} := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨n, hz⟩ := Set.mem_iUnion.mp hz
    aesop
  · intro hz
    have hgap : 0 < q - z.val.2 coordinate := sub_pos.mpr hz
    have hwidth_eventually : ∀ᶠ n in atTop,
        parabolicDyadicVelocityWidth n < q - z.val.2 coordinate :=
      tendsto_parabolicDyadicVelocityWidth_atTop.eventually_lt_const hgap
    obtain ⟨n, hn⟩ := eventually_atTop.mp hwidth_eventually
    have hwidth : parabolicDyadicVelocityWidth n < q - z.val.2 coordinate := hn n le_rfl
    have hzcover : (z : TimeVelocity d) ∈
        ⋃ index : ParabolicDyadicIndex d n, parabolicDyadicHalfOpenCell index := by
      rw [iUnion_parabolicDyadicHalfOpenCell_eq_reference]
      simp
    obtain ⟨index, hzindex⟩ := Set.mem_iUnion.mp hzcover
    have hzindex' : z ∈ parabolicDyadicRestrictedCell index := hzindex
    have hcell : ∀ y ∈ parabolicDyadicRestrictedCell index,
        y.val.2 coordinate < q := by
      intro y hy
      change (y : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index at hy
      rw [mem_parabolicDyadicHalfOpenCell_iff,
        mem_parabolicDyadicVelocityCell_iff] at hzindex hy
      have hcell_width := parabolicDyadicVelocityCell_width index coordinate
      grind
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    aesop

private theorem measurableSet_velocity_preimage_Iio_iSup  :
    MeasurableSet[⨆ k : ℕ, parabolicDyadicFiltration d k]
      {z : ParabolicDyadicReferenceSpace d | z.val.2 coordinate < q} := by
  rw [← parabolicDyadicVelocityLowerUnion_eq_preimage_Iio]
  exact measurableSet_parabolicDyadicVelocityLowerUnion d coordinate q

/-- The scheduled finite parabolic dyadic filtration generates exactly the
ambient subtype measurable space of the half-open reference cell. -/
theorem iSup_parabolicDyadicFiltration_eq_referenceMeasurableSpace  :
    (⨆ k : ℕ, parabolicDyadicFiltration d k) =
      (inferInstance : MeasurableSpace (ParabolicDyadicReferenceSpace d)) := by
  apply le_antisymm
  · apply iSup_le
    intro k
    exact (parabolicDyadicFiltration d).le k
  · let M : MeasurableSpace (ParabolicDyadicReferenceSpace d) :=
      ⨆ k : ℕ, parabolicDyadicFiltration d k
    have htime : Measurable[M] (fun z : ParabolicDyadicReferenceSpace d => z.val.1) :=
      measurable_of_Iio fun q => by
        exact measurableSet_time_preimage_Iio_iSup d q
    have hvelocity : Measurable[M] (fun z : ParabolicDyadicReferenceSpace d => z.val.2) :=
      measurable_pi_iff.mpr fun coordinate =>
        measurable_of_Iio fun q => by
          exact measurableSet_velocity_preimage_Iio_iSup d coordinate q
    have hcoe : Measurable[M] (fun z : ParabolicDyadicReferenceSpace d =>
        ((z.val.1, z.val.2) : TimeVelocity d)) := htime.prodMk hvelocity
    exact hcoe.comap_le

end

end HypoellipticAleksandrov.Parabolic
