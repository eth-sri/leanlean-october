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
  have hz' : z' ∈ parabolicDyadicRestrictedCell index := by
    change z ∈ parabolicDyadicHalfOpenCell index
    exact hz
  have hatom :=
    ProbabilityTheory.measurableSet_partitionFiltration_memPartitionSet
      (measurableSet_parabolicDyadicGenerator d) ((d + 2) * n) z'
  rw [memPartitionSet_parabolicDyadicFiltration_checkpoint_eq_cell index z' hz'] at hatom
  exact (le_iSup (fun k : ℕ => parabolicDyadicFiltration d k)
    ((d + 2) * n)) _ hatom

private noncomputable def parabolicDyadicTimeLowerUnion (d : ℕ) (q : ℝ) :
    Set (ParabolicDyadicReferenceSpace d) := by
  classical
  exact ⋃ n : ℕ, ⋃ index : ParabolicDyadicIndex d n,
    if ∀ z ∈ parabolicDyadicRestrictedCell index, z.val.1 < q then
      parabolicDyadicRestrictedCell index
    else ∅

private noncomputable def parabolicDyadicVelocityLowerUnion (d )
    (coordinate : Fin d) (q : ℝ) : Set (ParabolicDyadicReferenceSpace d) := by
  classical
  exact ⋃ n : ℕ, ⋃ index : ParabolicDyadicIndex d n,
    if ∀ z ∈ parabolicDyadicRestrictedCell index, z.val.2 coordinate < q then
      parabolicDyadicRestrictedCell index
    else ∅

theorem iSup_parabolicDyadicFiltration_eq_referenceMeasurableSpace (d : ℕ) :
    (⨆ k : ℕ, parabolicDyadicFiltration d k) =
      (inferInstance : MeasurableSpace (ParabolicDyadicReferenceSpace d)) := by
  apply le_antisymm
  · apply iSup_le
    intro k
    exact (parabolicDyadicFiltration d).le k
  · let M : MeasurableSpace (ParabolicDyadicReferenceSpace d) :=
      ⨆ k : ℕ, parabolicDyadicFiltration d k
    have htime :=
      measurable_of_Iio fun q => by
        change MeasurableSet[⨆ k : ℕ, parabolicDyadicFiltration d k]
          {z : ParabolicDyadicReferenceSpace d | z.val.1 < q}
        have _h_inl_10 (d : ℕ) (q) : parabolicDyadicTimeLowerUnion d q = {z : ParabolicDyadicReferenceSpace d | z.val.1 < q} := by
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
            · rw [if_neg hcell] at hz
              exact False.elim (Set.notMem_empty z hz)
          · intro hz
            have hgap : 0 < q - z.val.1 := sub_pos.mpr hz
            have hwidth_eventually :=
              tendsto_parabolicDyadicTimeWidth_atTop.eventually_lt_const hgap
            obtain ⟨n, hn⟩ := eventually_atTop.mp hwidth_eventually
            have hwidth := hn n le_rfl
            have hzcover : (z : TimeVelocity d) ∈
                ⋃ index : ParabolicDyadicIndex d n, parabolicDyadicHalfOpenCell index := by
              rw [iUnion_parabolicDyadicHalfOpenCell_eq_reference]
              exact z.property
            obtain ⟨index, hzindex⟩ := Set.mem_iUnion.mp hzcover
            have hzindex' : z ∈ parabolicDyadicRestrictedCell index := by
              change (z : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index
              exact hzindex
            have hcell : ∀ y ∈ parabolicDyadicRestrictedCell index, y.val.1 < q := by
              intro y hy
              change (y : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index at hy
              rw [mem_parabolicDyadicHalfOpenCell_iff] at hzindex hy
              linarith [hzindex.1.1, hy.1.2, (parabolicDyadicTimeCell_width index), hwidth]
            refine Set.mem_iUnion.mpr ⟨n, ?_⟩
            refine Set.mem_iUnion.mpr ⟨index, ?_⟩
            rw [if_pos hcell]
            exact hzindex'
        rw [← _h_inl_10]
        classical
        unfold parabolicDyadicTimeLowerUnion
        apply MeasurableSet.iUnion
        intro n
        apply MeasurableSet.iUnion
        intro index
        let M :=
          ⨆ k : ℕ, parabolicDyadicFiltration d k
        change @MeasurableSet _ M (if ∀ z ∈ parabolicDyadicRestrictedCell index,
          z.val.1 < q then parabolicDyadicRestrictedCell index else ∅)
        exact @MeasurableSet.ite' _ M _ _ _
          (fun _ => measurableSet_parabolicDyadicRestrictedCell_iSup d n index)
          (fun _ => @MeasurableSet.empty _ M)
    have hvelocity : Measurable[M] (fun z : ParabolicDyadicReferenceSpace d => z.val.2) :=
      measurable_pi_iff.mpr fun coordinate =>
        measurable_of_Iio fun q => by
          change MeasurableSet[⨆ k : ℕ, parabolicDyadicFiltration d k]
            {z : ParabolicDyadicReferenceSpace d | z.val.2 coordinate < q}
          have _h_inl_12 (d : ℕ) (coordinate : Fin d) (q) : parabolicDyadicVelocityLowerUnion d coordinate q = {z : ParabolicDyadicReferenceSpace d | z.val.2 coordinate < q} := by
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
              · rw [if_neg hcell] at hz
                exact False.elim (Set.notMem_empty z hz)
            · intro hz
              have hgap : 0 < q - z.val.2 coordinate := sub_pos.mpr hz
              have hwidth_eventually :=
                tendsto_parabolicDyadicVelocityWidth_atTop.eventually_lt_const hgap
              obtain ⟨n, hn⟩ := eventually_atTop.mp hwidth_eventually
              have hwidth := hn n le_rfl
              have hzcover : (z : TimeVelocity d) ∈
                  ⋃ index : ParabolicDyadicIndex d n, parabolicDyadicHalfOpenCell index := by
                rw [iUnion_parabolicDyadicHalfOpenCell_eq_reference]
                exact z.property
              obtain ⟨index, hzindex⟩ := Set.mem_iUnion.mp hzcover
              have hzindex' : z ∈ parabolicDyadicRestrictedCell index := by
                change (z : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index
                exact hzindex
              have hcell : ∀ y ∈ parabolicDyadicRestrictedCell index,
                  y.val.2 coordinate < q := by
                intro y hy
                change (y : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index at hy
                rw [mem_parabolicDyadicHalfOpenCell_iff,
                  mem_parabolicDyadicVelocityCell_iff] at hzindex hy
                linarith [hzindex.2 coordinate |>.1, hy.2 coordinate |>.2, (parabolicDyadicVelocityCell_width index coordinate), hwidth]
              refine Set.mem_iUnion.mpr ⟨n, ?_⟩
              refine Set.mem_iUnion.mpr ⟨index, ?_⟩
              rw [if_pos hcell]
              exact hzindex'
          rw [← _h_inl_12]
          classical
          unfold parabolicDyadicVelocityLowerUnion
          apply MeasurableSet.iUnion
          intro n
          apply MeasurableSet.iUnion
          intro index
          let M :=
            ⨆ k : ℕ, parabolicDyadicFiltration d k
          change @MeasurableSet _ M (if ∀ z ∈ parabolicDyadicRestrictedCell index,
            z.val.2 coordinate < q then parabolicDyadicRestrictedCell index else ∅)
          exact @MeasurableSet.ite' _ M _ _ _
            (fun _ => measurableSet_parabolicDyadicRestrictedCell_iSup d n index)
            (fun _ => @MeasurableSet.empty _ M)
    have hcoe := htime.prodMk hvelocity
    change MeasurableSpace.comap Subtype.val
      (inferInstance : MeasurableSpace (TimeVelocity d)) ≤ M
    exact hcoe.comap_le

end

end HypoellipticAleksandrov.Parabolic
