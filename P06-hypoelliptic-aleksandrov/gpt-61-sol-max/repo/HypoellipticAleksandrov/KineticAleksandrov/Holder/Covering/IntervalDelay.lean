module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.IntervalDelayFinite
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-! # Sharp delayed-interval union inequality

The finite estimate uses bounded open components. The countable estimate follows by
continuity from below over finite subfamilies, with no uniform bound on the intervals.
-/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

variable {ι : Type*}

variable (a h : ι → ℝ)

/-- A bounded forward union controls the preceding union by the sharp delay factor. -/
theorem interval_delay_of_bounded_union   (I : Set ι)
    {m : ℝ} (hm : 0 < m) (hh : ∀ i ∈ I, 0 < h i)
    (hbelow : BddBelow (⋃ i ∈ I, Ioo (a i) (a i + m*h i)))
    (habove : BddAbove (⋃ i ∈ I, Ioo (a i) (a i + m*h i))) :
    volume (⋃ i ∈ I, Ioo (a i-h i) (a i)) ≤
      ENNReal.ofReal ((m+1)/m) * volume (⋃ i ∈ I, Ioo (a i) (a i+m*h i)) := by
  let sharedTerm_d29ca50734 := (ENNReal.ofReal ((m + 1) / m))


  obtain ⟨C, hcount, hdisj, hcomp, hcover, hcontains⟩ :=
    bounded_open_interval_components (isOpen_biUnion fun _ _ => isOpen_Ioo) hbelow habove
  let ext  := fun s => Ioo (sInf s-(sSup s-sInf s)/m) (sSup s)



  calc
    volume (((⋃ i ∈ I, Ioo (a i - h i) (a i)))) ≤ volume (⋃ s ∈ C, ext s) :=
      measure_mono (by
          intro x hx
          obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx

          obtain ⟨s, hs, hIs⟩ := hcontains (a i) (a i+m*h i) (by nlinarith only [hm, hh i hi])
            (subset_iUnion₂_of_subset i hi Subset.rfl)
          have hI := backwardInterval_subset_component_extension (hh i hi) hm
            (hIs.trans (subset_of_eq (hcomp s hs).2))
          exact mem_iUnion₂.mpr ⟨s, hs, hI hxi⟩)
    _ ≤ ∑' s : C, volume (ext s) := measure_biUnion_le volume hcount ext
    _ = ∑' s : C, sharedTerm_d29ca50734 * volume (s : Set ℝ) :=
      tsum_congr fun s => (show ∀ s ∈ C, volume (ext s) = sharedTerm_d29ca50734 * volume s by
          intro s hs
          change volume (Ioo (sInf s-(sSup s-sInf s)/m) (sSup s)) = _
          rw [volume_component_extension hm, ← (hcomp s hs).2]) s s.2
    _ = sharedTerm_d29ca50734 * ∑' s : C, volume (s : Set ℝ) :=
      ENNReal.tsum_mul_left
    _ = sharedTerm_d29ca50734 * volume (⋃ i ∈ I, Ioo (a i) (a i+m*h i)) := by
      have hsum := measure_biUnion (μ := volume) hcount hdisj (by
          intro s hs
          rw [(hcomp s hs).2]
          exact measurableSet_Ioo)
      simp only [id_eq] at hsum
      rw [hcover] at hsum
      rw [← hsum]

/-- The sharp delayed-union inequality for a finite interval family. -/
theorem interval_delay_finset   (s : Finset ι)
    {m : ℝ} (hm : 0 < m) (hh : ∀ i ∈ s, 0 < h i) :
    volume (⋃ i ∈ s, Ioo (a i-h i) (a i)) ≤
      ENNReal.ofReal ((m+1)/m) * volume (⋃ i ∈ s, Ioo (a i) (a i+m*h i)) := by
  let sharedTerm_88da0a54dc := ((fun i => a i + m * h i))
  apply interval_delay_of_bounded_union a h (s : Set ι) hm hh
  · obtain ⟨l, hl⟩ := (s.finite_toSet.image a).bddBelow
    refine ⟨l, ?_⟩
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact (hl (mem_image_of_mem a hi)).trans hxi.1.le
  · obtain ⟨b, hb⟩ := (s.finite_toSet.image sharedTerm_88da0a54dc).bddAbove
    refine ⟨b, ?_⟩
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact hxi.2.le.trans (hb (mem_image_of_mem sharedTerm_88da0a54dc hi))

/-- Countable delayed interval families satisfy the same sharp factor. -/
theorem interval_delay_countable  [Countable ι] (a h : ι → ℝ)
    {m : ℝ} (hm : 0 < m) (hh : ∀ i, 0 < h i) :
    volume (⋃ i, Ioo (a i-h i) (a i)) ≤
      ENNReal.ofReal ((m+1)/m) * volume (⋃ i, Ioo (a i) (a i+m*h i)) := by
  classical
  let B : Finset ι → Set ℝ := fun s => ⋃ i ∈ s, Ioo (a i-h i) (a i)
  have hB : Monotone B := by
    intro s t hst x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨i, hst hi, hxi⟩
  have heq : (⋃ s, B s) = ⋃ i, Ioo (a i-h i) (a i) := by
    ext x
    simp only [B, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨s, i, _, hx⟩
      exact ⟨i, hx⟩
    · rintro ⟨i, hx⟩
      exact ⟨{i}, i, Finset.mem_singleton_self i, hx⟩
  rw [← heq, hB.measure_iUnion]
  apply iSup_le
  intro s
  calc
    volume (B s) ≤ ENNReal.ofReal ((m+1)/m) *
        volume (⋃ i ∈ s, Ioo (a i) (a i+m*h i)) :=
      interval_delay_finset a h s hm (fun i _ => hh i)
    _ ≤ ENNReal.ofReal ((m+1)/m) * volume (⋃ i, Ioo (a i) (a i+m*h i)) := by
      apply mul_le_mul_right
      apply measure_mono
      intro x hx
      obtain ⟨i, _, hxi⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion.mpr ⟨i, hxi⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
