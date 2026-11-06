module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.IntervalDelayFinite
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-! # Sharp delayed-interval union inequality

The finite estimate uses bounded open components. The countable estimate follows by
continuity from below over finite subfamilies, with no uniform bound on the intervals.
-/

@[expose] public section


namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/-- A bounded forward union controls the preceding union by the sharp delay factor. -/
theorem interval_delay_of_bounded_union {ι : Type*} (a h : ι → ℝ) (I : Set ι)
    {m : ℝ} (hm : 0 < m) (hh : ∀ i ∈ I, 0 < h i)
    (hbelow : BddBelow (⋃ i ∈ I, Ioo (a i) (a i + m*h i)))
    (habove : BddAbove (⋃ i ∈ I, Ioo (a i) (a i + m*h i))) :
    volume (⋃ i ∈ I, Ioo (a i-h i) (a i)) ≤
      ENNReal.ofReal ((m+1)/m) * volume (⋃ i ∈ I, Ioo (a i) (a i+m*h i)) := by
  let U := ⋃ i ∈ I, Ioo (a i) (a i+m*h i)
  obtain ⟨C, hcount, hdisj, hcomp, hcover, hcontains⟩ :=
    bounded_open_interval_components (isOpen_biUnion fun _ _ => isOpen_Ioo) hbelow habove
  let ext  := fun s => Ioo (sInf s-(sSup s-sInf s)/m) (sSup s)
  have hback : (⋃ i ∈ I, Ioo (a i-h i) (a i)) ⊆ ⋃ s ∈ C, ext s := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    have hai : a i < a i+m*h i := by nlinarith only [hm, hh i hi]
    obtain ⟨s, hs, hIs⟩ := hcontains _ _ hai
      (subset_iUnion₂_of_subset i hi Subset.rfl)
    have hI := backwardInterval_subset_component_extension (hh i hi) hm
      (hIs.trans (subset_of_eq (hcomp s hs).2))
    exact mem_iUnion₂.mpr ⟨s, hs, hI hxi⟩
  have hvol : ∀ s ∈ C, volume (ext s) = ENNReal.ofReal ((m+1)/m) * volume s := by
    intro s hs
    rw [volume_component_extension hm, ← (hcomp s hs).2]
  have hmeas : ∀ s ∈ C, MeasurableSet s := by
    intro s hs
    rw [(hcomp s hs).2]
    simp
  calc
    volume _ ≤ volume _ :=
      measure_mono hback
    _ ≤ ∑' s : C, volume _ := measure_biUnion_le volume hcount ext
    _ = ∑' s : C, ENNReal.ofReal _ * volume _ :=
      tsum_congr fun s => hvol s s.2
    _ = ENNReal.ofReal _ * ∑' s : C, volume _ :=
      ENNReal.tsum_mul_left
    _ = ENNReal.ofReal _ * volume U := by
      have hsum := measure_biUnion (μ := volume) hcount hdisj hmeas
      grind

/-- The sharp delayed-union inequality for a finite interval family. -/
theorem interval_delay_finset {ι : Type*} (a h : ι → ℝ) (s : Finset ι)
    {m : ℝ} (hm : 0 < m) (hh : ∀ i ∈ s, 0 < h i) :
    volume (⋃ i ∈ s, Ioo (a i-h i) (a i)) ≤
      ENNReal.ofReal ((m+1)/m) * volume (⋃ i ∈ s, Ioo (a i) (a i+m*h i)) := by
  apply interval_delay_of_bounded_union a h _ hm hh
  · obtain ⟨l, hl⟩ := (s.finite_toSet.image a).bddBelow
    refine ⟨l, ?_⟩
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact (hl (mem_image_of_mem a hi)).trans hxi.1.le
  · obtain ⟨b, hb⟩ := (s.finite_toSet.image (fun i => a i+m*h i)).bddAbove
    refine ⟨b, ?_⟩
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact hxi.2.le.trans (hb (mem_image_of_mem _ hi))

/-- Countable delayed interval families satisfy the same sharp factor. -/
theorem interval_delay_countable {ι : Type*} [Countable ι] (a h : ι → ℝ)
    {m : ℝ} (hm : 0 < m) (hh : ∀ i, 0 < h i) :
    volume (⋃ i, Ioo (a i-h i) (a i)) ≤
      ENNReal.ofReal ((m+1)/m) * volume (⋃ i, Ioo (a i) (a i+m*h i)) := by
  classical
  let B : Finset ι → Set ℝ := fun s => ⋃ i ∈ s, Ioo (a i-h i) (a i)
  have hB : Monotone B := by
    intro s t hst x hx
    aesop
  have heq : (⋃ s, B s) = ⋃ i, Ioo (a i-h i) (a i) := by
    ext x
    simp only [B, mem_iUnion]
    constructor
    · grind
    · rintro ⟨i, hx⟩
      exact ⟨{i}, i, Finset.mem_singleton_self i, hx⟩
  rw [← heq, hB.measure_iUnion]
  apply iSup_le
  intro s
  calc
    volume _ ≤ ENNReal.ofReal _ *
        volume _ :=
      interval_delay_finset a h s hm (fun i _ => hh i)
    _ ≤ ENNReal.ofReal _ * volume _ := by
      apply mul_le_mul_right
      apply measure_mono
      intro x hx
      aesop

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
