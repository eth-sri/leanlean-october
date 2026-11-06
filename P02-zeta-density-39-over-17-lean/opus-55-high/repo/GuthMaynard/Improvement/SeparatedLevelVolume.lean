module
public import MathCollab.Density.ZeroSeparation
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import WeylPort.Analytic.RealLaplace

public section
open MeasureTheory Set
open scoped ENNReal
namespace GuthMaynard.Improvement

/-- A bounded measurable or nonmeasurable level set has volume at most twice
any uniform bound for the cardinalities of its one-separated finite subsets. -/
theorem level_volume_of_separated_bound {S : Set ℝ} {a b B : ℝ}
    (hS : S ⊆ Icc a b)
    (hcard : ∀ W : Finset ℝ, (∀ x ∈ W, x ∈ S) →
      (∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x-y|) → (W.card:ℝ) ≤ B) :
    volume.real S ≤ 2*B := by
  classical
  let K := (Finset.Icc ⌊a⌋ ⌊b⌋).filter (fun k => ∃ x ∈ S, ⌊x⌋ = k)
  have hK (x : ℝ) (hx : x ∈ S) : ⌊x⌋ ∈ K := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_,?_⟩,x,hx,rfl⟩
    · exact Int.floor_mono (hS hx).1
    · exact Int.floor_mono (hS hx).2
  pm_4600
  have hinj : Set.InjOn f (J : Set ℤ) := by
    intro k hk l hl he
    rw [← (hfJ k hk).2, ← (hfJ l hl).2,he]
  pm_4601
  have hcover : S ⊆ ⋃ k ∈ K, Ico (k:ℝ) ((k:ℝ)+1) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⌊x⌋,mem_iUnion.mpr ⟨hK x hx,
      ⟨Int.floor_le x,Int.lt_floor_add_one x⟩⟩⟩
  have hm : volume S ≤ (K.card : ℝ≥0∞) := by
    calc
      _ ≤ volume (⋃ k ∈ K, Ico (k:ℝ) ((k:ℝ)+1)) := measure_mono hcover
      _ ≤ ∑ k ∈ K, volume (Ico (k:ℝ) ((k:ℝ)+1)) := measure_biUnion_finset_le _ _
      _ = _ := by simp
  have hmreal : volume.real S ≤ (K.card:ℝ) := by
    simpa [Measure.real] using ENNReal.toReal_mono (by simp : (K.card:ℝ≥0∞) ≠ ⊤) hm
  pm_373 hcounts K.card J.card hcount
  linarith

end GuthMaynard.Improvement
