module

public import Chazelle.Core.Facts2Trap

/-! Horizontal-chord lemmas used to count chords adjacent to a region. -/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (IsHChordIn freeIn regionsIn TouchesIn box)
open Chazelle.Visibility (hseg)
open Chazelle.Geometry (point_ext)

namespace SegObs

/-! ## Horizontal chords of an arbitrary domain -/

section Chords

variable {D : Set Point}

/-- A horizontal chord of the domain `D`. -/
def HCD (D : Set Point) (c : Set Point) : Prop :=
  ∃ y a b : ℝ, IsHChordIn D y a b ∧ c = hseg y a b

/-- A point of a chord in the domain is strictly inside it. -/
theorem open_of_mem {y a b : ℝ} (h : IsHChordIn D y a b) {z : Point} (hz : z ∈ hseg y a b)
    (hzD : z ∈ D) : a < z.1 ∧ z.1 < b := by
  obtain ⟨hzy, hza, hzb⟩ := hz
  refine ⟨lt_of_le_of_ne hza fun e => h.left_not ?_, lt_of_le_of_ne hzb fun e => h.right_not ?_⟩
  · have : ((a, y) : Point) = z := point_ext e hzy.symm
    rwa [this]
  · have : ((b, y) : Point) = z := point_ext e.symm hzy.symm
    rwa [this]

/-- Two chords sharing a point of the domain are equal. -/
theorem eq_of_common {c c' : Set Point} (hc : HCD D c) (hc' : HCD D c') {z : Point} (hz : z ∈ c)
    (hz' : z ∈ c') (hzD : z ∈ D) : c = c' := by
  obtain ⟨y, a, b, h, rfl⟩ := hc
  obtain ⟨y', a', b', h', rfl⟩ := hc'
  rcases Chazelle.Chain.hchordIn_inter h h' hz hz' with ⟨rfl, rfl, rfl⟩ | ⟨h1 | h1, -⟩
  · rfl
  · exact absurd (h1 ▸ hzD) h.left_not
  · exact absurd (h1 ▸ hzD) h.right_not

/-- A chord contains every point of its line joined to it inside the domain. -/
theorem mem_of_joined {y a b : ℝ} (h : IsHChordIn D y a b) {z : Point} (hz : z ∈ hseg y a b)
    (hzD : z ∈ D) {w : Point} (hw : w.2 = y)
    (hj : ∀ s : ℝ, min z.1 w.1 ≤ s → s ≤ max z.1 w.1 → ((s, y) : Point) ∈ D) :
    w ∈ hseg y a b := by
  obtain ⟨hza, hzb⟩ := open_of_mem h hz hzD
  refine ⟨hw, ?_, ?_⟩
  · by_contra hwa
    push Not at hwa
    exact h.left_not (hj a (by have := min_le_right z.1 w.1; linarith) (by
      have := le_max_left z.1 w.1; linarith))
  · by_contra hwb
    push Not at hwb
    exact h.right_not (hj b (by have := min_le_left z.1 w.1; linarith) (by
      have := le_max_right z.1 w.1; linarith))

end Chords

/-! ## Chords on a horizontal side of the trapezoid -/

variable {R : ℝ} {S : Set (Point × Point)}


end SegObs
end
end Chazelle.Core
