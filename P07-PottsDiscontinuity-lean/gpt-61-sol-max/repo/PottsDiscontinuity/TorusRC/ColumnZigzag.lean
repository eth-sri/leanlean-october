module
public import Mathlib

public import PottsDiscontinuity.TorusRC.LiftedPaths

/-! # Explicit vertical zigzags in the lifted right half -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

/-- A nearest-neighbor zigzag in the two columns x and x+1. -/
def columnZigzagSite (x : ℤ) (hx : Even x) (t : ℕ) : RotatedVertex :=
  ⟨(x + (t % 2 : ℕ), t), by
    grind⟩

section

variable (x : ℤ) (hx : Even x) (t : ℕ)


theorem columnZigzagSite_adj  :
    rotatedLattice.Adj (columnZigzagSite x hx t) (columnZigzagSite x hx (t + 1)) := by
  grind [rotatedLattice, columnZigzagSite]

theorem columnZigzagSite_even  (ht : Even t) :
    columnZigzagSite x hx t = liftedColumnSite x t hx (by exact_mod_cast ht) := by
  grind [columnZigzagSite, liftedColumnSite]

end

section

variable (hNp : 0 < N) (hMp : 0 < M)
include hNp hMp

theorem columnZigzagSite_index 
    (x : ℤ) (hx : Even x) (t : ℕ) :
    liftedEdgeIndex hNp hMp (columnZigzagSite x hx t)
      (columnZigzagSite x hx (t + 1)) =
      (periodicCoordinate hNp (x + 1), periodicCoordinate hMp (t + 1)) := by
  have hxmax : max (x + (t % 2 : ℕ)) (x + ((t + 1) % 2 : ℕ)) = x + 1 := by
    omega
  change (periodicCoordinate hNp (max (x + (t % 2 : ℕ))
    (x + ((t + 1) % 2 : ℕ))), periodicCoordinate hMp (max t (t + 1 : ℕ))) = _
  rw [hxmax, max_eq_right (by omega)]
  rfl

/-- Every finite portion of an open zigzag gives a localized lifted path.
The endpoint is allowed to be the top seam lift at height M. -/
theorem columnZigzag_box_connection 
    (A : RCConfig N M) (a b x : ℤ) (hx : Even x) (s t R : ℕ)
    (hst : s ≤ t) (hR : t - s ≤ R) (hR1 : 1 ≤ R)
    (ha : a ≤ x) (hb : x + 1 ≤ b)
    (hopen : ∀ k, s ≤ k → k < t →
      A (periodicCoordinate hNp (x + 1), periodicCoordinate hMp (k + 1)) = true) :
    liftedBoxConnection hNp hMp A a b R
      (columnZigzagSite x hx s) (columnZigzagSite x hx t) := by
  have hwalk (d : ℕ) (hd : s + d ≤ t) :
      ∃ w : (liftedStripGraph hNp hMp A a b).Walk
          (columnZigzagSite x hx s) (columnZigzagSite x hx (s + d)),
        ∀ z ∈ w.support, inLiftedBox R (columnZigzagSite x hx s) z := by
    induction d with
    | zero =>
      refine ⟨.nil, ?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst z
      simp [inLiftedBox]
    | succ d ih =>
      obtain ⟨w, hw⟩ := ih (by omega)
      have hadj : (liftedStripGraph hNp hMp A a b).Adj
          (columnZigzagSite x hx (s + d)) (columnZigzagSite x hx (s + (d + 1))) := by
        refine ⟨columnZigzagSite_adj x hx (s + d), ?_, ?_, ?_⟩
        · grind [columnZigzagSite_index]
        · grind +locals
        · grind +locals
      refine ⟨w.append (.cons hadj .nil), ?_⟩
      intro z hz
      rw [SimpleGraph.Walk.support_append] at hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hw z hz
      · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
          List.tail_cons, List.mem_singleton] at hz
        subst z
        dsimp [inLiftedBox, columnZigzagSite]
        constructor <;> apply abs_le.mpr <;> constructor <;> omega
  have hw := hwalk (t - s) (by omega)
  rw [Nat.add_sub_of_le hst] at hw
  exact hw

end

end PottsDiscontinuity.TorusRC
