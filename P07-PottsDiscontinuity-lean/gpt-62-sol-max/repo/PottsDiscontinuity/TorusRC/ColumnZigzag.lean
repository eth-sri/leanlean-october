module

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

theorem columnZigzagSite_adj (x : ℤ) (hx : Even x) (t : ℕ) :
    rotatedLattice.Adj (columnZigzagSite x hx t) (columnZigzagSite x hx (t + 1)) := by
  grind [rotatedLattice, columnZigzagSite]

theorem columnZigzagSite_even (x : ℤ) (hx : Even x) (t : ℕ) (ht : Even t) :
    columnZigzagSite x hx t = liftedColumnSite x t hx (by exact_mod_cast ht) := by
  apply Subtype.ext
  have ht0 : t % 2 = 0 := Nat.even_iff.mp ht
  simp [columnZigzagSite, liftedColumnSite, ht0]

theorem columnZigzagSite_index (hNp : 0 < N) (hMp : 0 < M)
    (x : ℤ) (hx : Even x) (t : ℕ) :
    liftedEdgeIndex hNp hMp (columnZigzagSite x hx t)
      (columnZigzagSite x hx (t + 1)) =
      (periodicCoordinate hNp (x + 1), periodicCoordinate hMp (t + 1)) := by
  have hxmax : max (x + (t % 2 : ℕ)) (x + ((t + 1) % 2 : ℕ)) = x + 1 := by
    have ht : t % 2 = 0 ∨ t % 2 = 1 := by omega
    rcases ht with ht | ht <;> simp [Nat.add_mod, ht]
  change (periodicCoordinate hNp (max (x + (t % 2 : ℕ))
    (x + ((t + 1) % 2 : ℕ))), periodicCoordinate hMp (max (t : ℤ) (t + 1 : ℕ))) = _
  rw [hxmax, max_eq_right (by omega)]
  rfl

/-- An open zigzag in the strip has a walk supported on the indicated integer interval. -/
theorem columnZigzag_walk (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (a b x : ℤ) (hx : Even x) (s t : ℕ)
    (hst : s ≤ t) (ha : a ≤ x) (hb : x + 1 ≤ b)
    (hopen : ∀ k, s ≤ k → k < t →
      A (periodicCoordinate hNp (x + 1), periodicCoordinate hMp (k + 1)) = true) :
    ∃ w : (liftedStripGraph hNp hMp A a b).Walk (columnZigzagSite x hx s) (columnZigzagSite x hx t),
      ∀ z ∈ w.support, ∃ k, s ≤ k ∧ k ≤ t ∧ z = columnZigzagSite x hx k := by
  have hstrip (k : ℕ) : a ≤ (columnZigzagSite x hx k).val.1 ∧ (columnZigzagSite x hx k).val.1 ≤ b := by
    dsimp [columnZigzagSite]; omega
  induction t, hst using Nat.le_induction with
  | base =>
    refine ⟨.nil, ?_⟩
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton]
    rintro _ rfl
    exact ⟨s, le_rfl, le_rfl, rfl⟩
  | succ t ht ih =>
    obtain ⟨w, hw⟩ := ih (fun k hk hkt => hopen k hk (by omega))
    let h : (liftedStripGraph hNp hMp A a b).Adj (columnZigzagSite x hx t) (columnZigzagSite x hx (t + 1)) :=
      ⟨columnZigzagSite_adj x hx t, by rw [columnZigzagSite_index]; exact hopen _ ht (by omega),
        hstrip t, hstrip (t + 1)⟩
    refine ⟨w.append h.toWalk, ?_⟩
    simp only [SimpleGraph.Walk.support_append, SimpleGraph.Adj.support_toWalk, List.tail_cons,
      List.mem_append, List.mem_singleton]
    rintro z (hz | rfl)
    · obtain ⟨k, hk, hkt, rfl⟩ := hw z hz
      exact ⟨k, hk, hkt.step, rfl⟩
    · exact ⟨t + 1, ht.step, le_rfl, rfl⟩

/-- Every finite portion of an open zigzag gives a localized lifted path.
The endpoint is allowed to be the top seam lift at height M. -/
theorem columnZigzag_box_connection (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (a b x : ℤ) (hx : Even x) (s t R : ℕ)
    (hst : s ≤ t) (hR : t - s ≤ R) (hR1 : 1 ≤ R)
    (ha : a ≤ x) (hb : x + 1 ≤ b)
    (hopen : ∀ k, s ≤ k → k < t →
      A (periodicCoordinate hNp (x + 1), periodicCoordinate hMp (k + 1)) = true) :
    liftedBoxConnection hNp hMp A a b R
      (columnZigzagSite x hx s) (columnZigzagSite x hx t) := by
  obtain ⟨w, hw⟩ := columnZigzag_walk hNp hMp A a b x hx s t hst ha hb hopen
  refine ⟨w, fun z hz => ?_⟩
  obtain ⟨k, hsk, hkt, rfl⟩ := hw z hz
  simp only [inLiftedBox, columnZigzagSite, abs_le]
  omega

end PottsDiscontinuity.TorusRC
