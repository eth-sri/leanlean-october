module

public import Chazelle.Core.GranInitL5

/-!
# WP-F, init part 11: the areas of a normal form readable below a bound

`NFWithin m B E N` (the normal form can be read from every memory agreeing with `m` below `E`)
puts every word the initialisation reads below `E` (`nf_areas`): the header, the chord, region
and arc records, the sequence table and the exit lists.  The exit lists are reached through two
pointers (`robust_addr3`).
-/

namespace Chazelle.Core

namespace Gran

open NFLoc

@[expose] public section

/-- A word reached through the sum of two pointers, the second one below the bound, that robustly
holds a value lies below the bound. -/
theorem robust_addr3 {E : ℕ} {m : ℕ → ℕ} {b₁ p₂ t v : ℕ} (hp₂ : p₂ < E)
    (h : Robust E m fun m' => m' (m' b₁ + m' p₂ + t) = v) : m b₁ + m p₂ + t < E := by
  rw [Nat.add_assoc]
  exact (Robust.ptrAddress_of (b := b₁) (fun mm hm => congrArg (· + t) (hm p₂ hp₂))
    (fun mm hm => by simpa only [Nat.add_assoc] using h mm hm)).2

/-- **The areas of a normal form readable below `E`.** -/
theorem nf_areas {m : ℕ → ℕ} {B E : ℕ} {N : NF} (h : NFWithin m B E N) :
    B + 7 < E ∧
    (∀ i, i < N.nChords → m (B + 3) + 5 * i + 4 < E) ∧
    (∀ r, r < N.nRegions → m (B + 5) + 5 * r + 4 < E) ∧
    (∀ r, r < N.nRegions → ∀ t, t < (N.region r).chords.length →
      m (B + 7) + m (m (B + 5) + 5 * r + 3) + t < E) ∧
    (∀ j, j < N.arcs.length → m (B + 4) + 5 * j + 4 < E) ∧
    (∀ j, j < N.seq.length → m (B + 6) + j < E) := by
  have q := h.bounds
  exact ⟨by have := q.hdr; omega, q.chord, q.region, fun r hr t ht => q.regionChord r t hr ht, q.arc, q.seq⟩

end

end Gran

end Chazelle.Core
