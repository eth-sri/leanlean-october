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
  have hb₁ : b₁ < E := by
    by_contra hge
    set Z := E + b₁ + m p₂ + t + 1 with hZ
    have := h (Function.update (Function.update m b₁ Z) (Z + m p₂ + t) (v + 1))
      (fun a ha => by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
    simp at this
    rw [Function.update_of_ne (show b₁ ≠ Z + m p₂ + t by omega), Function.update_self,
      Function.update_of_ne (show p₂ ≠ Z + m p₂ + t by omega),
      Function.update_of_ne (show p₂ ≠ b₁ by omega), Function.update_self] at this
    omega
  by_contra hge
  have := h (Function.update m (m b₁ + m p₂ + t) (v + 1)) (fun a ha => by
    rw [Function.update_of_ne (by omega)])
  simp at this
  rw [Function.update_of_ne (show b₁ ≠ m b₁ + m p₂ + t by omega),
    Function.update_of_ne (show p₂ ≠ m b₁ + m p₂ + t by omega), Function.update_self] at this
  omega

/-- **The areas of a normal form readable below `E`.** -/
theorem nf_areas {m : ℕ → ℕ} {B E : ℕ} {N : NF} (h : NFWithin m B E N) :
    B + 7 < E ∧
    (∀ i, i < N.nChords → m (B + 3) + 5 * i + 4 < E) ∧
    (∀ r, r < N.nRegions → m (B + 5) + 5 * r + 4 < E) ∧
    (∀ r, r < N.nRegions → ∀ t, t < (N.region r).chords.length →
      m (B + 7) + m (m (B + 5) + 5 * r + 3) + t < E) ∧
    (∀ j, j < N.arcs.length → m (B + 4) + 5 * j + 4 < E) ∧
    (∀ j, j < N.seq.length → m (B + 6) + j < E) := by
  have hB : B + 11 < E := robust_addr (v := N.dec.length) fun m' hm' => (h m' hm').2.2.2.2.1
  refine ⟨by omega, fun i hi => ?_, fun r hr => ?_, fun r hr t ht => ?_, fun j hj => ?_,
    fun j hj => ?_⟩
  · have := robust_addr2 (b := B + 3) (o := 5 * i + 4) (v := (N.chord i).dn)
      (fun m' hm' => by
        have := ((h m' hm').2.2.2.2.2.1 i hi).2.2.2.2
        simpa only [Nat.add_assoc] using this)
    omega
  · have := robust_addr2 (b := B + 5) (o := 5 * r + 4) (v := (N.region r).wt)
      (fun m' hm' => by
        have := ((h m' hm').2.2.2.2.2.2.2.1 r hr).2.2.1
        simpa only [Nat.add_assoc] using this)
    omega
  · have hp : m (B + 5) + 5 * r + 3 < E := by
      have := robust_addr2 (b := B + 5) (o := 5 * r + 4) (v := (N.region r).wt)
        (fun m' hm' => by
          have := ((h m' hm').2.2.2.2.2.2.2.1 r hr).2.2.1
          simpa only [Nat.add_assoc] using this)
      omega
    have := robust_addr3 (b₁ := B + 7) (p₂ := m (B + 5) + 5 * r + 3) (t := t)
      (v := (N.region r).chords.getD t 0) hp (fun m' hm' => by
        have e5 : m' (B + 5) = m (B + 5) := hm' _ (by omega)
        have := ((h m' hm').2.2.2.2.2.2.2.1 r hr).2.2.2.2 t ht
        rw [e5] at this
        exact this)
    exact this
  · have := robust_addr2 (b := B + 4) (o := 5 * j + 4) (v := (N.arc j).e.hgt)
      (fun m' hm' => by
        have := ((h m' hm').2.2.2.2.2.2.1 j hj).2.2.2.2
        simpa only [Nat.add_assoc] using this)
    omega
  · have := robust_addr2 (b := B + 6) (o := j) (v := N.seq.getD j 0)
      (fun m' hm' => (h m' hm').2.2.2.2.2.2.2.2.1 j hj)
    omega

end

end Gran

end Chazelle.Core
