module

public import Chazelle.Core.OracleEdge

/-!
# Lemma 3.6 (WP-H), part 11: the scan of a node as the program computes it

* `wrap_iff`: only the last arc of the spine wraps around the end of the walk
  (`sk p < ek p ↔ p + 1 < A`); hence the number of scanned walk edges of an arc is computed from
  its two edge indices and its spine position (`scanLen_eq`).
* `mem_nodeScan_iff`: the scanned points of a node are those of the arcs listed by its region
  record, each at its spine position (read from the inverse of the arc-sequence table).
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (sideInArc)

namespace OracleQ

section Wrap

variable {M : Model} {Q : Polygon} {N : NF}

/-- **Only the last arc of the spine wraps.** -/
theorem wrap_iff (hN : IsNF M Q N) (hGM : GoodModel M) {p : ℕ} (hp : p < N.arcs.length) :
    sk M Q N p < ek M Q N p ↔ p + 1 < N.arcs.length := by
  set A := N.arcs.length
  by_cases hne : (N.F M Q).Nonempty
  · obtain ⟨-, -, hne', hfree⟩ := arc_facts hN hne hp
    constructor
    · intro hlt
      by_contra hr
      -- the end of the last arc is a cut, which starts an arc: its start is not after `sk p`
      obtain ⟨-, hc, -, -⟩ := arc_facts hN hne hp
      obtain ⟨U, hU, b, hab⟩ := (arcCover M Q (N.F M Q) hGM hN.1).2 _ hc
      obtain ⟨j, hj, hjs, -⟩ := NFLoc.listed_of_isArc hN hU hab
      obtain ⟨r, hr', hrj⟩ := NFLoc.seq_surj hN hj
      have hsr : sk M Q N r = ek M Q N p := by
        show M.key Q (N.arc (N.seq.getD r 0)).s = _
        rw [hrj, hjs]
      have := sk_mono hN (show r ≤ p by omega) hp
      linarith
    · intro hr
      set r := p + 1
      have hpr := starts_lt hN hGM hne (show p < r by omega) hr
      have hcr := (arc_facts hN hne hr).1
      by_contra hc
      exact hfree _ (by unfold sideInArc; rw [ite_eq_right hc]; exact Or.inl hpr) hcr
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have h1 := arcs_le_one_of_empty hN hGM hne
    obtain ⟨reg, -, -, harc⟩ := isArc_sj hN hp
    have heq : sk M Q N p = ek M Q N p := by
      rcases harc.2.2.2.2.1 with ⟨⟨c, hc, -⟩, -⟩ | ⟨-, h1', h2'⟩
      · rw [hne] at hc; exact absurd hc (Set.notMem_empty _)
      · rw [h1', h2']
    constructor
    · intro h; linarith
    · intro h; omega

end Wrap

section Len

variable (C : Chain) (Q : Polygon) (N : NF)

/-- **The number of scanned walk edges of an arc, minus one**, as the program computes it. -/
def scanLenR (n A p : ℕ) : ℕ :=
  (if p + 1 < A then (N.arc (sj N p)).e.edge - (N.arc (sj N p)).s.edge
    else (N.arc (sj N p)).e.edge + n - (N.arc (sj N p)).s.edge) + 2

theorem scanLen_eq (hN : IsNF (chainModel C) Q N) (hP : C.P.Simple) {p : ℕ}
    (hp : p < N.arcs.length) :
    scanLen C Q N p = scanLenR N (chainModel C).W.n N.arcs.length p := by
  unfold scanLen scanLenR
  have hw := wrap_iff hN (Or.inl ⟨C, hP, rfl⟩) hp
  by_cases h : p + 1 < N.arcs.length
  · rw [ite_eq_left (hw.2 h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hw.1 h')), ite_eq_right h]

end Len

end OracleQ

end

end Chazelle.Core
