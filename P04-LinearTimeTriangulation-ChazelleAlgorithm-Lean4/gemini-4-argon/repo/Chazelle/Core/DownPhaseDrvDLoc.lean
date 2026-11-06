module

public import Chazelle.Core.DownPhaseDrvDArc
public import Chazelle.Core.RestoreDrvMath
public import Chazelle.Core.DownPhaseDrvRBktM

/-!
# Down-phase restoration rounds (D8), part 2: locating the ends of a new chord

For each end `x` of the chord found in region `r`, the round scans the arcs `j` of `r` with two
key decisions, `t₁ = [key s_j ≤ key x]` and `t₂ = [key x ≤ key e_j]`, and on a match
(`matchB`: both, on an arc other than the last one; either one, on the last, wrapping arc) sets
the bucket `bktB` (`j + 1`; on the last arc `0` below its end, `A` above its start).

* `bkt_of_match`: a match gives the bucket condition `BktKey`, and `arcOfB` recovers the arc;
* `exists_closedArc`: the ends of a chord splitting region `r` lie on closed arcs of `r`
  (`Restore.attach_closedArc`), listed by the region record;
* `match_of_closedArc`: in `buildNF`, an end on a closed arc matches;
* `bcnt_le_two`: if the codes of one bucket all belong to one chord, the bucket has at most two
  codes.
-/

namespace Chazelle.Core

namespace DrvD

@[expose] public section

open BuildNF (codeLe wposOf buildNF gapStarts)
open Chazelle.Chain (SideAttach sideInArc)

variable {M : Model} {Q : Polygon}

/-! ## The decision of the arc scan -/

/-- The scan's test on arc `j` of `A` arcs, with `t₁ = [key s ≤ key x]`, `t₂ = [key x ≤ key e]`. -/
def matchB (A j : ℕ) (t₁ t₂ : Bool) : Bool := if j + 1 < A then t₁ && t₂ else t₂ || t₁

/-- The bucket the scan assigns on a match. -/
def bktB (A j : ℕ) (t₂ : Bool) : ℕ := if j + 1 < A then j + 1 else if t₂ then 0 else A

/-- The arc of a bucket. -/
def arcOfB (A b : ℕ) : ℕ := if b = 0 ∨ A ≤ b then A - 1 else b - 1

theorem arcOfB_bktB {A j : ℕ} (hj : j < A) (t₂ : Bool) : arcOfB A (bktB A j t₂) = j := by
  unfold arcOfB bktB
  by_cases h : j + 1 < A
  · rw [ite_eq_left h, ite_eq_right (by omega)]; omega
  · rw [ite_eq_right h]
    cases t₂ <;> simp <;> omega

/-- **A match gives the bucket condition.** -/
theorem bkt_of_match (N : NF) {x : ℝ} {j : ℕ} (hj : j < N.arcs.length) {t₁ t₂ : Bool}
    (h₁ : t₁ = true ↔ M.key Q (N.arc j).s ≤ x) (h₂ : t₂ = true ↔ x ≤ M.key Q (N.arc j).e)
    (hm : matchB N.arcs.length j t₁ t₂ = true) : BktKey M Q N x (bktB N.arcs.length j t₂) := by
  unfold matchB at hm
  unfold bktB
  by_cases h : j + 1 < N.arcs.length
  · rw [ite_eq_left h] at hm ⊢
    simp only [Bool.and_eq_true] at hm
    right; left
    exact ⟨by omega, h, by rw [Nat.add_sub_cancel]; exact h₁.1 hm.1,
      by rw [Nat.add_sub_cancel]; exact h₂.1 hm.2⟩
  · rw [ite_eq_right h] at hm ⊢
    have hjA : j = N.arcs.length - 1 := by omega
    by_cases ht : t₂ = true
    · rw [ite_eq_left ht]
      left
      exact ⟨rfl, by rw [← hjA]; exact h₂.1 ht⟩
    · rw [ite_eq_right ht]
      have ht1 : t₁ = true := by
        simp only [Bool.or_eq_true] at hm
        rcases hm with h' | h'
        · exact absurd h' ht
        · exact h'
      right; right
      exact ⟨rfl, by rw [← hjA]; exact h₁.1 ht1⟩

/-! ## The ends of a new chord lie on arcs of its region -/

/-- **The ends of a chord splitting region `r` lie on closed arcs of `r`.** -/
theorem exists_closedArc (hM : WalkAx M) {N : NF} {reg : ℕ → Set Point} (hNF : IsNF M Q N)
    (hregs : Restore.NFRegs M Q N reg) (hne : (N.F M Q).Nonempty) {r : ℕ} (hr : r < N.nRegions)
    {e : Set Point} (he : e ∈ M.Adm) (hw : Restore.SplitsWell M (N.F M Q) (reg r) e) {p : ℕ}
    {τ : ℝ} (hA : SideAttach M.W e p τ) :
    ∃ j ∈ (N.region r).arcs, j < N.arcs.length ∧
      Restore.ClosedArc (M.key Q (N.arc j).s) (M.key Q (N.arc j).e) (p + τ) := by
  obtain ⟨a, b, harc, hcl⟩ := Restore.attach_closedArc hM hNF.1.2.1 hNF.1.1 hne (hregs.1.1 r hr)
    he hw.1 hw.2.1 hA
  obtain ⟨j, hj, hjr, hs, he'⟩ := hregs.2.2.1.2.2.1 r hr a b harc
  refine ⟨j, (hregs.2.2.1.2.2.2 r hr j).2 ⟨hj, hjr⟩, hj, ?_⟩
  rwa [hs, he']

variable {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

/-- **In `buildNF`, an end on a closed arc matches.** -/
theorem match_of_closedArc (hK : 0 < L.length) (hE : 0 < E.length) {j : ℕ}
    (_hj : j < (buildNF M Q L E).arcs.length) {x : ℝ}
    (hc : Restore.ClosedArc (M.key Q ((buildNF M Q L E).arc j).s)
      (M.key Q ((buildNF M Q L E).arc j).e) x) {t₁ t₂ : Bool}
    (h₁ : t₁ = true ↔ M.key Q ((buildNF M Q L E).arc j).s ≤ x)
    (h₂ : t₂ = true ↔ x ≤ M.key Q ((buildNF M Q L E).arc j).e) :
    matchB (buildNF M Q L E).arcs.length j t₁ t₂ = true := by
  unfold matchB
  by_cases h : j + 1 < (buildNF M Q L E).arcs.length
  · rw [ite_eq_left h]
    have hlt := key_s_lt_e (M := M) (Q := Q) hK hE (j := j) (by rwa [← arcs_length hK])
    simp only [Bool.and_eq_true]
    rcases hc with hc | hc | hc
    · unfold sideInArc at hc
      rw [ite_eq_left hlt] at hc
      exact ⟨h₁.2 hc.1.le, h₂.2 hc.2.le⟩
    · exact ⟨h₁.2 hc.ge, h₂.2 (hc ▸ hlt.le)⟩
    · exact ⟨h₁.2 (hc ▸ hlt.le), h₂.2 hc.le⟩
  · rw [ite_eq_right h]
    simp only [Bool.or_eq_true]
    rcases hc with hc | hc | hc
    · unfold sideInArc at hc
      split_ifs at hc
      · exact Or.inl (h₂.2 hc.2.le)
      · rcases hc with hc | hc
        · exact Or.inr (h₁.2 hc.le)
        · exact Or.inl (h₂.2 hc.le)
    · exact Or.inr (h₁.2 hc.ge)
    · exact Or.inl (h₂.2 hc.le)

/-! ## Bucket sizes -/

/-- **A bucket whose codes all belong to one chord has at most two codes.** -/
theorem bcnt_le_two {bk : ℕ → ℕ} {n b : ℕ}
    (h : ∀ q q', q < n → q' < n → bk q = b → bk q' = b → q / 2 = q' / 2) :
    DrvR.bcnt bk n b ≤ 2 := by
  unfold DrvR.bcnt
  by_contra hcon
  push Not at hcon
  set l := DrvR.bfilt bk n b
  have hpw : l.Pairwise (· < ·) := List.Pairwise.filter _ List.pairwise_lt_range
  have m0 := (DrvR.mem_bfilt (bk := bk)).1 (List.getElem_mem (l := l) (n := 0) (by omega))
  have m2 := (DrvR.mem_bfilt (bk := bk)).1 (List.getElem_mem (l := l) (n := 2) (by omega))
  have h01 := List.pairwise_iff_getElem.1 hpw 0 1 (by omega) (by omega) (by omega)
  have h12 := List.pairwise_iff_getElem.1 hpw 1 2 (by omega) (by omega) (by omega)
  have := h _ _ m0.1 m2.1 m0.2 m2.2
  omega

end

end DrvD

end Chazelle.Core
