module

public import Chazelle.Core.NFBuildGlue
public import Chazelle.Core.NFBuildWtRam
public import Chazelle.Core.NFBuildEvCmp

/-!
# WP-C (BuildNF), RAM part 7: the weight of an arc record by the machine formula

`arcW_eq`: for a gap start `m` of the sorted codes (`K > 0`), the weight of its arc record is
`wtF lo hi ea eb pz lt`, with the edges `ea`, `eb` of its two ends, the parameter bit `pz` of its
end and `lt = 1` iff the gap does not wrap (`m + 1 < 2K`).
-/

namespace Chazelle.Core

namespace BuildNF

@[expose] public section

open List
open BuildRam (wtF)

variable {M : Model} {P : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

/-- The codes of a permutation of `range N` are below `N`. -/
theorem getD_lt_of_perm {N : ℕ} (hp : E.Perm (range N)) {m : ℕ} (hm : m < E.length) :
    E.getD m 0 < N := by
  rw [getD_eq_getElem?_getD, getElem?_eq_getElem hm, Option.getD_some]
  exact mem_range.1 (hp.mem_iff.1 (getElem_mem hm))

/-- The key of the first sorted code is at most the key of any later one. -/
theorem Input.key_first_le (h : Input M (Qof P) L E) {m : ℕ} (hm : m < E.length) :
    M.key (Qof P) (wposOf L (E.getD 0 0)) ≤ M.key (Qof P) (wposOf L (E.getD m 0)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · exact le_rfl
  rw [h.key_s (by omega), h.key_s hm, BuildSort.kap_eq (by rw [h.length_evs]; omega),
    BuildSort.kap_eq (by rw [h.length_evs]; exact hm)]
  exact BuildSort.key_le_of_evLe (List.pairwise_iff_getElem.1 h.sorted 0 m (by
    rw [length_map]; omega) (by rw [length_map]; exact hm) hpos)

/-- **The weight of an arc record** by the machine formula. -/
theorem Input.arcW_eq (h : Input M (Qof P) L E) {m : ℕ} (hm : m < E.length)
    (hgap : m ∈ gapStarts M (Qof P) L E) {lo hi : ℕ}
    (hc : ∀ p, p < M.W.n → (M.counted p ↔ lo ≤ p ∧ p < hi)) (hhi : hi ≤ M.W.n) {pz : ℕ}
    (hpz : pz = 1 ↔ M.counted (wposOf L (E.getD ((m + 1) % E.length) 0)).edge ∧
      M.param (Qof P) (wposOf L (E.getD ((m + 1) % E.length) 0)) ≠ 0) (hpz1 : pz ≤ 1) :
    arcW M (Qof P) (arcRec M (Qof P) L E m) =
      wtF lo hi (wposOf L (E.getD m 0)).edge (wposOf L (E.getD ((m + 1) % E.length) 0)).edge pz
        (if m + 1 < E.length then 1 else 0) := by
  have hlen := h.length_E
  have hm2 : (m + 1) % E.length < E.length := Nat.mod_lt _ (by omega)
  have ps := BuildRam.properPos_ev h.valid (c := E.getD m 0) (by
    exact getD_lt_of_perm h.perm hm)
  have pe := BuildRam.properPos_ev h.valid (c := E.getD ((m + 1) % E.length) 0) (by
    exact getD_lt_of_perm h.perm hm2)
  have he := BuildRam.edge_lt h.valid (c := E.getD ((m + 1) % E.length) 0) (by
    exact getD_lt_of_perm h.perm hm2)
  unfold arcW arcRec
  simp only
  rw [M.arcWt_key hc hhi (Qof P) ⟨ps.1, ps.2.1⟩ ⟨pe.1, pe.2.1⟩]
  refine BuildRam.arcWtNat_eq_wtF (hc _ he) hpz hpz1 ?_
  change _ ↔ M.key (Qof P) _ < M.key (Qof P) _
  by_cases hw : m + 1 < E.length
  · rw [ite_eq_left hw, Nat.mod_eq_of_lt hw]
    have := (h.gap_iff hm).1 hgap
    simp only [show m + 1 ≠ E.length by omega, false_or] at this
    exact ⟨fun _ => this, fun _ => rfl⟩
  · rw [ite_eq_right hw, show (m + 1) % E.length = 0 by
      rw [show m + 1 = E.length by omega, Nat.mod_self]]
    refine ⟨fun h' => absurd h' (by norm_num), fun h' => ?_⟩
    exact absurd (h.key_first_le hm) (not_le.2 h')

end

end BuildNF

end Chazelle.Core
