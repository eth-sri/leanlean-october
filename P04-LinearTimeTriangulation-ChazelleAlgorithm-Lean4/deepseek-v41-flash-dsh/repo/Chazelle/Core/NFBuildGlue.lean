module

public import Chazelle.Golf

public import Chazelle.Core.NFBuildValid

/-!
# WP-C (BuildNF), RAM part 3: `buildNF` in the terms of the machine pass

The machine computes `buildNF M Q L E` in one pass over the sorted codes `E` with a stack of chord
indices.  This file restates the definitions of `buildNF` in the terms of that pass:

* `word_eq`: the chord word is `E.map (· / 2)`;
* `first_e1`, `outside_eq`: the first occurrence of chord `i` in the word is its first event; the
  label outside chord `i` is the label before that occurrence;
* `first_parity`: that first event is the left endpoint iff `kl i < kr i`;
* `chordRec_eq`: the chord record from the first occurrence;
* `push_iff`: the stack pass pops at position `m` iff the letter occurred before;
* `gap_iff`: the gap starts are the positions where the key strictly increases (and the last).
-/

namespace Chazelle.Core

namespace BuildNF

@[expose] public section

open List
open BuildSort (Ev EvLe kap cntBelow)
open BuildRegions (eL eR crec famOf e1 e2 kl kr lo hi)

variable {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

theorem evOf_fst (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (c : ℕ) :
    (evOf M Q L c).1 = c / 2 := by
  unfold evOf; split_ifs <;> rfl

/-- **The chord word** is the list of chords of the codes. -/
theorem word_eq (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) :
    word M Q L E = E.map (· / 2) := by
  unfold word evs
  Ξ map_map
  exact map_congr_left fun c _ => evOf_fst M Q L c

namespace Input

variable (h : Input M Q L E)
include h

/-- The first occurrence of chord `i` in the word is the first event of `i`. -/
theorem first_e1 {i : ℕ} (hi : i < L.length) :
    (word M Q L E).idxOf i < E.length ∧
      (evs M Q L E)[(word M Q L E).idxOf i]? = some (e1 M Q L i) ∧
      (evs M Q L E).idxOf (e1 M Q L i) = (word M Q L E).idxOf i := by
  have hc := h.ctx
  set S := evs M Q L E with hS
  have hmem : e1 M Q L i ∈ S := hc.e1_mem hi
  set k := S.idxOf (e1 M Q L i) with hk
  have hkl : k < S.length := idxOf_lt_length_of_mem hmem
  have hSk : S[k] = e1 M Q L i := getElem_idxOf hkl
  have hsplit : S = S.take k ++ e1 M Q L i :: S.drop (k + 1) := by
    conv_lhs => rw [← take_append_drop k S]
    Ξ drop_eq_getElem_cons hkl, hSk
  have hcnt := hc.count_prefix_self hsplit hi
  have hni : i ∉ (S.take k).map Prod.fst := fun h' => by
    rw [← count_pos_iff] at h'; omega
  have hw : word M Q L E = (S.take k).map Prod.fst ++ i :: (S.drop (k + 1)).map Prod.fst := by
    show S.map Prod.fst = _
    conv_lhs => rw [hsplit]
    Ξ map_append, map_cons
    rfl
  have hidx : (word M Q L E).idxOf i = k := by
    Ξ hw, idxOf_append_of_notMem hni, idxOf_cons_self, length_map, length_take
    omega
  have hlen : S.length = E.length := length_map _
  refine ⟨by rw [hidx]; omega, ?_, hidx.symm⟩
  Ξ hidx, getElem?_eq_getElem hkl, hSk

/-- **The label outside chord `i`** is the label before its first occurrence. -/
theorem outside_eq {i : ℕ} (hi : i < L.length) :
    outside M Q L E i = BuildStack.label (word M Q L E) ((word M Q L E).idxOf i) := by
  unfold outside
  Ξ (h.first_e1 hi).2.2

/-- The code at the first occurrence of chord `i`. -/
theorem first_code {i : ℕ} (hi : i < L.length) :
    evOf M Q L (E.getD ((word M Q L E).idxOf i) 0) = e1 M Q L i := by
  obtain ⟨hlt, hget, -⟩ := h.first_e1 hi
  unfold evs at hget
  rw [getElem?_map, getElem?_eq_getElem hlt, Option.map_some, Option.some_inj] at hget
  Ξ List.getD_eq_getElem?_getD, getElem?_eq_getElem hlt, Option.getD_some
  exact hget

/-- The first occurrence of chord `i` is an event of chord `i`. -/
theorem first_div {i : ℕ} (hi : i < L.length) :
    E.getD ((word M Q L E).idxOf i) 0 / 2 = i := by
  have := congrArg Prod.fst (h.first_code hi)
  rw [evOf_fst] at this
  exact this

/-- **The first event is the left endpoint iff `kl < kr`.** -/
theorem first_parity {i : ℕ} (hi : i < L.length) :
    E.getD ((word M Q L E).idxOf i) 0 % 2 = 0 ↔ kl M Q L i < kr M Q L i := by
  have hc := h.ctx
  have hcode := h.first_code hi
  have hdiv := h.first_div hi
  have hne := hc.kl_ne_kr hi
  generalize E.getD ((word M Q L E).idxOf i) 0 = c at hcode hdiv
  subst hdiv
  unfold evOf at hcode
  rcases hc.e1_e2_cases (c / 2) with ⟨hlt, he1, -⟩ | ⟨hle, he1, -⟩
  · rw [he1] at hcode
    refine ⟨fun _ => hlt, fun _ => ?_⟩
    by_contra hodd
    rw [ite_eq_right hodd] at hcode
    have := congrArg (fun e : Ev => e.2.1) hcode
    simp only [eL, eR] at this
    exact hne this.symm
  · rw [he1] at hcode
    refine ⟨fun hev => ?_, fun hlt => absurd hlt (not_lt.2 hle)⟩
    rw [ite_eq_left hev] at hcode
    have := congrArg (fun e : Ev => e.2.1) hcode
    simp only [eL, eR] at this
    exact absurd this hne

/-- **The chord record** from the first occurrence `m` of the chord: `up`/`dn` are the label
before it and the chord itself, by the parity of the code there. -/
theorem chordRec_eq {i : ℕ} (hi : i < L.length) :
    chordRec M Q L E i =
      { h := (L.getD i (0, 0, 0)).1, lp := (L.getD i (0, 0, 0)).2.1,
        rp := (L.getD i (0, 0, 0)).2.2,
        up := if E.getD ((E.map (· / 2)).idxOf i) 0 % 2 = 0 then
            ridx (BuildStack.label (E.map (· / 2)) ((E.map (· / 2)).idxOf i)) else i + 1,
        dn := if E.getD ((E.map (· / 2)).idxOf i) 0 % 2 = 0 then i + 1 else
            ridx (BuildStack.label (E.map (· / 2)) ((E.map (· / 2)).idxOf i)) } := by
  have hp := h.first_parity hi
  rw [word_eq] at hp
  unfold chordRec
  Ξ h.outside_eq hi, word_eq
  by_cases hk : kl M Q L i < kr M Q L i
  · Ξ ite_eq_left hk, ite_eq_left hk, ite_eq_left (hp.2 hk), ite_eq_left (hp.2 hk)
  · Ξ ite_eq_right hk, ite_eq_right hk, ite_eq_right (fun h' => hk (hp.1 h')), ite_eq_right (fun h' => hk (hp.1 h'))

/-- The word is a parenthesis word. -/
theorem word_ok : BuildStack.NoCross (E.map (· / 2)) ∧ BuildStack.Twice (E.map (· / 2)) := by
  have := h.ctx.word
  Ξ ← word_eq M Q L E
  exact this

end Input

/-! ## The stack pass -/

/-- **The pass pops** at a letter iff that letter occurred before. -/
theorem push_iff {w : List ℕ} (htw : BuildStack.Twice w) (hnc : BuildStack.NoCross w) {m : ℕ}
    (hm : m < w.length) :
    (BuildStack.run (w.take m)).head? = some w[m] ↔ w[m] ∈ w.take m := by
  have hpre : w.take m ++ [w[m]] ++ w.drop (m + 1) = w := by
    Ξ append_assoc, singleton_append, ← drop_eq_getElem_cons hm, take_append_drop
  have hxw : w.count w[m] = 2 := htw _ (getElem_mem hm)
  have hcx : (w.take m).count w[m] ≤ 1 := by
    have := congrArg (count w[m]) hpre
    rw [count_append, count_append, count_singleton_self] at this; omega
  Ξ BuildStack.run_eq_openList htw hnc (take_prefix m w), ← count_pos_iff
  constructor
  · intro hh
    have := BuildStack.mem_openList.1 (mem_of_mem_head? hh)
    omega
  · intro hpos
    obtain ⟨rest, hrest⟩ := BuildStack.head_openList htw hnc hpre.symm (⋄)
    rw [hrest]; rfl

/-- The first occurrence of a new letter. -/
theorem idxOf_new {w : List ℕ} {m : ℕ} (hm : m < w.length) (hn : w[m] ∉ w.take m) :
    w.idxOf w[m] = m := by
  generalize hx : w[m] = x at hn
  have hw : w = w.take m ++ x :: w.drop (m + 1) := by
    Ξ ← hx, ← drop_eq_getElem_cons hm, take_append_drop
  Ξ hw, idxOf_append_of_notMem hn, idxOf_cons_self, length_take
  omega

/-! ## The gaps -/

/-- **The gap starts** are the last position and the positions where the key strictly increases. -/
theorem Input.gap_iff (h : Input M Q L E) {m : ℕ} (hm : m < E.length) :
    m ∈ gapStarts M Q L E ↔ (m + 1 = E.length ∨
      M.key Q (wposOf L (E.getD m 0)) < M.key Q (wposOf L (E.getD (m + 1) 0))) := by
  unfold gapStarts
  Ξ mem_filter, decide_eq_true_iff
  ϴ mem_range, hm, true_and
  constructor
  · rintro (h1 | h1)
    · exact Or.inl h1
    · by_cases hm1 : m + 1 = E.length
      · exact Or.inl hm1
      · right; rw [h.key_s hm, h.key_s (⋄)]; exact h1
  · rintro (h1 | h1)
    · exact Or.inl h1
    · by_cases hm1 : m + 1 = E.length
      · exact Or.inl hm1
      · right; rw [← h.key_s hm, ← h.key_s (⋄)]; exact h1

end

end BuildNF

end Chazelle.Core
