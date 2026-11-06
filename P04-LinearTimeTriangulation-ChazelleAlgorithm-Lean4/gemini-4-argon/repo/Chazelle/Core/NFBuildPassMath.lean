module

public import Chazelle.Core.NFBuildArcW

/-!
# WP-C (BuildNF), RAM part 12: the state of the main pass, mathematically

* `stk E m`: the stack after the first `m` letters of the chord word, bottom first;
  `topR E m`: the region index of the label there (`topR_eq`: from the stack);
  `stk_pop`, `stk_push`: one step;
* `gapsUpTo E p m`: the gap starts below `m` (`gapsUpTo_succ`);
* `cf`, `af`: the five words of a chord record and of an arc record.
-/

namespace Chazelle.Core

namespace BuildNF

@[expose] public section

open List

/-- The chord word of the codes. -/
def cw (E : List ℕ) : List ℕ := E.map (· / 2)

/-- The stack after `m` letters, bottom first. -/
def stk (E : List ℕ) (m : ℕ) : List ℕ := (BuildStack.run ((cw E).take m)).reverse

/-- The region index of the label after `m` letters. -/
def topR (E : List ℕ) (m : ℕ) : ℕ := ridx (BuildStack.label (cw E) m)

theorem topR_eq (E : List ℕ) (m : ℕ) :
    topR E m = if (stk E m).length = 0 then 0 else (stk E m).getD ((stk E m).length - 1) 0 + 1 := by
  unfold topR stk BuildStack.label
  generalize BuildStack.run ((cw E).take m) = S
  rcases S with _ | ⟨y, S⟩
  · rfl
  · simp only [head?_cons, ridx, reverse_cons, length_append, length_reverse, length_cons,
      length_nil, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, Nat.add_sub_cancel]
    rw [getD_eq_getElem?_getD, getElem?_append_right (by simp), length_reverse, Nat.sub_self]
    rfl

theorem cw_getElem {E : List ℕ} {m : ℕ} (hm : m < E.length) :
    (cw E)[m]'(by simp [cw, hm]) = E.getD m 0 / 2 := by
  simp [cw, getD_eq_getElem?_getD, getElem?_eq_getElem hm]

theorem run_succ {E : List ℕ} {m : ℕ} (hm : m < E.length) :
    BuildStack.run ((cw E).take (m + 1)) =
      BuildStack.step (BuildStack.run ((cw E).take m)) (E.getD m 0 / 2) := by
  rw [take_add_one, getElem?_eq_getElem (by simp [cw, hm]), Option.toList_some,
    BuildStack.run_snoc, cw_getElem hm]

/-- A pop. -/
theorem stk_pop {E : List ℕ} {m : ℕ} (hm : m < E.length)
    (hh : (BuildStack.run ((cw E).take m)).head? = some (E.getD m 0 / 2)) :
    stk E (m + 1) = (stk E m).dropLast ∧ (stk E m).length = (stk E (m + 1)).length + 1 := by
  unfold stk
  rw [run_succ hm]
  unfold BuildStack.step
  rw [ite_eq_left hh]
  generalize BuildStack.run ((cw E).take m) = S at hh ⊢
  rcases S with _ | ⟨y, S⟩
  · simp at hh
  · simp [dropLast_append_of_ne_nil]

/-- A push. -/
theorem stk_push {E : List ℕ} {m : ℕ} (hm : m < E.length)
    (hh : ¬ (BuildStack.run ((cw E).take m)).head? = some (E.getD m 0 / 2)) :
    stk E (m + 1) = stk E m ++ [E.getD m 0 / 2] := by
  unfold stk
  rw [run_succ hm]
  unfold BuildStack.step
  rw [ite_eq_right hh, reverse_cons]

/-- The label is `x + 1` iff the stack top is `x`. -/
theorem topR_eq_succ_iff (E : List ℕ) (m x : ℕ) :
    topR E m = x + 1 ↔ (BuildStack.run ((cw E).take m)).head? = some x := by
  unfold topR BuildStack.label
  generalize (BuildStack.run ((cw E).take m)).head? = o
  cases o <;> simp [ridx]

/-- The gap predicate of `gapStarts`. -/
noncomputable def gapP (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) (m : ℕ) : Bool :=
  decide (m + 1 = E.length ∨ BuildSort.kap (evs M Q L E) m < BuildSort.kap (evs M Q L E) (m + 1))

/-- The gap starts below `m`. -/
noncomputable def gapsB (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) (m : ℕ) :
    List ℕ := (range m).filter (gapP M Q L E)

theorem gapsB_full (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) :
    gapsB M Q L E E.length = gapStarts M Q L E := rfl

theorem gapsB_succ (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) (m : ℕ) :
    gapsB M Q L E (m + 1) = gapsB M Q L E m ++ (if gapP M Q L E m then [m] else []) := by
  unfold gapsB
  rw [range_succ, filter_append]
  congr 1
  by_cases h : gapP M Q L E m <;> simp [h]

theorem gapsB_length_le (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) (m : ℕ) :
    (gapsB M Q L E m).length ≤ m := by
  unfold gapsB
  exact (length_filter_le _ _).trans (by simp)

/-- The gap predicate by keys. -/
theorem Input.gapP_iff {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}
    (h : Input M Q L E) {m : ℕ} (hm : m < E.length) :
    gapP M Q L E m = true ↔ (m + 1 = E.length ∨
      M.key Q (wposOf L (E.getD m 0)) < M.key Q (wposOf L (E.getD ((m + 1) % E.length) 0))) := by
  unfold gapP
  rw [decide_eq_true_iff]
  by_cases h1 : m + 1 = E.length
  · simp [h1]
  · rw [Nat.mod_eq_of_lt (by omega), h.key_s hm, h.key_s (by omega)]

/-- The word `f` of a chord record. -/
def cf (r : CRec) (f : ℕ) : ℕ :=
  if f = 0 then r.h else if f = 1 then r.lp else if f = 2 then r.rp else if f = 3 then r.up
  else r.dn

/-- The word `f` of an arc record. -/
def af (a : ARec) (f : ℕ) : ℕ :=
  if f = 0 then a.reg else if f = 1 then a.s.edge else if f = 2 then a.s.hgt
  else if f = 3 then a.e.edge else a.e.hgt

theorem take_succ_cw {E : List ℕ} {m : ℕ} (hm : m < E.length) :
    (cw E).take (m + 1) = (cw E).take m ++ [E.getD m 0 / 2] := by
  rw [take_add_one, getElem?_eq_getElem (by simp [cw, hm]), Option.toList_some, cw_getElem hm]

/-- **The pass pops** at `m` iff the chord occurred before. -/
theorem Input.pop_iff {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}
    (h : Input M Q L E) {m : ℕ} (hm : m < E.length) :
    topR E m = E.getD m 0 / 2 + 1 ↔ E.getD m 0 / 2 ∈ (cw E).take m := by
  rw [topR_eq_succ_iff]
  obtain ⟨hnc, htw⟩ := h.word_ok
  have := push_iff (w := cw E) htw hnc (m := m) (by simp [cw, hm])
  rwa [cw_getElem hm] at this

/-- **The chord record written at the first occurrence** `m` of a chord. -/
theorem Input.chordRec_new {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}
    (h : Input M Q L E) {m : ℕ} (hm : m < E.length) (hx : E.getD m 0 / 2 < L.length)
    (hn : E.getD m 0 / 2 ∉ (cw E).take m) :
    chordRec M Q L E (E.getD m 0 / 2) =
      { h := (L.getD (E.getD m 0 / 2) (0, 0, 0)).1, lp := (L.getD (E.getD m 0 / 2) (0, 0, 0)).2.1,
        rp := (L.getD (E.getD m 0 / 2) (0, 0, 0)).2.2,
        up := if E.getD m 0 % 2 < 1 then topR E m else E.getD m 0 / 2 + 1,
        dn := if E.getD m 0 % 2 < 1 then E.getD m 0 / 2 + 1 else topR E m } := by
  have hidx : (E.map (· / 2)).idxOf (E.getD m 0 / 2) = m := by
    have := idxOf_new (w := cw E) (m := m) (by simp [cw, hm]) (by rwa [cw_getElem hm])
    rwa [cw_getElem hm] at this
  rw [h.chordRec_eq hx, hidx]
  unfold topR cw
  by_cases hp : E.getD m 0 % 2 = 0
  · rw [ite_eq_left hp, ite_eq_left hp, ite_eq_left (by omega), ite_eq_left (by omega)]
  · rw [ite_eq_right hp, ite_eq_right hp, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The arc record of a gap start. -/
theorem arcRec_eq (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) (m : ℕ) :
    arcRec M Q L E m =
      { reg := topR E (m + 1), s := wposOf L (E.getD m 0),
        e := wposOf L (E.getD ((m + 1) % E.length) 0) } := by
  unfold arcRec topR
  rw [word_eq]
  rfl

theorem cf_mk (h lp rp up dn f : ℕ) :
    cf ⟨h, lp, rp, up, dn⟩ f = if f = 0 then h else if f = 1 then lp else if f = 2 then rp
      else if f = 3 then up else dn := rfl

theorem af_mk (reg : ℕ) (s e : WPos) (f : ℕ) :
    af ⟨reg, s, e⟩ f = if f = 0 then reg else if f = 1 then s.edge else if f = 2 then s.hgt
      else if f = 3 then e.edge else e.hgt := rfl

end

end BuildNF

end Chazelle.Core
