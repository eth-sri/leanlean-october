module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.NFBuildCmp

/-!
# Down-phase driver, S-M1 and S-M2: arcs as gaps of the event list, and splicing

* **S-M1** (`buildNF_arc`): for `K > 0`, arc `j` of `buildNF M Q L E` is the gap of `E` after
  the event at index `gapStarts j` (from the event `E[m]` to the event `E[m + 1]`), and the arcs
  are listed in the order of `E` (`seq = range`).
* **S-M2** (`splice_ok`): appending chords `L₂` to `L` and merging (by the comparator `codeLe`) a
  sorted list `E₂` of the new event codes `2|L| …` into the sorted list `E` gives a sorted
  permutation of all event codes of `L ++ L₂`, a valid input of `BuildNFSortedSpec`.  The old codes
  name the same walk positions in `L ++ L₂` (`wposOf_append`).

Design: `docs/design-downphase-driver.md` §4.2 (g).
-/

namespace Chazelle.Core

namespace DownDrv

@[expose] public section

open BuildNF (codeLe wposOf tieBit buildNF gapStarts arcRec arcList)

variable {M : Model} {Q : Polygon} {L L₂ : List (ℕ × ℕ × ℕ)} {E E₂ : List ℕ}

/-! ## S-M1 -/

section
variable (hK : 0 < L.length)
include hK
/-- **The arcs of `buildNF` are the gaps of the event list, in order.** -/
theorem buildNF_arcs :
    (buildNF M Q L E).arcs = (gapStarts M Q L E).map (arcRec M Q L E) := by
  show arcList M Q L E = _
  grind [arcList]

/-- Arc `j` runs from the event at `gapStarts j` to the next event. -/
theorem buildNF_arc {j : ℕ} (hj : j < (gapStarts M Q L E).length) :
    (buildNF M Q L E).arcs.getD j ⟨0, ⟨0, 0⟩, ⟨0, 0⟩⟩ =
      { reg := (arcRec M Q L E ((gapStarts M Q L E).getD j 0)).reg,
        s := wposOf L (E.getD ((gapStarts M Q L E).getD j 0) 0),
        e := wposOf L (E.getD (((gapStarts M Q L E).getD j 0 + 1) % E.length) 0) } := by
  rw [buildNF_arcs hK, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some,
    show (gapStarts M Q L E)[j] = (gapStarts M Q L E).getD j 0 by
      simp_all]
  rfl


end

/-- The arc sequence of `buildNF` is the identity order. -/
theorem buildNF_seq : (buildNF M Q L E).seq = List.range (buildNF M Q L E).arcs.length := rfl

/-! ## S-M2 -/

section
variable {c : ℕ} (hc : c < 2 * L.length)
include hc

/-- **Old event codes name the same walk positions after appending chords.** -/
theorem wposOf_append : wposOf (L ++ L₂) c = wposOf L c := by
  grind [wposOf, BuildRegions.crec]

theorem tieBit_append : tieBit M (L ++ L₂) c = tieBit M L c := by
  unfold tieBit
  rw [wposOf_append hc]


end

theorem codeLe_append {c c' : ℕ} (hc : c < 2 * L.length) (hc' : c' < 2 * L.length) :
    codeLe M Q (L ++ L₂) c c' ↔ codeLe M Q L c c' := by
  unfold codeLe
  rw [wposOf_append hc, wposOf_append hc', tieBit_append hc, tieBit_append hc']

open Classical in
/-- The comparator as a Boolean function. -/
noncomputable def codeLeB (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (a b : ℕ) : Bool :=
  decide (codeLe M Q L a b)

theorem codeLeB_iff (a b : ℕ) : codeLeB M Q L a b = true ↔ codeLe M Q L a b := by
  unfold codeLeB; simp

/-- **The spliced event list.** -/
noncomputable def splice (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E E₂ : List ℕ) :
    List ℕ :=
  List.merge E E₂ (codeLeB M Q L)

/-- **S-M2: splicing gives a valid sorted event list for the extended chord list.** -/
theorem splice_ok (hperm : E.Perm (List.range (2 * L.length)))
    (hsort : E.Pairwise (codeLe M Q L))
    (hperm₂ : E₂.Perm ((List.range (2 * L₂.length)).map (2 * L.length + ·)))
    (hsort₂ : E₂.Pairwise (codeLe M Q (L ++ L₂))) :
    (splice M Q (L ++ L₂) E E₂).Perm (List.range (2 * (L ++ L₂).length)) ∧
      (splice M Q (L ++ L₂) E E₂).Pairwise (codeLe M Q (L ++ L₂)) := by
  constructor
  · unfold splice
    refine (List.merge_perm_append (le := codeLeB M Q (L ++ L₂))).trans ?_
    rw [List.length_append, Nat.mul_add, List.range_add]
    grind
  · have hE : E.Pairwise (fun a b => codeLeB M Q (L ++ L₂) a b = true) := by
      refine hsort.imp_of_mem fun {a b} ha hb hab => ?_
      have ha' := List.mem_range.1 (hperm.mem_iff.1 ha)
      have hb' := List.mem_range.1 (hperm.mem_iff.1 hb)
      rw [codeLeB_iff, codeLe_append ha' hb']
      exact hab
    have hE₂ : E₂.Pairwise (fun a b => codeLeB M Q (L ++ L₂) a b = true) :=
      hsort₂.imp fun h => (codeLeB_iff _ _).2 h
    have h := List.pairwise_merge (le := codeLeB M Q (L ++ L₂))
      (fun a b c h1 h2 => by
        rw [codeLeB_iff] at h1 h2 ⊢
        core_grind)
      (fun a b => by
        rcases BuildNF.codeLe_total M Q (L ++ L₂) a b with h | h
        · rw [(codeLeB_iff a b).2 h]; rfl
        · rw [(codeLeB_iff b a).2 h, Bool.or_true])
      E E₂ hE hE₂
    unfold splice
    exact h.imp fun h' => (codeLeB_iff _ _).1 h'

end

end DownDrv

end Chazelle.Core
