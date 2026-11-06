module

public import Chazelle.Core.RestoreTHoleRam

/-!
# WP-E, the candidate test on the RAM: the holes of a chain model

`chainH` computes the holes of the candidate `x = (e, h)` (registers `83005`, `83006`) in a chain
model from the chain descriptor at `83020` (`C.m`, the top index, the orientation bit), into
`84009 … 84015`:

* inside a tour edge (`h > 0`): the edge `e` and its twin `tourTwin C (e - 6) + 6`;
* at a tour vertex (`h = 0`) of the chain vertex `k`: the vertex holes of the candidates
  `candIdx k + 6`, `candIdx (2m - k) + 6`, and of `2m + 6` if `k` is the top.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim SignK
open Chazelle.Chain (sideE)

variable {P : Polygon} {W : ℕ} {c : Config}

/-- The descriptor words and the tour step `i = e - 6`. -/
def chainPre : Stmt := block [.constN 83096 2, .addN 83095 83020 83096, .loadN 83097 83095,
  .addN 83095 83095 83023, .loadN 83098 83095, .addN 83095 83095 83023, .loadN 83099 83095,
  .addN 83100 83097 83097, .constN 83101 7, .addN 83090 83100 83101, .constN 83103 6,
  .subN 83104 83005 83103]

/-- The start `S` of the tour (`sideS`). -/
def sS : Stmt := .ifLtN 83099 83023 (.instr (.subN 83102 83100 83098))
  (.ifLtN 83023 83099 (.instr (.subN 83102 83100 83098)) (.instr (.copyN 83102 83098)))

/-- The tour position `j = (S + i) mod 2m` (without sums above `2m`). -/
def jS : Stmt := .seq (.instr (.subN 83105 83100 83102))
  (.ifLtN 83104 83105 (.instr (.addN 83106 83102 83104))
    (.seq (.instr (.subN 83106 83104 83105)) (condSub 83106 83106 83100)))

/-- The holes of a point inside a tour edge. -/
def edgeH : Stmt := .seq (.instr (.subN 83107 83100 83023)) (.seq (.instr (.subN 83107 83107 83106))
  (.seq (candS 83108 83107 83102 83100) (.seq (.instr (.constN 84009 2))
    (.seq (.instr (.copyN 84010 83005)) (.seq (.instr (.addN 84011 83005 83023))
      (.seq (.instr (.addN 84012 83108 83103)) (.instr (.addN 84013 84012 83023))))))))

/-- The third hole, at the last tour vertex, for the top. -/
def topH : Stmt := .ifLtN 83109 83098 .skip (.ifLtN 83098 83109 .skip
  (.seq (.instr (.constN 84009 3)) (.seq (.instr (.addN 84014 83100 83101))
    (.seq (.instr (.subN 84014 84014 83096)) (.instr (.constN 84015 0))))))

/-- The holes of a chain vertex. -/
def vtxH : Stmt :=
  .seq (.ifLtN 83097 83106 (.instr (.subN 83109 83100 83106)) (.instr (.copyN 83109 83106)))
  (.seq (candS 83110 83109 83102 83100) (.seq (.instr (.subN 83111 83100 83109))
  (.seq (candS 83112 83111 83102 83100) (.seq (.instr (.addN 83113 83110 83103))
  (.seq (.instr (.addN 83114 83112 83103)) (.seq (.instr (.constN 84009 2))
  (.seq (.instr (.subN 84010 83113 83023)) (.seq (.instr (.addN 84011 83113 83023))
  (.seq (nxtS 84011 83090) (.seq (.instr (.subN 84012 83114 83023))
  (.seq (.instr (.addN 84013 83114 83023)) (.seq (nxtS 84013 83090) topH))))))))))))

/-- **The holes of the candidate in a chain model.** -/
def chainH : Stmt := .seq chainPre (.seq sS (.seq jS (.ifLtN 83022 83006 edgeH vtxH)))

/-- The scratch registers of `chainH`. -/
def chainHL : List ℕ := [83090, 83095, 83096, 83097, 83098, 83099, 83100, 83101, 83102, 83103,
  83104, 83105, 83106, 83107, 83108, 83109, 83110, 83111, 83112, 83113, 83114, 84009, 84010,
  84011, 84012, 84013, 84014, 84015]

/-- The start of the tour from the descriptor words. -/
def sOf (m top bit : ℕ) : ℕ := if bit = 1 then top else 2 * m - top

theorem chainPre_exec (hw : WordsBounded W c) {B m top bit : ℕ} (hB : c.nreg 83020 = B)
    (h23 : c.nreg 83023 = 1) (hm : c.nmem (B + 2) = m) (ht : c.nmem (B + 3) = top)
    (hb : c.nmem (B + 4) = bit) (hBW : B + 4 ≤ W) (hmW : 2 * m + 7 ≤ W) :
    ∃ c', ∃ k ≤ 12, Exec P W chainPre c c' k ∧ c'.nreg 83097 = m ∧ c'.nreg 83098 = top ∧
      c'.nreg 83099 = bit ∧ c'.nreg 83100 = 2 * m ∧ c'.nreg 83101 = 7 ∧
      c'.nreg 83090 = 2 * m + 7 ∧ c'.nreg 83096 = 2 ∧ c'.nreg 83103 = 6 ∧
      c'.nreg 83104 = c.nreg 83005 - 6 ∧ Out c c' chainHL := by
  unfold chainPre
  have hB' := hB
  obtain ⟨c', k, ex, hk, q97, q98, q99, q100, q101, q90, q96, q103, q104, hr, rr, mm, rm, oo⟩ :
      ∃ c' k, Exec P W (block [.constN 83096 2, .addN 83095 83020 83096, .loadN 83097 83095,
        .addN 83095 83095 83023, .loadN 83098 83095, .addN 83095 83095 83023,
        .loadN 83099 83095, .addN 83100 83097 83097, .constN 83101 7,
        .addN 83090 83100 83101, .constN 83103 6, .subN 83104 83005 83103]) c c' k ∧ k = 12 ∧
        c'.nreg 83097 = m ∧ c'.nreg 83098 = top ∧ c'.nreg 83099 = bit ∧
        c'.nreg 83100 = 2 * m ∧ c'.nreg 83101 = 7 ∧ c'.nreg 83090 = 2 * m + 7 ∧
        c'.nreg 83096 = 2 ∧ c'.nreg 83103 = 6 ∧ c'.nreg 83104 = c.nreg 83005 - 6 ∧
        (∀ r, r ∉ chainHL → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
        c'.rmem = c.rmem ∧ c'.output = c.output := by
    have ht' := ht
    have hb' : c.nmem (B + 3 + 1) = bit := by rw [show B + 3 + 1 = B + 4 by omega]; exact hb
    exec_block
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hB', h23]; omega)
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hB', h23, hm, ht', hb']
    · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hB', h23, hm, ht', hb']
    · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hB', h23, hm, ht', hb']
    · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hB', h23, hm, ht', hb']; ring
    · simp (disch := omega) only [Machine.upd_same, Machine.upd_other]
    · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hB', h23, hm, ht', hb']; ring
    · simp (disch := omega) only [Machine.upd_same, Machine.upd_other]
    · simp (disch := omega) only [Machine.upd_same, Machine.upd_other]
    · simp (disch := omega) only [Machine.upd_same]
    · ϴ' chainHL, List.mem_cons, List.not_mem_nil, or_false, not_or at hr
      simp (disch := omega) only [Machine.upd_other]
  exact ⟨c', k, ⋄, ex, q97, q98, q99, q100, q101, q90, q96, q103, q104,
    ⟨hr, rr, mm, rm, oo⟩⟩

theorem sS_exec (hw : WordsBounded W c) {m top bit : ℕ} (h99 : c.nreg 83099 = bit)
    (h100 : c.nreg 83100 = 2 * m) (h98 : c.nreg 83098 = top) (h23 : c.nreg 83023 = 1) :
    ∃ c', ∃ k ≤ 5, Exec P W sS c c' k ∧ c'.nreg 83102 = sOf m top bit ∧ Out c c' [83102] := by
  unfold sS sOf
  by_cases g1 : c.nreg 83099 < c.nreg 83023
  · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.subN hw 83102 83100 83098)
    refine ⟨c', _, ⋄, .ifLtN_true g1 e, ?_, o⟩
    Ξ v, h100, h98, ite_eq_right (⋄)
  by_cases g2 : c.nreg 83023 < c.nreg 83099
  · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.subN hw 83102 83100 83098)
    refine ⟨c', _, ⋄, .ifLtN_false g1 (.ifLtN_true g2 e), ?_, o⟩
    Ξ v, h100, h98, ite_eq_right (⋄)
  · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.copyN hw 83102 83098)
    refine ⟨c', _, ⋄, .ifLtN_false g1 (.ifLtN_false g2 e), ?_, o⟩
    Ξ v, h98, ite_eq_left (⋄)

theorem jS_exec (hw : WordsBounded W c) {m S i : ℕ} (_hm : 0 < m) (h102 : c.nreg 83102 = S)
    (h104 : c.nreg 83104 = i) (h100 : c.nreg 83100 = 2 * m) (hS : S ≤ 2 * m) (hi : i ≤ 2 * m)
    (hW : 2 * m ≤ W) :
    ∃ c', ∃ k ≤ 8, Exec P W jS c c' k ∧ c'.nreg 83106 = (S + i) % (2 * m) ∧
      Out c c' [83105, 83106] := by
  obtain ⟨c₁, e₁, v₁, o₁⟩ := out_instr (P := P) (Exec.subN hw 83105 83100 83102)
  have g : ∀ r, r ≠ 83105 → c₁.nreg r = c.nreg r := fun r hr => o₁.1 r (⊚ hr)
  have u : c₁.nreg 83105 = 2 * m - S := Ρ v₁, h100, h102
  by_cases hlt : c₁.nreg 83104 < c₁.nreg 83105
  · Ξ' g _ (⋄), h104, u at hlt
    obtain ⟨c₂, e₂, v₂, o₂⟩ := out_instr (P := P) (Exec.addN e₁.wb_right 83106 83102 83104
      (by rw [g _ (⋄), g _ (⋄), h102, h104]; omega))
    refine ⟨c₂, _, ⋄, .seq e₁ (.ifLtN_true (by rw [g _ (⋄), h104, u]; exact hlt) e₂),
      ?_, (o₁.trans o₂).mono (✓)⟩
    Ξ v₂, g _ (⋄), g _ (⋄), h102, h104, Nat.mod_eq_of_lt (⋄)
  · Ξ' g _ (⋄), h104, u at hlt
    obtain ⟨c₂, e₂, v₂, o₂⟩ := out_instr (P := P) (Exec.subN e₁.wb_right 83106 83104 83105)
    obtain ⟨c₃, k₃, hk₃, e₃, v₃, o₃⟩ := condSub_exec (P := P) e₂.wb_right 83106 83106 83100
    refine ⟨c₃, _, ⋄, .seq e₁ (.ifLtN_false (by rw [g _ (⋄), h104, u]; exact hlt)
      (.seq e₂ e₃)), ?_, ((o₁.trans o₂).trans o₃).mono (✓)⟩
    have w6 : c₂.nreg 83106 = S + i - 2 * m := by
      rw [v₂, g _ (⋄), h104, u]; omega
    have w100 : c₂.nreg 83100 = 2 * m := Ρ o₂.1 _ (✓), g _ (⋄), h100
    Ξ v₃, w6, w100
    by_cases h2 : S + i - 2 * m < 2 * m
    · Ξ ite_eq_left h2, Nat.mod_eq_sub_mod (⋄), Nat.mod_eq_of_lt h2
    · Ξ ite_eq_right h2, show S + i = 2 * m + 2 * m by omega, Nat.add_mod_right, Nat.mod_self
      omega

theorem edgeH_exec (hw : WordsBounded W c) {m S j e : ℕ} (h100 : c.nreg 83100 = 2 * m)
    (h106 : c.nreg 83106 = j) (h102 : c.nreg 83102 = S) (h103 : c.nreg 83103 = 6)
    (h23 : c.nreg 83023 = 1) (h05 : c.nreg 83005 = e) (hj : j < 2 * m) (hS : S ≤ 2 * m)
    (heW : e + 1 ≤ W) (hmW : 2 * m + 7 ≤ W) :
    ∃ c', ∃ k ≤ 12, Exec P W edgeH c c' k ∧ c'.nreg 84009 = 2 ∧ c'.nreg 84010 = e ∧
      c'.nreg 84011 = e + 1 ∧ c'.nreg 84012 = candIdx m S (2 * m - 1 - j) + 6 ∧
      c'.nreg 84013 = candIdx m S (2 * m - 1 - j) + 7 ∧
      Out c c' [83107, 83108, 84009, 84010, 84011, 84012, 84013] := by
  obtain ⟨c₁, e₁, v₁, o₁⟩ := out_instr (P := P) (Exec.subN hw 83107 83100 83023)
  obtain ⟨c₂, e₂, v₂, o₂⟩ := out_instr (P := P) (Exec.subN e₁.wb_right 83107 83107 83106)
  have g : ∀ r, r ≠ 83107 → c₂.nreg r = c.nreg r := fun r hr => by
    Ξ o₂.1 r (by simp [hr]), o₁.1 r (by simp [hr])
  have q107 : c₂.nreg 83107 = 2 * m - 1 - j := by
    Ξ v₂, v₁, o₁.1 _ (✓), h100, h23, h106
  obtain ⟨c₃, k₃, hk₃, e₃, v₃, o₃⟩ := candS_exec (P := P) e₂.wb_right (dst := 83108) (jr := 83107)
    (sr := 83102) (mr := 83100) (⋄) (⋄) (⋄) q107
    (Ρ g _ (⋄), h102) (Ρ g _ (⋄), h100) hS (⋄) (⋄)
  have g3 : ∀ r, r ≠ 83107 → r ≠ 83108 → c₃.nreg r = c.nreg r := fun r h1 h2 => by
    Ξ o₃.1 r (by simp [h2]), g r h1
  obtain ⟨c₄, e₄, v₄, o₄⟩ := out_instr (P := P) (Exec.constN e₃.wb_right 84009 2 (⋄))
  obtain ⟨c₅, e₅, v₅, o₅⟩ := out_instr (P := P) (Exec.copyN e₄.wb_right 84010 83005)
  obtain ⟨c₆, e₆, v₆, o₆⟩ := out_instr (P := P) (Exec.addN e₅.wb_right 84011 83005 83023
    (by rw [o₅.1 _ (✓), o₄.1 _ (✓), o₅.1 _ (✓), o₄.1 _ (✓),
      g3 _ (⋄) (⋄), g3 _ (⋄) (⋄), h05, h23]; exact heW))
  have c1 : ∀ r, r ≠ 84009 → r ≠ 84010 → r ≠ 84011 → c₆.nreg r = c₃.nreg r := fun r a b d => by
    Ξ o₆.1 r (by simp [d]), o₅.1 r (by simp [b]), o₄.1 r (by simp [a])
  have hc : candIdx m S (2 * m - 1 - j) ≤ 2 * m := by unfold candIdx; split_ifs <;> omega
  have a108 : c₆.nreg 83108 = candIdx m S (2 * m - 1 - j) := by
    Ξ c1 _ (⋄) (⋄) (⋄), v₃
  have a103 : c₆.nreg 83103 = 6 := by rw [c1 _ (⋄) (⋄) (⋄),
    g3 _ (⋄) (⋄), h103]
  have a23 : c₆.nreg 83023 = 1 := by rw [c1 _ (⋄) (⋄) (⋄),
    g3 _ (⋄) (⋄), h23]
  obtain ⟨c₇, e₇, v₇, o₇⟩ := out_instr (P := P) (Exec.addN e₆.wb_right 84012 83108 83103
    (by rw [a108, a103]; omega))
  have b12 : c₇.nreg 84012 = candIdx m S (2 * m - 1 - j) + 6 := Ρ v₇, a108, a103
  have b23 : c₇.nreg 83023 = 1 := Ρ o₇.1 _ (✓), a23
  obtain ⟨c₈, e₈, v₈, o₈⟩ := out_instr (P := P) (Exec.addN e₇.wb_right 84013 84012 83023
    (by rw [b12, b23]; omega))
  have ex : Exec P W edgeH c c₈ _ :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈))))))
  have a05 : c₄.nreg 83005 = e := Ρ o₄.1 _ (✓), g3 _ (⋄) (⋄), h05
  have a23' : c₅.nreg 83023 = 1 := by rw [o₅.1 _ (✓), o₄.1 _ (✓),
    g3 _ (⋄) (⋄), h23]
  have a05' : c₅.nreg 83005 = e := Ρ o₅.1 _ (✓), a05
  refine ⟨c₈, _, ⋄, ex, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · Ξ o₈.1 _ (✓), o₇.1 _ (✓), o₆.1 _ (✓), o₅.1 _ (✓), v₄
  · Ξ o₈.1 _ (✓), o₇.1 _ (✓), o₆.1 _ (✓), v₅, a05
  · Ξ o₈.1 _ (✓), o₇.1 _ (✓), v₆, a05', a23'
  · Ξ o₈.1 _ (✓), b12
  · Ξ v₈, b12, b23
  · exact (((((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).trans o₆).trans o₇).trans o₈).mono
      (by intro r hr; ϴ' List.mem_append, List.mem_cons, List.not_mem_nil, or_false at hr
          simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)

theorem candIdx_le {m S j : ℕ} (hS : S ≤ 2 * m) (hj : j ≤ 2 * m) : candIdx m S j ≤ 2 * m := by
  unfold candIdx; split_ifs <;> omega

theorem vtxH_exec (hw : WordsBounded W c) {m top S j : ℕ} (h97 : c.nreg 83097 = m)
    (h98 : c.nreg 83098 = top) (h100 : c.nreg 83100 = 2 * m) (h101 : c.nreg 83101 = 7)
    (h96 : c.nreg 83096 = 2) (h90 : c.nreg 83090 = 2 * m + 7) (h103 : c.nreg 83103 = 6)
    (h102 : c.nreg 83102 = S) (h106 : c.nreg 83106 = j) (h23 : c.nreg 83023 = 1)
    (hS : S ≤ 2 * m) (hj : j < 2 * m) (hmW : 2 * m + 7 ≤ W) :
    ∃ c', ∃ k ≤ 60, Exec P W vtxH c c' k ∧
      c'.nreg 84009 = (if sideE m j = top then 3 else 2) ∧
      c'.nreg 84010 = candIdx m S (sideE m j) + 5 ∧
      c'.nreg 84011 = (candIdx m S (sideE m j) + 7) % (2 * m + 7) ∧
      c'.nreg 84012 = candIdx m S (2 * m - sideE m j) + 5 ∧
      c'.nreg 84013 = (candIdx m S (2 * m - sideE m j) + 7) % (2 * m + 7) ∧
      (sideE m j = top → c'.nreg 84014 = 2 * m + 5 ∧ c'.nreg 84015 = 0) ∧
      Out c c' chainHL := by
  set k := sideE m j with hkd
  have hkm : k ≤ m := by rw [hkd]; unfold sideE; split_ifs <;> omega
  -- the chain vertex
  obtain ⟨c₁, k₁, hk₁, e₁, v₁, o₁⟩ : ∃ c₁, ∃ k₁ ≤ 3, Exec P W (.ifLtN 83097 83106
      (.instr (.subN 83109 83100 83106)) (.instr (.copyN 83109 83106))) c c₁ k₁ ∧
      c₁.nreg 83109 = k ∧ Out c c₁ [83109] := by
    by_cases g : c.nreg 83097 < c.nreg 83106
    · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.subN hw 83109 83100 83106)
      refine ⟨c', _, by omega, .ifLtN_true g e, ?_, o⟩
      rw [v, h100, h106]; rw [h97, h106] at g
      rw [hkd]; unfold sideE; rw [ite_eq_right (by omega)]
    · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.copyN hw 83109 83106)
      refine ⟨c', _, by omega, .ifLtN_false g e, ?_, o⟩
      rw [v, h106]; rw [h97, h106] at g
      rw [hkd]; unfold sideE; rw [ite_eq_left (by omega)]
  have i1 : ∀ r, r ≠ 83109 → c₁.nreg r = c.nreg r := fun r hr => o₁.1 r (by simp [hr])
  obtain ⟨c₂, k₂, hk₂, e₂, v₂, o₂⟩ := candS_exec (P := P) e₁.wb_right (dst := 83110)
    (jr := 83109) (sr := 83102) (mr := 83100) (by omega) (by omega) (by omega) v₁
    (by rw [i1 _ (by omega), h102]) (by rw [i1 _ (by omega), h100]) hS (by omega) (by omega)
  have o12 := o₁.trans o₂
  obtain ⟨c₃, e₃, v₃, o₃⟩ := out_instr (P := P) (Exec.subN e₂.wb_right 83111 83100 83109)
  have q111 : c₃.nreg 83111 = 2 * m - k := by
    rw [v₃, o12.1 _ (by simp), h100, o₂.1 _ (by simp), v₁]
  have o13 := o12.trans o₃
  obtain ⟨c₄, k₄, hk₄, e₄, v₄, o₄⟩ := candS_exec (P := P) e₃.wb_right (dst := 83112)
    (jr := 83111) (sr := 83102) (mr := 83100) (by omega) (by omega) (by omega) q111
    (by rw [o13.1 _ (by simp), h102]) (by rw [o13.1 _ (by simp), h100]) hS (by omega) (by omega)
  have o14 := o13.trans o₄
  have c1le := candIdx_le (m := m) (j := k) hS (by omega)
  have c2le := candIdx_le (m := m) (j := 2 * m - k) hS (by omega)
  have a110 : c₄.nreg 83110 = candIdx m S k := by rw [o₄.1 _ (by simp), o₃.1 _ (by simp), v₂]
  obtain ⟨c₅, e₅, v₅, o₅⟩ := out_instr (P := P) (Exec.addN e₄.wb_right 83113 83110 83103
    (by rw [a110, o14.1 _ (by simp), h103]; omega))
  have o15 := o14.trans o₅
  have a112 : c₅.nreg 83112 = candIdx m S (2 * m - k) := by rw [o₅.1 _ (by simp), v₄]
  obtain ⟨c₆, e₆, v₆, o₆⟩ := out_instr (P := P) (Exec.addN e₅.wb_right 83114 83112 83103
    (by rw [a112, o15.1 _ (by simp), h103]; omega))
  have o16 := o15.trans o₆
  have q113 : c₆.nreg 83113 = candIdx m S k + 6 := by
    rw [o₆.1 _ (by simp), v₅, a110, o14.1 _ (by simp), h103]
  have q114 : c₆.nreg 83114 = candIdx m S (2 * m - k) + 6 := by
    rw [v₆, a112, o15.1 _ (by simp), h103]
  obtain ⟨c₇, e₇, v₇, o₇⟩ := out_instr (P := P) (Exec.constN e₆.wb_right 84009 2 (by omega))
  obtain ⟨c₈, e₈, v₈, o₈⟩ := out_instr (P := P) (Exec.subN e₇.wb_right 84010 83113 83023)
  have o18 := (o16.trans o₇).trans o₈
  obtain ⟨c₉, e₉, v₉, o₉⟩ := out_instr (P := P) (Exec.addN e₈.wb_right 84011 83113 83023
    (by rw [o₈.1 _ (by simp), o₇.1 _ (by simp), q113, o18.1 _ (by simp), h23]; omega))
  obtain ⟨c₁₀, k₁₀, hk₁₀, e₁₀, v₁₀, o₁₀⟩ := nxtS_exec (P := P) e₉.wb_right 84011 83090
  have o110 := (o18.trans o₉).trans o₁₀
  have g113 : c₉.nreg 83113 = candIdx m S k + 6 := by
    rw [o₉.1 _ (by simp), o₈.1 _ (by simp), o₇.1 _ (by simp), q113]
  have g23 : ∀ {cc : Config} {L : List ℕ}, Out c cc L → 83023 ∉ L → cc.nreg 83023 = 1 :=
    fun o h => by rw [o.1 _ h, h23]
  obtain ⟨c₁₁, e₁₁, v₁₁, o₁₁⟩ := out_instr (P := P) (Exec.subN e₁₀.wb_right 84012 83114 83023)
  obtain ⟨c₁₂, e₁₂, v₁₂, o₁₂⟩ := out_instr (P := P) (Exec.addN e₁₁.wb_right 84013 83114 83023
    (by rw [o₁₁.1 _ (by simp), o₁₀.1 _ (by simp), o₉.1 _ (by simp), o₈.1 _ (by simp),
      o₇.1 _ (by simp), q114, g23 (o110.trans o₁₁) (by simp)]; omega))
  obtain ⟨c₁₃, k₁₃, hk₁₃, e₁₃, v₁₃, o₁₃⟩ := nxtS_exec (P := P) e₁₂.wb_right 84013 83090
  have o113 := ((o110.trans o₁₁).trans o₁₂).trans o₁₃
  have g114 : c₁₀.nreg 83114 = candIdx m S (2 * m - k) + 6 := by
    rw [o₁₀.1 _ (by simp), o₉.1 _ (by simp), o₈.1 _ (by simp), o₇.1 _ (by simp), q114]
  -- the values of the two vertex holes
  have a9_11 : c₉.nreg 84011 = candIdx m S k + 7 := by
    rw [v₉, o₈.1 _ (by simp), o₇.1 _ (by simp), q113, g23 o18 (by simp)]
  have a9_90 : c₉.nreg 83090 = 2 * m + 7 := by rw [(o18.trans o₉).1 _ (by simp), h90]
  have a12_13 : c₁₂.nreg 84013 = candIdx m S (2 * m - k) + 7 := by
    rw [v₁₂, o₁₁.1 _ (by simp), g114, g23 (o110.trans o₁₁) (by simp)]
  have a12_90 : c₁₂.nreg 83090 = 2 * m + 7 := by
    rw [((o110.trans o₁₁).trans o₁₂).1 _ (by simp), h90]
  have w10 : c₁₃.nreg 84010 = candIdx m S k + 5 := by
    rw [o₁₃.1 _ (by simp), o₁₂.1 _ (by simp), o₁₁.1 _ (by simp), o₁₀.1 _ (by simp),
      o₉.1 _ (by simp), v₈, o₇.1 _ (by simp), q113, g23 (o16.trans o₇) (by simp)]; omega
  have w11 : c₁₃.nreg 84011 = (candIdx m S k + 7) % (2 * m + 7) := by
    rw [o₁₃.1 _ (by simp), o₁₂.1 _ (by simp), o₁₁.1 _ (by simp), v₁₀, a9_11, a9_90,
      show candIdx m S k + 7 = candIdx m S k + 6 + 1 by ring]
    exact wrap_succ (by omega)
  have w12 : c₁₃.nreg 84012 = candIdx m S (2 * m - k) + 5 := by
    rw [o₁₃.1 _ (by simp), o₁₂.1 _ (by simp), v₁₁, g114, g23 o110 (by simp)]; omega
  have w13 : c₁₃.nreg 84013 = (candIdx m S (2 * m - k) + 7) % (2 * m + 7) := by
    rw [v₁₃, a12_13, a12_90, show candIdx m S (2 * m - k) + 7 = candIdx m S (2 * m - k) + 6 + 1
      by ring]
    exact wrap_succ (by omega)
  have w09 : c₁₃.nreg 84009 = 2 := by
    rw [o₁₃.1 _ (by simp), o₁₂.1 _ (by simp), o₁₁.1 _ (by simp), o₁₀.1 _ (by simp),
      o₉.1 _ (by simp), o₈.1 _ (by simp), v₇]
  -- the third hole
  have b109 : c₁₃.nreg 83109 = k := by
    rw [(o₂.trans (((((((((((o₃.trans o₄).trans o₅).trans o₆).trans o₇).trans o₈).trans o₉).trans
      o₁₀).trans o₁₁).trans o₁₂).trans o₁₃))).1 _ (by simp), v₁]
  have b98 : c₁₃.nreg 83098 = top := by rw [o113.1 _ (by simp), h98]
  have hW13 := e₁₃.wb_right
  have b100 : c₁₃.nreg 83100 = 2 * m := by rw [o113.1 _ (by simp), h100]
  have b101 : c₁₃.nreg 83101 = 7 := by rw [o113.1 _ (by simp), h101]
  have b96 : c₁₃.nreg 83096 = 2 := by rw [o113.1 _ (by simp), h96]
  obtain ⟨cT, kT, hkT, eT, t09, t1415, oT⟩ : ∃ cT, ∃ kT ≤ 8, Exec P W topH c₁₃ cT kT ∧
      cT.nreg 84009 = (if k = top then 3 else 2) ∧
      (k = top → cT.nreg 84014 = 2 * m + 5 ∧ cT.nreg 84015 = 0) ∧
      Out c₁₃ cT [84009, 84014, 84015] := by
    unfold topH
    by_cases g1 : c₁₃.nreg 83109 < c₁₃.nreg 83098
    · refine ⟨c₁₃, _, by omega, .ifLtN_true g1 (.skip hW13), ?_, fun h => ?_, Out.refl _ _⟩
      · rw [w09, ite_eq_right (by rw [b109, b98] at g1; omega)]
      · rw [b109, b98] at g1; omega
    by_cases g2 : c₁₃.nreg 83098 < c₁₃.nreg 83109
    · refine ⟨c₁₃, _, by omega, .ifLtN_false g1 (.ifLtN_true g2 (.skip hW13)), ?_,
        fun h => ?_, Out.refl _ _⟩
      · rw [w09, ite_eq_right (by rw [b109, b98] at g2; omega)]
      · rw [b109, b98] at g2; omega
    have hkt : k = top := by rw [b109, b98] at g1 g2; omega
    obtain ⟨d₁, f₁, u₁, p₁⟩ := out_instr (P := P) (Exec.constN hW13 84009 3 (by omega))
    obtain ⟨d₂, f₂, u₂, p₂⟩ := out_instr (P := P) (Exec.addN f₁.wb_right 84014 83100 83101
      (by rw [p₁.1 _ (by simp), p₁.1 _ (by simp), b100, b101]; omega))
    obtain ⟨d₃, f₃, u₃, p₃⟩ := out_instr (P := P) (Exec.subN f₂.wb_right 84014 84014 83096)
    obtain ⟨d₄, f₄, u₄, p₄⟩ := out_instr (P := P) (Exec.constN f₃.wb_right 84015 0 (Nat.zero_le _))
    refine ⟨d₄, _, by omega, .ifLtN_false g1 (.ifLtN_false g2 (.seq f₁ (.seq f₂ (.seq f₃ f₄)))),
      ?_, fun _ => ⟨?_, ?_⟩, (((p₁.trans p₂).trans p₃).trans p₄).mono (by simp)⟩
    · rw [p₄.1 _ (by simp), p₃.1 _ (by simp), p₂.1 _ (by simp), u₁, ite_eq_left hkt]
    · rw [p₄.1 _ (by simp), u₃, u₂, p₂.1 _ (by simp), p₁.1 _ (by simp), p₁.1 _ (by simp),
        b100, b101, p₁.1 _ (by simp), b96]; omega
    · rw [u₄]
  have ex : Exec P W vtxH c cT _ :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ (.seq e₉
      (.seq e₁₀ (.seq e₁₁ (.seq e₁₂ (.seq e₁₃ eT))))))))))))
  refine ⟨cT, _, by omega, ex, t09, ?_, ?_, ?_, ?_, t1415, (o113.trans oT).mono ?_⟩
  · rw [oT.1 _ (by simp), w10]
  · rw [oT.1 _ (by simp), w11]
  · rw [oT.1 _ (by simp), w12]
  · rw [oT.1 _ (by simp), w13]
  · intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [chainHL, List.mem_cons, List.not_mem_nil, or_false]; omega

end

end Restore

end Chazelle.Core
