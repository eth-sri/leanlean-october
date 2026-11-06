module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepIoHoleRam

/-!
# The sweep RAM (WP-D), answers: the holes of a chain model (copied from WP-E, renumbered)

`chainH` computes the holes of the candidate `x = (e, h)` (registers `243005`, `243006`) in a chain
model from the chain descriptor at `243020` (`C.m`, the top index, the orientation bit), into
`241309 … 241315`:

* inside a tour edge (`h > 0`): the edge `e` and its twin `tourTwin C (e - 6) + 6`;
* at a tour vertex (`h = 0`) of the chain vertex `k`: the vertex holes of the candidates
  `candIdx k + 6`, `candIdx (2m - k) + 6`, and of `2m + 6` if `k` is the top.
-/

namespace Chazelle.Core

namespace SweepIo

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim SignK
open Chazelle.Chain (sideE)

variable {P : Polygon} {W : ℕ} {c : Config}

/-- The descriptor words and the tour step `i = e - 6`. -/
def chainPre : Stmt := block [.constN 243096 2, .addN 243095 243020 243096, .loadN 243097 243095,
  .addN 243095 243095 243023, .loadN 243098 243095, .addN 243095 243095 243023, .loadN 243099 243095,
  .addN 243100 243097 243097, .constN 243101 7, .addN 243090 243100 243101, .constN 243103 6,
  .subN 243104 243005 243103]

/-- The start `S` of the tour (`sideS`). -/
def sS : Stmt := .ifLtN 243099 243023 (.instr (.subN 243102 243100 243098))
  (.ifLtN 243023 243099 (.instr (.subN 243102 243100 243098)) (.instr (.copyN 243102 243098)))

/-- The tour position `j = (S + i) mod 2m` (without sums above `2m`). -/
def jS : Stmt := .seq (.instr (.subN 243105 243100 243102))
  (.ifLtN 243104 243105 (.instr (.addN 243106 243102 243104))
    (.seq (.instr (.subN 243106 243104 243105)) (condSub 243106 243106 243100)))

/-- The holes of a point inside a tour edge. -/
def edgeH : Stmt := .seq (.instr (.subN 243107 243100 243023)) (.seq (.instr (.subN 243107 243107 243106))
  (.seq (candS 243108 243107 243102 243100) (.seq (.instr (.constN 241309 2))
    (.seq (.instr (.copyN 241310 243005)) (.seq (.instr (.addN 241311 243005 243023))
      (.seq (.instr (.addN 241312 243108 243103)) (.instr (.addN 241313 241312 243023))))))))

/-- The third hole, at the last tour vertex, for the top. -/
def topH : Stmt := .ifLtN 243109 243098 .skip (.ifLtN 243098 243109 .skip
  (.seq (.instr (.constN 241309 3)) (.seq (.instr (.addN 241314 243100 243101))
    (.seq (.instr (.subN 241314 241314 243096)) (.instr (.constN 241315 0))))))

/-- The holes of a chain vertex. -/
def vtxH : Stmt :=
  .seq (.ifLtN 243097 243106 (.instr (.subN 243109 243100 243106)) (.instr (.copyN 243109 243106)))
  (.seq (candS 243110 243109 243102 243100) (.seq (.instr (.subN 243111 243100 243109))
  (.seq (candS 243112 243111 243102 243100) (.seq (.instr (.addN 243113 243110 243103))
  (.seq (.instr (.addN 243114 243112 243103)) (.seq (.instr (.constN 241309 2))
  (.seq (.instr (.subN 241310 243113 243023)) (.seq (.instr (.addN 241311 243113 243023))
  (.seq (nxtS 241311 243090) (.seq (.instr (.subN 241312 243114 243023))
  (.seq (.instr (.addN 241313 243114 243023)) (.seq (nxtS 241313 243090) topH))))))))))))

/-- **The holes of the candidate in a chain model.** -/
def chainH : Stmt := .seq chainPre (.seq sS (.seq jS (.ifLtN 243022 243006 edgeH vtxH)))

/-- The scratch registers of `chainH`. -/
def chainHL : List ℕ := [243090, 243095, 243096, 243097, 243098, 243099, 243100, 243101, 243102, 243103,
  243104, 243105, 243106, 243107, 243108, 243109, 243110, 243111, 243112, 243113, 243114, 241309, 241310,
  241311, 241312, 241313, 241314, 241315]

/-- The start of the tour from the descriptor words. -/
def sOf (m top bit : ℕ) : ℕ := if bit = 1 then top else 2 * m - top

section
variable (hw : WordsBounded W c)
include hw
theorem chainPre_exec {B m top bit : ℕ} (hB : c.nreg 243020 = B)
    (h23 : c.nreg 243023 = 1) (hm : c.nmem (B + 2) = m) (ht : c.nmem (B + 3) = top)
    (hb : c.nmem (B + 4) = bit) (hBW : B + 4 ≤ W) (hmW : 2 * m + 7 ≤ W) :
    ∃ c', ∃ k ≤ 12, Exec P W chainPre c c' k ∧ c'.nreg 243097 = m ∧ c'.nreg 243098 = top ∧
      c'.nreg 243099 = bit ∧ c'.nreg 243100 = 2 * m ∧ c'.nreg 243101 = 7 ∧
      c'.nreg 243090 = 2 * m + 7 ∧ c'.nreg 243096 = 2 ∧ c'.nreg 243103 = 6 ∧
      c'.nreg 243104 = c.nreg 243005 - 6 ∧ Out c c' chainHL := by
  unfold chainPre
  have hB' : c.nreg 243020 = B := hB
  obtain ⟨c', k, ex, hk, q97, q98, q99, q100, q101, q90, q96, q103, q104, hr, rr, mm, rm, oo⟩ :
      ∃ c' k, Exec P W (block [.constN 243096 2, .addN 243095 243020 243096, .loadN 243097 243095,
        .addN 243095 243095 243023, .loadN 243098 243095, .addN 243095 243095 243023,
        .loadN 243099 243095, .addN 243100 243097 243097, .constN 243101 7,
        .addN 243090 243100 243101, .constN 243103 6, .subN 243104 243005 243103]) c c' k ∧ k = 12 ∧
        c'.nreg 243097 = m ∧ c'.nreg 243098 = top ∧ c'.nreg 243099 = bit ∧
        c'.nreg 243100 = 2 * m ∧ c'.nreg 243101 = 7 ∧ c'.nreg 243090 = 2 * m + 7 ∧
        c'.nreg 243096 = 2 ∧ c'.nreg 243103 = 6 ∧ c'.nreg 243104 = c.nreg 243005 - 6 ∧
        (∀ r, r ∉ chainHL → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
        c'.rmem = c.rmem ∧ c'.output = c.output := by
    
    
    exec_block
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hB', h23]; omega)
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · ram_simp
    · ram_simp
    · ram_simp
    · ram_simp <;> omega_nf
    · ram_simp
    · ram_simp <;> omega_nf
    · ram_simp
    · ram_simp
    · grind [Machine.upd_same]
    · simp only [chainHL, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      ram_simp
  ram_grind

theorem sS_exec {m top bit : ℕ} (h99 : c.nreg 243099 = bit)
    (h100 : c.nreg 243100 = 2 * m) (h98 : c.nreg 243098 = top) (h23 : c.nreg 243023 = 1) :
    ∃ c', ∃ k ≤ 5, Exec P W sS c c' k ∧ c'.nreg 243102 = sOf m top bit ∧ Out c c' [243102] := by
  unfold sS sOf
  by_cases g1 : c.nreg 243099 < c.nreg 243023
  · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.subN hw 243102 243100 243098)
    refine ⟨c', _, by omega, .ifLtN_true g1 e, ?_, o⟩
    simp_all
  by_cases g2 : c.nreg 243023 < c.nreg 243099
  · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.subN hw 243102 243100 243098)
    refine ⟨c', _, by omega, .ifLtN_false g1 (.ifLtN_true g2 e), ?_, o⟩
    grind
  · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.copyN hw 243102 243098)
    refine ⟨c', _, by omega, .ifLtN_false g1 (.ifLtN_false g2 e), ?_, o⟩
    grind

theorem jS_exec {m S i : ℕ} (_hm : 0 < m) (h102 : c.nreg 243102 = S)
    (h104 : c.nreg 243104 = i) (h100 : c.nreg 243100 = 2 * m) (hS : S ≤ 2 * m) (hi : i ≤ 2 * m)
    (hW : 2 * m ≤ W) :
    ∃ c', ∃ k ≤ 8, Exec P W jS c c' k ∧ c'.nreg 243106 = (S + i) % (2 * m) ∧
      Out c c' [243105, 243106] := by
  obtain ⟨c₁, e₁, v₁, o₁⟩ := out_instr (P := P) (Exec.subN hw 243105 243100 243102)
  have g : ∀ r, r ≠ 243105 → c₁.nreg r = c.nreg r := fun r hr => o₁.1 r (by simp [hr])
  have u : c₁.nreg 243105 = 2 * m - S := by omega
  by_cases hlt : c₁.nreg 243104 < c₁.nreg 243105
  · rw [g _ (by omega), h104, u] at hlt
    obtain ⟨c₂, e₂, v₂, o₂⟩ := out_instr (P := P) (Exec.addN e₁.wb_right 243106 243102 243104
      (by grind))
    refine ⟨c₂, _, by omega, .seq e₁ (.ifLtN_true (by simp_all) e₂),
      ?_, (o₁.trans o₂).mono (by simp)⟩
    rw [v₂, g _ (by omega), g _ (by omega), h102, h104, Nat.mod_eq_of_lt (by omega)]
  · rw [g _ (by omega), h104, u] at hlt
    obtain ⟨c₂, e₂, v₂, o₂⟩ := out_instr (P := P) (Exec.subN e₁.wb_right 243106 243104 243105)
    obtain ⟨c₃, k₃, hk₃, e₃, v₃, o₃⟩ := condSub_exec (P := P) e₂.wb_right 243106 243106 243100
    refine ⟨c₃, _, by omega, .seq e₁ (.ifLtN_false (by grind)
      (.seq e₂ e₃)), ?_, ((o₁.trans o₂).trans o₃).mono (by simp)⟩
    have w6 : c₂.nreg 243106 = S + i - 2 * m := by
      grind
    have w100 : c₂.nreg 243100 = 2 * m := by ram_grind
    rw [v₃, w6, w100]
    by_cases h2 : S + i - 2 * m < 2 * m
    · rw [ite_eq_left h2, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt h2]
    · rw [ite_eq_right h2, show S + i = 2 * m + 2 * m by omega, Nat.add_mod_right, Nat.mod_self]
      omega

theorem edgeH_exec {m S j e : ℕ} (h100 : c.nreg 243100 = 2 * m)
    (h106 : c.nreg 243106 = j) (h102 : c.nreg 243102 = S) (h103 : c.nreg 243103 = 6)
    (h23 : c.nreg 243023 = 1) (h05 : c.nreg 243005 = e) (hj : j < 2 * m) (hS : S ≤ 2 * m)
    (heW : e + 1 ≤ W) (hmW : 2 * m + 7 ≤ W) :
    ∃ c', ∃ k ≤ 12, Exec P W edgeH c c' k ∧ c'.nreg 241309 = 2 ∧ c'.nreg 241310 = e ∧
      c'.nreg 241311 = e + 1 ∧ c'.nreg 241312 = candIdx m S (2 * m - 1 - j) + 6 ∧
      c'.nreg 241313 = candIdx m S (2 * m - 1 - j) + 7 ∧
      Out c c' [243107, 243108, 241309, 241310, 241311, 241312, 241313] := by
  obtain ⟨c₁, e₁, v₁, o₁⟩ := out_instr (P := P) (Exec.subN hw 243107 243100 243023)
  obtain ⟨c₂, e₂, v₂, o₂⟩ := out_instr (P := P) (Exec.subN e₁.wb_right 243107 243107 243106)
  have g : ∀ r, r ≠ 243107 → c₂.nreg r = c.nreg r := fun r hr => by
    ram_grind
  have q107 : c₂.nreg 243107 = 2 * m - 1 - j := by
    ram_grind
  obtain ⟨c₃, k₃, hk₃, e₃, v₃, o₃⟩ := candS_exec (P := P) e₂.wb_right (dst := 243108) (jr := 243107)
    (sr := 243102) (mr := 243100) (by omega) (by omega) (by omega) q107
    (by grind) (by grind) hS (by omega) (by omega)
  have g3 : ∀ r, r ≠ 243107 → r ≠ 243108 → c₃.nreg r = c.nreg r := fun r h1 h2 => by
    ram_grind
  obtain ⟨c₄, e₄, v₄, o₄⟩ := out_instr (P := P) (Exec.constN e₃.wb_right 241309 2 (by omega))
  obtain ⟨c₅, e₅, v₅, o₅⟩ := out_instr (P := P) (Exec.copyN e₄.wb_right 241310 243005)
  obtain ⟨c₆, e₆, v₆, o₆⟩ := out_instr (P := P) (Exec.addN e₅.wb_right 241311 243005 243023
    (by ram_grind))
  have c1 : ∀ r, r ≠ 241309 → r ≠ 241310 → r ≠ 241311 → c₆.nreg r = c₃.nreg r := fun r a b d => by
    rw [o₆.1 r (by simp [d]), o₅.1 r (by simp [b]), o₄.1 r (by simp [a])]
  have hc : candIdx m S (2 * m - 1 - j) ≤ 2 * m := by grind [candIdx]
  have a108 : c₆.nreg 243108 = candIdx m S (2 * m - 1 - j) := by
    grind
  have a103 : c₆.nreg 243103 = 6 := by grind
  have a23 : c₆.nreg 243023 = 1 := by grind
  obtain ⟨c₇, e₇, v₇, o₇⟩ := out_instr (P := P) (Exec.addN e₆.wb_right 241312 243108 243103
    (by omega))
  have b12 : c₇.nreg 241312 = candIdx m S (2 * m - 1 - j) + 6 := by omega
  have b23 : c₇.nreg 243023 = 1 := by rw [o₇.1 _ (by simp), a23]
  obtain ⟨c₈, e₈, v₈, o₈⟩ := out_instr (P := P) (Exec.addN e₇.wb_right 241313 241312 243023
    (by omega))
  have ex : Exec P W edgeH c c₈ _ :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈))))))
  have a05 : c₄.nreg 243005 = e := by rw [o₄.1 _ (by simp), g3 _ (by omega) (by omega), h05]
  have a23' : c₅.nreg 243023 = 1 := by rw [o₅.1 _ (by simp), o₄.1 _ (by simp),
    g3 _ (by omega) (by omega), h23]
  have a05' : c₅.nreg 243005 = e := by rw [o₅.1 _ (by simp), a05]
  ram_grind


end

theorem candIdx_le {m S j : ℕ} (hS : S ≤ 2 * m) (hj : j ≤ 2 * m) : candIdx m S j ≤ 2 * m := by
  core_grind

theorem vtxH_exec (hw : WordsBounded W c) {m top S j : ℕ} (h97 : c.nreg 243097 = m)
    (h98 : c.nreg 243098 = top) (h100 : c.nreg 243100 = 2 * m) (h101 : c.nreg 243101 = 7)
    (h96 : c.nreg 243096 = 2) (h90 : c.nreg 243090 = 2 * m + 7) (h103 : c.nreg 243103 = 6)
    (h102 : c.nreg 243102 = S) (h106 : c.nreg 243106 = j) (h23 : c.nreg 243023 = 1)
    (hS : S ≤ 2 * m) (hj : j < 2 * m) (hmW : 2 * m + 7 ≤ W) :
    ∃ c', ∃ k ≤ 60, Exec P W vtxH c c' k ∧
      c'.nreg 241309 = (if sideE m j = top then 3 else 2) ∧
      c'.nreg 241310 = candIdx m S (sideE m j) + 5 ∧
      c'.nreg 241311 = (candIdx m S (sideE m j) + 7) % (2 * m + 7) ∧
      c'.nreg 241312 = candIdx m S (2 * m - sideE m j) + 5 ∧
      c'.nreg 241313 = (candIdx m S (2 * m - sideE m j) + 7) % (2 * m + 7) ∧
      (sideE m j = top → c'.nreg 241314 = 2 * m + 5 ∧ c'.nreg 241315 = 0) ∧
      Out c c' chainHL := by
  set k := sideE m j with hkd
  have hkm : k ≤ m := by grind [sideE]
  -- the chain vertex
  obtain ⟨c₁, k₁, hk₁, e₁, v₁, o₁⟩ : ∃ c₁, ∃ k₁ ≤ 3, Exec P W (.ifLtN 243097 243106
      (.instr (.subN 243109 243100 243106)) (.instr (.copyN 243109 243106))) c c₁ k₁ ∧
      c₁.nreg 243109 = k ∧ Out c c₁ [243109] := by
    by_cases g : c.nreg 243097 < c.nreg 243106
    · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.subN hw 243109 243100 243106)
      refine ⟨c', _, by omega, .ifLtN_true g e, ?_, o⟩
      simp_all [sideE]
    · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.copyN hw 243109 243106)
      refine ⟨c', _, by omega, .ifLtN_false g e, ?_, o⟩
      simp_all [sideE]
  have i1 : ∀ r, r ≠ 243109 → c₁.nreg r = c.nreg r := fun r hr => o₁.1 r (by simp [hr])
  obtain ⟨c₂, k₂, hk₂, e₂, v₂, o₂⟩ := candS_exec (P := P) e₁.wb_right (dst := 243110)
    (jr := 243109) (sr := 243102) (mr := 243100) (by omega) (by omega) (by omega) v₁
    (by simp_all) (by simp_all) hS (by omega) (by omega)
  have o12 := o₁.trans o₂
  obtain ⟨c₃, e₃, v₃, o₃⟩ := out_instr (P := P) (Exec.subN e₂.wb_right 243111 243100 243109)
  have q111 : c₃.nreg 243111 = 2 * m - k := by
    rw [v₃, o12.1 _ (by simp), h100, o₂.1 _ (by simp), v₁]
  have o13 := o12.trans o₃
  obtain ⟨c₄, k₄, hk₄, e₄, v₄, o₄⟩ := candS_exec (P := P) e₃.wb_right (dst := 243112)
    (jr := 243111) (sr := 243102) (mr := 243100) (by omega) (by omega) (by omega) q111
    (by rw [o13.1 _ (by simp), h102]) (by rw [o13.1 _ (by simp), h100]) hS (by omega) (by omega)
  have o14 := o13.trans o₄
  have c1le := candIdx_le (m := m) (j := k) hS (by omega)
  have c2le := candIdx_le (m := m) (j := 2 * m - k) hS (by omega)
  have a110 : c₄.nreg 243110 = candIdx m S k := by rw [o₄.1 _ (by simp), o₃.1 _ (by simp), v₂]
  obtain ⟨c₅, e₅, v₅, o₅⟩ := out_instr (P := P) (Exec.addN e₄.wb_right 243113 243110 243103
    (by rw [a110, o14.1 _ (by simp), h103]; omega))
  have o15 := o14.trans o₅
  have a112 : c₅.nreg 243112 = candIdx m S (2 * m - k) := by rw [o₅.1 _ (by simp), v₄]
  obtain ⟨c₆, e₆, v₆, o₆⟩ := out_instr (P := P) (Exec.addN e₅.wb_right 243114 243112 243103
    (by rw [a112, o15.1 _ (by simp), h103]; omega))
  have o16 := o15.trans o₆
  have q113 : c₆.nreg 243113 = candIdx m S k + 6 := by
    rw [o₆.1 _ (by simp), v₅, a110, o14.1 _ (by simp), h103]
  have q114 : c₆.nreg 243114 = candIdx m S (2 * m - k) + 6 := by
    rw [v₆, a112, o15.1 _ (by simp), h103]
  obtain ⟨c₇, e₇, v₇, o₇⟩ := out_instr (P := P) (Exec.constN e₆.wb_right 241309 2 (by omega))
  obtain ⟨c₈, e₈, v₈, o₈⟩ := out_instr (P := P) (Exec.subN e₇.wb_right 241310 243113 243023)
  have o18 := (o16.trans o₇).trans o₈
  obtain ⟨c₉, e₉, v₉, o₉⟩ := out_instr (P := P) (Exec.addN e₈.wb_right 241311 243113 243023
    (by rw [o₈.1 _ (by simp), o₇.1 _ (by simp), q113, o18.1 _ (by simp), h23]; omega))
  obtain ⟨c₁₀, k₁₀, hk₁₀, e₁₀, v₁₀, o₁₀⟩ := nxtS_exec (P := P) e₉.wb_right 241311 243090
  have o110 := (o18.trans o₉).trans o₁₀
  have g113 : c₉.nreg 243113 = candIdx m S k + 6 := by
    rw [o₉.1 _ (by simp), o₈.1 _ (by simp), o₇.1 _ (by simp), q113]
  have g23 : ∀ {cc : Config} {L : List ℕ}, Out c cc L → 243023 ∉ L → cc.nreg 243023 = 1 :=
    fun o h => by rw [o.1 _ h, h23]
  obtain ⟨c₁₁, e₁₁, v₁₁, o₁₁⟩ := out_instr (P := P) (Exec.subN e₁₀.wb_right 241312 243114 243023)
  obtain ⟨c₁₂, e₁₂, v₁₂, o₁₂⟩ := out_instr (P := P) (Exec.addN e₁₁.wb_right 241313 243114 243023
    (by rw [o₁₁.1 _ (by simp), o₁₀.1 _ (by simp), o₉.1 _ (by simp), o₈.1 _ (by simp),
      o₇.1 _ (by simp), q114, g23 (o110.trans o₁₁) (by simp)]; omega))
  obtain ⟨c₁₃, k₁₃, hk₁₃, e₁₃, v₁₃, o₁₃⟩ := nxtS_exec (P := P) e₁₂.wb_right 241313 243090
  have o113 := ((o110.trans o₁₁).trans o₁₂).trans o₁₃
  have g114 : c₁₀.nreg 243114 = candIdx m S (2 * m - k) + 6 := by
    rw [o₁₀.1 _ (by simp), o₉.1 _ (by simp), o₈.1 _ (by simp), o₇.1 _ (by simp), q114]
  -- the values of the two vertex holes
  have a9_11 : c₉.nreg 241311 = candIdx m S k + 7 := by
    rw [v₉, o₈.1 _ (by simp), o₇.1 _ (by simp), q113, g23 o18 (by simp)]
  have a9_90 : c₉.nreg 243090 = 2 * m + 7 := by rw [(o18.trans o₉).1 _ (by simp), h90]
  have a12_13 : c₁₂.nreg 241313 = candIdx m S (2 * m - k) + 7 := by
    rw [v₁₂, o₁₁.1 _ (by simp), g114, g23 (o110.trans o₁₁) (by simp)]
  have a12_90 : c₁₂.nreg 243090 = 2 * m + 7 := by
    rw [((o110.trans o₁₁).trans o₁₂).1 _ (by simp), h90]
  have w10 : c₁₃.nreg 241310 = candIdx m S k + 5 := by
    rw [o₁₃.1 _ (by simp), o₁₂.1 _ (by simp), o₁₁.1 _ (by simp), o₁₀.1 _ (by simp),
      o₉.1 _ (by simp), v₈, o₇.1 _ (by simp), q113, g23 (o16.trans o₇) (by simp)]; omega
  have w11 : c₁₃.nreg 241311 = (candIdx m S k + 7) % (2 * m + 7) := by
    rw [o₁₃.1 _ (by simp), o₁₂.1 _ (by simp), o₁₁.1 _ (by simp), v₁₀, a9_11, a9_90,
      show candIdx m S k + 7 = candIdx m S k + 6 + 1 by ring]
    exact wrap_succ (by omega)
  have w12 : c₁₃.nreg 241312 = candIdx m S (2 * m - k) + 5 := by
    rw [o₁₃.1 _ (by simp), o₁₂.1 _ (by simp), v₁₁, g114, g23 o110 (by simp)]; omega
  have w13 : c₁₃.nreg 241313 = (candIdx m S (2 * m - k) + 7) % (2 * m + 7) := by
    rw [v₁₃, a12_13, a12_90, show candIdx m S (2 * m - k) + 7 = candIdx m S (2 * m - k) + 6 + 1
      by ring]
    exact wrap_succ (by omega)
  have w09 : c₁₃.nreg 241309 = 2 := by
    rw [o₁₃.1 _ (by simp), o₁₂.1 _ (by simp), o₁₁.1 _ (by simp), o₁₀.1 _ (by simp),
      o₉.1 _ (by simp), o₈.1 _ (by simp), v₇]
  -- the third hole
  have b109 : c₁₃.nreg 243109 = k := by
    rw [(o₂.trans (((((((((((o₃.trans o₄).trans o₅).trans o₆).trans o₇).trans o₈).trans o₉).trans
      o₁₀).trans o₁₁).trans o₁₂).trans o₁₃))).1 _ (by simp), v₁]
  have b98 : c₁₃.nreg 243098 = top := by rw [o113.1 _ (by simp), h98]
  have hW13 := e₁₃.wb_right
  have b100 : c₁₃.nreg 243100 = 2 * m := by rw [o113.1 _ (by simp), h100]
  have b101 : c₁₃.nreg 243101 = 7 := by rw [o113.1 _ (by simp), h101]
  have b96 : c₁₃.nreg 243096 = 2 := by rw [o113.1 _ (by simp), h96]
  obtain ⟨cT, kT, hkT, eT, t09, t1415, oT⟩ : ∃ cT, ∃ kT ≤ 8, Exec P W topH c₁₃ cT kT ∧
      cT.nreg 241309 = (if k = top then 3 else 2) ∧
      (k = top → cT.nreg 241314 = 2 * m + 5 ∧ cT.nreg 241315 = 0) ∧
      Out c₁₃ cT [241309, 241314, 241315] := by
    unfold topH
    by_cases g1 : c₁₃.nreg 243109 < c₁₃.nreg 243098
    · refine ⟨c₁₃, _, by omega, .ifLtN_true g1 (.skip hW13), ?_, fun h => ?_, Out.refl _ _⟩
      · rw [w09, ite_eq_right (by omega)]
      omega
    by_cases g2 : c₁₃.nreg 243098 < c₁₃.nreg 243109
    · refine ⟨c₁₃, _, by omega, .ifLtN_false g1 (.ifLtN_true g2 (.skip hW13)), ?_,
        fun h => ?_, Out.refl _ _⟩
      · rw [w09, ite_eq_right (by omega)]
      omega
    have hkt : k = top := by omega
    obtain ⟨d₁, f₁, u₁, p₁⟩ := out_instr (P := P) (Exec.constN hW13 241309 3 (by omega))
    obtain ⟨d₂, f₂, u₂, p₂⟩ := out_instr (P := P) (Exec.addN f₁.wb_right 241314 243100 243101
      (by rw [p₁.1 _ (by simp), p₁.1 _ (by simp), b100, b101]; omega))
    obtain ⟨d₃, f₃, u₃, p₃⟩ := out_instr (P := P) (Exec.subN f₂.wb_right 241314 241314 243096)
    obtain ⟨d₄, f₄, u₄, p₄⟩ := out_instr (P := P) (Exec.constN f₃.wb_right 241315 0 (Nat.zero_le _))
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

end SweepIo

end Chazelle.Core
