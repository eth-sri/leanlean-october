module

public import Chazelle.MacT
public import Chazelle.Core.DownPhaseOracleTop
public import Chazelle.Core.RestoreRound
public import Chazelle.Core.ShotListGLeaf
public import Chazelle.Core.DownPhaseOracleArc
public import Chazelle.Core.SweepChainT
public import Chazelle.Core.RestoreTPos
public import Chazelle.Core.FactsAttach
public import Chazelle.Core.FuseMathCut
public import Chazelle.Core.GranInitL3
public import Chazelle.Core.DownPhaseDrvXRamH
public import Chazelle.Core.SweepPrimKer
public import Chazelle.Core.BruteCorner

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
def sS : Stmt := .ifLtN 83099 83023 ztncd
  (.ifLtN 83023 83099 ztncd (.instr (.copyN 83102 83098)))

/-- The tour position `j = (S + i) mod 2m` (without sums above `2m`). -/
def jS : Stmt := .seq (.instr (.subN 83105 83100 83102))
  (.ifLtN 83104 83105 (.instr (.addN 83106 83102 83104))
    (.seq (.instr (.subN 83106 83104 83105)) (condSub 83106 83106 83100)))

/-- The holes of a point inside a tour edge. -/
def edgeH : Stmt := .seq (.instr (.subN 83107 83100 83023)) (.seq (.instr (.subN 83107 83107 83106))
  (.seq (candS 83108 83107 83102 83100) (.seq ztouh
    (.seq ztigm (.seq (.instr (.addN 84011 83005 83023))
      (.seq (.instr (.addN 84012 83108 83103)) (.instr (.addN 84013 84012 83023))))))))

/-- The third hole, at the last tour vertex, for the top. -/
def topH : Stmt := .ifLtN 83109 83098 .skip (.ifLtN 83098 83109 .skip
  (.seq (.instr (.constN 84009 3)) (.seq (.instr (.addN 84014 83100 83101))
    (.seq (.instr (.subN 84014 84014 83096)) (.instr (.constN 84015 0))))))

/-- The holes of a chain vertex. -/
def vtxH : Stmt :=
  .seq (.ifLtN 83097 83106 ztnce ztovu)
  (.seq (candS 83110 83109 83102 83100) (.seq (.instr (.subN 83111 83100 83109))
  (.seq (candS 83112 83111 83102 83100) (.seq (.instr (.addN 83113 83110 83103))
  (.seq (.instr (.addN 83114 83112 83103)) (.seq ztouh
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
    (h23 : c.nreg 83023 = 1) (hm : c.nmem zthb = m) (ht : c.nmem ztkh = top)
    (hb : c.nmem ztow = bit) (hBW : B + 4 ≤ W) (hmW : 2 * m + 7 ≤ W) :
    ∃ c', ∃ k ≤ 12, Exec P W chainPre c c' k ∧ c'.nreg 83097 = m ∧ c'.nreg 83098 = top ∧
      c'.nreg 83099 = bit ∧ c'.nreg 83100 = 2 * m ∧ c'.nreg 83101 = 7 ∧
      c'.nreg 83090 = 2 * m + 7 ∧ c'.nreg 83096 = 2 ∧ c'.nreg 83103 = 6 ∧
      c'.nreg 83104 = c.nreg 83005 - 6 ∧ Out c c' chainHL := by
  zulbk

  obtain ⟨c', k, ex, hk, q97, q98, q99, q100, q101, q90, q96, q103, q104, hr, rr, mm, rm, oo⟩ :
      ∃ c' k, Exec P W (block [.constN 83096 2, .addN 83095 83020 83096, .loadN 83097 83095,
        .addN 83095 83095 83023, .loadN 83098 83095, .addN 83095 83095 83023,
        .loadN 83099 83095, .addN 83100 83097 83097, .constN 83101 7,
        .addN 83090 83100 83101, .constN 83103 6, .subN 83104 83005 83103]) c c' k ∧ k = 12 ∧
        c'.nreg 83097 = m ∧ c'.nreg 83098 = top ∧ c'.nreg 83099 = bit ∧
        c'.nreg 83100 = 2 * m ∧ c'.nreg 83101 = 7 ∧ c'.nreg 83090 = 2 * m + 7 ∧
        c'.nreg 83096 = 2 ∧ c'.nreg 83103 = 6 ∧ c'.nreg 83104 = c.nreg 83005 - 6 ∧
        ztiuw ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
        c'.rmem = c.rmem ∧ c'.output = c.output := by
    have ht' : ztunm := ht
    have hb' : ztlxo := by_omega
    exec_block
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, hB', h23]; omega)
    zubqj
    refine ztdbj
    · simp_all
    · simp_all
    · simp_all
    · zugu
    · simp
    · zugu
    · simp
    · simp
    · simp
    · zudwa

  exact ⟨c', k, by_omega, ex, q97, q98, q99, q100, q101, q90, q96, q103, q104,
    ⟨hr, rr, mm, rm, oo⟩⟩
theorem sS_exec (hw : WordsBounded W c) {m top bit : ℕ} (h99 : c.nreg 83099 = bit)
    (h100 : c.nreg 83100 = 2 * m) (h98 : c.nreg 83098 = top) (h23 : c.nreg 83023 = 1) :
    ∃ c', ∃ k ≤ 5, Exec P W sS c c' k ∧ c'.nreg 83102 = sOf m top bit ∧ Out c c' [83102] := by
  unfold sS sOf
  by_cases g1 : c.nreg 83099 < c.nreg 83023
  · zuetu
    refine ztinu
    simp_all
  by_cases g2 : c.nreg 83023 < c.nreg 83099
  · zuetu
    refine ztgok
    grind
  · obtain ⟨c', e, v, o⟩ := out_instr (Exec.copyN hw 83102 83098)
    refine ztgoj
    grind
theorem jS_exec (hw : WordsBounded W c) {m S i : ℕ} (_hm : 0 < m) (h102 : c.nreg 83102 = S)
    (h104 : c.nreg 83104 = i) (h100 : c.nreg 83100 = 2 * m) (hS : S ≤ 2 * m) (hi : i ≤ 2 * m)
    (hW : 2 * m ≤ W) :
    ∃ c', ∃ k ≤ 8, Exec P W jS c c' k ∧ c'.nreg 83106 = ztbat % ztdk ∧
      Out c c' [83105, 83106] := by
  obtain ⟨c₁, e₁, v₁, o₁⟩ := out_instr (P := P) (Exec.subN hw 83105 83100 83102)
  have g : ∀ r, r ≠ 83105 → c₁.nreg r = c.nreg r := fun r hr => o₁.1 r by_simp_all
  have u : c₁.nreg 83105 = 2 * m - S := by_omega
  by_cases hlt : c₁.nreg 83104 < c₁.nreg 83105
  · zubcz
    obtain ⟨c₂, e₂, v₂, o₂⟩ := out_instr (Exec.addN e₁.wb_right 83106 83102 83104
      by_grind)
    refine ⟨c₂, _, by_omega, .seq e₁ ztspg,
      ?_, (o₁.trans o₂).mono by_simp⟩
    zudaw
  · zubcz
    obtain ⟨c₂, e₂, v₂, o₂⟩ := out_instr (Exec.subN e₁.wb_right 83106 83104 83105)
    obtain ⟨c₃, k₃, hk₃, e₃, v₃, o₃⟩ := condSub_exec e₂.wb_right 83106 83106 83100
    refine ⟨c₃, _, by_omega, .seq e₁ (.ifLtN_false by_simp_all
      ztcr), ?_, ((o₁.trans o₂).trans o₃).mono by_simp⟩
    have w6 : c₂.nreg 83106 = S + i - 2 * m := by
      grind
    have w100 : c₂.nreg 83100 = 2 * m := by zunmr
    zuckc

    · zucpz
    · zubyu
theorem edgeH_exec (hw : WordsBounded W c) {m S j e : ℕ} (h100 : c.nreg 83100 = 2 * m)
    (h106 : c.nreg 83106 = j) (h102 : c.nreg 83102 = S) (h103 : c.nreg 83103 = 6)
    (h23 : c.nreg 83023 = 1) (h05 : c.nreg 83005 = e) (hj : j < 2 * m) (hS : S ≤ 2 * m)
    (heW : e + 1 ≤ W) (hmW : 2 * m + 7 ≤ W) :
    ∃ c', ∃ k ≤ 12, Exec P W edgeH c c' k ∧ c'.nreg 84009 = 2 ∧ c'.nreg 84010 = e ∧
      c'.nreg 84011 = e + 1 ∧ c'.nreg 84012 = candIdx m S ztbdt + 6 ∧
      c'.nreg 84013 = candIdx m S ztbdt + 7 ∧
      Out c c' [83107, 83108, 84009, 84010, 84011, 84012, 84013] := by
  obtain ⟨c₁, e₁, v₁, o₁⟩ := out_instr (P := P) (Exec.subN hw 83107 83100 83023)
  obtain ⟨c₂, e₂, v₂, o₂⟩ := out_instr (P := P) (Exec.subN e₁.wb_right 83107 83107 83106)
  have g : ∀ r, r ≠ 83107 → c₂.nreg r = c.nreg r := fun r hr => by
    zugwv
  have q107 : c₂.nreg 83107 = 2 * m - 1 - j := by
    zudvl
  obtain ⟨c₃, k₃, hk₃, e₃, v₃, o₃⟩ := candS_exec (P := P) e₂.wb_right (dst := 83108) (jr := 83107)
    (sr := 83102) (mr := 83100) by_omega by_omega by_omega q107
    by_simp_all by_simp_all hS by_omega by_omega
  have g3 : ∀ r, r ≠ 83107 → r ≠ 83108 → c₃.nreg r = c.nreg r := fun r h1 h2 => by
    zugww
  obtain ⟨c₄, e₄, v₄, o₄⟩ := out_instr (P := P) (Exec.constN e₃.wb_right 84009 2 by_omega)
  obtain ⟨c₅, e₅, v₅, o₅⟩ := out_instr (P := P) (Exec.copyN e₄.wb_right 84010 83005)
  obtain ⟨c₆, e₆, v₆, o₆⟩ := out_instr (P := P) (Exec.addN e₅.wb_right 84011 83005 83023
    (by rw [o₅.1 _ by_simp, o₄.1 _ by_simp, o₅.1 _ by_simp, o₄.1 _ by_simp,
      g3 _ by_omega by_omega, g3 _ by_omega by_omega, h05, h23]; omega))
  have c1 : ∀ r, r ≠ 84009 → r ≠ 84010 → r ≠ 84011 → c₆.nreg r = c₃.nreg r := fun r a b d => by
    zuemm
  zugly
  have a108 : c₆.nreg 83108 = candIdx m S ztbdt := by
    grind
  have a103 : c₆.nreg 83103 = 6 := by_grind
  have a23 : c₆.nreg 83023 = 1 := by_grind
  obtain ⟨c₇, e₇, v₇, o₇⟩ := out_instr (P := P) (Exec.addN e₆.wb_right 84012 83108 83103
    by_omega)
  have b12 : c₇.nreg 84012 = candIdx m S ztbdt + 6 := by_omega
  have b23 : c₇.nreg 83023 = 1 := by zuoam
  obtain ⟨c₈, e₈, v₈, o₈⟩ := out_instr (P := P) (Exec.addN e₇.wb_right 84013 84012 83023
    by_omega)
  have ex : ztpjn :=
    .seq e₁ ztey
  have a05 : c₄.nreg 83005 = e := by zunku
  have a23' : c₅.nreg 83023 = 1 := by rw [o₅.1 _ by_simp, o₄.1 _ by_simp,
    g3 _ by_omega by_omega, h23]
  have a05' : c₅.nreg 83005 = e := by zuoan
  refine ztfwf
  · zuctu
  · zudfy
  · zudvc
  · zuilz
  · omega
  · exact (((((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).trans o₆).trans o₇).trans o₈).mono
      by_simp
theorem candIdx_le {m S j : ℕ} (hS : S ≤ 2 * m) (hj : j ≤ 2 * m) : candIdx m S j ≤ 2 * m := by
  zumsb
theorem vtxH_exec (hw : WordsBounded W c) {m top S j : ℕ} (h97 : c.nreg 83097 = m)
    (h98 : c.nreg 83098 = top) (h100 : c.nreg 83100 = 2 * m) (h101 : c.nreg 83101 = 7)
    (h96 : c.nreg 83096 = 2) (h90 : c.nreg 83090 = 2 * m + 7) (h103 : c.nreg 83103 = 6)
    (h102 : c.nreg 83102 = S) (h106 : c.nreg 83106 = j) (h23 : c.nreg 83023 = 1)
    (hS : S ≤ 2 * m) (hj : j < 2 * m) (hmW : 2 * m + 7 ≤ W) :
    ∃ c', ∃ k ≤ 60, Exec P W vtxH c c' k ∧
      c'.nreg 84009 = ztkwr ∧
      c'.nreg 84010 = candIdx m S ztkfd + 5 ∧
      c'.nreg 84011 = ztyvs % ztfk ∧
      c'.nreg 84012 = candIdx m S ztela + 5 ∧
      c'.nreg 84013 = ztyvr % ztfk ∧
      (sideE m j = top → c'.nreg 84014 = 2 * m + 5 ∧ c'.nreg 84015 = 0) ∧
      Out c c' chainHL := by
  zubzf

  -- the chain vertex
  obtain ⟨c₁, k₁, hk₁, e₁, v₁, o₁⟩ : ∃ c₁, ∃ k₁ ≤ 3, Exec P W (.ifLtN 83097 83106
      ztnce ztovu) c c₁ k₁ ∧
      c₁.nreg 83109 = k ∧ Out c c₁ [83109] := by
    by_cases g : c.nreg 83097 < c.nreg 83106
    · obtain ⟨c', e, v, o⟩ := out_instr (Exec.subN hw 83109 83100 83106)
      zubpt

    · obtain ⟨c', e, v, o⟩ := out_instr (Exec.copyN hw 83109 83106)
      zubum

  have i1 : ∀ r, r ≠ 83109 → c₁.nreg r = c.nreg r := fun r hr => o₁.1 r by_simp_all
  obtain ⟨c₂, k₂, hk₂, e₂, v₂, o₂⟩ := candS_exec (P := P) e₁.wb_right (dst := 83110)
    (jr := 83109) (sr := 83102) (mr := 83100) by_omega by_omega by_omega v₁
    by_simp_all by_simp_all hS by_omega by_omega
  zulma
  obtain ⟨c₃, e₃, v₃, o₃⟩ := out_instr (P := P) (Exec.subN e₂.wb_right 83111 83100 83109)
  have q111 : c₃.nreg 83111 = 2 * m - k := by
    zudvm
  zulmb
  obtain ⟨c₄, k₄, hk₄, e₄, v₄, o₄⟩ := candS_exec (P := P) e₃.wb_right (dst := 83112)
    (jr := 83111) (sr := 83102) (mr := 83100) by_omega by_omega by_omega q111
    ztlif ztlie hS by_omega by_omega
  zubgo

  have a110 : c₄.nreg 83110 = candIdx m S k := by zunms
  obtain ⟨c₅, e₅, v₅, o₅⟩ := out_instr (P := P) (Exec.addN e₄.wb_right 83113 83110 83103
    ztiie)
  zulmc
  have a112 : c₅.nreg 83112 = candIdx m S ztbhk := by zuoao
  obtain ⟨c₆, e₆, v₆, o₆⟩ := out_instr (P := P) (Exec.addN e₅.wb_right 83114 83112 83103
    ztiif)
  zulmd
  have q113 : c₆.nreg 83113 = candIdx m S k + 6 := by
    zudvb
  have q114 : c₆.nreg 83114 = candIdx m S ztbhk + 6 := by
    zufoq
  obtain ⟨c₇, e₇, v₇, o₇⟩ := out_instr (P := P) (Exec.constN e₆.wb_right 84009 2 by_omega)
  obtain ⟨c₈, e₈, v₈, o₈⟩ := out_instr (P := P) (Exec.subN e₇.wb_right 84010 83113 83023)
  zuhgb
  obtain ⟨c₉, e₉, v₉, o₉⟩ := out_instr (P := P) (Exec.addN e₈.wb_right 84011 83113 83023
    ztfbo)
  obtain ⟨c₁₀, k₁₀, hk₁₀, e₁₀, v₁₀, o₁₀⟩ := nxtS_exec (P := P) e₉.wb_right 84011 83090
  zuhga
  have g113 : c₉.nreg 83113 = candIdx m S k + 6 := by
    zudvd
  have g23 : ∀ {cc : Config} {L : List ℕ}, Out c cc L → 83023 ∉ L → cc.nreg 83023 = 1 :=
    fun o h => by zuoap
  obtain ⟨c₁₁, e₁₁, v₁₁, o₁₁⟩ := out_instr (P := P) (Exec.subN e₁₀.wb_right 84012 83114 83023)
  obtain ⟨c₁₂, e₁₂, v₁₂, o₁₂⟩ := out_instr (P := P) (Exec.addN e₁₁.wb_right 84013 83114 83023
    (by rw [o₁₁.1 _ by_simp, o₁₀.1 _ by_simp, o₉.1 _ by_simp, o₈.1 _ by_simp,
      o₇.1 _ by_simp, q114, g23 ztmms by_simp]; omega))
  obtain ⟨c₁₃, k₁₃, hk₁₃, e₁₃, v₁₃, o₁₃⟩ := nxtS_exec (P := P) e₁₂.wb_right 84013 83090
  zuesv
  have g114 : c₁₀.nreg 83114 = candIdx m S ztbhk + 6 := by
    zucts
  -- the values of the two vertex holes
  have a9_11 : c₉.nreg 84011 = candIdx m S k + 7 := by
    zudge
  have a9_90 : c₉.nreg 83090 = 2 * m + 7 := by zunmt
  have a12_13 : c₁₂.nreg 84013 = candIdx m S ztbhk + 7 := by
    zuems
  have a12_90 : c₁₂.nreg 83090 = 2 * m + 7 := by
    zudtf
  have w10 : c₁₃.nreg 84010 = candIdx m S k + 5 := by
    rw [o₁₃.1 _ by_simp, o₁₂.1 _ by_simp, o₁₁.1 _ by_simp, o₁₀.1 _ by_simp,
      o₉.1 _ by_simp, v₈, o₇.1 _ by_simp, q113, g23 ztwaw by_simp]; omega
  have w11 : c₁₃.nreg 84011 = ztpac % ztfk := by
    rw [o₁₃.1 _ by_simp, o₁₂.1 _ by_simp, o₁₁.1 _ by_simp, v₁₀, a9_11, a9_90,
      show candIdx m S k + 7 = candIdx m S k + 6 + 1 by ring]
    zuitx
  have w12 : c₁₃.nreg 84012 = candIdx m S ztbhk + 5 := by
    zuctt
  have w13 : c₁₃.nreg 84013 = ztyvq % ztfk := by
    rw [v₁₃, a12_13, a12_90, show candIdx m S _ + 7 = candIdx m S _ + 6 + 1
      by ring]
    zuitx
  have w09 : c₁₃.nreg 84009 = 2 := by
    rw [o₁₃.1 _ by_simp, o₁₂.1 _ by_simp, o₁₁.1 _ by_simp, o₁₀.1 _ by_simp,
      o₉.1 _ by_simp, o₈.1 _ by_simp, v₇]
  -- the third hole
  have b109 : c₁₃.nreg 83109 = k := by
    rw [(o₂.trans (((((((((((o₃.trans o₄).trans o₅).trans o₆).trans o₇).trans o₈).trans o₉).trans
      o₁₀).trans o₁₁).trans o₁₂).trans o₁₃))).1 _ by_simp, v₁]
  have b98 : c₁₃.nreg 83098 = top := by zuoaq
  zumcr
  have b100 : c₁₃.nreg 83100 = 2 * m := by zuoar
  have b101 : c₁₃.nreg 83101 = 7 := by zuoas
  have b96 : c₁₃.nreg 83096 = 2 := by zuoat
  obtain ⟨cT, kT, hkT, eT, t09, t1415, oT⟩ : ∃ cT, ∃ kT ≤ 8, Exec P W topH c₁₃ cT kT ∧
      cT.nreg 84009 = ztmlr ∧
      (k = top → cT.nreg 84014 = 2 * m + 5 ∧ cT.nreg 84015 = 0) ∧
      Out c₁₃ cT [84009, 84014, 84015] := by
    unfold topH
    by_cases g1 : c₁₃.nreg 83109 < c₁₃.nreg 83098
    · refine zteye
      · zudax
      omega
    by_cases g2 : c₁₃.nreg 83098 < c₁₃.nreg 83109
    · refine ⟨c₁₃, _, by_omega, .ifLtN_false g1 ztotb, ?_,
        fun h => ?_, Out.refl _ _⟩
      · zudax
      omega
    zuhyx
    obtain ⟨d₁, f₁, u₁, p₁⟩ := out_instr (P := P) (Exec.constN hW13 84009 3 by_omega)
    obtain ⟨d₂, f₂, u₂, p₂⟩ := out_instr (P := P) (Exec.addN f₁.wb_right 84014 83100 83101
      ztgfy)
    obtain ⟨d₃, f₃, u₃, p₃⟩ := out_instr (P := P) (Exec.subN f₂.wb_right 84014 84014 83096)
    obtain ⟨d₄, f₄, u₄, p₄⟩ := out_instr (P := P) (Exec.constN f₃.wb_right 84015 0 ztbg)
    refine ⟨d₄, _, by_omega, .ifLtN_false g1 ztgwq,
      ?_, fun _ => ztcp, (((p₁.trans p₂).trans p₃).trans p₄).mono by_simp⟩
    · zudan
    · rw [p₄.1 _ by_simp, u₃, u₂, p₂.1 _ by_simp, p₁.1 _ by_simp, p₁.1 _ by_simp,
        b100, b101, p₁.1 _ by_simp, b96]; omega
    omega
  have ex : ztpjx :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ (.seq e₉
      ztgxb))))))))
  refine zteba
  · zuilv
  · zuilw
  · zuilx
  · zuily
  decide
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Chazelle.Chain (sidePt sideInArc sidePt_zero)
open ShotList

/-- **The holes are near `z`**: every walk point with a key in a closed hole lies on a walk edge
through `z`. -/
def Near (M : Model) (Q : Polygon) (hs : List ztqx) (z : Point) : Prop :=
  ∀ g ∈ hs, ∀ p : ℕ, ∀ τ : ℝ, p < M.W.n → 0 ≤ τ → τ ≤ 1 →
    CIn ztfod ztfoe ztejd →
    ∃ p', p' < M.W.n ∧ (∃ t₁ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ sidePt M.W p' t₁ = z) ∧
      ∃ t₂ : ℝ, 0 ≤ t₂ ∧ t₂ ≤ 1 ∧ sidePt M.W p' t₂ = sidePt M.W p τ
variable (W : Polygon) {p e : ℕ} {τ : ℝ} {n q : ℕ}
theorem sidePt_one' (p : ℕ) : sidePt W p 1 = W.vtx ztwjb := by
  zufdr

/-- A key equal to a natural `e` at a position `(p, τ)`: the position is `(e, 0)` or `(e - 1, 1)`. -/
theorem key_eq_nat (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (h : (p : ℝ) + τ = e) :
    (p = e ∧ τ = 0) ∨ (p + 1 = e ∧ τ = 1) := by
  zuff
  · left
    have a1 : ztphd := by_linarith
    zujwn
    have b1 : p ≤ e := by_simp_all
    zuhvp
    grind
  · right
    zucuj
    have : ((p + 1 : ℕ) : ℝ) = e := by_simp_all
    exact ⟨by exact_mod_cast this, rfl⟩

/-- A key strictly between `e` and `e + 1` at a position `(p, τ)`: the position is on edge `e`. -/
theorem key_between (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (ha : (e : ℝ) < p + τ)
    (hb : (p : ℝ) + τ < e + 1) : p = e := by
  have a1 : ztmrn := by_linarith
  zujwn
  have b1 : p < e + 1 := by exact_mod_cast a1
  zuhvp
  omega

/-- **Positions with keys in the closed key interval of a walk edge** are points of the edge. -/
theorem edge_keys {e : ℕ} (he : e < W.n) {p : ℕ} (hp : p < W.n) {τ : ℝ}
    (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (hk : CIn (e : ℝ) ((ztda % W.n : ℕ) : ℝ) ztejd) :
    ∃ t₂ : ℝ, 0 ≤ t₂ ∧ t₂ ≤ 1 ∧ sidePt W e t₂ = sidePt W p τ := by
  -- the start vertex of the edge
  have at_e : (p : ℝ) + τ = e → ∃ t₂ : ℝ, 0 ≤ t₂ ∧ t₂ ≤ 1 ∧ sidePt W e t₂ = sidePt W p τ := by
    zuq
    rcases key_eq_nat h0 h1 h with ⟨rfl, rfl⟩ | ⟨hpe, rfl⟩
    · grind
    · zumkq
      rw [sidePt_zero, sidePt_one', ← hpe, Nat.mod_eq_of_lt by_omega]
  -- the end vertex of the edge
  have at_f : (p : ℝ) + τ = ((ztda % W.n : ℕ) : ℝ) →
      ∃ t₂ : ℝ, 0 ≤ t₂ ∧ t₂ ≤ 1 ∧ sidePt W e t₂ = sidePt W p τ := by
    zuq
    refine ztolm
    rw [sidePt_one']
    rcases key_eq_nat h0 h1 h with ⟨hpe, rfl⟩ | ⟨hpe, rfl⟩
    · rw [sidePt_zero, hpe]
    · -- `p + 1 = (e + 1) % n`: then `p = e` (the edge itself, at its end)
      rw [sidePt_one', hpe, Nat.mod_mod_of_dvd _ (dvd_refl _)]
  rcases hk with hin | h | h
  · zubix
    rcases Nat.lt_or_ge ztda W.n with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hin
      push_cast at hin
      rw [ite_eq_left by_linarith] at hin
      have := key_between h0 h1 hin.1 hin.2
      grind
    · have hn : e + 1 = W.n := by_omega
      rw [hn, Nat.mod_self] at hin
      push_cast at hin
      rw [ite_eq_right by_simp] at hin
      zukll
      · have hpe : p = e := by
          have a1 : ztehk := by_linarith
          have b1 : ztizr := by exact_mod_cast a1
          omega
        grind
      grind
  · grind
  simp_all
theorem prevV_succ (hn : 2 ≤ n) (hq : q < n) : ztkcn % n = q := by
  zuhqy

  · have : ztblb := by
      simp
    rw [this, show n - 1 + 1 = n by omega, Nat.mod_self]
  · have : ztquv % n = q - 1 := by
      zuxx
    rw [this, show q - 1 + 1 = q by omega, Nat.mod_eq_of_lt hq]

/-- **The key interval of a vertex hole** is the union of those of its two walk edges. -/
theorem vtx_keys_split (hn : 3 ≤ n) (hq : q < n) {k : ℝ} (hk0 : 0 ≤ k)
    (_hkn : k ≤ n) (h : CIn ((prevV n q : ℕ) : ℝ) ((ztfo % n : ℕ) : ℝ) k) :
    CIn ((prevV n q : ℕ) : ℝ) ((ztkcn % n : ℕ) : ℝ) k ∨
      CIn (q : ℝ) ((ztfo % n : ℕ) : ℝ) k := by
  have hpq : ztkcn % n = q := prevV_succ by_omega hq
  zumoa
  unfold CIn sideInArc at h ⊢
  grind

/-- **An edge hole is near the points of its edge.** -/
theorem near_eHole (M : Model) (Q : Polygon) {e : ℕ} (he : e < M.W.n) {z : Point}
    (hz : ∃ t₁ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ sidePt M.W e t₁ = z) {p : ℕ} {τ : ℝ} (hp : p < M.W.n)
    (h0 : 0 ≤ τ) (h1 : τ ≤ 1)
    (hk : CIn (M.key Q (eHole M.W.n e).1) (M.key Q (eHole M.W.n e).2) ztejd) :
    ∃ p', p' < M.W.n ∧ (∃ t₁ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ sidePt M.W p' t₁ = z) ∧
      ∃ t₂ : ℝ, 0 ≤ t₂ ∧ t₂ ≤ 1 ∧ sidePt M.W p' t₂ = sidePt M.W p τ := by
  simp only [eHole, key_hole] at hk
  exact ⟨e, he, hz, edge_keys M.W he hp h0 h1 hk⟩

/-- **A vertex hole is near its vertex.** -/
theorem near_vHole (M : Model) (Q : Polygon) (hn : 3 ≤ M.W.n) {q : ℕ} (hq : q < M.W.n)
    {z : Point} (hz : M.W.vtx q = z) {p : ℕ} {τ : ℝ} (hp : p < M.W.n) (h0 : 0 ≤ τ) (h1 : τ ≤ 1)
    (hk : CIn (M.key Q (vHole M.W.n q).1) (M.key Q (vHole M.W.n q).2) ztejd) :
    ∃ p', p' < M.W.n ∧ (∃ t₁ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ sidePt M.W p' t₁ = z) ∧
      ∃ t₂ : ℝ, 0 ≤ t₂ ∧ t₂ ≤ 1 ∧ sidePt M.W p' t₂ = sidePt M.W p τ := by
  simp only [vHole, key_hole] at hk
  have hk0 : (0 : ℝ) ≤ p + τ := by_grind
  have hkn : (p : ℝ) + τ ≤ M.W.n := by
    have : ((p + 1 : ℕ) : ℝ) ≤ M.W.n := by exact_mod_cast hp
    grind
  have hpv : prevV M.W.n q < M.W.n := by unfold prevV; exact Nat.mod_lt _ by_omega
  have hpq : (prevV M.W.n q + 1) % M.W.n = q := prevV_succ by_omega hq
  rcases vtx_keys_split hn hq hk0 hkn hk with h | h
  · refine ⟨prevV M.W.n q, hpv, ztolm, edge_keys M.W hpv hp h0 h1 h⟩
    rw [sidePt_one', hpq, hz]
  · exact ⟨q, hq, ⟨0, le_rfl, zero_le_one, by rw [sidePt_zero, hz]⟩, edge_keys M.W hq hp h0 h1 h⟩
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim SignK
open Chazelle.Chain (sideE sidePt)
variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-- **The holes of the candidate.** -/
def holeS : Stmt := .ifLtN 83021 83023 chainH intH

/-! ## The candidate on the chain -/

/-- **Where the candidate of a chain model lies**: at a tour vertex, or inside a tour edge. -/
theorem chain_x_cases {C : Chain} {Q : Polygon} {n : ℕ} {x : WPos}
    (hx : ProperPos ztc Q n x) (he : x.edge < (chainModel C).W.n)
    (hxc : x.hgt = 0 ∨ 0 < (chainModel C).param Q x) (hz : (chainModel C).pos Q x ∈ C.set) :
    6 ≤ x.edge ∧
      (x.hgt = 0 → x.edge - 6 ≤ 2 * C.m ∧
        (chainModel C).pos Q x = C.vertex ztyop) ∧
      (0 < x.hgt → x.edge - 6 < 2 * C.m ∧ 0 < (chainModel C).param Q x ∧
        (chainModel C).param Q x < 1) := by
  zucn
  have hpos : (chainModel C).pos Q x = sidePt ztcs x.edge
      _ := rfl
  zubmb

  · zufsc
  refine ztxzi
  · have hp0 : ztmrc := by
      zudei
    zuedg

  · grind
  grind

/-! ## The holes as a list -/

/-! ## The descriptor chain of a run -/

/-- **The chain of the descriptor of a run**, with its host regular and its polygon simple. -/
theorem TInv.chainS (hE : TGood P W M N c₀) (hI : TInv W c₀ c) {C : Chain}
    (hM : M = chainModel C) :
    ∃ H C', ChainDescAt c.nmem ztdms zta H C' ∧ M = chainModel C' ∧
      ChainWF P ztm c.nmem ztdms ∧ C'.P.Simple ∧
      HostRegular (Qof P).n H := by
  obtain ⟨h0, H₀, C₀, hC₀, hM₀⟩ := chainDesc_of hE.hMD hM
  zuqq
  have hcw := hE.hwfMD.2 h0
  obtain ⟨-, -, hEb, -⟩ := hcw.2 H₀ C₀ hC₀
  have hC₀' : ChainDescAt c.nmem ztdms zta H₀ C₀ := by
    rw [hI.h20]; exact chainDesc_agree hC₀ hcw.1 hEb hI.hm
  have e1 := NFLoc.chain_eq_of_desc hC₀' hC
  have e2 := NFLoc.hostAt_unique hC₀'.1 hC.1
  subst e1 e2
  exact ⟨H₀, C₀, hC, hM', hwf, hE.hsimp h0 H₀ C₀ hC₀, hE.hreg h0 H₀ C₀ hC₀⟩

/-! ## The contract -/

/-- **The holes in the registers** `84009 … 84015` are proper and cover the point `z`. -/
def HoleOut (M : Model) (Q : Polygon) (c : Config) (z : Point) : Prop :=
  c.nreg 84009 ≤ 3 ∧
    (∀ j < c.nreg 84009, c.nreg ztgzm < M.W.n ∧
      c.nreg ztgzn < M.W.n ∧ c.nreg ztgzm ≠ c.nreg ztgzn) ∧
    Cover M Q zttda z ∧ Near M Q zttda z

/-- The scratch registers of `holeS`. -/
def holeL : List ℕ := chainHL ++ [83092, 83093]
theorem holeAt_eq (c : Config) (j : ℕ) :
    ShotList.holeAt c 84000 j = (⟨c.nreg ztgzm, 0⟩, ⟨c.nreg ztgzn, 0⟩) :=
  rfl

/-! ## Hole arithmetic -/
theorem hole_mem {c : Config} {j : ℕ} (hj : j < c.nreg 84009) (h3 : c.nreg 84009 ≤ 3) :
    ShotList.holeAt c 84000 j ∈ ShotList.holeList c 84000 :=
  List.mem_map.2 by_grind
variable {n q : ℕ}
theorem prevV_lt (hn : 0 < n) : prevV n q < n := Nat.mod_lt _ hn
theorem prevV_ne (hn : 3 ≤ n) (hq : q < n) : prevV n q ≠ ztfo % n := by
  zuhqy

  · zucqd
    omega
  · zuxx
    zuidk
    · zuczo
    · zuedx
theorem succ_ne (hn : 2 ≤ n) (hq : q < n) : q ≠ ztfo % n := by
  rcases Nat.lt_or_ge ztfo n with h | h
  · zuczo
  · zuedx
theorem vHole_six {n c : ℕ} (h : c + 6 < n) : vHole n ztthh = ztyga := by
  zucah
theorem vtx_hole_ne {m c : ℕ} (hc : c ≤ 2 * m) : c + 5 ≠ ztfqb % ztfk := by
  zuidu
  · zuczo
  · zudap

/-! ## The holes on the RAM -/
theorem holeS_int (hE : TGood P W ztwiq N c₀) (hI : TInv W c₀ c)
    (h1 : c₀.nmem ztchn = 1) :
    RS P W c₀ holeS c 40 (fun c' => HoleOut ztwiq zta c'
      ((interiorModel zta).pos zta ztxt) ∧ Out c c' holeL) := by
  zudcv

  have hn : (interiorModel _).W.n = P.n := interior_n
  zuiyp
  zufgb
  have hWs : (interiorModel _).W.Simple := (FactsInterior.interiorWalk_spec hQ).1
  zudmz
  have he : c.nreg 83005 < P.n := by rw [h05, ← hn]; exact hE.hxe
  obtain ⟨c', k, hk, ex, v9, v10, v11, ho⟩ := intH_exec hI.hw
    (by have := hE.hW; unfold hostWords at this; omega) hI.h22 hI.h23 he
  have hL : ∀ r ∈ [83090, 83092, 83093, 84009, 84010, 84011], r ∈ holeL := by
    decide
  refine RS.out hI ztez (.ifLtN_false g21 ex) by_omega (ho.mono hL) ⟨?_, ho.mono hL⟩
  · zubes
    zumrj
  rw [h05, h06] at v10
  rw [h05] at v11
  rw [h05] at he
  set e := c₀.nreg 83005
  have a0 := holeAt_eq c' 0
  have hp := hE.hxp
  refine ⟨by_omega, fun j hj => ?_, ?_, ?_⟩
  · obtain rfl : ztebi := by_omega
    show c'.nreg 84010 < _ ∧ c'.nreg 84011 < _ ∧ c'.nreg 84010 ≠ c'.nreg 84011
    rw [hn, v10, v11]
    refine ⟨?_, Nat.mod_lt _ by_omega, ?_⟩
    · split_ifs
      · exact prevV_lt by_omega
      omega
    · split_ifs
      · exact prevV_ne hn3 he
      · exact succ_ne by_omega he
  · have hmem := hole_mem (c := c') (j := 0) by_omega by_omega
    rw [a0] at hmem
    exact cover_unique hWs by_simp_all hp.1 hp.2.1 by_omega
      (fun h0 => by
        have hg : c₀.nreg 83006 = 0 := by
          zufzq
          · zubh
          simp_all
        rw [v10, v11, ite_eq_left hg] at hmem; zvmxq; tauto)
      (fun hpos => by
        have hg : c₀.nreg 83006 ≠ 0 := fun hg => by
          have : (interiorModel zta).param zta ⟨e, c₀.nreg 83006⟩ = 0 := by
            rw [hg]; rfl
          grind
        rw [v10, v11, ite_eq_right hg] at hmem; zvmxq; tauto) _
  · zudif
    zues

    obtain rfl : ztsle := by_simp_all
    rw [a0, v10, v11] at hkk
    by_cases hg0 : c₀.nreg 83006 = 0
    · rw [ite_eq_left hg0] at hkk
      have hv : vHole (interiorModel zta).W.n e = (⟨prevV P.n e, 0⟩, ztzir) := by
        zukvg
      refine near_vHole _ _ (by zvmxq; exact hn3) (by zvmxq; exact he) ?_ hp' h0 h1
        (by zvmyq; exact hkk)
      rw [hg0, ← Chazelle.Chain.sidePt_zero]; rfl
    · rw [ite_eq_right hg0] at hkk
      have hv : eHole (interiorModel zta).W.n e = (ztjy, ztzir) := by
        zukvg
      exact near_eHole _ zta by_simp_all ⟨_, hp.1, hp.2.1.le, rfl⟩ hp' h0 h1
        by_simp_all
theorem sOf_sideS {C : Chain} {b : ℕ} (hb : b = 1 ↔ C.sideBeta = true) :
    sOf C.m C.topIdx b = C.sideS C.sideBeta := by
  zumuk
theorem holeL_scr : ∀ r ∈ holeL, Scr r := by
  zuz
  zubes
  zumrj
set_option maxHeartbeats 1600000 in
/-- **The holes of the candidate in a chain model** (`chainH`): pairs of distinct walk vertices
covering the candidate point. -/
theorem holeS_chain (hE : TGood P W M N c₀) (hI : TInv W c₀ c) {C₀ : Chain}
    (hM₀ : M = chainModel C₀) :
    RS P W c₀ holeS c 100 (fun c' => HoleOut M zta c'
      ztypk ∧ Out c c' holeL) := by
  zuchl

  zudcv

  zubb
  zuet
  have hWm := hE.hWm C rfl
  have hz0 : c₀.nmem _ = 0 := (chainDesc_of hE.hMD rfl).1
  have g21 : ztsex := by rw [hI.h21, hI.h23, hz0]; omega
  -- the candidate
  zuiok
  obtain ⟨he6, hvtx, hedge⟩ := chain_x_cases hE.hxp hE.hxe hE.hxc (hE.hxC C rfl)
  have hxe : c₀.nreg 83005 < 2 * C.m + 7 := by_grind
  -- the descriptor words
  set B := c.nreg 83020 with hBdef
  zudqo
  have hBW : ztsam := by
    have := hwf.1; have := hI.hw.1 ALLOC; omega
  obtain ⟨c₁, k₁, hk₁, e₁, v97, v98, v99, v100, v101, v90, v96, v103, v104, o₁⟩ :=
    chainPre_exec (P := P) hI.hw (B := B) rfl hI.h23 hs2 hs3 rfl hBW hWm
  obtain ⟨c₂, k₂, hk₂, e₂, v102, o₂⟩ := sS_exec (P := P) e₁.wb_right v99 v100 v98
    (by zuonf; exact hI.h23)
  have hS : sOf C.m C.topIdx _ = C.sideS C.sideBeta := sOf_sideS hs4
  zugdk

  zubad
  have hi : c₀.nreg 83005 - 6 ≤ 2 * C.m := by_omega
  obtain ⟨c₃, k₃, hk₃, e₃, v106, o₃⟩ := jS_exec (P := P) e₂.wb_right (m := C.m) (i := c₀.nreg 83005 - 6) by_omega v102
    ztjqf ztlig hSle hi
    by_omega
  set j := (S + (c₀.nreg 83005 - 6)) % ztbb with hjdef
  zudhq
  -- registers carried to the branch

  have r05 : c₃.nreg 83005 = c₀.nreg 83005 := by zuoau
  have r06 : c₃.nreg 83006 = c₀.nreg 83006 := by zuoav
  have r22 : ztusm := by rw [o₁₃.1 _ by_decide, hI.h22]
  have r23 : ztusn := by rw [o₁₃.1 _ by_decide, hI.h23]
  have r100 : c₃.nreg 83100 = 2 * C.m := by zunmu
  have r102 : c₃.nreg 83102 = S := by zuoaw
  have r103 : c₃.nreg 83103 = 6 := by zunmv
  have r97 : c₃.nreg 83097 = C.m := by zunmw
  have r98 : c₃.nreg 83098 = C.topIdx := by zunmx
  have r101 : c₃.nreg 83101 = 7 := by zunmy
  have r96 : c₃.nreg 83096 = 2 := by zunmz
  have r90 : c₃.nreg 83090 = 2 * C.m + 7 := by zunna
  have hL₁₃ : ∀ r ∈ chainHL ++ [83102] ++ [83105, 83106], r ∈ holeL := by
    decide
  have hpos : (chainModel C).pos _ x =
      Chazelle.Chain.sidePt (chainModel C).W x.edge ztwte := rfl
  by_cases hh : c₀.nreg 83006 = 0
  · -- a tour vertex
    have g06 : ¬ c₃.nreg 83022 < c₃.nreg 83006 := by_omega
    obtain ⟨c₄, k₄, hk₄, e₄, w9, w10, w11, w12, w13, wtop, o₄⟩ := vtxH_exec (P := P)
      e₃.wb_right r97 r98 r100 r101 r96 r90 r103 r102 by_omega r23 hSle hj hWm
    have ex : ztpjo :=
      .ifLtN_true g21 (.seq e₁ ztjds)
    have ho : ztlxi := (o₁₃.trans o₄).mono (fun r hr => by
      simp only [holeL, chainHL, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr ⊢; omega)
    zuiew
    zuxy

    have h9 : c₄.nreg 84009 = 2 ∨ c₄.nreg 84009 = 3 := by zupaw; split_ifs <;> simp
    have m0 : ztzqx :=
      hole_mem (j := 0) by_omega by_omega
    have m1 : ztzqy :=
      hole_mem (j := 1) by_omega by_omega
    have va : vHole (chainModel C).W.n ztczc =
        ztbqt := by
      zugee
    have vb : vHole (chainModel C).W.n ztwsn =
        ztbqu := by
      zugef
    zumkl
    · zuhj
      · show c₄.nreg 84010 < _ ∧ c₄.nreg 84011 < _ ∧ c₄.nreg 84010 ≠ c₄.nreg 84011
        zugve

      · show c₄.nreg 84012 < _ ∧ c₄.nreg 84013 < _ ∧ c₄.nreg 84012 ≠ c₄.nreg 84013
        zugvf

      · have ht : ztmwe := by
          grind
        zuvf
        show c₄.nreg 84014 < _ ∧ c₄.nreg 84015 < _ ∧ c₄.nreg 84014 ≠ c₄.nreg 84015
        omega
    · zugr

      refine cover_chain_vertex hsimp hk by_grind by_grind
        ztefc _
      zuvf
      have h93 : c₄.nreg 84009 = 3 := by_grind
      have m2 : ztind ∈ ShotList.holeList c₄ 84000 :=
        hole_mem (j := 2) by_omega by_omega
      rw [hn, show 2 * C.m + 6 = 2 * C.m + 6 from rfl, vHole_six by_omega, t14, t15,
        Nat.mod_self] at *
      omega
    · zudif
      zukeb
      zugr

      zucn
      zuiur
      have za : ztykv := by
        zufnh
      have zb : ztbank := by
        zufni
      zues

      zubwm
      zuhj
      · have e : ShotList.holeAt c₄ 84000 0 =
            vHole (chainModel C).W.n ztczc := by rw [va]; rfl
        zurh
        zufsh
      · have e : ShotList.holeAt c₄ 84000 1 =
            vHole (chainModel C).W.n ztwsn := by rw [vb]; rfl
        zurh
        zufsi
      · have ht : ztmwe := by
          zuefj
        zuvf
        have e : ShotList.holeAt c₄ 84000 2 = vHole (chainModel C).W.n ztcc := by
          zuhlt
          show (ztind : WPos × WPos) = _
          grind
        zurh
        have e2m : ztyxz := by
          zugtm
        zudhd

        have ztop : ztyku := by
          zudfw
        zufsj
  · -- inside a tour edge
    zulkd
    have g06 : c₃.nreg 83022 < c₃.nreg 83006 := by_omega
    zufyf
    have hi2' : c₀.nreg 83005 - 6 < 2 * C.m := hi2
    have he6' : 6 ≤ c₀.nreg 83005 := he6
    obtain ⟨c₄, k₄, hk₄, e₄, w9, w10, w11, w12, w13, o₄⟩ := edgeH_exec (P := P)
      e₃.wb_right r100 v106 r102 r103 r23 r05 hj hSle by_omega hWm
    have ex : ztpjo :=
      .ifLtN_true g21 (.seq e₁ ztjdt)
    have ho : ztlxi := (o₁₃.trans o₄).mono (fun r hr => by
      simp only [holeL, chainHL, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr ⊢; omega)
    zuiew
    zucms

    have m0 : ztzqx :=
      hole_mem (j := 0) by_omega by_omega
    have m1 : ztzqy :=
      hole_mem (j := 1) by_omega by_omega
    zumkl
    · zuow
      · grind
      grind
    · have e1 : eHole (chainModel C).W.n (c₀.nreg 83005 - 6 + 6) =
          ztbqt := by
        unfold eHole
        rw [hn, w10, w11, Nat.mod_eq_of_lt by_omega, show c₀.nreg 83005 - 6 + 6 =
          c₀.nreg 83005 by omega]
      have e2 : eHole (chainModel C).W.n ztddp =
          ztbqu := by
        zuuc

      have hcov := cover_chain_edge hsimp hi2 hτ hτ1 ztmdg
        by_grind zta
      grind
    · zuhgi
      zues

      have hq' : q < min (c₄.nreg 84009) 3 := hq
      zufwo
      zuow
      · have e : ShotList.holeAt c₄ 84000 0 = eHole (chainModel C).W.n ztqke := by
          zujjr
          show (ztbqt : WPos × WPos) = _
          zugeg
        zurh
        exact near_eHole _ _ by_grind by_grind hp' h0 h1 hkk
      · have e2 : eHole (chainModel C).W.n ztddp =
            ztbqu := by
          zuuc

        have e : ShotList.holeAt c₄ 84000 1 =
            eHole (chainModel C).W.n ztddp := by
          zukvi
        zurh
        zufil
        rw [show c₀.nreg 83005 - 6 + 6 = c₀.nreg 83005 by omega] at a1 a2
        have zt : Chazelle.Chain.sidePt (chainModel C).W ztddp
            ztydj = (chainModel C).pos zta x := by
          show Geometry.lerp ztiez
            ztifa _ =
            Geometry.lerp ((chainModel C).wa ztqke) ((chainModel C).wb ztqke)
              _
          zukqa
          zudxm
        zugki

/-- **The holes of the candidate** (both models): pairs of distinct walk vertices covering the
candidate point; only the scratch registers `holeL` change. -/
theorem holeS_rs (hE : TGood P W M N c₀) (hI : TInv W c₀ c) :
    RS P W c₀ holeS c 100 (fun c' => HoleOut M zta c'
      ztypk ∧ Out c c' holeL) := by
  rcases hE.kind with ⟨-, C, hM⟩ | ⟨h1, hM, -⟩
  · exact holeS_chain hE hI hM
  · zulas
    exact (holeS_int hE hI h1).mono by_omega by_simp_all
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim SignK NFLoc ShotList ShotListG
open Chazelle.Geometry (lerp)

/-! ## Inner points of the interior model -/
variable {Q : Polygon} (C : Chain) {p : ℕ}
theorem iv_inj {p q : ℕ} (hp : p < Q.n) (hq : q < Q.n) (h : IOrc.iv Q p = IOrc.iv Q q) :
    p = q := by
  unfold IOrc.iv at h; grind

/-- **A point strictly inside an edge of the interior walk is an inner point** of the interior
model, when `Q` has distinct heights: its height is strictly between the heights of the edge's
ends, and its abscissa between theirs. -/
theorem innerPt_mi_edge (hD : DistinctHeights Q) (hn : 3 ≤ Q.n) {p h : ℕ}
    (hp : p < Q.n) (h0 : 0 < (interiorModel Q).param Q ztnk)
    (h1 : (interiorModel Q).param Q ztnk < 1) :
    (interiorModel Q).InnerPt ((interiorModel Q).pos Q ztnk) := by
  set t := (interiorModel Q).param Q ztnk
  have hq : ztymf := Nat.mod_lt _ by_omega
  have hne := succ_ne by_omega hp
  have hn' : ztbdm := IOrc.mi_n
  have va : (interiorModel Q).W.vtx p = Q.vtx _ := IOrc.iw_vtx hp
  have vb : (interiorModel Q).W.vtx _ = Q.vtx _ :=
    IOrc.iw_vtx hq
  have hy : ztkyy :=
    hD _ _ (IOrc.iv_lt hp) (IOrc.iv_lt hq) (fun e => hne (iv_inj hp hq e))
  have hz : (interiorModel Q).pos Q ztnk =
      lerp (Q.vtx ztsxz) (Q.vtx ztbare) t := by
    zueew
    zubi
    rw [IOrc.mi_wa hp, IOrc.mi_wb hp]
  zudur
  set a := Q.vtx ztsxz
  set b := Q.vtx ztbare
  unfold Model.InnerPt
  zubzm
  zujx
  · rcases lt_or_gt_of_ne hy with hab | hab
    · refine ztxrn
      · simp_all
      · zudvk
    · refine ztxro
      · zudvk
      · zukyz
  · rcases le_total a.1 b.1 with hab | hab
    · refine ztxrn
      · simp_all
      · zudvk
    · refine ztxro
      · zudvk
      · zukyz

/-! ## Walk points of a chain model lie between the vertical sides of the box -/
theorem chain_vtx_abs_fst (hp : p < (chainModel C).W.n) :
    |((chainModel C).W.vtx p).1| ≤ C.radius := by
  zuet
  zumch
  have htop := (C.abs_le_coordBound_of_mem_set C.top_mem_set).1.trans hR.le
  have hRp : 0 ≤ C.radius := by_grind
  zucn
  zugus
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ 6 ≤ p) with
    rfl | rfl | rfl | rfl | rfl | rfl | h6
  · tauto
  · zugbq
  · zukov
  · zugbr
  · zukos
  · tauto
  · zuii
    rw [C.sideWalk_vtx_tour _ by_omega, Chain.sideTour]
    exact (C.abs_le_coordBound_of_mem_set ztxuz).1.trans hR.le

/-- **A point of the walk of a chain model is within the vertical sides of the box.** -/
theorem chain_pos_abs_fst (Q : Polygon) {x : WPos}
    (he : x.edge < (chainModel C).W.n) (h0 : 0 ≤ (chainModel C).param Q x)
    (h1 : (chainModel C).param Q x ≤ 1) : |((chainModel C).pos Q x).1| ≤ C.radius := by
  have hn : ztixp := by_omega
  zueew
  simp only [Model.wa, Model.wb, Geometry.lerp_fst]
  have ha := abs_le.1 (chain_vtx_abs_fst C he)
  have hb := abs_le.1 (chain_vtx_abs_fst C ztzum)
  rw [abs_le]
  zueop

/-- **An inner point of a chain model**: a point of the walk strictly inside the height band of
the box. -/
theorem innerPt_chain_walk (Q : Polygon) {x : WPos}
    (he : x.edge < (chainModel C).W.n) (h0 : 0 ≤ (chainModel C).param Q x)
    (h1 : (chainModel C).param Q x ≤ 1) (hy : |((chainModel C).pos Q x).2| < C.radius) :
    (chainModel C).InnerPt ztte := by
  have hx := abs_le.1 (chain_pos_abs_fst C Q he h0 h1)
  have hy' := abs_lt.1 hy
  zuet
  zubbq

  refine ztbrc
  · simp_all
  · simp_all
  · simp_all
  simp_all

/-- **The box vertices are on the boundary of the height band**: walk vertices `0 … 5` of a
chain model are at height `± radius`. -/
theorem chain_box_vtx_abs (hp : p < 6) :
    |((chainModel C).W.vtx p).2| = C.radius := by
  have hR := (abs_nonneg _).trans
    ((C.abs_le_coordBound_of_mem_set C.top_mem_set).1.trans C.coordBound_lt_radius.le)
  zucn
  zugus
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl
  · rw [C.sideWalk_vtx_zero]; exact abs_of_nonneg hR
  · rw [C.sideWalk_vtx_one]; simp_all
  · rw [C.sideWalk_vtx_two]; simp_all
  · rw [C.sideWalk_vtx_three]; simp_all
  · rw [C.sideWalk_vtx_four]; simp_all
  · rw [C.sideWalk_vtx_five]; exact abs_of_nonneg hR

/-- **A position the tests compare**: a proper position inside the height band of the box (for
a chain model). -/
theorem posG_of_band {M : Model} {Q : Polygon} {n : ℕ} {x : WPos} (he : x.edge < M.W.n)
    (hp : ProperPos M Q n x)
    (hy : ∀ C : Chain, M = chainModel C → |(M.pos Q x).2| < C.radius) : PosG M Q n x := by
  refine ztkyn
  zulwd
  have hv : M.pos Q x = M.W.vtx x.edge := by
    obtain ⟨e, g⟩ := x
    zujpd
    zubvi
    show Geometry.lerp ztmbq ztmbr 0 = _
    simp [Geometry.lerp, Model.wa]
  have := hy C hM
  rw [hv, hM, chain_box_vtx_abs C by_omega] at this
  simp_all

/-! ## The arcs of the region are pieces of the shot -/
section arcs
variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ : Config}

/-- **One end of an arc record**, normalised: a normalised position on a walk edge, a vertex or
an inner point. -/
theorem TGood.end_ok (hE : TGood P W M N c₀) {x : WPos}
    (hx : ProperPos M zta (Qof P).n x) (hk : M.key zta x < M.W.n)
    (hy : ∀ C : Chain, M = chainModel C → |(M.pos zta x).2| < C.radius) :
    NormPos M zta P.n ztznb ∧ (normOf M zta x).edge < M.W.n ∧
      ((normOf M zta x).hgt = 0 ∨ M.InnerPt (M.pos zta ztznb)) := by
  zuc
  zukta
  obtain ⟨hN, he, hpos, -, hcase⟩ := normOf_facts hx
  have hkey : M.key _ x = x.edge + M.param zta x := rfl
  have hxe : x.edge < M.W.n := by
    have : (x.edge : ℝ) < M.W.n := by zungt
    simp_all
  refine ztrct
  zuklc
  · omega
  right
  zudul
  have hp' : ztxsz := by
    zuhat
    · simp_all
    omega
  zubby
  · zulas
    exact innerPt_chain_walk C _ hxe hx.1 hx.2.1.le by_simp_all
  · zulas
    zuerr
    zubkw
    exact innerPt_mi_edge ztqcr hn3
      ztlgp hp' hx.2.1

/-- **The arcs of the region are pieces of the shot** of weight at most `γ`. -/
theorem TGood.arc_piece (hE : TGood P W M N c₀) (hne : (N.F M zta).Nonempty) {γ : ℕ}
    (hsg : M.Semigranular ztwiv γ) {t : ℕ}
    (ht : t < (N.region ztco).arcs.length) :
    PieceOK M zta P.n (nArc M zta N ztco t) ∧
      M.arcWt (M.key zta (nArc M zta N ztco t).1)
        (M.key zta (nArc M zta N ztco t).2) ≤ γ := by
  zuhol
  zugnb
  obtain ⟨-, -, -, reg, hRC, -, hArcs, -, -, -, hpp⟩ := hE.hNF
  set j := arcAt N r t with hjdef
  have hjm : ztgav := by
    rw [hjdef, arcAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
    simp
  obtain ⟨hj, -⟩ := (hArcs.2.2.2 r hr j).1 hjm
  zubjk

  have hs := hE.end_ok by_simp_all ha (hE.arc_abs hne hj).1
  have he := hE.end_ok by_simp_all hb (hE.arc_abs hne hj).2
  zuc
  have hps : ProperPos M zta P.n (N.arc j).s := by_simp_all
  have hpe : ProperPos M zta P.n (N.arc j).e := by_simp_all
  have hks := (normOf_facts hps).2.2.2.1
  have hke := (normOf_facts hpe).2.2.2.1
  refine ⟨⟨hs.1, he.1, hs.2.1, he.2.1, hs.2.2, he.2.2⟩, ?_⟩
  simp only [nArc]
  rw [hks, hke]
  exact (BoxT.arcWt_le_weight (hArcs.1 j hj).2).trans zttok
end arcs

/-! ## The shot block -/
section shot
variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-- The copies into the shot block `RS0 = 84000`: model descriptor, arc array (address, count),
origin (edge, height code), direction, weight bound, context. -/
def shL : List ztw := [ztsuj, ztsuk, ztsul, ztsum,
  ztsun, ztsuo, ztsup, ztsuq]

/-- **Filling the shot block** (the origin kind `2`: a walk position). -/
def shPrep : Stmt := .seq (block (SweepPrim.copies shL)) (.instr (.constN 84003 2))

/-- The registers `shPrep` writes. -/
def shW : List ℕ := [84000, 84001, 84002, 84003, 84004, 84005, 84006, 84007, 84008]
theorem shW_scr : ∀ r ∈ shW, Scr r := by
  intro r hr; simp only [shW, List.mem_cons, List.not_mem_nil, or_false] at hr; unfold Scr; omega
theorem shPrep_rs (hE : TGood P W M N c₀) (hI : TInv W c₀ c) :
    RS P W c₀ shPrep c 9 (fun c' => (∀ p ∈ shL, c'.nreg p.1 = c.nreg p.2) ∧
      c'.nreg 84003 = 2 ∧ Out c c' shW) := by
  obtain ⟨c₁, e₁, h1, h2, h3, h4, h5, h6⟩ := SweepPrim.copies_exec (P := P) shL c hI.hw
    by_decide
    by_decide
  obtain ⟨c₂, e₂, v₂, o₂⟩ := out_instr (P := P) (Exec.constN e₁.wb_right 84003 2 (by
    have := hE.hW; unfold hostWords at this; omega))
  have o₁ : Out c c₁ shW := ⟨fun r hr => h2 r (by
    simp only [shW, shL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢; omega), h3, h4, h5, h6⟩
  have ho : Out c c₂ shW := (o₁.trans o₂).mono (fun r hr => by
    simp only [shW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega)
  refine RS.out hI shW_scr ztyv by_rfl ho ⟨fun p hp => ?_, v₂, ho⟩
  have hp1 : p.1 ≠ 84003 := by
    simp only [shL, List.mem_cons, List.not_mem_nil, or_false] at hp
    grind
  rw [o₂.1 _ by_grind, h1 p hp]

/-- **The precondition of the shot wrapper** at a configuration of the run whose shot block is
filled: model descriptor, arc array of the region (`arcBuild`), origin the candidate, direction,
weight bound, context (`shPrep`), and the holes of the candidate (`holeS`). -/
theorem shotPre_of {X : MemCtx} {Ok : Polygon → Model → Prop} (hE : TGood P W M N c₀)
    (hI : TInv W c₀ c) (hX : X.holds P c₀.nmem zthvz ztdq)
    (hcap : c₀.nreg 83003 ≤ X.cap P c₀.nmem zthvz) (hXl : X.CapLocal) (hOk : Ok P M)
    (hne : (N.F M zta).Nonempty) (hsg : M.Semigranular ztwiv ztqkd)
    {B : ℕ} (h00 : c.nreg 84000 = c₀.nreg 83000) (h01 : c.nreg 84001 = B)
    (h02 : c.nreg 84002 = (N.region ztco).arcs.length) (h03 : c.nreg 84003 = 2)
    (h04 : c.nreg 84004 = c₀.nreg 83005) (h05 : c.nreg 84005 = c₀.nreg 83006)
    (h07 : c.nreg 84007 = c₀.nreg 83003) (h08 : c.nreg 84008 = c₀.nreg 83004)
    (hB : B + 4 * (N.region ztco).arcs.length ≤ c.nreg ALLOC)
    (harr : ∀ j, j < (N.region ztco).arcs.length →
      ShotList.arcAt c.nmem B j = nArc M zta N ztco j)
    (hho : HoleOut M zta c ztypk) :
    ShotPreG X Ok RS0 P W M zthcy ztqdh c := by
  zugmr
  have hA := hI.hA
  have i00 : c.nreg 83000 = c₀.nreg 83000 := hI.hin _ by_norm_num by_norm_num
  zubxo
  rw [i00] at hMD hwf
  have hX' : X.holds P c.nmem _ _ :=
    X.mono _ _ _ _ _ hA ztgew
  have hcap' : X.cap P c.nmem _ = X.cap P c₀.nmem _ :=
    hXl _ _ _ _ _ hm hX
  have hreg : HReg P c.nmem _ :=
    hreg_keep hE.hwfMD hE.hMD hE.hreg hm
  zuiok
  have hyR : YR M (M.pos _ x).2 := fun C hM =>
    lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set ztjxg).2 C.coordBound_lt_radius
  -- the origin is a vertex or an inner point
  have horig : (∃ q, Origin.walk x = .walk ztkmm) ∨ (M.InnerPt ((Origin.walk x).eval M zta) ∧
      ∀ y, Origin.walk x = .walk y → ProperPos M zta P.n y) := by
    rcases hE.hxc with h0 | hp
    · simp_all
    right
    refine ⟨?_, fun y hy => by cases hy; exact hE.hxp⟩
    show M.InnerPt (M.pos _ x)
    zubby
    · zulas
      exact innerPt_chain_walk C _ hE.hxe hE.hxp.1 hE.hxp.2.1.le (hyR C rfl)
    · zulas
      zuc
      zuerr
      have he := hE.hxe
      rw [IOrc.mi_n] at he
      exact innerPt_mi_edge ztqcr hn3 he hp hE.hxp.2.1
  -- the holes
  obtain ⟨h9, hhl, hcov, -⟩ := hho
  have hv : ∀ g ∈ ShotList.holeList c 84000, g.1.hgt = 0 ∧ g.1.edge < M.W.n := by
    zubrf
    simp only [ShotList.holeList, List.mem_map, List.mem_range] at hg
    obtain ⟨j, hj, rfl⟩ := hg
    exact ⟨rfl, (hhl j by_simp_all).1⟩
  refine ⟨hE.hG, hE.hW, ?_, ?_, ?_, ?_, ?_, hI, hOk, ?_, h9, ?_, hhl, Origin.walk x,
    ⟨h03, h04, h05⟩, ⟨hE.hxe, hE.hxp.2.2⟩, horig, hyR, ?_⟩
  · show X.holds P c.nmem ztvje _; grind
  · show c.nreg 84007 ≤ X.cap P c.nmem ztvje; grind
  · show ModelDescWF P _ c.nmem ztqil; grind
  · show ModelDescAt c.nmem ztqil _ M; grind
  · show HReg P c.nmem ztqil; grind
  · show c.nreg 84001 + 4 * c.nreg 84002 ≤ c.nreg ALLOC; omega
  · zun
    change j < c.nreg 84002 at hj
    rw [h02] at hj
    show PieceOK M _ P.n (ShotList.arcAt c.nmem ztqim j) ∧
      M.arcWt (M.key _ (ShotList.arcAt c.nmem ztqim j).1)
        (M.key _ (ShotList.arcAt c.nmem ztqim j).2) ≤ c.nreg 84007
    rw [h01, harr j hj, h07]
    exact hE.arc_piece hne hsg hj
  · exact avoid_of_cover hcov hv _ _ _
end shot

/-! ## The arrival step -/
variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-- The copies of the arrival step: descriptor, returned position, reversed direction code. -/
def arrL : List ztw := [ztgzg, ztnhi, ztnhk, ztsto]

/-- The arrival step in a chain model. -/
def tArrC : Stmt := .seq (.instr (.subN 83120 83023 83008)) (.seq (.seq (block (copies arrL))
  SweepPrim.arrivalPos) (.seq (.instr (.copyN 83012 50211)) (.instr (.copyN 83013 50212))))

/-- **The arrival step**: in a chain model, the arrival position of the hit point. -/
def tArr : Stmt := .ifLtN 83021 83023 tArrC .skip
theorem rho_dir {v : ℕ} (hv : v ≤ 1) : -dirOf (1 - v) = dirOf v := by
  have : 1 - v = if v = 1 then 0 else 1 := by_grind
  rw [this, SweepPrim.neg_dirOf_flip]

/-- **The arrival step.**  From a proper position `f` (registers `83012`, `83013`) of a point at
which, in a chain model, an arrival position of the ray exists: in a chain model the registers
hold an arrival position of the same point afterwards; in the interior model they are unchanged.
Only `83012`, `83013`, `83120` of band `bRestore` change. -/
theorem tArr_rs (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hp : ProperPos M zta P.n ztbfl) (he : c.nreg 83012 < M.W.n)
    (hy : ∀ C : Chain, M = chainModel C →
      |(M.pos (Qof P) ⟨c.nreg 83012, c.nreg 83013⟩).2| < C.radius)
    (hex : ∀ C : Chain, M = chainModel C → ∃ p t, Sweep.Arrival M.W
      ztxkh ztjs p t)
    (hroom : c.nreg ALLOC + 35000 ≤ W) :
    RS P W c₀ tArr c 35012 (fun c' =>
      ProperPos M zta P.n ztha ∧ c'.nreg 83012 < M.W.n ∧
      M.pos zta ztha = M.pos zta ztbfl ∧
      (∀ C : Chain, M = chainModel C → Sweep.Arrival M.W
        ztxkh ztjs ztfgi
        ztwzk) ∧
      ztxie ∧
      Agr c c' [83012, 83013, 83120]) := by
  rcases hE.kind with ⟨h0, C₀, hM₀⟩ | ⟨h1, hMi, -⟩
  · -- a chain model
    have g21 : ztsex := by rw [hI.h21, hI.h23, h0]; omega
    zuchl

    have h8 : ztsew := hI.hin _ by_norm_num by_norm_num
    zumff
    -- ρ = 1 - σb
    obtain ⟨c₁, e₁, v₁, o₁⟩ := out_instr (Exec.subN hI.hw 83120 83023 83008)
    obtain ⟨hI₁, rf₁⟩ := hI.regs e₁.wb_right (fun r hr => o₁.1 r (by
      grind)) o₁.2.1 o₁.2.2.1 o₁.2.2.2.1 o₁.2.2.2.2 (k := 1)
    have k₁ : ∀ r, r ≠ 83120 → c₁.nreg r = c.nreg r := fun r hr => o₁.1 r by_simp_all
    have r120 : c₁.nreg 83120 = 1 - c₀.nreg 83008 := by rw [v₁, hI.h23, h8]
    have hA₁ : ztdc := k₁ _ by_decide
    have hC₁ : ChainDescAt c₁.nmem ztmib zta H C := by
      rw [o₁.2.2.1, k₁ 83020 by_norm_num]; exact hC
    have hwf₁ : ChainWF P ztbmq c₁.nmem ztmib := by
      rw [hA₁, o₁.2.2.1, k₁ 83020 by_norm_num]; omega
    have f12 : c₁.nreg 83012 = c.nreg 83012 := by_simp_all
    have f13 : c₁.nreg 83013 = c.nreg 83013 := by_simp_all
    obtain ⟨c₂', c₂, k₂, q, -, -, ex₂, hk₂, hout, hf₂⟩ := callPrim SweepPrim.arrivalPos_meets arrL
      by_decide
      by_decide by_decide by_decide e₁.wb_right hE.hG hE.hW
      hwf₁ hC₁ (fun c' h1 _ _ => by
        have q1 := h1 ztnhi by_decide
        have q2 := h1 ztnhk by_decide
        zuhqe
        refine ⟨ztram, ?_, ?_⟩
        · grind
        · omega
        · exact hE.hWm C rfl) by_omega
    have q1 := q ztnhi by_decide
    have q2 := q ztnhk by_decide
    have q3 := q ztsto by_decide
    zulan
    unfold SweepPrim.ArrOut SweepPrim.ArrRes at hout
    rw [q1, q2, q3, f12, f13, r120, rho_dir hσ] at hout
    obtain ⟨hfl, hyes, hno⟩ := hout
    have hflag : zture := by
      grind
    obtain ⟨hpe, hpp, harr⟩ := hyes hflag
    have T₂ := hI₁.prim ex₂.wb_right hf₂
    -- copy the arrival position back
    obtain ⟨c₃, e₃, v₃, o₃⟩ := out_instr (Exec.copyN ex₂.wb_right 83012 50211)
    obtain ⟨hI₃, rf₃⟩ := T₂.1.regs e₃.wb_right (fun r hr => o₃.1 r (by
      grind)) o₃.2.1 o₃.2.2.1 o₃.2.2.2.1 o₃.2.2.2.2 (k := 1)
    obtain ⟨c₄, e₄, v₄, o₄⟩ := out_instr (Exec.copyN e₃.wb_right 83013 50212)
    obtain ⟨hI₄, rf₄⟩ := hI₃.regs e₄.wb_right (fun r hr => o₄.1 r (by
      grind)) o₄.2.1 o₄.2.2.1 o₄.2.2.2.1 o₄.2.2.2.2 (k := 1)
    have w12 : c₄.nreg 83012 = c₂.nreg 50211 := by rw [o₄.1 _ by_simp, v₃]
    have w13 : c₄.nreg 83013 = c₂.nreg 50212 := by rw [v₄, o₃.1 _ by_simp]
    refine ⟨c₄, 1 + (k₂ + ztcse) + 1,
      .ifLtN_true g21 (.seq e₁ (.seq ex₂ ztfml)), ?_, hI₄,
      ((rf₁.trans (T₂.2.1.trans (rf₃.trans rf₄)))).mono subset_rfl by_omega, ?_⟩
    · simp [arrL] at hk₂; omega
    show _ ∧ _
    rw [w12, w13]
    refine ⟨hpp, hpe, harr.2.2.2.1, by_grind, fun h => absurd h
      zthgg, fun r h1 h2 hr => ?_⟩
    zvnvw at hr
    rw [o₄.1 r by_grind, o₃.1 r by_grind,
      T₂.2.2 r h1 h2, k₁ r hr.2.2]
  · -- the interior model: nothing to do
    zudmz
    refine RS.ifF g21 (RS.skip (K := 0) hI ⟨hp, he, rfl, fun C hC => absurd (hC.symm.trans hMi)
      zthgg, by_omega, Agr.refl _ _⟩) |>.mono
      by_omega ztb
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (sidePt SideAttach sideLeft)
open Chazelle.Visibility (rayPt)
open ShotList
variable {M : Model}

/-- **The arc points are off the domain.** -/
theorem hiSet_off (hGM : GoodModel M) (Q : Polygon) (m : ℕ → ℕ) (B K : ℕ) :
    hiSet M Q m B K ⊆ (M.D)ᶜ := by
  zuh
  simp only [hiSet, mem_iUnion] at hx
  obtain ⟨j, -, p, t, hp, h0, h1, -, rfl⟩ := hx
  exact (walkAx_of_goodModel hGM).trace p hp t h0 h1

/-- **The exit point is an arc point outside the holes.** -/
theorem exit_lo (hGM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {z : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hzD : z ∉ M.D) (hini : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ U)
    (htop : ∀ C : Chain, M = chainModel C → z.2 ≤ C.top.2) {m : ℕ → ℕ} {B K : ℕ}
    {hs : List ztqx}
    (harr : ∀ a b, M.IsArc F U a b →
      ∃ j < K, M.key Q (ShotList.arcAt m B j).1 = a ∧ M.key Q (ShotList.arcAt m B j).2 = b)
    (hnear : Near M Q hs z) {t₁ : ℝ} (ht₁ : 0 < t₁) (hout : rayPt z σ t₁ ∉ M.D) :
    ∃ T, 0 < T ∧ T ≤ t₁ ∧ rayPt z σ T ∉ M.D ∧ ztgnn ∧
      chordOf z σ T ∈ M.Adm ∧
      ztxeo ∧
      rayPt z σ T ∈ loSet M Q m B K hs := by
  obtain ⟨T, hT, hTt, hTD, hdomU, hadm, hatt, a, b, harc, hmem⟩ :=
    local_exit hGM hFam hU hσ hzD hini ht₁ hout htop
  refine ⟨T, hT, hTt, hTD, hdomU, hadm, hatt, ?_⟩
  obtain ⟨p, τ, hp, h0, h1, hk, hx⟩ := hmem
  obtain ⟨j, hj, hja, hjb⟩ := harr a b harc
  refine ⟨p, τ, hp, h0, h1, ⟨j, hj, by rw [hja, hjb]; exact hk⟩, fun g hg hin => ?_, hx⟩
  obtain ⟨p', hp', ⟨s₁, a1, a2, e1⟩, s₂, b1, b2, e2⟩ := hnear g hg p τ hp h0 h1 hin
  have hUfree : U ⊆ Chazelle.Chain.freeIn M.D F := Chazelle.Chain.regionsIn_subset hU
  have hdom : ∀ t, 0 < t → t < T → rayPt z σ t ∈ M.D := fun t h1 h2 => (hUfree (hdomU t h1 h2)).1
  exact no_common_edge ztqyo hσ hT hdom hp' a1 a2 b1 b2 e1
    (by zvnlz; exact hx.symm)

/-- **The first hit of the shot is the first exit of the ray.** -/
theorem firstHit_exit (hGM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {z : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hzD : z ∉ M.D) (hini : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ U)
    (htop : ∀ C : Chain, M = chainModel C → z.2 ≤ C.top.2) {m : ℕ → ℕ} {B K : ℕ}
    {hs : List ztqx}
    (harr : ∀ a b, M.IsArc F U a b →
      ∃ j < K, M.key Q (ShotList.arcAt m B j).1 = a ∧ M.key Q (ShotList.arcAt m B j).2 = b)
    (hnear : Near M Q hs z) {A : Set Point} (hlo : loSet M Q m B K hs ⊆ A)
    (hhi : A ⊆ hiSet M Q m B K) {t : ℝ} (hfh : FirstHit A z σ t) :
    rayPt z σ t ∉ M.D ∧ (∀ s, 0 < s → s < t → rayPt z σ s ∈ U) ∧ chordOf z σ t ∈ M.Adm ∧
      (∃ p t', SideAttach M.W (chordOf z σ t) p t' ∧ sidePt M.W p t' = rayPt z σ t) := by
  have hout : rayPt z σ t ∉ M.D := hiSet_off hGM Q m B K (hhi hfh.2.1)
  obtain ⟨T, hT, hTt, hTD, hdomU, hadm, hatt, hlo'⟩ :=
    exit_lo hGM hFam hU hσ hzD hini htop harr hnear hfh.1 hout
  have hTe : T = t := by
    rcases hTt.lt_or_eq with h | h
    · exact absurd (hlo hlo') (hfh.2.2 T hT h)
    omega
  simp_all

/-- **The shot hits** when the ray leaves the domain. -/
theorem not_noHit (hGM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {z : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hzD : z ∉ M.D) (hini : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ U)
    (htop : ∀ C : Chain, M = chainModel C → z.2 ≤ C.top.2) {m : ℕ → ℕ} {B K : ℕ}
    {hs : List ztqx}
    (harr : ∀ a b, M.IsArc F U a b →
      ∃ j < K, M.key Q (ShotList.arcAt m B j).1 = a ∧ M.key Q (ShotList.arcAt m B j).2 = b)
    (hnear : Near M Q hs z) {A : Set Point} (hlo : loSet M Q m B K hs ⊆ A) {t₁ : ℝ}
    (ht₁ : 0 < t₁) (hout : rayPt z σ t₁ ∉ M.D) : ¬ NoHit A z σ := by
  intro hno
  obtain ⟨T, hT, -, -, -, -, -, hlo'⟩ := exit_lo hGM hFam hU hσ hzD hini htop harr hnear ht₁ hout
  tauto

/-! ## The far end -/
variable {W : Polygon}
/-- **An attachment at the far end is an arrival position** of the ray. -/
theorem arrival_of_attach {z : Point} {σ T : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hT : 0 < T) {p : ℕ} {t : ℝ} (hA : SideAttach W ztcmu p t)
    (hw : sidePt W p t = rayPt z σ T) : Sweep.Arrival W ztxn σ p t := by
  obtain ⟨hp, h0, h1, -, r, hr, hsec⟩ := hA
  refine ⟨hp, h0, h1, hw, ?_⟩
  zudpr
  zubfj

  have hmem : rayPt ztxn (-σ) s ∈ chordOf z σ T := by
    rw [rayPt_back]; exact (mem_chordOf hσ hT.le).2 ⟨T - s, by_linarith, by_linarith, rfl⟩
  have hd : dist (rayPt ztxn (-σ) s) ztxn = s := Sweep.dist_rayPt _ hσ' hs.le
  have hne : rayPt ztxn (-σ) s ≠ sidePt W p t := by
    zunft; intro h; rw [h, dist_self] at hd; linarith
  zuiak
  rw [← hw] at hsl ⊢
  exact (Sweep.sideLeft_rayPt_iff W p t (-σ) one_pos hs).2 hsl

/-- **On a simple walk**, the chord is attached at the proper position of its far end. -/
theorem attach_far_simple (hW : W.Simple) {d : Set Point} {w : Point} {p p' : ℕ}
    {t t' : ℝ} (hA : SideAttach W d p t) (hw : sidePt W p t = w) (hp' : p' < W.n) (h0 : 0 ≤ t')
    (h1 : t' < 1) (hw' : sidePt W p' t' = w) : SideAttach W d p' t' := by
  obtain ⟨rfl, rfl⟩ := FactsInterior.pos_unique hW hA.1 hp' hA.2.1 hA.2.2.1 h0 h1 (hw.trans hw'.symm)
  exact hA

/-! ## The height code of a chord record -/

/-- **The parameter of a position from the height vertex.** -/
theorem param_code (M : Model) (Q : Polygon) {y : WPos} {h : ℕ}
    (hy : (M.pos Q y).2 = (Q.vtx h).2) : M.param Q ztrez = M.param Q y := by
  have hy' : (M.wa y.edge).2 + M.param Q y * ztjcd = (Q.vtx h).2 := by
    tauto
  show (if (M.wa y.edge).2 = (M.wb y.edge).2 then 0
    else ((Q.vtx h).2 - (M.wa y.edge).2) / ztjcd) = M.param Q y
  split_ifs with hz
  · obtain ⟨e, g⟩ := y
    cases g with
    | zero => rfl
    | succ g =>
      show 0 = (if (M.wa e).2 = (M.wb e).2 then 0 else _)
      rw [ite_eq_left hz]
  grind

/-- **The point of a position from the height vertex.** -/
theorem pos_code (M : Model) (Q : Polygon) {y : WPos} {h : ℕ}
    (hy : (M.pos Q y).2 = (Q.vtx h).2) : M.pos Q ztrez = M.pos Q y := by
  zueew
  rw [param_code M Q hy]
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim SignK NFLoc ShotList ShotListG
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- **A run step in the bands `B`.** -/
def RSB (B : Finset ℕ) (P : Polygon) (W : ℕ) (c₀ : Config) (s : Stmt) (c : Config) (K : ℕ)
    (Q : Config → Prop) : Prop :=
  ∃ c' k, Exec P W s c c' k ∧ k ≤ K ∧ TInv W c₀ c' ∧ RF B ztdq c c' k ∧ Q c'
variable {B : Finset ℕ} {a b : ℕ} {t e : Stmt} {M : Model} {R : ℕ} {E : Config → Prop}
theorem RSB.of_RS (hB : dBands ⊆ B) {s : Stmt} {K : ℕ} {Q : Config → Prop}
    (h : RS P W c₀ s c K Q) : RSB B P W c₀ s c K Q := by
  zuw
  exact ⟨c', k, ex, hk, hI, hrf.mono hB le_rfl, hq⟩
theorem RSB.mono {s : Stmt} {K K' : ℕ} {Q Q' : Config → Prop}
    (h : RSB B P W c₀ s c K Q) (hK : K ≤ K') (hQ : ∀ c', Q c' → Q' c') : RSB B P W c₀ s c K' Q' := by
  zuw
  exact zthmo
theorem RSB.seq {s t : Stmt} {K₁ K₂ : ℕ} {Q₁ Q₂ : Config → Prop}
    (h₁ : RSB B P W c₀ s c K₁ Q₁)
    (h₂ : ∀ c₁, TInv W c₀ c₁ → c₁.nreg ALLOC ≤ c.nreg ALLOC + K₁ → Q₁ c₁ →
      RSB B P W c₀ t c₁ K₂ Q₂) : RSB B P W c₀ (.seq s t) c (K₁ + K₂) Q₂ := by
  zudf
theorem RSB.ifT {K : ℕ} {Q : Config → Prop}
    (ht : c.nreg a < c.nreg b) (h : RSB B P W c₀ t c K Q) :
    RSB B P W c₀ ztva c ztnu Q := by
  zuw
  exact ztcou
theorem RSB.ifF {K : ℕ} {Q : Config → Prop}
    (ht : ¬ c.nreg a < c.nreg b) (h : RSB B P W c₀ e c K Q) :
    RSB B P W c₀ ztva c ztnu Q := by
  zuw
  exact ztcov
theorem RSB.skip {K : ℕ} {Q : Config → Prop} (hI : TInv W c₀ c) (hq : Q c) :
    RSB B P W c₀ .skip c K Q :=
  ⟨c, 0, .skip hI.hw, by_omega, hI, RF.refl c 0, hq⟩

/-! ## Larger cost bounds -/
theorem KeyG.mono {kc : ℕ → ℕ → ℕ → ℕ → Stmt}
    {Bk : ℕ → Bool} {K K' : ℕ} (h : KeyG P W M R E kc Bk K) (hK : K ≤ K') :
    KeyG P W M R E kc Bk K' := by
  zucxc
  obtain ⟨c', k, ex, hk, b1, f⟩ := h a b d e ha hb hd he c hw hctx hx hxe hx0 hy hye hy0
    by_omega
  grind
theorem XG.mono {Y : ℝ → Prop}
    {xc : ℕ → ℕ → ℕ → ℕ → Stmt} {Bx : ℕ → Bool} {K K' : ℕ} (h : XG P W M R E Y xc Bx K)
    (hK : K ≤ K') : XG P W M R E Y xc Bx K' := by
  zucxb
  obtain ⟨c', k, ex, hk, b1, f⟩ := h a b d e ha hb hd he c hw hctx hp1 he1 hp2 he2 hyy hY
    by_omega
  grind

/-! ## The shot -/

/-- The cost bound of the operations of the test's shot. -/
def shK : ℕ := 34000

/-- **The shot of the candidate test** as a run step: the wrapper's postcondition; the band
`bRestore` below the shot block is unchanged. -/
theorem shot_rsb {N : NF} {X : MemCtx} {Ok : Polygon → Model → Prop}
    {sh : Stmt} {Bs Bo : Finset ℕ} {F : ℕ → ℕ} (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ Bo) (hXl : X.CapLocal) (hB8 : bRestore ∉ Bo)
    (hBo : oracleBands ⊆ Bo) (hpre : ShotPreG X Ok RS0 P W M zthcy ztqdh c)
    (hroom : c.nreg ALLOC + shotCostG ztpyi shK ztvjd ≤ W) :
    RSB ztjtu P W c₀ ztqwg c
      (shotCostG ztpyi shK ztvjd)
      (fun c' => ShotPost RS0 P c c' ∧ ∀ q, 80000 ≤ q → q < 84000 → c'.nreg q = c.nreg q) := by
  have hRB : bandOf RS0 ∉ Bo := by_tauto
  obtain ⟨c', k, ex, hk, hpost, fT⟩ := shotListG_execR hsh hBs hXl regsOK_RS0 hRB hBo
    (stable_tinv hB8) (KeyG.mono (gKey_keyG hE) by_decide) opW_BgK
    (XG.mono (xcR_xG hE) by_rfl) opW_BxR c hI.hw hpre hroom
  zudev
  have keep : zthoz := fun q h1 h2 =>
    r₁ q ztlgv ztu ztqgg
  have hI' : TInv W c₀ c' := by
    refine ⟨ex.wb_right, fun q h1 h2 => by zuogb; exact hI.hin q h1 h2,
      le_trans hI.hA a₁, fun a ha => by zunkw; exact hI.hm a ha,
      by zumyo; exact hI.h20,
      by zumyo; exact hI.h21,
      by zumyo; exact hI.h22,
      by zumyo; exact hI.h23⟩
  have hb8 : bRestore ∈ dBands := by_decide
  have hblk : ∀ r, (RS0 ≤ r ∧ r < RS0 + 300) → bandOf r ∈ dBands ∪ Bo := by
    intro r h
    unfold RS0 at h
    refine Finset.mem_union_left _ ?_
    rw [band8 by_omega by_omega]
    omega
  refine ⟨c', k, ex, hk, hI', ⟨fun r hr ha => r₁ r ztloa ha
    ztlob,
    fun r hr => rr₁ r ztloa ztlob,
    fun a ha => m₁ a (by have := hI.hA; omega), fun a ha => rm₁ a (by have := hI.hA; omega),
    o₁, a₁, b₁⟩, hpost, keep⟩
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim
variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-- Set the flag `r` if `50210 = 1`. -/
def setIf1 (r : ℕ) : Stmt := .ifLtN 50210 83023 .skip (.ifLtN 83023 50210 .skip ztwdp)
theorem setIf1_rs {r : ℕ} (hr : Scr r) (hI : TInv W c₀ c) :
    RS P W c₀ (setIf1 r) c 5 (fun c' => FlagUpd c c' r (c.nreg 50210 = 1)) := by
  zuglc
  unfold setIf1
  by_cases a : c.nreg 50210 < 1
  · zulxi
  · by_cases b : 1 < c.nreg 50210
    · exact RS.ifF by_omega (RS.ifT by_omega ztocv)
    · exact RS.ifF by_omega (RS.ifF by_omega (leaf_set hI hr le_rfl by_omega))

/-- If the flag `f` is set, run the turning test `t` and record a positive turn in `83052`. -/
def condTurn (f : ℕ) (t : Stmt) : Stmt := .ifLtN f 83023 .skip (.seq t (setIf1 83052))
theorem condTurn_rs {f : ℕ} {t : Stmt} {Kt : ℕ} {turn : Prop}
    (ht : ∀ c, TInv W c₀ c → c.nreg ALLOC + Kt ≤ W →
      ∃ c' k, Exec P W t c c' k ∧ k ≤ Kt ∧ (c'.nreg 50210 = 1 ↔ turn) ∧ TStep W c₀ c c' k)
    (hI : TInv W c₀ c) (hf : c.nreg f ≤ 1) (hroom : c.nreg ALLOC + Kt ≤ W) :
    RS P W c₀ (condTurn f t) c ztnmb (fun c' => FlagUpd c c' 83052 (c.nreg f = 1 ∧ turn)) := by
  zuglc
  unfold condTurn
  by_cases a : c.nreg f < 1
  · zulxi
  · refine RS.ifF by_omega (RS.seq (RS.op (ht c hI hroom)) fun c₁ hI₁ _ ⟨v₁, h8₁⟩ =>
      (setIf1_rs by_trivial hI₁).mono le_rfl fun c₂ ⟨u1, u2, a₂⟩ => ?_)
    have e52 : c₁.nreg 83052 = c.nreg 83052 := by_simp_all
    refine ⟨?_, by_omega, (Agr.of_band h8₁ []).trans a₂⟩
    grind

/-- **The vertex case**: an arc begins (ends) at the vertex with a positive turn, and no exit
chord leaves the vertex in the direction. -/
def vertexCase (kc : ℕ → ℕ → ℕ → ℕ → Stmt) (tn tp : Stmt) : Stmt :=
  .seq (.instr (.constN 83052 0)) (.seq (condTurn 83043 tn) (.seq (condTurn 83044 tp)
    (.ifLtN 83052 83023 .skip (.seq ztvqb (.ifLtN 83046 83023 ztwdn .skip)))))

/-- The cost bound of the vertex case. -/
def vertexK (Kk Kt D : ℕ) : ℕ := 1 + (ztnmb + (ztnmb + (exitScanK Kk D + 5)))

/-- The scratch registers of the validity check. -/
def validScr : List ℕ := [83010, 83030, 83031, 83032, 83033, 83034, 83035, 83036, 83037, 83038,
  83039, 83040, 83041, 83042, 83043, 83044, 83046, 83047, 83048, 83050, 83051, 83052]
variable {kc : ℕ → ℕ → ℕ → ℕ → Stmt} {Kk : ℕ}
theorem vertexCase_rs (hK : KeyOK kc Kk) {tn tp : Stmt}
    {Kt : ℕ} (hT : TurnOK tn tp Kt) (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hv : c₀.nreg 83006 = 0)
    (h10 : c.nreg 83010 = 0) (h43 : c.nreg 83043 ≤ 1) (h44 : c.nreg 83044 ≤ 1)
    (hroom : c.nreg ALLOC + vertexK Kk Kt (N.region ztco).chords.length ≤ W) :
    RS P W c₀ ztrya c (vertexK Kk Kt (N.region ztco).chords.length)
      (fun c' => c'.nreg 83010 ≤ 1 ∧
        (c'.nreg 83010 = 1 ↔ (ztyeg ∨
          ztyeh) ∧
          Clear M P N ztco ztfy ztbkn) ∧ Agr c c' validScr) := by
  zucwd
  unfold vertexCase vertexK
  refine RS.seq zthsa
    fun c₁ hI₁ hA₁ h₁ => ?_
  have q43 : c₁.nreg 83043 = c.nreg 83043 := by_simp_all
  have q44 : c₁.nreg 83044 = c.nreg 83044 := by_simp_all
  refine RS.seq (condTurn_rs (fun c h1 h2 => hT.1 P W M N c₀ c hE h1 h2) hI₁ by_omega
    zthfy) fun c₂ hI₂ hA₂ ⟨u1, u2, a₂⟩ => ?_
  have q44' : c₂.nreg 83044 = c.nreg 83044 := by
    rw [a₂ _ by_norm_num by_norm_num by_simp, q44]
  refine RS.seq (condTurn_rs (fun c h1 h2 => hT.2 P W M N c₀ c hE h1 hv h2) hI₂ by_omega
    zthfy) fun c₃ hI₃ hA₃ ⟨v1, v2, a₃⟩ => ?_
  have e52 : c₁.nreg 83052 = 0 := by_simp_all
  have ok : c₃.nreg 83052 = 1 ↔ (ztyeg ∨
      ztyeh) := by
    simp_all
  have ok1 := by_omega
  have a13 : Agr c c₃ [83052] := (((Agr.of_upd h₁).trans a₂).trans a₃).mono by_simp
  have e10 : ztusl := by rw [a13 _ by_norm_num by_norm_num by_simp, h10]
  zumbb
  by_cases hok : c₃.nreg 83052 < 1
  · refine (RS.ifT by_omega (RS.skip (K := 0) hI₃
      ⟨by_omega, ?_, a13.mono by_decide⟩)).mono by_omega (fun _ h => h)
    simp_all
  · refine RS.ifF by_omega ?_
    refine RS.seq (exitScan_rs hK hE hI₃ zthfy)
      fun c₄ hI₄ hA₄ ⟨b1, b2, a₄⟩ => ?_
    have e10' : ztusz := by rw [a₄ _ by_norm_num by_norm_num by_simp, e10]
    zumbd
    have hok' : c₃.nreg 83052 = 1 := by_omega
    have agr : Agr c c₄ validScr := (a13.trans a₄).mono by_decide
    by_cases hb : c₄.nreg 83046 < c₄.nreg 83023
    · refine (RS.ifT hb (RS.const hI₄ by_trivial
        hW1)).mono by_norm_num fun c' h' => ⟨by_simp_all, ?_, ?_⟩
      · simp_all
      · exact agr.trans ztpvs |>.mono by_decide
    · refine (RS.ifF hb (RS.skip (K := 0) hI₄
        ⟨by_omega, ?_, agr⟩)).mono by_omega (fun _ h => h)
      grind

/-- **The validity check.** -/
def validS (kc : ℕ → ℕ → ℕ → ℕ → Stmt) (ls tn tp : Stmt) : Stmt :=
  .seq (.instr (.constN 83010 0)) (.seq ztqxg (.seq (.instr (.copyN 83050 50210))
    (.ifLtN 83050 83023 .skip (.seq ls (.ifLtN 50210 83023 .skip (.seq ztvem
      (.ifLtN 83042 83023 (.ifLtN 83006 83023 ztrya .skip) ztwdn)))))))

/-- The cost bound of the validity check for a region with `A` arcs and `D` exit chords. -/
def validK (Kk Kl Kt A D : ℕ) : ℕ :=
  1 + (13 + (1 + ((Kl + (arcScanK Kk A + (vertexK Kk Kt D + 4) + 2)) + 2)))

/-- **Contract of the validity check**: `83010 = 1` iff `ValidB`. -/
theorem valid_rs (hK : KeyOK kc Kk) {ls : Stmt} {Kl : ℕ}
    (hL : LeftOK ls Kl) {tn tp : Stmt} {Kt : ℕ} (hT : TurnOK tn tp Kt)
    (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hroom : c.nreg ALLOC + validK Kk Kl Kt (N.region ztco).arcs.length
      (N.region ztco).chords.length ≤ W) :
    RS P W c₀ (validS kc ls tn tp) c (validK Kk Kl Kt (N.region ztco).arcs.length
      (N.region ztco).chords.length) (fun c' => c'.nreg 83010 ≤ 1 ∧
        ztxsb ∧
        Agr c c' validScr) := by
  zucwd
  unfold validS validK
  refine RS.seq zthsa
    fun c₁ hI₁ hA₁ h₁ => ?_
  refine RS.seq (RS.op (tRegLen_exec (f := 2) ztbt hE hI₁ zteqs))
    fun c₂ hI₂ hA₂ ⟨v₂, h8₂⟩ => ?_
  refine RS.seq zttbt
    fun c₃ hI₃ hA₃ h₃ => ?_
  have a₃ : Agr c c₃ [83010, 83050] :=
    (((Agr.of_upd h₁).trans ztrik).trans ztmai).mono by_simp
  have e50 : c₃.nreg 83050 = (N.region ztco).chords.length := by
    rw [h₃, upd_eq, v₂]; rfl
  have e10 : ztusl := by
    simp_all
  zumbb
  -- no exit chord: invalid
  by_cases hD0 : c₃.nreg 83050 < c₃.nreg 83023
  · refine (RS.ifT hD0 (RS.skip (K := 0) hI₃ ⟨by_omega, ?_, a₃.mono by_decide⟩)).mono by_omega
      ztb
    zummf
    refine ⟨by_simp_all, fun ⟨hne, _⟩ => ?_⟩
    simp_all
  refine RS.ifF hD0 ?_
  have hne : (N.region ztco).chords ≠ [] := by
    simp_all
  have hFne : ztxml := by
    obtain ⟨i, hi⟩ : ∃ i, i ∈ (N.region (c₀.nreg 83002)).chords := by
      rcases hl : (N.region _).chords with _ | ⟨a, l⟩
      · simp_all
      simp
    zuchj
    exact ⟨_, chord_toSet_mem' (((hregs _ hE.hr).1 i).1 hi).1⟩
  refine RS.seq (RS.op (hL P W M N c₀ c₃ hE hI₃ zteqs))
    fun c₄ hI₄ hA₄ ⟨bL, h8₄⟩ => ?_
  zumbd
  have a₄ : Agr c c₄ [83010, 83050] := (a₃.trans ztril).mono by_simp
  have e10' : ztusz := by_simp_all
  by_cases hL0 : c₄.nreg 50210 < c₄.nreg 83023
  · refine (RS.ifT hL0 (RS.skip (K := 0) hI₄ ⟨by_omega, ?_, a₄.mono by_decide⟩)).mono by_omega
      ztb
    rw [e10']
    refine ⟨by_simp_all, fun ⟨_, hl, _⟩ => ?_⟩
    have := bL.2.2 hl
    omega
  have hLt : LeftB M P _ _ := bL.2.1 (by have := bL.1; omega)
  refine RS.ifF hL0 ?_
  refine RS.seq (arcScan_rs hK hE hFne hI₄ zteqs)
    fun c₅ hI₅ hA₅ ⟨f1, f2, f3, i1, i2, i3, a₅⟩ => ?_
  have agr5 : Agr c c₅ validScr := (a₄.trans a₅).mono by_decide
  have e10'' : c₅.nreg 83010 = 0 := by
    rw [a₅ _ by_norm_num by_norm_num by_simp, e10']
  have h1'' := hI₅.h23
  have i6 := hI₅.hin 83006 by_norm_num by_norm_num
  -- the canonical code of the candidate
  have hz : M.param zta ztfy = 0 ↔ c₀.nreg 83006 = 0 := by
    constructor
    · zubww
      zufzq
      · zubh
      · exact absurd h0 ztvzp
    · zubww
      exact WalkKey.param_of_code_zero h0
  by_cases hin : c₅.nreg 83042 < c₅.nreg 83023
  · refine RS.ifT hin ?_
    have nIn : ¬ FIn M P N ztco ztfy := by_grind
    by_cases hv : c₅.nreg 83006 < c₅.nreg 83023
    · refine (RS.ifT hv (vertexCase_rs hK hT hE hI₅ by_omega e10'' f2 f3
        zteqs)).mono by_omega fun c' ⟨v1, v2, a'⟩ =>
        ⟨v1, ?_, agr5.trans a' |>.mono by_simp⟩
      rw [v2, i2, i3]
      unfold ValidB
      grind
    · refine (RS.ifF hv (RS.skip (K := 0) hI₅ ⟨by_omega, ?_, agr5⟩)).mono by_omega ztb
      rw [e10'']
      refine ⟨by_grind, fun ⟨_, _, h⟩ => ?_⟩
      grind
  · refine (RS.ifF hin (RS.const hI₅ by_trivial hW1)).mono
      by_omega fun c' h' => ⟨by zunqg, ?_, ?_⟩
    · zunqg
      zuhqc
      exact ⟨hne, hLt, by_grind⟩
    · exact (agr5.trans ztpvs).mono by_decide
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace DrvP
open Machine Machine.Stmt Programs SignK WalkKey
@[expose] public section
def gSetup : Stmt := block [.constN 170011 1, .constN 170012 0, .constN 170067 2,
  .addN 170056 218008 170067, .loadN 170016 170056, .addN 170056 170056 170011,
  .loadN 170017 170056]

/-- `170046 := a`, `170070 := a + m`, `170072 := a + ⌊m/2⌋`. -/
def gEnds : Stmt := block [.copyN 170046 218004, .addN 170070 218004 218002,
  .addN 170056 170017 218002, .loadN 170071 170056, .addN 170072 218004 170071]

/-- **The top of a long leaf** by the grade table. -/
def gTop : Stmt :=
  .seq gSetup (.seq gEnds (.seq (block [.copyN 170059 170072]) (.seq IOrc.cmpUpd
  (.seq (block [.copyN 170059 170070]) (.seq IOrc.cmpUpd
  (.seq ztkrv (.seq IOrc.topLoop
  (.seq ztkru (.seq IOrc.topLoop
  (block [.subN 218013 170046 218004]))))))))))

/-- The registers `gTop` writes. -/
def Bg (r : ℕ) : Bool := decide ztgxw || Bk r || r == 218013
theorem wr_gTop : wr Bg gTop = true := by
  rfl

/-! ## Execution -/
section exec
variable {P : Polygon} {W : ℕ} {O : OracleIface}
theorem tenv_upd {s : TSt} {c : Config} (h : TEnv P W O s c) {r₀ : ℕ} (v : ℕ)
    (hr : r₀ < 170000 ∨ 170030 ≤ r₀) (hA : r₀ ≠ ALLOC) :
    TEnv P W O s { c with nreg := upd c.nreg r₀ v } :=
  h.keep (fun r h1 h2 => by zvmwf; grind)
    by_simp_all (by zvmwf; grind)
theorem log_le_of_half {d μ : ℕ} (hμ : 1 ≤ μ) (hd : d ≤ 2 ^ ztfvs) :
    Nat.log 2 ztnfd ≤ μ := by
  have h2 : 2 * d ≤ 2 ^ μ := by
    have : ztyle := by
      zujmi
    omega
  calc Nat.log 2 _ ≤ Nat.log 2 _ := Nat.log_mono_right h2
    _ = μ := by_simp_all
theorem half_le {m μ : ℕ} (hμ : 1 ≤ μ) (hm : m ≤ 2 ^ μ) : m / 2 ≤ 2 ^ ztfvs ∧
    m - m / 2 ≤ 2 ^ ztfvs := by
  have : ztyle := by
    zujmi
  omega
set_option maxHeartbeats 1000000 in
/-- **The top of a long leaf** `v_a … v_{a+m}` (`1 ≤ μ`, `m ≤ 2^μ`, at least `μ` grades in the
table): `218013 := T ≤ m` with `v_{a+T}` at least as high as every vertex of the leaf. -/
theorem gTop_exec {s : TSt} (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hW : hostWords P.n ≤ W) (hmem : ∀ a, a < s.A₀ → c.nmem a = s.m₀ a)
    (hal : s.A₀ ≤ c.nreg ALLOC) (hgr : Robust s.A₀ s.m₀ ztfrr)
    (hh : c.nreg 218008 = s.h) {μ : ℕ} (hμ1 : 1 ≤ μ) (hμ : c.nreg 218002 ≤ 2 ^ μ)
    (hμΛ : μ ≤ s.m₀ s.h) (ham : c.nreg 218004 + c.nreg 218002 + 1 ≤ P.n) :
    ∃ c' k, Exec P W gTop c c' k ∧ k ≤ 1204 * μ + 600 ∧ FrameB Bg c c' ∧
      c'.nreg 218013 ≤ c.nreg 218002 ∧
      ∀ j, j ≤ c.nreg 218002 →
        IOrc.Y P (c.nreg 218004 + j) ≤ IOrc.Y P (c.nreg 218004 + c'.nreg 218013) := by
  have hlow := ShootCut.grade_low hgr
  zuhea
  zuixh
  zudwh
  set a := c.nreg 218004 with ha
  set m := c.nreg 218002 with hm
  have hmn : m ≤ P.n := by_omega
  have hhalf := (hgr.holds).2.2.1 m hmn
  have e2 : c.nmem _ = s.m₀ ztohm := hmem _ by_omega
  have e3 : c.nmem (s.h + 2 + 1) = s.m₀ ztkeo := by_simp_all
  -- 1. setup
  obtain ⟨c₁, k₁, e₁, hk₁, S₁, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W gSetup c c₁ k₁ ∧ k₁ = 7 ∧
      TEnv P W O s c₁ ∧ (∀ r, ztcau → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem := by
    unfold gSetup
    exec_block
    all_goals first | omega | skip
    · config_simp; omega
    · config_simp; omega
    refine ⟨rfl, ⟨hG, hW, by config_simp, by config_simp, ?_, ?_, fun a ha => ?_, ?_, hgr⟩,
      fun r hr => ?_, rfl⟩
    · simp_all
    · simp_all
    · simp_all
    · tauto
    · zufx
  zud
  have a₁ : c₁.nreg 218004 = a := by_simp_all
  have m₁' : ztuqf := by_simp_all
  have hm2 : c₁.nmem (s.m₀ ztkeo + m) = m / 2 := by
    simp_all
  -- 2. the ends and the middle
  obtain ⟨c₂, k₂, e₂, hk₂, S₂, v46, v70, v72, r₂, m₂⟩ : ∃ c₂ k₂, Exec P W gEnds c₁ c₂ k₂ ∧
      k₂ = 5 ∧ TEnv P W O s c₂ ∧ c₂.nreg 170046 = a ∧ c₂.nreg 170070 = a + m ∧
      c₂.nreg 170072 = a + m / 2 ∧ (∀ r, ztcau → c₂.nreg r = c.nreg r) ∧
      c₂.nmem = c.nmem := by
    unfold gEnds
    exec_block
    all_goals first | omega | skip
    · config_simp; omega
    · config_simp; rw [S₁.r17, m₁']; grind
    · config_simp; zunsc; omega
    refine ⟨rfl, S₁.keep ztpbv by_simp_all by_rfl, ?_, ?_, ?_,
      fun r hr => ?_, m₁⟩
    · zufx
    · simp_all
    · simp_all
    · config_simp; zunsc
    · zufx
  zue
  -- 3. the first comparison (the middle)
  obtain ⟨c₃, k₃, e₃, hk₃, h59, r₃⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 170059 170072]) c₂ c₃ k₃ ∧
      k₃ = 1 ∧ c₃.nreg 170059 = a + m / 2 ∧ c₃ = { c₂ with nreg := upd c₂.nreg 170059 (a + m / 2) } := by
    exec_block
    simp_all
  zubj
  have S₃ : TEnv P W O s c₃ := by zuodv; exact tenv_upd S₂ _ by_norm_num by_decide
  have c346 : c₃.nreg 170046 = a := by_simp_all
  obtain ⟨c₄, k₄, e₄, hk₄, u46, f₄, m₄⟩ := cmpUpd_exec c₃ w₃ S₃ by_omega
    by_omega
  rw [c346, h59] at u46
  zucc
  have S₄ : TEnv P W O s c₄ := S₃.keep by_grind
    by_grind (by rw [f₄ _ by_decide by_decide by_decide])
  have k₄' : ∀ r, ztcau → ztcu → c₄.nreg r = c.nreg r :=
    fun r h1 h2 => by
      rw [f₄ r by_omega by_omega h2, r₃]
      zugzs
  have c470 : c₄.nreg 170070 = a + m := by
    zudfs
  have c472 : c₄.nreg 170072 = a + m / 2 := by
    zudfs
  set v₄ := c₄.nreg 170046 with hv₄
  have hv₄G : a ≤ v₄ ∧ v₄ ≤ a + m := by rw [u46]; split_ifs <;> omega
  have hv₄Y := IOrc.Y_max_le (P := P) (a := a) (b := a + m / 2)
  rw [← u46] at hv₄Y
  -- 4. the second comparison (the end)
  have e₅ := IOrc.exec_copyN_upd (P := P) w₄ 170059 170070
  set c₅ : Config := { c₄ with nreg := upd c₄.nreg 170059 _ } with hc₅
  zuef
  have S₅ : TEnv P W O s c₅ := tenv_upd S₄ _ by_norm_num by_decide
  have c546 : c₅.nreg 170046 = v₄ := by_rfl
  have c559 : c₅.nreg 170059 = a + m := by zunbe; zumwv; omega
  obtain ⟨c₆, k₆, e₆, hk₆, u46', f₆, m₆⟩ := cmpUpd_exec c₅ w₅ S₅ by_omega
    by_omega
  rw [c546, c559] at u46'
  zujb
  have S₆ : TEnv P W O s c₆ := S₅.keep by_grind
    by_grind (by rw [f₆ _ by_decide by_decide by_decide])
  have k₆' : ∀ r, ztcau → ztcu → c₆.nreg r = c.nreg r :=
    fun r h1 h2 => by
      rw [f₆ r by_omega by_omega h2, hc₅]
      zugzs
  have c670 : c₆.nreg 170070 = a + m := by
    zudfu
  have c672 : c₆.nreg 170072 = a + m / 2 := by
    zudfu
  set v₆ := c₆.nreg 170046 with hv₆
  have hv₆G : a ≤ v₆ ∧ v₆ ≤ a + m := by rw [u46']; split_ifs <;> omega
  have hv₆Y := IOrc.Y_max_le (P := P) (a := v₄) (b := a + m)
  rw [← u46'] at hv₆Y
  have hm₆ : c₆.nmem = c.nmem := by_grind
  -- 5. the cover of `[a, mid]`
  obtain ⟨c₇, k₇, e₇, hk₇, x₇, y₇, r₇⟩ : ∃ c₇ k₇, Exec P W
      ztkrv c₆ c₇ k₇ ∧ k₇ = 2 ∧
      c₇.nreg 170050 = a ∧ c₇.nreg 170051 = a + m / 2 ∧
      c₇ = { c₆ with nreg := upd (upd c₆.nreg 170050 a) 170051 (a + m / 2) } := by
    exec_block
    refine ⟨rfl, by config_simp; rw [k₆' _ by_norm_num by_norm_num], by config_simp; omega,
      ?_⟩
    rw [k₆' _ by_norm_num by_norm_num, c672]
  zubgp
  have S₇ : TEnv P W O s c₇ := by
    zuovu; exact tenv_upd (tenv_upd S₆ _ by_norm_num by_decide) _ by_norm_num by_decide
  have c746 : c₇.nreg 170046 = v₆ := by zuovu; rfl
  have hcap : ∀ d, d ≤ 2 ^ ztfvs → d ≤ 2 ^ ztbwe := fun d hd =>
    hd.trans (Nat.pow_le_pow_right by_norm_num by_omega)
  have hhl := half_le hμ1 hμ
  obtain ⟨c₈, k₈, e₈, hk₈, S₈, g₈, n₈, cov₈, f₈, y₈, m₈⟩ := topLoop_exec
    (G := fun v => a ≤ v ∧ v ≤ a + m) c₇ w₇ S₇ x₇ y₇ by_omega by_omega
    zttng by_omega by_omega
    by_grind by_grind
    (fun v h1 h2 => ⟨h1, by_omega⟩)
  zujai
  have hk₈' : k₈ ≤ 602 * μ + 6 := by
    have := Nat.mul_le_mul_left 602 (log_le_of_half hμ1 (d := a + m / 2 - a) by_omega)
    omega
  have k₈' : ∀ r, ztcau → ztcu → c₈.nreg r = c.nreg r :=
    fun r h1 h2 => by
      rw [f₈ r by_omega h2, r₇]
      zugib
      exact k₆' r h1 h2
  have c870 : c₈.nreg 170070 = a + m := by
    zudjy
  have c872 : c₈.nreg 170072 = a + m / 2 := by
    zudjy
  set v₈ := c₈.nreg 170046 with hv₈
  -- 6. the cover of `[mid, a + m]`
  obtain ⟨c₉, k₉, e₉, hk₉, x₉, y₉, r₉⟩ : ∃ c₉ k₉, Exec P W
      ztkru c₈ c₉ k₉ ∧ k₉ = 2 ∧
      c₉.nreg 170050 = a + m / 2 ∧ c₉.nreg 170051 = a + m ∧
      c₉ = { c₈ with nreg := upd (upd c₈.nreg 170050 (a + m / 2)) 170051 (a + m) } := by
    exec_block
    refine ⟨rfl, by config_simp; omega, by config_simp; omega, ?_⟩
    grind
  zujaj
  have S₉ : TEnv P W O s c₉ := by
    zuovv; exact tenv_upd (tenv_upd S₈ _ by_norm_num by_decide) _ by_norm_num by_decide
  have c946 : c₉.nreg 170046 = v₈ := by zuovv; rfl
  have yv₆ : IOrc.Y P v₆ ≤ IOrc.Y P v₈ := by_grind
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, S₁₀, g₁₀, n₁₀, cov₁₀, f₁₀, y₁₀, m₁₀⟩ := topLoop_exec
    (G := fun v => a ≤ v ∧ v ≤ a + m) c₉ w₉ S₉ x₉ y₉ by_omega by_omega
    zttng by_grind by_omega
    by_grind
    by_grind
    (fun v h1 h2 => ⟨by_omega, h2⟩)
  zumfw
  have hk₁₀' : k₁₀ ≤ 602 * μ + 6 := by
    have := Nat.mul_le_mul_left 602 (log_le_of_half hμ1 (d := a + m - (a + m / 2)) by_omega)
    omega
  have k₁₀' : ∀ r, ztcau → ztcu →
      c₁₀.nreg r = c.nreg r := fun r h1 h2 => by
    rw [f₁₀ r by_omega h2, r₉]
    zugib
    exact k₈' r h1 h2
  set v₁₀ := c₁₀.nreg 170046 with hv₁₀
  have yv₈ : IOrc.Y P v₈ ≤ IOrc.Y P v₁₀ := by rw [← c946]; omega
  -- 7. the offset
  obtain ⟨c₁₁, k₁₁, e₁₁, hk₁₁, v13⟩ : ∃ c₁₁ k₁₁, Exec P W (block [.subN 218013 170046 218004])
      c₁₀ c₁₁ k₁₁ ∧ k₁₁ = 1 ∧ c₁₁.nreg 218013 = c₁₀.nreg 170046 - c₁₀.nreg 218004 := by
    exec_block
    simp
  have ex : Exec P W gTop c c₁₁ _ :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ (.seq e₉
      ztsqd))))))))
  have a₁₀ : c₁₀.nreg 218004 = a := k₁₀' _ by_norm_num by_norm_num
  rw [a₁₀] at v13
  refine ⟨_, _, ex, by_omega, exec_frameB ex wr_gTop, ?_, fun j hj => ?_⟩
  · rw [v13]; omega
  · rw [v13, show a + (v₁₀ - a) = v₁₀ by omega]
    by_cases hj2 : a + j ≤ a + m / 2
    · exact (cov₈ _ by_omega hj2).trans yv₈
    · exact cov₁₀ _ by_omega by_omega
end exec
end
end DrvP
end Chazelle.Core
namespace Chazelle.Core
namespace DrvP
open Machine Machine.Stmt Programs SignK WalkKey NFLoc
@[expose] public section
def pt (H : Host) (n i : ℕ) : SymPt := (H.pts n).getD i ztga

/-- The height of the host point `i`. -/
noncomputable def Yh (P : Polygon) (H : Host) (i : ℕ) : ℝ := ((pt H P.n i).eval zta).2
variable {H : Host} {n i : ℕ}
theorem pt_of_some {sp : SymPt} (h : ztmbe[i]? = some sp) :
    pt H n i = sp := by
  unfold pt; simp_all
theorem pt_lt (hwf : HostWF n H) (hn : 0 < n) (hi : i < (H.pts n).length) :
    (pt H n i).Lt n := by
  unfold pt
  zuhjy
  exact hostWF_pts hwf hn _ ztdyp

/-! ## The programs -/

/-- **The host count** and the constants. -/
def cntS : Stmt := .seq (block [.copyN 50060 218000]) (.seq cntStmt
  ztfxy)

/-- The first point of the piece into the best slot `218040`. -/
def scInit : Stmt := .seq (block [.copyN 50071 218001]) (.seq lookStmt
  (block [.copyN 218040 50046, .copyN 218041 50047, .copyN 218042 50048, .constN 218030 0,
    .constN 218031 1, .addN 218032 218002 218021]))

/-- The best slot takes the current point. -/
def scTake : Stmt := block [.copyN 218030 218031, .copyN 218040 218043, .copyN 218041 218044,
  .copyN 218042 218045]

/-- One point of the scan. -/
def scBody : Stmt := .seq (block [.addN 50071 218001 218031]) (.seq lookStmt
  (.seq zthtc
  (.seq (SweepPrim.kbit 218040 218043 218040 1 218046)
  (.seq ztprq (block [.addN 218031 218031 218021])))))

/-- **The scan.** -/
def scanS : Stmt :=
  .seq scInit (.seq (.whileLtN 218031 218032 scBody) (block [.copyN 218013 218030]))

/-- The registers written by the count and the scan. -/
def Bsc (r : ℕ) : Bool := decide ztgze || Bk r || decide (218012 ≤ r ∧ r < 218100)

/-- The registers written by the scan (finer than `Bsc`). -/
def Bscan (r : ℕ) : Bool :=
  Bhost r || Bk r || decide zttxr || decide (218030 ≤ r ∧ r < 218047)
theorem wr_cntS : wr Bsc cntS = true := by
  rfl
theorem wr_scBody : wr Bsc scBody = true := by
  rfl
theorem wr_scanS' : wr Bscan scanS = true := by
  rfl

/-! ## The count -/
section exec
variable {P : Polygon} {W : ℕ}

/-- **The host count.** -/
theorem cntS_exec (c : Config) (hw : WordsBounded W c) {H : Host}
    (hH : HostAt c.nmem ztjrx H) (haW : c.nreg 218000 + 3 * H.length + 4 ≤ W)
    (hN : (H.pts P.n).length ≤ W) (hW : 65 ≤ W) :
    ∃ c' k, Exec P W cntS c c' k ∧ k ≤ 12 * H.length + 17 ∧ FrameB Bsc c c' ∧
      c'.nreg 218012 = (H.pts P.n).length ∧ c'.nreg 218020 = 0 ∧ c'.nreg 218021 = 1 ∧
      c'.nreg 218022 = 65 ∧ HostEnv W ztjrx H.length c.nmem c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, h60, m₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 50060 218000]) c c₁ k₁ ∧
      k₁ = 1 ∧ c₁.nreg 50060 = c.nreg 218000 ∧ c₁.nmem = c.nmem := by
    exec_block
    simp
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, n₂, E₂⟩ := cnt_exec (P := P) (n := P.n) c₁ e₁.wb_right
    by_simp_all h60 haW hN
  zue
  obtain ⟨c₃, k₃, e₃, hk₃, v12, v20, v21, v22, E₃⟩ : ∃ c₃ k₃, Exec P W
      ztfxy
      c₂ c₃ k₃ ∧ k₃ = 4 ∧ c₃.nreg 218012 = (H.pts P.n).length ∧ c₃.nreg 218020 = 0 ∧
      c₃.nreg 218021 = 1 ∧ c₃.nreg 218022 = 65 ∧
      HostEnv W ztjrx H.length c.nmem c₃ := by
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, by_simp_all, by config_simp, by config_simp, by config_simp,
      ⟨by_omega, by config_simp; exact E₂.h60, by config_simp; exact E₂.h61, by config_simp; exact E₂.h67,
        by config_simp; exact E₂.h68, by config_simp; exact E₂.h69, ?_⟩⟩
    config_simp; rw [E₂.mem, m₁]
  have ex : Exec P W cntS c c₃ _ := .seq e₁ ztcr
  exact ⟨c₃, _, ex, by_omega, exec_frameB ex wr_cntS, v12, v20, v21, v22, E₃⟩

/-! ## The scan -/

/-- **The invariant of the scan** after the points `s, …, s + k - 1` (`k` in `218031`): the
best offset `218030 < k`, its point in the slot `218040`, at least as high as the points seen
and strictly higher than those before it. -/
structure ScI (P : Polygon) (W : ℕ) (H : Host) (m₀ : ℕ → ℕ) (HB s m : ℕ) (c : Config) : Prop where
  env : HostEnv W HB H.length m₀ c
  r01 : c.nreg 218001 = s
  r20 : c.nreg 218020 = 0
  r21 : c.nreg 218021 = 1
  r32 : c.nreg 218032 = m + 1
  k1 : 1 ≤ c.nreg 218031
  km : c.nreg 218031 ≤ m + 1
  bk : c.nreg 218030 < c.nreg 218031
  slot : SymPtIn c 218040 (pt H P.n ztlsy)
  le : ∀ j, j < c.nreg 218031 → Yh P H ztcoi ≤ Yh P H ztlsy
  lt : ∀ j, j < c.nreg 218030 → Yh P H ztcoi < Yh P H ztlsy

/-- The facts of the scan's environment. -/
structure ScE (P : Polygon) (W : ℕ) (H : Host) (m₀ : ℕ → ℕ) (HB : ℕ) : Prop where
  good : GoodEnv P
  hW : hostWords P.n ≤ W
  hH : HostAt m₀ HB H
  hwf : HostWF P.n H
  hl : H.length ≤ 64
  haW : HB + 3 * H.length + 4 ≤ W
variable {H : Host} {m₀ : ℕ → ℕ} {HB : ℕ}
theorem ScE.nW (h : ScE P W H m₀ HB) : P.n + 3 ≤ W := by
  have := h.hW; unfold hostWords at this; omega
theorem ScE.npos (h : ScE P W H m₀ HB) : 0 < P.n := by
  have := Chazelle.Jordan.simple_three_le h.good.1; omega
theorem ScE.hN (h : ScE P W H m₀ HB) :
    (H.pts P.n).length ≤ W := by
  have h1 := Host.pts_length_le h.hwf
  have := h.hW; unfold hostWords at this
  have : ztgak := Nat.mul_le_mul_right _ h.hl
  omega

/-- **One lookup** of the host point `p` into the slot `50046`. -/
theorem look_pt {HB p : ℕ} (E : ScE P W H m₀ HB) (c : Config)
    (hE : HostEnv W HB H.length m₀ c) (h71 : c.nreg 50071 = p) (hp : p < (H.pts P.n).length) :
    ∃ c' k, Exec P W lookStmt c c' k ∧ k ≤ 1733 ∧ FrameB Bhost c c' ∧
      HostEnv W HB H.length m₀ c' ∧ SymPtIn c' 50046 ztlrv := by
  obtain ⟨c', k, e, hk, F, E', -, sp, hsp, hin⟩ := look_exec (P := P) c hE h71 E.hH E.hwf
    (by have := E.nW; omega) E.haW E.hN hp
  rw [← pt_of_some hsp] at hin
  exact ⟨c', k, e, by have := E.hl; omega, F, E', hin⟩
theorem bhost_218 {r : ℕ} (h : 218000 ≤ r) : Bhost r = false := by
  simp only [Bhost, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
theorem bkb_218 {r d : ℕ} (h : 218000 ≤ r) (hd : r ≠ d) : SweepPrim.Bkb d r = false := by
  simp only [SweepPrim.Bkb, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne]; omega
set_option maxHeartbeats 2000000 in
/-- **One point of the scan.** -/
theorem scBody_exec {HB s m : ℕ} (E : ScE P W H m₀ HB)
    (hsm : s + m + 1 ≤ (H.pts P.n).length) (c : Config) (hI : ScI P W H m₀ HB s m c)
    (hlt : c.nreg 218031 < c.nreg 218032) :
    ∃ c' k, Exec P W scBody c c' k ∧ ScI P W H m₀ HB s m c' ∧ k ≤ 1990 ∧
      m + 1 - c'.nreg 218031 < m + 1 - c.nreg 218031 ∧ FrameB Bsc c c' := by
  have hw := hI.env.wb
  have hk := hI.km
  rw [hI.r32] at hlt
  obtain ⟨k, hkdef⟩ : ∃ k, c.nreg 218031 = k := by_simp_all
  obtain ⟨b, hbdef⟩ : ∃ b, c.nreg 218030 = b := by_simp_all
  rw [hkdef] at hk hlt
  -- the address
  obtain ⟨c₁, k₁, e₁, hk₁, v71, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W (block [.addN 50071 218001 218031])
      c c₁ k₁ ∧ k₁ = 1 ∧ c₁.nreg 50071 = s + k ∧ ztedg ∧
      c₁.nmem = c.nmem := by
    exec_block
    · config_simp; zuojh; have := E.hN; omega
    refine ⟨rfl, by config_simp; zuojh, fun r hr => ?_, rfl⟩
    simp_all
  have E₁ : zthof := ⟨e₁.wb_right, by zvmww; exact hI.env.h60,
    by zvmww; exact hI.env.h61, by zvmww; exact hI.env.h67,
    by zvmww; exact hI.env.h68, by zvmww; exact hI.env.h69,
    by zvmxn; exact hI.env.mem⟩
  -- the lookup
  zucds
  zue
  have k₂' : ztkon := fun r hr => by
    zugts
  -- the copy into the current slot
  obtain ⟨c₃, k₃, e₃, hk₃, s₃, r₃, m₃⟩ : ∃ c₃ k₃, Exec P W
      zthtc c₂ c₃ k₃ ∧ k₃ = 3 ∧
      SymPtIn c₃ 218043 (pt H P.n ztnj) ∧
      (∀ r, r ≠ 218043 → r ≠ 218044 → r ≠ 218045 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem := by
    exec_block
    refine ⟨rfl, symPtIn_copy s₂ (by config_simp) (by config_simp) (by config_simp),
      fun r h1 h2 h3 => ?_, rfl⟩
    simp_all
  zubj
  have k₃' : ∀ r, 218000 ≤ r → r ≠ 218043 → r ≠ 218044 → r ≠ 218045 → c₃.nreg r = c.nreg r :=
    by simp_all
  have sl := hI.slot
  rw [hbdef] at sl
  have sb₃ : SymPtIn c₃ 218040 _ := symPtIn_copy sl
    by_simp_all
    by_simp_all
    by_simp_all
  -- the height test
  have hlb : (pt H P.n ztkeh).Lt P.n := pt_lt E.hwf E.npos (by have := hI.bk; omega)
  have hlk : (pt H P.n ztnj).Lt P.n := pt_lt E.hwf E.npos by_omega
  obtain ⟨c₄, k₄, e₄, hk₄, F₄, b₄, t₄⟩ := SweepPrim.kbit_exec (P := P) E.good E.nW c₃ w₃
    (a := 218040) (b := 218043) (d := 218040) (op := 1) (dst := 218046) by_norm_num
    by_norm_num by_norm_num by_norm_num by_norm_num hlb hlk hlb sb₃ s₃ sb₃
  zvnhd at t₄
  zucc
  have k₄' := fun r h0 h1 =>
    F₄.1 r (bkb_218 h0 h1)
  have m₄ : c₄.nmem = m₀ := by rw [F₄.2.2.1, m₃]; exact E₂.mem
  have E₄ : HostEnv W HB H.length m₀ c₄ := by
    have g : ∀ r, 50060 ≤ r → r < 50070 → c₄.nreg r = c₂.nreg r := fun r h1 h2 => by
      rw [F₄.1 r (by simp only [SweepPrim.Bkb, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
        beq_eq_false_iff_ne]; omega), r₃ r by_omega by_omega by_omega]
    exact ⟨w₄, by zumwu; exact E₂.h60,
      by zumwu; exact E₂.h61,
      by zumwu; exact E₂.h67,
      by zumwu; exact E₂.h68,
      by zumwu; exact E₂.h69, m₄⟩
  have c420 : c₄.nreg 218020 = 0 := by
    rw [k₄' _ by_norm_num by_norm_num, k₃' _ by_norm_num by_norm_num by_norm_num
      by_norm_num]; exact hI.r20
  have c421 : c₄.nreg 218021 = 1 := by
    rw [k₄' _ by_norm_num by_norm_num, k₃' _ by_norm_num by_norm_num by_norm_num
      by_norm_num]; exact hI.r21
  have c431 : c₄.nreg 218031 = k := by
    simp_all
  have c430 : c₄.nreg 218030 = b := by
    simp_all
  have sk₄ : SymPtIn c₄ 218043 _ := symPtIn_copy s₃
    by_simp_all by_simp_all
    by_simp_all
  have sb₄ : SymPtIn c₄ 218040 _ := symPtIn_copy sb₃
    by_simp_all by_simp_all
    by_simp_all
  -- the decision
  obtain ⟨c₅, k₅, e₅, hk₅, b₅, s₅, r₅, m₅⟩ : ∃ c₅ k₅,
      Exec P W ztprq c₄ c₅ k₅ ∧ k₅ ≤ 6 ∧
      c₅.nreg 218030 = ztwux ∧
      SymPtIn c₅ 218040 (pt H P.n (s + ztwux)) ∧
      (∀ r, r ≠ 218030 → r ≠ 218040 → r ≠ 218041 → r ≠ 218042 → c₅.nreg r = c₄.nreg r) ∧
      c₅.nmem = c₄.nmem := by
    by_cases hc : c₄.nreg 218020 < c₄.nreg 218046
    · have hy : Yh P H _ < Yh P H _ := t₄.1 by_omega
      rw [ite_eq_left hy]
      zumju
      unfold scTake
      exec_block
      refine ⟨by_omega, by config_simp; omega, symPtIn_copy sk₄ (by config_simp)
        (by config_simp) (by config_simp), fun r h1 h2 h3 h4 => ?_, rfl⟩
      simp only [Config.nreg_mk, upd, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
    · have hy : ¬ Yh P H _ < Yh P H _ := fun h => hc (by
        rw [c420]; have := t₄.2 h; omega)
      rw [ite_eq_right hy]
      exact spec_ifLtN_false hc (spec_skip w₄ by_grind)
  zuef
  have k₅' : ∀ r, 218000 ≤ r → r ≠ 218030 → r ≠ 218040 → r ≠ 218041 → r ≠ 218042 →
      r ≠ 218043 → r ≠ 218044 → r ≠ 218045 → r ≠ 218046 → c₅.nreg r = c.nreg r :=
    by grind
  -- the next point
  obtain ⟨c₆, k₆, e₆, hk₆, v31, r₆⟩ : ∃ c₆ k₆, Exec P W (block [.addN 218031 218031 218021])
      c₅ c₆ k₆ ∧ k₆ = 1 ∧ c₆.nreg 218031 = k + 1 ∧
      c₆ = { c₅ with nreg := upd c₅.nreg 218031 (k + 1) } := by
    have e31 : c₅.nreg 218031 = k := by
      grind
    have e21 : c₅.nreg 218021 = 1 := by
      grind
    exec_block
    · config_simp; rw [e31, e21]; have := E.hN; omega
    refine ⟨rfl, by config_simp; omega, ?_⟩
    grind
  zujb
  have ex : Exec P W scBody c c₆ _ :=
    .seq e₁ ztfv
  have k₆' : ∀ r, 218000 ≤ r → r ≠ 218030 → r ≠ 218031 → r ≠ 218040 → r ≠ 218041 →
      r ≠ 218042 → r ≠ 218043 → r ≠ 218044 → r ≠ 218045 → r ≠ 218046 → c₆.nreg r = c.nreg r :=
    fun r h0 h1 h1' h2 h3 h4 h5 h6 h7 h8 => by
      zunrz; simp only [upd, ite_eq_right h1']; grind
  have E₆ : HostEnv W HB H.length m₀ c₆ := by
    have g : ∀ r, 50060 ≤ r → r < 50070 → c₆.nreg r = c₄.nreg r := fun r h1 h2 => by
      zunrz; simp only [upd, ite_eq_right (show r ≠ 218031 by omega)]
      exact r₅ r by_omega by_omega by_omega by_omega
    exact ⟨w₆, by zumwu; exact E₄.h60,
      by zumwu; exact E₄.h61,
      by zumwu; exact E₄.h67,
      by zumwu; exact E₄.h68,
      by zumwu; exact E₄.h69, by_grind⟩
  have v30 : c₆.nreg 218030 = ztwux := by
    zunrz; zvmwf; exact b₅
  have hbk := hI.bk
  rw [hkdef, hbdef] at hbk
  have hle := hI.le
  have hlt' := hI.lt
  rw [hkdef, hbdef] at hle
  rw [hbdef] at hlt'
  have kk : ∀ r, 218000 ≤ r → r < 218030 → c₆.nreg r = c.nreg r := fun r h0 h1 =>
    k₆' r h0 by_omega by_omega by_omega by_omega by_omega by_omega by_omega
      by_omega by_omega
  have I₆ : ScI P W H m₀ HB s m c₆ := by
    refine ⟨E₆, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [kk _ by_norm_num by_norm_num]; exact hI.r01
    · grind
    · grind
    · rw [k₆' _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
        by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num]; exact hI.r32
    · omega
    · omega
    · grind
    · zumpb
      exact symPtIn_copy s₅ zthez zthez
        zthez
    · rw [v30, v31]
      zun
      split_ifs with hy
      · grind
      grind
    · zumpb
      zun
      split_ifs at hj ⊢ with hy
      · grind
      grind
  refine ⟨c₆, _, ex, I₆, by_omega, by_omega, exec_frameB ex wr_scBody⟩

/-- **The scan**: `218013 := T ≤ m`, the least offset of a highest point among the host points
`s, …, s + m`. -/
theorem scanS_exec (E : ScE P W H m₀ HB) (c : Config)
    (hE : HostEnv W HB H.length m₀ c) (h20 : c.nreg 218020 = 0) (h21 : c.nreg 218021 = 1)
    (hsm : c.nreg 218001 + c.nreg 218002 + 1 ≤ (H.pts P.n).length) :
    ∃ c' k, Exec P W scanS c c' k ∧ k ≤ 1992 * c.nreg 218002 + 1750 ∧ FrameB Bscan c c' ∧
      HostEnv W HB H.length m₀ c' ∧ c'.nreg 218013 ≤ c.nreg 218002 ∧
      (∀ j, j ≤ c.nreg 218002 →
        Yh P H ztrlz ≤ Yh P H ztqhu) ∧
      (∀ j, j < c'.nreg 218013 →
        Yh P H ztrlz < Yh P H ztqhu) := by
  zuyv
  zumcu
  zuctb

  rw [hs, hm] at hsm ⊢
  -- the first point
  obtain ⟨c₁, k₁, e₁, hk₁, v71, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 50071 218001])
      c c₁ k₁ ∧ k₁ = 1 ∧ c₁.nreg 50071 = s ∧ ztedg ∧
      c₁.nmem = c.nmem := by
    exec_block
    simp_all
  have E₁ : zthof := ⟨e₁.wb_right, by zvmww; exact hE.h60,
    by zvmww; exact hE.h61, by zvmww; exact hE.h67,
    by zvmww; exact hE.h68, by zvmww; exact hE.h69,
    by zvmxn; exact hE.mem⟩
  zucds
  zue
  have k₂' : ztkon := fun r hr => by
    zugts
  obtain ⟨c₃, k₃, e₃, hk₃, I₃⟩ : ∃ c₃ k₃, Exec P W
      (block [.copyN 218040 50046, .copyN 218041 50047, .copyN 218042 50048, .constN 218030 0,
        .constN 218031 1, .addN 218032 218002 218021]) c₂ c₃ k₃ ∧ k₃ = 6 ∧
      ScI P W H m₀ HB s m c₃ := by
    exec_block
    all_goals first | omega | skip
    · config_simp; zunio; have := E.hN; omega
    refine ⟨rfl, ⟨⟨by_omega, by config_simp; exact E₂.h60, by config_simp; exact E₂.h61,
      by config_simp; exact E₂.h67, by config_simp; exact E₂.h68, by config_simp; exact E₂.h69,
      by config_simp; exact E₂.mem⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    all_goals config_simp
    all_goals first
      | omega
      | (rw [k₂' _ by_norm_num]; first | exact hs | exact h20 | exact h21)
      | (zunio)
      | (rw [Nat.add_zero]; exact symPtIn_copy s₂ (by config_simp) (by config_simp)
          (by config_simp))
      | (intro j hj; zunus)
      | (intro j hj; omega)
  zubj
  -- the loop
  obtain ⟨c₄, k₄, e₄, I₄, hx₄, hk₄⟩ := Exec.whileLtN_bounded (P := P) (W := W) (a := 218031)
    (b := 218032) (body := scBody) (ScI P W H m₀ HB s m) (fun d => m + 1 - d.nreg 218031) 1990
    (fun d hd => hd.env.wb) (fun d hd ht => by
      obtain ⟨d', k, e, I', hk, hμ, -⟩ := scBody_exec E hsm d hd ht
      grind) I₃
  have hk₄' : k₄ ≤ 1992 * m + 2 := by
    have := I₃.k1
    omega
  zucc
  have hx : c₄.nreg 218031 = m + 1 := by have := I₄.km; rw [I₄.r32] at hx₄; omega
  obtain ⟨c₅, k₅, e₅, hk₅, v13, r₅⟩ : ∃ c₅ k₅, Exec P W (block [.copyN 218013 218030]) c₄ c₅ k₅ ∧
      k₅ = 1 ∧ c₅.nreg 218013 = c₄.nreg 218030 ∧
      c₅ = { c₄ with nreg := upd c₄.nreg 218013 (c₄.nreg 218030) } := by
    exec_block
    simp
  have ex : Exec P W scanS c c₅ _ := .seq ztwrj ztgxe
  have hbk := I₄.bk
  zvnly at hbk
  refine ⟨c₅, _, ex, by_omega, exec_frameB ex wr_scanS', ?_, by_omega, fun j hj => ?_,
    fun j hj => ?_⟩
  · have E₄ := I₄.env
    zuef
    rw [r₅] at w₅ ⊢
    exact ⟨w₅, by zvmwf; exact E₄.h60, by zvmwf; exact E₄.h61,
      by zvmwf; exact E₄.h67, by zvmwf; exact E₄.h68,
      by zvmwf; exact E₄.h69, E₄.mem⟩
  · rw [v13]; exact I₄.le j by_omega
  · rw [v13] at hj ⊢; exact I₄.lt j hj
end exec
end
end DrvP
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
@[expose] public section
open Set
open Chazelle.Chain (sideE sideInArc)
open Chazelle.Visibility (rayPt)
variable {Q : Polygon}

/-! ## The chain of a stretch -/
theorem ch_vertex {u L : ℕ} {h1 : 1 ≤ L} {h2 : L + 1 ≤ Q.n} (k : ℕ) :
    (ch Q u L h1 h2).vertex k = Q.vtx ztkpj := rfl

/-! ## The vertex ranges of a chain -/

/-- The end of the first index range. -/
def rY1 (n cs L : ℕ) : ℕ := if cs + L < n then cs + L else n - 1

/-- The start of the second index range. -/
def rX2 (n cs L : ℕ) : ℕ := if cs + L < n then cs else 0

/-- The end of the second index range. -/
def rY2 (n cs L : ℕ) : ℕ := if cs + L < n then cs else cs + L - n

/-- The vertex indices of a chain of `L ≤ n - 1` edges from `cs`. -/
def InCh (n cs L v : ℕ) : Prop := ∃ k, k ≤ L ∧ v = ztfqq % n
theorem rng_of {n cs L k : ℕ} (hcs : cs < n) (hL : L < n) (hk : k ≤ L) :
    (cs ≤ ztfqq % n ∧ ztfqq % n ≤ rY1 n cs L) ∨
      (rX2 n cs L ≤ ztfqq % n ∧ ztfqq % n ≤ rY2 n cs L) := by
  unfold rY1 rX2 rY2
  by_cases h : cs + k < n
  · left; zvnnm; grind
  · right
    zul
    grind
variable {n cs L v : ℕ} {C : Chain} {A B : Set Point} {z : Point} {σ t : ℝ}
theorem of_rng1 (hcs : cs < n) (h1 : cs ≤ v) (h2 : v ≤ rY1 n cs L) :
    InCh n cs L v := by
  unfold rY1 at h2
  refine ⟨v - cs, by_grind, ?_⟩
  rw [show cs + (v - cs) = v by omega, Nat.mod_eq_of_lt by_grind]
theorem of_rng2 (hcs : cs < n) (hL : L < n) (h1 : rX2 n cs L ≤ v)
    (h2 : v ≤ rY2 n cs L) : InCh n cs L v := by
  unfold rX2 rY2 at *
  by_cases h : cs + L < n
  · zvnbq at h1 h2
    exact ⟨0, by_omega, by rw [Nat.add_zero, Nat.mod_eq_of_lt hcs]; omega⟩
  · zvnoi at h1 h2
    refine ⟨v + n - cs, by_omega, ?_⟩
    rw [show cs + (v + n - cs) = v + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
theorem rY1_lt {n cs L : ℕ} (hcs : cs < n) : rY1 n cs L < n := by
  zujqt
theorem rY2_lt {n cs L : ℕ} (hcs : cs < n) (hL : L < n) : rY2 n cs L < n := by
  unfold rY2; grind
theorem rX2_le {n cs L : ℕ} (_hcs : cs < n) (_hL : L < n) : rX2 n cs L ≤ rY2 n cs L := by
  zulut
theorem cs_le_rY1 {n cs L : ℕ} (hcs : cs < n) : cs ≤ rY1 n cs L := by
  zujqt
theorem rY1_sub {n cs L : ℕ} : rY1 n cs L - cs ≤ L := by
  zujqt
theorem rY2_sub {n cs L : ℕ} (hcs : cs < n) : rY2 n cs L - rX2 n cs L ≤ L := by
  zulut

/-! ## The top of the chain -/

/-- **The top index of the chain of a stretch** from its highest vertex `v` (distinct heights). -/
theorem topIdx_ch (hD : DistinctHeights Q) {u L : ℕ} {h1 : 1 ≤ L} {h2 : L + 1 ≤ Q.n}
    {v : ℕ} (hv : InCh Q.n ztllx L v)
    (hmax : ∀ k, k ≤ L → (Q.vtx ztkpj).2 ≤ (Q.vtx v).2)
    (hu : cStart Q u L < Q.n) :
    (ch Q u L h1 h2).topIdx = (v + Q.n - cStart Q u L) % Q.n ∧
      (cStart Q u L + (ch Q u L h1 h2).topIdx) % Q.n = v := by
  zugqf
  have hT : (ch Q u L h1 h2).topIdx = j :=
    topIdx_of_max (C := ch Q u L h1 h2) hD hj (fun k hk => by
      tauto)
  refine ⟨?_, by zvncs⟩
  zujik
  have hjn : ztsjp := by_omega
  by_cases h : cStart Q u L + j < Q.n
  · have e1 : ztpab % Q.n = cStart Q u L + j := Nat.mod_eq_of_lt h
    rw [e1, show cStart Q u L + j + Q.n - cStart Q u L = j + Q.n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hjn]
  · have e1 : ztpab % Q.n = cStart Q u L + j - Q.n := by
      zul
    rw [e1, show cStart Q u L + j - Q.n + Q.n - cStart Q u L = j by omega, Nat.mod_eq_of_lt hjn]

/-! ## The orientation bit -/

/-- The combination of the six sign tests giving the orientation bit (`BruteCorner.sideBeta_iff`)
for the vertices `A`, `T`, `B` before, at and after the top. -/
def BetaF (A T B : Point) : Prop :=
  (0 < det A T B ∧ T.1 < B.1 ∧ A.1 < T.1) ∨
    (¬ 0 < det A T B ∧ ¬ det A T B = 0 ∧ (T.1 < B.1 ∨ A.1 < T.1)) ∨
    (det A T B = 0 ∧ T.2 < B.2 ∧ T.1 < B.1) ∨ (det A T B = 0 ∧ B.2 < T.2)
theorem prev_idx {n s T : ℕ} (hn : 1 < n) (hT : 1 ≤ T) :
    (s + ztnpt) % n = (zttzf % n + n - 1) % n := sub_idx by_omega hT by_omega

/-- **The orientation bit of a chain of `Q`** (top not the first vertex), with the vertex indices
of `Q` taken modulo `n`. -/
theorem sideBeta_ch {C : Chain} (hC : C.P = Q) (hD : DistinctHeights Q) (hT0 : 0 < C.topIdx)
    {v : ℕ} (hv : v = ztwi % Q.n) :
    C.sideBeta = true ↔ BetaF (Q.vtx ztlda) (Q.vtx v) (Q.vtx ztbaax) := by
  have hDH : ztrfm := by_simp_all
  have hn : 1 < Q.n := by have := C.add_one_le; have := C.one_le; grind
  have eA : C.vertex ztbap = Q.vtx ztlda := by
    show C.P.vtx ((C.s + ztbap) % C.P.n) = _
    rw [hC, prev_idx hn hT0, hv]
  have eT : C.top = Q.vtx v := by
    show C.P.vtx ztbabc = _
    simp_all
  have eB : C.vertex ztbao = Q.vtx ztbaax := by
    show C.P.vtx ztymh = _
    rw [hC, hv, Nat.mod_add_mod, Nat.add_assoc]
  rw [Brute.sideBeta_iff (C := C) hDH hT0, eA, eT, eB]
  unfold BetaF
  constructor
  · grind
  · rintro (h | ⟨h1, h2, h3⟩ | h | h)
    · simp_all
    · grind
    · simp_all
    simp_all

/-! ## The boundary symbolic point of a hit, in closed form -/

/-- The tour start: `sideS`. -/
def sSV (β : Bool) (T L : ℕ) : ℕ := if β then T else 2 * L - T

/-- `j mod 2L` for `j < 6L`, by two conditional subtractions. -/
def mod2 (L j : ℕ) : ℕ :=
  if 2 * L ≤ ztdoq then ztdoq - 2 * L
  else ztdoq
theorem mod2_eq {L j : ℕ} (_hL : 1 ≤ L) (hj : j < 6 * L) : mod2 L j = j % ztbtk := by
  unfold mod2
  by_cases h1 : 2 * L ≤ j
  · zubel
    by_cases h2 : 2 * L ≤ j - 2 * L
    · rw [ite_eq_left h2, Nat.mod_eq_sub_mod h1, Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt by_omega]
    · rw [ite_eq_right h2, Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt by_omega]
  · rw [ite_eq_right h1, ite_eq_right h1, Nat.mod_eq_of_lt by_omega]

/-- The vertex index of `Q` at the walk vertex `6 + i` (`i ≤ 2L`) of the chain model. -/
def cVtxV (n cs L S i : ℕ) : ℕ :=
  (cs + sideE L (mod2 L ztbat)) % n
theorem cVtx_ch {i : ℕ} (hi : i ≤ 2 * C.m) :
    cVtx C ztcy = cVtxV C.P.n C.s C.m ztiao i := by
  unfold cVtx cVtxV Chain.sideIdx
  zuwi
  zubt
  have hS : C.sideS C.sideBeta = sSV C.sideBeta C.topIdx C.m := by
    rfl
  rw [show i + 6 - 6 = i by omega, hS, mod2_eq hm (by unfold sSV; grind)]

/-- **The boundary symbolic point of a chain-model position**, in closed form (`v` the top vertex
of `Q`, `S` the tour start). -/
noncomputable def hitSymV (n cs L S v e h : ℕ) : SymPt := by
  classical
  exact if e < 6 ∨ 2 * L + 6 ≤ e then .vtx v
    else if h = 0 ∨ h - 1 = cVtxV n cs L S ztbcs then .vtx ztyvo
    else .onEdge (ShootCut.edgeOf n (.vtx ztyvo)
      (.vtx (cVtxV n cs L S zterq))) (h - 1)
theorem hitSym_ch {v : ℕ} (hv : v = ztwi % C.P.n) {e h : ℕ}
    (_he : e < 2 * C.m + 7) :
    hitSym C e h = hitSymV C.P.n C.s C.m ztiao v e h := by
  unfold hitSym hitSymV
  by_cases h6 : e < 6 ∨ 2 * C.m + 6 ≤ e
  · simp_all
  · rw [ite_eq_right h6, ite_eq_right h6]
    have e1 : cVtx C e = cVtxV C.P.n C.s C.m ztiao ztbcs := by
      rw [← cVtx_ch by_omega, show e - 6 + 6 = e by omega]
    have e2 : cVtx C ztda = cVtxV C.P.n C.s C.m ztiao zterq := by
      rw [← cVtx_ch by_omega, show e - 6 + 1 + 6 = e + 1 by omega]
    simp_all

/-! ## First hits on a union -/
theorem firstHit_union_l (hA : FirstHit A z σ t)
    (hB : ∀ t', 0 < t' → t' < t → rayPt z σ t' ∉ B) : FirstHit ztbgp z σ t :=
  ⟨hA.1, Or.inl hA.2.1, fun t' h0 h1 hm => hm.elim (hA.2.2 t' h0 h1) (hB t' h0 h1)⟩
theorem firstHit_union_r (hB : FirstHit B z σ t)
    (hA : ∀ t', 0 < t' → t' < t → rayPt z σ t' ∉ A) : FirstHit ztbgp z σ t := by
  zuoes; exact firstHit_union_l hB hA
theorem firstHit_noHit (hA : FirstHit A z σ t)
    (hB : NoHit B z σ) : FirstHit ztbgp z σ t :=
  firstHit_union_l hA fun t' h0 _ => hB t' h0
theorem noHit_firstHit (hA : NoHit A z σ)
    (hB : FirstHit B z σ t) : FirstHit ztbgp z σ t :=
  firstHit_union_r hB fun t' h0 _ => hA t' h0
theorem noHit_union {σ : ℝ} (hA : NoHit A z σ) (hB : NoHit B z σ) :
    NoHit ztbgp z σ := fun t h0 hm => hm.elim (hA t h0) (hB t h0)

/-- Two first hits: the nearer one. -/
theorem firstHit_min {σ t₁ t₂ : ℝ} (hA : FirstHit A z σ t₁)
    (hB : FirstHit B z σ t₂) (h : t₁ ≤ t₂) : FirstHit ztbgp z σ t₁ :=
  firstHit_union_l hA fun t' h0 h1 => hB.2.2 t' h0 (lt_of_lt_of_le h1 h)
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
open Machine Machine.Stmt Programs SignK WalkKey
@[expose] public section
def csI : Stmt :=
  .ifLtN 170014 170011
    (.seq (block [.subN 170038 170019 170033, .subN 170084 170010 170037,
        .addN 170038 170038 170084])
      (.ifLtN 170038 170010 .skip (block [.subN 170038 170038 170010])))
    (block [.copyN 170038 170033])

/-- The vertex ranges `[cs, y₁]` and `[x₂, y₂]` into `170039 … 170041`. -/
def rngI : Stmt :=
  .seq (block [.addN 170084 170038 170037])
    (.ifLtN 170084 170010
      (block [.copyN 170039 170084, .copyN 170040 170038, .copyN 170041 170038])
      (block [.copyN 170039 170019, .constN 170040 0, .subN 170041 170084 170010]))

/-- The cover of the first range (the running maximum starts at its ends). -/
def top1 : Stmt :=
  .seq (block [.copyN 170046 170038, .copyN 170059 170039]) (.seq cmpUpd
    (.seq (block [.copyN 170050 170038, .copyN 170051 170039]) topLoop))

/-- The cover of the second range (the running maximum first takes its ends). -/
def top2 : Stmt :=
  .seq (block [.copyN 170059 170040]) (.seq cmpUpd (.seq (block [.copyN 170059 170041])
    (.seq cmpUpd (.seq (block [.copyN 170050 170040, .copyN 170051 170041]) topLoop))))

/-- `170079 := v`, `170074 := (v + n - cs) mod n`. -/
def tI : Stmt :=
  .seq (block [.copyN 170079 170046, .addN 170074 170046 170010, .subN 170074 170074 170038])
    (.ifLtN 170074 170010 .skip (block [.subN 170074 170074 170010]))

/-- **The chain of a stretch and its top.** -/
def topCh : Stmt := .seq csI (.seq rngI (.seq top1 (.seq top2 tI)))

/-- The registers `topCh` writes. -/
def Bch (r : ℕ) : Bool :=
  decide ztekn || decide ztgxy ||
    decide (r = 170074 ∨ r = 170079 ∨ r = 170084) || Bk r
theorem btop_bch {r : ℕ} (h : Btop r = true) : Bch r = true := by
  unfold Btop at h; unfold Bch
  grind
theorem wr_topCh : wr Bch topCh = true := by
  rfl

/-! ## Execution -/
section exec
variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}
theorem qn' : (Qof P).n = P.n := shear_n _ _

/-- **The start of the chain.** -/
theorem csI_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c) {u L : ℕ}
    (hu : c.nreg 170033 = u) (hL : c.nreg 170037 = L) (hun : u < P.n) (h1 : 1 ≤ L)
    (h2 : L + 1 ≤ P.n) :
    ∃ c' k, Exec P W csI c c' k ∧ k ≤ 7 ∧ c'.nreg 170038 = cStart zta u L ∧
      c'.nmem = c.nmem ∧ (∀ r, r ≠ 170038 → r ≠ 170084 → c'.nreg r = c.nreg r) := by
  zucg

  zudq
  unfold csI
  by_cases hb : c.nreg 170014 < c.nreg 170011
  · have hL' : ¬ Mountain.LeftInside _ := fun h => by
      have := hS.lb.2 h; zvnem at hb; omega
    zugst
    refine spec_seq ?_
    exec_block
    · config_simp; rw [hS.r19, hS.r10, hu, hL]; omega
    by_cases hlt : P.n - 1 - u + ztoz < P.n
    · refine spec_ifLtN_true (by config_simp; rw [hS.r19, hS.r10, hu, hL]; omega) ?_
      refine spec_skip ‹_› ztedo
      · config_simp; rw [hS.r19, hS.r10, hu, hL]
        unfold cStart; rw [ite_eq_right hL', hQ, Nat.mod_eq_of_lt hlt]
      simp_all
    · refine spec_ifLtN_false (by config_simp; rw [hS.r19, hS.r10, hu, hL]; omega) ?_
      exec_block
      refine ztedo
      · config_simp; rw [hS.r19, hS.r10, hu, hL]
        unfold cStart; rw [ite_eq_right hL', hQ, Nat.mod_eq_sub_mod by_omega,
          Nat.mod_eq_of_lt by_omega]
      · zuhoz
  · have hL' : Mountain.LeftInside _ := hS.lb.1 (by zvnem at hb; have := hS.lb1; omega)
    zugsq
    exec_block
    refine ztedo
    · config_simp; rw [hu]; unfold cStart; simp_all
    simp_all

/-- **The vertex ranges of the chain.** -/
theorem rngI_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c) {cs L : ℕ}
    (hcs : c.nreg 170038 = cs) (hL : c.nreg 170037 = L) (hcsn : cs < P.n) (h2 : L + 1 ≤ P.n) :
    ∃ c' k, Exec P W rngI c c' k ∧ k ≤ 6 ∧ c'.nreg 170039 = rY1 P.n cs L ∧
      c'.nreg 170040 = rX2 P.n cs L ∧ c'.nreg 170041 = rY2 P.n cs L ∧ c'.nmem = c.nmem ∧
      (∀ r, r ≠ 170039 → r ≠ 170040 → r ≠ 170041 → r ≠ 170084 → c'.nreg r = c.nreg r) := by
  zucg

  unfold rngI
  refine spec_seq ?_
  exec_block
  · omega
  by_cases hlt : cs + L < P.n
  · refine spec_ifLtN_true (by config_simp; rw [hcs, hL, hS.r10]; omega) ?_
    exec_block
    refine ztfzd
    · config_simp; rw [hcs, hL]; unfold rY1; simp_all
    · config_simp; zuoei; unfold rX2; simp_all
    · config_simp; zuoei; unfold rY2; simp_all
    simp_all
  · refine spec_ifLtN_false (by config_simp; rw [hcs, hL, hS.r10]; omega) ?_
    exec_block
    · omega
    refine ztfzd
    · config_simp; rw [hS.r19]; unfold rY1; simp_all
    · config_simp; unfold rX2; simp_all
    · config_simp; rw [hcs, hL, hS.r10]; unfold rY2; simp_all
    simp_all

/-- Two copies. -/
theorem copy2_exec (c : Config) (hw : WordsBounded W c) (a b a' b' : ℕ) (hab : a ≠ b)
    (hb : a ≠ b') :
    ∃ c' k, Exec P W (block [.copyN a a', .copyN b b']) c c' k ∧ k = 2 ∧
      c'.nreg a = c.nreg a' ∧ c'.nreg b = c.nreg b' ∧
      (∀ r, r ≠ a → r ≠ b → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  refine ztfkb
  · simp_all
  · simp [upd, Ne.symm hb]
  simp_all
variable {G : ℕ → Prop}
/-- **The cover of the first range.** -/
theorem top1_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    {x y : ℕ} (hx : c.nreg 170038 = x) (hy : c.nreg 170039 = y) (hxy : x ≤ y) (hyn : y ≤ P.n - 1)
    (hcap : y - x ≤ 2 ^ ztbwe) (hgood : ∀ v, x ≤ v → v ≤ y → G v) :
    ∃ c' k, Exec P W top1 c c' k ∧ k ≤ 602 * Nat.log 2 zteks + 262 ∧ SEnv P W O s c' ∧
      G ztbso ∧ c'.nreg 170046 < P.n ∧
      ztwrd ∧
      ztwjo ∧
      c'.nmem = c.nmem := by
  zucgt
  obtain ⟨c₁, k₁, e₁, hk₁, a46, a59, r₁, m₁, -, -, -⟩ := copy2_exec (P := P) c hw 170046 170059
    170038 170039 by_norm_num by_norm_num
  have S₁ : zteeb := hS.keep by_grind
    by_simp_all ztmdy
  obtain ⟨c₂, k₂, e₂, hk₂, b46, r₂, m₂⟩ := cmpUpd_exec c₁ e₁.wb_right S₁
    by_omega by_omega
  have S₂ : zthoi := S₁.keep by_grind
    by_simp_all ztlir
  obtain ⟨c₃, k₃, e₃, hk₃, d50, d51, r₃, m₃, -, -, -⟩ := copy2_exec (P := P) c₂ e₂.wb_right
    170050 170051 170038 170039 by_norm_num by_norm_num
  have S₃ : ztlai := S₂.keep by_grind
    by_simp_all ztmdz
  have k38 : c₂.nreg 170038 = x := by
    simp_all
  have k39 : c₂.nreg 170039 = y := by
    simp_all
  have v46 : c₃.nreg 170046 = c₂.nreg 170046 := by_simp_all
  have hmx := Y_max_le (P := P) (a := c₁.nreg 170046) (b := c₁.nreg 170059)
  rw [← b46, a46, a59, hx, hy] at hmx
  have hv : c₂.nreg 170046 = x ∨ c₂.nreg 170046 = y := by
    grind
  obtain ⟨c₄, k₄, e₄, hk₄, S₄, g₄, n₄, cov₄, r₄, -, m₄⟩ := topLoop_exec (G := G) c₃ e₃.wb_right S₃
    by_omega by_omega hxy hyn hcap
    by_grind
    by_omega
    by_grind by_grind hgood
  refine ⟨c₄, _, .seq e₁ ztcb, by_omega, S₄, g₄, n₄, cov₄,
    fun r h1 h2 => ?_, by_grind⟩
  rw [r₄ r h1 h2, r₃ r by_omega by_omega, r₂ r by_omega by_omega h2,
    r₁ r by_omega by_omega]

/-- **The cover of the second range.** -/
theorem top2_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    {x y : ℕ} (hx : c.nreg 170040 = x) (hy : c.nreg 170041 = y) (hxy : x ≤ y) (hyn : y ≤ P.n - 1)
    (hcap : y - x ≤ 2 ^ ztbwe) (hgood : ∀ v, x ≤ v → v ≤ y → G v)
    (hvG : G ztyh) (hvn : c.nreg 170046 < P.n) :
    ∃ c' k, Exec P W top2 c c' k ∧ k ≤ 602 * Nat.log 2 zteks + 512 ∧ SEnv P W O s c' ∧
      G ztbso ∧ c'.nreg 170046 < P.n ∧
      ztwrd ∧
      Y P ztyh ≤ Y P ztbso ∧
      ztwjo ∧
      c'.nmem = c.nmem := by
  zucgt
  zucwc
  -- the first end
  obtain ⟨c₁, k₁, e₁, hk₁, a59, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 170059 170040]) c c₁ k₁ ∧
      k₁ = 1 ∧ c₁.nreg 170059 = x ∧ (∀ r, r ≠ 170059 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem := by
    exec_block
    simp_all
  have S₁ : zteeb := hS.keep by_grind
    by_simp_all (by zvmww)
  obtain ⟨c₂, k₂, e₂, hk₂, b46, r₂, m₂⟩ := cmpUpd_exec c₁ e₁.wb_right S₁
    by_simp_all by_omega
  have S₂ : zthoi := S₁.keep by_grind
    by_simp_all ztlir
  have k41 : c₂.nreg 170041 = y := by
    simp_all
  have k40 : c₂.nreg 170040 = x := by
    simp_all
  -- the second end
  obtain ⟨c₃, k₃, e₃, hk₃, a59', r₃, m₃⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 170059 170041]) c₂ c₃ k₃ ∧
      k₃ = 1 ∧ c₃.nreg 170059 = y ∧ (∀ r, r ≠ 170059 → c₃.nreg r = c₂.nreg r) ∧
      c₃.nmem = c₂.nmem := by
    zue
    exec_block
    simp_all
  have S₃ : ztlai := S₂.keep by_grind
    by_simp_all by_grind
  have hmx1 := Y_max_le (P := P) (a := c₁.nreg 170046) (b := c₁.nreg 170059)
  rw [← b46, a59, r₁ _ by_decide] at hmx1
  have hv2 : c₂.nreg 170046 < P.n ∧ G (c₂.nreg 170046) := by
    grind
  obtain ⟨c₄, k₄, e₄, hk₄, b46', r₄, m₄⟩ := cmpUpd_exec c₃ e₃.wb_right S₃
    by_simp_all by_omega
  have S₄ : ztrfu := S₃.keep by_grind
    by_grind (by zunys)
  have hmx2 := Y_max_le (P := P) (a := c₃.nreg 170046) (b := c₃.nreg 170059)
  rw [← b46', a59', r₃ _ by_decide] at hmx2
  have hv4 : c₄.nreg 170046 < P.n ∧ G ztvnp := by
    grind
  have k40' : c₄.nreg 170040 = x := by
    grind
  have k41' : c₄.nreg 170041 = y := by
    grind
  -- the cover
  obtain ⟨c₅, k₅, e₅, hk₅, d50, d51, r₅, m₅, -, -, -⟩ := copy2_exec (P := P) c₄ e₄.wb_right
    170050 170051 170040 170041 by_norm_num by_norm_num
  have S₅ : SEnv P W O s c₅ := S₄.keep by_grind
    by_grind ztmea
  have v46 : c₅.nreg 170046 = c₄.nreg 170046 := by_grind
  obtain ⟨c₆, k₆, e₆, hk₆, S₆, g₆, n₆, cov₆, r₆, y₆, m₆⟩ := topLoop_exec (G := G) c₅ e₅.wb_right S₅
    by_omega by_omega hxy hyn hcap by_grind
    by_omega by_grind
    by_grind hgood
  refine ⟨c₆, _, .seq e₁ ztfv, by_omega, S₆, g₆, n₆, cov₆,
    ?_, fun r h1 h2 => ?_, by_grind⟩
  · grind
  · rw [r₆ r h1 h2, r₅ r by_omega by_omega, r₄ r by_omega by_omega h2, r₃ r by_omega,
      r₂ r by_omega by_omega h2, r₁ r by_omega]

/-- **The top index.** -/
theorem tI_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c) {v cs : ℕ}
    (hv : c.nreg 170046 = v) (hcs : c.nreg 170038 = cs) (hvn : v < P.n) (hcsn : cs < P.n) :
    ∃ c' k, Exec P W tI c c' k ∧ k ≤ 6 ∧ c'.nreg 170079 = v ∧
      c'.nreg 170074 = (v + P.n - cs) % P.n ∧ c'.nmem = c.nmem ∧
      (∀ r, r ≠ 170079 → r ≠ 170074 → c'.nreg r = c.nreg r) := by
  zucg

  unfold tI
  refine spec_seq ?_
  exec_block
  · config_simp; rw [hv, hS.r10]; omega
  by_cases hlt : v + P.n - cs < P.n
  · refine spec_ifLtN_true (by config_simp; rw [hv, hS.r10, hcs]; omega) ?_
    refine spec_skip ‹_› ⟨by_omega, by_simp_all, ?_, rfl, fun r h1 h2 => ?_⟩
    · config_simp; rw [hv, hS.r10, hcs, Nat.mod_eq_of_lt hlt]
    simp_all
  · refine spec_ifLtN_false (by config_simp; omega) ?_
    exec_block
    refine ⟨by_omega, by_tauto, ?_, rfl, fun r h1 h2 => ?_⟩
    · config_simp; rw [hv, hS.r10, hcs, Nat.mod_eq_sub_mod by_omega, Nat.mod_eq_of_lt by_omega]
    · zuhoz
theorem log_two_mono {a b : ℕ} (h : a ≤ b) : Nat.log 2 (2 * a) ≤ Nat.log 2 (2 * b) :=
  Nat.log_mono_right by_omega

/-- **The chain of a stretch and its top.** -/
theorem topCh_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c) {u L : ℕ}
    (hu : c.nreg 170033 = u) (hL : c.nreg 170037 = L) (hun : u < P.n) (h1 : 1 ≤ L)
    (h2 : L + 1 ≤ (Qof P).n) (hcap : L ≤ 2 ^ ztbwe) :
    ∃ c' k, Exec P W topCh c c' k ∧ k ≤ 1204 * Nat.log 2 ztbtk + 900 ∧ SEnv P W O s c' ∧
      c'.nreg 170038 = cStart zta u L ∧ c'.nreg 170079 < P.n ∧
      c'.nreg 170074 = (ch zta u L h1 h2).topIdx ∧
      ztxnm % (Qof P).n = c'.nreg 170079 ∧
      FrameB Bch c c' := by
  zudq
  zujyn
  zuhwq
  set cs := cStart _ u L with hcsd
  have hcsn : cs < P.n := by zvnoq; exact cStart_lt by_omega
  have hLn : L < P.n := by_omega
  -- the start
  obtain ⟨c₁, k₁, e₁, hk₁, a38, m₁, r₁⟩ := csI_exec c hw hS hu hL hun h1 h2'
  rw [← hcsd] at a38
  have S₁ : zteeb := hS.keep by_grind
    by_simp_all ztmdy
  -- the ranges
  obtain ⟨c₂, k₂, e₂, hk₂, b39, b40, b41, m₂, r₂⟩ := rngI_exec c₁ e₁.wb_right S₁ a38
    by_simp_all hcsn h2'
  have S₂ : zthoi := S₁.keep by_grind by_simp_all (by rw [r₂ _ by_decide by_decide by_decide
      by_decide])
  have b38 : c₂.nreg 170038 = cs := by
    simp_all
  let G : ℕ → Prop := fun v => InCh (Qof P).n cs L v
  have hcap1 : rY1 P.n cs L - cs ≤ 2 ^ ztbwe := le_trans rY1_sub hcap
  have hcap2 := le_trans ztwcj hcap
  -- the first cover
  obtain ⟨c₃, k₃, e₃, hk₃, S₃, g₃, n₃, cov₃, r₃, m₃⟩ := top1_exec (G := G) c₂ e₂.wb_right S₂ b38 b39
    (cs_le_rY1 hcsn) (by have := rY1_lt (L := L) hcsn; omega) hcap1
    (fun v hv1 hv2 => by
      show InCh (Qof P).n cs L v
      zvnao; exact of_rng1 hcsn hv1 hv2)
  have c40 : c₃.nreg 170040 = rX2 P.n cs L := by
    grind
  have c41 : c₃.nreg 170041 = rY2 P.n cs L := by
    grind
  -- the second cover
  obtain ⟨c₄, k₄, e₄, hk₄, S₄, g₄, n₄, cov₄, y₄, r₄, m₄⟩ := top2_exec (G := G) c₃ e₃.wb_right S₃
    c40 c41 (rX2_le hcsn hLn) (by have := rY2_lt hcsn hLn; omega) hcap2
    (fun v hv1 hv2 => by
      show InCh (Qof P).n cs L v
      zvnao; exact of_rng2 hcsn hLn hv1 hv2) g₃ n₃
  have c38 : c₄.nreg 170038 = cs := by
    grind
  -- the top index
  obtain ⟨c₅, k₅, e₅, hk₅, d79, d74, m₅, r₅⟩ := tI_exec c₄ e₄.wb_right S₄ rfl c38 n₄ hcsn
  have S₅ := S₄.keep (fun r h1 h2 => r₅ r by_omega by_omega)
    by_grind ztmea
  -- the mathematics
  have hmax : ∀ k, k ≤ L → ((Qof P).vtx (ztfqq % (Qof P).n)).2 ≤ ((Qof P).vtx ztvnp).2 := by
    zugf
    zuext
    rcases rng_of hcsn hLn hk with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · grind
    grind
  obtain ⟨hT, hTv⟩ := topIdx_ch (Q := Qof P) (h1 := h1) (h2 := h2) hD g₄ hmax by_omega
  have ex : Exec P W topCh c c₅ _ :=
    .seq e₁ ztbq
  have hlog1 : Nat.log 2 (2 * (rY1 P.n cs L - cs)) ≤ Nat.log 2 _ := log_two_mono rY1_sub
  have hlog2 : Nat.log 2 (2 * (rY2 P.n cs L - rX2 P.n cs L)) ≤ Nat.log 2 ztbtk :=
    log_two_mono ztwcj
  refine ⟨c₅, _, ex, by_omega, S₅, by rw [r₅ _ by_decide by_decide]; omega,
    by omega, ?_, by_grind, exec_frameB ex wr_topCh⟩
  grind
