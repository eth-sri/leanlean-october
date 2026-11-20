module

public import Chazelle.Core.OracleRamSearch

/-!
# Lemma 3.6 (WP-H), RAM part 10: the chords on the ray

The chords are stored sorted by height vertex, then by the abscissa of their left end (`CH`).
`chordSearchS` finds by binary search the partition point `t` of the predicate `chPr` (the chords
below the ray's height, or at it and not ahead of the origin); `chordPostS` reads the chord at
the ray's height next to the origin (`CH[t]` rightwards, `CH[t - 1]` leftwards), if any:

* `120140` found (`1`) or not;
* `120141`, `120142` the walk edges of its near and far ends;
* `120143` whether the origin lies on it (degenerate start: the near end is not ahead).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK SearchR WalkKey
open OracleQ

@[expose] public section

/-- **The binary search over the sorted chords.** -/
def chordSearchS : Stmt :=
  .seq (block [.copyN 50103 120038, .copyN 50104 120039]) (tsearch 120041 120042 chordPr)

/-- The registers written by `chordSearchS`. -/
def BCS (r : ℕ) : Bool := BP r || decide (50100 ≤ r ∧ r ≤ 50116)

theorem wr_chordSearchS : wr BCS chordSearchS = true := by decide

/-- **The memory facts of the chord search.** -/
structure ChordMemOK (V : QV) (m : ℕ → ℕ) (W : ℕ) : Prop where
  tab : ∀ j, j < V.L → m (V.TB + j) = 2 ^ j
  K_lt : V.K < 2 ^ V.L
  CH_le : V.CH + V.K ≤ V.TB
  TB_le : V.TB + V.L ≤ W
  recs : ∀ i, i < V.K → V.CB + 5 * i + 2 < V.TB

open Classical in
/-- **The chord search.** -/
theorem chordSearch_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W)
    {C : Chain} {V : QV} (hv : QVOK P C V) (htv : V.tv < P.n) (c : Config)
    (hw : WordsBounded W c) (hq : QConst P V c) (hm : ChordMemOK V c.nmem W)
    (hmono : ∀ i j, i ≤ j → j < V.K → chPr P C V c.nmem (chAt c.nmem V j) = true →
      chPr P C V c.nmem (chAt c.nmem V i) = true) :
    ∃ c' k, Exec P W chordSearchS c c' k ∧ k ≤ 715 * V.L + 10 ∧ FrameB BCS c c' ∧
      c'.nreg 50105 ≤ V.K ∧
      (∀ j, j < c'.nreg 50105 → chPr P C V c.nmem (chAt c.nmem V j) = true) ∧
      (c'.nreg 50105 < V.K → chPr P C V c.nmem (chAt c.nmem V (c'.nreg 50105)) = false) := by
  obtain ⟨c₁, k₁, e₁, hk₁, v₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 50103 120038,
      .copyN 50104 120039]) c c₁ k₁ ∧ k₁ = 2 ∧ (c₁.nreg 50103 = V.CH ∧ c₁.nreg 50104 = V.K ∧
        ∀ r, r ≠ 50103 → r ≠ 50104 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem := by
    exec_block
    exact ⟨rfl, ⟨by config_simp; exact hq.CH, by config_simp; exact hq.K,
      fun r h1 h2 => by config_simp; upd_solve⟩, rfl⟩
  obtain ⟨x103, x104, r₁⟩ := v₁.1
  have m₁ := v₁.2
  have hq₁ : QConst P V c₁ := hq.congr fun r h1 h2 => r₁ r (by omega) (by omega)
  have hTW : V.TB ≤ W := by have := hm.TB_le; omega
  have hpr := chordPr_ok (P := P) hG hW hv htv (T := V.TB) (m₀ := c.nmem) hm.recs hTW
  obtain ⟨c₂, k₂, e₂, hk₂, hJ₂, -, m₂, -, ht₂, hpre, hpost⟩ := tsearch_exec (P := P) hpr
    (by simp [bLocate, bSign, bOQuery]) (rT := 120041) (rL := 120042) (T := V.TB) (L := V.L)
    (by unfold bandOf bLocate; omega) (by unfold bandOf bLocate; omega) e₁.wb_right
    ⟨hq₁, fun a _ => by rw [m₁]⟩ (chJ_stable P V V.TB c.nmem) hq₁.TB hq₁.L
    (fun j hj => by rw [m₁]; exact hm.tab j hj) (by rw [x104]; exact hm.K_lt)
    (by rw [x103, x104]; exact hm.CH_le) hm.TB_le
    (fun i j hij hj h => by
      rw [x104] at hj; rw [x103, m₁] at h ⊢; exact hmono i j hij hj h) (by omega)
  rw [x104] at ht₂ hpost
  rw [x103, m₁] at hpre hpost
  refine ⟨c₂, _, .seq e₁ e₂, by omega, exec_frameB (.seq e₁ e₂) wr_chordSearchS, ht₂,
    fun j hj => hpre j hj, hpost⟩

/-! ## The chord at the ray's height next to the origin -/

/-- Read the height of the chord record in `120145` (into `120147`). -/
def readRec : Stmt := .seq (t5 120146 120145 120043) (.instr (.loadN 120147 120146))

/-- The ends of the found chord, rightwards. -/
def foundPos : Stmt := block [.constN 120140 1, .addN 120146 120146 120011, .loadN 120141 120146,
  .addN 120146 120146 120011, .loadN 120142 120146, .copyN 120120 120141, .copyN 120121 120023]

/-- The ends of the found chord, leftwards. -/
def foundNeg : Stmt := block [.constN 120140 1, .addN 120146 120146 120011, .loadN 120142 120146,
  .addN 120146 120146 120011, .loadN 120141 120146, .copyN 120120 120141, .copyN 120121 120023]

/-- The found chord, rightwards. -/
def postPos : Stmt :=
  .ifLtN 50105 120039
    (.seq (block [.addN 120144 120038 50105, .loadN 120145 120144])
      (.seq readRec
        (ifEq 120147 120023 (.seq foundPos (.seq gtZS (.instr (.subN 120143 120011 120128))))
          .skip)))
    .skip

/-- The found chord, leftwards. -/
def postNeg : Stmt :=
  .ifLtN 120012 50105
    (.seq (block [.subN 120148 50105 120011, .addN 120144 120038 120148, .loadN 120145 120144])
      (.seq readRec
        (ifEq 120147 120023 (.seq foundNeg (.seq ltZS (.instr (.subN 120143 120011 120128))))
          .skip)))
    .skip

/-- **The chord at the ray's height next to the origin.** -/
def chordPostS : Stmt := .seq (.instr (.constN 120140 0)) (.ifLtN 120024 120011 postNeg postPos)

/-- The registers written by `chordPostS`. -/
def BCP (r : ℕ) : Bool := BX2 r || decide (120120 ≤ r ∧ r ≤ 120121) || decide (120140 ≤ r ∧ r ≤ 120148)

theorem wr_chordPostS : wr BCP chordPostS = true := by decide

section Post
variable (P : Polygon) (C : Chain) (V : QV) (m : ℕ → ℕ) (t : ℕ)

/-- The position of the chord next to the origin in the sorted table. -/
def jCOf : ℕ := if V.σb = 1 then t else t - 1

/-- The chord next to the origin exists and lies at the ray's height. -/
def FoundC : Prop :=
  (if V.σb = 1 then t < V.K else 0 < t) ∧ chH m V (chAt m V (jCOf V t)) = V.hz

/-- The near end of the chord next to the origin. -/
def nearC : ℕ := if V.σb = 1 then chL m V (chAt m V (jCOf V t)) else chR m V (chAt m V (jCOf V t))

/-- The far end of the chord next to the origin. -/
def farC : ℕ := if V.σb = 1 then chR m V (chAt m V (jCOf V t)) else chL m V (chAt m V (jCOf V t))

/-- The origin lies on the chord (its near end is not ahead). -/
def DegC : Prop :=
  ¬ (if V.σb = 1 then EndGtZ P C V (nearC V m t) V.hz else EndLtZ P C V (nearC V m t) V.hz)

end Post

/-- **The memory facts of the sorted chord table.** -/
structure ChordTabOK (V : QV) (m : ℕ → ℕ) (W : ℕ) : Prop where
  lt : ∀ q, q < V.K → chAt m V q < V.K
  CH_le : V.CH + V.K ≤ W
  rec_le : ∀ i, i < V.K → V.CB + 5 * i + 2 ≤ W

/-- Read the height of the chord record in `120145`. -/
theorem readRec_exec {P : Polygon} {W : ℕ} {V : QV} (c : Config) (hw : WordsBounded W c)
    (hCB : c.nreg 120043 = V.CB) {i : ℕ} (hi : c.nreg 120145 = i) (hrec : V.CB + 5 * i + 2 ≤ W) :
    ∃ c' k, Exec P W readRec c c' k ∧ k = 5 ∧ c'.nreg 120146 = V.CB + 5 * i ∧ c'.nreg 120147 = chH c.nmem V i ∧
      (∀ r, r ≠ 120146 → r ≠ 120147 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  unfold readRec
  obtain ⟨c₁, e₁, v₁, r₁, m₁, -, -, -⟩ := t5_exec (P := P) (rd := 120146) (rs := 120145)
    (rb := 120043) (by decide) (by decide) c hw (by rw [hi, hCB]; omega)
  rw [hi, hCB] at v₁
  refine ⟨_, _, .seq e₁ (Exec.loadN e₁.wb_right 120147 120146), rfl, ?_, ?_, fun r h1 h2 => ?_,
    ?_⟩
  · config_simp; exact v₁
  · config_simp; rw [v₁, m₁]; rfl
  · config_simp; rw [Machine.upd_other _ _ _ h2]; exact r₁ r h1
  · config_simp; exact m₁

/-- The found chord's ends, rightwards. -/
theorem foundPos_exec {P : Polygon} {W : ℕ} {V : QV} (c : Config) (hw : WordsBounded W c)
    (hone : c.nreg 120011 = 1) (hhz : c.nreg 120023 = V.hz) {i : ℕ}
    (h46 : c.nreg 120146 = V.CB + 5 * i) (hrec : V.CB + 5 * i + 2 ≤ W) :
    ∃ c' k, Exec P W foundPos c c' k ∧ k = 7 ∧ c'.nreg 120140 = 1 ∧
      c'.nreg 120141 = chL c.nmem V i ∧ c'.nreg 120142 = chR c.nmem V i ∧
      c'.nreg 120120 = chL c.nmem V i ∧ c'.nreg 120121 = V.hz ∧
      (∀ r, r ≠ 120140 → r ≠ 120146 → r ≠ 120141 → r ≠ 120142 → r ≠ 120120 → r ≠ 120121 →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  first | unfold foundPos
  exec_block
  · omega
  · config_simp; rw [h46, hone]; omega
  · config_simp; rw [h46, hone]; omega
  · refine ⟨rfl, by config_simp, ?_, ?_, ?_, by config_simp; exact hhz,
      fun r h1 h2 h3 h4 h5 h6 => by config_simp; upd_solve, rfl⟩
    · config_simp; rw [h46, hone]; rfl
    · config_simp; rw [h46, hone]; rfl
    · config_simp; rw [h46, hone]; rfl

/-- The found chord's ends, leftwards. -/
theorem foundNeg_exec {P : Polygon} {W : ℕ} {V : QV} (c : Config) (hw : WordsBounded W c)
    (hone : c.nreg 120011 = 1) (hhz : c.nreg 120023 = V.hz) {i : ℕ}
    (h46 : c.nreg 120146 = V.CB + 5 * i) (hrec : V.CB + 5 * i + 2 ≤ W) :
    ∃ c' k, Exec P W foundNeg c c' k ∧ k = 7 ∧ c'.nreg 120140 = 1 ∧
      c'.nreg 120141 = chR c.nmem V i ∧ c'.nreg 120142 = chL c.nmem V i ∧
      c'.nreg 120120 = chR c.nmem V i ∧ c'.nreg 120121 = V.hz ∧
      (∀ r, r ≠ 120140 → r ≠ 120146 → r ≠ 120141 → r ≠ 120142 → r ≠ 120120 → r ≠ 120121 →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  first | unfold foundPos | unfold foundNeg
  exec_block
  · omega
  · config_simp; rw [h46, hone]; omega
  · config_simp; rw [h46, hone]; omega
  · refine ⟨rfl, by config_simp, ?_, ?_, ?_, by config_simp; exact hhz,
      fun r h1 h2 h3 h4 h5 h6 => by config_simp; upd_solve, rfl⟩
    · config_simp; rw [h46, hone]; rfl
    · config_simp; rw [h46, hone]; rfl
    · config_simp; rw [h46, hone]; rfl

/-- **The chord at the ray's height next to the origin.** -/
theorem chordPost_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W)
    {C : Chain} {V : QV} (hv : QVOK P C V) (htv : V.tv < P.n) (c : Config)
    (hw : WordsBounded W c) (hq : QConst P V c) (hT : ChordTabOK V c.nmem W)
    (ht : c.nreg 50105 ≤ V.K) :
    ∃ c' k, Exec P W chordPostS c c' k ∧ k ≤ 360 ∧ FrameB BCP c c' ∧ c'.nreg 120140 ≤ 1 ∧
      (c'.nreg 120140 = 1 ↔ FoundC V c.nmem (c.nreg 50105)) ∧
      (FoundC V c.nmem (c.nreg 50105) → c'.nreg 120141 = nearC V c.nmem (c.nreg 50105) ∧
        c'.nreg 120142 = farC V c.nmem (c.nreg 50105) ∧ c'.nreg 120143 ≤ 1 ∧
        (c'.nreg 120143 = 1 ↔ DegC P C V c.nmem (c.nreg 50105))) := by
  obtain ⟨t, htd⟩ : ∃ t, c.nreg 50105 = t := ⟨_, rfl⟩
  rw [htd] at ht ⊢
  suffices H : ∃ c' k, Exec P W chordPostS c c' k ∧ k ≤ 360 ∧ c'.nreg 120140 ≤ 1 ∧
      (c'.nreg 120140 = 1 ↔ FoundC V c.nmem t) ∧
      (FoundC V c.nmem t → c'.nreg 120141 = nearC V c.nmem t ∧ c'.nreg 120142 = farC V c.nmem t ∧
        c'.nreg 120143 ≤ 1 ∧ (c'.nreg 120143 = 1 ↔ DegC P C V c.nmem t)) by
    obtain ⟨c', k, ex, hk, h1, h2, h3⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex wr_chordPostS, h1, h2, h3⟩
  obtain ⟨c₀, e₀, v₀, r₀⟩ := const_exec (P := P) hw 120140 0 (by omega)
  have hq₀ : QConst P V c₀ := hq.congr fun r h1 h2 => r₀ r (by omega)
  have m₀ : c₀.nmem = c.nmem :=
    (exec_frameB e₀ (B := fun r => decide (r = 120140)) (by decide)).2.2.1
  have w₀ := e₀.wb_right
  have t₀ : c₀.nreg 50105 = t := by rw [r₀ _ (by decide), htd]
  -- the common tail: the chord at position `j`
  have tail : ∀ (pos : Bool) (j : ℕ), j < V.K → (pos = true ↔ V.σb = 1) →
      jCOf V t = j → ∀ d : Config, WordsBounded W d → QConst P V d → d.nmem = c.nmem →
      d.nreg 120140 = 0 → d.nreg 120145 = chAt c.nmem V j →
      ∃ d' k, Exec P W (.seq readRec (ifEq 120147 120023
          (.seq (if pos then foundPos else foundNeg)
            (.seq (if pos then gtZS else ltZS) (.instr (.subN 120143 120011 120128)))) .skip))
        d d' k ∧ k ≤ 340 ∧ d'.nreg 120140 ≤ 1 ∧
        (d'.nreg 120140 = 1 ↔ chH c.nmem V (chAt c.nmem V j) = V.hz) ∧
        (chH c.nmem V (chAt c.nmem V j) = V.hz → d'.nreg 120141 = nearC V c.nmem t ∧
          d'.nreg 120142 = farC V c.nmem t ∧ d'.nreg 120143 ≤ 1 ∧
          (d'.nreg 120143 = 1 ↔ DegC P C V c.nmem t)) := by
    intro pos j hj hpos hjc d hd hqd hmd h140 h145
    have hi := hT.lt j hj
    have hrec := hT.rec_le _ hi
    obtain ⟨d₁, k₁, e₁, hk₁, v146, v147, r₁, m₁⟩ := readRec_exec (P := P) (V := V) d hd hqd.CB h145
      hrec
    rw [hmd] at v147
    have hq₁ : QConst P V d₁ := hqd.congr fun r h1 h2 => r₁ r (by omega) (by omega)
    by_cases heq : chH c.nmem V (chAt c.nmem V j) = V.hz
    · have hq12 : d₁.nreg 120147 = d₁.nreg 120023 := by rw [v147, hq₁.hz, heq]
      have hmd₁ : d₁.nmem = c.nmem := m₁.trans hmd
      -- the ends
      obtain ⟨d₂, k₂, e₂, hk₂, a140, a141, a142, a120, a121, r₂, m₂⟩ :
          ∃ d₂ k₂, Exec P W (if pos then foundPos else foundNeg) d₁ d₂ k₂ ∧ k₂ = 7 ∧
            d₂.nreg 120140 = 1 ∧ d₂.nreg 120141 = nearC V c.nmem t ∧
            d₂.nreg 120142 = farC V c.nmem t ∧ d₂.nreg 120120 = nearC V c.nmem t ∧
            d₂.nreg 120121 = V.hz ∧
            (∀ r, r ≠ 120140 → r ≠ 120146 → r ≠ 120141 → r ≠ 120142 → r ≠ 120120 → r ≠ 120121 →
              d₂.nreg r = d₁.nreg r) ∧ d₂.nmem = d₁.nmem := by
        cases pos
        · have hσ : V.σb ≠ 1 := fun h => Bool.false_ne_true (hpos.2 h)
          obtain ⟨d₂, k₂, e₂, hk₂, a1, a2, a3, a4, a5, a6, a7⟩ := foundNeg_exec (P := P) (V := V)
            d₁ e₁.wb_right hq₁.one hq₁.hz v146 hrec
          rw [hmd₁] at a2 a3 a4
          refine ⟨d₂, k₂, e₂, hk₂, a1, ?_, ?_, ?_, a5, a6, a7⟩ <;>
            simp only [nearC, farC, ite_eq_right hσ, hjc] <;> assumption
        · have hσ : V.σb = 1 := hpos.1 rfl
          obtain ⟨d₂, k₂, e₂, hk₂, a1, a2, a3, a4, a5, a6, a7⟩ := foundPos_exec (P := P) (V := V)
            d₁ e₁.wb_right hq₁.one hq₁.hz v146 hrec
          rw [hmd₁] at a2 a3 a4
          refine ⟨d₂, k₂, e₂, hk₂, a1, ?_, ?_, ?_, a5, a6, a7⟩ <;>
            simp only [nearC, farC, ite_eq_left hσ, hjc] <;> assumption
      have hq₂ : QConst P V d₂ := hq₁.congr fun r h1 h2 => r₂ r (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
      -- the comparison
      obtain ⟨d₃, k₃, e₃, hk₃, f₃, b₃, g₃⟩ : ∃ d₃ k₃, Exec P W (if pos then gtZS else ltZS) d₂ d₃ k₃ ∧
          k₃ ≤ 300 ∧ FrameB BX2 d₂ d₃ ∧ d₃.nreg 120128 ≤ 1 ∧
          (d₃.nreg 120128 = 1 ↔ (if V.σb = 1 then EndGtZ P C V (nearC V c.nmem t) V.hz
            else EndLtZ P C V (nearC V c.nmem t) V.hz)) := by
        cases pos
        · have hσ : V.σb ≠ 1 := fun h => Bool.false_ne_true (hpos.2 h)
          obtain ⟨d₃, k₃, e₃, hk₃, f₃, b₃, g₃⟩ := ltZS_exec (P := P) hG (by omega) hv htv d₂
            e₂.wb_right hq₂ (by rw [a121]; exact hv.hz_lt)
          rw [a120, a121] at g₃
          exact ⟨d₃, k₃, e₃, hk₃, f₃, b₃, by rw [ite_eq_right hσ]; exact g₃⟩
        · have hσ : V.σb = 1 := hpos.1 rfl
          obtain ⟨d₃, k₃, e₃, hk₃, f₃, b₃, g₃⟩ := gtZS_exec (P := P) hG (by omega) hv htv d₂
            e₂.wb_right hq₂ (by rw [a121]; exact hv.hz_lt)
          rw [a120, a121] at g₃
          exact ⟨d₃, k₃, e₃, hk₃, f₃, b₃, by rw [ite_eq_left hσ]; exact g₃⟩
      have one₃ : d₃.nreg 120011 = 1 := (f₃.1 _ (by decide)).trans hq₂.one
      have w₃ := e₃.wb_right
      obtain ⟨d₄, e₄, v₄, v₄'⟩ : ∃ d₄, Exec P W (.instr (.subN 120143 120011 120128)) d₃ d₄ 1 ∧
          d₄.nreg 120143 = d₃.nreg 120011 - d₃.nreg 120128 ∧
          ∀ r, r ≠ 120143 → d₄.nreg r = d₃.nreg r :=
        ⟨_, Exec.subN w₃ _ _ _, by config_simp, fun r hr => by config_simp; upd_solve⟩
      have R₄ : ∀ r, r ≠ 120143 → BX2 r = false → d₄.nreg r = d₂.nreg r := fun r h1 h2 => by
        rw [v₄' r h1, f₃.1 r h2]
      refine ⟨d₄, _, .seq e₁ (ifEq_eq_exec hq12 (.seq e₂ (.seq e₃ e₄))), by omega, ?_, ?_, fun _ => ?_⟩
      · rw [R₄ _ (by decide) (by decide), a140]
      · rw [R₄ _ (by decide) (by decide), a140]; simp [heq]
      · refine ⟨by rw [R₄ _ (by decide) (by decide), a141], by rw [R₄ _ (by decide) (by decide), a142],
          by rw [v₄, one₃]; omega, ?_⟩
        rw [v₄, one₃]
        unfold DegC
        constructor
        · intro h hc; have := g₃.2 hc; omega
        · intro h; have := mt g₃.1 h; omega
    · have hq12 : d₁.nreg 120147 ≠ d₁.nreg 120023 := by rw [v147, hq₁.hz]; exact heq
      obtain ⟨k', ex', hk'⟩ := ifEq_ne_exec (S := .seq (if pos then foundPos else foundNeg)
        (.seq (if pos then gtZS else ltZS) (.instr (.subN 120143 120011 120128)))) hq12
        (.skip e₁.wb_right)
      refine ⟨d₁, _, .seq e₁ ex', by omega, by rw [r₁ _ (by decide) (by decide), h140]; omega,
        ?_, fun h => absurd h heq⟩
      rw [r₁ _ (by decide) (by decide), h140]
      simp [heq]
  have hCH := hT.CH_le
  by_cases hσ : V.σb < 1
  · -- leftwards
    have hσ' : V.σb ≠ 1 := by omega
    have hjc : jCOf V t = t - 1 := by unfold jCOf; rw [ite_eq_right hσ']
    by_cases ht0 : 0 < t
    · obtain ⟨d, k, e, hk, v⟩ : ∃ d k, Exec P W (block [.subN 120148 50105 120011,
          .addN 120144 120038 120148, .loadN 120145 120144]) c₀ d k ∧ k = 3 ∧
          (d.nreg 120145 = chAt c.nmem V (t - 1) ∧
            (∀ r, r ≠ 120148 → r ≠ 120144 → r ≠ 120145 → d.nreg r = c₀.nreg r) ∧ d.nmem = c₀.nmem) := by
        exec_block
        · config_simp; rw [hq₀.CH, t₀, hq₀.one]; omega
        · refine ⟨rfl, ?_, fun r h1 h2 h3 => by config_simp; upd_solve, rfl⟩
          config_simp; rw [hq₀.CH, t₀, hq₀.one, m₀]; rfl
      obtain ⟨v145, rd, md⟩ := v
      have hqd : QConst P V d := hq₀.congr fun r h1 h2 => rd r (by omega) (by omega) (by omega)
      obtain ⟨d', k', e', hk', b', f', g'⟩ := tail false (t - 1) (by omega)
        ⟨fun h => absurd h (by simp), fun h => absurd h hσ'⟩ hjc d e.wb_right hqd (md.trans m₀)
        (by rw [rd _ (by decide) (by decide) (by decide), v₀]) v145
      refine ⟨d', _, .seq e₀ (.ifLtN_true (by rw [hq₀.σb, hq₀.one]; exact hσ)
        (.ifLtN_true (by rw [hq₀.zero, t₀]; exact ht0) (.seq e e'))), by omega, b', ?_, ?_⟩
      · rw [f']; unfold FoundC; rw [ite_eq_right hσ', hjc]; simp [ht0]
      · intro hF; unfold FoundC at hF; rw [ite_eq_right hσ', hjc] at hF; exact g' hF.2
    · refine ⟨c₀, _, .seq e₀ (.ifLtN_true (by rw [hq₀.σb, hq₀.one]; exact hσ)
        (.ifLtN_false (by rw [hq₀.zero, t₀]; exact ht0) (.skip w₀))), by omega,
        by rw [v₀]; omega, ?_, ?_⟩
      · rw [v₀]; unfold FoundC; rw [ite_eq_right hσ']; simp [ht0]
      · intro hF; unfold FoundC at hF; rw [ite_eq_right hσ'] at hF; exact absurd hF.1 ht0
  · -- rightwards
    have hσ' : V.σb = 1 := by have := hv.σb_le; omega
    have hjc : jCOf V t = t := by unfold jCOf; rw [ite_eq_left hσ']
    by_cases htK : t < V.K
    · obtain ⟨d, k, e, hk, v⟩ : ∃ d k, Exec P W (block [.addN 120144 120038 50105,
          .loadN 120145 120144]) c₀ d k ∧ k = 2 ∧
          (d.nreg 120145 = chAt c.nmem V t ∧
            (∀ r, r ≠ 120144 → r ≠ 120145 → d.nreg r = c₀.nreg r) ∧ d.nmem = c₀.nmem) := by
        exec_block
        · rw [hq₀.CH, t₀]; omega
        · refine ⟨rfl, ?_, fun r h1 h2 => by config_simp; upd_solve, rfl⟩
          config_simp; rw [hq₀.CH, t₀, m₀]; rfl
      obtain ⟨v145, rd, md⟩ := v
      have hqd : QConst P V d := hq₀.congr fun r h1 h2 => rd r (by omega) (by omega)
      obtain ⟨d', k', e', hk', b', f', g'⟩ := tail true t htK
        ⟨fun _ => hσ', fun _ => rfl⟩ hjc d e.wb_right hqd (md.trans m₀)
        (by rw [rd _ (by decide) (by decide), v₀]) v145
      refine ⟨d', _, .seq e₀ (.ifLtN_false (by rw [hq₀.σb, hq₀.one]; exact hσ)
        (.ifLtN_true (by rw [hq₀.K, t₀]; exact htK) (.seq e e'))), by omega, b', ?_, ?_⟩
      · rw [f']; unfold FoundC; rw [ite_eq_left hσ', hjc]; simp [htK]
      · intro hF; unfold FoundC at hF; rw [ite_eq_left hσ', hjc] at hF; exact g' hF.2
    · refine ⟨c₀, _, .seq e₀ (.ifLtN_false (by rw [hq₀.σb, hq₀.one]; exact hσ)
        (.ifLtN_false (by rw [hq₀.K, t₀]; exact htK) (.skip w₀))), by omega,
        by rw [v₀]; omega, ?_, ?_⟩
      · rw [v₀]; unfold FoundC; rw [ite_eq_left hσ']; simp [htK]
      · intro hF; unfold FoundC at hF; rw [ite_eq_left hσ'] at hF; exact absurd hF.1 htK

end

end OracleR

end Chazelle.Core
