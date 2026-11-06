module

public import Chazelle.Core.SweepPrimIdx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics

/-!
# Sweep RAM primitives (WP-D2), part 14: navigation in a normal form

design-merge-v2 §9.6 item 7: reading a normal form stored at a handle (`NFAt`, design doc §3.4).
The layout is a header, and five-word records of chords (`h, lp, rp, up, dn`), arcs
(`reg, s.edge, s.hgt, e.edge, e.hgt`) and regions (arc count, arc-list start, chord count,
chord-list start, weight), a sequence table and a list area.  Every navigation step of the sweep
is one indexed load from a base of the header:

* `nfRd k s f` (handle `50200`, index `50201`): `50210 := m (m (B + k) + s · i + f)`;
  `chordRd f` (the region `up`/`dn` of a chord, its height vertex and the edges of `lpos`/`rpos`),
  `arcRd f` (the region of an arc, its start and end positions), `regRd f` (the numbers of arcs and
  exit chords of a region, its weight), `seqRd` (the arc at a place of `seq`; the previous and next
  arc in `seq` are the places `j - 1` and `j + 1`);
* `nfLst f` (handle `50200`, region `50201`, place `50202`): the `t`-th arc (`f = 1`) or exit chord
  (`f = 3`) of a region: `regArcRd`, `regChordRd`.

Each writes only band `bLocate` (`50100`, `50101`, `50210`) and costs a constant.  The only
condition is that the addresses fit in a word.
-/

namespace Chazelle.Core

namespace SweepPrim

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-! ## Multiplication by a constant -/

/-- `d := d + s · a`, as `s` additions. -/
def mulAdd (d a : ℕ) : ℕ → Stmt
  | 0 => .skip
  | s + 1 => .seq (.instr (.addN d d a)) (mulAdd d a s)

theorem wr_mulAdd {B : ℕ → Bool} {d a : ℕ} (hd : B d = true) : ∀ s, wr B (mulAdd d a s) = true
  | 0 => rfl
  | s + 1 => by simp [mulAdd, wr, wrOK, hd, wr_mulAdd hd s]

theorem mulAdd_exec {P : Polygon} {W : ℕ} {d a : ℕ} (hda : d ≠ a) :
    ∀ (s : ℕ) (c : Config), WordsBounded W c → c.nreg d + s * c.nreg a ≤ W →
      ∃ c' k, Exec P W (mulAdd d a s) c c' k ∧ k = s ∧ c'.nreg d = c.nreg d + s * c.nreg a ∧
        FrameB (fun r => r == d) c c'
  | 0, c, hw, _ => ⟨c, 0, .skip hw, rfl, by simp, FrameB.refl _ _⟩
  | s + 1, c, hw, hb => by
    have e₁ := Exec.addN (P := P) hw d d a (by nlinarith)
    obtain ⟨c', k, e', hk, v, f⟩ := mulAdd_exec hda s _ e₁.wb_right (by
      sinl only [upd_same, upd_other _ _ _ (Ne.symm hda)])
    refine ⟨c', _, .seq e₁ e', by omega, ?_, (exec_frameB e₁ (by simp [wr, wrOK])).trans f⟩
    rw [v]; sir only [upd_same, upd_other _ _ _ (Ne.symm hda)]

/-! ## One indexed load -/

/-- `50210 := m (m (B + k) + s · i + f)` for the handle `B = 50200` and the index `i = 50201`. -/
def nfRd (k s f : ℕ) : Stmt :=
  .seq (block [.constN 50100 k, .addN 50100 50200 50100, .loadN 50101 50100])
    (.seq (mulAdd 50101 50201 s) (block [.constN 50100 f, .addN 50101 50101 50100,
      .loadN 50210 50101]))

theorem wr_nfRd (k s f : ℕ) : wr Bidx (nfRd k s f) = true := by
  simp [nfRd, wr, block, wrOK, wr_mulAdd (B := Bidx) (d := 50101) (by decide)]
  decide

/-- The address condition of `nfRd k s f`. -/
def NFRdOK (k s f W : ℕ) (c : Config) : Prop :=
  c.nreg 50200 + k ≤ W ∧ c.nmem (c.nreg 50200 + k) + s * c.nreg 50201 + f ≤ W

/-- The value read by `nfRd k s f`. -/
def nfVal (k s f : ℕ) (c : Config) : ℕ :=
  c.nmem (c.nmem (c.nreg 50200 + k) + s * c.nreg 50201 + f)

theorem nfRd_exec {P : Polygon} {W : ℕ} (k s f : ℕ) (c : Config) (hw : WordsBounded W c)
    (h : NFRdOK k s f W c) :
    ∃ c' j, Exec P W (nfRd k s f) c c' j ∧ j = s + 6 ∧ c'.nreg 50210 = nfVal k s f c ∧
      FrameB Bidx c c' := by
  obtain ⟨h1, h2⟩ := h
  have e₁ := Exec.constN (P := P) hw 50100 k (by omega)
  have e₂ := Exec.addN (P := P) e₁.wb_right 50100 50200 50100 (by sio)
  have e₃ := Exec.loadN (P := P) e₂.wb_right 50101 50100
  obtain ⟨c₄, k₄, e₄, hk₄, v₄, f₄⟩ := mulAdd_exec (P := P) (d := 50101) (a := 50201) (by decide)
    s _ e₃.wb_right (by sio)
  have e₅ := Exec.constN (P := P) e₄.wb_right 50100 f (by omega)
  have e₆ := Exec.addN (P := P) e₅.wb_right 50101 50101 50100 (by
    simp [upd_same, upd_other _ _ _ (show (50101 : ℕ) ≠ 50100 by decide)]
    rws [v₄]; omega)
  have e₇ := Exec.loadN (P := P) e₆.wb_right 50210 50101
  have ex : Exec P W (nfRd k s f) c _ ((1 + (1 + (1 + 0))) + (k₄ + (1 + (1 + (1 + 0))))) :=
    .seq (.seq e₁ (.seq e₂ (.seq e₃ (.skip e₃.wb_right))))
      (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.skip e₇.wb_right)))))
  refine ⟨_, _, ex, by omega, ?_, exec_frameB ex (wr_nfRd k s f)⟩
  simp [upd_same, upd_other _ _ _ (show (50101 : ℕ) ≠ 50100 by decide)]
  rw [f₄.2.2.1, v₄]
  simp [nfVal]

/-- **Contract of `nfRd k s f`** (at most `s + 6` steps). -/
theorem nfRd_meets (k s f : ℕ) : Meets (nfRd k s f) {bLocate}
    (fun _ W c => NFRdOK k s f W c) (fun _ c c' => c'.nreg 50210 = nfVal k s f c)
    (fun _ _ => s + 6) := by
  intro P W c hw h _
  obtain ⟨c', j, e, hj, v, fr⟩ := nfRd_exec (P := P) k s f c hw h
  exact ⟨c', j, e, by show _ ≤ s + 6; omega, v, Bidx_frame fr _⟩

/-! ## The fields of a normal form -/

/-- Field `f` of a chord record: `h, lp, rp, up, dn`. -/
def crFld (c : CRec) : ℕ → ℕ
  | 0 => c.h
  | 1 => c.lp
  | 2 => c.rp
  | 3 => c.up
  | _ => c.dn

/-- Field `f` of an arc record: `reg, s.edge, s.hgt, e.edge, e.hgt`. -/
def arFld (a : ARec) : ℕ → ℕ
  | 0 => a.reg
  | 1 => a.s.edge
  | 2 => a.s.hgt
  | 3 => a.e.edge
  | _ => a.e.hgt

/-- Field `f ∈ {0, 2, 4}` of a region record: number of arcs, number of exit chords, weight. -/
def rrFld (r : RRec) : ℕ → ℕ
  | 0 => r.arcs.length
  | 2 => r.chords.length
  | _ => r.wt

theorem nfVal_chord {c : Config} {N : NF} (hN : NFAt c.nmem (c.nreg 50200) N)
    (hi : c.nreg 50201 < N.chords.length) {f : ℕ} (hf : f < 5) :
    nfVal 3 5 f c = crFld (N.chord (c.nreg 50201)) f := by
  obtain ⟨q0, q1, q2, q3, q4⟩ := hN.2.2.2.2.2.1 _ hi
  unfold nfVal
  interval_cases f <;> simp [add_zero, crFld] <;> assumption

theorem nfVal_arc {c : Config} {N : NF} (hN : NFAt c.nmem (c.nreg 50200) N)
    (hi : c.nreg 50201 < N.arcs.length) {f : ℕ} (hf : f < 5) :
    nfVal 4 5 f c = arFld (N.arc (c.nreg 50201)) f := by
  obtain ⟨q0, q1, q2, q3, q4⟩ := hN.2.2.2.2.2.2.1 _ hi
  unfold nfVal
  interval_cases f <;> simp [add_zero, arFld] <;> assumption

theorem nfVal_region {c : Config} {N : NF} (hN : NFAt c.nmem (c.nreg 50200) N)
    (hi : c.nreg 50201 < N.regions.length) {f : ℕ} (hf : f = 0 ∨ f = 2 ∨ f = 4) :
    nfVal 5 5 f c = rrFld (N.region (c.nreg 50201)) f := by
  obtain ⟨q0, q2, q4, -, -⟩ := hN.2.2.2.2.2.2.2.1 _ hi
  unfold nfVal
  rcases hf with rfl | rfl | rfl <;> simp [add_zero, rrFld] <;> assumption

/-- **`chordRd f`**: field `f` of chord `i = 50201` (`0` the height vertex, `1`/`2` the edges of
`lpos`/`rpos`, `3`/`4` the regions `up`/`dn`). -/
def chordRd (f : ℕ) : Stmt := nfRd 3 5 f

theorem chordRd_meets {f : ℕ} (hf : f < 5) : Meets (chordRd f) {bLocate}
    (fun _ W c => NFRdOK 3 5 f W c)
    (fun _ c c' => ∀ N, NFAt c.nmem (c.nreg 50200) N → c.nreg 50201 < N.chords.length →
      c'.nreg 50210 = crFld (N.chord (c.nreg 50201)) f)
    (fun _ _ => 11) :=
  fun P W c hw h hr => by
    obtain ⟨c', j, e, hj, v, fr⟩ := nfRd_meets 3 5 f P W c hw h hr
    exact ⟨c', j, e, hj, fun N hN hi => v.trans (nfVal_chord hN hi hf), fr⟩

/-- **`arcRd f`**: field `f` of arc `j = 50201` (`0` its region, `1`/`2` its start, `3`/`4` its
end). -/
def arcRd (f : ℕ) : Stmt := nfRd 4 5 f

theorem arcRd_meets {f : ℕ} (hf : f < 5) : Meets (arcRd f) {bLocate}
    (fun _ W c => NFRdOK 4 5 f W c)
    (fun _ c c' => ∀ N, NFAt c.nmem (c.nreg 50200) N → c.nreg 50201 < N.arcs.length →
      c'.nreg 50210 = arFld (N.arc (c.nreg 50201)) f)
    (fun _ _ => 11) :=
  fun P W c hw h hr => by
    obtain ⟨c', j, e, hj, v, fr⟩ := nfRd_meets 4 5 f P W c hw h hr
    exact ⟨c', j, e, hj, fun N hN hi => v.trans (nfVal_arc hN hi hf), fr⟩

/-- **`regRd f`**: field `f ∈ {0, 2, 4}` of region `r = 50201` (number of arcs, number of exit
chords, weight). -/
def regRd (f : ℕ) : Stmt := nfRd 5 5 f

theorem regRd_meets {f : ℕ} (hf : f = 0 ∨ f = 2 ∨ f = 4) : Meets (regRd f) {bLocate}
    (fun _ W c => NFRdOK 5 5 f W c)
    (fun _ c c' => ∀ N, NFAt c.nmem (c.nreg 50200) N → c.nreg 50201 < N.regions.length →
      c'.nreg 50210 = rrFld (N.region (c.nreg 50201)) f)
    (fun _ _ => 11) :=
  fun P W c hw h hr => by
    obtain ⟨c', j, e, hj, v, fr⟩ := nfRd_meets 5 5 f P W c hw h hr
    exact ⟨c', j, e, hj, fun N hN hi => v.trans (nfVal_region hN hi hf), fr⟩

/-! ## The lists of a region -/

/-- `50210 := m (m (B + 7) + m (m (B + 5) + 5 r + f) + t)` for the handle `B = 50200`, the region
`r = 50201` and the place `t = 50202`: the `t`-th arc (`f = 1`) or exit chord (`f = 3`). -/
def nfLst (f : ℕ) : Stmt :=
  .seq (nfRd 5 5 f) (block [.constN 50100 7, .addN 50100 50200 50100, .loadN 50101 50100,
    .addN 50101 50101 50210, .addN 50101 50101 50202, .loadN 50210 50101])

theorem wr_nfLst (f : ℕ) : wr Bidx (nfLst f) = true := by
  sid only [nfLst, wr, wr_nfRd, Bool.true_and]

/-- The address condition of `nfLst f`. -/
def NFLstOK (f W : ℕ) (c : Config) : Prop :=
  NFRdOK 5 5 f W c ∧ c.nreg 50200 + 7 ≤ W ∧
    c.nmem (c.nreg 50200 + 7) + nfVal 5 5 f c + c.nreg 50202 ≤ W

theorem nfLst_exec {P : Polygon} {W : ℕ} (f : ℕ) (c : Config) (hw : WordsBounded W c)
    (h : NFLstOK f W c) :
    ∃ c' j, Exec P W (nfLst f) c c' j ∧ j = 17 ∧
      c'.nreg 50210 = c.nmem (c.nmem (c.nreg 50200 + 7) + nfVal 5 5 f c + c.nreg 50202) ∧
      FrameB Bidx c c' := by
  obtain ⟨h0, h1, h2⟩ := h
  obtain ⟨c₁, j₁, e₁, hj₁, v₁, f₁⟩ := nfRd_exec (P := P) 5 5 f c hw h0
  have g  := f₁.1
  have m₁ := f₁.2.2.1
  have e₂ := Exec.constN (P := P) e₁.wb_right 50100 7 (by omega)
  have e₃ := Exec.addN (P := P) e₂.wb_right 50100 50200 50100 (by
    simp [upd_same, upd_other _ _ _ (show (50200 : ℕ) ≠ 50100 by decide)]
    rwo [g 50200 (by decide)])
  have e₄ := Exec.loadN (P := P) e₃.wb_right 50101 50100
  have e₅ := Exec.addN (P := P) e₄.wb_right 50101 50101 50210 (by
    simp [upd_same, upd_other _ _ _ (show (50210 : ℕ) ≠ 50101 by decide),
      upd_other _ _ _ (show (50210 : ℕ) ≠ 50100 by decide),
      upd_other _ _ _ (show (50200 : ℕ) ≠ 50100 by decide)]
    rwo [g 50200 (by decide), m₁, v₁])
  have e₆ := Exec.addN (P := P) e₅.wb_right 50101 50101 50202 (by
    simp [upd_same, upd_other _ _ _ (show (50210 : ℕ) ≠ 50101 by decide),
      upd_other _ _ _ (show (50210 : ℕ) ≠ 50100 by decide),
      upd_other _ _ _ (show (50200 : ℕ) ≠ 50100 by decide),
      upd_other _ _ _ (show (50202 : ℕ) ≠ 50101 by decide),
      upd_other _ _ _ (show (50202 : ℕ) ≠ 50100 by decide)]
    rwo [g 50200 (by decide), g 50202 (by decide), m₁, v₁])
  have e₇ := Exec.loadN (P := P) e₆.wb_right 50210 50101
  have ex : Exec P W (nfLst f) c _ (j₁ + (1 + (1 + (1 + (1 + (1 + (1 + 0))))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.skip e₇.wb_right)))))))
  refine ⟨_, _, ex, by omega, ?_, exec_frameB ex (wr_nfLst f)⟩
  simp [upd_same, upd_other _ _ _ (show (50210 : ℕ) ≠ 50101 by decide),
    upd_other _ _ _ (show (50210 : ℕ) ≠ 50100 by decide),
    upd_other _ _ _ (show (50200 : ℕ) ≠ 50100 by decide),
    upd_other _ _ _ (show (50202 : ℕ) ≠ 50101 by decide),
    upd_other _ _ _ (show (50202 : ℕ) ≠ 50100 by decide)]
  rw [g 50200 (by decide), g 50202 (by decide), m₁, v₁]

end

end SweepPrim

end Chazelle.Core
