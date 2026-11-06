module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.ClusterLabel
public import Chazelle.Core.ClusterBfsRam

/-!
# WP-I, part 5: component labelling on the RAM

`labelStmt`: fill the label array with the sentinel `nv`, then for `v = 0, …, nv - 1` run the
breadth-first search `bfsStmt` from `v` with label `v` if `v` is unblocked and unlabelled.
`labelStmt_exec`: at most `120 nv + 50 N + 10` steps; afterwards every unblocked vertex carries a
label `< nv`, and two unblocked vertices carry the same label iff they are connected through
unblocked darts and vertices (for a symmetric rotation system, `Env.Sym`).

Registers: those of `bfsStmt` (`130001`, the layout `130100 … 130110`; `130111`, `130112` are set
here), the loop counter `130140` and the scratch registers `130141`, `130142`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-! ## The program -/

/-- One cell of the fill: `lab i := nv`, `i := i + 1`. -/
def fillBody : Stmt := block [.addN 130141 130106 130140, .storeN 130141 130110,
  .addN 130140 130140 130001]

/-- Fill the label array with the sentinel. -/
def fillLoop : Stmt := .whileLtN 130140 130110 fillBody

/-- The search from `v` with label `v`. -/
def searchV : Stmt := .seq (block [.copyN 130111 130140, .copyN 130112 130140]) bfsStmt

/-- Search from `v` unless it is labelled. -/
def unlabB : Stmt := .seq (block [.addN 130141 130106 130140, .loadN 130142 130141])
  (.ifLtN 130142 130110 .skip searchV)

/-- One vertex of the driver. -/
def drvBody : Stmt := .seq (block [.addN 130141 130105 130140, .loadN 130142 130141])
  (.seq (ifNe1 130142 unlabB) (.instr (.addN 130140 130140 130001)))

/-- The driver loop. -/
def drvLoop : Stmt := .whileLtN 130140 130110 drvBody

/-- **Component labelling.** -/
def labelStmt : Stmt :=
  .seq (.instr (.constN 130140 0)) (.seq fillLoop (.seq (.instr (.constN 130140 0)) drvLoop))

/-! ## Registers and frame -/

/-- The layout registers of the labelling (all those of `Regs` but the label and the source). -/
structure Regs0 (Y : Lay) (c : Config) : Prop where
  one : c.nreg 130001 = 1
  rO : c.nreg 130100 = Y.bO
  rR : c.nreg 130101 = Y.bR
  rV : c.nreg 130102 = Y.bV
  rF : c.nreg 130103 = Y.bF
  rDB : c.nreg 130104 = Y.bDB
  rVB : c.nreg 130105 = Y.bVB
  rLab : c.nreg 130106 = Y.bLab
  rLev : c.nreg 130107 = Y.bLev
  rPar : c.nreg 130108 = Y.bPar
  rQ : c.nreg 130109 = Y.bQ
  rn : c.nreg 130110 = Y.nv

theorem Regs0.regs {Y : Lay} {c : Config} (h : Regs0 Y c) {s L : ℕ} (hL : c.nreg 130111 = L)
    (hs : c.nreg 130112 = s) : Regs Y s L c :=
  ⟨h.one, h.rO, h.rR, h.rV, h.rF, h.rDB, h.rVB, h.rLab, h.rLev, h.rPar, h.rQ, h.rn, hL, hs⟩

/-- The registers written by the labelling. -/
def LScr (r : ℕ) : Prop := r = 130111 ∨ r = 130112 ∨ Scr r ∨ (130140 ≤ r ∧ r ≤ 130142)

/-- **The frame of the labelling**: only its registers and the written arrays change. -/
def LFr (Y : Lay) (c0 c : Config) : Prop :=
  (∀ r, ¬ LScr r → c.nreg r = c0.nreg r) ∧ c.rreg = c0.rreg ∧ c.rmem = c0.rmem ∧
    c.output = c0.output ∧ ∀ a, ¬ Y.Written a → c.nmem a = c0.nmem a

theorem LFr.trans {Y : Lay} {c0 c1 c2 : Config} (h1 : LFr Y c0 c1) (h2 : LFr Y c1 c2) :
    LFr Y c0 c2 :=
  ⟨fun r hr => (h2.1 r hr).trans (h1.1 r hr), h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
    h2.2.2.2.1.trans h1.2.2.2.1, fun a ha => (h2.2.2.2.2 a ha).trans (h1.2.2.2.2 a ha)⟩

theorem LFr.of_fr {Y : Lay} {c0 c : Config} (h : Fr Y c0 c) : LFr Y c0 c :=
  ⟨fun r hr => h.1 r (fun h' => hr (Or.inr (Or.inr (Or.inl h')))), h.2.1, h.2.2.1, h.2.2.2.1,
    h.2.2.2.2⟩

theorem LFr.nreg {Y : Lay} {c0 c : Config} (hf : LFr Y c0 c) {f : ℕ → ℕ}
    (hfr : ∀ r, ¬ LScr r → f r = c.nreg r) : LFr Y c0 { c with nreg := f } :=
  ⟨fun r hr => (hfr r hr).trans (hf.1 r hr), hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩

theorem Regs0.lfr {Y : Lay} {c0 c : Config} (h : Regs0 Y c0) (hf : LFr Y c0 c) : Regs0 Y c := by
  have k := hf.1
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rwa [k _ (by unfold LScr Scr; omega)])

/-! ## The fill -/

section fill

variable {P : Polygon} {W : ℕ} {Y : Lay}

/-- **The fill** of the label array with the sentinel `nv`: cost `≤ 5 nv + 2`. -/
theorem fillLoop_exec (hY : Y.Good W) {c : Config} (hw : WordsBounded W c) (hR : Regs0 Y c)
    (h0 : c.nreg 130140 = 0) :
    ∃ c' k, Exec P W fillLoop c c' k ∧ k ≤ 5 * Y.nv + 2 ∧ WordsBounded W c' ∧ LFr Y c c' ∧
      c'.nreg 130140 = Y.nv ∧ ∀ x, x < Y.nv → labV Y c'.nmem x = Y.nv := by
  have := hY.wLab; have := hY.wn
  obtain ⟨c', k, e, ⟨hw', hf', hle, hlab⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := 130140) (b := 130110) (body := fillBody)
    (fun c' => WordsBounded W c' ∧ LFr Y c c' ∧ c'.nreg 130140 ≤ Y.nv ∧
      ∀ x, x < c'.nreg 130140 → labV Y c'.nmem x = Y.nv)
    (fun c' => 5 * (Y.nv - c'.nreg 130140)) (fun c' h => h.1)
    (fun c1 ⟨hw1, hf1, hle1, hl1⟩ htest => by
      have hR1 := hR.lfr hf1
      Ξ' hR1.rn at htest
      unfold fillBody
      exec_block
      · rw [hR1.rLab]; omega
      · config_simp; rw [hR1.one]; omega
      · refine ⟨⟨‹_›, ?_, ?_, fun x hx => ?_⟩, ?_⟩
        · refine ⟨fun r hr => ?_, hf1.2.1, hf1.2.2.1, hf1.2.2.2.1, fun a ha => ?_⟩
          · ϴ Machine.upd_apply
            split_ifs with h1 h2
            · exact absurd (Or.inr (Or.inr (Or.inr ⟨⋄, ⋄⟩))) (h1 ▸ hr)
            · exact absurd (Or.inr (Or.inr (Or.inr ⟨⋄, ⋄⟩))) (h2 ▸ hr)
            · exact hf1.1 r hr
          · ϴ Machine.upd_apply, hR1.rLab
            unfold Lay.Written at ha
            split_ifs with h1
            · omega
            · exact hf1.2.2.2.2 a ha
        · config_simp; rw [hR1.one]; omega
        · config_simp
          Ξ' hR1.one at hx
          unfold labV
          Ξ hR1.rLab, hR1.rn, view_upd_in _ _ _ _ _ htest
          rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
          · rw [Function.update_of_ne (⋄)]; exact hl1 x hx
          · Ξ Function.update_self
        · config_simp; rw [hR1.one]; omega)
    ⟨hw, ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩, ⋄, fun x hx => ⋄⟩
  have hR' := hR.lfr hf'
  Ξ' hR'.rn at htest
  refine ⟨c', k, e, by rw [h0] at hk; omega, hw', hf', ⋄,
    fun x hx => hlab x (⋄)⟩

end fill

/-! ## The driver -/

/-- The unlabelled vertices of a label array. -/
def unlab (Y : Lay) (m : ℕ → ℕ) : Finset ℕ := (Finset.range Y.nv).filter (fun x => labV Y m x = Y.nv)

/-- The potential of the driver. -/
def drvPot (Y : Lay) (G : Env) (c : Config) : ℕ :=
  40 * (Y.nv - c.nreg 130140) + 70 * (unlab Y c.nmem).card + 50 * ∑ x ∈ unlab Y c.nmem, G.deg x

/-- **The invariant of the driver** (relative to the entry configuration `cE`). -/
structure DI (Y : Lay) (W : ℕ) (cE c : Config) : Prop where
  wb : WordsBounded W c
  fr : LFr Y cE c
  vle : c.nreg 130140 ≤ Y.nv
  inv : (Y.env cE.nmem).LInv (labV Y c.nmem) (c.nreg 130140)

section drv

variable {P : Polygon} {W : ℕ} {Y : Lay} {cE : Config}

/-- The labelling frame keeps the rotation system. -/
theorem LFr.env (hY : Y.Good W) {c : Config} (hf : LFr Y cE c) : Y.env c.nmem = Y.env cE.nmem :=
  Lay.env_congr hY hf.2.2.2.2

/-- Reading a read-only array through the labelling frame. -/
theorem LFr.read (hY : Y.Good W) {c : Config} (hf : LFr Y cE c) {b n i : ℕ}
    (hb : (b = Y.bO ∧ n = Y.N) ∨ (b = Y.bR ∧ n = Y.N) ∨ (b = Y.bV ∧ n = Y.N) ∨
      (b = Y.bF ∧ n = Y.nv) ∨ (b = Y.bDB ∧ n = Y.N) ∨ (b = Y.bVB ∧ n = Y.nv)) (hi : i < n) :
    c.nmem (b + i) = view cE.nmem b n i := by
  Ξ view_lt hi
  refine hf.2.2.2.2 _ ?_
  obtain ⟨h1, h2, h3, h4⟩ := hY.d1 b n hb
  unfold Lay.Written Disj at *
  omega

/-- **One vertex of the driver**: skip it if blocked or labelled, otherwise search from it. -/
theorem drvBody_exec (hY : Y.Good W) (hR : Regs0 Y cE) (hok : (Y.env cE.nmem).OK)
    (hs : (Y.env cE.nmem).Sym) {c : Config} (hI : DI Y W cE c) (hlt : c.nreg 130140 < Y.nv) :
    ∃ c' k, Exec P W drvBody c c' k ∧ DI Y W cE c' ∧
      drvPot Y (Y.env cE.nmem) c' + k + 2 ≤ drvPot Y (Y.env cE.nmem) c := by
  have hRc := hR.lfr hI.fr
  have hw := hI.wb
  have := hY.wVB; have := hY.wLab; have := hY.wn
  have rvb : c.nmem (Y.bVB + c.nreg 130140) = (Y.env cE.nmem).vb (c.nreg 130140) :=
    LFr.read hY hI.fr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))) hlt
  have rlab : c.nmem (Y.bLab + c.nreg 130140) = labV Y c.nmem (c.nreg 130140) := by
    Ξ labV, view_lt hlt
  -- the final increment, common to all cases
  have fin : ∀ c2 : Config, WordsBounded W c2 → LFr Y cE c2 →
      c2.nreg 130140 = c.nreg 130140 →
      (Y.env cE.nmem).LInv (labV Y c2.nmem) (c.nreg 130140 + 1) →
      ∃ c3, Exec P W (.instr (.addN 130140 130140 130001)) c2 c3 1 ∧ DI Y W cE c3 ∧
        c3.nreg 130140 = c.nreg 130140 + 1 ∧ c3.nmem = c2.nmem := by
    intro c2 hw2 hf2 hv2 hL2
    have hone : c2.nreg 130001 = 1 := (hR.lfr hf2).one
    have e := Exec.addN (P := P) hw2 130140 130140 130001 (by rw [hone, hv2]; omega)
    refine ⟨_, e, ⟨e.wb_right, LFr.nreg hf2 (fun r hr => ?_), ?_, ?_⟩, ?_, rfl⟩
    · rw [Machine.upd_other _ _ _ (fun h => hr (Or.inr (Or.inr (Or.inr ⟨⋄, by omega⟩))))]
    · simp only [Machine.upd_same]; rw [hone, hv2]; omega
    · simp only [Machine.upd_same]; rw [hone, hv2]; exact hL2
    · simp only [Machine.upd_same]; rw [hone, hv2]
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, hX1, hr1, hrr1, hrm1, ho1⟩ : ∃ c1 k1,
      Exec P W (block [.addN 130141 130105 130140, .loadN 130142 130141]) c c1 k1 ∧ k1 = 2 ∧
      WordsBounded W c1 ∧ c1.nmem = c.nmem ∧
      c1.nreg 130142 = (Y.env cE.nmem).vb (c.nreg 130140) ∧
      (∀ r, r ≠ 130141 → r ≠ 130142 → c1.nreg r = c.nreg r) ∧ c1.rreg = c.rreg ∧
      c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    · rw [hRc.rVB]; omega
    · refine ⟨rfl, ‹_›, rfl, by config_simp; rw [hRc.rVB, rvb], fun r h1 h2 => ?_, rfl, rfl,
        rfl⟩
      ϴ Machine.upd_apply, h1, h2, ite_false
  have hf1 : LFr Y cE c1 := by
    refine ⟨fun r hr => ?_, hrr1.trans hI.fr.2.1, hrm1.trans hI.fr.2.2.1, ho1.trans hI.fr.2.2.2.1,
      fun a ha => by rw [hm1]; exact hI.fr.2.2.2.2 a ha⟩
    rw [hr1 r (fun h => hr (Or.inr (Or.inr (Or.inr ⟨⋄, by omega⟩))))
      (fun h => hr (Or.inr (Or.inr (Or.inr ⟨⋄, by omega⟩))))]
    exact hI.fr.1 r hr
  have hv1 : c1.nreg 130140 = c.nreg 130140 := hr1 _ (⌖) (by decide)
  have hone1 : c1.nreg 130001 = 1 := (hR.lfr hf1).one
  have hpot : ∀ c3 : Config, c3.nreg 130140 = c.nreg 130140 + 1 → c3.nmem = c.nmem →
      drvPot Y (Y.env cE.nmem) c3 + 40 = drvPot Y (Y.env cE.nmem) c := by
    intro c3 hv3 hm3
    unfold drvPot
    Ξ hv3, hm3
    omega
  by_cases hvb : (Y.env cE.nmem).vb (c.nreg 130140) = 1
  · -- blocked: skip
    obtain ⟨c3, e3, hD3, hv3, hm3⟩ := fin c1 hw1 hf1 hv1 (by
      rw [hm1]; exact hI.inv.skip (Or.inl hvb))
    refine ⟨c3, 2 + (4 + 1), .seq (hk1 ▸ e1) (.seq (ifNe1_skip hw1 hone1 (by rw [hX1]; exact hvb))
      e3), hD3, ?_⟩
    have := hpot c3 hv3 (hm3.trans hm1)
    omega
  · have hX1' : c1.nreg 130142 ≠ 1 := by rw [hX1]; exact hvb
    -- load the label
    obtain ⟨c2, k2, e2, hk2, hw2, hm2, hX2, hr2, hrr2, hrm2, ho2⟩ : ∃ c2 k2,
        Exec P W (block [.addN 130141 130106 130140, .loadN 130142 130141]) c1 c2 k2 ∧ k2 = 2 ∧
        WordsBounded W c2 ∧ c2.nmem = c.nmem ∧
        c2.nreg 130142 = labV Y c.nmem (c.nreg 130140) ∧
        (∀ r, r ≠ 130141 → r ≠ 130142 → c2.nreg r = c1.nreg r) ∧ c2.rreg = c1.rreg ∧
        c2.rmem = c1.rmem ∧ c2.output = c1.output := by
      have hRc1 := hR.lfr hf1
      exec_block
      · rw [hRc1.rLab, hv1]; omega
      · refine ⟨rfl, ‹_›, hm1, by config_simp; rw [hRc1.rLab, hv1, hm1, rlab], fun r h1 h2 => ?_,
          rfl, rfl, rfl⟩
        ϴ Machine.upd_apply, h1, h2, ite_false
    have hf2 : LFr Y cE c2 := by
      refine ⟨fun r hr => ?_, hrr2.trans hf1.2.1, hrm2.trans hf1.2.2.1, ho2.trans hf1.2.2.2.1,
        fun a ha => by rw [hm2]; exact hI.fr.2.2.2.2 a ha⟩
      rw [hr2 r (fun h => hr (Or.inr (Or.inr (Or.inr ⟨⋄, by omega⟩))))
        (fun h => hr (Or.inr (Or.inr (Or.inr ⟨⋄, by omega⟩))))]
      exact hf1.1 r hr
    have hv2 : c2.nreg 130140 = c.nreg 130140 := (hr2 _ (⌖) (by decide)).trans hv1
    have hRc2 := hR.lfr hf2
    by_cases hl : labV Y c.nmem (c.nreg 130140) < Y.nv
    · -- labelled: skip
      obtain ⟨c3, e3, hD3, hv3, hm3⟩ := fin c2 hw2 hf2 hv2 (by
        rw [hm2]; exact hI.inv.skip (Or.inr (by simp only [Lay.env_nv]; omega)))
      have hlt2 : c2.nreg 130142 < c2.nreg 130110 := by rw [hX2, hRc2.rn]; exact hl
      have eU : Exec P W unlabB c1 c2 (k2 + (0 + 1)) :=
        Exec.seq e2 (.ifLtN_true hlt2 (.skip hw2))
      obtain ⟨k', e', hk'⟩ := ifNe1_run (P := P) (W := W) hone1 hX1' eU
      refine ⟨c3, 2 + (k' + 1), .seq (hk1 ▸ e1) (.seq e' e3), hD3, ?_⟩
      have := hpot c3 hv3 (hm3.trans hm2)
      omega
    · -- unlabelled: search
      have hlv : labV Y c.nmem (c.nreg 130140) = Y.nv := by
        by_contra hne
        exact hl (hI.inv.lbl _ hlt hne).1
      -- set the label and the source
      obtain ⟨c3, e3, hw3, hm3, h111, h112, hr3, hrr3, hrm3, ho3⟩ : ∃ c3,
          Exec P W (block [.copyN 130111 130140, .copyN 130112 130140]) c2 c3 2 ∧
          WordsBounded W c3 ∧ c3.nmem = c.nmem ∧ c3.nreg 130111 = c.nreg 130140 ∧
          c3.nreg 130112 = c.nreg 130140 ∧
          (∀ r, r ≠ 130111 → r ≠ 130112 → c3.nreg r = c2.nreg r) ∧ c3.rreg = c2.rreg ∧
          c3.rmem = c2.rmem ∧ c3.output = c2.output := by
        have := Exec.copyN (P := P) hw2 130111 130140
        have h2 := Exec.copyN (P := P) this.wb_right 130112 130140
        refine ⟨_, Exec.block_cons this (Exec.block_cons h2 (Exec.block_nil h2.wb_right)),
          h2.wb_right, hm2, ?_, ?_, fun r a b => ?_, rfl, rfl, rfl⟩
        · Θ hv2
        · Θ hv2
        · Θ a, b
      have hf3 : LFr Y cE c3 := by
        refine ⟨fun r hr => ?_, hrr3.trans hf2.2.1, hrm3.trans hf2.2.2.1, ho3.trans hf2.2.2.2.1,
          fun a ha => by rw [hm3]; exact hI.fr.2.2.2.2 a ha⟩
        Ξ hr3 r (fun h => hr (Or.inl h)) (fun h => hr (Or.inr (Or.inl h)))
        exact hf2.1 r hr
      have hR3 : Regs Y (c.nreg 130140) (c.nreg 130140) c3 := (hR.lfr hf3).regs h111 h112
      have henv3 : Y.env c3.nmem = Y.env cE.nmem := hf3.env hY
      have hlab3 : labV Y c3.nmem = labV Y c.nmem := Ρ hm3
      have hp : (Y.env c3.nmem).Pre (c.nreg 130140) (c.nreg 130140) (labV Y c3.nmem) := by
        Ξ henv3, hlab3
        exact ⟨hok, hlt, hvb, hlt, hI.inv.fresh hok hs hlt hlv⟩
      obtain ⟨c4, k4, e4, hk4, hOI, hht⟩ := bfs_exec (P := P) hY hR3 hp hw3
      rw [henv3] at hk4
      have hB : (Y.env cE.nmem).Inv (c.nreg 130140) (c.nreg 130140) (labV Y c.nmem)
          (labV Y c4.nmem) (levV Y c4.nmem) (parV Y c4.nmem) (qV Y c4.nmem) (c4.nreg 130121)
          (c4.nreg 130121) := by
        have := hOI.inv
        rw [henv3, hlab3, hht] at this
        exact this
      have hf4 : LFr Y cE c4 := hf3.trans (LFr.of_fr hOI.fr)
      have hv4 : c4.nreg 130140 = c.nreg 130140 := by
        rw [hOI.fr.1 _ (by unfold Scr; omega), hr3 _ (⌖) (by decide), hv2]
      have hL4 := hI.inv.bfs hok hs hlt hB
      obtain ⟨c5, e5, hD5, hv5, hm5⟩ := fin c4 hOI.wb hf4 hv4 hL4
      have hge2 : ¬ c2.nreg 130142 < c2.nreg 130110 := by rw [hX2, hRc2.rn]; exact hl
      have eU : Exec P W unlabB c1 c4 (k2 + ((2 + k4) + 2)) :=
        Exec.seq e2 (.ifLtN_false hge2 (Exec.seq e3 e4))
      obtain ⟨k', e', hk'⟩ := ifNe1_run (P := P) (W := W) hone1 hX1' eU
      refine ⟨c5, 2 + (k' + 1), .seq (hk1 ▸ e1) (.seq e' e5), hD5, ?_⟩
      -- the potential
      obtain ⟨hcard, hsum⟩ := hI.inv.unlab_split hok hs hlt hlv hB
      have hcard' : (unlab Y c4.nmem).card + c4.nreg 130121 = (unlab Y c.nmem).card := hcard
      have hsum' : ∑ x ∈ unlab Y c4.nmem, (Y.env cE.nmem).deg x +
          ∑ i ∈ Finset.range (c4.nreg 130121), (Y.env cE.nmem).deg (qV Y c4.nmem i) =
          ∑ x ∈ unlab Y c.nmem, (Y.env cE.nmem).deg x := hsum
      unfold drvPot
      Ξ hv5, hm5
      have hsl : c.nreg 130140 + 1 ≤ Y.nv := hlt
      omega

end drv

/-! ## The whole labelling -/

section main

variable {P : Polygon} {W : ℕ} {Y : Lay}

/-- **Component labelling on the RAM.**  On a good layout (`Regs0`) whose rotation system is
well formed and symmetric, `labelStmt` runs in at most `120 nv + 50 N + 10` steps, writes only its
registers and the arrays `lab`, `lev`, `par`, `q` (`LFr`), gives every unblocked vertex a label
`< nv`, and two unblocked vertices get the same label iff they are connected. -/
theorem labelStmt_exec (hY : Y.Good W) {c : Config} (hw : WordsBounded W c) (hR : Regs0 Y c)
    (hok : (Y.env c.nmem).OK) (hs : (Y.env c.nmem).Sym) :
    ∃ c' k, Exec P W labelStmt c c' k ∧ k ≤ 120 * Y.nv + 50 * Y.N + 10 ∧ WordsBounded W c' ∧
      LFr Y c c' ∧
      (∀ x, x < Y.nv → (Y.env c.nmem).vb x ≠ 1 → labV Y c'.nmem x < Y.nv) ∧
      ∀ x y, x < Y.nv → y < Y.nv → (Y.env c.nmem).vb x ≠ 1 → (Y.env c.nmem).vb y ≠ 1 →
        (labV Y c'.nmem x = labV Y c'.nmem y ↔ (Y.env c.nmem).Reach x y) := by
  have := hY.wn
  have e1 := Exec.constN (P := P) hw 130140 0 (by omega)
  set c1 := { c with nreg := upd c.nreg 130140 0 }
  have hf1 : LFr Y c c1 := LFr.nreg ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
    (fun r hr => Machine.upd_other _ _ _ (fun h => hr (Or.inr (Or.inr (Or.inr
      ⟨by omega, by omega⟩)))))
  obtain ⟨c2, k2, e2, hk2, hw2, hf2, hv2, hlab2⟩ := fillLoop_exec (P := P) hY e1.wb_right
    (hR.lfr hf1) (by simp [c1])
  have hf12 := hf1.trans hf2
  have e3 := Exec.constN (P := P) hw2 130140 0 (by omega)
  set c3 := { c2 with nreg := upd c2.nreg 130140 0 }
  have hf3 : LFr Y c c3 := LFr.nreg hf12
    (fun r hr => Machine.upd_other _ _ _ (fun h => hr (Or.inr (Or.inr (Or.inr
      ⟨by omega, by omega⟩)))))
  have henv3 : Y.env c3.nmem = Y.env c.nmem := hf3.env hY
  have hD3 : DI Y W c c3 := ⟨e3.wb_right, hf3, by simp [c3], by
    simp only [c3, Machine.upd_same]
    exact Env.LInv.init (fun x hx => hlab2 x hx)⟩
  obtain ⟨c4, k4, e4, hD4, htest, hk4⟩ := whileLtN_pot (P := P) (W := W) (a := 130140)
    (b := 130110) (body := drvBody) (DI Y W c) (drvPot Y (Y.env c.nmem)) (fun c h => h.wb)
    (fun c' hD htest => by
      have := (hR.lfr hD.fr).rn
      rw [this] at htest
      exact drvBody_exec hY hR hok hs hD htest) hD3
  have hv4 : c4.nreg 130140 = Y.nv := by
    have := (hR.lfr hD4.fr).rn
    have := hD4.vle
    omega
  have hL4 := hD4.inv
  rw [hv4] at hL4
  obtain ⟨hfin1, hfin2⟩ := hL4.final hok hs
  refine ⟨c4, 1 + (k2 + (1 + k4)), .seq e1 (.seq e2 (.seq e3 e4)), ?_, hD4.wb, hD4.fr, hfin1,
    hfin2⟩
  -- the cost
  have hU3 : unlab Y c3.nmem = Finset.range Y.nv := by
    unfold unlab
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, and_iff_left_iff_imp]
    intro hx
    exact hlab2 x hx
  have hpot3 : drvPot Y (Y.env c.nmem) c3 = 40 * Y.nv + 70 * Y.nv + 50 * Y.N := by
    unfold drvPot
    have hsd : ∑ x ∈ Finset.range Y.nv, (Y.env c.nmem).deg x = Y.N := hok.sum_deg
    rw [hU3, Finset.card_range, hsd]
    simp [c3]
  omega

end main

end

end Chazelle.Core.Cluster
