module

public import Chazelle.Core.ClusterStageD1

/-!
# WP-I, part 53: stage D2 — placing the items (one step)

`placeBody`: for the preorder position `p` (register `130860`), the face `g = INV[p]` and its tail
`v = VERT[g]`; if `FIRST[v] = g` and the level of `v` is not light, place `v` at the current end
`q = CNT[b]` of its block `b = BLK[LEV[v]]`: `ACT[q] := v`, `POS[v] := q`, `CNT[b] := q + 1`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-- The placement of `v` (registers: `130863` `v`, `130865` its level). -/
def placeB : Stmt := block [.addN 130861 130065 130865, .loadN 130867 130861,
  .addN 130861 130072 130867, .loadN 130868 130861, .addN 130869 130073 130868,
  .storeN 130869 130863, .addN 130869 130074 130863, .storeN 130869 130868,
  .addN 130868 130868 130001, .storeN 130861 130868]

/-- The light test. -/
def lightB : Stmt := .seq (block [.addN 130861 130033 130863, .loadN 130865 130861,
  .addN 130861 130066 130865, .loadN 130866 130861]) (.ifLtN 130866 130001 placeB .skip)

/-- One preorder position. -/
def placeBody : Stmt := .seq (block [.addN 130861 130062 130860, .loadN 130862 130861,
  .addN 130861 130023 130862, .loadN 130863 130861, .addN 130861 130030 130863,
  .loadN 130864 130861])
  (.seq (.ifLtN 130864 130862 .skip (.ifLtN 130862 130864 .skip lightB))
    (.instr (.addN 130860 130860 130001)))

/-- **The placement** of the items in preorder. -/
def placeS : Stmt := .seq (.instr (.constN 130860 0)) (.whileLtN 130860 130014 placeBody)

/-- The registers of the placement. -/
def PLRG (r : ℕ) : Prop := 130860 ≤ r ∧ r ≤ 130869

/-- The memory written by the placement. -/
def PlMem (g : GV) (a : ℕ) : Prop := g.base 42 ≤ a ∧ a < g.base 45

section proofs

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 2000000 in
theorem placeB_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    {v l b q : ℕ} (h63 : c.nreg 130863 = v) (hv : v < g.μ) (h65 : c.nreg 130865 = l)
    (hl : l < g.μ) (hb : c.nmem (g.base 35 + l) = b) (hbμ : b < g.μ)
    (hq : c.nmem (g.base 42 + b) = q) (hqμ : q < g.μ) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W placeB c c' k ∧ k = 10 ∧ WordsBounded W c' ∧ PFr PLRG (PlMem g) c c' ∧
      c'.nreg 130860 = c.nreg 130860 ∧
      c'.nmem = upd (upd (upd c.nmem (g.base 43 + q) v) (g.base 44 + v) q)
        (g.base 42 + b) (q + 1) := by
  have hU := g.U_ge; have hE := g.END_eq; have b35 := g.base_eq 35; have b42 := g.base_eq 42
  have b43 := g.base_eq 43; have b44 := g.base_eq 44; have b45 := g.base_eq 45
  have r65 := hG.rbase 35 (by omega); have r72 := hG.rbase 42 (by omega)
  have r73 := hG.rbase 43 (by omega); have r74 := hG.rbase 44 (by omega)
  have r1 := hG.one
  unfold placeB
  exec_block
  · rw [r65, h65]; omega
  · config_simp; rw [r72, r65, h65, hb]; omega
  · config_simp; rw [r73, r72, r65, h65, hb, hq]; omega
  · config_simp; rw [r74, h63]; omega
  · config_simp; rw [r72, r65, h65, hb, hq, r1]; omega
  · refine ⟨rfl, ‹_›, ⟨fun r hr => ?_, rfl, rfl, rfl, fun a ha => ?_⟩, by config_simp, ?_⟩
    · simp only; unfold PLRG at hr
      repeat (rw [Machine.upd_other _ _ _ (by omega)])
    · config_simp; unfold PlMem at ha
      rw [r74, r73, r72, r65, h65, hb, hq, h63]
      rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (by omega)]
    · config_simp; rw [r74, r73, r72, r65, h65, hb, hq, h63, r1]

set_option maxHeartbeats 2000000 in
theorem lightB_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    {v l h b q : ℕ} (h63 : c.nreg 130863 = v) (hv : v < g.μ)
    (hlev : c.nmem (g.base 3 + v) = l) (hl : l < g.μ) (hh : c.nmem (g.base 36 + l) = h)
    (hh1 : h ≤ 1) (hb : c.nmem (g.base 35 + l) = b) (hbμ : h ≠ 1 → b < g.μ)
    (hq : c.nmem (g.base 42 + b) = q) (hqμ : h ≠ 1 → q < g.μ) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W lightB c c' k ∧ k ≤ 16 ∧ WordsBounded W c' ∧ PFr PLRG (PlMem g) c c' ∧
      c'.nreg 130860 = c.nreg 130860 ∧
      c'.nmem = if h ≠ 1 then upd (upd (upd c.nmem (g.base 43 + q) v) (g.base 44 + v) q)
        (g.base 42 + b) (q + 1) else c.nmem := by
  have hU := g.U_ge; have hE := g.END_eq; have b3 := g.base_eq 3; have b36 := g.base_eq 36
  have r33 := hG.rbase 3 (by omega); have r66 := hG.rbase 36 (by omega)
  have r1 := hG.one
  obtain ⟨c1, k1, e1, hk1, hw1, hf1, h65, h66, h63', h60, hm1⟩ : ∃ c1 k1, Exec P W
      (block [.addN 130861 130033 130863, .loadN 130865 130861,
        .addN 130861 130066 130865, .loadN 130866 130861]) c c1 k1 ∧ k1 = 4 ∧ WordsBounded W c1 ∧
      PFr PLRG (PlMem g) c c1 ∧ c1.nreg 130865 = l ∧ c1.nreg 130866 = h ∧
      c1.nreg 130863 = v ∧ c1.nreg 130860 = c.nreg 130860 ∧ c1.nmem = c.nmem := by
    exec_block
    · rw [r33, h63]; omega
    · config_simp; rw [r66, r33, h63, hlev]; omega
    · refine ⟨rfl, ‹_›, ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩, ?_, ?_, ?_,
        by config_simp, rfl⟩
      · simp only; unfold PLRG at hr
        repeat (rw [Machine.upd_other _ _ _ (by omega)])
      · config_simp; rw [r33, h63, hlev]
      · config_simp; rw [r66, r33, h63, hlev, hh]
      · config_simp; exact h63
  have hG1 : GR g c1 := hG.frame (fun r hr => hf1.1 r (by unfold GRReg at hr; unfold PLRG; omega))
  have r1' := hG1.one
  unfold lightB
  by_cases hp : h < 1
  · have hne : h ≠ 1 := by omega
    obtain ⟨c2, k2, e2, hk2, hw2, hf2, h60', hm2⟩ := placeB_exec (P := P) hw1 hG1 h63' hv h65 hl
      (by rw [hm1]; exact hb) (hbμ hne) (by rw [hm1]; exact hq) (hqμ hne) hW
    refine ⟨c2, k1 + (k2 + 1), .seq e1 (.ifLtN_true (by rw [h66, r1']; exact hp) e2), by omega,
      hw2, hf1.trans hf2, by rw [h60', h60], ?_⟩
    rw [ite_eq_left hne, hm2, hm1]
  · have he : h = 1 := by omega
    refine ⟨c1, k1 + (0 + 2), .seq e1 (.ifLtN_false (by rw [h66, r1']; exact hp) (.skip hw1)),
      by omega, hw1, hf1, h60, ?_⟩
    rw [ite_eq_right (by omega), hm1]

set_option maxHeartbeats 2000000 in
/-- **One placement step.** -/
theorem placeBody_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    {p gg v f l h b q : ℕ} (h60 : c.nreg 130860 = p) (hpN : p < g.N)
    (hinv : c.nmem (g.base 32 + p) = gg) (hgW : g.bV + gg ≤ W)
    (hvert : c.nmem (g.bV + gg) = v) (hv : v < g.μ) (hfst : c.nmem (g.base 0 + v) = f)
    (hlev : f = gg → c.nmem (g.base 3 + v) = l) (hl : f = gg → l < g.μ)
    (hh : f = gg → c.nmem (g.base 36 + l) = h) (hh1 : f = gg → h ≤ 1)
    (hb : f = gg → c.nmem (g.base 35 + l) = b) (hbμ : f = gg → h ≠ 1 → b < g.μ)
    (hq : f = gg → c.nmem (g.base 42 + b) = q) (hqμ : f = gg → h ≠ 1 → q < g.μ)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W placeBody c c' k ∧ k ≤ 30 ∧ WordsBounded W c' ∧
      PFr PLRG (PlMem g) c c' ∧ c'.nreg 130860 = p + 1 ∧
      c'.nmem = if f = gg ∧ h ≠ 1 then upd (upd (upd c.nmem (g.base 43 + q) v)
        (g.base 44 + v) q) (g.base 42 + b) (q + 1) else c.nmem := by
  have hU := g.U_ge; have hE := g.END_eq; have b32 := g.base_eq 32; have b0 := g.base_eq 0
  have hN : g.N ≤ g.U := by have := g.U_ge; omega
  have r62 := hG.rbase 32 (by omega); have r30 := hG.rbase 0 (by omega)
  have r23 := hG.rV; have r1 := hG.one
  obtain ⟨c1, k1, e1, hk1, hw1, hf1, h62, h63, h64, h60', hm1⟩ : ∃ c1 k1, Exec P W
      (block [.addN 130861 130062 130860, .loadN 130862 130861,
        .addN 130861 130023 130862, .loadN 130863 130861, .addN 130861 130030 130863,
        .loadN 130864 130861]) c c1 k1 ∧ k1 = 6 ∧ WordsBounded W c1 ∧
      PFr PLRG (PlMem g) c c1 ∧ c1.nreg 130862 = gg ∧ c1.nreg 130863 = v ∧
      c1.nreg 130864 = f ∧ c1.nreg 130860 = p ∧ c1.nmem = c.nmem := by
    exec_block
    · rw [r62, h60]; omega
    · config_simp; rw [r23, r62, h60, hinv]; omega
    · config_simp; rw [r30, r23, r62, h60, hinv, hvert]; omega
    · refine ⟨rfl, ‹_›, ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩, ?_, ?_, ?_, ?_, rfl⟩
      · simp only; unfold PLRG at hr
        repeat (rw [Machine.upd_other _ _ _ (by omega)])
      · config_simp; rw [r62, h60, hinv]
      · config_simp; rw [r23, r62, h60, hinv, hvert]
      · config_simp; rw [r30, r23, r62, h60, hinv, hvert, hfst]
      · config_simp; exact h60
  have hG1 : GR g c1 := hG.frame (fun r hr => hf1.1 r (by unfold GRReg at hr; unfold PLRG; omega))
  obtain ⟨c2, k2, e2, hk2, hw2, hf2, h60'', hm2⟩ : ∃ c2 k2, Exec P W
      (.ifLtN 130864 130862 .skip (.ifLtN 130862 130864 .skip lightB)) c1 c2 k2 ∧ k2 ≤ 20 ∧
      WordsBounded W c2 ∧ PFr PLRG (PlMem g) c1 c2 ∧ c2.nreg 130860 = p ∧
      c2.nmem = if f = gg ∧ h ≠ 1 then upd (upd (upd c.nmem (g.base 43 + q) v)
        (g.base 44 + v) q) (g.base 42 + b) (q + 1) else c.nmem := by
    by_cases h1 : f < gg
    · refine ⟨c1, 0 + 1, .ifLtN_true (by rw [h64, h62]; exact h1) (.skip hw1), by omega, hw1,
        PFr.refl c1, h60', ?_⟩
      rw [ite_eq_right (by omega), hm1]
    by_cases h2 : gg < f
    · refine ⟨c1, (0 + 1) + 2, .ifLtN_false (by rw [h64, h62]; exact h1)
        (.ifLtN_true (by rw [h64, h62]; exact h2) (.skip hw1)), by omega, hw1,
        PFr.refl c1, h60', ?_⟩
      rw [ite_eq_right (by omega), hm1]
    have hfg : f = gg := by omega
    obtain ⟨c3, k3, e3, hk3, hw3, hf3, h603, hm3⟩ := lightB_exec (P := P) hw1 hG1 h63 hv
      (by rw [hm1]; exact hlev hfg) (hl hfg) (by rw [hm1]; exact hh hfg) (hh1 hfg)
      (by rw [hm1]; exact hb hfg) (hbμ hfg) (by rw [hm1]; exact hq hfg) (hqμ hfg) hW
    refine ⟨c3, (k3 + 2) + 2, .ifLtN_false (by rw [h64, h62]; exact h1)
      (.ifLtN_false (by rw [h64, h62]; exact h2) e3), by omega, hw3, hf3,
      by rw [h603]; exact h60', ?_⟩
    rw [hm3, hm1]
    by_cases hh' : h ≠ 1
    · rw [ite_eq_left hh', ite_eq_left ⟨hfg, hh'⟩]
    · rw [ite_eq_right hh', ite_eq_right (fun hc => hh' hc.2)]
  have r1' : c2.nreg 130001 = 1 := by
    rw [hf2.1 _ (by unfold PLRG; omega), hf1.1 _ (by unfold PLRG; omega)]; exact r1
  have e3 := Exec.addN (P := P) hw2 130860 130860 130001 (by rw [h60'', r1']; omega)
  refine ⟨_, k1 + (k2 + 1), .seq e1 (.seq e2 e3), by omega, e3.wb_right,
    (hf1.trans hf2).trans ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩, ?_, hm2⟩
  · simp only [Machine.upd_other _ _ _ (show r ≠ 130860 by unfold PLRG at hr; omega)]
  · simp only [Machine.upd_same]; rw [h60'', r1']

end proofs

end

end Chazelle.Core.Cluster
