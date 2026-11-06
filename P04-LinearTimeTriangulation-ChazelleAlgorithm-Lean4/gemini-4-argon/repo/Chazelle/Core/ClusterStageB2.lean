module

public import Chazelle.Core.ClusterStageB1
public import Chazelle.Core.ClusterEulerRam

/-!
# WP-I, part 47: stage B2 — the dual search, the preorder intervals and the dual table

After stage B1: `DLAB := N` (slot `24`), the breadth-first search from face `0` on the dual of the
star map with the star tree darts blocked (levels slot `25`, parent darts `FPAR` slot `26`, queue
`DQ` slot `27`), `FPAR[0] := 0`, the preorder intervals of its tree (`FSZ` slot `28`, `FPRE` slot
`29`, `SLOT` slot `30`), the parent array `PF` (slot `31`) and the table `UP` of its powers.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs
open Chazelle.Separator Chazelle.Separator.CombMap

@[expose] public section

/-- The dual search, then `FPAR[0] := 0`. -/
def dbfsP : Stmt := .seq (block [.copyN 130100 130041, .copyN 130101 130044,
  .copyN 130102 130047, .copyN 130103 130050, .copyN 130104 130051, .copyN 130105 130031,
  .copyN 130106 130054, .copyN 130107 130055, .copyN 130108 130056, .copyN 130109 130057,
  .copyN 130110 130014, .constN 130111 0, .constN 130112 0])
  (.seq bfsStmt (.instr (.storeN 130056 130009)))

/-- The preorder intervals. -/
def eulerP : Stmt := .seq (block [.copyN 130200 130057, .copyN 130201 130056,
  .copyN 130202 130047, .copyN 130203 130058, .copyN 130204 130059, .copyN 130205 130060,
  .copyN 130206 130014]) eulerStmt

/-- The dual parent array `PF`. -/
def pfP : Stmt := .seq (block [.copyN 130500 130047, .copyN 130501 130056, .copyN 130502 130061,
  .copyN 130503 130014]) parStmt

/-- The dual table `UP`. -/
def updP : Stmt := .seq (block [.copyN 130510 130061, .copyN 130511 130085, .copyN 130512 130014,
  .copyN 130513 130017]) upStmt

/-- **Stage B2.** -/
def stageB2 : Stmt := .seq (fillWith 130054 130014 130014) (.seq dbfsP (.seq eulerP
  (.seq pfP updP)))

/-- The layout of the dual search. -/
def dualLay (g : GV) : Lay := ⟨g.base 11, g.base 14, g.base 17, g.base 20, g.base 21, g.base 1,
  g.base 24, g.base 25, g.base 26, g.base 27, g.N, 3 * g.N⟩

/-- The tree of the dual search read from memory. -/
def dtree (g : GV) (m : ℕ → ℕ) : BTree :=
  ⟨g.N, fun i => m (g.base 27 + i), fun x => m (g.base 17 + m (g.base 26 + x))⟩

section proofs

variable {P : Polygon} {W : ℕ}

theorem dualLay_good {g : GV} (hW : g.END ≤ W) : (dualLay g).Good W := by
  have hU := g.U_ge
  have hE := g.END_eq
  have b1 := g.base_eq 1; have b11 := g.base_eq 11; have b14 := g.base_eq 14
  have b17 := g.base_eq 17; have b20 := g.base_eq 20; have b21 := g.base_eq 21
  have b24 := g.base_eq 24; have b25 := g.base_eq 25; have b26 := g.base_eq 26
  have b27 := g.base_eq 27
  refine ⟨fun b n h => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [dualLay, Disj] at *
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  all_goals first | omega

set_option maxHeartbeats 4000000 in
open Classical in
theorem dbfsP_exec {g : GV} {F : Type} [Fintype F] [DecidableEq F]
    {M : CombMap (Fin g.μ) F (Fin g.N)} {T : SpanTree M} {a : F → Fin g.N}
    {ha : ∀ f, M.face (a f) = f} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    (hA : AF g M T c.nmem) (hB : B1F g M T a ha c.nmem) (hM : M.Connected) (hN : 0 < g.N)
    (hdl : ∀ x, x < g.N → c.nmem (g.base 24 + x) = g.N) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W dbfsP c c' k ∧ k ≤ 220 * g.N + 30 ∧ WordsBounded W c' ∧
      PFr StBRG (fun a => g.base 24 ≤ a ∧ a < g.base 28) c c' ∧
      ∃ C : CoTree (starTree T a ha), (C.r0 : ℕ) = 0 ∧
        (∀ x : Fin g.N, x ≠ C.r0 → c'.nmem (g.base 26 + x) = enc g.N (C.fpar x)) ∧
        (∀ x, x < g.N → c'.nmem (g.base 26 + x) < 3 * g.N) ∧ (dtree g c'.nmem).OK ∧
        (dtree g c'.nmem).q 0 = 0 ∧ ∀ x : Fin g.N, (dtree g c'.nmem).up x = C.parent x := by
  have hU := g.U_ge
  have hE := g.END_eq
  have b1 := g.base_eq 1; have b7 := g.base_eq 7; have b8 := g.base_eq 8
  have b11 := g.base_eq 11; have b14 := g.base_eq 14
  have b17 := g.base_eq 17; have b20 := g.base_eq 20; have b21 := g.base_eq 21
  have b24 := g.base_eq 24; have b25 := g.base_eq 25; have b26 := g.base_eq 26
  have b27 := g.base_eq 27; have b28 := g.base_eq 28
  set Y := dualLay g with hY
  have hYg : Y.Good W := dualLay_good hW
  unfold dbfsP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, hR1, hf1⟩ : ∃ c1 k1, Exec P W (block [.copyN 130100 130041,
      .copyN 130101 130044, .copyN 130102 130047, .copyN 130103 130050, .copyN 130104 130051,
      .copyN 130105 130031, .copyN 130106 130054, .copyN 130107 130055, .copyN 130108 130056,
      .copyN 130109 130057, .copyN 130110 130014, .constN 130111 0, .constN 130112 0]) c c1 k1 ∧
      k1 = 13 ∧ WordsBounded W c1 ∧ c1.nmem = c.nmem ∧ Regs Y 0 0 c1 ∧
      PFr StBRG (fun a => g.base 24 ≤ a ∧ a < g.base 28) c c1 := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ‹_›, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      ⟨fun r hr => ?fr, rfl, rfl, rfl, fun a _ => rfl⟩⟩
    case fr =>
      simp only
      unfold StBRG at hr
      repeat (rw [Machine.upd_other _ _ _ (by omega)])
    all_goals try (config_simp <;>
                   first
                   | exact hG.one
                   | exact hG.rN
                   | exact hG.rbase 1 (by omega)
                   | exact hG.rbase 11 (by omega)
                   | exact hG.rbase 14 (by omega)
                   | exact hG.rbase 17 (by omega)
                   | exact hG.rbase 20 (by omega)
                   | exact hG.rbase 21 (by omega)
                   | exact hG.rbase 24 (by omega)
                   | exact hG.rbase 25 (by omega)
                   | exact hG.rbase 26 (by omega)
                   | exact hG.rbase 27 (by omega))
  -- the rotation system
  set G := Y.env c1.nmem with hGdef
  have hview : ∀ b n i, i < n → view c1.nmem b n i = c.nmem (b + i) := fun b n i hi => by
    rw [view_lt hi, hm1]
  have hGenc : EnvEnc G (star M).dual (fun f => (f : ℕ)) (enc g.N) := by
    refine star_dual_enc (opp := fun x => c.nmem (g.base 11 + x))
      (fp := fun x => c.nmem (g.base 7 + x)) (fpi := fun x => c.nmem (g.base 8 + x))
      (fun d => (hB.so d).1) hB.fp hB.fpi rfl rfl (fun d hd => ?_) (fun d hd => ?_)
      (fun d hd => ?_) (fun d hd => ?_)
    · obtain ⟨h1, h2, h3⟩ := hB.so ⟨d, hd⟩
      refine ⟨hview (g.base 11) (3 * g.N) d (by omega), ?_, ?_⟩
      · show view c1.nmem (g.base 11) (3 * g.N) (g.N + d) = _
        rw [hview _ _ _ (by omega), ← Nat.add_assoc]; exact h2
      · show view c1.nmem (g.base 11) (3 * g.N) (2 * g.N + d) = _
        rw [hview _ _ _ (by omega), ← Nat.add_assoc]; exact h3
    · obtain ⟨h1, h2, h3⟩ := hB.sr ⟨d, hd⟩
      refine ⟨?_, ?_, ?_⟩
      · show view c1.nmem (g.base 14) (3 * g.N) d = _
        rw [hview _ _ _ (by omega), h1, ← hB.fp ⟨d, hd⟩]
      · show view c1.nmem (g.base 14) (3 * g.N) (g.N + d) = _
        rw [hview _ _ _ (by omega), ← Nat.add_assoc]; exact h2
      · show view c1.nmem (g.base 14) (3 * g.N) (2 * g.N + d) = _
        rw [hview _ _ _ (by omega), ← Nat.add_assoc, h3, ← hB.fpi ⟨d, hd⟩]
    · obtain ⟨h1, h2, h3⟩ := hB.sf ⟨d, hd⟩
      refine ⟨?_, ?_, ?_⟩
      · show view c1.nmem (g.base 17) (3 * g.N) d = _
        rw [hview _ _ _ (by omega)]; exact h1
      · show view c1.nmem (g.base 17) (3 * g.N) (g.N + d) = _
        rw [hview _ _ _ (by omega), ← Nat.add_assoc]; exact h2
      · show view c1.nmem (g.base 17) (3 * g.N) (2 * g.N + d) = _
        rw [hview _ _ _ (by omega), ← Nat.add_assoc, h3, ← hB.fpi ⟨d, hd⟩]
    · show view c1.nmem (g.base 20) g.N d = d
      rw [hview _ _ _ hd]; exact hB.sfirst ⟨d, hd⟩
  have hok : G.OK := hGenc.ok
  have hpre : G.Pre 0 0 (labV Y c1.nmem) := by
    refine ⟨hok, hN, ?_, hN, fun w hw' _ => ?_⟩
    · show view c1.nmem (g.base 1) g.N 0 ≠ 1
      rw [hview _ _ _ hN, hA.zero 0 hN]; omega
    · show view c1.nmem (g.base 24) g.N w = g.N
      rw [hview _ _ _ (show w < g.N from hw')]; exact hdl w hw'
  obtain ⟨c2, k2, e2, hk2, ⟨hw2, hfr2, hI⟩, hht⟩ := bfs_exec (P := P) hYg hR1 hpre hw1
  rw [hht] at hI
  have hdb : ∀ x, G.db (enc g.N x) = 1 ↔ (starTree T a ha).IsTreeDart x := by
    intro x
    show view c1.nmem (g.base 21) (3 * g.N) (enc g.N x) = 1 ↔ _
    rw [hview _ _ _ (enc_lt x)]; exact hB.sdb x
  have hvb : ∀ f, f < g.N → G.vb f ≠ 1 := by
    intro f hf
    show view c1.nmem (g.base 1) g.N f ≠ 1
    rw [hview _ _ _ hf, hA.zero f hf]; omega
  obtain ⟨ht, C, hr0, hpar, hROK, hRup⟩ := dual_cotree (T := T) (ha := ha) hM hN rfl rfl hGenc
    hdb hvb hI
  -- the store `FPAR[0] := 0`
  have r56 : c2.nreg 130056 = g.base 26 := by
    rw [hfr2.1 _ (by unfold Scr; omega), hf1.1 _ (by unfold StBRG; omega)]
    exact hG.rbase 26 (by omega)
  have r09 : c2.nreg 130009 = 0 := by
    rw [hfr2.1 _ (by unfold Scr; omega), hf1.1 _ (by unfold StBRG; omega)]; exact hG.zero
  have e3 := Exec.storeN (P := P) hw2 130056 130009
  set c3 := { c2 with nmem := upd c2.nmem (c2.nreg 130056) (c2.nreg 130009) } with hc3
  have hm3 : ∀ x, c3.nmem x = if x = g.base 26 then 0 else c2.nmem x := by
    intro x; simp only [c3, Machine.upd_apply, r56, r09]
  have hkeep2 : ∀ x, ¬ Y.Written x → c2.nmem x = c.nmem x := fun x hx => by
    rw [hfr2.2.2.2.2 x hx, hm1]
  have hq : ∀ i, i < g.N → c3.nmem (g.base 27 + i) = qV Y c2.nmem i := by
    intro i hi
    rw [hm3, ite_eq_right (by omega)]
    show _ = view c2.nmem (g.base 27) g.N i
    rw [view_lt hi]
  have hq0 : qV Y c2.nmem 0 = 0 := hI.q0
  have hpv : ∀ x, x < g.N → parV Y c2.nmem x = c2.nmem (g.base 26 + x) := fun x hx => by
    show view c2.nmem (g.base 26) g.N x = _; rw [view_lt hx]
  have hr0' : ∀ x : Fin g.N, x ≠ C.r0 ↔ (x : ℕ) ≠ 0 := by
    intro x
    constructor
    · intro h e; exact h (Fin.ext (by rw [hr0]; exact e))
    · intro h e; exact h (by rw [e, hr0])
  have hpar' : ∀ x, x < g.N → x ≠ 0 → c2.nmem (g.base 26 + x) < 3 * g.N ∧
      ∃ h : x < g.N, enc g.N (C.fpar ⟨x, h⟩) = c2.nmem (g.base 26 + x) := by
    intro x hx h0
    obtain ⟨h1, h2⟩ := hpar ⟨x, hx⟩ ((hr0' ⟨x, hx⟩).mpr h0)
    rw [hpv x hx] at h1 h2
    exact ⟨h1, hx, h2⟩
  set R0 : BTree := ⟨g.N, qV Y c2.nmem, fun x => G.vert (parV Y c2.nmem x)⟩ with hR0
  have hRq : ∀ i, i < R0.n → (dtree g c3.nmem).q i = R0.q i := fun i hi => hq i hi
  have hRp : ∀ x, x < R0.n → x ≠ R0.q 0 → (dtree g c3.nmem).par x = R0.par x := by
    intro x hx hx0
    have hx0' : x ≠ 0 := by rw [show R0.q 0 = 0 from hq0] at hx0; exact hx0
    obtain ⟨hlt, -⟩ := hpar' x hx hx0'
    show c3.nmem (g.base 17 + c3.nmem (g.base 26 + x)) = G.vert (parV Y c2.nmem x)
    rw [hm3 (g.base 26 + x), ite_eq_right (by omega), hm3, ite_eq_right (by omega), hpv x hx]
    show _ = view c1.nmem (g.base 17) (3 * g.N) _
    rw [hview _ _ _ hlt, hkeep2 _ (by unfold Lay.Written; simp only [hY, dualLay]; omega)]
  refine ⟨c3, k1 + (k2 + 1), .seq e1 (.seq e2 e3), ?_, e3.wb_right, ?_, C, hr0, fun x hx => ?_,
    fun x hx => ?_, hROK.congr rfl hRq hRp, ?_, fun x => ?_⟩
  · have hsum := hI.sum_deg_le hok (le_refl _)
    have htn := hI.tn
    have hGN3 : G.N = 3 * g.N := rfl
    have hGnv : G.nv = g.N := rfl
    rw [hGN3] at hsum
    rw [hGnv] at htn
    omega
  · refine hf1.trans ⟨fun r hr => hfr2.1 r (fun h => hr (by unfold Scr at h; unfold StBRG; omega)),
      hfr2.2.1, hfr2.2.2.1, hfr2.2.2.2.1, fun a ha' => ?_⟩
    rw [hm3, ite_eq_right (by omega)]
    exact hfr2.2.2.2.2 a (fun h => ha' (by
      unfold Lay.Written at h; simp only [hY, dualLay] at h; omega))
  · have h0 := (hr0' x).mp hx
    obtain ⟨-, hx', he⟩ := hpar' x x.2 h0
    rw [hm3, ite_eq_right (by omega)]
    exact he.symm
  · by_cases h0 : x = 0
    · subst h0; rw [hm3, ite_eq_left (by omega)]; omega
    · rw [hm3, ite_eq_right (by omega)]; exact (hpar' x hx h0).1
  · show c3.nmem (g.base 27 + 0) = 0
    rw [hq 0 hN]; exact hq0
  · have hq0' : (dtree g c3.nmem).q 0 = R0.q 0 := hq 0 hN
    rw [BTree.up_congr hq0' hRp x.2]
    exact hRup x

/-- The layout of the preorder intervals. -/
def eulerLay (g : GV) : ELay := ⟨g.base 27, g.base 26, g.base 17, g.base 28, g.base 29,
  g.base 30, g.N⟩

set_option maxHeartbeats 4000000 in
theorem eulerP_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    (hR : (dtree g c.nmem).OK) (hlt : ∀ x, x < g.N → c.nmem (g.base 26 + x) < 3 * g.N)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W eulerP c c' k ∧ k ≤ 45 * g.N + 27 ∧ WordsBounded W c' ∧
      PFr StBRG (fun a => g.base 28 ≤ a ∧ a < g.base 31) c c' ∧
      (∀ x, x < g.N → c'.nmem (g.base 28 + x) = ((dtree g c.nmem).sub x).card) ∧
      (dtree g c.nmem).PreInv (view c'.nmem (g.base 29) g.N) (view c'.nmem (g.base 30) g.N)
        g.N := by
  have hU := g.U_ge
  have hE := g.END_eq
  have b17 := g.base_eq 17; have b20 := g.base_eq 20; have b26 := g.base_eq 26
  have b27 := g.base_eq 27; have b28 := g.base_eq 28; have b29 := g.base_eq 29
  have b30 := g.base_eq 30; have b31 := g.base_eq 31
  set L := eulerLay g with hL
  unfold eulerP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, hR1, hf1⟩ : ∃ c1 k1, Exec P W (block [.copyN 130200 130057,
      .copyN 130201 130056, .copyN 130202 130047, .copyN 130203 130058, .copyN 130204 130059,
      .copyN 130205 130060, .copyN 130206 130014]) c c1 k1 ∧
      k1 = 7 ∧ WordsBounded W c1 ∧ c1.nmem = c.nmem ∧ L.Regs c1 ∧
      PFr StBRG (fun a => g.base 28 ≤ a ∧ a < g.base 31) c c1 := by
    exec_block
    refine ⟨rfl, ‹_›, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      ⟨fun r hr => ?fr, rfl, rfl, rfl, fun a _ => rfl⟩⟩
    case fr =>
      simp only
      unfold StBRG at hr
      repeat (rw [Machine.upd_other _ _ _ (by omega)])
    all_goals try (config_simp;
                   first
                   | exact hG.one
                   | exact hG.rN
                   | exact hG.rbase 17 (by omega)
                   | exact hG.rbase 26 (by omega)
                   | exact hG.rbase 27 (by omega)
                   | exact hG.rbase 28 (by omega)
                   | exact hG.rbase 29 (by omega)
                   | exact hG.rbase 30 (by omega))
  have hLG : L.Good c1.nmem W := by
    rw [hm1]
    refine ⟨?_, ?_, ?_, fun i hi => ?_, fun x hx _ => ?_, fun x hx _ => ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
    all_goals simp only [hL, eulerLay, Disj, ELay.WR] at *
    all_goals try omega
    have := hlt x hx
    constructor <;> omega
  obtain ⟨c', k, e, hk, hw', hf', hsz, hpre⟩ := eulerStmt_exec (P := P) hLG hR1
    (by rw [hm1]; exact hR) hw1
  rw [hm1] at hsz hpre
  refine ⟨c', k1 + k, .seq e1 e, by simp only [hL, eulerLay] at hk; omega, hw', hf1.trans
    (hf'.mono (fun r h => by unfold ERG at h; unfold StBRG; omega) (fun a h => by
      simp only [hL, eulerLay, ELay.WR] at h; omega)), hsz, hpre⟩

theorem pfP_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c) (hN : 0 < g.N)
    (hlt : ∀ x, x < g.N → c.nmem (g.base 26 + x) < 3 * g.N) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W pfP c c' k ∧ k ≤ 9 * g.N + 8 ∧ WordsBounded W c' ∧
      PFr StBRG (fun a => g.base 31 ≤ a ∧ a < g.base 31 + g.N) c c' ∧ c'.nmem (g.base 31) = 0 ∧
      ∀ x, 1 ≤ x → x < g.N →
        c'.nmem (g.base 31 + x) = c.nmem (g.base 17 + c.nmem (g.base 26 + x)) := by
  have hU := g.U_ge
  have hE := g.END_eq
  have b17 := g.base_eq 17; have b26 := g.base_eq 26; have b31 := g.base_eq 31
  unfold pfP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, r0, r1, r2, r3, hone1, hzero1, hf1⟩ : ∃ c1 k1, Exec P W
      (block [.copyN 130500 130047, .copyN 130501 130056, .copyN 130502 130061,
        .copyN 130503 130014]) c c1 k1 ∧ k1 = 4 ∧ WordsBounded W c1 ∧ c1.nmem = c.nmem ∧
      c1.nreg 130500 = g.base 17 ∧ c1.nreg 130501 = g.base 26 ∧ c1.nreg 130502 = g.base 31 ∧
      c1.nreg 130503 = g.N ∧ c1.nreg 130001 = 1 ∧ c1.nreg 130009 = 0 ∧
      PFr StBRG (fun a => g.base 31 ≤ a ∧ a < g.base 31 + g.N) c c1 := by
    exec_block
    refine ⟨rfl, ‹_›, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ⟨fun r hr => ?fr, rfl, rfl, rfl,
      fun a _ => rfl⟩⟩
    case fr =>
      simp only
      unfold StBRG at hr
      repeat (rw [Machine.upd_other _ _ _ (by omega)])
    all_goals try (config_simp;
                   first
                   | exact hG.one
                   | exact hG.zero
                   | exact hG.rN
                   | exact hG.rbase 17 (by omega)
                   | exact hG.rbase 26 (by omega)
                   | exact hG.rbase 31 (by omega))
  obtain ⟨c', k, e, hk, hw', hf', h0, hx⟩ := parStmt_exec (P := P) hw1 hone1 hzero1 r0 r1 r2 r3
    hN (by omega) (by omega) (by omega) (fun x h1 h2 => by
      rw [hm1]; have := hlt x h2; omega)
  refine ⟨c', k1 + k, .seq e1 e, by omega, hw',
    hf1.trans (hf'.mono (fun r h => by unfold ParRG at h; unfold StBRG; omega) (fun a h => h)),
    by simpa using h0, fun x h1 h2 => by rw [hx x h1 h2, hm1]⟩

theorem updP_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c) (hN : 0 < g.N)
    (hL : 0 < g.L) (hpf : ∀ x, x < g.N → c.nmem (g.base 31 + x) < g.N) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W updP c c' k ∧ k ≤ 12 * g.N * g.L + 7 * g.L + 16 ∧ WordsBounded W c' ∧
      PFr StBRG (fun a => g.A0 + 54 * g.U + g.L * g.U ≤ a ∧
        a < g.A0 + 54 * g.U + g.L * g.U + g.L * g.N) c c' ∧
      ∀ j, j < g.L → ∀ x, x < g.N → c'.nmem (g.A0 + 54 * g.U + g.L * g.U + j * g.N + x) =
        (fun y => c.nmem (g.base 31 + y))^[2 ^ j] x := by
  have hU := g.U_ge
  have hE := g.END_eq
  have b31 := g.base_eq 31
  have hLU := g.L_le_U
  have hLN : g.L * g.N ≤ g.L * g.U := Nat.mul_le_mul_left _ (by omega)
  unfold updP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, r0, r1, r2, r3, hone1, hf1⟩ : ∃ c1 k1, Exec P W
      (block [.copyN 130510 130061, .copyN 130511 130085, .copyN 130512 130014,
        .copyN 130513 130017]) c c1 k1 ∧ k1 = 4 ∧ WordsBounded W c1 ∧ c1.nmem = c.nmem ∧
      c1.nreg 130510 = g.base 31 ∧ c1.nreg 130511 = g.A0 + 54 * g.U + g.L * g.U ∧
      c1.nreg 130512 = g.N ∧ c1.nreg 130513 = g.L ∧ c1.nreg 130001 = 1 ∧
      PFr StBRG (fun a => g.A0 + 54 * g.U + g.L * g.U ≤ a ∧
        a < g.A0 + 54 * g.U + g.L * g.U + g.L * g.N) c c1 := by
    exec_block
    refine ⟨rfl, ‹_›, rfl, ?_, ?_, ?_, ?_, ?_, ⟨fun r hr => ?fr, rfl, rfl, rfl,
      fun a _ => rfl⟩⟩
    case fr =>
      simp only
      unfold StBRG at hr
      repeat (rw [Machine.upd_other _ _ _ (by omega)])
    all_goals try (config_simp;
                   first
                   | exact hG.one
                   | exact hG.rL
                   | exact hG.rN
                   | exact hG.rUP
                   | exact hG.rbase 31 (by omega))
  obtain ⟨c', k, e, hk, hw', hf', htab⟩ := upStmt_exec (P := P) hw1 hone1 r0 r1 r2 r3 hL
    (fun x hx => by rw [hm1]; exact hpf x hx) (by omega) (by omega) (by omega) (by omega) hN
  refine ⟨c', k1 + k, .seq e1 e, by omega, hw',
    hf1.trans (hf'.mono (fun r h => by unfold UpRG at h; unfold StBRG; omega) (fun a h => h)),
    fun j hj x hx => by rw [htab j hj x hx, hm1]⟩


end proofs



end

end Chazelle.Core.Cluster
