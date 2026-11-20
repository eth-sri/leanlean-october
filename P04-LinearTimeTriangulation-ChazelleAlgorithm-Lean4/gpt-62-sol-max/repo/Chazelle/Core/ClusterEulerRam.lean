module

public import Chazelle.Core.ClusterEuler
public import Chazelle.Core.ClusterPhase

/-!
# WP-I, part 10: preorder intervals on the RAM

`eulerStmt`: for a tree in breadth-first order stored as a queue `Q` and parent darts `PAR`
with tails `VERT` (the parent of `g` is `VERT[PAR[g]]`), compute the subtree sizes `SZ`
(backwards over the queue) and the preorder `PRE` with the next-free-slot array `SLOT`
(forwards).  `eulerStmt_exec`: at most `45 n + 20` steps; afterwards `h` is a descendant of `g`
iff `PRE g ≤ PRE h < PRE g + SZ g`.

Registers: `130200 … 130206` (bases of `Q`, `PAR`, `VERT`, `SZ`, `PRE`, `SLOT`; `n`), scratch
`130210 … 130215` and the fill registers `130150 … 130154`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-! ## The program -/

/-- Set up the fill of `SZ` with `1`. -/
def eulerFillSet : Stmt := block [.copyN 130150 130203, .copyN 130151 130206, .constN 130152 1]

/-- `i := i - 1`, `g := Q[i]`, `p := VERT[PAR[g]]`, `SZ[p] := SZ[p] + SZ[g]`. -/
def sizeBody : Stmt := block [.subN 130210 130210 130001, .addN 130213 130200 130210,
  .loadN 130211 130213, .addN 130213 130201 130211, .loadN 130214 130213,
  .addN 130213 130202 130214, .loadN 130212 130213, .addN 130213 130203 130211,
  .loadN 130214 130213, .addN 130213 130203 130212, .loadN 130215 130213,
  .addN 130215 130215 130214, .storeN 130213 130215]

/-- The size loop, `i = n - 1, …, 1`. -/
def sizeLoop : Stmt := .seq (.instr (.copyN 130210 130206)) (.whileLtN 130001 130210 sizeBody)

/-- The root: `PRE[root] := 0`, `SLOT[root] := 1`, `i := 1`. -/
def preInit : Stmt := block [.constN 130210 0, .addN 130213 130200 130210, .loadN 130211 130213,
  .addN 130213 130204 130211, .constN 130214 0, .storeN 130213 130214,
  .addN 130213 130205 130211, .storeN 130213 130001, .constN 130210 1]

/-- The entry `i`: `PRE[g] := SLOT[p]`, `SLOT[p] += SZ[g]`, `SLOT[g] := PRE[g] + 1`. -/
def preBody : Stmt := block [.addN 130213 130200 130210, .loadN 130211 130213,
  .addN 130213 130201 130211, .loadN 130214 130213, .addN 130213 130202 130214,
  .loadN 130212 130213, .addN 130213 130205 130212, .loadN 130214 130213,
  .addN 130213 130204 130211, .storeN 130213 130214, .addN 130213 130203 130211,
  .loadN 130215 130213, .addN 130215 130214 130215, .addN 130213 130205 130212,
  .storeN 130213 130215, .addN 130213 130205 130211, .addN 130215 130214 130001,
  .storeN 130213 130215, .addN 130210 130210 130001]

/-- **Preorder intervals.** -/
def eulerStmt : Stmt := .seq eulerFillSet (.seq fillStmt (.seq sizeLoop
  (.seq preInit (.whileLtN 130210 130206 preBody))))

/-! ## Layout -/

/-- The layout of the Euler computation, read from the registers of `c`. -/
structure ELay where
  /-- queue -/
  bQ : ℕ
  /-- parent darts -/
  bPar : ℕ
  /-- tails -/
  bVert : ℕ
  /-- sizes -/
  bSz : ℕ
  /-- preorders -/
  bPre : ℕ
  /-- next slots -/
  bSlot : ℕ
  /-- nodes -/
  n : ℕ

/-- The registers written by the Euler computation. -/
def ERG (r : ℕ) : Prop := (130150 ≤ r ∧ r ≤ 130154) ∨ (130210 ≤ r ∧ r ≤ 130215)

namespace ELay

variable (L : ELay)

/-- The tree read from memory. -/
def tree (m : ℕ → ℕ) : BTree := ⟨L.n, fun i => m (L.bQ + i), fun g => m (L.bVert + m (L.bPar + g))⟩

/-- The written addresses. -/
def WR (a : ℕ) : Prop :=
  (L.bSz ≤ a ∧ a < L.bSz + L.n) ∨ (L.bPre ≤ a ∧ a < L.bPre + L.n) ∨
    (L.bSlot ≤ a ∧ a < L.bSlot + L.n)

/-- The registers hold the layout. -/
structure Regs (c : Config) : Prop where
  one : c.nreg 130001 = 1
  rQ : c.nreg 130200 = L.bQ
  rPar : c.nreg 130201 = L.bPar
  rVert : c.nreg 130202 = L.bVert
  rSz : c.nreg 130203 = L.bSz
  rPre : c.nreg 130204 = L.bPre
  rSlot : c.nreg 130205 = L.bSlot
  rn : c.nreg 130206 = L.n

/-- A good layout for the memory `m`: disjoint written arrays not overlapping what is read, and
room below `W`. -/
structure Good (m : ℕ → ℕ) (W : ℕ) : Prop where
  dSz : Disj L.bSz L.n L.bPre L.n
  dSl : Disj L.bSz L.n L.bSlot L.n
  dPS : Disj L.bPre L.n L.bSlot L.n
  rq : ∀ i, i < L.n → ¬ L.WR (L.bQ + i)
  rpar : ∀ g, g < L.n → g ≠ m L.bQ → ¬ L.WR (L.bPar + g)
  rvert : ∀ g, g < L.n → g ≠ m L.bQ → ¬ L.WR (L.bVert + m (L.bPar + g)) ∧
    L.bVert + m (L.bPar + g) ≤ W
  wQ : L.bQ + L.n ≤ W
  wPar : L.bPar + L.n ≤ W
  wSz : L.bSz + L.n ≤ W
  wPre : L.bPre + L.n ≤ W
  wSlot : L.bSlot + L.n ≤ W
  wn : L.n + 1 ≤ W

end ELay

theorem Regs_of_pfr {L : ELay} {c0 c : Config} (h : L.Regs c0) (hf : PFr ERG L.WR c0 c) :
    L.Regs c := by
  have k : ∀ r, ¬ ERG r → c.nreg r = c0.nreg r := hf.1
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rwa [k _ (by unfold ERG; omega)])

/-! ## Proofs -/

section proofs

variable {P : Polygon} {W : ℕ} {L : ELay} {c0 : Config}

theorem ELay.tree_root (m : ℕ → ℕ) : (L.tree m).root = m L.bQ := by
  simp [BTree.root, ELay.tree]

/-- The view of an array after a store at one of its cells. -/
theorem fun_upd (m : ℕ → ℕ) (b x v : ℕ) :
    (fun g => upd m (b + x) v (b + g)) = Function.update (fun g => m (b + g)) x v := by
  funext g
  rw [Machine.upd_apply]
  by_cases h : g = x
  · subst h; simp
  · rw [ite_eq_right (by omega), Function.update_of_ne h]

/-- **One step of the size loop.** -/
theorem sizeBody_exec (hL : L.Good c0.nmem W) (hR0 : L.Regs c0) (hR : (L.tree c0.nmem).OK)
    {c : Config} (hw : WordsBounded W c) (hf : PFr ERG L.WR c0 c) {i : ℕ}
    (hi : c.nreg 130210 = i + 1) (hi0 : 0 < i) (hin : i < L.n)
    (hS : (L.tree c0.nmem).SizeInv (fun g => c.nmem (L.bSz + g)) (i + 1)) :
    ∃ c' k, Exec P W sizeBody c c' k ∧ k = 13 ∧ WordsBounded W c' ∧ PFr ERG L.WR c0 c' ∧
      c'.nreg 130210 = i ∧
      (L.tree c0.nmem).SizeInv (fun g => c'.nmem (L.bSz + g)) i := by
  have hRc := Regs_of_pfr hR0 hf
  set R := L.tree c0.nmem with hRdef
  have hqn : R.q i < L.n := hR.q_lt i hin
  have hqr : R.q i ≠ R.root := by
    intro h; have := hR.q_inj i hin 0 hR.n_pos h; omega
  have hqr' : c0.nmem (L.bQ + i) ≠ c0.nmem L.bQ := by
    rw [← L.tree_root c0.nmem]; exact hqr
  have hpn : R.par (R.q i) < L.n := (hR.par_spec hqn hqr).1
  -- reads
  have r1 : c.nmem (L.bQ + i) = R.q i := hf.2.2.2.2 _ (hL.rq i hin)
  have r2 : c.nmem (L.bPar + R.q i) = c0.nmem (L.bPar + R.q i) :=
    hf.2.2.2.2 _ (hL.rpar _ hqn hqr')
  have r3 : c.nmem (L.bVert + c0.nmem (L.bPar + R.q i)) = R.par (R.q i) :=
    hf.2.2.2.2 _ (hL.rvert _ hqn hqr').1
  have hvw := (hL.rvert _ hqn hqr').2
  have hszp := hS.le hR hpn
  have := hL.wQ; have := hL.wPar; have := hL.wSz; have := hL.wn
  -- the new size of the parent is at most the true size
  have hstep := hS.step hR hi0 hin
  have hnew := hstep.le hR hpn
  rw [Function.update_self] at hnew
  have hcs : (R.sub (R.par (R.q i))).card ≤ L.n := R.card_sub_le (R.par (R.q i))
  unfold sizeBody
  exec_block
  all_goals try (config_simp; simp only [hRc.rQ, hRc.rPar, hRc.rVert, hRc.rSz, hi, hRc.one,
    Nat.add_sub_cancel, r1, r2, r3]; omega)
  refine ⟨rfl, ‹_›, ?_, by config_simp; rw [hi, hRc.one]; omega, ?_⟩
  · refine PFr.nreg_nmem hf (fun r hr => ?_) ?_
    · simp only [Machine.upd_apply]; unfold ERG at hr; split_ifs <;> omega
    · simp only [hRc.rQ, hRc.rPar, hRc.rVert, hRc.rSz, hi, hRc.one, Nat.add_sub_cancel, r1, r2, r3]
      unfold ELay.WR; omega
  · config_simp
    simp only [hRc.rQ, hRc.rPar, hRc.rVert, hRc.rSz, hi, hRc.one, Nat.add_sub_cancel, r1, r2, r3]
    rw [fun_upd]
    exact hstep

/-- **The size loop**: afterwards `SZ` holds the subtree sizes. -/
theorem sizeLoop_exec (hL : L.Good c0.nmem W) (hR0 : L.Regs c0) (hR : (L.tree c0.nmem).OK)
    {c : Config} (hw : WordsBounded W c) (hf : PFr ERG L.WR c0 c)
    (h1 : ∀ g, g < L.n → c.nmem (L.bSz + g) = 1) :
    ∃ c' k, Exec P W sizeLoop c c' k ∧ k ≤ 15 * L.n + 3 ∧ WordsBounded W c' ∧
      PFr ERG L.WR c0 c' ∧
      ∀ g, g < L.n → c'.nmem (L.bSz + g) = ((L.tree c0.nmem).sub g).card := by
  have hRc := Regs_of_pfr hR0 hf
  have e0 := Exec.copyN (P := P) hw 130210 130206
  set c1 := { c with nreg := upd c.nreg 130210 (c.nreg 130206) }
  have hf1 : PFr ERG L.WR c0 c1 := PFr.nreg hf (fun r hr => by
    simp only [Machine.upd_apply]; unfold ERG at hr; split_ifs <;> omega)
  obtain ⟨c', k, e, ⟨hw', hf', i, hi, hi1, hin, hS⟩, htest, hk⟩ := Exec.whileLtN_potential
    (P := P) (W := W) (a := 130001) (b := 130210) (body := sizeBody)
    (fun c' => WordsBounded W c' ∧ PFr ERG L.WR c0 c' ∧ ∃ i, c'.nreg 130210 = i ∧ 1 ≤ i ∧
      i ≤ L.n ∧ (L.tree c0.nmem).SizeInv (fun g => c'.nmem (L.bSz + g)) i)
    (fun c' => 15 * c'.nreg 130210) (fun c' h => h.1)
    (fun c2 ⟨hw2, hf2, i, hi, hi1, hin, hS⟩ htest => by
      have hone := (Regs_of_pfr hR0 hf2).one
      rw [hone, hi] at htest
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      obtain ⟨c3, k3, e3, hk3, hw3, hf3, hi3, hS3⟩ :=
        sizeBody_exec (P := P) hL hR0 hR hw2 hf2 hi (by omega) (by omega) hS
      exact ⟨c3, k3, e3, ⟨hw3, hf3, i', hi3, by omega, by omega, hS3⟩, by rw [hi3, hi]; omega⟩)
    ⟨e0.wb_right, hf1, L.n, by simp [c1, hRc.rn], hR.n_pos, le_rfl,
      BTree.SizeInv.init (fun g hg => h1 g hg) hR⟩
  have hone := (Regs_of_pfr hR0 hf').one
  rw [hone, hi] at htest
  have hi1' : i = 1 := by omega
  subst hi1'
  refine ⟨c', 1 + k, .seq e0 e, ?_, hw', hf', fun g hg => hS.final hR hg⟩
  have : c1.nreg 130210 = L.n := by simp [c1, hRc.rn]
  rw [this] at hk
  omega

/-- **One entry of the preorder loop.** -/
theorem preBody_exec (hL : L.Good c0.nmem W) (hR0 : L.Regs c0) (hR : (L.tree c0.nmem).OK)
    {c : Config} (hw : WordsBounded W c) (hf : PFr ERG L.WR c0 c) {i : ℕ}
    (hi : c.nreg 130210 = i) (hin : i < L.n)
    (hsz : ∀ g, g < L.n → c.nmem (L.bSz + g) = ((L.tree c0.nmem).sub g).card)
    (hP : (L.tree c0.nmem).PreInv (view c.nmem L.bPre L.n) (view c.nmem L.bSlot L.n) i) :
    ∃ c' k, Exec P W preBody c c' k ∧ k = 19 ∧ WordsBounded W c' ∧ PFr ERG L.WR c0 c' ∧
      c'.nreg 130210 = i + 1 ∧ (∀ g, g < L.n → c'.nmem (L.bSz + g) = ((L.tree c0.nmem).sub g).card) ∧
      (L.tree c0.nmem).PreInv (view c'.nmem L.bPre L.n) (view c'.nmem L.bSlot L.n) (i + 1) := by
  have hRc := Regs_of_pfr hR0 hf
  set R := L.tree c0.nmem with hRdef
  have hi0 := hP.i_pos
  have hqn : R.q i < L.n := hR.q_lt i hin
  have hqr : R.q i ≠ R.root := by
    intro h; have := hR.q_inj i hin 0 hR.n_pos h; omega
  have hqr' : c0.nmem (L.bQ + i) ≠ c0.nmem L.bQ := by
    rw [← L.tree_root c0.nmem]; exact hqr
  have hpn : R.par (R.q i) < L.n := (hR.par_spec hqn hqr).1
  have hpq : R.par (R.q i) ≠ R.q i := by
    intro h; have := (hR.par_spec hqn hqr).2; rw [h] at this; omega
  -- reads
  have r1 : c.nmem (L.bQ + i) = R.q i := hf.2.2.2.2 _ (hL.rq i hin)
  have r2 : c.nmem (L.bPar + R.q i) = c0.nmem (L.bPar + R.q i) :=
    hf.2.2.2.2 _ (hL.rpar _ hqn hqr')
  have r3 : c.nmem (L.bVert + c0.nmem (L.bPar + R.q i)) = R.par (R.q i) :=
    hf.2.2.2.2 _ (hL.rvert _ hqn hqr').1
  have r4 : c.nmem (L.bSlot + R.par (R.q i)) = view c.nmem L.bSlot L.n (R.par (R.q i)) := by
    rw [view_lt hpn]
  have r5 : c.nmem (L.bSz + R.q i) = (R.sub (R.q i)).card := hsz _ hqn
  have hvw := (hL.rvert _ hqn hqr').2
  have := hL.wQ; have := hL.wPar; have := hL.wSz; have := hL.wn; have := hL.wPre; have := hL.wSlot
  have hstep := hP.step hR hin
  have hbd := hstep.bound i (by omega)
  rw [Function.update_self] at hbd
  have hbd' : view c.nmem L.bSlot L.n (R.par (R.q i)) + (R.sub (R.q i)).card ≤ L.n := hbd
  have hσ := BTree.one_le_card_sub (R := R) hqn
  have d1 := hL.dSz; have d2 := hL.dSl; have d3 := hL.dPS
  unfold Disj at d1 d2 d3
  have r5' : ∀ X, upd c.nmem (L.bPre + R.q i) X (L.bSz + R.q i) = (R.sub (R.q i)).card := by
    intro X; rw [Machine.upd_other _ _ _ (by omega), r5]
  unfold preBody
  exec_block
  all_goals try (config_simp; simp only [hRc.rQ, hRc.rPar, hRc.rVert, hRc.rSz, hRc.rPre,
    hRc.rSlot, hi, hRc.one, r1, r2, r3, r4, r5']; omega)
  refine ⟨rfl, ‹_›, ?_, by config_simp; rw [hi, hRc.one], ?_, ?_⟩
  · refine PFr.of_eq hf (fun r hr => ?_) (fun a ha => ?_)
    · simp only [Machine.upd_apply]; unfold ERG at hr; split_ifs <;> omega
    · simp only [hRc.rQ, hRc.rPar, hRc.rVert, hRc.rSz, hRc.rPre, hRc.rSlot, hi, hRc.one, r1, r2,
        r3, r4, r5', Machine.upd_apply]
      unfold ELay.WR at ha
      split_ifs <;> omega
  · intro g hg
    config_simp
    simp only [hRc.rQ, hRc.rPar, hRc.rVert, hRc.rSz, hRc.rPre, hRc.rSlot, hi, hRc.one, r1, r2,
      r3, r4, r5', Machine.upd_apply]
    split_ifs <;> first | omega | exact hsz g hg
  · config_simp
    simp only [hRc.rQ, hRc.rPar, hRc.rVert, hRc.rSz, hRc.rPre, hRc.rSlot, hi, hRc.one, r1, r2,
      r3, r4, r5']
    have hv1 : ∀ X Y Z, view (upd (upd (upd c.nmem (L.bPre + R.q i) X) (L.bSlot + R.par (R.q i)) Y)
        (L.bSlot + R.q i) Z) L.bPre L.n = Function.update (view c.nmem L.bPre L.n) (R.q i) X := by
      intro X Y Z
      rw [view_upd_out _ L.bPre L.n (L.bSlot + R.q i) Z (by omega),
        view_upd_out _ L.bPre L.n (L.bSlot + R.par (R.q i)) Y (by omega),
        view_upd_in _ _ _ _ _ hqn]
    have hv2 : ∀ X Y Z, view (upd (upd (upd c.nmem (L.bPre + R.q i) X) (L.bSlot + R.par (R.q i)) Y)
        (L.bSlot + R.q i) Z) L.bSlot L.n = Function.update (Function.update
          (view c.nmem L.bSlot L.n) (R.par (R.q i)) Y) (R.q i) Z := by
      intro X Y Z
      rw [view_upd_in _ _ _ _ _ hqn, view_upd_in _ _ _ _ _ hpn,
        view_upd_out _ L.bSlot L.n (L.bPre + R.q i) X (by omega)]
    rw [hv1, hv2]
    exact hstep

/-- The root of the preorder. -/
theorem preInit_exec (hL : L.Good c0.nmem W) (hR0 : L.Regs c0) (hR : (L.tree c0.nmem).OK)
    {c : Config} (hw : WordsBounded W c) (hf : PFr ERG L.WR c0 c)
    (hsz : ∀ g, g < L.n → c.nmem (L.bSz + g) = ((L.tree c0.nmem).sub g).card) :
    ∃ c' k, Exec P W preInit c c' k ∧ k = 9 ∧ WordsBounded W c' ∧ PFr ERG L.WR c0 c' ∧
      c'.nreg 130210 = 1 ∧ (∀ g, g < L.n → c'.nmem (L.bSz + g) = ((L.tree c0.nmem).sub g).card) ∧
      (L.tree c0.nmem).PreInv (view c'.nmem L.bPre L.n) (view c'.nmem L.bSlot L.n) 1 := by
  have hRc := Regs_of_pfr hR0 hf
  set R := L.tree c0.nmem with hRdef
  have hrn : R.root < L.n := hR.root_lt
  have r1 : c.nmem (L.bQ + 0) = R.root := hf.2.2.2.2 _ (hL.rq 0 hR.n_pos)
  have := hL.wQ; have := hL.wPre; have := hL.wSlot; have := hL.wSz; have := hL.wn
  have d1 := hL.dSz; have d2 := hL.dSl; have d3 := hL.dPS
  unfold Disj at d1 d2 d3
  unfold preInit
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp only [hRc.rQ, hRc.rPre, hRc.rSlot, r1]; omega)
  refine ⟨rfl, ‹_›, ?_, by config_simp, ?_, ?_⟩
  · refine PFr.of_eq hf (fun r hr => ?_) (fun a ha => ?_)
    · simp only [Machine.upd_apply]; unfold ERG at hr; split_ifs <;> omega
    · simp only [hRc.rQ, hRc.rPre, hRc.rSlot, r1, Machine.upd_apply]
      unfold ELay.WR at ha
      split_ifs <;> omega
  · intro g hg
    config_simp
    simp only [hRc.rQ, hRc.rPre, hRc.rSlot, r1, Machine.upd_apply]
    split_ifs <;> first | omega | exact hsz g hg
  · config_simp
    simp only [hRc.rQ, hRc.rPre, hRc.rSlot, r1, hRc.one]
    refine BTree.PreInv.init hR ?_ ?_
    · rw [view_lt hrn, Machine.upd_other _ _ _ (by omega), Machine.upd_same]
    · rw [view_lt hrn, Machine.upd_same]

/-- **Preorder intervals on the RAM.**  With a good layout and a well-formed tree read from
memory, `eulerStmt` runs in at most `45 n + 20` steps, writes only the arrays `SZ`, `PRE`, `SLOT`
and its registers, and ends with the true subtree sizes in `SZ` and the final preorder invariant
(hence `BTree.PreInv.anc_iff`: descendants are exactly the preorder intervals). -/
theorem eulerStmt_exec (hL : L.Good c0.nmem W) (hR0 : L.Regs c0) (hR : (L.tree c0.nmem).OK)
    (hw : WordsBounded W c0) :
    ∃ c' k, Exec P W eulerStmt c0 c' k ∧ k ≤ 45 * L.n + 20 ∧ WordsBounded W c' ∧
      PFr ERG L.WR c0 c' ∧
      (∀ g, g < L.n → c'.nmem (L.bSz + g) = ((L.tree c0.nmem).sub g).card) ∧
      (L.tree c0.nmem).PreInv (view c'.nmem L.bPre L.n) (view c'.nmem L.bSlot L.n) L.n := by
  have := hL.wSz; have := hL.wn
  -- fill `SZ` with `1`
  obtain ⟨c1, e1, hw1, h150, h151, h152, hr1⟩ : ∃ c1, Exec P W eulerFillSet c0 c1 3 ∧
      WordsBounded W c1 ∧ c1.nreg 130150 = L.bSz ∧ c1.nreg 130151 = L.n ∧
      c1.nreg 130152 = 1 ∧ PFr ERG L.WR c0 c1 := by
    unfold eulerFillSet
    have a1 := Exec.copyN (P := P) hw 130150 130203
    have a2 := Exec.copyN (P := P) a1.wb_right 130151 130206
    have a3 := Exec.constN (P := P) a2.wb_right 130152 1 (by omega)
    refine ⟨_, Exec.block_cons a1 (Exec.block_cons a2 (Exec.block_cons a3
      (Exec.block_nil a3.wb_right))), a3.wb_right, ?_, ?_, ?_, ?_⟩
    · simp [hR0.rSz]
    · simp [hR0.rn]
    · simp
    · refine PFr.nreg (PFr.refl c0) (fun r hr => ?_)
      simp only [Machine.upd_apply]; unfold ERG at hr; split_ifs <;> omega
  have hone1 : c1.nreg 130001 = 1 := (Regs_of_pfr hR0 hr1).one
  obtain ⟨c2, k2, e2, hk2, hf2, hfill⟩ := fillStmt_exec (P := P) hw1 hone1
    (by rw [h150, h151]; exact hL.wSz) (by rw [h151]; omega)
  have hr2 : PFr ERG L.WR c0 c2 := hr1.trans (hf2.mono (fun r hr => by
    unfold FillScr at hr; unfold ERG; omega) (fun a ha => by
      rw [h150, h151] at ha; unfold ELay.WR; omega))
  rw [h150, h151, h152] at hfill
  rw [h151] at hk2
  obtain ⟨c3, k3, e3, hk3, hw3, hr3, hsz3⟩ := sizeLoop_exec (P := P) hL hR0 hR e2.wb_right hr2
    hfill
  obtain ⟨c4, k4, e4, hk4, hw4, hr4, hi4, hsz4, hP4⟩ := preInit_exec (P := P) hL hR0 hR hw3 hr3
    hsz3
  obtain ⟨c5, k5, e5, hk5, hw5, hr5, hi5, -, hsz5, hP5⟩ := forN (P := P) (W := W) (ri := 130210)
    (rn := 130206) (body := preBody)
    (fun j c => WordsBounded W c ∧ PFr ERG L.WR c0 c ∧ c.nreg 130210 = j ∧
      c.nreg 130206 = L.n ∧
      (∀ g, g < L.n → c.nmem (L.bSz + g) = ((L.tree c0.nmem).sub g).card) ∧
      (L.tree c0.nmem).PreInv (view c.nmem L.bPre L.n) (view c.nmem L.bSlot L.n) j)
    L.n 19 (fun j c h => ⟨h.1, h.2.2.1, h.2.2.2.1⟩)
    (fun j c hj ⟨hw, hf, hi, hn, hsz, hP⟩ => by
      obtain ⟨c', k, e, hk, hw', hf', hi', hsz', hP'⟩ := preBody_exec (P := P) hL hR0 hR hw hf hi
        hj hsz hP
      exact ⟨c', k, e, by omega, hw', hf', hi', (Regs_of_pfr hR0 hf').rn, hsz', hP'⟩)
    (j₀ := 1) ⟨hw4, hr4, hi4, (Regs_of_pfr hR0 hr4).rn, hsz4, hP4⟩ hR.n_pos
  refine ⟨c5, 3 + (k2 + (k3 + (k4 + k5))), .seq e1 (.seq e2 (.seq e3 (.seq e4 e5))), ?_, hw5,
    hr5, hsz5, hP5⟩
  omega

end proofs

end

end Chazelle.Core.Cluster
