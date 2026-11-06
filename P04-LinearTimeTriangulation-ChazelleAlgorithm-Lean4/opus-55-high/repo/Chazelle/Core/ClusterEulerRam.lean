module

public import Chazelle.MacT
public import Chazelle.Programs.Tactics
public import Chazelle.Core.Lemma41Cover
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.List.GetD

namespace Chazelle.Core.Cluster
open Machine Machine.Stmt Programs
@[expose] public section
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
def ERG (r : ℕ) : Prop := ztbxr ∨ (130210 ≤ r ∧ r ≤ 130215)
namespace ELay
variable (L : ELay)

/-- The tree read from memory. -/
def tree (m : ℕ → ℕ) : BTree := ⟨L.n, fun i => m ztjjm, fun g => m ztzkc⟩

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
  rq : ∀ i, i < L.n → ¬ L.WR ztjjm
  rpar : ∀ g, g < L.n → g ≠ m L.bQ → ¬ L.WR ztjjl
  rvert : ∀ g, g < L.n → g ≠ m L.bQ → ¬ L.WR ztzkc ∧
    L.bVert + m ztjjl ≤ W
  wQ : L.bQ + L.n ≤ W
  wPar : L.bPar + L.n ≤ W
  wSz : L.bSz + L.n ≤ W
  wPre : L.bPre + L.n ≤ W
  wSlot : L.bSlot + L.n ≤ W
  wn : L.n + 1 ≤ W
end ELay
theorem Regs_of_pfr {L : ELay} {c0 c : Config} (h : L.Regs c0) (hf : PFr ERG L.WR c0 c) :
    L.Regs c := by
  zujab
  zucsp
  refine ztdiu <;> (rwa [k _ (by unfold ERG; omega)])

/-! ## Proofs -/
section proofs
variable {P : Polygon} {W : ℕ} {L : ELay} {c0 : Config}
variable (m : ℕ → ℕ)
theorem ELay.tree_root : (L.tree m).root = m L.bQ := by
  rfl

/-- The view of an array after a store at one of its cells. -/
theorem fun_upd (b x v : ℕ) :
    (fun g => upd m (b + x) v zttfh) = Function.update (fun g => m zttfh) x v := by
  funext g
  zujgy
  grind

/-- **One step of the size loop.** -/
theorem sizeBody_exec (hL : L.Good c0.nmem W) (hR0 : L.Regs c0) (hR : (L.tree c0.nmem).OK)
    {c : Config} (hw : WordsBounded W c) (hf : PFr ERG L.WR c0 c) {i : ℕ}
    (hi : c.nreg 130210 = i + 1) (hi0 : 0 < i) (hin : i < L.n)
    (hS : (L.tree c0.nmem).SizeInv (fun g => c.nmem ztdth) ztg) :
    ∃ c' k, Exec P W sizeBody c c' k ∧ k = 13 ∧ WordsBounded W c' ∧ PFr ERG L.WR c0 c' ∧
      c'.nreg 130210 = i ∧
      (L.tree c0.nmem).SizeInv ztzew i := by
  zubwi

  zuiaf
  have hqr : ztplc := by
    zuesz
  have hqr' : ztzpi := by
    tauto
  zufwc
  -- reads
  zuibk
  have r2 : ztsej :=
    hf.2.2.2.2 _ ztrrp
  have r3 : ztseh :=
    hf.2.2.2.2 _ (hL.rvert _ hqn hqr').1
  zugng
  have hszp := hS.le hR hpn
  have := hL.wQ; have := hL.wPar; have := hL.wSz; have := hL.wn
  -- the new size of the parent is at most the true size
  have hstep := hS.step hR hi0 hin
  have hnew := hstep.le hR hpn
  rw [Function.update_self] at hnew
  have hcs : (R.sub _).card ≤ L.n := R.card_sub_le ztwxc
  unfold sizeBody
  exec_block
  all_goals try (config_simp; simp only [hRc.rQ, hRc.rPar, hRc.rVert, hRc.rSz, hi, hRc.one,
    Nat.add_sub_cancel, r1, r2, r3]; omega)
  refine ⟨rfl, by_omega, ?_, by config_simp; zuohx; omega, ?_⟩
  · refine PFr.nreg_nmem hf ztez ?_
    · zubde
    · zucfa
      unfold ELay.WR; omega
  · config_simp
    zucfa
    rw [fun_upd]
    omega

/-- **The size loop**: afterwards `SZ` holds the subtree sizes. -/
theorem sizeLoop_exec (hL : L.Good c0.nmem W) (hR0 : L.Regs c0) (hR : (L.tree c0.nmem).OK)
    {c : Config} (hw : WordsBounded W c) (hf : PFr ERG L.WR c0 c)
    (h1 : ∀ g, g < L.n → c.nmem ztdth = 1) :
    ∃ c' k, Exec P W sizeLoop c c' k ∧ k ≤ 15 * L.n + 3 ∧ WordsBounded W c' ∧
      PFr ERG L.WR c0 c' ∧
      ∀ g, g < L.n → c'.nmem ztdth = ((L.tree c0.nmem).sub g).card := by
  have hRc := Regs_of_pfr hR0 hf
  have e0 := Exec.copyN (P := P) hw 130210 130206
  set c1 := { c with nreg := upd c.nreg 130210 (c.nreg 130206) }
  have hf1 : PFr ERG L.WR c0 c1 := PFr.nreg hf (fun r hr => by
    zumwj; unfold ERG at hr; grind)
  obtain ⟨c', k, e, ⟨hw', hf', i, hi, hi1, hin, hS⟩, htest, hk⟩ := Exec.whileLtN_potential
    (P := P) (W := W) (a := 130001) (b := 130210) (body := sizeBody)
    (fun c' => WordsBounded W c' ∧ PFr ERG L.WR c0 c' ∧ ∃ i, c'.nreg 130210 = i ∧ 1 ≤ i ∧
      i ≤ L.n ∧ (L.tree c0.nmem).SizeInv ztzew i)
    (fun c' => 15 * c'.nreg 130210) ztbms
    (fun c2 ⟨hw2, hf2, i, hi, hi1, hin, hS⟩ htest => by
      have hone := (Regs_of_pfr hR0 hf2).one
      zuikg
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ztrdi
      obtain ⟨c3, k3, e3, hk3, hw3, hf3, hi3, hS3⟩ :=
        sizeBody_exec (P := P) hL hR0 hR hw2 hf2 hi by_omega by_omega hS
      grind)
    ⟨e0.wb_right, hf1, L.n, by zuohy, hR.n_pos, le_rfl,
      BTree.SizeInv.init (fun g hg => h1 g hg) hR⟩
  have hone := (Regs_of_pfr hR0 hf').one
  zuikg
  have hi1' : i = 1 := by_omega
  subst hi1'
  refine ⟨c', 1 + k, .seq e0 e, ?_, hw', hf', fun g hg => hS.final hR hg⟩
  have : c1.nreg 130210 = L.n := by zuohy
  omega

/-- **One entry of the preorder loop.** -/
theorem preBody_exec (hL : L.Good c0.nmem W) (hR0 : L.Regs c0) (hR : (L.tree c0.nmem).OK)
    {c : Config} (hw : WordsBounded W c) (hf : PFr ERG L.WR c0 c) {i : ℕ}
    (hi : c.nreg 130210 = i) (hin : i < L.n)
    (hsz : ∀ g, g < L.n → c.nmem ztdth = ((L.tree c0.nmem).sub g).card)
    (hP : (L.tree c0.nmem).PreInv ztryd ztlul i) :
    ∃ c' k, Exec P W preBody c c' k ∧ k = 19 ∧ WordsBounded W c' ∧ PFr ERG L.WR c0 c' ∧
      c'.nreg 130210 = i + 1 ∧ ztcbi ∧
      (L.tree c0.nmem).PreInv ztluj ztluk ztg := by
  zubwi

  have hi0 := hP.i_pos
  zuiaf
  have hqr : ztplc := by
    zuesz
  have hqr' : ztzpi := by
    tauto
  zufwc
  have hpq : R.par ztbed ≠ R.q i := by
    intro h; have := (hR.par_spec hqn hqr).2; simp_all
  -- reads
  zuibk
  have r2 : ztsej :=
    hf.2.2.2.2 _ ztrrp
  have r3 : ztseh :=
    hf.2.2.2.2 _ (hL.rvert _ hqn hqr').1
  have r4 : c.nmem (L.bSlot + R.par ztbed) = view c.nmem L.bSlot L.n ztwxc := by
    rw [view_lt hpn]
  have r5 : c.nmem _ = (R.sub _).card := hsz _ hqn
  zugng
  have := hL.wQ; have := hL.wPar; have := hL.wSz; have := hL.wn; have := hL.wPre; have := hL.wSlot
  have hstep := hP.step hR hin
  have hbd := hstep.bound i by_omega
  rw [Function.update_self] at hbd
  have hbd' : view c.nmem L.bSlot L.n _ + (R.sub _).card ≤ L.n := hbd
  have hσ := BTree.one_le_card_sub (R := R) hqn
  zucrn

  have r5' : ∀ X, upd c.nmem ztlfd X (L.bSz + R.q i) = (R.sub ztbed).card := by
    intro X; rw [Machine.upd_other _ _ _ by_omega, r5]
  unfold preBody
  exec_block
  all_goals try (config_simp; simp only [hRc.rQ, hRc.rPar, hRc.rVert, hRc.rSz, hRc.rPre,
    hRc.rSlot, hi, hRc.one, r1, r2, r3, r4, r5']; omega)
  refine ⟨rfl, by_omega, ?_, by config_simp; zuohx, ?_, ?_⟩
  · zulob
    · zubde
    · simp only [hRc.rQ, hRc.rPar, hRc.rVert, hRc.rSz, hRc.rPre, hRc.rSlot, hi, hRc.one, r1, r2,
        r3, r4, r5', Machine.upd_apply]
      zults

  · zubrf
    config_simp
    simp only [hRc.rQ, hRc.rPar, hRc.rVert, hRc.rSz, hRc.rPre, hRc.rSlot, hi, hRc.one, r1, r2,
      r3, r4, r5', Machine.upd_apply]
    grind
  · config_simp
    simp only [hRc.rQ, hRc.rPar, hRc.rVert, hRc.rSz, hRc.rPre, hRc.rSlot, hi, hRc.one, r1, r2,
      r3, r4, r5']
    have hv1 : ∀ X Y Z, view (upd ztxox
        ztrjw Z) L.bPre L.n = Function.update (view c.nmem L.bPre L.n) (R.q i) X := by
      zumgh
      rw [view_upd_out _ L.bPre L.n _ Z by_omega,
        view_upd_out _ L.bPre L.n _ Y by_omega,
        view_upd_in _ _ _ _ _ hqn]
    have hv2 : ∀ X Y Z, view (upd ztxox
        ztrjw Z) L.bSlot L.n = Function.update (Function.update
          ztlul ztwxc Y) (R.q i) Z := by
      zumgh
      rw [view_upd_in _ _ _ _ _ hqn, view_upd_in _ _ _ _ _ hpn,
        view_upd_out _ L.bSlot L.n _ X by_omega]
    grind

/-- The root of the preorder. -/
theorem preInit_exec (hL : L.Good c0.nmem W) (hR0 : L.Regs c0) (hR : (L.tree c0.nmem).OK)
    {c : Config} (hw : WordsBounded W c) (hf : PFr ERG L.WR c0 c)
    (hsz : ∀ g, g < L.n → c.nmem ztdth = ((L.tree c0.nmem).sub g).card) :
    ∃ c' k, Exec P W preInit c c' k ∧ k = 9 ∧ WordsBounded W c' ∧ PFr ERG L.WR c0 c' ∧
      c'.nreg 130210 = 1 ∧ ztcbi ∧
      (L.tree c0.nmem).PreInv ztluj ztluk 1 := by
  zubwi

  have hrn : R.root < L.n := hR.root_lt
  have r1 : c.nmem _ = R.root := hf.2.2.2.2 _ (hL.rq 0 hR.n_pos)
  have := hL.wQ; have := hL.wPre; have := hL.wSlot; have := hL.wSz; have := hL.wn
  zucrn

  unfold preInit
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp only [hRc.rQ, hRc.rPre, hRc.rSlot, r1]; omega)
  refine ⟨rfl, by_omega, ?_, by config_simp, ?_, ?_⟩
  · zulob
    · zubde
    · zufbm
      zults

  · zubrf
    config_simp
    zufbm
    grind
  · config_simp
    simp only [hRc.rQ, hRc.rPre, hRc.rSlot, r1, hRc.one]
    refine BTree.PreInv.init hR ?_ ?_
    · rw [view_lt hrn, Machine.upd_other _ _ _ by_omega, Machine.upd_same]
    · rw [view_lt hrn, Machine.upd_same]

/-- **Preorder intervals on the RAM.**  With a good layout and a well-formed tree read from
memory, `eulerStmt` runs in at most `45 n + 20` steps, writes only the arrays `SZ`, `PRE`, `SLOT`
and its registers, and ends with the true subtree sizes in `SZ` and the final preorder invariant
(hence `BTree.PreInv.anc_iff`: descendants are exactly the preorder intervals). -/
theorem eulerStmt_exec (hL : L.Good c0.nmem W) (hR0 : L.Regs c0) (hR : (L.tree c0.nmem).OK)
    (hw : WordsBounded W c0) :
    ∃ c' k, Exec P W eulerStmt c0 c' k ∧ k ≤ 45 * L.n + 20 ∧ WordsBounded W c' ∧
      PFr ERG L.WR c0 c' ∧
      ztcbi ∧
      (L.tree c0.nmem).PreInv ztluj ztluk L.n := by
  have := hL.wSz; have := hL.wn
  -- fill `SZ` with `1`
  obtain ⟨c1, e1, hw1, h150, h151, h152, hr1⟩ : ∃ c1, Exec P W eulerFillSet c0 c1 3 ∧
      WordsBounded W c1 ∧ c1.nreg 130150 = L.bSz ∧ c1.nreg 130151 = L.n ∧
      c1.nreg 130152 = 1 ∧ PFr ERG L.WR c0 c1 := by
    unfold eulerFillSet
    have a1 := Exec.copyN (P := P) hw 130150 130203
    have a2 := Exec.copyN (P := P) a1.wb_right 130151 130206
    have a3 := Exec.constN (P := P) a2.wb_right 130152 1 by_omega
    refine ⟨_, Exec.block_cons a1 (Exec.block_cons a2 (Exec.block_cons a3
      (Exec.block_nil a3.wb_right))), a3.wb_right, ?_, ?_, ?_, ?_⟩
    · simp [hR0.rSz]
    · simp [hR0.rn]
    · simp
    · refine PFr.nreg (PFr.refl c0) ztez
      zubde
  have hone1 := (Regs_of_pfr hR0 hr1).one
  obtain ⟨c2, k2, e2, hk2, hf2, hfill⟩ := fillStmt_exec (P := P) hw1 hone1
    by_omega by_omega
  have hr2 := hr1.trans (hf2.mono (fun r hr => by
    unfold FillScr at hr; unfold ERG; omega) (fun a ha => by
      rw [h150, h151] at ha; unfold ELay.WR; omega))
  zubig

  obtain ⟨c3, k3, e3, hk3, hw3, hr3, hsz3⟩ := sizeLoop_exec (P := P) hL hR0 hR e2.wb_right hr2
    hfill
  obtain ⟨c4, k4, e4, hk4, hw4, hr4, hi4, hsz4, hP4⟩ := preInit_exec (P := P) hL hR0 hR hw3 hr3
    hsz3
  obtain ⟨c5, k5, e5, hk5, hw5, hr5, hi5, -, hsz5, hP5⟩ := forN (P := P) (W := W) (ri := 130210)
    (rn := 130206) (body := preBody)
    (fun j c => WordsBounded W c ∧ PFr ERG L.WR c0 c ∧ c.nreg 130210 = j ∧
      c.nreg 130206 = L.n ∧
      (∀ g, g < L.n → c.nmem ztdth = ((L.tree c0.nmem).sub g).card) ∧
      (L.tree c0.nmem).PreInv ztryd ztlul j)
    L.n 19 (fun j c h => ⟨h.1, h.2.2.1, h.2.2.2.1⟩)
    (fun j c hj ⟨hw, hf, hi, hn, hsz, hP⟩ => by
      obtain ⟨c', k, e, hk, hw', hf', hi', hsz', hP'⟩ := preBody_exec (P := P) hL hR0 hR hw hf hi
        hj hsz hP
      exact ⟨c', k, e, by_omega, hw', hf', hi', (Regs_of_pfr hR0 hf').rn, hsz', hP'⟩)
    (j₀ := 1) ⟨hw4, hr4, hi4, (Regs_of_pfr hR0 hr4).rn, hsz4, hP4⟩ hR.n_pos
  refine ⟨c5, 3 + ztvs, .seq e1 ztbxo, ?_, hw5,
    hr5, hsz5, hP5⟩
  omega
end proofs
def firstBody : Stmt := block [.addN 130225 130221 130224, .loadN 130226 130225,
  .addN 130225 130222 130226, .storeN 130225 130224, .addN 130224 130224 130001]

/-- **The first darts.** -/
def firstStmt : Stmt := .seq (.instr (.constN 130224 0)) (.whileLtN 130224 130223 firstBody)

/-- The registers written. -/
def FirstRG (r : ℕ) : Prop := 130224 ≤ r ∧ r ≤ 130226
section proofs
variable {P : Polygon} {W : ℕ}

/-- **The first darts**: if the tails of the `N` darts are below `nv` and every vertex `u < nv`
is a tail, then afterwards `FIRST[u] < N` and `VERT[FIRST[u]] = u` for all `u < nv`, in at most
`7 N + 3` steps, writing only `FIRST` (and the scratch registers). -/
theorem firstStmt_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    {bV bF N nv : ℕ} (hbV : c.nreg 130221 = bV) (hbF : c.nreg 130222 = bF) (hN : c.nreg 130223 = N)
    (hvlt : ∀ d, d < N → c.nmem zthdv < nv) (hsurj : ∀ u, u < nv → ∃ d, d < N ∧ c.nmem zthdv = u)
    (hdisj : bF + nv ≤ bV ∨ bV + N ≤ bF) (hwV : bV + N ≤ W) (hwF : bF + nv ≤ W) (hwN : N + 1 ≤ W) :
    ∃ c' k, Exec P W firstStmt c c' k ∧ k ≤ 7 * N + 3 ∧
      PFr FirstRG ztisk c c' ∧
      ∀ u, u < nv → c'.nmem ztdts < N ∧ c.nmem ztzkn = u := by
  have e0 := Exec.constN (P := P) hw 130224 0 by_omega
  obtain ⟨c', k, e, hk, hw', hi', hn', hf', hI⟩ := forN (P := P) (W := W) (ri := 130224)
    (rn := 130223) (body := firstBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130224 = j ∧ c'.nreg 130223 = N ∧
      PFr FirstRG ztisk c c' ∧
      ∀ u, u < nv → (∃ d, d < j ∧ c.nmem zthdv = u) →
        c'.nmem ztdts < j ∧ c.nmem ztzkn = u)
    N 5 zthd
    (fun j c2 hj ⟨hw2, hi2, hn2, hf2, hI2⟩ => by
      have r1 : c2.nreg 130221 = bV := (hf2.1 _ ztjqu).trans hbV
      have r2 : c2.nreg 130222 = bF := (hf2.1 _ ztjqu).trans hbF
      have r3 : zthoo := (hf2.1 _ ztjqu).trans hone
      have rv : c2.nmem zttgl = c.nmem zttgl := hf2.2.2.2.2 _ by_omega
      have hvj := hvlt j hj
      unfold firstBody
      exec_block
      · omega
      · config_simp; grind
      · config_simp; omega
      · refine ⟨le_refl _, ‹_›, by_simp_all, by_simp_all, ?_, ?_⟩
        · zuloc
          · zumwj; unfold FirstRG at hr; grind
          · rw [r2, r1, hi2, rv, Machine.upd_other _ _ _ by_omega]
        · intro u hu hex
          config_simp
          rw [r2, r1, hi2, rv, Machine.upd_apply]
          zus
          · omega
          grind)
    (j₀ := 0) ⟨e0.wb_right, by_simp, by_simp_all, PFr.nreg ztffw (fun r hr => by
      zumwj; unfold FirstRG at hr; grind),
      fun u hu ⟨d, hd, _⟩ => absurd hd (Nat.not_lt_zero d)⟩ (Nat.zero_le _)
  refine ⟨c', 1 + k, .seq e0 e, by_omega, hf', fun u hu => hI u hu (hsurj u hu)⟩
end proofs
section map
variable {P : Polygon} {W : ℕ}

/-- **Map loop.**  If from every configuration of the frame with counter `j < n` the body stores
`F j` at `bOut + j`, advances the counter and changes only registers in `Rg`, the loop stores
`F j` for all `j ∈ [j₀, n)`. -/
theorem mapLoop {ri rn : ℕ} {body : Stmt} {Rg : ℕ → Prop} (_hri : Rg ri) (hrn : ¬ Rg rn)
    {bOut n j₀ B : ℕ} (F : ℕ → ℕ) {c0 : Config} (hw0 : WordsBounded W c0)
    (hi0 : c0.nreg ri = j₀) (hn0 : c0.nreg rn = n) (hj₀ : j₀ ≤ n)
    (hbody : ∀ j c, j₀ ≤ j → j < n → WordsBounded W c → c.nreg ri = j →
      PFr Rg ztdnm c0 c →
      ∃ c' k, Exec P W body c c' k ∧ k ≤ B ∧ c'.nreg ri = j + 1 ∧
        (∀ r, ¬ Rg r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
        c'.output = c.output ∧ c'.nmem = upd c.nmem zttgd (F j)) :
    ∃ c' k, Exec P W zthqm c0 c' k ∧ k ≤ zthb * ztodq + 2 ∧
      WordsBounded W c' ∧ c'.nreg ri = n ∧
      PFr Rg ztdnm c0 c' ∧
      ∀ j, j₀ ≤ j → j < n → c'.nmem zttgd = F j := by
  obtain ⟨c', k, e, hk, hw', hi', hn', hf', hI⟩ := forN (P := P) (W := W) (ri := ri) (rn := rn)
    (body := body)
    (fun j c => WordsBounded W c ∧ c.nreg ri = j ∧ c.nreg rn = n ∧
      PFr Rg ztdnm c0 c ∧ j₀ ≤ j ∧
      ∀ i, j₀ ≤ i → i < j → c.nmem (bOut + i) = F i)
    n B ztywd
    (fun j c hj ⟨hw, hi, hn, hf, hjj, hm⟩ => by
      obtain ⟨c', k, e, hk, hi', hr', hrr', hrm', ho', hm'⟩ := hbody j c hjj hj hw hi hf
      refine ⟨c', k, e, hk, e.wb_right, hi', by_simp_all, ⟨fun r hr => ?_,
        hrr'.trans hf.2.1, hrm'.trans hf.2.2.1, ho'.trans hf.2.2.2.1, fun a ha => ?_⟩,
        by omega, fun i hi1 hi2 => ?_⟩
      · rw [hr' r hr]; exact hf.1 r hr
      · have hne : bOut + j ≠ a := by_omega
        rw [hm', Machine.upd_other _ _ _ hne.symm]
        exact hf.2.2.2.2 a ha
      · zugec
        grind)
    (j₀ := j₀) ⟨hw0, hi0, hn0, PFr.refl c0, le_rfl, fun i h1 h2 => by_omega⟩ hj₀
  grind
end map

/-! ## Parent arrays -/

/-- One vertex: `OUT[x] := VA[PA[x]]`, `x := x + 1`. -/
def parBody : Stmt := block [.addN 130505 130501 130504, .loadN 130506 130505,
  .addN 130505 130500 130506, .loadN 130506 130505, .addN 130505 130502 130504,
  .storeN 130505 130506, .addN 130504 130504 130001]

/-- **The parent array**: `OUT[0] := 0`, then `OUT[x] := VA[PA[x]]` for `1 ≤ x < n`. -/
def parStmt : Stmt := .seq ztksp
  (.whileLtN 130504 130503 parBody)

/-- The scratch registers of `parStmt`. -/
def ParRG (r : ℕ) : Prop := 130504 ≤ r ∧ r ≤ 130506
section par
variable {P : Polygon} {W : ℕ}

/-- **The parent array.** -/
theorem parStmt_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    (hzero : c.nreg 130009 = 0) {bVA bPA bOut n : ℕ} (hVA : c.nreg 130500 = bVA)
    (hPA : c.nreg 130501 = bPA) (hOut : c.nreg 130502 = bOut) (hn : c.nreg 130503 = n)
    (hn1 : 1 ≤ n) (hwP : bPA + n ≤ W) (hwO : bOut + n ≤ W)
    (hdP : bOut + n ≤ bPA ∨ bPA + n ≤ bOut)
    (hVAw : ∀ x, 1 ≤ x → x < n → bVA + c.nmem zthdr ≤ W ∧
      (bVA + c.nmem zthdr < bOut ∨ bOut + n ≤ bVA + c.nmem zthdr)) :
    ∃ c' k, Exec P W parStmt c c' k ∧ k ≤ 9 * n + 4 ∧ WordsBounded W c' ∧
      PFr ParRG (fun a => bOut ≤ a ∧ a < bOut + n) c c' ∧ c'.nmem bOut = 0 ∧
      ∀ x, 1 ≤ x → x < n → c'.nmem (bOut + x) = c.nmem ztzkp := by
  obtain ⟨c1, k1, e1, hk1, hw1, h1m, h1r, h1c, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      ztksp c c1 k1 ∧ k1 = 2 ∧
      WordsBounded W c1 ∧ c1.nmem = upd c.nmem bOut 0 ∧
      (∀ r, r ≠ 130504 → c1.nreg r = c.nreg r) ∧ c1.nreg 130504 = 1 ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    simp_all
  have hmem1 : ∀ a, a ≠ bOut → c1.nmem a = c.nmem a := by
    simp_all
  obtain ⟨c', k, e, hk, hw', -, hf', hI⟩ := mapLoop (P := P) (W := W) (ri := 130504)
    (rn := 130503) (body := parBody) (Rg := ParRG) by_trivial
    zteqm (bOut := bOut) (n := n) (j₀ := 1) (B := 7)
    (fun x => c.nmem ztzkp) hw1 h1c
    by_simp_all hn1
    (fun j c2 hj1 hjn hw2 hi2 hf2 => by
      have r0 := fun r hr =>
        (hf2.1 r hr).trans (h1r r ztzfd)
      have rVA := (r0 130500 zteqm).trans hVA
      have rPA := (r0 130501 zteqm).trans hPA
      have rO := (r0 130502 zteqm).trans hOut
      have r1 := (r0 130001 zteqm).trans hone
      have m0 : ∀ a, ¬ (bOut + 1 ≤ a ∧ a < bOut + n) → a ≠ bOut → c2.nmem a = c.nmem a :=
        fun a h1 h2 => (hf2.2.2.2.2 a h1).trans by_simp_all
      have mP : c2.nmem _ = c.nmem zttge := m0 _ by_omega by_omega
      obtain ⟨hwv, hdv⟩ := hVAw j hj1 hjn
      have mV : c2.nmem _ = c.nmem (bVA + c.nmem zttge) :=
        m0 _ by_omega by_omega
      unfold parBody
      exec_block
      · omega
      · config_simp; grind
      · config_simp; omega
      · config_simp; omega
      · refine ⟨le_refl _, by config_simp; omega, fun r hr => ?_, rfl, rfl, rfl, ?_⟩
        · zumwj; unfold ParRG at hr; grind
        grind)
  zultc
  refine ⟨c', 2 + k, .seq e1 e, by_omega, hw', ⟨fun r hr => ?_, hf'.2.1.trans hrr1,
    hf'.2.2.1.trans hrm1, hf'.2.2.2.1.trans ho1, fun a ha => ?_⟩, ?_, fun x hx1 hxn => ?_⟩
  · rw [hf'.1 r hr]; exact h1r r ztzfd
  · rw [hf'.2.2.2.2 a by_omega]; grind
  · rw [hf'.2.2.2.2 bOut by_omega, h1m, Machine.upd_same]
  simp_all
end par

/-! ## Binary-lifting tables -/

/-- Row `0`, one cell: `TAB[x] := PARENT[x]`. -/
def row0Body : Stmt := block [.addN 130518 130510 130517, .loadN 130519 130518,
  .addN 130518 130511 130517, .storeN 130518 130519, .addN 130517 130517 130001]

/-- Row `j`, one cell: `TAB[j n + x] := TAB[(j-1) n + TAB[(j-1) n + x]]` (`130515` holds the base
of row `j - 1`, `130516` that of row `j`). -/
def cellBody : Stmt := block [.addN 130518 130515 130517, .loadN 130519 130518,
  .addN 130518 130515 130519, .loadN 130519 130518, .addN 130518 130516 130517,
  .storeN 130518 130519, .addN 130517 130517 130001]

/-- One row. -/
def rowBody : Stmt := .seq ztotm (.seq (.whileLtN 130517 130512 cellBody)
  ztgqv)

/-- **The binary-lifting table** of the parent array `PARENT`. -/
def upStmt : Stmt := .seq ztotm (.seq (.whileLtN 130517 130512 row0Body)
  (.seq zthea
    (.whileLtN 130514 130513 rowBody)))

/-- The scratch registers of `upStmt`. -/
def UpRG (r : ℕ) : Prop := 130514 ≤ r ∧ r ≤ 130519
section up
variable {P : Polygon} {W : ℕ}

/-- The registers of the cell loops. -/
def CellRG (r : ℕ) : Prop := 130517 ≤ r ∧ r ≤ 130519

/-- **One row of the table.** -/
theorem rowBody_exec {c0 c4 : Config} (hw4 : WordsBounded W c4) {bT n L j : ℕ}
    (up : ℕ → ℕ) (hupl : ∀ m x, x < n → up^[m] x < n)
    (hone : c4.nreg 130001 = 1) (hn : c4.nreg 130512 = n) (hj4 : c4.nreg 130514 = j)
    (h4a : c4.nreg 130515 = bT + zthv * n) (h4b : c4.nreg 130516 = bT + j * n)
    (hj1 : 1 ≤ j) (hjL : j < L) (hwT : bT + L * n ≤ W) (hLW : L + 1 ≤ W) (hn1 : 1 ≤ n)
    (hf4 : PFr UpRG ztbde c0 c4)
    (hI4 : ∀ i, i < j → ∀ x, x < n → c4.nmem zthdu = up^[2 ^ i] x) :
    ∃ c5 k, Exec P W rowBody c4 c5 k ∧ k ≤ 12 * n + 5 ∧ WordsBounded W c5 ∧
      c5.nreg 130514 = j + 1 ∧ c5.nreg 130515 = bT + (j + 1 - 1) * n ∧
      c5.nreg 130516 = bT + ztl * n ∧
      PFr UpRG ztbde c0 c5 ∧
      ∀ i, i < j + 1 → ∀ x, x < n → c5.nmem zthdu = up^[2 ^ i] x := by
  have hjn : zthv * n + n = j * n := by
    zuoqy; simp_all
  have hjLn : j * n + n ≤ L * n := by
    have := Nat.mul_le_mul_right n ztmnx
    grind
  have e0 := Exec.constN (P := P) hw4 130517 0 by_omega
  set c5 := { c4 with nreg := upd c4.nreg 130517 0 }
  have hf5 : PFr CellRG (fun a => bT + j * n + 0 ≤ a ∧ a < bT + j * n + n) c4 c5 :=
    PFr.nreg (PFr.refl c4) (fun r hr => by
      zumwj; unfold CellRG at hr; grind)
  obtain ⟨c6, k6, e6, hk6, hw6, hi6, hf6, hI6⟩ := mapLoop (P := P) (W := W) (ri := 130517)
    (rn := 130512) (body := cellBody) (Rg := CellRG) by_tauto
    ztchf (bOut := bT + j * n) (n := n) (j₀ := 0) (B := 7)
    (fun x => up^[2 ^ j] x) e0.wb_right by_rfl by_tauto ztbg
    (fun x c7 _ hxn hw7 hi7 hf7 => by
      have hf57 := hf5.trans hf7
      have r0 := hf57.1
      have ra := (r0 130515 ztchf).trans h4a
      have rb := (r0 130516 ztchf).trans h4b
      have r1 := (r0 130001 ztchf).trans hone
      have hx1 : c7.nmem (bT + zthv * n + x) = up^[2 ^ zthv] x := by
        zuijt
      set y := up^[2 ^ zthv] x
      have hyn : y < n := by_grind
      have hx2 : c7.nmem (bT + zthv * n + y) = up^[2 ^ zthv] y := by
        zuijt
      have hval : up^[2 ^ zthv] y = up^[2 ^ j] x := by
        simp only [y]
        zuoqt
        zucr
        rw [← two_mul, ← pow_succ']
        simp_all
      unfold cellBody
      exec_block
      · omega
      · config_simp; rw [ra, hi7, hx1]; omega
      · config_simp; omega
      · config_simp; omega
      · refine ⟨le_refl _, by config_simp; omega, fun r hr => ?_, rfl, rfl, rfl, ?_⟩
        · zumwj; unfold CellRG at hr; split_ifs <;> omega
        simp_all)
  have hf46 := hf5.trans hf6
  have r6 := hf46.1
  have rn6 := (r6 130512 ztchf).trans hn
  have rj6 := (r6 130514 ztchf).trans hj4
  have rb6 := (r6 130516 ztchf).trans h4b
  have r16 := (r6 130001 ztchf).trans hone
  obtain ⟨c7, k7, e7, hk7, hw7, h7a, h7b, h7j, h7r, hrr7, hrm7, ho7, hm7⟩ : ∃ c7 k7, Exec P W
      ztgqv
      c6 c7 k7 ∧ k7 = 3 ∧ WordsBounded W c7 ∧ c7.nreg 130515 = bT + j * n ∧
      c7.nreg 130516 = bT + ztl * n ∧ c7.nreg 130514 = j + 1 ∧
      (∀ r, r ≠ 130514 → r ≠ 130515 → r ≠ 130516 → c7.nreg r = c6.nreg r) ∧
      c7.rreg = c6.rreg ∧ c7.rmem = c6.rmem ∧ c7.output = c6.output ∧ c7.nmem = c6.nmem := by
    exec_block
    all_goals first
      | (config_simp; rw [rb6, rn6]; omega)
      | (config_simp; rw [rj6, r16]; omega)
      | skip
    · refine ⟨rfl, by_omega, by_simp_all, by config_simp; grind,
        by simp_all, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
      simp_all
  subst hk7
  refine ⟨c7, 1 + (k6 + 3), .seq e0 ztsqa, by_omega, hw7, h7j,
    by grind, h7b, ztgox, fun i hi x hx => ?_⟩
  · rw [h7r r ztcmn ztcmn
      ztcmn, r6 r (by unfold CellRG UpRG at *; omega)]
    exact hf4.1 r hr
  · rw [hrr7, hf46.2.1, hf4.2.1]
  · rw [hrm7, hf46.2.2.1, hf4.2.2.1]
  · rw [ho7, hf46.2.2.2.1, hf4.2.2.2.1]
  · rw [hm7, hf46.2.2.2.2 a by_omega]; exact hf4.2.2.2.2 a ha
  · rw [hm7]
    zuoz
    · have hle : i * n + n ≤ j * n := by
        have := Nat.mul_le_mul_right n (show i + 1 ≤ j by omega)
        grind
      rw [hf46.2.2.2.2 _ by_grind]
      grind
    grind

/-- **The binary-lifting table**: `TAB[j n + x] = up^[2^j] x` for `j < L`, `x < n`, where
`up x = PARENT[x]` maps `[0, n)` into itself; cost `≤ 12 n L + 7 L + 12`. -/
theorem upStmt_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    {bPa bT n L : ℕ} (hPa : c.nreg 130510 = bPa) (hT : c.nreg 130511 = bT)
    (hn : c.nreg 130512 = n) (hL : c.nreg 130513 = L) (hL1 : 1 ≤ L)
    (hup : ∀ x, x < n → c.nmem (bPa + x) < n) (hwPa : bPa + n ≤ W) (hwT : bT + L * n ≤ W)
    (hd : bPa + n ≤ bT ∨ bT + L * n ≤ bPa) (hLW : L + 1 ≤ W) (hn1 : 1 ≤ n) :
    ∃ c' k, Exec P W upStmt c c' k ∧ k ≤ 12 * n * L + 7 * L + 12 ∧ WordsBounded W c' ∧
      PFr UpRG ztbde c c' ∧
      ∀ j, j < L → ∀ x, x < n →
        c'.nmem (bT + j * n + x) = (fun y => c.nmem (bPa + y))^[2 ^ j] x := by
  set up : ℕ → ℕ := fun y => c.nmem _ with hupdef
  have hupl : ∀ m x, x < n → up^[m] x < n := by
    intro m; induction m with
    | zero => intro x hx; exact hx
    | succ m ih => intro x hx; rw [Function.iterate_succ_apply]; exact by_simp_all
  have hLn : n ≤ L * n := Nat.le_mul_of_pos_left n by_omega
  -- row 0
  have e0 := Exec.constN (P := P) hw 130517 0 by_omega
  set c1 := { c with nreg := upd c.nreg 130517 0 }
  have hf1 : PFr UpRG ztbde c c1 :=
    PFr.nreg ztffw (fun r hr => by
      zumwj; unfold UpRG at hr; grind)
  obtain ⟨c2, k2, e2, hk2, hw2, -, hf2, hI2⟩ := mapLoop (P := P) (W := W) (ri := 130517)
    (rn := 130512) (body := row0Body) (Rg := UpRG) by_trivial
    ztbml (bOut := bT) (n := n) (j₀ := 0) (B := 5) up e0.wb_right
    by_rfl
    by_tauto ztbg
    (fun j c3 _ hjn hw3 hi3 hf3 => by
      have r0 := fun r hr =>
        (hf3.1 r hr).trans (hf1.1 r hr)
      have rPa := (r0 130510 ztbml).trans hPa
      have rT := (r0 130511 ztbml).trans hT
      zugnv
      have mP : c3.nmem _ = c.nmem (bPa + j) :=
        (hf3.2.2.2.2 _ by_grind).trans (hf1.2.2.2.2 _ by_omega)
      unfold row0Body
      exec_block
      · omega
      · config_simp; omega
      · config_simp; omega
      · zumkg
        · zumwj; unfold UpRG at hr; grind
        simp_all)
  have hf12 :=
    hf1.trans (hf2.mono by_simp_all by_grind)
  -- the row setup
  have hr2 := hf12.1
  have rT2 := (hr2 130511 ztbml).trans hT
  have rn2 := (hr2 130512 ztbml).trans hn
  have r12 := (hr2 130001 ztbml).trans hone
  obtain ⟨c3, k3, e3, hk3, hw3, h3a, h3b, h3j, h3r, hrr3, hrm3, ho3, hm3⟩ : ∃ c3 k3, Exec P W
      zthea c2 c3 k3 ∧
      k3 = 3 ∧ WordsBounded W c3 ∧ c3.nreg 130515 = bT ∧ c3.nreg 130516 = bT + n ∧
      c3.nreg 130514 = 1 ∧ (∀ r, r ≠ 130514 → r ≠ 130515 → r ≠ 130516 → c3.nreg r = c2.nreg r) ∧
      c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output ∧ c3.nmem = c2.nmem := by
    exec_block
    all_goals first
      | (config_simp; rw [rT2, rn2]; omega)
      | skip
    simp_all
  have hf3 : PFr UpRG ztbde c c3 :=
    ⟨fun r hr => (h3r r ztcmn ztcmn
      ztcmn).trans by_simp_all, hrr3.trans hf12.2.1,
      hrm3.trans hf12.2.2.1, ho3.trans hf12.2.2.2.1, fun a ha => by rw [hm3]; exact hf12.2.2.2.2 a ha⟩
  -- the rows
  obtain ⟨c', k, e, hk, hw', -, -, -, -, hf', -, hrows⟩ := forN (P := P) (W := W)
    (ri := 130514) (rn := 130513) (body := rowBody)
    (fun j c4 => WordsBounded W c4 ∧ c4.nreg 130514 = j ∧ c4.nreg 130513 = L ∧
      c4.nreg 130515 = bT + zthv * n ∧ c4.nreg 130516 = bT + j * n ∧
      PFr UpRG ztbde c c4 ∧ 1 ≤ j ∧
      ∀ i, i < j → ∀ x, x < n → c4.nmem zthdu = up^[2 ^ i] x)
    L (12 * n + 5) ztywe
    (fun j c4 hjL ⟨hw4, hj4, hL4, h4a, h4b, hf4, hj1, hI4⟩ => by
      zumfn
      have rn := (r0 130512 ztbml).trans hn
      zugnv
      obtain ⟨c5, k5, e5, hk5, hw5, h5j, h5a, h5b, hf5, hI5⟩ := rowBody_exec (P := P) hw4 up hupl
        r1 rn hj4 h4a h4b hj1 hjL hwT hLW hn1 hf4 hI4
      exact ⟨c5, k5, e5, hk5, hw5, h5j, by rw [hf5.1 _ ztbml, hL], h5a, h5b,
        hf5, by_omega, hI5⟩)
    (j₀ := 1) ⟨hw3, h3j, by rw [h3r _ by_omega by_omega by_omega,
      hr2 _ ztbml, hL],
      by omega, by_omega, hf3, le_rfl, fun i hi x hx => by
        zudgv
        zumo
        rw [hm3, Nat.zero_mul, add_zero, hI2 x ztbg hx]
        simp⟩ hL1
  subst hk3
  refine ⟨c', 1 + (k2 + (3 + k)), .seq e0 ztgwz, ?_, hw', hf', hrows⟩
  have hLm : (12 * n + 5 + 2) * ztszb + (12 * n + 7) = 12 * n * L + 7 * L := by
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by_omega⟩
    grind
  omega
end up
def ArrRG (r : ℕ) : Prop := 130554 ≤ r ∧ r ≤ 130556

/-- `OUT[i] := a + i`. -/
def affBody : Stmt := block [.addN 130555 130553 130554, .addN 130556 130550 130554,
  .storeN 130556 130555, .addN 130554 130554 130001]

/-- **Affine fill.** -/
def affStmt : Stmt := .seq ztfen (.whileLtN 130554 130552 affBody)

/-- `OUT[i] := a + IN[i]`. -/
def shBody : Stmt := block [.addN 130555 130551 130554, .loadN 130555 130555,
  .addN 130555 130553 130555, .addN 130556 130550 130554, .storeN 130556 130555,
  .addN 130554 130554 130001]

/-- **Shifted copy.** -/
def shStmt : Stmt := .seq ztfen (.whileLtN 130554 130552 shBody)

/-- `OUT[i] := [IN[i] = i]`. -/
def eqBody : Stmt := .seq (block [.addN 130555 130551 130554, .loadN 130555 130555,
    .addN 130556 130550 130554, .storeN 130556 130009])
  (.seq (.ifLtN 130555 130554 .skip ztipk)
    (.instr (.addN 130554 130554 130001)))

/-- **Equality flags.** -/
def eqStmt : Stmt := .seq ztfen (.whileLtN 130554 130552 eqBody)
section proofs
variable {P : Polygon} {W : ℕ}
variable {c : Config}
/-- The common frame of the three loops. -/
theorem arr_start (hw : WordsBounded W c) {bO n : ℕ} :
    Exec P W ztfen c { c with nreg := upd c.nreg 130554 0 } 1 ∧
    PFr ArrRG (fun a => bO + 0 ≤ a ∧ a < bO + n) c { c with nreg := upd c.nreg 130554 0 } := by
  refine ⟨Exec.constN (P := P) hw 130554 0 by_omega, PFr.nreg ztffw ztez⟩
  zubdd

/-- **Affine fill**: `OUT[i] = a + i` for `i < n`. -/
theorem affStmt_exec (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    {bO n a : ℕ} (hO : c.nreg 130550 = bO) (hn : c.nreg 130552 = n) (ha : c.nreg 130553 = a)
    (hwO : bO + n ≤ W) (hwa : a + n ≤ W) :
    ∃ c' k, Exec P W affStmt c c' k ∧ k ≤ 6 * n + 3 ∧ WordsBounded W c' ∧
      PFr ArrRG zteck c c' ∧ ∀ i, i < n → c'.nmem ztnrv = a + i := by
  zupq
  obtain ⟨c', k, e, hk, hw', -, hf', hI⟩ := mapLoop (P := P) (W := W) (ri := 130554)
    (rn := 130552) (body := affBody) (Rg := ArrRG) by_tauto
    ztxf (bOut := bO) (n := n) (j₀ := 0) (B := 4) (fun i => a + i)
    e0.wb_right by_simp
    by_simp_all ztbg
    (fun j c2 _ hjn hw2 hi2 hf2 => by
      have r0 : ztfan := (hf1.trans hf2).1
      have rO := (r0 130550 ztxf).trans hO
      zucsa

      unfold affBody
      exec_block
      all_goals try (config_simp; simp only [rO, ra, r1, hi2]; omega)
      zumkg
      · zubdd
      simp_all)
  refine ⟨c', 1 + k, .seq e0 e, by_omega, hw', (hf1.trans hf').mono ztng
    ztjwr,
    fun i hi => hI i ztbg hi⟩

/-- **Shifted copy**: `OUT[i] = a + IN[i]` for `i < n`. -/
theorem shStmt_exec (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    {bO bI n a : ℕ} (hO : c.nreg 130550 = bO) (hI : c.nreg 130551 = bI)
    (hn : c.nreg 130552 = n) (ha : c.nreg 130553 = a)
    (hwO : bO + n ≤ W) (hwI : bI + n ≤ W) (hd : bO + n ≤ bI ∨ bI + n ≤ bO)
    (hwa : ∀ i, i < n → a + c.nmem ztdgo ≤ W) :
    ∃ c' k, Exec P W shStmt c c' k ∧ k ≤ 8 * n + 3 ∧ WordsBounded W c' ∧
      PFr ArrRG zteck c c' ∧
      ∀ i, i < n → c'.nmem ztnrv = a + c.nmem ztdgo := by
  zupq
  obtain ⟨c', k, e, hk, hw', -, hf', hI'⟩ := mapLoop (P := P) (W := W) (ri := 130554)
    (rn := 130552) (body := shBody) (Rg := ArrRG) by_tauto
    ztxf (bOut := bO) (n := n) (j₀ := 0) (B := 6)
    (fun i => a + c.nmem ztdgo) e0.wb_right by_simp
    by_simp_all ztbg
    (fun j c2 _ hjn hw2 hi2 hf2 => by
      zubgc

      zucsa

      zuibg
      have := hwa j hjn
      unfold shBody
      exec_block
      all_goals try (config_simp; simp only [rO, rI, ra, r1, hi2, mI]; omega)
      zumkg
      · zubdd
      simp_all)
  refine ⟨c', 1 + k, .seq e0 e, by_omega, hw', (hf1.trans hf').mono ztng
    ztjwr,
    fun i hi => hI' i ztbg hi⟩

/-- **Equality flags**: `OUT[i] = 1` if `IN[i] = i`, else `0`, for `i < n`. -/
theorem eqStmt_exec (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    (hzero : c.nreg 130009 = 0) {bO bI n : ℕ} (hO : c.nreg 130550 = bO)
    (hI : c.nreg 130551 = bI) (hn : c.nreg 130552 = n)
    (hwO : bO + n ≤ W) (hwI : bI + n ≤ W) (hd : bO + n ≤ bI ∨ bI + n ≤ bO) :
    ∃ c' k, Exec P W eqStmt c c' k ∧ k ≤ 12 * n + 3 ∧ WordsBounded W c' ∧
      PFr ArrRG zteck c c' ∧
      ∀ i, i < n → c'.nmem ztnrv = if c.nmem ztdgo = i then 1 else 0 := by
  zupq
  obtain ⟨c', k, e, hk, hw', -, hf', hI'⟩ := mapLoop (P := P) (W := W) (ri := 130554)
    (rn := 130552) (body := eqBody) (Rg := ArrRG) by_tauto
    ztxf (bOut := bO) (n := n) (j₀ := 0) (B := 10)
    (fun i => if c.nmem ztdgo = i then 1 else 0) e0.wb_right by_simp
    by_simp_all ztbg
    (fun j c2 _ hjn hw2 hi2 hf2 => by
      zubgc

      have r0' := (r0 130009 ztxf).trans hzero
      have r1 := (r0 130001 ztxf).trans hone
      zuibg
      obtain ⟨c3, k3, e3, hk3, hw3, h3v, h3a, h3i, h3r, hrr3, hrm3, ho3, hm3⟩ : ∃ c3 k3,
          Exec P W (block [.addN 130555 130551 130554, .loadN 130555 130555,
            .addN 130556 130550 130554, .storeN 130556 130009]) c2 c3 k3 ∧ k3 = 4 ∧
          WordsBounded W c3 ∧ c3.nreg 130555 = c.nmem ztctv ∧ c3.nreg 130556 = bO + j ∧
          c3.nreg 130554 = j ∧ (∀ r, ¬ ArrRG r → c3.nreg r = c2.nreg r) ∧
          c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output ∧
          c3.nmem = upd c2.nmem zthdq 0 := by
        exec_block
        all_goals try (config_simp; simp only [rO, rI, hi2, mI]; omega)
        refine ⟨rfl, ‹_›, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, ?_⟩
        · simp_all
        · simp_all
        · simp_all
        · zubdd
        simp_all
      have hone3 : ztpmn := (h3r _ ztxf).trans r1
      -- the test and the increment
      have hfin : ∀ c4 k4, Exec P W (.ifLtN 130555 130554 .skip
          ztipk) c3 c4 k4 →
          c4.nreg = c3.nreg → c4.rreg = c3.rreg → c4.rmem = c3.rmem → c4.output = c3.output →
          c4.nmem = upd c2.nmem zthdq ztyfd → k4 ≤ 5 →
          ∃ c' k, Exec P W eqBody c2 c' k ∧ k ≤ 10 ∧ c'.nreg 130554 = j + 1 ∧
            (∀ r, ¬ ArrRG r → c'.nreg r = c2.nreg r) ∧ c'.rreg = c2.rreg ∧
            c'.rmem = c2.rmem ∧ c'.output = c2.output ∧
            c'.nmem = upd c2.nmem zthdq ztyfd := by
        intro c4 k4 e4 hr4 hrr4 hrm4 ho4 hm4 hk4
        zubgi
        have e5 := Exec.addN (P := P) hw4 130554 130554 130001 (by
          grind)
        refine ⟨_, k3 + ztfsx, .seq e3 ztncj, by_omega, by_simp_all,
          fun r hr => ?_, hrr4.trans hrr3, hrm4.trans hrm3, ho4.trans ho3, by_omega⟩
        zudi
        rw [ite_eq_right (by unfold ArrRG at hr; omega), hr4, h3r r hr]
      by_cases h1 : c3.nreg 130555 < c3.nreg 130554
      · refine hfin c3 ztbgo (.ifLtN_true h1 ztdyd) rfl rfl rfl rfl ?_ by_omega
        grind
      · by_cases h2 : c3.nreg 130554 < c3.nreg 130555
        · refine hfin c3 (0 + 1 + 2) (.ifLtN_false h1 ztzrw) rfl rfl rfl
            rfl ?_ by_omega
          grind
        · have e4 := Exec.storeN (P := P) hw3 130556 130001
          refine hfin _ (1 + 2 + 2) (.ifLtN_false h1 (.ifLtN_false h2 e4)) rfl rfl rfl rfl ?_
            by_omega
          show upd c3.nmem (c3.nreg 130556) (c3.nreg 130001) = _
          rw [hm3, h3a, hone3, ite_eq_left by_omega]
          simp)
  refine ⟨c', 1 + k, .seq e0 e, by_omega, hw', (hf1.trans hf').mono ztng
    ztjwr,
    fun i hi => hI' i ztbg hi⟩
end proofs
end
end Chazelle.Core.Cluster
section
set_option hygiene false
local macro "zqbbf" : tactic => `(tactic| obtain ⟨j', rfl⟩ : ztieq := ⟨j - 1, by_omega⟩)
local macro "zqbbg" : tactic => `(tactic| (zumwj; unfold LbRG at hr; grind))
local macro "zqbbh" : tactic => `(tactic| (rw [ite_eq_right ztgr]))
set_option hygiene true

/-!
# WP-I, part 17: lower-bound search on the RAM

`lbStmt`: in a segment `[lo, hi)` of the item array `ACT` whose keys
`κ i = FPRE[FIRST[ACT[i]]]` are sorted, find the partition point of `κ i < key` by binary
lifting over the table `POW` of powers of two (`POW[j] = 2^j` for `j < LP`, `hi - lo < 2^LP`).
`lbStmt_exec`: at most `17 LP + 4` steps; the result `pos` has all keys before it below `key`
and none from it on (`LbInv.final`).

Registers: `130009` the constant `0`; `130300` `lo`, `130301` `hi`, `130310` `key`; output
`130311` `pos`; scratch `130312 … 130316`; bases `130320` (`ACT`), `130321` (`FIRST`),
`130322` (`FPRE`), `130323` (`POW`), `130324` `LP`.
-/
namespace Chazelle.Core.Cluster
open Machine Machine.Stmt Programs
@[expose] public section
def lbProbe : Stmt := .seq (block [.addN 130314 130320 130316, .subN 130314 130314 130001,
    .loadN 130315 130314, .addN 130314 130321 130315, .loadN 130315 130314,
    .addN 130314 130322 130315, .loadN 130315 130314])
  (.ifLtN 130315 130310 (.instr (.copyN 130311 130316)) .skip)

/-- One level of the search: `j := j - 1`, `p := 2^j`, probe if `pos + p ≤ hi`. -/
def lbBody : Stmt := .seq (block [.subN 130312 130312 130001, .addN 130314 130323 130312,
    .loadN 130313 130314, .addN 130316 130311 130313])
  (.ifLtN 130301 130316 .skip lbProbe)

/-- **The lower-bound search.** -/
def lbStmt : Stmt := .seq ztkrq
  (.whileLtN 130009 130312 lbBody)

/-- The registers written by the search. -/
def LbRG (r : ℕ) : Prop := 130311 ≤ r ∧ r ≤ 130316

/-- The key of position `i`. -/
def keyOf (m : ℕ → ℕ) (bACT bFIRST bFPRE i : ℕ) : ℕ := m (bFPRE + m ztzkk)
section proofs
variable {P : Polygon} {W : ℕ}

/-- The registers read by the search. -/
structure LbRegs (c : Config) (lo hi key bACT bFIRST bFPRE bPOW LP : ℕ) : Prop where
  one : c.nreg 130001 = 1
  zero : c.nreg 130009 = 0
  rlo : c.nreg 130300 = lo
  rhi : c.nreg 130301 = hi
  rkey : c.nreg 130310 = key
  rACT : c.nreg 130320 = bACT
  rFIRST : c.nreg 130321 = bFIRST
  rFPRE : c.nreg 130322 = bFPRE
  rPOW : c.nreg 130323 = bPOW
  rLP : c.nreg 130324 = LP
variable {c c' : Config}
theorem LbRegs.of_frame {lo hi key bACT bFIRST bFPRE bPOW LP : ℕ}
    (h : LbRegs c lo hi key bACT bFIRST bFPRE bPOW LP)
    (hr : ∀ r, ¬ LbRG r → c'.nreg r = c.nreg r) : LbRegs c' lo hi key bACT bFIRST bFPRE bPOW LP := by
  zucbi
  refine ztbbh <;> (rw [hr _ ztjqy]; assumption)

/-- **One level of the search.** -/
theorem lbBody_exec {c : Config} (hw : WordsBounded W c) {lo hi key bACT bFIRST bFPRE bPOW LP : ℕ}
    (hR : LbRegs c lo hi key bACT bFIRST bFPRE bPOW LP)
    (hs : Sorted ztcvz lo hi) {pos j : ℕ}
    (hpos : c.nreg 130311 = pos) (hj : c.nreg 130312 = j + 1) (hjL : j < LP)
    (hpow : c.nmem zthds = 2 ^ j) (hI : LbInv ztcvz lo hi key pos ztl)
    (hwpow : bPOW + LP ≤ W) (hwact : bACT + hi ≤ W) (hw2 : hi + 2 ^ j ≤ W)
    (hwf : ∀ i, lo ≤ i → i < hi → bFIRST + c.nmem ztdgm ≤ W ∧
      bFPRE + c.nmem ztyeb ≤ W) :
    ∃ c' k, Exec P W lbBody c c' k ∧ k ≤ 15 ∧ c'.nmem = c.nmem ∧
      ztedl ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧ c'.nreg 130312 = j ∧
      ∃ pos', c'.nreg 130311 = pos' ∧ LbInv ztcvz lo hi key pos' j := by
  have hle := hI.le_hi
  have hlo := hI.lo_le
  obtain ⟨hstep1, hstep2⟩ := LbInv.step hs hI
  have hp1 := Nat.one_le_two_pow (n := j)
  -- load the power and form `pos + 2^j`
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, hj1, hpos1, ht1, hr1, hrr1, hrm1, ho1⟩ : ∃ c1 k1,
      Exec P W (block [.subN 130312 130312 130001, .addN 130314 130323 130312,
        .loadN 130313 130314, .addN 130316 130311 130313]) c c1 k1 ∧ k1 = 4 ∧ WordsBounded W c1 ∧
      c1.nmem = c.nmem ∧ c1.nreg 130312 = j ∧ c1.nreg 130311 = pos ∧
      c1.nreg 130316 = pos + 2 ^ j ∧ ztivq ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    · config_simp; rw [hR.rPOW, hj, hR.one]; omega
    · config_simp; zunbp; omega
    · refine ⟨rfl, by_omega, rfl, by config_simp; rw [hj, hR.one]; omega, by_tauto, ?_,
        fun r hr => ?_, rfl, rfl, rfl⟩
      · config_simp; zunbp
      · zqbbg
  zuliy
  by_cases hbig : hi < pos + 2 ^ j
  · -- out of range: skip
    zultc
    refine ⟨c1, 4 + ztbgo, .seq e1 (.ifLtN_true ztfpl
      ztdbq), by_omega, hm1, hr1, hrr1, hrm1, ho1, hj1, pos, hpos1, ?_⟩
    simp_all
  · -- probe the key at `pos + 2^j - 1`
    have hin : lo ≤ pos + 2 ^ j - 1 ∧ pos + 2 ^ j - 1 < hi := by_omega
    obtain ⟨hwa, hwb⟩ := hwf _ hin.1 hin.2
    rw [← hm1] at hwa hwb
    obtain ⟨c2, k2, e2, hk2', hw2', hm2, hk2, hr2, hrr2, hrm2, ho2⟩ : ∃ c2 k2,
        Exec P W (block [.addN 130314 130320 130316, .subN 130314 130314 130001,
          .loadN 130315 130314, .addN 130314 130321 130315, .loadN 130315 130314,
          .addN 130314 130322 130315, .loadN 130315 130314]) c1 c2 k2 ∧ k2 = 7 ∧
        WordsBounded W c2 ∧
        c2.nmem = c1.nmem ∧
        c2.nreg 130315 = keyOf c1.nmem bACT bFIRST bFPRE _ ∧
        (∀ r, r ≠ 130314 → r ≠ 130315 → c2.nreg r = c1.nreg r) ∧ c2.rreg = c1.rreg ∧
        c2.rmem = c1.rmem ∧ c2.output = c1.output := by
      exec_block
      · rw [hR1.rACT, ht1]; omega
      · config_simp; rw [hR1.rFIRST, hR1.rACT, ht1, hR1.one,
          show bACT + ztgli - 1 = bACT + ztbjr by omega]; omega
      · config_simp; rw [hR1.rFPRE, hR1.rFIRST, hR1.rACT, ht1, hR1.one,
          show bACT + ztgli - 1 = bACT + ztbjr by omega]; omega
      · refine ⟨rfl, by_omega, rfl, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
        · config_simp; rw [hR1.rFPRE, hR1.rFIRST, hR1.rACT, ht1, hR1.one,
            show bACT + ztgli - 1 = bACT + ztbjr by omega]; rfl
        · zughc
    subst hk1 hk2'
    have hkey2 : c2.nreg 130310 = key := by rw [hr2 _ by_decide by_decide]; exact hR1.rkey
    have hkk : c2.nreg 130315 = keyOf c.nmem bACT bFIRST bFPRE ztbjr := by
      grind
    have hframe : ∀ c3 : Config, (∀ r, ¬ LbRG r → c3.nreg r = c2.nreg r) →
        ∀ r, ¬ LbRG r → c3.nreg r = c.nreg r := by
      zulmn
      rw [h3 r hr, hr2 r ztijm
        ztijm, hr1 r hr]
    by_cases hlt : keyOf c.nmem bACT bFIRST bFPRE ztbjr < key
    · have e3 := Exec.copyN (P := P) hw2' 130311 130316
      refine ⟨_, 4 + ((7 + ztcse) + 2), .seq e1 (.ifLtN_false ztfpl
        ztnci), by_omega, ?_, ?_, ?_, ?_,
        ?_, ?_, pos + 2 ^ j, ?_, by_grind⟩
      · grind
      · refine hframe _ ztez
        zqbbg
      · grind
      · grind
      · grind
      · zudi
        grind
      · zuvz
        grind
    · refine ⟨c2, 4 + ((7 + ztdeu) + 2), .seq e1 (.ifLtN_false ztfpl
        (.seq e2 (.ifLtN_false by_omega (.skip hw2')))), by_omega,
        hm2.trans hm1, by_grind, hrr2.trans hrr1, hrm2.trans hrm1,
        ho2.trans ho1, by_grind, pos,
        by grind, by_grind⟩

/-- **The lower-bound search.**  At the end `pos` (register `130311`) is the partition point of
the sorted keys of `[lo, hi)` for `key`; only the scratch registers change. -/
theorem lbStmt_exec {c : Config} (hw : WordsBounded W c) {lo hi key bACT bFIRST bFPRE bPOW LP : ℕ}
    (hR : LbRegs c lo hi key bACT bFIRST bFPRE bPOW LP)
    (hs : Sorted ztcvz lo hi) (hlh : lo ≤ hi)
    (hpow : ∀ j, j < LP → c.nmem zthds = 2 ^ j) (hLP : hi - lo < 2 ^ LP)
    (hwpow : bPOW + LP ≤ W) (hwact : bACT + hi ≤ W) (hw2 : hi + 2 ^ LP ≤ W)
    (hwf : ∀ i, lo ≤ i → i < hi → bFIRST + c.nmem ztdgm ≤ W ∧
      bFPRE + c.nmem ztyeb ≤ W) :
    ∃ c' k, Exec P W lbStmt c c' k ∧ k ≤ 17 * LP + 4 ∧ c'.nmem = c.nmem ∧
      ztedl ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧ lo ≤ c'.nreg 130311 ∧ c'.nreg 130311 ≤ hi ∧
      (∀ i, lo ≤ i → i < c'.nreg 130311 → keyOf c.nmem bACT bFIRST bFPRE i < key) ∧
      (∀ i, c'.nreg 130311 ≤ i → i < hi → key ≤ keyOf c.nmem bACT bFIRST bFPRE i) := by
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, hj1, hpos1, hr1, hrr1, hrm1, ho1⟩ : ∃ c1 k1,
      Exec P W ztkrq c c1 k1 ∧ k1 = 2 ∧
      WordsBounded W c1 ∧ c1.nmem = c.nmem ∧ c1.nreg 130312 = LP ∧ c1.nreg 130311 = lo ∧
      ztivq ∧ c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧
      c1.output = c.output := by
    exec_block
    refine ⟨rfl, by_omega, rfl, by config_simp; exact hR.rLP, by config_simp; exact hR.rlo,
      fun r hr => ?_, rfl, rfl, rfl⟩
    zqbbg
  obtain ⟨c', k, e, ⟨hw', hm', hr', hrr', hrm', ho', j, pos, hj, hpos, hjL, hI⟩, htest, hk⟩ :=
    Exec.whileLtN_potential (P := P) (W := W) (a := 130009) (b := 130312) (body := lbBody)
    (fun c' => WordsBounded W c' ∧ c'.nmem = c.nmem ∧ ztedl ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      ∃ j pos, c'.nreg 130312 = j ∧ c'.nreg 130311 = pos ∧ j ≤ LP ∧
        LbInv ztcvz lo hi key pos j)
    (fun c' => 17 * c'.nreg 130312) ztbms
    (fun c2 ⟨hw2', hm2, hr2, hrr2, hrm2, ho2, j, pos, hj, hpos, hjL, hI⟩ htest => by
      have hR2 := hR.of_frame hr2
      rw [hR2.zero, hj] at htest
      zqbbf
      have hs2 : Sorted ztqsl lo hi := by_simp_all
      have hI2 : LbInv ztqsl lo hi key pos ztdhr := by
        simp_all
      have hpow2 : c2.nmem (bPOW + j') = 2 ^ j' := by_simp_all
      have hp : 2 ^ j' ≤ 2 ^ LP := Nat.pow_le_pow_right by_norm_num by_omega
      obtain ⟨c3, k3, e3, hk3, hm3, hr3, hrr3, hrm3, ho3, hj3, pos', hpos3, hI3⟩ :=
        lbBody_exec (P := P) hw2' hR2 hs2 hpos hj by_omega hpow2 hI2 hwpow hwact by_omega
          ztfhi
      refine ⟨c3, k3, e3, ⟨e3.wb_right, hm3.trans hm2, by_simp_all,
        hrr3.trans hrr2, hrm3.trans hrm2, ho3.trans ho2, j', pos', hj3, hpos3, by_omega,
        by simp_all⟩, ?_⟩
      omega)
    ⟨hw1, hm1, hr1, hrr1, hrm1, ho1, LP, lo, hj1, hpos1, le_rfl, LbInv.init hlh hLP⟩
  have hR' := hR.of_frame hr'
  rw [hR'.zero, hj] at htest
  zubkk

  obtain ⟨fin1, fin2⟩ := LbInv.final hs hI
  refine ⟨c', k1 + k, .seq e1 e, by_omega, hm', hr', hrr', hrm', ho',
    by zvnbl; exact hI.lo_le, by zvnbl; exact hI.le_hi, by_simp_all,
    by simp_all⟩

/-! ## The good test -/

/-- `key := FPRE[z]`. -/
def goodPre1 : Stmt := block [.addN 130333 130322 130330, .loadN 130310 130333]

/-- Save the first count, `key := FPRE[z] + FSZ[z]`. -/
def goodPre2 : Stmt := block [.copyN 130332 130311, .addN 130333 130325 130330,
  .loadN 130334 130333, .addN 130310 130310 130334]

/-- `2 cnt` and the comparison with `W`. -/
def goodFin : Stmt := .seq ztira
  (.ifLtN 130302 130334 (.instr (.constN 130331 1)) (.instr (.constN 130331 0)))

/-- **The good test** of the face in `130330`: `130331 := 1` iff more than half of the segment
has its key in the preorder interval of the face. -/
def goodStmt : Stmt := .seq goodPre1 (.seq lbStmt (.seq goodPre2 (.seq lbStmt goodFin)))

/-- The registers written by the good test. -/
def GoodRG (r : ℕ) : Prop := 130310 ≤ r ∧ r ≤ 130316 ∨ 130331 ≤ r ∧ r ≤ 130334

/-- The keys of `[lo, hi)` in the half-open interval `[a, b)`. -/
def cntIn (κ : ℕ → ℕ) (lo hi a b : ℕ) : ℕ :=
  ((Finset.Ico lo hi).filter ztisr).card

/-- Counting a key interval with two partition points. -/
theorem cntIn_eq {κ : ℕ → ℕ} {lo hi a b p1 p2 : ℕ} (_hab : a ≤ b)
    (h1 : lo ≤ p1 ∧ p1 ≤ hi) (h2 : lo ≤ p2 ∧ p2 ≤ hi)
    (b1 : ∀ i, lo ≤ i → i < p1 → κ i < a) (a1 : ∀ i, p1 ≤ i → i < hi → a ≤ κ i)
    (b2 : ∀ i, lo ≤ i → i < p2 → κ i < b) (a2 : ∀ i, p2 ≤ i → i < hi → b ≤ κ i) :
    cntIn κ lo hi a b = p2 - p1 := by
  zuluh
  have : (Finset.Ico lo hi).filter ztisr = Finset.Ico p1 p2 := by
    grind
  simp_all

/-- The registers read by the good test. -/
structure GoodRegs (c : Config) (lo hi z bACT bFIRST bFPRE bPOW LP bFSZ : ℕ) : Prop where
  one : c.nreg 130001 = 1
  zero : c.nreg 130009 = 0
  rlo : c.nreg 130300 = lo
  rhi : c.nreg 130301 = hi
  rACT : c.nreg 130320 = bACT
  rFIRST : c.nreg 130321 = bFIRST
  rFPRE : c.nreg 130322 = bFPRE
  rPOW : c.nreg 130323 = bPOW
  rLP : c.nreg 130324 = LP
  rW : c.nreg 130302 = hi - lo
  rz : c.nreg 130330 = z
  rFSZ : c.nreg 130325 = bFSZ
theorem GoodRegs.lb {c : Config} {lo hi z bACT bFIRST bFPRE bPOW LP bFSZ : ℕ}
    (h : GoodRegs c lo hi z bACT bFIRST bFPRE bPOW LP bFSZ) :
    LbRegs c lo hi (c.nreg 130310) bACT bFIRST bFPRE bPOW LP :=
  ⟨h.one, h.zero, h.rlo, h.rhi, rfl, h.rACT, h.rFIRST, h.rFPRE, h.rPOW, h.rLP⟩
theorem GoodRegs.of_frame {lo hi z bACT bFIRST bFPRE bPOW LP bFSZ : ℕ}
    (h : GoodRegs c lo hi z bACT bFIRST bFPRE bPOW LP bFSZ)
    (hr : ∀ r, ¬ GoodRG r → c'.nreg r = c.nreg r) :
    GoodRegs c' lo hi z bACT bFIRST bFPRE bPOW LP bFSZ := by
  zuboz
  refine ztexk <;>
    (rw [hr _ ztcum]; assumption)

/-- **The good test.** -/
theorem goodStmt_exec {c : Config} (hw : WordsBounded W c)
    {lo hi z bACT bFIRST bFPRE bPOW LP bFSZ : ℕ}
    (hR : GoodRegs c lo hi z bACT bFIRST bFPRE bPOW LP bFSZ)
    (hs : Sorted ztcvz lo hi) (hlh : lo ≤ hi)
    (hpow : ∀ j, j < LP → c.nmem zthds = 2 ^ j) (hLP : hi - lo < 2 ^ LP)
    (hwpow : bPOW + LP ≤ W) (hwact : bACT + hi ≤ W) (hw2 : hi + 2 ^ LP ≤ W)
    (hwf : ∀ i, lo ≤ i → i < hi → bFIRST + c.nmem ztdgm ≤ W ∧
      bFPRE + c.nmem ztyeb ≤ W)
    (hwz : bFPRE + z ≤ W ∧ bFSZ + z ≤ W ∧ c.nmem ztdgn + c.nmem zthdp ≤ W)
    (hwh : 2 * hi ≤ W) :
    ∃ c' k, Exec P W goodStmt c c' k ∧ k ≤ 34 * LP + 25 ∧ c'.nmem = c.nmem ∧
      ztivp ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧ c'.nreg 130331 ≤ 1 ∧
      (c'.nreg 130331 = 1 ↔ hi - lo < 2 * cntIn ztcvz lo hi
        (c.nmem ztdgn) (c.nmem ztdgn + c.nmem zthdp)) := by
  obtain ⟨hwz1, hwz2, hwz3⟩ := hwz
  -- key := FPRE[z]
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, hkey1, hr1, hrr1, hrm1, ho1⟩ : ∃ c1 k1,
      Exec P W goodPre1 c c1 k1 ∧ k1 = 2 ∧ WordsBounded W c1 ∧ c1.nmem = c.nmem ∧
      c1.nreg 130310 = c.nmem ztdgn ∧ (∀ r, r ≠ 130333 → r ≠ 130310 → c1.nreg r = c.nreg r) ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    unfold goodPre1
    exec_block
    · zuoic; omega
    · refine ⟨rfl, by_omega, rfl, by config_simp; zuoic, fun r h1 h2 => ?_, rfl, rfl,
        rfl⟩
      simp_all
  have hR1 :=
    hR.of_frame (fun r hr => hr1 r ztgs
      ztgs)
  have hL1 := hR1.lb
  rw [hkey1] at hL1
  obtain ⟨c2, k2, e2, hk2, hm2, hr2, hrr2, hrm2, ho2, hp1a, hp1b, hb1, ha1⟩ :=
    lbStmt_exec (P := P) hw1 hL1 by_simp_all hlh by_simp_all hLP hwpow
      hwact hw2 by_simp_all
  zvmxz at hb1 ha1
  have hR2 :=
    hR1.of_frame (fun r hr => hr2 r (fun h => hr (Or.inl ⟨by unfold LbRG at h; omega,
      by unfold LbRG at h; omega⟩)))
  have hkey2 : c2.nreg 130310 = c.nmem ztdgn := by rw [hr2 _ ztjqy, hkey1]
  set p1 := c2.nreg 130311
  have hw2' := e2.wb_right
  -- save `p1`, key := FPRE[z] + FSZ[z]
  obtain ⟨c3, k3, e3, hk3, hw3, hm3, hs3, hkey3, hr3, hrr3, hrm3, ho3⟩ : ∃ c3 k3,
      Exec P W goodPre2 c2 c3 k3 ∧ k3 = 4 ∧ WordsBounded W c3 ∧ c3.nmem = c.nmem ∧
      c3.nreg 130332 = p1 ∧ c3.nreg 130310 = c.nmem ztdgn + c.nmem zthdp ∧
      (∀ r, r ≠ 130332 → r ≠ 130333 → r ≠ 130334 → r ≠ 130310 → c3.nreg r = c2.nreg r) ∧
      c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output := by
    unfold goodPre2
    exec_block
    · config_simp; rw [hR2.rFSZ, hR2.rz]; omega
    · config_simp; zunlq; omega
    · refine ⟨rfl, by_omega, by_simp_all, by_rfl, ?_, fun r h1 h2 h3 h4 => ?_, rfl,
        rfl, rfl⟩
      · config_simp; zunlq
      simp_all
  have hR3 :=
    hR2.of_frame (fun r hr => hr3 r ztgs
      ztgs ztgs
      ztgs)
  have hL3 := hR3.lb
  rw [hkey3] at hL3
  obtain ⟨c4, k4, e4, hk4, hm4, hr4, hrr4, hrm4, ho4, hp2a, hp2b, hb2, ha2⟩ :=
    lbStmt_exec (P := P) hw3 hL3 by_simp_all hlh by_simp_all hLP hwpow
      hwact hw2 by_grind
  rw [hm3] at hb2 ha2
  have hs4 : c4.nreg 130332 = p1 := by rw [hr4 _ ztjqy, hs3]
  have hR4 :=
    hR3.of_frame (fun r hr => hr4 r (fun h => hr (Or.inl ⟨by unfold LbRG at h; omega,
      by unfold LbRG at h; omega⟩)))
  set p2 := c4.nreg 130311
  zubgi
  have hcnt : cntIn _ lo hi _
      _ = p2 - p1 :=
    cntIn_eq by_omega by_omega by_omega hb1 ha1 hb2 ha2
  -- the comparison
  obtain ⟨c5, k5, e5, hk5, hw5, hm5, hd5, hr5, hrr5, hrm5, ho5⟩ : ∃ c5 k5,
      Exec P W ztira c4 c5 k5 ∧
      k5 = 2 ∧ WordsBounded W c5 ∧ c5.nmem = c4.nmem ∧ c5.nreg 130334 = 2 * (p2 - p1) ∧
      (∀ r, r ≠ 130334 → c5.nreg r = c4.nreg r) ∧ c5.rreg = c4.rreg ∧ c5.rmem = c4.rmem ∧
      c5.output = c4.output := by
    exec_block
    · config_simp; omega
    · refine ⟨rfl, by_omega, rfl, by config_simp; omega, fun r h1 => ?_, rfl, rfl, rfl⟩
      simp only [Machine.upd_apply, h1, ite_false]
  have hW5 : c5.nreg 130302 = hi - lo := by
    rw [hr5 _ by_decide]; exact hR4.rW
  have hframe : ∀ c6 : Config, (∀ r, r ≠ 130331 → c6.nreg r = c5.nreg r) →
      ∀ r, ¬ GoodRG r → c6.nreg r = c.nreg r := by
    intro c6 h6 r hr
    have n1 : ¬ LbRG r := fun h => hr (Or.inl ⟨by unfold LbRG at h; omega, by unfold LbRG at h; omega⟩)
    rw [h6 r ztgs,
      hr5 r ztgs, hr4 r n1,
      hr3 r ztgs ztgs
        ztgs ztgs,
      hr2 r n1, hr1 r ztgs
        ztgs]
  zumqc
  by_cases hgood : c5.nreg 130302 < c5.nreg 130334
  · have e6 := Exec.constN (P := P) hw5 130331 1 by_omega
    refine ⟨_, 2 + (k2 + (4 + (k4 + (2 + ztcse)))), .seq e1 (.seq e2 (.seq e3 (.seq e4
      (.seq e5 (.ifLtN_true hgood e6))))), by_omega, ?_, hframe _ (fun r hr => by zumwy),
      by grind, by_grind,
      by grind, by_simp, ?_⟩
    · grind
    · zuoco
      omega
  · have e6 := Exec.constN (P := P) hw5 130331 0 by_omega
    refine ⟨_, 2 + (k2 + (4 + (k4 + (2 + ztgxh)))), .seq e1 (.seq e2 (.seq e3 (.seq e4
      (.seq e5 (.ifLtN_false hgood e6))))), by_omega, ?_, hframe _ (fun r hr => by zumwy),
      by grind, by_grind,
      by grind, by_simp, ?_⟩
    · grind
    · simp only [Machine.upd_same, zero_ne_one, false_iff]
      omega

/-! ## The climb -/

/-- One level of the climb: `j := j - 1`, `base := base - N`, `z := UP_j[x]`, move if bad. -/
def climbBody : Stmt := .seq (block [.subN 130342 130342 130001, .subN 130343 130343 130328,
    .addN 130333 130343 130341, .loadN 130330 130333])
  (.seq goodStmt (.ifLtN 130331 130001 (.instr (.copyN 130341 130330)) .skip))

/-- The climb loop and the final parent step `f := UP_0[x]`. -/
def climbLoop : Stmt := .seq (block [.copyN 130341 130340, .copyN 130342 130345,
    .copyN 130343 130327])
  (.seq (.whileLtN 130009 130342 climbBody) (block [.addN 130333 130326 130341,
    .loadN 130344 130333]))

/-- **The climb** from `y` (register `130340`) to the centroid `f` (register `130344`). -/
def climbStmt : Stmt := .seq (.instr (.copyN 130330 130340))
  (.seq goodStmt (.ifLtN 130331 130001 climbLoop (.instr (.copyN 130344 130340))))

/-- The registers written by the climb. -/
def ClimbRG (r : ℕ) : Prop := GoodRG r ∨ r = 130330 ∨ ztneg

/-- The good predicate of the segment `[lo, hi)`. -/
def GdF (m : ℕ → ℕ) (bACT bFIRST bFPRE bFSZ lo hi z : ℕ) : Prop :=
  hi - lo < 2 * cntIn ztqsm lo hi (m ztdgn) (m ztdgn + m zthdp)

/-- The static hypotheses of the good test and the climb (everything but the tested face). -/
structure ClimbCtx (c : Config) (lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N : ℕ) : Prop where
  one : c.nreg 130001 = 1
  zero : c.nreg 130009 = 0
  rlo : c.nreg 130300 = lo
  rhi : c.nreg 130301 = hi
  rACT : c.nreg 130320 = bACT
  rFIRST : c.nreg 130321 = bFIRST
  rFPRE : c.nreg 130322 = bFPRE
  rPOW : c.nreg 130323 = bPOW
  rLP : c.nreg 130324 = LP
  rW : c.nreg 130302 = hi - lo
  rFSZ : c.nreg 130325 = bFSZ
  rUP : c.nreg 130326 = bUP
  rUPE : c.nreg 130327 = bUP + L * N
  rN : c.nreg 130328 = N
  rL : c.nreg 130345 = L
theorem ClimbCtx.of_frame {lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N : ℕ}
    (h : ClimbCtx c lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N)
    (hr : ∀ r, ¬ ClimbRG r → c'.nreg r = c.nreg r) :
    ClimbCtx c' lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N := by
  zubct
  refine ztcl <;>
    (rw [hr _ ztiis]; assumption)
theorem ClimbCtx.good {c : Config} {lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N z : ℕ}
    (h : ClimbCtx c lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N) (hz : c.nreg 130330 = z) :
    GoodRegs c lo hi z bACT bFIRST bFPRE bPOW LP bFSZ :=
  ⟨h.one, h.zero, h.rlo, h.rhi, h.rACT, h.rFIRST, h.rFPRE, h.rPOW, h.rLP, h.rW, hz, h.rFSZ⟩

/-- The static memory hypotheses of the climb. -/
structure ClimbMem (m : ℕ → ℕ) (W lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N : ℕ)
    (up : ℕ → ℕ) : Prop where
  sorted : Sorted ztqsm lo hi
  lh : lo ≤ hi
  pow : ∀ j, j < LP → m zthds = 2 ^ j
  hLP : hi - lo < 2 ^ LP
  wpow : bPOW + LP ≤ W
  wact : bACT + hi ≤ W
  w2 : hi + 2 ^ LP ≤ W
  wf : ∀ i, lo ≤ i → i < hi → bFIRST + m ztdgm ≤ W ∧
    bFPRE + m ztzkk ≤ W
  wz : ∀ z, z < N → bFPRE + z ≤ W ∧ bFSZ + z ≤ W ∧ m ztdgn + m zthdp ≤ W
  wh : 2 * hi ≤ W
  up_lt : ∀ g, g < N → up g < N
  tab : ∀ j, j < L → ∀ g, g < N → m (bUP + j * N + g) = up^[2 ^ j] g
  wup : bUP + L * N ≤ W

/-- The good test in the climb context. -/
theorem good_in_ctx {c : Config} (hw : WordsBounded W c)
    {lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N : ℕ} {up : ℕ → ℕ}
    (hC : ClimbCtx c lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N)
    (hM : ClimbMem c.nmem W lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N up) {z : ℕ}
    (hz : c.nreg 130330 = z) (hzN : z < N) :
    ∃ c' k, Exec P W goodStmt c c' k ∧ k ≤ 34 * LP + 25 ∧ c'.nmem = c.nmem ∧
      ztivp ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧ c'.nreg 130331 ≤ 1 ∧
      (c'.nreg 130331 = 1 ↔ GdF c.nmem bACT bFIRST bFPRE bFSZ lo hi z) :=
  goodStmt_exec hw (hC.good hz) hM.sorted hM.lh hM.pow hM.hLP hM.wpow hM.wact hM.w2 hM.wf
    (hM.wz z hzN) hM.wh

/-- **One level of the climb.** -/
theorem climbBody_exec {c : Config} (hw : WordsBounded W c)
    {lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N : ℕ} {up : ℕ → ℕ}
    (hC : ClimbCtx c lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N)
    (hM : ClimbMem c.nmem W lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N up) {x j y : ℕ}
    (hx : c.nreg 130341 = x) (hj : c.nreg 130342 = j + 1) (hjL : j < L)
    (hb : c.nreg 130343 = bUP + ztl * N) (hxN : x < N)
    (hI : ClimbInv up ztgdx x ztl)
    (hanc : ∃ n, up^[n] y = x) :
    ∃ c' k, Exec P W climbBody c c' k ∧ k ≤ 34 * LP + 32 ∧ c'.nmem = c.nmem ∧
      ztivm ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧ c'.nreg 130342 = j ∧ c'.nreg 130343 = bUP + j * N ∧
      ∃ x', c'.nreg 130341 = x' ∧ x' < N ∧
        ClimbInv up ztgdx x' j ∧ ∃ n, up^[n] y = x' := by
  obtain ⟨hs1, hs2⟩ := hI.step
  have hzN : up^[2 ^ j] x < N := by
    have : zthoy := by
      intro n; induction n with
      | zero => intro g hg; exact hg
      | succ n ih => intro g hg; rw [Function.iterate_succ_apply]; exact ih _ (hM.up_lt g hg)
    simp_all
  have htab := hM.tab j hjL x hxN
  have hjN : bUP + j * N + x ≤ W := by
    have : j * N + x < L * N := by
      calc j * N + x < j * N + N := by_omega
        _ = ztl * N := by_ring
        _ ≤ L * N := Nat.mul_le_mul_right _ hjL
    have := hM.wup; omega
  -- load `z := UP_j[x]`
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, hj1, hb1, hz1, hr1, hrr1, hrm1, ho1⟩ : ∃ c1 k1,
      Exec P W (block [.subN 130342 130342 130001, .subN 130343 130343 130328,
        .addN 130333 130343 130341, .loadN 130330 130333]) c c1 k1 ∧ k1 = 4 ∧
      WordsBounded W c1 ∧ c1.nmem = c.nmem ∧ c1.nreg 130342 = j ∧
      c1.nreg 130343 = bUP + j * N ∧ c1.nreg 130330 = up^[2 ^ j] x ∧
      (∀ r, r ≠ 130342 → r ≠ 130343 → r ≠ 130333 → r ≠ 130330 → c1.nreg r = c.nreg r) ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    have hbj : bUP + ztl * N - N = bUP + j * N := by
      grind
    exec_block
    · config_simp; rw [hb, hC.rN, hx, hbj]; omega
    · refine ⟨rfl, by_omega, rfl, by config_simp; rw [hj, hC.one]; omega,
        by config_simp; rw [hb, hC.rN, hbj], ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl⟩
      · config_simp; rw [hb, hC.rN, hx, hbj, htab]
      · zueeo
  have hC1 :=
    hC.of_frame (fun r hr => hr1 r ztgr
      ztgr
      ztcvi
      ztgr)
  have hM1 : ClimbMem c1.nmem W lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N up := by
    simp_all
  obtain ⟨c2, k2, e2, hk2, hm2, hr2, hrr2, hrm2, ho2, hle2, hg2⟩ :=
    good_in_ctx (P := P) hw1 hC1 hM1 hz1 hzN
  zvmxz at hg2
  have hone2 : zthoo := by rw [hr2 _ ztcum]; exact hC1.one
  have hx2 : c2.nreg 130341 = x := by
    rw [hr2 _ ztcum, hr1 _ by_decide by_decide by_decide by_decide, hx]
  have hz2 : c2.nreg 130330 = up^[2 ^ j] x := by
    rw [hr2 _ ztcum, hz1]
  have hframe : ∀ c3 : Config, (∀ r, r ≠ 130341 → c3.nreg r = c2.nreg r) →
      ∀ r, ¬ ClimbRG r → c3.nreg r = c.nreg r := by
    zulmn
    rw [h3 r ztgr,
      hr2 r ztwnm,
      hr1 r ztgr
        ztgr
        ztcvi
        ztgr]
  have hj2 : c2.nreg 130342 = j := by rw [hr2 _ ztcum, hj1]
  have hb2 : c2.nreg 130343 = bUP + j * N := by rw [hr2 _ ztcum, hb1]
  obtain ⟨n, hn⟩ := hanc
  zultc
  by_cases hbad : c2.nreg 130331 < c2.nreg 130001
  · -- not good: move
    have hng : ¬ GdF c.nmem bACT bFIRST bFPRE bFSZ lo hi ztceb := by
      grind
    have e3 := Exec.copyN (P := P) e2.wb_right 130341 130330
    refine ⟨_, 4 + (k2 + ztcse), .seq e1 (.seq e2 (.ifLtN_true hbad e3)), by_omega,
      by grind, hframe _ ztlou, by_grind,
      by grind, by_grind, by simp [hj2], by simp [hb2],
      up^[2 ^ j] x, by simp [hz2], hzN, hs1 hng, 2 ^ j + n, ?_⟩
    rw [Function.iterate_add_apply, hn]
  · have hgd : GdF c.nmem bACT bFIRST bFPRE bFSZ lo hi ztceb := by
      grind
    refine ⟨c2, 4 + (k2 + ztdeu), .seq e1 (.seq e2 (.ifLtN_false hbad (.skip e2.wb_right))),
      by omega, by_grind, by_grind, by_grind,
      by grind, by_grind, hj2, hb2, x, hx2, hxN, hs2 hgd, n, hn⟩

/-- **The climb**: from `y < N` (register `130340`), the face `f` in register `130344` is `y` if
`y` is good, and otherwise the parent of an ancestor `x` of `y` that is not good while its parent
is.  Needs the `2^L`-th ancestor of `y` to be good. -/
theorem climbStmt_exec {c : Config} (hw : WordsBounded W c)
    {lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N : ℕ} {up : ℕ → ℕ}
    (hC : ClimbCtx c lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N)
    (hM : ClimbMem c.nmem W lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N up) {y : ℕ}
    (hy : c.nreg 130340 = y) (hyN : y < N) (hL : 0 < L)
    (hroot : GdF c.nmem bACT bFIRST bFPRE bFSZ lo hi (up^[2 ^ L] y)) :
    ∃ c' k, Exec P W climbStmt c c' k ∧ k ≤ ztelh * zttz + 10 ∧ c'.nmem = c.nmem ∧
      ztivm ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧ c'.nreg 130344 < N ∧
      ((GdF c.nmem bACT bFIRST bFPRE bFSZ lo hi y ∧ c'.nreg 130344 = y) ∨
        ∃ x n, up^[n] y = x ∧ ¬ GdF c.nmem bACT bFIRST bFPRE bFSZ lo hi x ∧
          GdF c.nmem bACT bFIRST bFPRE bFSZ lo hi ztwhb ∧ c'.nreg 130344 = up x) := by
  have e0 := Exec.copyN (P := P) hw 130330 130340
  set c0 := { c with nreg := upd c.nreg 130330 (c.nreg 130340) }
  have hC0 : ClimbCtx c0 lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N :=
    hC.of_frame (fun r hr => by
      zufbk
      rw [ite_eq_right (fun e => hr by_tauto)])
  have hz0 : c0.nreg 130330 = y := by_tauto
  obtain ⟨c1, k1, e1, hk1, hm1, hr1, hrr1, hrm1, ho1, hle1, hg1⟩ :=
    good_in_ctx (P := P) e0.wb_right hC0 by_omega hz0 hyN
  have hm1' := hm1
  rw [show c0.nmem = c.nmem from rfl] at hg1
  have hC1 :=
    hC0.of_frame (fun r hr => hr1 r ztwnm)
  have hy1 : c1.nreg 130340 = y := by
    rw [hr1 _ ztcum]; tauto
  have hframe1 : ∀ r, ¬ ClimbRG r → c1.nreg r = c.nreg r := by
    zuz
    rw [hr1 r ztwnm]
    zufbk
    zqbbh
  have hone1 := hC1.one
  have hup_lt : zthoy := by
    intro n; induction n with
    | zero => intro g hg; exact hg
    | succ n ih => intro g hg; rw [Function.iterate_succ_apply]; exact ih _ (hM.up_lt g hg)
  by_cases hbad : c1.nreg 130331 < c1.nreg 130001
  · -- `y` is not good: the loop
    have hng : ¬ GdF c.nmem bACT bFIRST bFPRE bFSZ lo hi y := by
      simp_all
    obtain ⟨c2, k2, e2, hk2, hw2, hm2, hx2, hj2, hb2, hr2, hrr2, hrm2, ho2⟩ : ∃ c2 k2,
        Exec P W (block [.copyN 130341 130340, .copyN 130342 130345, .copyN 130343 130327])
          c1 c2 k2 ∧ k2 = 3 ∧ WordsBounded W c2 ∧ c2.nmem = c1.nmem ∧ c2.nreg 130341 = y ∧
        c2.nreg 130342 = L ∧ c2.nreg 130343 = bUP + L * N ∧
        (∀ r, r ≠ 130341 → r ≠ 130342 → r ≠ 130343 → c2.nreg r = c1.nreg r) ∧
        c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧ c2.output = c1.output := by
      have := e1.wb_right
      exec_block
      refine ⟨rfl, by_omega, rfl, by_simp_all, by config_simp; exact hC1.rL,
        by config_simp; exact hC1.rUPE, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
      simp_all
    have hC2 :=
      hC1.of_frame (fun r hr => hr2 r ztgr
        ztgr
        ztgr)
    obtain ⟨c3, k3, e3, ⟨hw3, hm3, hr3, hrr3, hrm3, ho3, x, j, hx3, hj3, hb3, hxN, hjL, hI3,
        hanc3⟩, htest, hk3⟩ :=
      Exec.whileLtN_potential (P := P) (W := W) (a := 130009) (b := 130342) (body := climbBody)
      (fun c' => WordsBounded W c' ∧ c'.nmem = c.nmem ∧
        (∀ r, ¬ ClimbRG r → c'.nreg r = c2.nreg r) ∧ c'.rreg = c2.rreg ∧ c'.rmem = c2.rmem ∧
        c'.output = c2.output ∧ ∃ x j, c'.nreg 130341 = x ∧ c'.nreg 130342 = j ∧
          c'.nreg 130343 = bUP + j * N ∧ x < N ∧ j ≤ L ∧
          ClimbInv up ztgdx x j ∧ ∃ n, up^[n] y = x)
      (fun c' => ztelh * c'.nreg 130342) ztbms
      (fun c4 ⟨hw4, hm4, hr4, hrr4, hrm4, ho4, x, j, hx4, hj4, hb4, hxN4, hjL4, hI4, hanc4⟩
          htest => by
        have hC4 := hC2.of_frame hr4
        rw [hC4.zero, hj4] at htest
        zqbbf
        have hM4 : ClimbMem c4.nmem W lo hi bACT bFIRST bFPRE bPOW LP bFSZ bUP L N up := by
          grind
        rw [← hm4] at hI4
        obtain ⟨c5, k5, e5, hk5, hm5, hr5, hrr5, hrm5, ho5, hj5, hb5, x', hx5, hxN5, hI5, hanc5⟩ :=
          climbBody_exec (P := P) hw4 hC4 hM4 hx4 hj4 by_omega hb4 hxN4 hI4 hanc4
        rw [hm4] at hI5
        refine ⟨c5, k5, e5, ⟨e5.wb_right, hm5.trans hm4, by_simp_all,
          hrr5.trans hrr4, hrm5.trans hrm4, ho5.trans ho4, x', j', hx5, hj5, hb5, hxN5, by_omega,
          hI5, hanc5⟩, ?_⟩
        rw [hj5, hj4]
        grind)
      ⟨e2.wb_right, hm2.trans hm1', fun _ _ => rfl, rfl, rfl, rfl, y, L, hx2, hj2, hb2, hyN,
        le_rfl, ⟨hng, hroot⟩, 0, rfl⟩
    have hC3 := hC2.of_frame hr3
    rw [hC3.zero, hj3] at htest
    zubkk

    obtain ⟨hfb, hfg⟩ := hI3.final
    -- `f := UP_0[x]`
    have htab := hM.tab 0 hL x hxN
    simp only [Nat.zero_mul, add_zero, pow_zero, Function.iterate_one] at htab
    have hwx : bUP + x ≤ W := by
      have := hM.wup
      have : x < L * N := lt_of_lt_of_le hxN by_nlinarith
      omega
    obtain ⟨c4, k4, e4, hk4, hw4, hm4, hf4, hr4, hrr4, hrm4, ho4⟩ : ∃ c4 k4,
        Exec P W (block [.addN 130333 130326 130341, .loadN 130344 130333]) c3 c4 k4 ∧ k4 = 2 ∧
        WordsBounded W c4 ∧ c4.nmem = c3.nmem ∧ c4.nreg 130344 = up x ∧
        (∀ r, r ≠ 130333 → r ≠ 130344 → c4.nreg r = c3.nreg r) ∧ c4.rreg = c3.rreg ∧
        c4.rmem = c3.rmem ∧ c4.output = c3.output := by
      exec_block
      · rw [hC3.rUP, hx3]; omega
      · refine ⟨rfl, by_omega, rfl, by config_simp; rw [hC3.rUP, hx3, hm3, htab], fun r h1 h2 => ?_,
          rfl, rfl, rfl⟩
        simp_all
    subst hk2 hk4
    refine ⟨c4, _, .seq e0 (.seq e1 (.ifLtN_true hbad
      ztbal)), ?_, hm4.trans hm3, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have : ztelh * zttz = ztelh * L + 2 * ztelh := by_ring
      grind
    · rw [hr4 r ztcvi
        ztgr, hr3 r hr,
        hr2 r ztgr
          by_grind
          ztgr]
      simp_all
    · grind
    · grind
    · grind
    · rw [hf4]; exact hM.up_lt x hxN
    grind
  · -- `y` is good
    have hgd : GdF c.nmem bACT bFIRST bFPRE bFSZ lo hi y := by
      grind
    have e2 := Exec.copyN (P := P) e1.wb_right 130344 130340
    refine ⟨_, 1 + (k1 + ztgxh), .seq e0 (.seq e1 (.ifLtN_false hbad e2)), ?_, hm1', ?_, ?_, ?_,
      ?_, ?_, Or.inl ⟨hgd, ?_⟩⟩
    · grind
    · zuz
      zudi
      zqbbh
      simp_all
    · omega
    · omega
    · omega
    · simp_all
    simp_all
end proofs
end
end Chazelle.Core.Cluster
end
section
set_option hygiene false
local macro "zqblp" : tactic => `(tactic| (zumwj; unfold MarkRG at hr; grind))
local macro "zqblq" : tactic => `(tactic| simp only [Machine.upd_apply, h1, h2, h3, ite_false])
set_option hygiene true

/-!
# WP-I, part 27: marking the separator on the RAM

`markStmt`: for the corner `u` (register `130600`) of the centroid face, mark in `DF` the
ancestors of `u` in the primal tree whose level lies in the window `[lbot, ltop]` of the piece and
whose position `POS[w]` lies in the segment `[lo, hi)`:

* `t := min (LEV[u], ltop)`; if `t < lbot` nothing is marked;
* the ancestor `w` of `u` at level `t` by binary lifting (`ancLoop`, the table `UPT` of
  `ClusterTables.upStmt` for the parent array `PV`);
* `t + 1 - lbot` steps up from `w`, marking.

`markStmt_exec`: the new flags are `1` exactly at the positions of `lo ≤ POS[x] < hi` among
`up^[LEV[u] - t + i] u`, `i < t + 1 - lbot`; nothing else changes but `DF` and the scratch
registers.

Registers: `130300` `lo`, `130301` `hi`, `130600` `u`; static `130601` (`LEV`), `130602` (`UPT`),
`130603` (`POW`), `130604` (`L`), `130605` (`PV`), `130606` (`POS`), `130607` (`DF`), `130608`
(`μ`), `130609` `lbot`, `130610` `ltop`, `130620` (`UPT + L μ`); scratch `130611 … 130619`.
-/
namespace Chazelle.Core.Cluster
open Machine Machine.Stmt Programs
@[expose] public section
def ancBody : Stmt := .seq (block [.subN 130614 130614 130001, .subN 130615 130615 130608,
    .addN 130618 130603 130614, .loadN 130618 130618])
  (.ifLtN 130613 130618 .skip (block [.addN 130619 130615 130616, .loadN 130616 130619,
    .subN 130613 130613 130618]))

/-- One step of the marking: mark `w` if `lo ≤ POS[w] < hi`, `w := PV[w]`, `cnt := cnt - 1`. -/
def markBody : Stmt := .seq ztjor
  (.seq (.ifLtN 130618 130300 .skip (.ifLtN 130618 130301
      zteph .skip))
    ztgqq)

/-- The search for the ancestor at level `t` and the marking. -/
def markMain : Stmt := .seq (block [.subN 130613 130611 130612, .copyN 130616 130600,
    .copyN 130614 130604, .copyN 130615 130620])
  (.seq ztric
    (.seq ztirb
      ztrid))

/-- **Marking the ancestors of `u` in the window of the piece.** -/
def markStmt : Stmt := .seq (block [.addN 130618 130601 130600, .loadN 130611 130618,
    .copyN 130612 130611])
  (.seq ztipl
    (.ifLtN 130612 130609 .skip markMain))

/-- The scratch registers of the marking. -/
def MarkRG (r : ℕ) : Prop := 130611 ≤ r ∧ r ≤ 130619

/-- The static registers of the marking. -/
structure MarkCtx (c : Config) (lo hi bLEV bUPT bPOW L bPV bPOS bDF μ lbot ltop : ℕ) : Prop where
  one : c.nreg 130001 = 1
  zero : c.nreg 130009 = 0
  rlo : c.nreg 130300 = lo
  rhi : c.nreg 130301 = hi
  rLEV : c.nreg 130601 = bLEV
  rUPT : c.nreg 130602 = bUPT
  rPOW : c.nreg 130603 = bPOW
  rL : c.nreg 130604 = L
  rPV : c.nreg 130605 = bPV
  rPOS : c.nreg 130606 = bPOS
  rDF : c.nreg 130607 = bDF
  rμ : c.nreg 130608 = μ
  rbot : c.nreg 130609 = lbot
  rtop : c.nreg 130610 = ltop
  rend : c.nreg 130620 = bUPT + L * μ
theorem MarkCtx.of_frame {c c' : Config} {lo hi bLEV bUPT bPOW L bPV bPOS bDF μ lbot ltop : ℕ}
    (h : MarkCtx c lo hi bLEV bUPT bPOW L bPV bPOS bDF μ lbot ltop)
    (hr : ∀ r, ¬ MarkRG r → c'.nreg r = c.nreg r) :
    MarkCtx c' lo hi bLEV bUPT bPOW L bPV bPOS bDF μ lbot ltop := by
  zubct
  refine ztcl <;>
    (rw [hr _ ztqgc]; assumption)

/-- The static memory of the marking. -/
structure MarkMem (m : ℕ → ℕ) (W bLEV bUPT bPOW L bPV bPOS bDF μ : ℕ) (up : ℕ → ℕ) : Prop where
  up_lt : ∀ x, x < μ → up x < μ
  pv : ∀ x, x < μ → m (bPV + x) = up x
  tab : ∀ j, j < L → ∀ x, x < μ → m (bUPT + j * μ + x) = up^[2 ^ j] x
  pow : ∀ j, j < L → m zthds = 2 ^ j
  lev_lt : ∀ x, x < μ → m zttgb < 2 ^ L
  lev_mu : ∀ x, x < μ → m zttgb < μ
  wLEV : bLEV + μ ≤ W
  wUPT : bUPT + L * μ ≤ W
  wPOW : bPOW + L ≤ W
  wPV : bPV + μ ≤ W
  wPOS : bPOS + μ ≤ W
  wDF : bDF + μ ≤ W
  -- `DF` is disjoint from what is read
  dLEV : bDF + μ ≤ bLEV ∨ bLEV + μ ≤ bDF
  dUPT : bDF + μ ≤ bUPT ∨ bUPT + L * μ ≤ bDF
  dPOW : bDF + μ ≤ bPOW ∨ bPOW + L ≤ bDF
  dPV : bDF + μ ≤ bPV ∨ bPV + μ ≤ bDF
  dPOS : bDF + μ ≤ bPOS ∨ bPOS + μ ≤ bDF
section proofs
variable {P : Polygon} {W : ℕ}
theorem iterate_lt_of {up : ℕ → ℕ} {μ : ℕ} (h : ∀ x, x < μ → up x < μ) (n : ℕ) {x : ℕ}
    (hx : x < μ) : up^[n] x < μ := by
  induction n generalizing x with
  | zero => exact hx
  | succ n ih => rw [Function.iterate_succ_apply]; exact by_simp_all

/-- The registers written by the ancestor search. -/
def AncRG (r : ℕ) : Prop :=
  r = 130613 ∨ r = 130614 ∨ r = 130615 ∨ r = 130616 ∨ r = 130618 ∨ r = 130619
variable {c : Config}
/-- **The ancestor search**: from `w = u` with `diff < 2^L`, the loop ends with
`w = up^[diff] u`. -/
theorem ancLoop_exec (hw : WordsBounded W c)
    {lo hi bLEV bUPT bPOW L bPV bPOS bDF μ lbot ltop : ℕ} {up : ℕ → ℕ}
    (hC : MarkCtx c lo hi bLEV bUPT bPOW L bPV bPOS bDF μ lbot ltop)
    (hM : MarkMem c.nmem W bLEV bUPT bPOW L bPV bPOS bDF μ up) {u d0 : ℕ} (hu : u < μ)
    (hd : c.nreg 130613 = d0) (hd0 : d0 < 2 ^ L) (hwu : c.nreg 130616 = u)
    (hj : c.nreg 130614 = L) (hrow : c.nreg 130615 = bUPT + L * μ) :
    ∃ c' k, Exec P W ztric c c' k ∧ k ≤ 12 * L + 2 ∧
      WordsBounded W c' ∧ c'.nmem = c.nmem ∧ (∀ r, ¬ AncRG r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      c'.nreg 130616 = up^[d0] u := by
  obtain ⟨c', k, e, ⟨hw', hm', hr', hrr', hrm', ho', j, hjL', hj', hrow', hdj, hwj, hwlt⟩, htest, hk⟩ :=
    whileLtN_pot (P := P) (W := W) (a := 130009) (b := 130614) (body := ancBody)
    (fun c2 => WordsBounded W c2 ∧ c2.nmem = c.nmem ∧ (∀ r, ¬ AncRG r → c2.nreg r = c.nreg r) ∧
      c2.rreg = c.rreg ∧ c2.rmem = c.rmem ∧ c2.output = c.output ∧ ∃ j, j ≤ L ∧
      c2.nreg 130614 = j ∧ c2.nreg 130615 = bUPT + j * μ ∧ c2.nreg 130613 < 2 ^ j ∧
      up^[c2.nreg 130613] (c2.nreg 130616) = up^[d0] u ∧ c2.nreg 130616 < μ)
    (fun c2 => 12 * c2.nreg 130614) ztjvr
    (fun c2 ⟨hw2, hm2, hr2, hrr2, hrm2, ho2, j, hjL, hj2, hrow2, hdj, hwj, hwlt⟩ htest => by
      have hC2 := hC.of_frame (fun r hr => hr2 r ztgrk)
      rw [hC2.zero, hj2] at htest
      zugqe
      have hrowj : bUPT + ztdhr * μ = bUPT + j' * μ + μ := by_grind
      have hjLμ : j' * μ + μ ≤ L * μ := by
        have := Nat.mul_le_mul_right μ by_omega; omega
      have hpow := hM.pow j' by_omega
      rw [← hm2] at hpow
      set w := c2.nreg 130616
      set df := c2.nreg 130613
      obtain ⟨c3, k3, e3, hk3, hw3, h3j, h3row, h3p, h3r, hrr3, hrm3, ho3, hm3⟩ : ∃ c3 k3,
          Exec P W (block [.subN 130614 130614 130001, .subN 130615 130615 130608,
            .addN 130618 130603 130614, .loadN 130618 130618]) c2 c3 k3 ∧ k3 = 4 ∧
          WordsBounded W c3 ∧ c3.nreg 130614 = j' ∧ c3.nreg 130615 = bUPT + j' * μ ∧
          c3.nreg 130618 = 2 ^ j' ∧
          (∀ r, r ≠ 130614 → r ≠ 130615 → r ≠ 130618 → c3.nreg r = c2.nreg r) ∧
          c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output ∧ c3.nmem = c2.nmem := by
        exec_block
        all_goals try (config_simp; simp only [hC2.rPOW, hC2.one, hj2]; have := hM.wPOW; omega)
        refine ⟨rfl, by_omega, by config_simp; rw [hj2, hC2.one]; omega, by
          config_simp; rw [hrow2, hC2.rμ, hrowj]; omega, by
          config_simp; rw [hC2.rPOW, hj2, hC2.one, show j' + 1 - 1 = j' by omega]; omega,
          fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
        zqblq
      have h3w : ztupi := by_grind
      have h3d : c3.nreg 130613 = df := by_grind
      have hframe3 : ∀ r, ¬ AncRG r → c3.nreg r = c.nreg r := fun r hr =>
        (h3r r ztcmj ztcmj
          ztcmj).trans by_simp_all
      by_cases hlt : c3.nreg 130613 < c3.nreg 130618
      · -- no jump
        refine ⟨c3, k3 + ztbgo, .seq e3 (.ifLtN_true hlt ztdyd), ⟨hw3, hm3.trans hm2,
          hframe3, hrr3.trans hrr2, hrm3.trans hrm2, ho3.trans ho2, j', by_omega, h3j, h3row,
          ?_, ?_, ?_⟩, ?_⟩
        · omega
        · simp_all
        · omega
        omega
      · -- the jump
        have hwμ := hwlt
        have htab := hM.tab j' by_omega w hwμ
        rw [← hm2] at htab
        obtain ⟨c4, k4, e4, hk4, hw4, h4w, h4d, h4r, hrr4, hrm4, ho4, hm4⟩ : ∃ c4 k4,
            Exec P W (block [.addN 130619 130615 130616, .loadN 130616 130619,
              .subN 130613 130613 130618]) c3 c4 k4 ∧ k4 = 3 ∧ WordsBounded W c4 ∧
            c4.nreg 130616 = up^[2 ^ j'] w ∧ c4.nreg 130613 = df - 2 ^ j' ∧
            (∀ r, r ≠ 130613 → r ≠ 130616 → r ≠ 130619 → c4.nreg r = c3.nreg r) ∧
            c4.rreg = c3.rreg ∧ c4.rmem = c3.rmem ∧ c4.output = c3.output ∧
            c4.nmem = c3.nmem := by
          exec_block
          · rw [h3row, h3w]; have := hM.wUPT; omega
          · refine ⟨rfl, by_omega, by_simp_all, by
              simp_all, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
            zqblq
        rw [h3d, h3p] at hlt
        refine ⟨c4, k3 + (k4 + 2), .seq e3 (.ifLtN_false by_omega e4),
          ⟨hw4, by_grind, fun r hr => ?_, by_grind,
          by grind, by_grind, j', by_omega, ?_, ?_, ?_, ?_,
          ?_⟩, ?_⟩
        · rw [h4r r ztcmj ztcmj
            ztcmj]
          grind
        · grind
        · grind
        · omega
        · rw [h4d, h4w, ← Function.iterate_add_apply, show df - 2 ^ j' + 2 ^ j' = df by omega]
          omega
        · rw [h4w]; exact iterate_lt_of hM.up_lt _ hwμ
        grind)
    ⟨hw, rfl, fun _ _ => rfl, rfl, rfl, rfl, L, le_rfl, hj, hrow, by_omega,
      by simp_all, by_omega⟩
  have hC' := hC.of_frame (fun r hr => hr' r ztgrk)
  rw [hC'.zero, hj'] at htest
  zubkk

  have : c'.nreg 130613 = 0 := by_omega
  refine ⟨c', k, e, ?_, hw', hm', hr', hrr', hrm', ho', ?_⟩
  · omega
  simp_all
open Classical in
/-- The memory after marking the first `i` vertices `up^[i'] w0`, `i' < i`, found in `[lo, hi)`. -/
noncomputable def markMem (m : ℕ → ℕ) (bPOS bDF lo hi : ℕ) (up : ℕ → ℕ) (w0 i : ℕ) : ℕ → ℕ :=
  fun a => if ∃ x, a = bDF + x ∧ lo ≤ m ztfpd ∧ m ztfpd < hi ∧
    ∃ i', i' < i ∧ x = up^[i'] w0 then 1 else m a

/-- **The marking loop.** -/
theorem markLoop_exec (hw : WordsBounded W c)
    {lo hi bLEV bUPT bPOW L bPV bPOS bDF μ lbot ltop : ℕ} {up : ℕ → ℕ}
    (hC : MarkCtx c lo hi bLEV bUPT bPOW L bPV bPOS bDF μ lbot ltop)
    (hM : MarkMem c.nmem W bLEV bUPT bPOW L bPV bPOS bDF μ up) {w0 cnt : ℕ} (hw0 : w0 < μ)
    (hwr : c.nreg 130616 = w0) (hcnt : c.nreg 130617 = cnt) :
    ∃ c' k, Exec P W ztrid c c' k ∧ k ≤ 12 * cnt + 2 ∧
      WordsBounded W c' ∧ c'.nmem = markMem c.nmem bPOS bDF lo hi up w0 cnt ∧
      ztivr ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  classical
  obtain ⟨c', k, e, ⟨hw', i, hile, hcnt', hw'', hwlt, hm', hr', hrr', hrm', ho'⟩, htest, hk⟩ :=
    whileLtN_pot (b := 130617)
    (fun c2 => WordsBounded W c2 ∧ ∃ i, i ≤ cnt ∧ c2.nreg 130617 = cnt - i ∧
      c2.nreg 130616 = up^[i] w0 ∧ up^[i] w0 < μ ∧
      c2.nmem = markMem c.nmem bPOS bDF lo hi up w0 i ∧
      (∀ r, ¬ MarkRG r → c2.nreg r = c.nreg r) ∧ c2.rreg = c.rreg ∧ c2.rmem = c.rmem ∧
      c2.output = c.output)
    (fun c2 => 12 * c2.nreg 130617) ztjvr
    (fun c2 ⟨hw2, i, hile, hc2, hw2', hwlt, hm2, hr2, hrr2, hrm2, ho2⟩ htest => by
      zulhq
      rw [hC2.zero, hc2] at htest
      set w := up^[i] w0
      -- reads of the static arrays are unchanged by the marks
      have hread : ∀ b n, b + n ≤ bDF ∨ bDF + μ ≤ b → ∀ y, y < n →
          c2.nmem zttfj = c.nmem zttfj := by
        intro b n hb y hy
        zumnp
        zulup
        zucjw
        rintro ⟨x, hx, -, -, i', -, rfl⟩
        have := iterate_lt_of hM.up_lt i' hw0
        omega
      have hpos : c2.nmem _ = c.nmem _ := hread _ _ hM.dPOS.symm w hwlt
      have hpv : c2.nmem zttgg = up w := by
        rw [hread _ _ hM.dPV.symm w hwlt, hM.pv w hwlt]
      obtain ⟨c3, k3, e3, hk3, hw3, h3p, h3r, hrr3, hrm3, ho3, hm3⟩ : ∃ c3 k3, Exec P W
          ztjor c2 c3 k3 ∧ k3 = 2 ∧
          WordsBounded W c3 ∧ c3.nreg 130618 = c.nmem zttgf ∧
          (∀ r, r ≠ 130618 → c3.nreg r = c2.nreg r) ∧ c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧
          c3.output = c2.output ∧ c3.nmem = c2.nmem := by
        exec_block
        · rw [hC2.rPOS, hw2']; have := hM.wPOS; omega
        · refine ⟨rfl, by_omega, by config_simp; rw [hC2.rPOS, hw2', hpos], fun r hr => ?_, rfl, rfl,
            rfl, rfl⟩
          simp_all
      have hC3 := hC2.of_frame (fun r hr => h3r r ztbzo)
      have h3w : ztupi := by_simp_all
      have h3c : c3.nreg 130617 = cnt - i := by_simp_all
      -- the conditional mark
      set inseg := c.nmem zttgf
      obtain ⟨c4, k4, e4, hk4, hw4, h4r, hrr4, hrm4, ho4, hm4⟩ : ∃ c4 k4, Exec P W
          (.ifLtN 130618 130300 .skip (.ifLtN 130618 130301
            zteph .skip)) c3 c4 k4 ∧
          k4 ≤ 5 ∧ WordsBounded W c4 ∧ (∀ r, r ≠ 130619 → c4.nreg r = c3.nreg r) ∧
          c4.rreg = c3.rreg ∧ c4.rmem = c3.rmem ∧ c4.output = c3.output ∧
          c4.nmem = if lo ≤ inseg ∧ inseg < hi then upd c3.nmem (bDF + w) 1 else c3.nmem := by
        by_cases h1 : c3.nreg 130618 < c3.nreg 130300
        · refine ⟨c3, 0 + 1, .ifLtN_true h1 ztdyd, by_omega, hw3, by_omega, rfl, rfl,
            rfl, ?_⟩
          zunjl; rw [h3p, hC3.rlo] at h1; omega
        · by_cases h2 : c3.nreg 130618 < c3.nreg 130301
          · obtain ⟨c5, k5, e5, hk5, hw5, h5r, hrr5, hrm5, ho5, hm5⟩ : ∃ c5 k5, Exec P W
                zteph c3 c5 k5 ∧ k5 = 2 ∧
                WordsBounded W c5 ∧ (∀ r, r ≠ 130619 → c5.nreg r = c3.nreg r) ∧
                c5.rreg = c3.rreg ∧ c5.rmem = c3.rmem ∧ c5.output = c3.output ∧
                c5.nmem = upd c3.nmem _ 1 := by
              exec_block
              · rw [hC3.rDF, h3w]; have := hM.wDF; omega
              · refine ⟨rfl, by_omega, fun r hr => ?_, rfl, rfl, rfl, ?_⟩
                · zuhpk
                · config_simp; rw [hC3.rDF, h3w, hC3.one]
            refine ⟨c5, k5 + 1 + 2, .ifLtN_false h1 (.ifLtN_true h2 e5), by_omega, hw5, h5r,
              hrr5, hrm5, ho5, ?_⟩
            rw [ite_eq_left]; · omega
            rw [h3p, hC3.rlo] at h1; rw [h3p, hC3.rhi] at h2; omega
          · refine ⟨c3, 0 + 2 + 2, .ifLtN_false h1 ztzro, by_omega, hw3,
              by omega, rfl, rfl, rfl, ?_⟩
            zunjl; rw [h3p, hC3.rhi] at h2; omega
      have h4w : c4.nreg 130616 = w := by_grind
      have h4c : c4.nreg 130617 = cnt - i := by_grind
      have hC4 := hC3.of_frame (fun r hr => h4r r ztbzo)
      have hpv4 : c4.nmem zttgg = up w := by
        zumnq
        split_ifs
        · rw [Machine.upd_other _ _ _ (by have := hM.dPV; omega), hm3, hpv]
        grind
      obtain ⟨c5, k5, e5, hk5, hw5, h5w, h5c, h5r, hrr5, hrm5, ho5, hm5⟩ : ∃ c5 k5, Exec P W
          ztgqq
          c4 c5 k5 ∧ k5 = 3 ∧ WordsBounded W c5 ∧ c5.nreg 130616 = up w ∧
          c5.nreg 130617 = cnt - i - 1 ∧
          (∀ r, r ≠ 130616 → r ≠ 130617 → r ≠ 130618 → c5.nreg r = c4.nreg r) ∧
          c5.rreg = c4.rreg ∧ c5.rmem = c4.rmem ∧ c5.output = c4.output ∧ c5.nmem = c4.nmem := by
        exec_block
        · rw [hC4.rPV, h4w]; have := hM.wPV; omega
        · refine ⟨rfl, by_omega, by config_simp; rw [hC4.rPV, h4w, hpv4], by
            config_simp; rw [h4c, hC4.one], fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
          zqblq
      refine ⟨c5, k3 + zttqj, .seq e3 ztncj, ⟨hw5, i + 1, by_omega, by_omega,
        by rw [h5w, Function.iterate_succ_apply'], by
          zuocm; exact hM.up_lt _ hwlt, ?_, fun r hr => ?_,
        by grind, by_grind,
        by grind⟩, ?_⟩
      · rw [hm5, hm4, hm3, hm2]
        funext a
        zulup
        by_cases hseg : lo ≤ inseg ∧ inseg < hi
        · rw [ite_eq_left hseg, Machine.upd_apply]
          by_cases ha : a = bDF + w
          · rw [ite_eq_left ha, ite_eq_left by_grind]
          · zuhmm
            by_cases hex : ∃ x, a = bDF + x ∧ lo ≤ c.nmem ztfpd ∧ c.nmem ztfpd < hi ∧
                ∃ i', i' < i ∧ x = up^[i'] w0
            · rw [ite_eq_left hex, ite_eq_left (by
                grind)]
            · zueys
              grind
        · rw [ite_eq_right hseg]
          by_cases hex : ∃ x, a = bDF + x ∧ lo ≤ c.nmem ztfpd ∧ c.nmem ztfpd < hi ∧
              ∃ i', i' < i ∧ x = up^[i'] w0
          · rw [ite_eq_left hex, ite_eq_left (by
              grind)]
          · zueys
            grind
      · rw [h5r r ztbzo ztbzo
          ztbzo, h4r r ztbzo,
          h3r r ztbzo]
        grind
      omega)
    ⟨hw, 0, Nat.zero_le _, by_omega, hwr, hw0, by
      funext a; unfold markMem; simp,
      by omega, rfl, rfl, rfl⟩
  have hC' := hC.of_frame hr'
  rw [hC'.zero, hcnt'] at htest
  have hic : i = cnt := by_omega
  subst hic
  refine ⟨c', k, e, ?_, hw', hm', hr', hrr', hrm', ho'⟩
  rw [hcnt] at hk; omega

/-- **Marking the ancestors of the corner `u`.** -/
theorem markStmt_exec (hw : WordsBounded W c)
    {lo hi bLEV bUPT bPOW L bPV bPOS bDF μ lbot ltop : ℕ} {up : ℕ → ℕ}
    (hC : MarkCtx c lo hi bLEV bUPT bPOW L bPV bPOS bDF μ lbot ltop)
    (hM : MarkMem c.nmem W bLEV bUPT bPOW L bPV bPOS bDF μ up) {u : ℕ}
    (hu : c.nreg 130600 = u) (huμ : u < μ) :
    ∃ c' k, Exec P W markStmt c c' k ∧ k ≤ 12 * L + 12 * ztgkx + 30 ∧
      WordsBounded W c' ∧
      c'.nmem = (if lbot ≤ min ztija ltop then
        markMem c.nmem bPOS bDF lo hi up (up^[c.nmem (bLEV + u) - min ztija ltop] u)
          (min ztija ltop + 1 - lbot) else c.nmem) ∧
      ztivr ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  set lu := c.nmem _
  set t := min lu ltop
  have hlu := hM.lev_lt u huμ
  -- `lu` and `t`
  obtain ⟨c1, k1, e1, hk1, hw1, h1l, h1t, h1r, hrr1, hrm1, ho1, hm1⟩ : ∃ c1 k1, Exec P W
      (block [.addN 130618 130601 130600, .loadN 130611 130618, .copyN 130612 130611]) c c1 k1 ∧
      k1 = 3 ∧ WordsBounded W c1 ∧ c1.nreg 130611 = lu ∧ c1.nreg 130612 = lu ∧
      (∀ r, ¬ MarkRG r → c1.nreg r = c.nreg r) ∧ c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧
      c1.output = c.output ∧ c1.nmem = c.nmem := by
    exec_block
    · zunnt; have := hM.wLEV; omega
    · refine ⟨rfl, by_omega, by config_simp; zunnt, by config_simp; zunnt,
        fun r hr => ?_, rfl, rfl, rfl, rfl⟩
      zqblp
  have hC1 := hC.of_frame h1r
  obtain ⟨c2, k2, e2, hk2, hw2, h2l, h2t, h2r, hrr2, hrm2, ho2, hm2⟩ : ∃ c2 k2, Exec P W
      ztipl c1 c2 k2 ∧ k2 ≤ 2 ∧
      WordsBounded W c2 ∧ c2.nreg 130611 = lu ∧ c2.nreg 130612 = t ∧
      (∀ r, ¬ MarkRG r → c2.nreg r = c1.nreg r) ∧ c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧
      c2.output = c1.output ∧ c2.nmem = c1.nmem := by
    by_cases h : c1.nreg 130610 < c1.nreg 130612
    · have ec := Exec.copyN (P := P) hw1 130612 130610
      refine ⟨_, _, .ifLtN_true h ec, le_refl _, ec.wb_right, by_simp_all, ?_, fun r hr => ?_,
        rfl, rfl, rfl, rfl⟩
      · simp only [Machine.upd_same, hC1.rtop]
        rw [hC1.rtop, h1t] at h; grind
      · zqblp
    · refine ⟨c1, _, .ifLtN_false h ztdbq, by_omega, hw1, h1l, ?_, by_omega, rfl,
        rfl, rfl, rfl⟩
      rw [h1t]; rw [hC1.rtop, h1t] at h; grind
  zulhr
  have hframe2 : ∀ r, ¬ MarkRG r → c2.nreg r = c.nreg r := by_simp_all
  by_cases hbot : c2.nreg 130612 < c2.nreg 130609
  · -- nothing to mark
    refine ⟨c2, k1 + (k2 + ztbgo), .seq e1 (.seq e2 (.ifLtN_true hbot ztgbs)),
      by omega, hw2, ?_, hframe2, hrr2.trans hrr1, hrm2.trans hrm1, ho2.trans ho1⟩
    rw [h2t, hC2.rbot] at hbot
    simp_all
  · have htb : lbot ≤ t := by rw [h2t, hC2.rbot] at hbot; omega
    have hm21 := hm2.trans hm1
    obtain ⟨c3, k3, e3, hk3, hw3, h3d, h3w, h3j, h3row, h3t, h3r, hrr3, hrm3, ho3, hm3⟩ :
        ∃ c3 k3, Exec P W (block [.subN 130613 130611 130612, .copyN 130616 130600,
          .copyN 130614 130604, .copyN 130615 130620]) c2 c3 k3 ∧ k3 = 4 ∧ WordsBounded W c3 ∧
        c3.nreg 130613 = lu - t ∧ c3.nreg 130616 = u ∧ c3.nreg 130614 = L ∧
        c3.nreg 130615 = bUPT + L * μ ∧ c3.nreg 130612 = t ∧
        (∀ r, ¬ MarkRG r → c3.nreg r = c2.nreg r) ∧
        c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output ∧ c3.nmem = c2.nmem := by
      exec_block
      refine ⟨rfl, by_omega, by_simp_all, by config_simp; rw [hframe2 _ (by
        unfold MarkRG; omega), hu], by config_simp; exact hC2.rL, by config_simp; exact hC2.rend,
        by simp_all, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
      zqblp
    have hC3 := hC2.of_frame h3r
    have hM3 : MarkMem c3.nmem W bLEV bUPT bPOW L bPV bPOS bDF μ up := by
      simp_all
    obtain ⟨c4, k4, e4, hk4, hw4, hm4, h4r, hrr4, hrm4, ho4, h4w⟩ := ancLoop_exec hw3 hC3
      hM3 huμ h3d by_omega h3w h3j h3row
    have hA4 : ∀ r, ¬ MarkRG r → ¬ AncRG r := fun r hr h => hr (by
      unfold AncRG at h; unfold MarkRG; omega)
    have hC4 := hC3.of_frame (fun r hr => h4r r by_simp_all)
    have h4t := (h4r _ (by unfold AncRG; omega)).trans h3t
    obtain ⟨c5, k5, e5, hk5, hw5, h5c, h5w, h5r, hrr5, hrm5, ho5, hm5⟩ : ∃ c5 k5, Exec P W
        ztirb c4 c5 k5 ∧ k5 = 2 ∧
        WordsBounded W c5 ∧ c5.nreg 130617 = t + 1 - lbot ∧ c5.nreg 130616 = up^[lu - t] u ∧
        (∀ r, ¬ MarkRG r → c5.nreg r = c4.nreg r) ∧ c5.rreg = c4.rreg ∧ c5.rmem = c4.rmem ∧
        c5.output = c4.output ∧ c5.nmem = c4.nmem := by
      exec_block
      · config_simp; zunxp; have := hM.wLEV; have := hM.lev_mu u huμ
        grind
      · refine ⟨rfl, by_omega, by config_simp; zunxp; omega,
          by simp_all, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
        zqblp
    zulhs
    have hM5 : MarkMem c5.nmem W bLEV bUPT bPOW L bPV bPOS bDF μ up := by
      simp_all
    obtain ⟨c6, k6, e6, hk6, hw6, hm6, h6r, hrr6, hrm6, ho6⟩ := markLoop_exec hw5 hC5 hM5
      (iterate_lt_of hM.up_lt _ huμ) h5w h5c
    refine ⟨c6, _, .seq e1 (.seq e2 (.ifLtN_false hbot (.seq e3 (.seq e4 (.seq e5 e6))))), ?_,
      hw6, ?_,
      fun r hr => ?_, ?_, ?_, ?_⟩
    · grind
    · grind
    · simp_all
    · simp_all
    · simp_all
    simp_all
end proofs
end
end Chazelle.Core.Cluster
end
namespace Chazelle.Core.Cluster
namespace BTree
@[expose] public section
variable {R : BTree}

/-- The good predicate: more than half of the keys of `[lo, hi)` lie in the interval of `z`. -/
def GdN (pre sz κ : ℕ → ℕ) (lo hi z : ℕ) : Prop :=
  hi - lo < 2 * cntIn κ lo hi ztwbt (pre z + sz z)
variable {κ : ℕ → ℕ}
/-- The count of a key interval is at most the number of positions in any range containing all
positions whose key is in the interval. -/
theorem cntIn_le_of_sub {lo hi a b l r : ℕ}
    (h : ∀ i, lo ≤ i → i < hi → a ≤ κ i → κ i < b → l ≤ i ∧ i < r) :
    cntIn κ lo hi a b ≤ r - l := by
  zuluh
  rw [← Nat.card_Ico l r]
  refine Finset.card_le_card ztjvx
  simp_all

/-- **The median**: a key interval holding more than half of the sorted keys holds the key of
the median position. -/
theorem median_mem {lo hi a b : ℕ} (hs : Sorted κ lo hi)
    (hg : hi - lo < 2 * cntIn κ lo hi a b) :
    a ≤ κ ztwno ∧ κ ztwno < b := by
  have hlh : ztskf := by
    zumv
    have : cntIn κ lo hi a b = 0 := by
      zuluh
      simp_all
    omega
  set m := lo + ztcw / 2
  have hm : m < hi := by_omega
  constructor
  · zubq

    have := cntIn_le_of_sub (κ := κ) (lo := lo) (hi := hi) (a := a) (b := b) (l := m + 1) (r := hi)
      (fun i h1 h2 h3 _ => by
        refine ztufr
        by_contra hi'
        have := hs i m h1 by_omega hm
        omega)
    omega
  · zubq

    have := cntIn_le_of_sub (κ := κ) (lo := lo) (hi := hi) (a := a) (b := b) (l := lo) (r := m)
      (fun i h1 h2 _ h4 => by
        zujfv
        by_contra hi'
        have := hs m i by_omega by_omega h2
        omega)
    omega
variable {pre slot : ℕ → ℕ}

/-- **Every good node is an ancestor of the median face.** -/
theorem good_anc_median (hR : R.OK) (hP : R.PreInv pre slot R.n) {κ φ : ℕ → ℕ} {lo hi z : ℕ}
    (hs : Sorted κ lo hi) (hκ : ∀ i, lo ≤ i → i < hi → φ i < R.n ∧ κ i = pre ztwim)
    (hz : z < R.n) (hg : GdN pre ztuo κ lo hi z) :
    R.Anc z (φ ztwno) := by
  unfold GdN at hg
  simp only at hg
  have hlh : ztskf := by
    zumv
    have : cntIn κ lo hi ztwbt (pre z + (R.sub z).card) = 0 := by
      zuluh
      simp_all
    omega
  obtain ⟨h1, h2⟩ := median_mem hs hg
  obtain ⟨hφ, hκm⟩ := hκ ztwno by_omega by_omega
  rw [hκm] at h1 h2
  exact (hP.anc_iff hR hz hφ).mpr ztwo

/-- **The root is good** for a nonempty piece whose keys are preorders. -/
theorem good_root (hR : R.OK) (hP : R.PreInv pre slot R.n) {κ φ : ℕ → ℕ} {lo hi : ℕ}
    (hκ : ∀ i, lo ≤ i → i < hi → φ i < R.n ∧ κ i = pre ztwim) (hlh : lo < hi) :
    GdN pre ztuo κ lo hi R.root := by
  unfold GdN cntIn
  zubi
  rw [hP.root, hR.card_sub_root]
  have : (Finset.Ico lo hi).filter (fun i => 0 ≤ κ i ∧ κ i < 0 + R.n) = Finset.Ico lo hi := by
    refine Finset.filter_true_of_mem ztjvx
    simp only [Finset.mem_Ico] at hi'
    obtain ⟨a, b⟩ := hκ i hi'.1 hi'.2
    rw [b]
    exact ⟨Nat.zero_le _, by have := hP.pre_lt hR a; omega⟩
  rw [this, Nat.card_Ico]
  omega

/-- Going up `j ≥ pos h` steps reaches the root. -/
theorem iterate_up_root (hR : R.OK) {h : ℕ} (hh : h < R.n) {j : ℕ} (hj : R.pos h ≤ j) :
    R.up^[j] h = R.root := by
  induction j generalizing h with
  | zero =>
    have : R.pos h = 0 := by_omega
    have e := (hR.pos_spec hh).2
    zvmwk at e
    rw [Function.iterate_zero_apply, ← e]; rfl
  | succ j ih =>
    zujgm
    zufrj
    · have : R.up h = h := by zuncn
      zubk
      exact ih hh (by rw [hr, hR.pos_root]; omega)
    · have hup : ztmtu := by zuncn
      obtain ⟨a, b⟩ := hR.par_spec hh hr
      grind

/-- **Two children of one node on the path to `y` are equal.** -/
theorem anc_ch_unique (hR : R.OK) {y c c' : ℕ} (hy : y < R.n) (hc : R.Anc c y)
    (hc' : R.Anc c' y) (hcr : c ≠ R.root) (hcr' : c' ≠ R.root) (hp : R.par c = R.par c') :
    c = c' := by
  -- ancestors of `y` are totally ordered
  obtain ⟨m, hm⟩ := hc
  obtain ⟨m', hm'⟩ := hc'
  have hcn : c < R.n := hm ▸ hR.iterate_up_lt m hy
  have hcn' : c' < R.n := hm' ▸ hR.iterate_up_lt m' hy
  have key : ∀ {a b : ℕ} {i j : ℕ}, R.up^[i] y = a → R.up^[j] y = b → i ≤ j → a < R.n →
      a ≠ R.root → b ≠ R.root → R.par a = R.par b → a = b := by
    intro a b i j hi hj hij ha har hbr hpar
    zuct
    have hab : R.Anc b a := ⟨j - i, by
      rw [← hi, ← Function.iterate_add_apply, show j - i + i = j by omega]; exact hj⟩
    have hba : b ≠ a := fun h => hne h.symm
    have h1 := (anc_iff_up hba).mp hab
    rw [show R.up a = R.par a by simp [up, har], hpar] at h1
    have hbn : b < R.n := hj ▸ hR.iterate_up_lt j hy
    have := hR.pos_le_of_anc (hR.par_spec hbn hbr).1 h1
    have := (hR.par_spec hbn hbr).2
    omega
  grind

/-- **The centroid from the climb.**  If every good node is an ancestor of `y`, the result of
the climb (either `y` good, or `up x` good for an ancestor `x` of `y` that is not good) is a good
node without good children. -/
theorem centroid_of_climb (hR : R.OK) {Gd : ℕ → Prop} {y f : ℕ} (hy : y < R.n)
    (hanc : ∀ z, z < R.n → Gd z → R.Anc z y)
    (hres : (Gd y ∧ f = y) ∨ ∃ x n, R.up^[n] y = x ∧ ¬ Gd x ∧ Gd ztqcf ∧ f = R.up x) :
    Gd f ∧ ∀ c, c < R.n → c ≠ R.root → R.par c = f → ¬ Gd c := by
  rcases hres with ⟨hg, rfl⟩ | ⟨x, n, hx, hng, hg, rfl⟩
  · refine ⟨hg, fun c hc hcr hpc hgc => ?_⟩
    have h1 := hanc c hc hgc
    have h2 : R.Anc f c := ⟨1, by zunxn⟩
    have := hR.anc_antisymm hy hc h1 h2
    zumo
    have := (hR.par_spec hc hcr).2
    simp_all
  · have hxr : x ≠ R.root := by
      zuq
      have : R.up x = x := by simp [up, h]
      simp_all
    have hxn : x < R.n := hx ▸ hR.iterate_up_lt n hy
    refine ⟨hg, fun c hc hcr hpc hgc => hng ?_⟩
    have hupx : R.up x = R.par x := by simp [up, hxr]
    have := anc_ch_unique hR hy (hanc c hc hgc) ⟨n, hx⟩ hcr hxr by_omega
    simp_all
end
end BTree
end Chazelle.Core.Cluster
namespace Chazelle.Core.L41
open Machine Machine.Stmt Programs
@[expose] public section
theorem dvd_succ_iff {x g : ℕ} (h : 2 ^ g ∣ x) : 2 ^ ztbs ∣ x ↔ ztqyu % 2 = 0 := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.mul_div_cancel_left _ by_positivity, pow_succ, Nat.mul_dvd_mul_iff_left by_positivity]
  omega
theorem div_succ (x g : ℕ) : x / 2 ^ ztbs = x / 2 ^ g / 2 := by
  zuolh

/-- If `g` satisfies the grade condition but `g + 1` does not (or is out of range), `g` is the
greedy grade. -/
theorem nextG_eq_of {lam b x g : ℕ} (hg : g ≤ lam - 1) (hok : GradeOK b x g)
    (hno : g + 1 ≤ lam - 1 → ¬ GradeOK b x ztbs) : nextG lam b x = g := by
  zudmc
  · zux

    have hx : x < b := by have := hok.2; grind
    exact hno (by have := nextG_le lam b x; omega)
      (gradeOK_mono (nextG_spec hx) hc)
  · exact le_nextG hg hok

/-! ## The program -/

/-- One step of the ascending search. -/
def ascBody : Stmt := .seq (.instr (.addN 160016 160012 160024))
  (.ifLtN 160016 160026
    (.seq ztgqr
      (.ifLtN 160018 160013 ztfep
        (.seq (block [.addN 160019 160021 160016, .loadN 160019 160019,
            .addN 160019 160010 160019])
          (.ifLtN 160011 160019 ztfep
            ztkrt))))
    ztfep)

/-- **The greedy grade.** -/
def ascS : Stmt := .seq zthsi
  (.whileLtN 160025 160024 ascBody)

/-- The registers written by `ascS`. -/
def AscRG (r : ℕ) : Prop := r = 160012 ∨ r = 160013 ∨ (160016 ≤ r ∧ r ≤ 160019) ∨ r = 160025
section proofs
variable {P : Polygon} {W : ℕ}

/-- The state of the ascending search. -/
def AscInv (lam b x : ℕ) (c0 c : Config) : Prop :=
  (∀ r, ¬ AscRG r → c.nreg r = c0.nreg r) ∧ c.nmem = c0.nmem ∧ c.rreg = c0.rreg ∧
    c.rmem = c0.rmem ∧ c.output = c0.output ∧ c.nreg 160012 ≤ lam - 1 ∧
    GradeOK b x (c.nreg 160012) ∧ c.nreg 160013 = x / 2 ^ c.nreg 160012 ∧
    (c.nreg 160025 = 0 ∨ (c.nreg 160025 = 1 ∧ c.nreg 160012 = nextG lam b x))
set_option maxHeartbeats 4000000 in
/-- One step of the ascending search. -/
theorem ascBody_exec {c0 c : Config} (hw : WordsBounded W c) {lam b x D PW : ℕ}
    (h10 : c0.nreg 160010 = x) (h11 : c0.nreg 160011 = b) (h26 : c0.nreg 160026 = lam)
    (h24 : c0.nreg 160024 = 1) (h20 : c0.nreg 160020 = D) (h21 : c0.nreg 160021 = PW)
    (hD : ∀ y, y ≤ b → c0.nmem ztnki = y / 2)
    (hPW : ∀ i, i ≤ lam → c0.nmem ztjlf = 2 ^ i)
    (hWD : D + b ≤ W) (hWP : PW + lam ≤ W) (hWx : b + 2 ^ lam ≤ W)
    (hI : AscInv lam b x c0 c) (hf : c.nreg 160025 = 0) :
    ∃ c' k, Exec P W ascBody c c' k ∧ AscInv lam b x c0 c' ∧
      20 * ztife + k + 2 ≤
        20 * ((lam - c.nreg 160012) + (1 - c.nreg 160025)) := by
  obtain ⟨hr, hm, hrr, hrm, ho, hgl, hok, hq, -⟩ := hI
  have r10 : c.nreg 160010 = x := by zunay; omega
  have r11 : c.nreg 160011 = b := by zunay; omega
  have r26 : c.nreg 160026 = lam := by zunay; omega
  have r24 : ztplx := by zunay; omega
  have r20 : c.nreg 160020 = D := by zunay; omega
  have r21 : c.nreg 160021 = PW := by zunay; omega
  set g := c.nreg 160012 with hg
  have hxb := hok.2
  have hqx : x / 2 ^ g ≤ x := Nat.div_le_self _ _
  have hpg := Nat.one_le_two_pow (n := g)
  have hpl : 2 ^ g ≤ 2 ^ lam := Nat.pow_le_pow_right by_norm_num by_omega
  -- the counter step
  have e1 := Exec.addN (P := P) hw 160016 160012 160024 by_omega
  set c1 := { c with nreg := upd c.nreg 160016 _ } with hc1
  have k1 : ∀ r, r ≠ 160016 → c1.nreg r = c.nreg r := by_simp_all
  have h16 : c1.nreg 160016 = g + 1 := by
    simp_all
  -- a stopping step: the flag is set, the grade is the greedy one
  have stop : ∀ c2 : Config, WordsBounded W c2 → (∀ r, ¬ AscRG r → c2.nreg r = c.nreg r) →
      c2.nmem = c.nmem → c2.rreg = c.rreg → c2.rmem = c.rmem → c2.output = c.output →
      c2.nreg 160012 = g → c2.nreg 160013 = x / 2 ^ g → nextG lam b x = g →
      Exec P W ztfep c2 { c2 with nreg := upd c2.nreg 160025 1 } 1 ∧
        AscInv lam b x c0 { c2 with nreg := upd c2.nreg 160025 1 } := by
    intro c2 hw2 hr2 hm2 hrr2 hrm2 ho2 hg2 hq2 hn
    refine ⟨Exec.constN hw2 160025 1 by_omega, ?_⟩
    refine ⟨fun r hr' => ?_, by_simp_all, by_simp_all,
      by simp_all, by_simp_all, ?_, ?_, ?_, ?_⟩
    · zubi
      rw [Machine.upd_other _ _ _ (by unfold AscRG at hr'; omega), hr2 r hr', hr r hr']
    · simp_all
    · simp_all
    · simp_all
    simp_all
  unfold ascBody
  by_cases hA : c1.nreg 160016 < c1.nreg 160026
  · zufna
    -- read `q / 2`
    obtain ⟨c2, k2, e2, hk2, hw2, h17, h18, k2r, hm2, hrr2, hrm2, ho2⟩ : ∃ c2 k2, Exec P W
        ztgqr
        c1 c2 k2 ∧ k2 = 3 ∧ WordsBounded W c2 ∧ c2.nreg 160017 = x / 2 ^ g / 2 ∧
        c2.nreg 160018 = x / 2 ^ g / 2 + x / 2 ^ g / 2 ∧
        (∀ r, r ≠ 160017 → r ≠ 160018 → c2.nreg r = c1.nreg r) ∧ c2.nmem = c.nmem ∧
        c2.rreg = c.rreg ∧ c2.rmem = c.rmem ∧ c2.output = c.output := by
      have q1 : c1.nreg 160020 = D := by_grind
      have q2 : c1.nreg 160013 = x / 2 ^ g := by_grind
      have md : c1.nmem (D + x / 2 ^ g) = x / 2 ^ g / 2 := by
        show c.nmem _ = _; zvmwi; exact hD _ by_omega
      have e1w := e1.wb_right
      exec_block
      · omega
      · config_simp; zunhs; omega
      · refine ⟨rfl, by_omega, by config_simp; zunhs, by config_simp; zunhs,
          fun r a1 a2 => ?_, rfl, rfl, rfl, rfl⟩
        zudi
        grind
    have fr2 : ∀ r, ¬ AscRG r → c2.nreg r = c.nreg r := fun r hr' => by
      unfold AscRG at hr'; rw [k2r r by_omega by_omega, k1 r by_omega]
    have g2 : c2.nreg 160012 = g := by zunpj
    have q2 : c2.nreg 160013 = x / 2 ^ g := by
      zunpj; exact hq
    have t13 := q2
    by_cases hodd : c2.nreg 160018 < c2.nreg 160013
    · rw [h18, t13] at hodd
      obtain ⟨e3, hI3⟩ := stop c2 hw2 fr2 hm2 hrr2 hrm2 ho2 g2 q2
        (nextG_eq_of hgl hok (fun _ hg1 => by
          have := (dvd_succ_iff hok.1).mp hg1.1; omega))
      refine ⟨_, _, .seq e1 (.ifLtN_true by_grind
        ztnci), hI3, ?_⟩
      simp only [Machine.upd_same, Machine.upd_other _ _ _ ztfci]
      omega
    · have heven : ztqyu % 2 = 0 := by_omega
      have hdv := (dvd_succ_iff hok.1).mpr heven
      obtain ⟨c4, k4, e4, hk4, hw4, h19, k4r, hm4, hrr4, hrm4, ho4⟩ : ∃ c4 k4, Exec P W
          (block [.addN 160019 160021 160016, .loadN 160019 160019, .addN 160019 160010 160019])
          c2 c4 k4 ∧ k4 = 3 ∧ WordsBounded W c4 ∧ c4.nreg 160019 = x + 2 ^ ztbs ∧
          (∀ r, r ≠ 160019 → c4.nreg r = c2.nreg r) ∧ c4.nmem = c.nmem ∧
          c4.rreg = c.rreg ∧ c4.rmem = c.rmem ∧ c4.output = c.output := by
        have q21 : ztupg := by zuoli; omega
        have q16 : c2.nreg 160016 = g + 1 := by rw [k2r _ by_omega by_omega]; omega
        have q10 : c2.nreg 160010 = x := by zuoli; omega
        have mp : c2.nmem (PW + ztbs) = 2 ^ ztbs := by_grind
        have hp1 : 2 ^ ztbs ≤ 2 ^ lam := Nat.pow_le_pow_right by_norm_num by_omega
        exec_block
        · omega
        · config_simp; zunst; omega
        · refine ⟨rfl, by_omega, by config_simp; zunst, fun r a1 => ?_, hm2, hrr2,
            hrm2, ho2⟩
          zudi
          grind
      have fr4 : ∀ r, ¬ AscRG r → c4.nreg r = c.nreg r := fun r hr' => by
        unfold AscRG at hr'; rw [k4r r by_omega, fr2 r ztnf]
      have r11' : c4.nreg 160011 = b := by rw [fr4 _ ztnf]; omega
      by_cases hB : c4.nreg 160011 < c4.nreg 160019
      · zuimf
        obtain ⟨e5, hI5⟩ := stop c4 hw4 fr4 hm4 hrr4 hrm4 ho4
          (by zunpk; exact g2) (by zunpk; exact q2)
          (nextG_eq_of hgl hok (fun _ hg1 => by have := hg1.2; omega))
        refine ⟨_, _, .seq e1 (.ifLtN_true
          by_grind (.seq e2 (.ifLtN_false
          by_omega (.seq e4 (.ifLtN_true by_omega e5))))),
          hI5, ?_⟩
        simp only [Machine.upd_same,
          Machine.upd_other _ _ _ ztfci]
        rw [k4r _ by_omega, g2, hf]; omega
      · zuimf
        obtain ⟨c6, k6, e6, hk6, hw6, h12', h13', k6r, hm6, hrr6, hrm6, ho6⟩ : ∃ c6 k6, Exec P W
            ztkrt c4 c6 k6 ∧ k6 = 2 ∧
            WordsBounded W c6 ∧ c6.nreg 160012 = g + 1 ∧ c6.nreg 160013 = x / 2 ^ g / 2 ∧
            (∀ r, r ≠ 160012 → r ≠ 160013 → c6.nreg r = c4.nreg r) ∧ c6.nmem = c.nmem ∧
            c6.rreg = c.rreg ∧ c6.rmem = c.rmem ∧ c6.output = c.output := by
          have q17 : c4.nreg 160017 = x / 2 ^ g / 2 := by zunpk; omega
          have q16 : c4.nreg 160016 = g + 1 := by
            rw [k4r _ by_omega, k2r _ by_omega by_omega]; omega
          exec_block
          refine ⟨rfl, by_omega, by config_simp; omega, by config_simp; omega,
            fun r a1 a2 => ?_, hm4, hrr4, hrm4, ho4⟩
          zudi
          grind
        refine ⟨c6, _, .seq e1 (.ifLtN_true
          by_grind (.seq e2 (.ifLtN_false
          by_omega (.seq e4 (.ifLtN_false by_omega e6))))),
          ⟨fun r hr' => ?_, by_grind, by_grind, by_grind, by_grind,
            ?_, ?_, ?_, Or.inl ?_⟩, ?_⟩
        · unfold AscRG at hr'; rw [k6r r by_omega by_omega, fr4 r ztnf]
          exact hr r ztnf
        · omega
        · rw [h12']; exact ⟨hdv, by_omega⟩
        · rw [h13', h12', div_succ]
        · rw [k6r _ by_omega by_omega, k4r _ by_omega, k2r _ by_omega by_omega,
            k1 _ by_omega]; exact hf
        omega
  · zufna
    have fr1 : ztkox := fun r hr' => by
      unfold AscRG at hr'; grind
    obtain ⟨e3, hI3⟩ := stop c1 e1.wb_right fr1 rfl rfl rfl rfl
      by_rfl by_grind
      (nextG_eq_of hgl hok ztczk)
    refine ⟨_, _, .seq e1 (.ifLtN_false
      by_grind e3), hI3, ?_⟩
    simp only [Machine.upd_same,
      Machine.upd_other _ _ _ ztfci]
    rw [k1 _ by_omega, hf]; omega
set_option maxHeartbeats 4000000 in
/-- **The greedy grade on the RAM.** -/
theorem ascS_exec {c : Config} (hw : WordsBounded W c) {lam b x D PW : ℕ}
    (h10 : c.nreg 160010 = x) (h11 : c.nreg 160011 = b) (h26 : c.nreg 160026 = lam)
    (h24 : c.nreg 160024 = 1) (h20 : c.nreg 160020 = D) (h21 : c.nreg 160021 = PW)
    (hl : 1 ≤ lam) (hx : x < b)
    (hD : ∀ y, y ≤ b → c.nmem ztnki = y / 2)
    (hPW : ∀ i, i ≤ lam → c.nmem ztjlf = 2 ^ i)
    (hWD : D + b ≤ W) (hWP : PW + lam ≤ W) (hWx : b + 2 ^ lam ≤ W) :
    ∃ c' k, Exec P W ascS c c' k ∧ k ≤ 20 * lam + 30 ∧ WordsBounded W c' ∧
      c'.nreg 160012 = nextG lam b x ∧ c'.nreg 160013 = x / 2 ^ nextG lam b x ∧
      (∀ r, ¬ AscRG r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ascS
  obtain ⟨c1, k1, e1, hk1, hw1, hI1, hf1⟩ : ∃ c1 k1, Exec P W
      zthsi c c1 k1 ∧ k1 = 3 ∧
      WordsBounded W c1 ∧ AscInv lam b x c c1 ∧ c1.nreg 160025 = 0 := by
    exec_block
    all_goals try omega
    refine ⟨rfl, by_omega, ⟨fun r hr' => ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_, Or.inl ?_⟩, ?_⟩
    · zudi
      unfold AscRG at hr'
      simp_all
    · simp
    · config_simp; exact gradeOK_zero hx
    · simp_all
    · config_simp
    simp
  obtain ⟨c', k, e, ⟨hw', hI'⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := 160025) (b := 160024) (body := ascBody)
    (fun c' => WordsBounded W c' ∧ AscInv lam b x c c')
    (fun c' => 20 * ztife) ztbms
    (fun c2 ⟨hw2, hI2⟩ htest => by
      have r24 : ztizc := by rw [hI2.1 _ ztnf]; omega
      have hf : c2.nreg 160025 = 0 := by_omega
      obtain ⟨c3, k3, e3, hI3, hp⟩ := ascBody_exec (P := P) hw2 h10 h11 h26 h24 h20 h21 hD hPW
        hWD hWP hWx hI2 hf
      exact ⟨c3, k3, e3, ⟨e3.wb_right, hI3⟩, hp⟩) ⟨hw1, hI1⟩
  obtain ⟨hr', hm', hrr', hrm', ho', hgl', hok', hq', hfl'⟩ := hI'
  have r24 : c'.nreg 160024 = 1 := by rw [hr' _ ztnf]; omega
  rw [r24] at htest
  rcases hfl' with h0 | ⟨h1, hn⟩
  · omega
  refine ⟨c', k1 + k, .seq e1 e, ?_, hw', hn, by_simp_all, hr', hm', hrr', hrm', ho'⟩
  omega

/-- **A counted loop** (as `Cluster.forN`): `while i < n do body`, the body advancing the counter
register `ri` by one and keeping the bound register `rn`; cost `≤ (B + 2) (n - j₀) + 2`. -/
theorem forN {ri rn : ℕ} {body : Stmt} (I : ℕ → Config → Prop) (n B : ℕ)
    (hI : ∀ j c, I j c → WordsBounded W c ∧ c.nreg ri = j ∧ c.nreg rn = n)
    (hbody : ∀ j c, j < n → I j c → ∃ c' k, Exec P W body c c' k ∧ k ≤ B ∧ I ztl c')
    {j₀ : ℕ} {c : Config} (hc : I j₀ c) (hj₀ : j₀ ≤ n) :
    ∃ c' k, Exec P W zthqm c c' k ∧ k ≤ zthb * ztodq + 2 ∧ I n c' := by
  obtain ⟨c', k, e, ⟨j', hIj, hj'⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := ri) (b := rn) (body := body) ztijj
    ztyvy ztgiw
    (fun c ⟨j, h, hjn⟩ htest => by
      zujw

      have : ztxtm := by
        zuezq
      omega) ⟨j₀, hc, hj₀⟩
  grind
end proofs
def entB : Stmt := block [.addN 160016 160022 160012, .loadN 160016 160016,
  .addN 160016 160016 160013, .addN 160016 160016 160013, .addN 160016 160016 160013,
  .loadN 160017 160016, .addN 160018 160016 160024, .loadN 160018 160018]

/-- The record stores. -/
def recB : Stmt := block [.storeN 160015 160027,
  .addN 160019 160015 160024, .addN 160017 160017 160024, .loadN 160016 160017,
  .storeN 160019 160016,
  .addN 160019 160019 160024, .addN 160017 160017 160024, .loadN 160016 160017,
  .storeN 160019 160016,
  .addN 160019 160019 160024, .addN 160017 160017 160024, .loadN 160016 160017,
  .storeN 160019 160016,
  .addN 160019 160019 160024, .addN 160017 160017 160024, .loadN 160016 160017,
  .storeN 160019 160016,
  .addN 160019 160019 160024, .storeN 160019 160018]

/-- The advance. -/
def advB : Stmt := block [.addN 160015 160019 160024, .addN 160014 160014 160024,
  .addN 160016 160021 160012, .loadN 160016 160016, .addN 160010 160010 160016]

/-- One piece. -/
def coverBody : Stmt := .seq ascS (.seq entB (.seq recB advB))

/-- **The cover loop.** -/
def coverS : Stmt := .whileLtN 160010 160011 coverBody

/-- The registers written by `coverS`. -/
def CovRG (r : ℕ) : Prop := AscRG r ∨ r = 160010 ∨ r = 160014 ∨ r = 160015

/-- The record of piece `q` at slot `k`: host handle, the four descriptor words of the table
entry of chain `(q.1, q.2 / 2^q.1)`, its NF handle. -/
def RecAt (m m0 : ℕ → ℕ) (R hp T : ℕ) (q : ℕ × ℕ) (k : ℕ) : Prop :=
  m (R + 6 * k) = hp ∧
    (∀ j, 1 ≤ j → j ≤ 4 → m (R + 6 * k + j) =
      m0 (m0 (m0 zttdj + 3 * ztqux) + j)) ∧
    m (R + 6 * k + 5) = m0 (m0 zttdj + 3 * ztqux + 1)
section proofs
variable {P : Polygon} {W : ℕ}
variable {c : Config}
set_option maxHeartbeats 8000000 in
/-- The entry of chain `(g, q)`. -/
theorem entB_exec (hw : WordsBounded W c) {T g q : ℕ}
    (h22 : c.nreg 160022 = T) (h12 : c.nreg 160012 = g) (h13 : c.nreg 160013 = q)
    (h24 : c.nreg 160024 = 1)
    (hW1 : T + g ≤ W) (hW2 : c.nmem ztbps + 3 * q + 1 ≤ W) :
    ∃ c' k, Exec P W entB c c' k ∧ k = 8 ∧ WordsBounded W c' ∧
      c'.nreg 160017 = c.nmem (c.nmem ztbps + 3 * q) ∧
      c'.nreg 160018 = c.nmem (c.nmem ztbps + 3 * q + 1) ∧
      (∀ r, r ≠ 160016 → r ≠ 160017 → r ≠ 160018 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold entB
  exec_block
  all_goals try (config_simp; simp only [h22, h12, h13, h24]; omega)
  refine ⟨rfl, ‹_›, ?_, ?_, fun r a1 a2 a3 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; grind
  · config_simp; grind
  simp_all
set_option maxHeartbeats 16000000 in
/-- The record stores. -/
theorem recB_exec (hw : WordsBounded W c) {rp d nf hp : ℕ}
    (h15 : c.nreg 160015 = rp) (h17 : c.nreg 160017 = d) (h18 : c.nreg 160018 = nf)
    (h27 : c.nreg 160027 = hp) (h24 : c.nreg 160024 = 1)
    (hd : d + 4 < rp) (hW : rp + 6 ≤ W) :
    ∃ c' k, Exec P W recB c c' k ∧ k = 19 ∧ WordsBounded W c' ∧
      c'.nmem rp = hp ∧ (∀ j, 1 ≤ j → j ≤ 4 → c'.nmem (rp + j) = c.nmem ztfqu) ∧
      c'.nmem (rp + 5) = nf ∧ (∀ a, (a < rp ∨ rp + 6 ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.nreg 160019 = rp + 5 ∧
      (∀ r, r ≠ 160016 → r ≠ 160017 → r ≠ 160019 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold recB
  exec_block
  all_goals try (config_simp; simp only [h15, h17, h18, h27, h24]; omega)
  refine ⟨rfl, ‹_›, ?_, fun j hj1 hj4 => ?_, ?_, fun a ha => ?_, ?_, fun r a1 a2 a3 => ?_, rfl, rfl,
    rfl⟩
  · config_simp; simp only [h15, h17, h18, h27, h24, Machine.upd_apply]
    grind
  · interval_cases j <;>
    · config_simp; simp only [h15, h17, h18, h27, h24, Machine.upd_apply]
      grind
  · config_simp; simp only [h15, h17, h18, h27, h24, Machine.upd_apply]
    simp
  · config_simp; simp only [h15, h17, h18, h27, h24, Machine.upd_apply]
    grind
  · config_simp; omega
  · zudi
    grind
set_option maxHeartbeats 4000000 in
/-- The advance. -/
theorem advB_exec (hw : WordsBounded W c) {rp cnt PW g x : ℕ}
    (h19 : c.nreg 160019 = rp) (h14 : c.nreg 160014 = cnt) (h21 : c.nreg 160021 = PW)
    (h12 : c.nreg 160012 = g) (h10 : c.nreg 160010 = x) (h24 : c.nreg 160024 = 1)
    (hp : c.nmem (PW + g) = 2 ^ g) (hW1 : rp + 1 ≤ W) (hW2 : cnt + 1 ≤ W) (hW3 : PW + g ≤ W)
    (hW4 : x + 2 ^ g ≤ W) :
    ∃ c' k, Exec P W advB c c' k ∧ k = 5 ∧ WordsBounded W c' ∧
      c'.nreg 160015 = rp + 1 ∧ c'.nreg 160014 = cnt + 1 ∧ c'.nreg 160010 = x + 2 ^ g ∧
      (∀ r, r ≠ 160015 → r ≠ 160014 → r ≠ 160016 → r ≠ 160010 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold advB
  exec_block
  all_goals try (config_simp; simp only [h19, h14, h21, h12, h10, h24, hp]; omega)
  simp_all
structure CovRegs (c : Config) (lam b D PW T hp : ℕ) : Prop where
  r11 : c.nreg 160011 = b
  r26 : c.nreg 160026 = lam
  r24 : c.nreg 160024 = 1
  r20 : c.nreg 160020 = D
  r21 : c.nreg 160021 = PW
  r22 : c.nreg 160022 = T
  r27 : c.nreg 160027 = hp
theorem CovRegs.frame {c c' : Config} {lam b D PW T hp : ℕ} (h : CovRegs c lam b D PW T hp)
    (hr : ∀ r, ¬ CovRG r → c'.nreg r = c.nreg r) : CovRegs c' lam b D PW T hp := by
  zumt
  refine ztuv <;>
    (rw [hr _ ztiit]; assumption)

/-- The table facts read by the cover loop (in the memory `m0`, below `R₀`). -/
structure CovTab (m0 : ℕ → ℕ) (lam b D PW T R0 W : ℕ) : Prop where
  half : ∀ y, y ≤ b → m0 ztnki = y / 2
  pow : ∀ i, i ≤ lam → m0 ztjlf = 2 ^ i
  hD : D + b < R0
  hP : PW + lam < R0
  hT : T + lam ≤ R0
  ent : ∀ g, g ≤ lam - 1 → ∀ i, ztg * 2 ^ g ≤ b →
    m0 ztbps + 3 * i + 1 < R0 ∧ m0 ztxcq + 4 < R0
  wb : b + 2 ^ lam ≤ W
  wR : R0 + 12 * lam + 6 ≤ W
variable {c : Config}
set_option maxHeartbeats 8000000 in
/-- **One piece of the cover.** -/
theorem coverBody_exec (hw : WordsBounded W c) {lam b D PW T hp R0 x cnt : ℕ}
    {m0 : ℕ → ℕ} (hR : CovRegs c lam b D PW T hp) (hT : CovTab m0 lam b D PW T R0 W)
    (hl : 1 ≤ lam) (h10 : c.nreg 160010 = x) (hx : x < b) (h14 : c.nreg 160014 = cnt)
    (h15 : c.nreg 160015 = R0 + 6 * cnt) (hcnt : cnt + 1 ≤ 2 * lam)
    (hm : ∀ a, a < R0 → c.nmem a = m0 a) :
    ∃ c' k, Exec P W coverBody c c' k ∧ k ≤ 20 * lam + 70 ∧ WordsBounded W c' ∧
      c'.nreg 160010 = x + 2 ^ nextG lam b x ∧ c'.nreg 160014 = cnt + 1 ∧
      c'.nreg 160015 = R0 + 6 * ztbzu ∧
      RecAt c'.nmem m0 R0 hp T ztfie cnt ∧
      (∀ a, (a < R0 + 6 * cnt ∨ R0 + 6 * ztbzu ≤ a) → c'.nmem a = c.nmem a) ∧
      ztedj ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨r11, r26, r24, r20, r21, r22, r27⟩ := hR
  have hpl := Nat.one_le_two_pow (n := lam)
  -- the greedy grade
  obtain ⟨c1, k1, e1, hk1, hw1, h12, h13, fr1, hm1, hrr1, hrm1, ho1⟩ := ascS_exec (P := P) hw
    h10 r11 r26 r24 r20 r21 hl hx (fun y hy => by rw [hm _ (by have := hT.hD; omega)]; exact hT.half y hy)
    (fun i hi => by rw [hm _ (by have := hT.hP; omega)]; exact hT.pow i hi)
    (by have := hT.hD; have := hT.wR; omega) (by have := hT.hP; have := hT.wR; omega) hT.wb
  set g := nextG lam b x with hg
  have hok := nextG_spec (lam := lam) hx
  rw [← hg] at hok
  zudhp
  obtain ⟨i, hi⟩ := hok.1
  have hq : ztpqk := by rw [hi, Nat.mul_div_cancel_left _ by_positivity]
  have hib : ztg * 2 ^ g ≤ b := by have := hok.2; grind
  obtain ⟨he1, he2⟩ := hT.ent g hgl i hib
  have g1 : ztkox := fr1
  -- the entry
  obtain ⟨c2, k2, e2, hk2, hw2, h17, h18, fr2, hm2, hrr2, hrm2, ho2⟩ := entB_exec (P := P) hw1
    (T := T) (g := g) (q := i)
    ztyec h12 by_omega
    ztyec
    (by have := hT.hT; have := hT.wR; omega)
    (by rw [hm1, hm _ (by have := hT.hT; omega)]; have := hT.wR; omega)
  have eT : c1.nmem ztbps = m0 ztbps := by zvmxz; exact hm _ (by have := hT.hT; omega)
  have eE : c1.nmem ztxcq = m0 ztxcq := by
    grind
  have eF : c1.nmem ztxhd = m0 ztxhd := by
    grind
  rw [eT, eE] at h17; rw [eT, eF] at h18
  -- the record
  obtain ⟨c3, k3, e3, hk3, hw3, s0, sj, s5, sout, h19, fr3, hrr3, hrm3, ho3⟩ := recB_exec (P := P)
    hw2 (rp := R0 + 6 * cnt) (d := m0 ztxcq)
    (nf := m0 ztxhd) (hp := hp)
    ztwtr h17 h18
    ztwtr
    ztwtr
    by_omega (by have := hT.wR; omega)
  -- the advance
  obtain ⟨c4, k4, e4, hk4, hw4, a15, a14, a10, fr4, hm4, hrr4, hrm4, ho4⟩ := advB_exec (P := P)
    hw3 (rp := R0 + 6 * cnt + 5) (cnt := cnt) (PW := PW) (g := g) (x := x) h19
    (by rw [fr3 _ by_omega by_omega by_omega, fr2 _ by_omega by_omega by_omega,
      g1 _ ztnf]; omega)
    (by rw [fr3 _ by_omega by_omega by_omega, fr2 _ by_omega by_omega by_omega,
      g1 _ ztnf]; omega)
    by_grind
    (by rw [fr3 _ by_omega by_omega by_omega, fr2 _ by_omega by_omega by_omega,
      g1 _ ztnf]; omega)
    (by rw [fr3 _ by_omega by_omega by_omega, fr2 _ by_omega by_omega by_omega,
      g1 _ ztnf]; omega)
    (by rw [sout _ (by have := hT.hP; omega), hm2, hm1, hm _ (by have := hT.hP; omega)]
        exact hT.pow g by_omega)
    (by have := hT.wR; omega) (by have := hT.wR; omega) (by have := hT.hP; have := hT.wR; omega)
    (by have := hok.2; have := hT.wb; omega)
  refine ⟨c4, k1 + ztbqj, .seq e1 ztbal, by_omega, hw4, a10, a14,
    by omega, ⟨?_, fun j h1 h2 => ?_, ?_⟩, fun a ha => ?_, fun r hr => ?_,
    by grind, by_grind,
    by grind⟩
  · grind
  · simp only; rw [hq, hm4, sj j h1 h2, hm2, hm1, hm _ by_omega]
  · simp only; rw [hq, hm4]; exact s5
  · grind
  · unfold CovRG at hr
    rw [fr4 r by_omega by_omega ztbzl by_omega,
      fr3 r ztbzl ztbzl
        ztbzl,
      fr2 r ztbzl ztbzl
        ztbzl, g1 r by_tauto]
set_option maxHeartbeats 8000000 in
/-- **The cover loop.** -/
theorem coverS_exec (hw : WordsBounded W c) {lam b D PW T hp R0 a : ℕ}
    (hR : CovRegs c lam b D PW T hp) (hT : CovTab c.nmem lam b D PW T R0 W)
    (hl : 1 ≤ lam) (h10 : c.nreg 160010 = a) (_hab : a ≤ b) (hb : b - a ≤ 2 ^ lam)
    (h14 : c.nreg 160014 = 0) (h15 : c.nreg 160015 = R0) :
    ∃ c' k, Exec P W coverS c c' k ∧ k ≤ ztelf * ztnff + 2 ∧
      WordsBounded W c' ∧ c'.nreg 160014 = (cover lam b a).length ∧
      c'.nreg 160015 = R0 + 6 * (cover lam b a).length ∧
      (∀ k, k < (cover lam b a).length →
        RecAt c'.nmem c.nmem R0 hp T ztxdd k) ∧
      (∀ x, (x < R0 ∨ R0 + 6 * (cover lam b a).length ≤ x) → c'.nmem x = c.nmem x) ∧
      ztedj ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hlen := cover_length_le (b := b) (x := a) hl hb
  set L := cover lam b a with hL
  let I : Config → Prop := fun c' => WordsBounded W c' ∧ ztedj ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
    ∃ x Wd, c'.nreg 160010 = x ∧ Wd ++ cover lam b x = L ∧ c'.nreg 160014 = Wd.length ∧
      c'.nreg 160015 = R0 + 6 * Wd.length ∧
      (∀ k, k < Wd.length → RecAt c'.nmem c.nmem R0 hp T (Wd.getD k ztdr) k) ∧
      (∀ y, (y < R0 ∨ R0 + 6 * Wd.length ≤ y) → c'.nmem y = c.nmem y)
  obtain ⟨c', k, e, ⟨hw', hr', hrr', hrm', ho', x, Wd, hx, hWd, h14', h15', hrec, hout⟩, htest,
      hk⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 160010) (b := 160011)
    (body := coverBody) I
    (fun c' => ztelf * (cover lam b (c'.nreg 160010)).length) ztbms
    (fun c2 ⟨hw2, hr2, hrr2, hrm2, ho2, x, Wd, hx, hWd, h14, h15, hrec, hout⟩ htest => by
      have hR2 : CovRegs c2 lam b D PW T hp := hR.frame hr2
      rw [hx, hR2.r11] at htest
      have hWl : Wd.length + 1 ≤ 2 * lam := by
        have := congrArg List.length hWd
        rw [List.length_append, cover_of_lt htest, List.length_cons] at this
        omega
      obtain ⟨c3, k3, e3, hk3, hw3, a10, a14, a15, hr3, hout3, fr3, hrr3, hrm3, ho3⟩ :=
        coverBody_exec (P := P) hw2 hR2 hT hl hx htest h14 h15 hWl
          (fun y hy => hout y (Or.inl hy))
      refine ⟨c3, k3, e3, ⟨hw3, fun r hr => by_simp_all, by_simp_all,
        by simp_all, by_simp_all, x + 2 ^ nextG lam b x,
        Wd ++ [ztfie], a10, ?_, by_simp_all, by_simp_all,
        fun k hk => ?_, fun y hy => ?_⟩, ?_⟩
      · rw [List.append_assoc, List.singleton_append, ← cover_of_lt htest]; omega
      · zuhpg
        rcases Nat.lt_or_ge k Wd.length with h | h
        · obtain ⟨b0, b1, b2⟩ := hrec k h
          zuhjw
          refine ⟨by_grind, fun j h1 h2 => ?_, ?_⟩
          · grind
          grind
        · have hk' : k = Wd.length := by_omega
          simp_all
      · grind
      · rw [a10, hx]
        have e := cover_of_lt (lam := lam) htest
        have hl2 : (cover lam b x).length = (cover lam b zteay).length + 1 := by
          simp_all
        rw [hl2, Nat.mul_add, Nat.mul_one]
        omega)
    ⟨hw, fun r _ => rfl, rfl, rfl, rfl, a, [], h10, by_rfl, by_omega, by_omega,
      fun k hk => by_simp_all, fun y _ => rfl⟩
  have hR' : CovRegs c' lam b D PW T hp := hR.frame hr'
  rw [hx, hR'.r11] at htest
  have hWL : Wd = L := by rw [← hWd, cover_of_ge by_omega, List.append_nil]
  subst hWL
  refine ⟨c', k, e, ?_, hw', h14', h15', hrec, hout, hr', hrr', hrm', ho'⟩
  rw [h10] at hk
  have : ztelf * (cover lam b a).length ≤ ztelf * ztnff :=
    Nat.mul_le_mul_left _ hlen
  grind
end proofs
end
end Chazelle.Core.L41
namespace Chazelle
namespace EarClip
open Machine Machine.Stmt Programs
@[expose] public section
def cyc (l : List ℕ) (q : ℕ) : ℕ := l.getD (q % l.length) 0

/-! ### The determinant kernel -/

/-- `rreg dst := det (rreg a1, rreg a2) (rreg v1, rreg v2) (rreg b1, rreg b2)`, with scratch
registers `t1`, `t2`:
`t1 := v1 - a1; t2 := b2 - a2; t1 := t1 * t2; t2 := b1 - a1; dst := v2 - a2; t2 := t2 * dst;
dst := t1 - t2`.  Exactly `7` instructions. -/
def detInto (dst t1 t2 a1 a2 v1 v2 b1 b2 : ℕ) : Stmt :=
  block [.subR t1 v1 a1, .subR t2 b2 a2, .mulR t1 t1 t2, .subR t2 b1 a1, .subR dst v2 a2,
    .mulR t2 t2 dst, .subR dst t1 t2]
set_option linter.unusedSimpArgs false in
/-- **Spec lemma for `detInto`.**  With `dst`, `t1`, `t2` pairwise distinct and distinct from
the six input registers: cost `≤ 7` (the code is straight-line, so exactly `7`); `rreg dst` receives the determinant; real registers
other than `dst, t1, t2`, all natural registers, both memories and the output are unchanged. -/
theorem detInto_exec {P : Polygon} {W : ℕ} (dst t1 t2 a1 a2 v1 v2 b1 b2 : ℕ)
    (hdt1 : dst ≠ t1) (hdt2 : dst ≠ t2) (ht12 : t1 ≠ t2)
    (hin : ∀ r, r = a1 ∨ r = a2 ∨ r = v1 ∨ r = v2 ∨ r = b1 ∨ r = b2 →
      r ≠ dst ∧ r ≠ t1 ∧ r ≠ t2)
    (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W (detInto dst t1 t2 a1 a2 v1 v2 b1 b2) c c' k ∧ k ≤ 7 ∧
      c'.rreg dst = det ztjso (c.rreg v1, c.rreg v2) ztjsp ∧
      (∀ r, r ≠ dst → r ≠ t1 → r ≠ t2 → c'.rreg r = c.rreg r) ∧
      c'.nreg = c.nreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨ha1d, ha1t1, ha1t2⟩ := hin a1 by_simp
  obtain ⟨ha2d, ha2t1, ha2t2⟩ := hin a2 by_simp
  obtain ⟨hv1d, hv1t1, hv1t2⟩ := hin v1 by_simp
  obtain ⟨hv2d, hv2t1, hv2t2⟩ := hin v2 by_simp
  obtain ⟨hb1d, hb1t1, hb1t2⟩ := hin b1 by_simp
  obtain ⟨hb2d, hb2t1, hb2t2⟩ := hin b2 by_simp
  unfold detInto
  exec_block
  refine ⟨by_omega, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp [hdt1, hdt2, ht12, hdt1.symm, hdt2.symm, ht12.symm, ha1d, ha1t1, ha1t2, ha2d, ha2t1,
      ha2t2, hv1d, hv1t1, hv1t2, hv2d, hv2t1, hv2t2, hb1d, hb1t1, hb1t2, hb2d, hb2t1, hb2t2, det]
  · zuete
    zubmk

/-! ### The constant `1/2` -/
end
end EarClip
end Chazelle
namespace Chazelle
namespace Exec
open Std
@[expose] public section
noncomputable def castPt (p : ℚ × ℚ) : Point := ((p.1 : ℝ), (p.2 : ℝ))

/-- Embed a rational polygon into the real plane. -/
noncomputable def castPoly (Pq : QPolygon) : Polygon := ⟨Pq.map castPt⟩

/-- Embed a rational configuration into a real one (absent keys read as `0`). -/
noncomputable def castConfig (c : QConfig) : Config where
  pc := c.pc
  nreg := fun i => c.nr i
  rreg := fun i => (c.rr i : ℝ)
  nmem := fun i => c.nm i
  rmem := fun i => (c.rm i : ℝ)
  output := c.output
