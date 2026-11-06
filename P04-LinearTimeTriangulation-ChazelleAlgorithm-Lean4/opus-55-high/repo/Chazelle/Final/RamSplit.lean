module

public import Chazelle.MacT
public import Chazelle.Core.SweepIoQry
public import Chazelle.Core.ClusterEulerRam
public import Chazelle.Programs.Tactics
public import Chazelle.Core.FactsAttach
public import Mathlib.Data.List.GetD
public import Chazelle.Core.SpecNF
public import Chazelle.Core.TopIdx

namespace Chazelle.Final
open Machine Machine.Stmt Programs
open Chazelle.EarClip (detInto detInto_exec)
@[expose] public section
def Chain (mem : ℕ → ℕ) (SB : ℕ) : ℕ → List ℕ → Prop
  | e, [] => e = 0
  | e, z :: l => e = z + 1 ∧ Chain mem SB (mem zthcn) l

/-- A chain only depends on the sibling entries of its members. -/
theorem chain_congr {mem mem' : ℕ → ℕ} {SB : ℕ} :
    ∀ {e : ℕ} {l : List ℕ}, (∀ z ∈ l, mem' zthcn = mem zthcn) →
      Chain mem SB e l → Chain mem' SB e l
  | _, [], _, h => h
  | _, z :: l, hs, ⟨h1, h2⟩ => ⟨h1, by
      rw [hs z List.mem_cons_self]
      exact chain_congr by_simp_all h2⟩

/-- A chain is determined by its start. -/
theorem chain_unique {mem : ℕ → ℕ} {SB : ℕ} :
    ∀ {e : ℕ} {l l' : List ℕ}, Chain mem SB e l → Chain mem SB e l' → l = l'
  | _, [], [], _, _ => rfl
  | _, [], _ :: _, h, h' => by
      zugzb
  | _, _ :: _, [], h, h' => by
      zugzb
  | _, z :: l, z' :: l', ⟨h1, h2⟩, ⟨h1', h2'⟩ => by
      have hz : z = z' := by_omega
      subst hz
      rw [chain_unique h2 h2']

/-- **The memory holds the structure**: the `vtx`, `nxt`, `prv` bands agree with `S` on the
nodes, and the copy lists of the vertices `< n` are chained through the `sib` band from the
`head` band. -/
structure MemRel (mem : ℕ → ℕ) (B NN n : ℕ) (S : LState) : Prop where
  vtx : ∀ z < S.cnt, mem ztjgr = S.vtx z
  nxt : ∀ z < S.cnt, mem ztgdb = S.nxt z
  prv : ∀ z < S.cnt, mem ztels = S.prv z
  cop : ∀ v < n, Chain mem ztcsv (mem ztgzu) ztqcm

/-! ### The wedge test -/

/-- Reading the corner of `node = nreg 124` and the target `w = nreg 125`: the coordinates of
`vtx (prv node)` into `rreg 101, 102`, of `vtx node` into `rreg 103, 104`, of
`vtx (nxt node)` into `rreg 105, 106`, of `w` into `rreg 107, 108`.  Exactly `18`
instructions. -/
def wedgeReadStmt : Stmt :=
  block [.addN 129 107 124, .loadN 130 129, .addN 129 105 130, .loadN 130 129,
    .readX 101 130, .readY 102 130,
    .addN 129 105 124, .loadN 130 129, .readX 103 130, .readY 104 130,
    .addN 129 106 124, .loadN 130 129, .addN 129 105 130, .loadN 130 129,
    .readX 105 130, .readY 106 130, .readX 107 125, .readY 108 125]

/-- The three determinants `D = rreg 109`, `L₁ = rreg 110`, `L₂ = rreg 111`, their products
with `σ = rreg 100` into `rreg 114, 115, 116`, and `flag := 0`. -/
def wedgeDetStmt : Stmt :=
  .seq (detInto 109 112 113 101 102 103 104 105 106)
    (.seq (detInto 110 112 113 101 102 103 104 107 108)
      (.seq (detInto 111 112 113 103 104 105 106 107 108)
        (block [.mulR 114 100 109, .mulR 115 100 110, .mulR 116 100 111, .constN 127 0])))

/-- `flag := 1`. -/
def setFlag : Stmt := .instr (.constN 127 1)

/-- The sign logic of `wedgeSign` (with `rreg 117 = 0`). -/
def wedgeLogic : Stmt :=
  .ifLtR 117 114 (.ifLtR 117 115 ztjdm .skip)
    (.ifLtR 114 117 (.ifLtR 117 115 setFlag ztjdm)
      ztjdm)

/-- **The wedge test on the RAM**: `flag = nreg 127` becomes `1` iff the node `nreg 124` passes
the wedge test towards the vertex `nreg 125`. -/
def wedgeStmt : Stmt := .seq wedgeReadStmt (.seq wedgeDetStmt wedgeLogic)
section Wedge
variable {P : Polygon} {W : ℕ}
set_option hygiene false
local macro "zqks" : tactic => `(tactic| refine spec_ifLtR_true by_simp_all ?_)
local macro "zqkt" : tactic => `(tactic| (refine spec_ifLtR_false by_simp_all ztoic; simp_all))
local macro "zqkz" : tactic => `(tactic| obtain ⟨c', k, ex, hk, hf, hr⟩ := hset 2)
set_option hygiene true
variable (c : Config)
/-- Spec of the sign logic of the wedge test. -/
theorem wedgeLogic_exec (hc : WordsBounded W c) (h1 : 1 ≤ W)
    (h117 : c.rreg 117 = 0) (h127 : c.nreg 127 = 0) :
    ∃ c' k, Exec P W wedgeLogic c c' k ∧ k ≤ 8 ∧
      (wedgeSign 1 ztvkb ztvkc ztvkd → c'.nreg 127 = 1) ∧
      (¬ wedgeSign 1 ztvkb ztvkc ztvkd → c'.nreg 127 = 0) ∧
      ztiuz ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hset : ∀ K, ∃ c' k, Exec P W setFlag c c' k ∧ k + K ≤ K + 1 ∧ c'.nreg 127 = 1 ∧
      ztiuz ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := fun K =>
    ⟨_, 1, Exec.constN hc 127 1 h1, by_omega, by_simp, by_simp_all, rfl, rfl, rfl,
      rfl⟩
  unfold wedgeLogic wedgeSign
  simp only [one_mul]
  by_cases hD : c.rreg 117 < c.rreg 114
  · zukrr
    zqks
    rw [ite_eq_left hD]
    zuirk
    · zqks
      zueoc
      · zqks
        zqkz
        grind
      · zqkt
    · zqkt
  · zukrr
    zupb
    rw [ite_eq_right hD]
    by_cases hD' : c.rreg 114 < 0
    · zqks
      rw [ite_eq_left hD']
      zuirk
      · zqks
        zqkz
        grind
      · zupb
        zueoc
        · zqks
          obtain ⟨c', k, ex, hk, hf, hr⟩ := hset 5
          grind
        · zqkt
    · zupb
      rw [ite_eq_right hD']
      zueoc
      · zqks
        obtain ⟨c', k, ex, hk, hf, hr⟩ := hset 4
        grind
      · zqkt

/-- The wedge test in terms of the three signed determinants. -/
theorem wedgeTest_iff_sign (σ : ℝ) (p a q x : Point) :
    wedgeTest σ p a q x ↔ wedgeSign 1 (σ * det p a q) (σ * det p a x) (σ * det a q x) := by
  unfold wedgeTest wedgeSign; simp

/-- **Spec of the wedge test.**  With the node `nreg 124`, the target vertex `nreg 125`, the
bases `nreg 105 = VB`, `nreg 106 = NB`, `nreg 107 = PB` and `rreg 117 = 0`: cost `≤ 55`; the
flag `nreg 127` is `1` iff the target passes the `σ = rreg 100` wedge test at the corner
`vtx[prv node] → vtx[node] → vtx[nxt node]`, else `0`; only `nreg 127, 129, 130` and
`rreg 101 … 116` change. -/
theorem wedgeStmt_exec (hc : WordsBounded W c) (h1 : 1 ≤ W)
    (h117 : c.rreg 117 = 0)
    (hA1 : c.nreg 107 + c.nreg 124 ≤ W)
    (hA2 : c.nreg 105 + c.nmem (c.nreg 107 + c.nreg 124) ≤ W)
    (hA3 : c.nreg 105 + c.nreg 124 ≤ W)
    (hA4 : c.nreg 106 + c.nreg 124 ≤ W)
    (hA5 : c.nreg 105 + c.nmem (c.nreg 106 + c.nreg 124) ≤ W) :
    ∃ c' k, Exec P W wedgeStmt c c' k ∧ k ≤ 55 ∧
      (wedgeTest ztvka ztbsd
          ztbyv
          ztbsc
          ztgen → c'.nreg 127 = 1) ∧
      (¬ wedgeTest ztvka ztbsd
          ztbyv
          ztbsc
          ztgen → c'.nreg 127 = 0) ∧
      (∀ r, r ≠ 127 → r ≠ 129 → r ≠ 130 → c'.nreg r = c.nreg r) ∧
      ztxbr ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold wedgeStmt wedgeReadStmt wedgeDetStmt
  refine spec_seq ?_
  exec_block
  zulcy
  refine spec_seq (spec_seq (spec_use (detInto_exec 109 112 113 101 102 103 104 105 106
    by_decide by_decide by_decide
    by_grind _ ‹_›) ?_))
  rintro c₁ k₁ hk₁ hw₁ ⟨hD, hfr₁, hn₁, hnm₁, hrm₁, hout₁⟩
  refine spec_seq (spec_use (detInto_exec 110 112 113 101 102 103 104 107 108
    by_decide by_decide by_decide
    by_grind _ hw₁) ?_)
  rintro c₂ k₂ hk₂ hw₂ ⟨hL1, hfr₂, hn₂, hnm₂, hrm₂, hout₂⟩
  refine spec_seq (spec_use (detInto_exec 111 112 113 103 104 105 106 107 108
    by_decide by_decide by_decide
    by_grind _ hw₂) ?_)
  rintro c₃ k₃ hk₃ hw₃ ⟨hL2, hfr₃, hn₃, hnm₃, hrm₃, hout₃⟩
  exec_block
  · omega
  refine spec_use (wedgeLogic_exec _ ‹_› h1 ?_ ?_) ?_
  · config_simp
    rw [hfr₃ 117 by_decide by_decide by_decide, hfr₂ 117 by_decide by_decide by_decide,
      hfr₁ 117 by_decide by_decide by_decide]
    tauto
  · config_simp
  rintro c₄ k₄ hk₄ hw₄ ⟨hy, hn, hnfr, hr₄, hnm₄, hrm₄, hout₄⟩
  config_simp at hy
  config_simp at hn
  -- the real registers after the three determinants
  have e : ∀ r, (r < 101 ∨ 108 < r) → r ≠ 109 → r ≠ 110 → r ≠ 111 → r ≠ 112 → r ≠ 113 →
      c₃.rreg r = c.rreg r := by
    intro r hr h9 h10 h11 h12 h13
    rw [hfr₃ r h11 h12 h13, hfr₂ r h10 h12 h13, hfr₁ r h9 h12 h13]
    config_simp
    simp [show r ≠ 101 by omega, show r ≠ 102 by omega, show r ≠ 103 by omega,
      show r ≠ 104 by omega, show r ≠ 105 by omega, show r ≠ 106 by omega, show r ≠ 107 by omega,
      show r ≠ 108 by omega]
  have e100 : c₃.rreg 100 = c.rreg 100 := by_grind
  have eD : c₃.rreg 109 = det ztbsd
      ztbyv
      ztbsc := by
    rw [hfr₃ 109 by_decide by_decide by_decide, hfr₂ 109 by_decide by_decide by_decide,
      hD]
    config_simp
  have eL1 : c₃.rreg 110 = det ztbsd
      ztbyv ztgen := by
    rw [hfr₃ 110 by_decide by_decide by_decide, hL1, hfr₁ 101 by_decide by_decide
      by_decide, hfr₁ 102 by_decide by_decide by_decide, hfr₁ 103 by_decide by_decide
      by_decide, hfr₁ 104 by_decide by_decide by_decide, hfr₁ 107 by_decide by_decide
      by_decide, hfr₁ 108 by_decide by_decide by_decide]
    config_simp
  have eL2 : c₃.rreg 111 = det ztbyv
      ztbsc ztgen := by
    rw [hL2, hfr₂ 103 by_decide by_decide by_decide, hfr₂ 104 by_decide by_decide
      by_decide, hfr₂ 105 by_decide by_decide by_decide, hfr₂ 106 by_decide by_decide
      by_decide, hfr₂ 107 by_decide by_decide by_decide, hfr₂ 108 by_decide by_decide
      by_decide, hfr₁ 103 by_decide by_decide by_decide, hfr₁ 104 by_decide by_decide
      by_decide, hfr₁ 105 by_decide by_decide by_decide, hfr₁ 106 by_decide by_decide
      by_decide, hfr₁ 107 by_decide by_decide by_decide, hfr₁ 108 by_decide by_decide
      by_decide]
    config_simp
  rw [eD, eL1, eL2, e100, ← wedgeTest_iff_sign] at hy hn
  refine ⟨by_omega, hy, hn, fun r h127 h129 h130 => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [hnfr r h127]
    config_simp
    rw [Machine.upd_other _ _ _ h127, hn₃, hn₂, hn₁]
    config_simp
    simp [h129, h130]
  · rw [congrFun hr₄ r]
    config_simp
    rw [Machine.upd_other _ _ _ by_grind, Machine.upd_other _ _ _ by_grind,
      Machine.upd_other _ _ _ by_grind]
    exact e r by_omega by_omega by_omega by_omega by_omega by_omega
  · grind
  · grind
  grind
end Wedge

/-! ### Finding the copy -/

/-- The body of the copy scan: `node := e - 1; wedge; if 0 < flag then res := node;
e := sib[node]`. -/
def findBody : Stmt :=
  .seq (.instr (.subN 124 123 113))
    (.seq wedgeStmt (.seq ztipi
      (block [.addN 129 108 124, .loadN 123 129])))

/-- The copy scan: `while 0 < e do findBody`. -/
def findLoop : Stmt := .whileLtN 112 123 findBody

/-- **Find the copy** of the vertex `v = nreg 128` passing the wedge test towards the vertex
`w = nreg 125`: `res := 0; e := head[v]; findLoop`; the result is in `nreg 126`. -/
def findStmt : Stmt := .seq (block [.constN 126 0, .addN 129 109 128, .loadN 123 129]) findLoop
open Classical in
/-- The wedge predicate of the scan, as a Boolean. -/
noncomputable def wedgeP (P : Polygon) (σ : ℝ) (S : LState) (w : ℕ) : ℕ → Bool :=
  fun z => decide ztpcu
open Classical in
/-- The Boolean wedge predicate. -/
theorem wedgeP_eq_true {P : Polygon} {σ : ℝ} {S : LState} {w z : ℕ} :
    wedgeP P σ S w z = true ↔ nodeWedge P σ S z w := by
  unfold wedgeP; simp

/-- The standing hypotheses of the scan on a configuration: the band bases, the constants, the
orientation, the memory relation, closure, and the address bound. -/
structure ScanHyp (P : Polygon) (W B NN n : ℕ) (σ : ℝ) (S : LState) (c : Config) : Prop where
  r105 : c.nreg 105 = B
  r106 : c.nreg 106 = B + NN
  r107 : c.nreg 107 = B + 2 * NN
  r108 : c.nreg 108 = B + 3 * NN
  r109 : c.nreg 109 = B + 4 * NN
  r112 : c.nreg 112 = 0
  r113 : c.nreg 113 = 1
  s100 : c.rreg 100 = σ
  s117 : c.rreg 117 = 0
  mem : MemRel c.nmem B NN n S
  closed : Closed S n
  cntNN : S.cnt ≤ NN
  addr : B + 4 * NN + n ≤ W

/-- The scan hypotheses only depend on the registers and memory they mention. -/
theorem ScanHyp.congr {P : Polygon} {W B NN n : ℕ} {σ : ℝ} {S : LState} {c c' : Config}
    (h : ScanHyp P W B NN n σ S c)
    (hn : ∀ r, r = 105 ∨ r = 106 ∨ r = 107 ∨ r = 108 ∨ r = 109 ∨ r = 112 ∨ r = 113 →
      c'.nreg r = c.nreg r)
    (hr : c'.rreg 100 = c.rreg 100 ∧ c'.rreg 117 = c.rreg 117) (hm : c'.nmem = c.nmem) :
    ScanHyp P W B NN n σ S c' where
  r105 := by rw [hn 105 by_simp]; exact h.r105
  r106 := by rw [hn 106 by_simp]; exact h.r106
  r107 := by rw [hn 107 by_simp]; exact h.r107
  r108 := by rw [hn 108 by_simp]; exact h.r108
  r109 := by rw [hn 109 by_simp]; exact h.r109
  r112 := by rw [hn 112 by_simp]; exact h.r112
  r113 := by rw [hn 113 by_simp]; exact h.r113
  s100 := by rw [hr.1]; exact h.s100
  s117 := by rw [hr.2]; exact h.s117
  mem := by zvmwi; exact h.mem
  closed := h.closed
  cntNN := h.cntNN
  addr := h.addr
section Find
variable {P : Polygon} {W B NN n : ℕ} {σ : ℝ} {S : LState}

/-- The invariant of the scan for the vertex `v` towards `w`, relative to the entry
configuration `c₀`. -/
def FindInv (P : Polygon) (W B NN n : ℕ) (σ : ℝ) (S : LState) (v w : ℕ) (c₀ c : Config) :
    Prop :=
  WordsBounded W c ∧ ScanHyp P W B NN n σ S c ∧ c.nreg 125 = w ∧
    (∀ r, r ≠ 123 → r ≠ 124 → r ≠ 126 → r ≠ 127 → r ≠ 129 → r ≠ 130 → c.nreg r = c₀.nreg r) ∧
    ztybs ∧
    c.nmem = c₀.nmem ∧ c.rmem = c₀.rmem ∧ c.output = c₀.output ∧
    ∃ done rest, S.cop v = done ++ rest ∧ Chain c.nmem ztcsv ztqhm rest ∧
      c.nreg 126 = selectLast (wedgeP P σ S w) done 0
open Classical in
/-- The measure of the scan: the length of the remaining chain. -/
noncomputable def chainLen (mem : ℕ → ℕ) (SB e : ℕ) : ℕ :=
  if h : ∃ l, Chain mem SB e l then (Classical.choose h).length else 0

/-- The measure of a chain is its length. -/
theorem chainLen_eq {mem : ℕ → ℕ} {SB e : ℕ} {l : List ℕ} (h : Chain mem SB e l) :
    chainLen mem SB e = l.length := by
  have hex : ∃ l, Chain mem SB e l := by_grind
  unfold chainLen
  rw [dite_eq_left hex, chain_unique (Classical.choose_spec hex) h]
variable {v w : ℕ}
/-- One iteration of the scan. -/
theorem findBody_inv {c₀ c : Config} (hI : FindInv P W B NN n σ S v w c₀ c)
    (ht : c.nreg 112 < c.nreg 123) :
    ∃ c' k, Exec P W findBody c c' k ∧ FindInv P W B NN n σ S v w c₀ c' ∧ k ≤ 60 ∧
      chainLen c₀.nmem ztcsv (c'.nreg 123) < chainLen c₀.nmem ztcsv ztqhm := by
  classical
  obtain ⟨hw, hH, h125, hfn, hfr, hnm, hrm, hout, done, rest, hsplit, hchain, hres⟩ := hI
  rw [hH.r112] at ht
  obtain ⟨z, rest', rfl⟩ : ztmxv := by
    cases rest with
    | nil => simp only [Chain] at hchain; omega
    | cons z rest' => exact by_simp_all
  zuico
  have hzmem : z ∈ S.cop v := by_simp_all
  have hz : z < S.cnt := hH.closed.cop v z hzmem
  have hpz := hH.closed.prv z hz
  have hnz := hH.closed.nxt z hz
  have hcnt := hH.cntNN
  zuixl
  zudk
  unfold findBody
  refine spec_seq (spec_instr (Exec.subN hw 124 123 113) fun hw₁ => ?_)
  have hH₁ := hH.congr
    (fun r hr => by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) by_simp_all rfl
  have hnode : c.nreg 123 - c.nreg 113 = z := by rw [hH.r113, he]; omega
  refine spec_seq (spec_use (wedgeStmt_exec _ hw₁ hW1 hH₁.s117 ?_ ?_ ?_ ?_ ?_) ?_)
  · config_simp; rw [hnode, hH.r107]; omega
  · config_simp; rw [hnode, hH.r107, hH.r105, hH.mem.prv z hz]; omega
  · config_simp; rw [hnode, hH.r105]; omega
  · config_simp; rw [hnode, hH.r106]; omega
  · config_simp; rw [hnode, hH.r106, hH.r105, hH.mem.nxt z hz]; omega
  rintro c₂ k₂ hk₂ hw₂ ⟨hyes, hno, hfn₂, hfr₂, hnm₂, hrm₂, hout₂⟩
  config_simp at hyes
  config_simp at hno
  rw [hnode, hH.r105, hH.r106, hH.r107, hH.mem.prv z hz, hH.mem.nxt z hz,
    hH.mem.vtx _ hpz, hH.mem.vtx _ hnz, hH.mem.vtx z hz, hH.s100, h125] at hyes hno
  have h112₂ : c₂.nreg 112 = 0 := by
    rw [hfn₂ 112 by_decide by_decide by_decide]; config_simp; exact hH.r112
  have h124₂ : c₂.nreg 124 = z := by
    rw [hfn₂ 124 by_decide by_decide by_decide]; tauto
  -- the conditional update of the result
  have hcond : ∃ c₃ k₃, Exec P W ztipi c₂ c₃ k₃ ∧
      k₃ ≤ 2 ∧ c₃.nreg 126 = (if wedgeP P σ S w z then z else c.nreg 126) ∧
      (∀ r, r ≠ 126 → c₃.nreg r = c₂.nreg r) ∧ c₃.rreg = c₂.rreg ∧ c₃.nmem = c₂.nmem ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    by_cases hp : nodeWedge P σ S z w
    · have h127 := hyes hp
      refine spec_ifLtN_true by_omega
        (spec_instr (Exec.copyN hw₂ 126 124) fun _ => ?_)
      refine ztcfp
      rw [ite_eq_left (wedgeP_eq_true.2 hp)]; tauto
    · have h127 := hno hp
      refine spec_ifLtN_false by_omega (spec_skip hw₂ ?_)
      refine ⟨by_omega, ?_, by_omega, rfl, rfl, rfl, rfl⟩
      rw [ite_eq_right (fun h => hp (wedgeP_eq_true.1 h)), hfn₂ 126 by_decide by_decide by_decide]
      config_simp
  refine spec_seq ztuau
  rintro c₃ k₃ hk₃ hw₃ ⟨hres₃, hfn₃, hfr₃, hnm₃, hrm₃, hout₃⟩
  have h108₃ : c₃.nreg 108 = B + 3 * NN := by
    rw [hfn₃ 108 by_decide, hfn₂ 108 by_decide by_decide by_decide]
    config_simp; exact hH.r108
  have h124₃ : c₃.nreg 124 = z := by_grind
  zukdr
  exec_block
  · omega
  have e1 : chainLen c₀.nmem ztcsv (c.nmem ztdff) = rest'.length :=
    chainLen_eq by_grind
  have e2 : chainLen c₀.nmem ztcsv ztqhm = rest'.length + 1 := by
    zueli
  refine ⟨?_, by_omega, ?_⟩
  · refine ⟨by_omega, hH.congr ztez ztcp ?_, ?_, fun r h123 h124 h126 h127 h129 h130 => ?_,
      fun r hr => ?_, ?_, ?_, ?_, done ++ [z], rest', by_grind, ?_, ?_⟩
    · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · config_simp
        rw [hfn₃ _ by_decide, hfn₂ _ by_decide by_decide by_decide]
        config_simp
    · grind
    · grind
    · omega
    · config_simp
      rw [hfn₃ 125 by_decide, hfn₂ 125 by_decide by_decide by_decide]
      tauto
    · config_simp
      rw [Machine.upd_other _ _ _ h123, Machine.upd_other _ _ _ h129, hfn₃ r h126,
        hfn₂ r h127 h129 h130]
      config_simp
      rw [Machine.upd_other _ _ _ h124]
      grind
    · grind
    · grind
    · grind
    · grind
    · config_simp
      grind
    · config_simp
      rw [hres₃, hres, selectLast_append, selectLast_cons, selectLast_nil]
  · config_simp
    grind

/-- **Spec of the copy scan.**  Under the scan hypotheses, with `nreg 128 = v < n` and
`nreg 125 = w`: cost `≤ 62 * (S.cop v).length + 5`, and `nreg 126 = findCopy P σ S v w`; only
`nreg 123, 124, 126, 127, 129, 130` and `rreg 101 … 116` change. -/
theorem findStmt_exec (c : Config) (hc : WordsBounded W c)
    (hH : ScanHyp P W B NN n σ S c) (hv : c.nreg 128 = v) (hvn : v < n) (h125 : c.nreg 125 = w) :
    ∃ c' k, Exec P W findStmt c c' k ∧ k ≤ 62 * (S.cop v).length + 5 ∧
      c'.nreg 126 = findCopy P σ S v w ∧ ScanHyp P W B NN n σ S c' ∧
      (∀ r, r ≠ 123 → r ≠ 124 → r ≠ 126 → r ≠ 127 → r ≠ 129 → r ≠ 130 → c'.nreg r = c.nreg r) ∧
      ztxbr ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuixl
  unfold findStmt findLoop
  refine spec_seq ?_
  exec_block
  · omega
  · config_simp; zuopy; omega
  set c₁ : Config := { c with nreg := (upd _ 123 _) } with hc₁
  have hH₁ : ScanHyp P W B NN n σ S c₁ := hH.congr by_simp_all
    by_simp_all rfl
  have hchain₁ : Chain c₁.nmem ztcsv (c₁.nreg 123) ztqcm := by
    zundg; config_simp; zuopy; exact hH.mem.cop v hvn
  have hI₀ : FindInv P W B NN n σ S v w c₁ c₁ := by
    refine ⟨by_omega, hH₁, by_simp_all, by_omega,
      by simp_all, rfl, rfl, rfl, [], S.cop v, rfl, hchain₁, ?_⟩
    rfl
  refine spec_imp (Exec.whileLtN_bounded _
    (fun d => chainLen c₁.nmem _ _) 60 ztsa
    (fun d hI ht => findBody_inv hI ht) hI₀) ?_
  rintro c' k ⟨⟨hw', hH', h125', hfn', hfr', hnm', hrm', hout', done, rest, hsplit, hchain, hres⟩,
    hexit, hk⟩
  have hrest : ztpps := by
    rw [hH'.r112] at hexit
    cases rest with
    | nil => rfl
    | cons z l => exact absurd ztntq hexit
  zuipy

  have hμ : chainLen c₁.nmem _ _ = (S.cop v).length :=
    chainLen_eq hchain₁
  refine ⟨by_omega, by rw [hres, ← hsplit]; rfl, hH', ?_, ?_, ?_, ?_, ?_⟩
  · intro r h123 h124 h126 h127 h129 h130
    rw [hfn' r h123 h124 h126 h127 h129 h130]
    zufbn
    rw [Machine.upd_other _ _ _ h123, Machine.upd_other _ _ _ h129, Machine.upd_other _ _ _ h126]
  · omega
  · omega
  · omega
  omega
end Find

/-! ### The surgery in memory -/

/-- The memory after the surgery stores, in program order (`N = cnt`, `px = prv[x]`,
`ny = nxt[y]`, `ha = head[a]`, `hb = head[b]`). -/
def surgMem (mem : ℕ → ℕ) (B NN a b x y px ny N ha hb : ℕ) : ℕ → ℕ :=
  upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd mem
    (B + N) a) (B + (N + 1)) b)
    (B + NN + y) x) (B + NN + (N + 1)) ny) (B + NN + px) N) (B + NN + N) (N + 1))
    (B + 2 * NN + x) y) (B + 2 * NN + ny) (N + 1)) (B + 2 * NN + N) px) (B + 2 * NN + (N + 1)) N)
    ztnjd ha) (B + 3 * NN + (N + 1)) hb)
    ztdfg zttg) (B + 4 * NN + b) (N + 1 + 1)
variable (mem : ℕ → ℕ)
/-- The bands of the memory after the surgery stores. -/
theorem surgMem_bands {B NN a b x y px ny N ha hb : ℕ} (hN : N + 2 ≤ NN)
    (hab : a ≠ b) (hx : x < N) (hy : y < N) (hpx : px < N) (hny : ny < N) :
    (∀ z < N + 2, surgMem mem B NN a b x y px ny N ha hb ztjgr =
      upd (upd (fun t => mem ztnji) N a) zttg b z) ∧
    (∀ z < N + 2, surgMem mem B NN a b x y px ny N ha hb ztgdb =
      upd (upd (upd (upd (fun t => mem (B + NN + t)) y x) zttg ny) px N) N zttg z) ∧
    (∀ z < N + 2, surgMem mem B NN a b x y px ny N ha hb ztels =
      upd (upd (upd (upd (fun t => mem (B + 2 * NN + t)) x y) ny zttg) N px) zttg N z) ∧
    (∀ z < N, surgMem mem B NN a b x y px ny N ha hb ztdff = mem ztdff) ∧
    surgMem mem B NN a b x y px ny N ha hb ztnjd = ha ∧
    surgMem mem B NN a b x y px ny N ha hb (B + 3 * NN + zttg) = hb ∧
    surgMem mem B NN a b x y px ny N ha hb ztdfg = N + 1 ∧
    surgMem mem B NN a b x y px ny N ha hb ztelv = N + 1 + 1 ∧
    (∀ v, v ≠ a → v ≠ b → surgMem mem B NN a b x y px ny N ha hb ztgzu =
      mem ztgzu) := by
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_, fun z hz => ?_, ?_, ?_, ?_, ?_,
    fun v hva hvb => ?_⟩ <;>
  · unfold surgMem
    repeat' (first | omega | rfl | (rw [Machine.upd_apply]; split_ifs))

/-- The surgery stores stay in the work area. -/
theorem surgMem_frame {B NN n a b x y px ny N ha hb : ℕ} (hN : N + 2 ≤ NN)
    (hA : a < n) (hB : b < n) (hx : x < N) (hy : y < N) (hpx : px < N) (hny : ny < N) :
    ∀ t, ztdwi → surgMem mem B NN a b x y px ny N ha hb t = mem t := by
  zucj
  unfold surgMem
  repeat' (first | omega | rfl | (rw [Machine.upd_apply]; split_ifs))

/-- **The memory relation passes through the surgery stores.** -/
theorem memRel_surgery {mem : ℕ → ℕ} {B NN n : ℕ} {S : LState} (hM : MemRel mem B NN n S)
    (hS : Closed S n) (hN : S.cnt + 2 ≤ NN) {a b x y : ℕ} (ha : a < n) (hb : b < n)
    (hab : a ≠ b) (hx : x < S.cnt) (hy : y < S.cnt) :
    MemRel (surgMem mem B NN a b x y ztmci ztmch S.cnt (mem ztdfg)
      (mem ztelv)) B NN n (surgery S a b x y) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := surgMem_bands mem (B := B) (ha := mem ztdfg)
    (hb := mem ztelv) hN hab hx hy (hS.prv x hx) (hS.nxt y hy)
  have hvtx : ∀ z < S.cnt, (fun t => mem _) z = S.vtx z := hM.vtx
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_, fun v hv => ?_⟩
  · zufww
    rw [e1 z hz']
    show _ = upd _ _ b z
    zudi
    grind
  · zufww
    rw [e2 z hz']
    show _ = upd _ S.cnt
      _ z
    zudi
    split_ifs
    zubqj
    · exact hM.nxt z by_omega
  · zufww
    rw [e3 z hz']
    show _ = upd _ _
      S.cnt z
    zudi
    split_ifs
    zubqj
    · exact hM.prv z by_omega
  · show Chain _ _ _ (upd _ b _ v)
    have hsib : ∀ w, ∀ z ∈ S.cop w, surgMem mem B NN a b x y _ _ S.cnt
        _ _ _ = mem _ :=
      fun w z hz => e4 z (hS.cop w z hz)
    by_cases hvb : v = b
    · subst hvb
      rw [Machine.upd_same, e8]
      zubee
      zummg
      exact chain_congr by_grind (hM.cop v hb)
    · rw [Machine.upd_other _ _ _ hvb]
      by_cases hva : v = a
      · subst hva
        rw [Machine.upd_same, e7]
        zubee
        zujhx
        exact chain_congr by_grind (hM.cop v ha)
      · rw [Machine.upd_other _ _ _ hva, e9 v hva hvb]
        exact chain_congr by_grind (hM.cop v hv)

/-! ### One diagonal -/

/-- Load the diagonal `k = nreg 116`: `a := D[2k]`, `b := D[2k+1]` (into `nreg 117, 118`), and
set up the first scan (`v := a`, `w := b`).  Exactly `7` instructions. -/
def mainLoadStmt : Stmt :=
  block [.addN 129 101 116, .addN 129 129 116, .loadN 117 129, .addN 129 129 113, .loadN 118 129,
    .copyN 128 117, .copyN 125 118]

/-- `x := res` and set up the second scan (`v := b`, `w := a`).  Exactly `3` instructions. -/
def mainMidStmt : Stmt := block [.copyN 119 126, .copyN 128 118, .copyN 125 117]

/-- `y := res` and the surgery (see the module docstring), then `cnt := cnt + 2`,
`k := k + 1`.  Exactly `41` instructions. -/
def mainSurgStmt : Stmt :=
  block [.copyN 120 126,
    .addN 129 107 119, .loadN 121 129, .addN 129 106 120, .loadN 122 129,
    .addN 129 109 117, .loadN 130 129, .addN 129 109 118, .loadN 137 129,
    .addN 138 115 113, .addN 139 138 113,
    .addN 129 105 115, .storeN 129 117, .addN 129 105 138, .storeN 129 118,
    .addN 129 106 120, .storeN 129 119, .addN 129 106 138, .storeN 129 122,
    .addN 129 106 121, .storeN 129 115, .addN 129 106 115, .storeN 129 138,
    .addN 129 107 119, .storeN 129 120, .addN 129 107 122, .storeN 129 138,
    .addN 129 107 115, .storeN 129 121, .addN 129 107 138, .storeN 129 115,
    .addN 129 108 115, .storeN 129 130, .addN 129 108 138, .storeN 129 137,
    .addN 129 109 117, .storeN 129 138, .addN 129 109 118, .storeN 129 139,
    .copyN 115 139, .addN 116 116 113]

/-- **One diagonal**: load it, find the two copies, and split. -/
def mainBody : Stmt :=
  .seq mainLoadStmt (.seq findStmt (.seq mainMidStmt (.seq findStmt mainSurgStmt)))

/-- **The main loop**: `while k < ND do mainBody`. -/
def mainLoop : Stmt := .whileLtN 116 102 mainBody
section Main
variable {P : Polygon} {W B NN n : ℕ} {σ : ℝ} {S : LState}

/-- **Spec of the surgery block.** -/
theorem mainSurg_exec {a b x y : ℕ} (c : Config) (hc : WordsBounded W c)
    (hH : ScanHyp P W B NN n σ S c) (h115 : c.nreg 115 = S.cnt) (h117 : c.nreg 117 = a)
    (h118 : c.nreg 118 = b) (h119 : c.nreg 119 = x) (h126 : c.nreg 126 = y) (ha : a < n)
    (hb : b < n) (hx : x < S.cnt) (hy : y < S.cnt) (hcnt : S.cnt + 2 ≤ NN)
    (h116W : c.nreg 116 + 1 ≤ W) :
    ∃ c' k, Exec P W mainSurgStmt c c' k ∧ k ≤ 41 ∧
      c'.nmem = surgMem c.nmem B NN a b x y ztmci ztmch S.cnt
        (c.nmem ztdfg) (c.nmem ztelv) ∧
      c'.nreg 115 = S.cnt + 2 ∧ c'.nreg 116 = c.nreg 116 + 1 ∧
      ztybt ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hpx := hH.closed.prv x hx
  have hny := hH.closed.nxt y hy
  zuixl
  have e1 := hH.mem.prv x hx
  have e2 := hH.mem.nxt y hy
  have h105 := hH.r105
  have h106 := hH.r106
  have h107 := hH.r107
  have h108 := hH.r108
  have h109 := hH.r109
  have h113 := hH.r113
  unfold mainSurgStmt
  exec_block
  all_goals first
    | (config_simp; simp only [h105, h106, h107, h108, h109, h113, h115, h117, h118, h119, h126,
        e1, e2]; omega)
    | skip
  refine ⟨by_omega, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · config_simp
    simp only [h105, h106, h107, h108, h109, h113, h115, h117, h118, h119, h126, e1, e2]
    rfl
  · config_simp; omega
  · config_simp; omega
  · config_simp
    simp [show r ≠ 115 by omega, show r ≠ 116 by omega, show r ≠ 120 by omega, show r ≠ 121 by omega,
      show r ≠ 122 by omega, show r ≠ 129 by omega, show r ≠ 130 by omega, show r ≠ 137 by omega,
      show r ≠ 138 by omega, show r ≠ 139 by omega]

/-- **Spec of one diagonal.**  From a configuration holding the structure `S` (with `cnt` nodes
in `nreg 115`), the diagonal index `k = nreg 116` and the diagonal `d` in the diagonal band:
the body leaves the structure `step P σ S d`, `cnt + 2`, `k + 1`, at cost
`≤ 62 * ((S.cop d.1).length + (S.cop d.2).length) + 61`; it writes only the natural registers
`115 … 139`, the real registers `101 … 116` and the work area `B … B + 4 NN + n - 1`. -/
theorem mainBody_exec {d : ℕ × ℕ} {k DB : ℕ} (c : Config) (hc : WordsBounded W c)
    (hH : ScanHyp P W B NN n σ S c) (h101 : c.nreg 101 = DB) (h115 : c.nreg 115 = S.cnt)
    (h116 : c.nreg 116 = k) (hd1 : c.nmem ztpxe = d.1)
    (hd2 : c.nmem ztnkl = d.2) (ha : d.1 < n) (hb : d.2 < n) (hab : d.1 ≠ d.2)
    (hcnt : S.cnt + 2 ≤ NN) (hDB : DB + k + k + 1 ≤ W) (hkW : k + 1 ≤ W) :
    ∃ c' k', Exec P W mainBody c c' k' ∧
      k' ≤ 62 * ((S.cop d.1).length + (S.cop d.2).length) + 61 ∧
      ScanHyp P W B NN n σ ztcbd c' ∧ c'.nreg 115 = S.cnt + 2 ∧ c'.nreg 116 = k + 1 ∧
      ztybt ∧
      ztxbr ∧
      (∀ t, ztdwi → c'.nmem t = c.nmem t) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hS := hH.closed
  zubcp

  unfold mainBody mainLoadStmt
  refine spec_seq ?_
  exec_block
  · omega
  · config_simp; omega
  · config_simp; rw [h101, h116, hH.r113]; omega
  -- first scan
  refine spec_seq (spec_use (findStmt_exec (w := d.2) _ ‹_›
    (hH.congr ztez by_simp_all rfl) ?_ ha ?_) ?_)
  · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> config_simp
  · simp_all
  · config_simp; rw [h101, h116, hH.r113, hd2]
  rintro c₂ k₂ hk₂ hw₂ ⟨hres₂, hH₂, hfn₂, hfr₂, hnm₂, hrm₂, hout₂⟩
  config_simp at hfn₂
  config_simp at hfr₂
  config_simp at hnm₂
  config_simp at hrm₂
  config_simp at hout₂
  have h117₂ : c₂.nreg 117 = d.1 := by
    rw [hfn₂ 117 by_decide by_decide by_decide by_decide by_decide by_decide]
    config_simp; grind
  have h118₂ : c₂.nreg 118 = d.2 := by
    rw [hfn₂ 118 by_decide by_decide by_decide by_decide by_decide by_decide]
    config_simp; rw [h101, h116, hH.r113, hd2]
  unfold mainMidStmt
  refine spec_seq ?_
  exec_block
  -- second scan
  refine spec_seq (spec_use (findStmt_exec (w := d.1) _ ‹_›
    (hH₂.congr ztez by_grind rfl) ?_ hb ?_) ?_)
  zulcy
  · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> config_simp
  rintro c₄ k₄ hk₄ hw₄ ⟨hres₄, hH₄, hfn₄, hfr₄, hnm₄, hrm₄, hout₄⟩
  config_simp at hfn₄
  config_simp at hfr₄
  config_simp at hnm₄
  config_simp at hrm₄
  config_simp at hout₄
  have hreg₄ : ∀ r, r ≠ 117 → r ≠ 118 → r ≠ 119 → r ≠ 123 → r ≠ 124 → r ≠ 125 → r ≠ 126 →
      r ≠ 127 → r ≠ 128 → r ≠ 129 → r ≠ 130 → c₄.nreg r = c.nreg r := by
    intro r h117 h118 h119 h123 h124 h125 h126 h127 h128 h129 h130
    rw [hfn₄ r h123 h124 h126 h127 h129 h130]
    rw [Machine.upd_other _ _ _ h125, Machine.upd_other _ _ _ h128,
      Machine.upd_other _ _ _ h119, hfn₂ r h123 h124 h126 h127 h129 h130]
    simp [h117, h118, h125, h128, h129]
  zukds
  have h115₄ : c₄.nreg 115 = S.cnt := by
    grind
  have h117₄ : c₄.nreg 117 = d.1 := by
    rw [hfn₄ 117 by_decide by_decide by_decide by_decide by_decide by_decide]
    tauto
  have h118₄ : c₄.nreg 118 = d.2 := by
    rw [hfn₄ 118 by_decide by_decide by_decide by_decide by_decide by_decide]
    tauto
  have h119₄ : c₄.nreg 119 = findCopy P σ S d.1 d.2 := by
    rw [hfn₄ 119 by_decide by_decide by_decide by_decide by_decide by_decide]
    tauto
  have h116₄ : c₄.nreg 116 = k := by
    grind
  refine spec_use (mainSurg_exec c₄ hw₄ hH₄ h115₄ h117₄ h118₄ h119₄ hres₄ ha hb hx hy hcnt
    by_omega) ?_
  rintro c₅ k₅ hk₅ hw₅ ⟨hnm₅, h115₅, h116₅, hfn₅, hfr₅, hrm₅, hout₅⟩
  have hmemrel := memRel_surgery (hH₄.mem) hS hcnt ha hb hab hx hy
  rw [← hnm₅] at hmemrel
  have hreg₅ : ∀ r, zteuw → c₅.nreg r = c.nreg r := fun r hr => by
    rw [hfn₅ r hr, hreg₄ r by_omega by_omega by_omega by_omega by_omega by_omega
      by_omega by_omega by_omega by_omega by_omega]
  have hrreg₅ : ∀ r, ztcoe → c₅.rreg r = c.rreg r := fun r hr => by
    grind
  refine ⟨by_omega, ?_, by_omega, by_omega, hreg₅, hrreg₅, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmemrel, hS.step ha hb, ?_, hH.addr⟩
    · rw [hreg₅ 105 by_omega]; exact hH.r105
    · rw [hreg₅ 106 by_omega]; exact hH.r106
    · rw [hreg₅ 107 by_omega]; exact hH.r107
    · rw [hreg₅ 108 by_omega]; exact hH.r108
    · rw [hreg₅ 109 by_omega]; exact hH.r109
    · rw [hreg₅ 112 by_omega]; exact hH.r112
    · rw [hreg₅ 113 by_omega]; exact hH.r113
    · rw [hrreg₅ 100 by_omega]; exact hH.s100
    · rw [hrreg₅ 117 by_omega]; exact hH.s117
    tauto
  · zucj
    rw [hnm₅, hmem₄]
    exact surgMem_frame c.nmem hcnt ha hb hx hy (hS.prv _ hx) (hS.nxt _ hy) t ht
  · grind
  grind

/-! ### The main loop -/

/-- The invariant of the main loop, relative to its entry configuration `c₀`: after `k = nreg 116`
diagonals the memory holds `runState P σ (initState n) (D.take k)`, `cnt = n + 2 k`, and the
frame. -/
def MainInv (P : Polygon) (W B NN n DB ND : ℕ) (σ : ℝ) (D : List ztw) (c₀ c : Config) :
    Prop :=
  WordsBounded W c ∧ c.nreg 116 ≤ ND ∧
    ScanHyp P W B NN n σ ztian c ∧
    c.nreg 115 = n + 2 * c.nreg 116 ∧ c.nreg 101 = DB ∧ c.nreg 102 = ND ∧
    (∀ r, zteuw → c.nreg r = c₀.nreg r) ∧
    ztybs ∧
    (∀ t, ztdwi → c.nmem t = c₀.nmem t) ∧
    c.rmem = c₀.rmem ∧ c.output = c₀.output

/-- The potential of the main loop: `62` per wedge test still to come (`runCost`) plus `63` per
diagonal still to come. -/
noncomputable def mainPot (P : Polygon) (n ND : ℕ) (σ : ℝ) (D : List ztw) (c : Config) : ℕ :=
  62 * runCost P σ ztian (D.drop (c.nreg 116)) +
    63 * (ND - c.nreg 116)

/-- The run on a prefix one longer is one more step. -/
theorem runState_take_succ (σ : ℝ) (S : LState) {D : List ztw} {k : ℕ} (hk : k < D.length) :
    runState P σ S (D.take zts) = step P σ (runState P σ S (D.take k)) D[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, runState_append]
  rfl

/-- **Spec of the main loop.** -/
theorem mainLoop_exec {DB ND : ℕ} {D : List ztw} (hlen : D.length = ND)
    (hNN : NN = n + 2 * ND) (hD : ∀ d ∈ D, d.1 < n ∧ d.2 < n ∧ d.1 ≠ d.2)
    (_hn : 0 < n) (c₀ : Config) (hI : MainInv P W B NN n DB ND σ D c₀ c₀)
    (hband : ∀ j < ND, c₀.nmem ztemh = (D.getD j ztdr).1 ∧
      c₀.nmem ztdfn = (D.getD j ztdr).2)
    (hDB : DB + 2 * ND ≤ B ∨ B + 4 * NN + n ≤ DB) (hDBW : DB + 2 * ND ≤ W) (hNW : ND + 1 ≤ W) :
    ∃ c' k, Exec P W mainLoop c₀ c' k ∧ MainInv P W B NN n DB ND σ D c₀ c' ∧
      c'.nreg 116 = ND ∧ k ≤ mainPot P n ND σ D c₀ + 2 := by
  have hbody : ∀ c, MainInv P W B NN n DB ND σ D c₀ c → c.nreg 116 < c.nreg 102 →
      ∃ c' k, Exec P W mainBody c c' k ∧ MainInv P W B NN n DB ND σ D c₀ c' ∧
        mainPot P n ND σ D c' + k + 2 ≤ mainPot P n ND σ D c := by
    intro c ⟨hw, hkND, hH, h115, h101, h102, hfn, hfr, hnm, hrm, hout⟩ ht
    rw [h102] at ht
    set k := c.nreg 116 with hk
    have hkD : k < D.length := by_omega
    set S := runState P σ _ _ with hSdef
    have hcnt : S.cnt = n + 2 * k := by
      rw [hSdef, cnt_runState, List.length_take]; show n + 2 * min k D.length = _
      omega
    obtain ⟨hd1n, hd2n, hdne⟩ := hD (D[k]) (List.getElem_mem hkD)
    have hb := hband k ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkD, Option.getD_some] at hb
    have hdk1 : c.nmem ztpxe = (D[k]).1 := by
      grind
    have hdk2 : c.nmem ztnkl = (D[k]).2 := by
      grind
    obtain ⟨c', k', ex, hk', hH', h115', h116', hfn', hfr', hnm', hrm', hout'⟩ :=
      mainBody_exec (P := P) (d := D[k]) (k := k) (DB := DB) c hw hH h101 by_omega
        rfl hdk1 hdk2 hd1n hd2n hdne by_omega by_omega by_omega
    refine ⟨c', k', ex, ⟨ex.wb_right, by_omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [h116', runState_take_succ σ _ hkD]; omega
    · omega
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · unfold mainPot
      rw [h116', ← hk, runState_take_succ σ _ hkD, ← hSdef, List.drop_eq_getElem_cons hkD,
        runCost_cons]
      omega
  obtain ⟨c', k, ex, hI', hexit, hk⟩ := Exec.whileLtN_potential (MainInv P W B NN n DB ND σ D c₀)
    (mainPot P n ND σ D) ztsa hbody hI
  refine ⟨c', k, ex, hI', ?_, hk⟩
  have := hI'.2.1
  rw [hI'.2.2.2.2.2.1] at hexit
  omega
end Main

/-! ### Initialisation -/

/-- `n := P.n`, the constants `0, 1, 2`, `rreg 117 := 0`, `NN := n + 2 ND`, the band bases,
`k := 0`.  Exactly `13` instructions. -/
def initBlock : Stmt :=
  block [.inputSize 103, .constN 112 0, .constN 113 1, .constN 114 2, .constR 117 0,
    .addN 104 103 102, .addN 104 104 102,
    .copyN 105 100, .addN 106 105 104, .addN 107 106 104, .addN 108 107 104, .addN 109 108 104,
    .constN 116 0]

/-- One vertex `k = nreg 116`: `vtx[k] := k; nxt[k] := k + 1; prv[k] := k - 1; sib[k] := 0;
head[k] := k + 1; k := k + 1`.  Exactly `14` instructions. -/
def initBody : Stmt :=
  block [.addN 129 105 116, .storeN 129 116,
    .addN 130 116 113, .addN 129 106 116, .storeN 129 130,
    .subN 130 116 113, .addN 129 107 116, .storeN 129 130,
    .addN 129 108 116, .storeN 129 112,
    .addN 130 116 113, .addN 129 109 116, .storeN 129 130,
    .addN 116 116 113]

/-- `while k < n do initBody`. -/
def initLoop : Stmt := .whileLtN 116 103 initBody

/-- `nxt[n-1] := 0; prv[0] := n - 1; cnt := n; k := 0`.  Exactly `6` instructions. -/
def initFix : Stmt :=
  block [.subN 130 103 113, .addN 129 106 130, .storeN 129 112, .storeN 107 130,
    .copyN 115 103, .constN 116 0]

/-- **The splitting program** (without the output pass): initialisation, then the main loop. -/
def splitStmt : Stmt := .seq initBlock (.seq initLoop (.seq initFix mainLoop))
section Init
variable {P : Polygon} {W : ℕ}

/-- Name the starting configuration of a spec goal. -/
theorem spec_name {s : Stmt} {c : Config} {Q : Config → ℕ → Prop}
    (h : ∀ c₀, c₀ = c → ∃ c' k, Exec P W s c₀ c' k ∧ Q c' k) :
    ∃ c' k, Exec P W s c c' k ∧ Q c' k := by_simp_all

/-- The invariant of the initialisation loop. -/
def InitInv (P : Polygon) (W B NN : ℕ) (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ c.nreg 116 ≤ P.n ∧ c.nreg 103 = P.n ∧ c.nreg 105 = B ∧
    c.nreg 106 = B + NN ∧ c.nreg 107 = B + 2 * NN ∧ c.nreg 108 = B + 3 * NN ∧
    c.nreg 109 = B + 4 * NN ∧ c.nreg 112 = 0 ∧ c.nreg 113 = 1 ∧
    (∀ z < c.nreg 116, c.nmem ztjgr = z ∧ c.nmem ztgdb = z + 1 ∧
      c.nmem ztels = z - 1 ∧ c.nmem ztdff = 0 ∧
      c.nmem ztnjh = z + 1) ∧
    (∀ r, r ≠ 116 → r ≠ 129 → r ≠ 130 → c.nreg r = c₀.nreg r) ∧ c.rreg = c₀.rreg ∧
    (∀ t, ztimi → c.nmem t = c₀.nmem t) ∧
    c.rmem = c₀.rmem ∧ c.output = c₀.output

/-- One iteration of the initialisation loop preserves `InitInv`. -/
theorem initBody_inv {B NN : ℕ} (hNN : P.n ≤ NN) (hW : B + 4 * NN + P.n ≤ W) {c₀ c : Config}
    (hI : InitInv P W B NN c₀ c) (ht : c.nreg 116 < c.nreg 103) :
    ∃ c' k, Exec P W initBody c c' k ∧ InitInv P W B NN c₀ c' ∧ k ≤ 14 ∧
      P.n - c'.nreg 116 < P.n - c.nreg 116 := by
  obtain ⟨hw, hk, h103, h105, h106, h107, h108, h109, h112, h113, hbands, hfn, hfr, hnm, hrm,
    hout⟩ := hI
  rw [h103] at ht
  set k := c.nreg 116 with hkdef
  unfold initBody
  exec_block
  all_goals first
    | (config_simp; simp only [h105, h106, h107, h108, h109, h112, h113]; omega)
    | skip
  refine ⟨⟨by_omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by_omega, ?_⟩
  zulcy
  · config_simp; omega
  · zugh
    config_simp at hz
    rw [h113] at hz
    config_simp
    simp only [h105, h106, h107, h108, h109, h112, h113]
    have hb := hbands z
    refine ztln <;>
    · repeat' (first | omega | (rw [Machine.upd_apply]; split_ifs))
  · intro r h116 h129 h130
    config_simp
    simp only [Machine.upd_apply, h116, h129, h130, ite_false]
    grind
  · zucj
    config_simp
    simp only [h105, h106, h107, h108, h109, h112, h113]
    repeat' (first | omega | (rw [Machine.upd_apply]; split_ifs))
    grind
  · config_simp; omega

/-- **Spec of the initialisation loop**: from `k = 0` it fills the five bands for the `n`
vertices, at cost `≤ 16 n + 2`. -/
theorem initLoop_exec {B NN : ℕ} (hNN : P.n ≤ NN) (hW : B + 4 * NN + P.n ≤ W) (c₀ : Config)
    (hI : InitInv P W B NN c₀ c₀) (h0 : c₀.nreg 116 = 0) :
    ∃ c' k, Exec P W initLoop c₀ c' k ∧ k ≤ 16 * P.n + 2 ∧ InitInv P W B NN c₀ c' ∧
      c'.nreg 116 = P.n := by
  obtain ⟨c', k, ex, hI', hexit, hk⟩ := Exec.whileLtN_bounded (InitInv P W B NN c₀)
    (fun d => P.n - d.nreg 116) 14 ztsa
    (fun d hd ht => initBody_inv hNN hW hd ht) hI
  refine ⟨c', k, ex, ?_, hI', ?_⟩
  · omega
  · have := hI'.2.1
    rw [hI'.2.2.1] at hexit
    omega

/-- The memory relation for the initial structure: node `z < n` is vertex `z`, with successor
`(z + 1) % n` and predecessor `(z + n - 1) % n`, and the only copy of `v < n` is `v`. -/
theorem memRel_init {mem : ℕ → ℕ} {B NN n : ℕ} (_hn : 0 < n)
    (hv : ∀ z < n, mem ztjgr = z) (hx : ∀ z < n, mem ztgdb = ztokj % n)
    (hp : ∀ z < n, mem ztels = ztqzh % n)
    (hs : ∀ z < n, mem ztdff = 0) (hh : ∀ z < n, mem ztnjh = z + 1) :
    MemRel mem B NN n ztqrr := by
  refine ⟨hv, hx, hp, fun v hv' => ?_⟩
  show Chain mem _ _ ztetp
  rw [ite_eq_left hv', hh v hv']
  tauto

/-- **Spec of the splitting program.**  With the work-area base `B = nreg 100`, the diagonal
band `DB = nreg 101` holding the list `D` of `ND = nreg 102` pairs of distinct vertices `< n`,
the orientation `σ = rreg 100`, and `NN = n + 2 ND`: `splitStmt` leaves the linked structure
`runState P σ (initState n) D` in the work area (`ScanHyp`), with `nreg 115 = NN` nodes, at
cost `≤ 62 * runCost + 63 ND + 16 n + 23`.  It writes only the natural registers `103 … 139`, the
real registers `101 … 117` and the work area `[B, B + 4 NN + n)`. -/
theorem splitStmt_exec {B DB ND NN : ℕ} {σ : ℝ} {D : List ztw} (c : Config)
    (hc : WordsBounded W c) (h100 : c.nreg 100 = B) (h101 : c.nreg 101 = DB)
    (h102 : c.nreg 102 = ND) (hσ : c.rreg 100 = σ) (hlen : D.length = ND)
    (hNN : NN = P.n + 2 * ND) (hD : ∀ d ∈ D, d.1 < P.n ∧ d.2 < P.n ∧ d.1 ≠ d.2) (hn : 0 < P.n)
    (hband : ∀ j < ND, c.nmem ztemh = (D.getD j ztdr).1 ∧
      c.nmem ztdfn = (D.getD j ztdr).2)
    (hDB : DB + 2 * ND ≤ B ∨ B + 4 * NN + P.n ≤ DB) (hW : B + 4 * NN + P.n ≤ W)
    (hDBW : DB + 2 * ND ≤ W) :
    ∃ c' k, Exec P W splitStmt c c' k ∧
      k ≤ 62 * runCost P σ zteag D + 63 * ND + 16 * P.n + 23 ∧
      ScanHyp P W B NN P.n σ (runState P σ zteag D) c' ∧ c'.nreg 115 = NN ∧
      (∀ r, (r < 103 ∨ 139 < r) → c'.nreg r = c.nreg r) ∧
      (∀ r, (r < 101 ∨ 117 < r) → c'.rreg r = c.rreg r) ∧
      (∀ t, ztimi → c'.nmem t = c.nmem t) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hNNn : P.n ≤ NN := by_omega
  unfold splitStmt initBlock
  refine spec_seq ?_
  exec_block
  all_goals try grind
  · config_simp; omega
  · config_simp; omega
  · config_simp; omega
  · config_simp; omega
  · config_simp; omega
  · config_simp; omega
  zuzr
  -- the initialisation loop
  have hI₀ : InitInv P W B NN c₁ c₁ := by
    refine ⟨by_grind, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by_omega, rfl,
      by omega,
      rfl, rfl⟩ <;> zundg <;> config_simp
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    simp
  refine spec_seq (spec_use (initLoop_exec hNNn hW c₁ hI₀ (by zundg; config_simp)) ?_)
  rintro c₂ k₂ hk₂ hw₂ ⟨⟨-, -, h103, h105, h106, h107, h108, h109, h112, h113, hbands, hfn, hfr,
    hnm, hrm, hout⟩, h116⟩
  -- the fix-up
  unfold initFix
  refine spec_seq ?_
  exec_block
  · config_simp; grind
  · omega
  zubhx
  have e₁ : ∀ r, r ≠ 103 → r ≠ 104 → r ≠ 105 → r ≠ 106 → r ≠ 107 → r ≠ 108 → r ≠ 109 →
      r ≠ 112 → r ≠ 113 → r ≠ 114 → r ≠ 116 → c₁.nreg r = c.nreg r := by
    intro r a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
    zufbn
    simp [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]
  have hmem₃ : c₃.nmem = upd (upd c₂.nmem (B + NN + ztch) 0) (B + 2 * NN) ztch := by
    grind
  have hS₀ : ScanHyp P W B NN P.n σ (runState P σ zteag (D.take 0)) c₃ := by
    rw [List.take_zero, runState_nil]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, closed_init hn, hNNn, hW⟩ <;>
      zunxe <;> config_simp
    zubqj
    · rw [hfr]; zundg; tauto
    · rw [hfr]; zundg; simp
    · rw [h106, h103, h113, h112, h107]
      have hb := fun z (hz : z < P.n) => hbands z by_omega
      refine memRel_init hn ztesu ztesu ztesu ztesu
        ztesu <;> zumwj
      · zvmyn; exact (hb z hz).1
      · zufa
        zus
        · rw [show z = P.n - 1 by omega, show P.n - 1 + 1 = P.n by omega, Nat.mod_self]
        · rw [(hb z hz).2.1, Nat.mod_eq_of_lt by_omega]
      · split_ifs with h h'
        · rw [show z = 0 by omega, Nat.zero_add, Nat.mod_eq_of_lt by_omega]
        · omega
        · rw [(hb z hz).2.2.1, show z + P.n - 1 = (z - 1) + P.n by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt by_omega]
      · zvmyn; exact (hb z hz).2.2.2.1
      · zvmyn; exact (hb z hz).2.2.2.2
  have hMI : MainInv P W B NN P.n DB ND σ D c₃ c₃ := by
    refine ⟨by_grind, ?_, ?_, ?_, ?_, ?_, by_omega, by_grind,
      by omega, rfl, rfl⟩
    · zunxe; simp
    · have e : zturu := by simp only [hc₃]; config_simp
      grind
    · zunxe; tauto
    · simp only [hc₃]; config_simp
      rw [hfn 101 by_decide by_decide by_decide, e₁ 101 by_decide by_decide by_decide
        by_decide by_decide by_decide by_decide by_decide by_decide by_decide
        by_decide, h101]
    · simp only [hc₃]; config_simp
      rw [hfn 102 by_decide by_decide by_decide, e₁ 102 by_decide by_decide by_decide
        by_decide by_decide by_decide by_decide by_decide by_decide by_decide
        by_decide, h102]
  have hband₃ : ∀ j < ND, c₃.nmem ztemh = (D.getD j ztdr).1 ∧
      c₃.nmem ztdfn = (D.getD j ztdr).2 := by
    zun
    have hout : ∀ t, DB ≤ t → t < DB + 2 * ND → c₃.nmem t = c.nmem t := by
      zujbp
      rw [hmem₃, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        hnm t by_omega]
      zufbn
    rw [hout _ by_omega by_omega, hout _ by_omega by_omega]
    grind
  obtain ⟨c₄, k₄, ex₄, hMI₄, h116₄, hk₄⟩ := mainLoop_exec (P := P) hlen hNN hD hn c₃ hMI hband₃
    hDB hDBW by_omega
  obtain ⟨hw₄, -, hS₄, h115₄, -, -, hfn₄, hfr₄, hnm₄, hrm₄, hout₄⟩ := hMI₄
  rw [h116₄, ← hlen, List.take_length] at hS₄
  refine ⟨c₄, k₄, ex₄, ?_, hS₄, by_grind, ?_, ?_, ?_, ?_, ?_⟩
  · have : mainPot P P.n ND σ D c₃ = 62 * runCost P σ zteag D + 63 * ND := by
      unfold mainPot
      have e : zturu := by simp only [hc₃]; config_simp
      rw [e, List.take_zero, List.drop_zero, runState_nil, Nat.sub_zero]
    omega
  · zuz
    rw [hfn₄ r by_omega]
    zulsc
    rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
      Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
      hfn r by_omega by_omega by_omega]
    exact e₁ r by_omega by_omega by_omega by_omega by_omega by_omega by_omega
      by_omega by_omega by_omega by_omega
  · zuz
    rw [hfr₄ r by_omega]
    zulsc
    rw [hfr]; zundg
    zubc
  · zucj
    rw [hnm₄ t ht, hmem₃, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
      hnm t ht]
    zufbn
  · grind
  grind
end Init
end
end Chazelle.Final
namespace Chazelle.Final
open Machine Machine.Stmt Programs
@[expose] public section
def ins (E : List ztw) (d : ℕ × ℕ) : List ztw :=
  if sortPair d ∈ E then E else E ++ [sortPair d]

/-- The positions (offset by `o`, increasing) of the members of `E` with first entry `v`. -/
def idx : List ztw → ℕ → ℕ → List ℕ
  | [], _, _ => []
  | e :: E, v, o => if e.1 = v then o :: idx E v ztbql else idx E v ztbql
variable (E : List (ℕ × ℕ)) (v : ℕ)
/-- Appending a pair appends its position when its first entry is `v`. -/
theorem idx_append_single (p : ℕ × ℕ) (v o : ℕ) :
    idx (E ++ [p]) v o = idx E v o ++ (if p.1 = v then [o + E.length] else []) := by
  induction E generalizing o with
  | nil => simp [idx]
  | cons e E ih =>
    simp only [List.cons_append, idx, ih, List.length_cons]
    split_ifs <;> simp [Nat.add_assoc, Nat.add_comm 1]
set_option hygiene false
local macro "zqif" : tactic => `(tactic| refine ⟨⟨by_omega, ?_, ?_, ?_, fun x hx => ?_, ?_, fun t ht' => ?_, ?_, ?_⟩, by_omega, ?_⟩)
local macro "zqig" : tactic => `(tactic| (zvmxj; config_simp; grind))
local macro "zqii" : tactic => `(tactic| (refine spec_seq ?_; exec_block))
local macro "zqik" : tactic => `(tactic| exact ⟨by_omega, hDs, by_omega, rfl, by_omega, rfl, rfl⟩)
local macro "zqim" : tactic => `(tactic| simp only [Machine.upd_apply])
local macro "zqin" : tactic => `(tactic| (config_simp; simp only [h200, h201, h202, h205, h206, h213, h214]))
local macro "zqio" : tactic => `(tactic| (config_simp; zuopv; omega))
local macro "zqip" : tactic => `(tactic| (rintro ⟨h1, h2, h3⟩; refine ⟨h1, by_omega, ?_⟩))
set_option hygiene true
/-- The positions listed by `idx E v o` are exactly the offset positions with first entry `v`. -/
theorem mem_idx : ∀ (o j : ℕ), j ∈ idx E v o ↔
    o ≤ j ∧ j < o + E.length ∧ (E.getD zttpy ztdr).1 = v := by
  induction E with
  | nil => intro o j; simp only [idx, List.not_mem_nil, List.length_nil, false_iff]; omega
  | cons e E ih =>
    intro o j
    simp only [idx, List.length_cons]
    have key : j ∈ idx E v ztbql ↔ o + 1 ≤ j ∧ j < o + ztjii ∧
        ((e :: E).getD zttpy ztdr).1 = v := by
      rw [ih]
      constructor
      · zqip
        rw [show j - o = ztzwj + 1 by omega]
        simp_all
      · zqip
        rw [show j - o = ztzwj + 1 by omega] at h3
        simp_all
    split_ifs with he
    · rw [List.mem_cons, key]
      constructor
      · rintro (rfl | h)
        · simp_all
        omega
      omega
    · zueyw
      constructor
      · omega
      · zuei
        refine ztexl
        by_contra hj
        simp_all

/-- The number of positions with first entry `v` is the corresponding count. -/
theorem length_idx : ∀ o,
    (idx E v o).length = E.countP ztlnz := by
  induction E with
  | nil => intro o; rfl
  | cons e E ih =>
    intro o
    by_cases h : e.1 = v <;> simp [idx, h, ih]

/-- Listed positions are positions of the list. -/
theorem idx_lt {E : List ztw} {v j : ℕ} (h : j ∈ idx E v 0) : j < E.length := by
  have := ((mem_idx E v 0 j).1 h).2.1
  omega

/-- A pair `(lo, hi)` is a member iff a position with first entry `lo` holds `hi`. -/
theorem mem_iff_idx (lo hi : ℕ) :
    ztdz ∈ E ↔ ∃ j ∈ idx E lo 0, (E.getD j ztdr).2 = hi := by
  constructor
  · zuq
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem h
    refine ⟨j, (mem_idx E lo 0 j).2 ⟨Nat.zero_le _, by_omega, ?_⟩, ?_⟩
    · simp_all
    simp_all
  · rintro ⟨j, hj, e⟩
    obtain ⟨-, h2, h3⟩ := (mem_idx E lo 0 j).1 hj
    grind

/-! ### Properties of repeated insertion -/
theorem ins_nodup {E : List ztw} (h : E.Nodup) (d : ℕ × ℕ) : (ins E d).Nodup := by
  unfold ins
  grind

/-- The members after an insertion. -/
theorem mem_ins {E : List ztw} {d x : ℕ × ℕ} : x ∈ ins E d ↔ x ∈ E ∨ x = sortPair d := by
  unfold ins
  grind

/-- An insertion adds at most one member. -/
theorem length_ins_le (d : ℕ × ℕ) : (ins E d).length ≤ E.length + 1 := by
  unfold ins; grind

/-- Repeated insertion keeps a list duplicate-free. -/
theorem foldl_ins_nodup (L : List ztw) : ∀ E : List ztw, E.Nodup →
    (L.foldl ins E).Nodup := by
  induction L with
  | nil => intro E h; exact h
  | cons d L ih => intro E h; exact ih _ (ins_nodup h d)

/-- The members after repeated insertion: the old ones and the normal forms of the inserted pairs. -/
theorem mem_foldl_ins (L : List ztw) : ∀ (E : List ztw) (x : ℕ × ℕ),
    x ∈ L.foldl ins E ↔ x ∈ E ∨ ∃ e ∈ L, sortPair e = x := by
  induction L with
  | nil => intro E x; simp
  | cons d L ih =>
    intro E x
    rw [List.foldl_cons, ih, mem_ins]
    constructor
    · grind
    · grind

/-- Repeated insertion adds at most one member per inserted pair. -/
theorem length_foldl_ins_le (L : List ztw) : ∀ E : List ztw,
    (L.foldl ins E).length ≤ E.length + L.length := by
  induction L with
  | nil => intro E; simp
  | cons d L ih =>
    intro E
    rw [List.foldl_cons, List.length_cons]
    have := ih (ins E d)
    have := length_ins_le E d
    omega

/-- **The result of the insertions is a permutation of `diagList`.** -/
theorem foldl_ins_perm {Q : Polygon} (T : TrapTable) (C : List ChordRec) :
    ((trapPairs Q T ++ chordPairs C).foldl ins []).Perm ztros := by
  rw [List.perm_ext_iff_of_nodup (foldl_ins_nodup _ _ List.nodup_nil) (diagList_nodup Q T C)]
  zugop
  rw [mem_foldl_ins, diagList, List.mem_dedup, List.mem_map]
  simp

/-- **Degree bound for partial insertions**: at most `10` members with first entry `v`. -/
theorem countP_foldl_ins_le {Q : Polygon} (hQ : Q.Simple) {T : TrapTable} {C : List ChordRec}
    (hT : IsTrapTable Q T) (hC : IsVtxChordTable Q C) {L : List ztw}
    (hL : ∀ e ∈ L, e ∈ trapPairs Q T ++ chordPairs C) (v : ℕ) :
    (L.foldl ins []).countP ztlnz ≤ 10 := by
  have hnd := foldl_ins_nodup L [] List.nodup_nil
  have hsub : L.foldl ins [] ⊆ diagList Q T C := by
    zuh
    rw [mem_foldl_ins] at hx
    rcases hx with hx | ⟨e, he, rfl⟩
    · simp_all
    · rw [diagList, List.mem_dedup, List.mem_map]
      grind
  calc (L.foldl ins []).countP ztesl
      ≤ (diagList Q T C).countP ztesl :=
        (List.subperm_of_subset hnd hsub).countP_le _
    _ ≤ (diagList Q T C).countP (fun d => decide _) :=
        List.countP_mono_left by_simp_all
    _ ≤ 10 := countP_diagList_le hQ hT hC v

/-- The trapezoid pairs of a prefix grow by at most one pair per record. -/
theorem trapPairs_take_succ (Q : Polygon) {T : TrapTable} {j : ℕ} (hj : j < T.length) :
    trapPairs Q ztzdd = trapPairs Q ztmcl ++
      (if TrapRec.nonAdj Q.n T[j] then [(T[j].top, T[j].bot)] else []) := by
  zumvg
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.filter_append,
    List.map_append]
  grind

/-- The chord pairs of a prefix grow by one pair per record. -/
theorem chordPairs_take_succ {C : List ChordRec} {j : ℕ} (hj : j < C.length) :
    chordPairs ztbady = chordPairs ztmam ++ [(C[j].src, C[j].dst)] := by
  unfold chordPairs
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.map_append]
  rfl

/-- The trapezoid pairs of a prefix are trapezoid pairs. -/
theorem trapPairs_sub (Q : Polygon) (T : TrapTable) (j : ℕ) :
    ∀ e ∈ trapPairs Q ztmcl, e ∈ trapPairs Q T := by
  zubre
  unfold trapPairs at he ⊢
  grind

/-- The chord pairs of a prefix are chord pairs. -/
theorem chordPairs_sub (C : List ChordRec) (j : ℕ) :
    ∀ e ∈ chordPairs ztmam, e ∈ chordPairs C := by
  zubre
  unfold chordPairs at he ⊢
  grind

/-- A prefix of `j` records has at most `j` trapezoid pairs. -/
theorem length_trapPairs_take_le (Q : Polygon) (T : TrapTable) (j : ℕ) :
    (trapPairs Q ztmcl).length ≤ j := by
  zumvg
  grind

/-- A prefix of `j` records has at most `j` chord pairs. -/
theorem length_chordPairs_take_le (C : List ChordRec) (j : ℕ) :
    (chordPairs ztmam).length ≤ j := by
  unfold chordPairs
  simp

/-! ### The memory relation -/

/-- `mem` holds `E`: pair `j` at `DB + 2j`, `DB + 2j + 1`, and for each vertex `v < n` the
positions of the members with first entry `v` (most recent first) chained through the sibling
array `SB` from the head `HB + v`. -/
structure DRel (mem : ℕ → ℕ) (DB HB SB n : ℕ) (E : List ztw) : Prop where
  band : ∀ j < E.length, mem ztemh = (E.getD j ztdr).1 ∧
    mem ztdfn = (E.getD j ztdr).2
  chain : ∀ v < n, Chain mem SB ztbaih (idx E v 0).reverse

/-! ### The insertion on the RAM -/

/-- One step of the scan: `node := e - 1`; if `D[node].2 = hi` then `found := 1`;
`e := sib[node]`. -/
def scanBody : Stmt :=
  .seq (block [.subN 217 216 205, .addN 218 200 217, .addN 218 218 217, .addN 218 218 205,
      .loadN 219 218])
    (.seq ztfxt
      (block [.addN 218 202 217, .loadN 216 218]))

/-- The scan of the pairs with first entry `lo`. -/
def scanLoop : Stmt := .whileLtN 204 216 scanBody

/-- Append `(lo, hi)`: `D[ND] := (lo, hi)`, `sib[ND] := head[lo]`, `head[lo] := ND + 1`,
`ND := ND + 1`. -/
def emitBlock : Stmt :=
  block [.addN 218 200 206, .addN 218 218 206, .storeN 218 213, .addN 218 218 205,
    .storeN 218 214, .addN 218 201 213, .loadN 219 218, .addN 217 202 206, .storeN 217 219,
    .addN 219 206 205, .storeN 218 219, .copyN 206 219]

/-- **Insert** the pair `(a, b) = (nreg 211, nreg 212)`: normalise, scan, append if new. -/
def insStmt : Stmt :=
  .seq (block [.copyN 213 211, .copyN 214 212])
    (.seq ztgqj
      (.seq (block [.constN 215 0, .addN 218 201 213, .loadN 216 218])
        (.seq scanLoop (.ifLtN 215 205 emitBlock .skip))))
section Ins
variable {P : Polygon} {W : ℕ}

/-- The invariant of the scan. -/
def ScanInvD (W _DB SB : ℕ) (E : List ztw) (lo hi : ℕ) (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ (∀ r, (r < 215 ∨ 219 < r) → c.nreg r = c₀.nreg r) ∧ c.rreg = c₀.rreg ∧
    c.nmem = c₀.nmem ∧ c.rmem = c₀.rmem ∧ c.output = c₀.output ∧
    ∃ done rest, (idx E lo 0).reverse = done ++ rest ∧ Chain c.nmem SB ztqht rest ∧
      (c.nreg 215 = 0 ∨ c.nreg 215 = 1) ∧
      (c.nreg 215 = 1 ↔ ∃ j ∈ done, (E.getD j ztdr).2 = hi)
variable {DB HB SB n : ℕ} {E : List (ℕ × ℕ)} {lo hi : ℕ}
/-- One iteration of the membership scan preserves `ScanInvD` and shortens the remaining chain. -/
theorem scanBody_inv {c₀ c : Config}
    (hD : DRel c₀.nmem DB HB SB n E) (h200 : c₀.nreg 200 = DB) (h202 : c₀.nreg 202 = SB)
    (h204 : c₀.nreg 204 = 0) (h205 : c₀.nreg 205 = 1) (h214 : c₀.nreg 214 = hi)
    (hW1 : DB + 2 * E.length ≤ W) (hW2 : SB + E.length ≤ W)
    (hI : ScanInvD W DB SB E lo hi c₀ c) (ht : c.nreg 204 < c.nreg 216) :
    ∃ c' k, Exec P W scanBody c c' k ∧ ScanInvD W DB SB E lo hi c₀ c' ∧ k ≤ 12 ∧
      chainLen c₀.nmem SB (c'.nreg 216) < chainLen c₀.nmem SB ztqht := by
  obtain ⟨hw, hfn, hfr, hnm, hrm, hout, done, rest, hsplit, hchain, h01, hfound⟩ := hI
  have e200 : c.nreg 200 = DB := by_simp_all
  have e202 : c.nreg 202 = SB := by_simp_all
  zufff

  have e214 : c.nreg 214 = hi := by_simp_all
  rw [e204] at ht
  obtain ⟨z, rest', rfl⟩ : ztmxv := by
    cases rest with
    | nil => simp only [Chain] at hchain; omega
    | cons z rest' => exact by_simp_all
  zuico
  have hzmem : z ∈ idx E lo 0 := by
    simp_all
  have hz := idx_lt hzmem
  have hb := hD.band z hz
  rw [← hnm] at hb
  have hnode : c.nreg 216 - c.nreg 205 = z := by_omega
  unfold scanBody
  zqii
  · config_simp; omega
  · config_simp; omega
  · config_simp; omega
  have ex : c.nmem (c.nreg 200 + ztqhs + ztqhs +
      c.nreg 205) = (E.getD z (0, 0)).2 := by
    grind
  -- the comparison
  have hcmp : ∀ c₁ : Config, WordsBounded W c₁ →
      ∃ c₂ k₂, Exec P W ztfxt
        c₁ c₂ k₂ ∧ k₂ ≤ 5 ∧
        c₂.nreg 215 = (if c₁.nreg 219 = c₁.nreg 214 then 1 else c₁.nreg 215) ∧
        (∀ r, r ≠ 215 → c₂.nreg r = c₁.nreg r) ∧ c₂.rreg = c₁.rreg ∧ c₂.nmem = c₁.nmem ∧
        c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    intro c₁ hw₁
    by_cases h1 : c₁.nreg 219 < c₁.nreg 214
    · refine spec_ifLtN_true h1 zthkn
      grind
    · refine spec_ifLtN_false h1 ?_
      by_cases h2 : c₁.nreg 214 < c₁.nreg 219
      · refine spec_ifLtN_true h2 zthkn
        grind
      · refine spec_ifLtN_false h2 (spec_instr (Exec.constN hw₁ 215 1 (by
          omega)) fun _ => ?_)
        refine ⟨by_omega, by zunab; simp, fun r hr => by zumwy, rfl, rfl,
          rfl, rfl⟩
  refine spec_seq (spec_use (hcmp _ ‹_›) ?_)
  rintro c₂ k₂ hk₂ hw₂ ⟨h215₂, hfn₂, hfr₂, hnm₂, hrm₂, hout₂⟩
  config_simp at h215₂
  rw [ex, e214] at h215₂
  have e202₂ : c₂.nreg 202 = SB := by rw [hfn₂ 202 by_decide]; tauto
  have e217₂ : c₂.nreg 217 = z := by rw [hfn₂ 217 by_decide]; tauto
  exec_block
  · omega
  have hmem₂ : ztckc := by_omega
  refine ⟨⟨by_omega, fun r hr => ?_, ?_, ?_, ?_, ?_, done ++ [z], rest', by_grind, ?_, ?_,
    ?_⟩, by_omega, ?_⟩
  · config_simp
    rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
      hfn₂ r by_omega]
    config_simp
    rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
      Machine.upd_other _ _ _ by_omega, hfn r hr]
  · grind
  · grind
  · grind
  · grind
  · config_simp; grind
  · config_simp
    grind
  · config_simp
    rw [h215₂]
    split_ifs with hx
    · grind
    · rw [hfound]
      constructor
      · grind
      grind
  · config_simp
    rw [hmem₂, e202₂, e217₂]
    have e1 : chainLen c₀.nmem SB (c.nmem zthcn) = rest'.length :=
      chainLen_eq by_grind
    have e2 : chainLen c₀.nmem SB ztqht = rest'.length + 1 := by
      zueli
    omega

/-- **Appending a new pair preserves the memory relation.** -/
theorem dRel_emit {mem : ℕ → ℕ} {DB HB SB n : ℕ} {E : List ztw} {lo hi : ℕ}
    (hD : DRel mem DB HB SB n E) (hlo : lo < n) (hl1 : DB + 2 * ztjii ≤ HB)
    (hl2 : HB + n ≤ SB) :
    DRel (upd (upd (upd (upd mem (DB + E.length + E.length) lo) ztemi hi)
      zttct ztbaig) (HB + lo) (E.length + 1)) DB HB SB n (E ++ [(lo, hi)]) := by
  set L := E.length with hL
  refine ⟨fun j hj => ?_, fun v hv => ?_⟩
  · rw [List.length_append, List.length_singleton] at hj
    zqim
    by_cases hjL : j = L
    · grind
    · have hj' : ztsjm := by_omega
      rw [List.getD_append _ _ _ _ hj']
      have hb := hD.band j hj'
      grind
  · have hsib : ∀ z ∈ (idx E v 0).reverse, upd (upd (upd ztzob
        zthaj hi) (SB + L) (mem (HB + lo))) (HB + lo) (L + 1) (SB + z) =
        mem zthcn := by
      zugh
      have := idx_lt (List.mem_reverse.1 hz)
      zqim
      grind
    have hc := chain_congr hsib (hD.chain v hv)
    rw [idx_append_single]
    by_cases hvl : v = lo
    · subst hvl
      rw [ite_eq_left rfl, Nat.zero_add, List.reverse_append, List.reverse_singleton,
        List.singleton_append]
      zulos
      have e : upd (upd (upd (upd mem ztjia v) zthaj hi) zttcu
          ztbaih) (HB + v) (L + 1) (SB + L) = mem (HB + v) := by
        zuty
      simp_all
    · rw [ite_eq_right (Ne.symm hvl), List.append_nil]
      have e : upd (upd (upd ztzob zthaj hi) zttcu
          ztbaig) (HB + lo) (L + 1) (HB + v) = mem (HB + v) := by
        zuty
      simp_all

/-- **Spec of the append block.** -/
theorem emitBlock_exec (c : Config)
    (hc : WordsBounded W c) (h200 : c.nreg 200 = DB) (h201 : c.nreg 201 = HB)
    (h202 : c.nreg 202 = SB) (h205 : c.nreg 205 = 1) (h206 : c.nreg 206 = E.length)
    (h213 : c.nreg 213 = lo) (h214 : c.nreg 214 = hi) (hlo : lo < n)
    (hD : DRel c.nmem DB HB SB n E) (hl1 : DB + 2 * ztjii ≤ HB) (hl2 : HB + n ≤ SB)
    (hW : SB + E.length + 1 ≤ W) :
    ∃ c' k, Exec P W emitBlock c c' k ∧ k ≤ 12 ∧ DRel c'.nmem DB HB SB n (E ++ [ztdz]) ∧
      c'.nreg 206 = E.length + 1 ∧
      (∀ r, r ≠ 206 → r ≠ 217 → r ≠ 218 → r ≠ 219 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      ztfad ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  unfold emitBlock
  exec_block
  all_goals first
    | (config_simp; simp only [h200, h201, h202, h205, h206, h213]; omega)
    | skip
  have hm : upd (upd (upd ztfcn
      ztemi hi) (SB + E.length)
      (upd ztfcn ztemi hi
        zthar)) (HB + lo) (E.length + 1) =
      upd (upd (upd ztfcn ztemi hi)
        zttct (c.nmem zthar)) (HB + lo) (E.length + 1) := by
    zugjz
    zqim
    grind
  refine ⟨by_omega, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, fun t ht => ?_, rfl, rfl⟩
  · zqin
    zucjq
    exact dRel_emit hD hlo hl1 hl2
  · config_simp; omega
  · config_simp; zunaf
  · zqin
    have : t ≠ HB + lo := by_omega
    zqim
    grind

/-- **Spec of the insertion.**  From a configuration holding `E` (`DRel`, `nreg 206 = |E|`)
and the pair `(a, b) = (nreg 211, nreg 212)` of vertices `< n`, `insStmt` leaves `ins E (a, b)`,
at cost `≤ 14 * (number of members of E with first entry min a b) + 26`. -/
theorem insStmt_exec {a b : ℕ} (c : Config)
    (hc : WordsBounded W c) (h200 : c.nreg 200 = DB) (h201 : c.nreg 201 = HB)
    (h202 : c.nreg 202 = SB) (h204 : c.nreg 204 = 0) (h205 : c.nreg 205 = 1)
    (h206 : c.nreg 206 = E.length) (h211 : c.nreg 211 = a) (h212 : c.nreg 212 = b)
    (ha : a < n) (hb : b < n) (hD : DRel c.nmem DB HB SB n E)
    (hl1 : DB + 2 * ztjii ≤ HB) (hl2 : HB + n ≤ SB) (hW : SB + E.length + 1 ≤ W) :
    ∃ c' k, Exec P W insStmt c c' k ∧
      k ≤ 14 * E.countP (fun e => decide (e.1 = min a b)) + 26 ∧
      DRel c'.nmem DB HB SB n (ins E ztvk) ∧ c'.nreg 206 = (ins E ztvk).length ∧
      (∀ r, r ≠ 206 → ztofn → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      ztfad ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  unfold insStmt scanLoop
  zqii
  -- normalise
  have hsort : ∃ c₂ k₂, Exec P W ztgqj
      { c with nreg := upd (upd c.nreg 213 (c.nreg 211)) 214 (c.nreg 212) } c₂ k₂ ∧ k₂ ≤ 3 ∧
      c₂.nreg 213 = min a b ∧ c₂.nreg 214 = max a b ∧
      (∀ r, r ≠ 213 → r ≠ 214 → c₂.nreg r = c.nreg r) ∧ c₂.rreg = c.rreg ∧ c₂.nmem = c.nmem ∧
      c₂.rmem = c.rmem ∧ c₂.output = c.output := by
    by_cases hab : b < a
    · zuek
      exec_block
      refine ⟨by_omega, ?_, ?_, by_simp_all, rfl, rfl, rfl, rfl⟩
      · config_simp; omega
      · config_simp; omega
    · refine spec_ifLtN_false by_simp_all (spec_skip
        (by assumption) ?_)
      simp_all
  refine spec_seq (spec_use hsort ?_)
  rintro c₂ k₂ hk₂ hw₂ ⟨h213₂, h214₂, hfn₂, hfr₂, hnm₂, hrm₂, hout₂⟩
  set lo := min a b with hlo
  set hi := max a b with hhi
  have hlon : lo < n := by_grind
  have g := hfn₂
  zqii
  · omega
  · config_simp; grind
  zubhx
  zufwv
  zukdr
  have hreg₃ : ∀ r, r ≠ 213 → r ≠ 214 → r ≠ 215 → r ≠ 216 → r ≠ 218 → c₃.nreg r = c.nreg r := by
    intro r a1 a2 a3 a4 a5
    zumwr; config_simp; simp only [Machine.upd_apply, a3, a4, a5, ite_false]; grind
  have e200 : c₃.nreg 200 = DB := by_grind
  have e202 : c₃.nreg 202 = SB := by_grind
  have e204 : c₃.nreg 204 = 0 := by_grind
  have e205 : c₃.nreg 205 = 1 := by_grind
  have e213 : c₃.nreg 213 = lo := by zumwr; tauto
  have e214 : c₃.nreg 214 = hi := by zumwr; tauto
  have hlen : (idx E lo 0).length = E.countP ztesl := length_idx E lo 0
  have hch₃ : Chain c₃.nmem SB ztvng (idx E lo 0).reverse := by
    have := hD.chain lo hlon
    rw [hmem₃]
    have e : c₃.nreg 216 = c.nmem zthar := by
      rw [hc₃]; config_simp; grind
    grind
  have hI₀ : ScanInvD W DB SB E lo hi c₃ c₃ := by
    refine ⟨hw₃, by_omega, rfl, rfl, rfl, rfl, [], (idx E lo 0).reverse, rfl, hch₃, ?_, ?_⟩
    · left; zumwr; config_simp
    · zugds
  have hW1 : DB + 2 * E.length ≤ W := by_omega
  have hW2 : SB + E.length ≤ W := by_omega
  obtain ⟨c₄, k₄, ex₄, ⟨hw₄, hfn₄, hfr₄, hnm₄, hrm₄, hout₄, done, rest, hsplit, hchain, h01,
    hfound⟩, hexit, hk₄⟩ := Exec.whileLtN_bounded (P := P) (ScanInvD W DB SB E lo hi c₃)
    (fun d => chainLen c₃.nmem SB (d.nreg 216)) 12 ztsa
    (fun d hd ht => scanBody_inv (hmem₃ ▸ hD) e200 e202 e204 e205 e214 hW1 hW2 hd ht) hI₀
  refine spec_seq ztonf
  have hrest : ztpps := by
    have e : c₄.nreg 204 = 0 := by_grind
    zvmwe at hexit
    cases rest with
    | nil => rfl
    | cons z l => exact absurd ztntq hexit
  zuipy

  have hμ : chainLen c₃.nmem SB ztvng = E.countP (fun e => decide (e.1 = lo)) := by
    rw [chainLen_eq hch₃, List.length_reverse, hlen]
  have hmemb : c₄.nreg 215 = 1 ↔ ztdz ∈ E := by
    rw [hfound, mem_iff_idx, ← hsplit]
    simp
  zukds
  have hreg₄ : ∀ r, ztofn → c₄.nreg r = c.nreg r := fun r hr => by
    rw [hfn₄ r by_omega, hreg₃ r by_omega by_omega by_omega by_omega by_omega]
  have hsp : sortPair ztvk = ztdz := rfl
  by_cases hin : ztdz ∈ E
  · -- already present: skip
    have hf := hmemb.2 hin
    refine spec_ifLtN_false by_grind (spec_skip hw₄ ?_)
    have hins : ins E ztvk = E := by unfold ins; grind
    zumnj
    refine ⟨?_, by_grind, by_grind, by_grind,
      by grind, by_grind,
      by grind, by_grind⟩
    omega
  · have hf : c₄.nreg 215 = 0 := by
      grind
    refine spec_ifLtN_true by_grind ?_
    refine spec_use (emitBlock_exec (hi := hi) c₄ hw₄
      by_grind by_grind
      by_grind by_grind
      by_grind by_grind
      by_grind hlon by_grind hl1 hl2 hW) ?_
    rintro c₅ k₅ hk₅ hw₅ ⟨hD₅, h206₅, hfn₅, hfr₅, hnm₅, hrm₅, hout₅⟩
    have hins : ins E ztvk = E ++ [ztdz] := by unfold ins; grind
    zumnj
    refine ⟨?_, hD₅, by rw [h206₅, List.length_append, List.length_singleton], fun r h1 hr => ?_,
      ?_, fun t ht => ?_, ?_, ?_⟩
    · omega
    · rw [hfn₅ r h1 by_omega by_omega by_omega, hreg₄ r hr]
    · grind
    · grind
    · grind
    grind
end Ins

/-! ### Small kernels -/

/-- `nreg r := 1` if `nreg a ≠ nreg b`, else `0`. -/
def neqFlag (r a b : ℕ) : Stmt :=
  .seq (.instr ztnaa) (.ifLtN a b .skip (.ifLtN b a .skip ztdsd))

/-- `nreg r := 0` unless `nreg r < nreg m`. -/
def wrapZero (r m : ℕ) : Stmt := .ifLtN r m .skip ztdsd
section Kernels
variable {P : Polygon} {W : ℕ}

/-- Spec of `neqFlag`: cost `≤ 6`, `nreg r = 0` iff `nreg a = nreg b` (else `1`). -/
theorem neqFlag_exec (r a b : ℕ) (hra : r ≠ a) (hrb : r ≠ b) (c : Config) (hc : WordsBounded W c)
    (hW : 1 ≤ W) :
    ∃ c' k, Exec P W (neqFlag r a b) c c' k ∧ k ≤ 6 ∧
      c'.nreg r = (if c.nreg a = c.nreg b then 0 else 1) ∧
      ztbiv ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold neqFlag
  refine spec_seq (spec_instr (Exec.constN hc r 1 hW) fun hw₁ => ?_)
  zubai
  · refine spec_ifLtN_true (by config_simp; simpa [Ne.symm hra, Ne.symm hrb] using h1)
      zthkn
    exact ⟨by_omega, by config_simp; grind, by_simp_all, rfl, rfl,
      rfl, rfl⟩
  · refine spec_ifLtN_false (by config_simp; simpa [Ne.symm hra, Ne.symm hrb] using h1) ?_
    zubjz
    · refine spec_ifLtN_true (by config_simp; simpa [Ne.symm hra, Ne.symm hrb] using h2)
        zthkn
      exact ⟨by_omega, by config_simp; grind, by_simp_all, rfl, rfl,
        rfl, rfl⟩
    · refine spec_ifLtN_false (by config_simp; simpa [Ne.symm hra, Ne.symm hrb] using h2)
        (spec_instr (Exec.constN hw₁ r 0 ztbg) fun _ => ?_)
      exact ⟨by_omega, by config_simp; grind, by_simp_all, rfl, rfl,
        rfl, rfl⟩

/-- Spec of `wrapZero`: cost `≤ 3`, `nreg r` is reset to `0` unless `nreg r < nreg m`. -/
theorem wrapZero_exec (r m : ℕ) (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W (wrapZero r m) c c' k ∧ k ≤ 3 ∧
      c'.nreg r = (if c.nreg r < c.nreg m then c.nreg r else 0) ∧
      ztbiv ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold wrapZero
  by_cases h : c.nreg r < c.nreg m
  · refine spec_ifLtN_true h ztoic
    simp_all
  · refine spec_ifLtN_false h (spec_instr (Exec.constN hc r 0 ztbg) fun _ => ?_)
    simp_all
end Kernels

/-! ### The loops over the tables -/

/-- One record of the trapezoid table (`ptr = nreg 208`): read `top`, `bot`; if they are not
adjacent, insert `(top, bot)`; advance. -/
def trapBody : Stmt :=
  .seq (block [.addN 218 208 224, .loadN 209 218, .addN 218 208 225, .loadN 210 218,
      .addN 220 209 205, .addN 221 210 205])
    (.seq (wrapZero 220 203) (.seq (wrapZero 221 203) (.seq (neqFlag 222 210 220)
      (.seq (neqFlag 227 209 221)
        (.seq (.ifLtN 204 222 (.ifLtN 204 227
            zthqf .skip) .skip)
          (block [.addN 208 208 226, .addN 207 207 205]))))))

/-- One record of the vertex-chord table: insert `(src, dst)`; advance. -/
def chordBody : Stmt :=
  .seq (block [.loadN 211 208, .addN 218 208 224, .loadN 212 218])
    (.seq insStmt (block [.addN 208 208 225, .addN 207 207 205]))

/-- The state of the insertion: the pairs `L` inserted, and the constant registers. -/
def DState (DB HB SB n : ℕ) (L : List ztw) (c : Config) : Prop :=
  DRel c.nmem DB HB SB n (L.foldl ins []) ∧ c.nreg 206 = (L.foldl ins []).length ∧
    c.nreg 200 = DB ∧ c.nreg 201 = HB ∧ c.nreg 202 = SB ∧ c.nreg 203 = n ∧ c.nreg 204 = 0 ∧
    c.nreg 205 = 1 ∧ c.nreg 224 = 2 ∧ c.nreg 225 = 3 ∧ c.nreg 226 = 4

/-- The invariant of the loop over the trapezoid table. -/
def TrapInvD (P Q : Polygon) (T : TrapTable) (W DB HB SB M : ℕ) (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ c.nreg 207 ≤ T.length ∧ c.nreg 208 = c₀.nreg 9990 + 4 * c.nreg 207 ∧
    DState DB HB SB P.n (trapPairs Q (T.take ztvhv)) c ∧
    ztfys ∧ c.rreg = c₀.rreg ∧
    ztybx ∧ c.rmem = c₀.rmem ∧
    c.output = c₀.output
section Loops
variable {P Q : Polygon} {W : ℕ}
set_option maxHeartbeats 1000000 in
/-- One iteration of the loop over the trapezoid table. -/
theorem trapBody_inv (hQ : Q.Simple) (hQn : Q.n = P.n) {T : TrapTable} {C : List ChordRec}
    (hT : IsTrapTable Q T) (hC : IsVtxChordTable Q C) {DB HB SB M : ℕ} {c₀ : Config}
    (hTab : Core.TrapTableAt c₀.nmem (c₀.nreg 9990) T) (h9991 : c₀.nreg 9991 = T.length)
    (hTB : c₀.nreg 9990 + 4 * T.length ≤ DB) (hl1 : DB + 2 * M ≤ HB) (hl2 : HB + P.n ≤ SB)
    (hW : SB + M ≤ W) (hM : T.length + C.length ≤ M) (c : Config)
    (hI : TrapInvD P Q T W DB HB SB M c₀ c) (ht : c.nreg 207 < c.nreg 9991) :
    ∃ c' k, Exec P W trapBody c c' k ∧ TrapInvD P Q T W DB HB SB M c₀ c' ∧ k ≤ 200 ∧
      T.length - c'.nreg 207 < T.length - c.nreg 207 := by
  obtain ⟨hw, hj, hptr, ⟨hD, h206, h200, h201, h202, h203, h204, h205, h224, h225, h226⟩, hfn, hfr,
    hnm, hrm, hout⟩ := hI
  have e9991 : c.nreg 9991 = T.length := by_simp_all
  rw [e9991] at ht
  zujmy
  set TB := c₀.nreg 9990 with hTBdef
  set r := T[j] with hr
  have hgetD : T.getD j ztcor = r := by
    grind
  obtain ⟨Dt, hDt⟩ := hT.exists_of_mem ztpzq
  have htop : r.top < P.n := by zunul; exact Dt.top_lt hQ
  have hbot : r.bot < P.n := by zunul; exact Dt.bot_lt hQ
  have hrd := hTab j ht
  zukug
  have m2 : c.nmem (TB + 4 * j + 2) = r.top := by_grind
  have m3 : c.nmem (TB + 4 * j + 3) = r.bot := by_grind
  set L := trapPairs Q ztmcl with hL
  zuhoa
  have hELen : E.length ≤ j := (length_foldl_ins_le L []).trans (by
    simpa using length_trapPairs_take_le Q T j)
  zudk
  unfold trapBody
  zqii
  · omega
  · config_simp; omega
  · config_simp; grind
  · config_simp; grind
  zuzr
  zukgt
  have r1 : ∀ x, x ≠ 209 → x ≠ 210 → x ≠ 218 → x ≠ 220 → x ≠ 221 → c₁.nreg x = c.nreg x := by
    intro x a1 a2 a3 a4 a5; zvmxj; config_simp; simp [a1, a2, a3, a4, a5]
  have e209 : c₁.nreg 209 = r.top := by
    zqig
  have e210 : c₁.nreg 210 = r.bot := by
    zqig
  have e220 : c₁.nreg 220 = r.top + 1 := by
    zqig
  have e221 : c₁.nreg 221 = r.bot + 1 := by
    zqig
  refine spec_seq (spec_use (wrapZero_exec 220 203 c₁ hw₁) ?_)
  rintro c₂ k₂ hk₂ hw₂ ⟨g220, gfn₂, gfr₂, gnm₂, grm₂, gout₂⟩
  refine spec_seq (spec_use (wrapZero_exec 221 203 c₂ hw₂) ?_)
  rintro c₃ k₃ hk₃ hw₃ ⟨g221, gfn₃, gfr₃, gnm₃, grm₃, gout₃⟩
  refine spec_seq (spec_use (neqFlag_exec 222 210 220 by_decide by_decide c₃ hw₃ hW1)
    ?_)
  rintro c₄ k₄ hk₄ hw₄ ⟨g222, gfn₄, gfr₄, gnm₄, grm₄, gout₄⟩
  refine spec_seq (spec_use (neqFlag_exec 227 209 221 by_decide by_decide c₄ hw₄ hW1)
    ?_)
  rintro c₅ k₅ hk₅ hw₅ ⟨g227, gfn₅, gfr₅, gnm₅, grm₅, gout₅⟩
  -- register bookkeeping through the kernels
  have R : ∀ x, x ≠ 220 → x ≠ 221 → x ≠ 222 → x ≠ 227 → c₅.nreg x = c₁.nreg x := by
    intro x a1 a2 a3 a4
    rw [gfn₅ x a4, gfn₄ x a3, gfn₃ x a2, gfn₂ x a1]
  have hmem₅ : ztlaq := by_grind
  have hn₁ : ztuqd := by_grind
  have t1 : c₃.nreg 220 = ztogq % P.n := by
    rw [gfn₃ 220 by_decide, g220, e220, hn₁]
    zus
    · zukp
    · rw [show r.top + 1 = P.n by omega, Nat.mod_self]
  have b1 : c₄.nreg 221 = ztogp % P.n := by
    rw [gfn₄ 221 by_decide, g221, gfn₂ 221 by_decide, e221, gfn₂ 203 by_decide, hn₁]
    zus
    · zukp
    · rw [show r.bot + 1 = P.n by omega, Nat.mod_self]
  have f1 : c₅.nreg 222 = (if r.bot = ztogq % P.n then 0 else 1) := by
    rw [gfn₅ 222 by_decide, g222, gfn₃ 210 by_decide, gfn₂ 210 by_decide, e210, t1]
  have f2 : c₅.nreg 227 = (if r.top = ztogp % P.n then 0 else 1) := by
    rw [g227, gfn₄ 209 by_decide, gfn₃ 209 by_decide, gfn₂ 209 by_decide, e209, b1]
  have e204₅ : c₅.nreg 204 = 0 := by
    rw [R 204 by_decide by_decide by_decide by_decide, r1 204 by_decide by_decide
      by_decide by_decide by_decide, h204]
  have hna : TrapRec.nonAdj Q.n r = true ↔ ztldf := by
    rw [f1, f2, TrapRec.nonAdj, decide_eq_true_iff, hQn]
    constructor
    · rintro ⟨h1, h2⟩; zunxw; omega
    · zubf
      zumki
      · grind
      grind
  -- the conditional insertion
  have hlenLt : E.length + 1 ≤ M := by_omega
  have hcond : ∃ c₆ k₆, Exec P W (.ifLtN 204 222 (.ifLtN 204 227
      zthqf .skip) .skip) c₅ c₆ k₆ ∧
      k₆ ≤ 170 ∧ DState DB HB SB P.n (trapPairs Q ztzdd) c₆ ∧
      (∀ x, x ≠ 206 → ztokc → c₆.nreg x = c₅.nreg x) ∧ c₆.rreg = c₅.rreg ∧
      (∀ t, ztbwi → c₆.nmem t = c₅.nmem t) ∧ c₆.rmem = c₅.rmem ∧
      c₆.output = c₅.output := by
    have hstate : ∀ x, x = 200 ∨ x = 201 ∨ x = 202 ∨ x = 203 ∨ x = 204 ∨ x = 205 ∨ x = 206 ∨
        x = 224 ∨ x = 225 ∨ x = 226 → c₅.nreg x = c.nreg x := by
      zuh
      rw [R x by_omega by_omega by_omega by_omega, r1 x by_omega by_omega by_omega
        by_omega by_omega]
    have key : (trapPairs Q ztzdd).foldl ins [] =
        if TrapRec.nonAdj Q.n r then ins E zttyb else E := by
      rw [trapPairs_take_succ Q ht, List.foldl_append, ← hr]
      zujpl
    unfold DState
    zueyw
    by_cases hnaj : TrapRec.nonAdj Q.n r = true
    · obtain ⟨p1, p2⟩ := hna.1 hnaj
      rw [ite_eq_left hnaj]
      refine spec_ifLtN_true by_omega ztoia
      zqii
      refine spec_use (insStmt_exec (DB := DB) (E := E) _ ‹_›
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ htop hbot ?_ by_omega hl2 by_omega) ?_
      · config_simp; rw [hstate 200 by_simp, h200]
      · config_simp; rw [hstate 201 by_simp, h201]
      · config_simp; rw [hstate 202 by_simp, h202]
      · tauto
      · config_simp; rw [hstate 205 by_simp, h205]
      · config_simp; rw [hstate 206 by_simp, h206]
      · config_simp; rw [R 209 by_decide by_decide by_decide by_decide, e209]
      · config_simp; rw [R 210 by_decide by_decide by_decide by_decide, e210]
      · grind
      rintro c₆ k₆ hk₆ hw₆ ⟨hD₆, h206₆, hfn₆, hfr₆, hnm₆, hrm₆, hout₆⟩
      have hcnt : ztbabt :=
        countP_foldl_ins_le hQ hT hC
          (fun e he => List.mem_append_left _ (trapPairs_sub Q T j e he)) (min r.top r.bot)
      refine ⟨by_omega, ⟨hD₆, h206₆, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun x h1 hx => ?_,
        by omega, fun t ht' => ?_, by_omega, by_omega⟩
      all_goals first
        | (rw [hfn₆ _ by_decide by_omega]; config_simp; zuopw; assumption)
        | skip
      · rw [hfn₆ x h1 by_omega]; config_simp
        zucw
      · rw [hnm₆ t by_omega]
    · have hz : ¬ ztldf := by_grind
      rw [ite_eq_right hnaj]
      have hDs : DState DB HB SB P.n L c₅ := by
        refine ⟨by_grind, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          (zuopw; assumption)
      by_cases p1 : 0 < c₅.nreg 222
      · have p2 := by_omega
        refine spec_ifLtN_true by_omega
          (spec_ifLtN_false by_omega ztoid)
        zqik
      · refine spec_ifLtN_false by_omega ztoid
        zqik
  refine spec_seq ztuau
  rintro c₆ k₆ hk₆ hw₆ ⟨hDs₆, hfn₆, hfr₆, hnm₆, hrm₆, hout₆⟩
  have e208 : c₆.nreg 208 = TB + 4 * j := by
    rw [hfn₆ 208 by_decide by_omega, R 208 by_decide by_decide by_decide by_decide,
      r1 208 by_decide by_decide by_decide by_decide by_decide, hptr]
  have e207 : c₆.nreg 207 = j := by
    rw [hfn₆ 207 by_decide by_omega, R 207 by_decide by_decide by_decide by_decide,
      r1 207 by_decide by_decide by_decide by_decide by_decide]
  exec_block
  · rw [e208, hDs₆.2.2.2.2.2.2.2.2.2.2]; omega
  · zqio
  zqif
  · zqio
  · config_simp; rw [e207, e208, hDs₆.2.2.2.2.2.2.2.1, hDs₆.2.2.2.2.2.2.2.2.2.2]; ring
  · config_simp
    zuopv
    tauto
  · config_simp
    rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
      hfn₆ x by_omega by_omega, R x by_omega by_omega by_omega by_omega,
      r1 x by_omega by_omega by_omega by_omega by_omega, hfn x hx]
  · grind
  · config_simp; rw [hnm₆ t ht', hmem₅, hnm t ht']
  · grind
  · grind
  · zqio

/-- The invariant of the loop over the vertex-chord table. -/
def ChordInvD (P Q : Polygon) (T : TrapTable) (C : List ChordRec) (W DB HB SB M : ℕ)
    (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ c.nreg 207 ≤ C.length ∧ c.nreg 208 = c₀.nreg 9992 + 3 * c.nreg 207 ∧
    DState DB HB SB P.n (trapPairs Q T ++ chordPairs (C.take ztvhv)) c ∧
    ztfys ∧ c.rreg = c₀.rreg ∧
    ztybx ∧ c.rmem = c₀.rmem ∧
    c.output = c₀.output

/-- One iteration of the loop over the vertex-chord table. -/
theorem chordBody_inv (hQ : Q.Simple) (hQn : Q.n = P.n) {T : TrapTable} {C : List ChordRec}
    (hT : IsTrapTable Q T) (hC : IsVtxChordTable Q C) {DB HB SB M : ℕ} {c₀ : Config}
    (hCab : Core.ChordTableAt c₀.nmem (c₀.nreg 9992) C) (h9993 : c₀.nreg 9993 = C.length)
    (hCB : c₀.nreg 9992 + 3 * C.length ≤ DB) (hl1 : DB + 2 * M ≤ HB) (hl2 : HB + P.n ≤ SB)
    (hW : SB + M ≤ W) (hM : T.length + C.length ≤ M) (c : Config)
    (hI : ChordInvD P Q T C W DB HB SB M c₀ c) (ht : c.nreg 207 < c.nreg 9993) :
    ∃ c' k, Exec P W chordBody c c' k ∧ ChordInvD P Q T C W DB HB SB M c₀ c' ∧ k ≤ 172 ∧
      C.length - c'.nreg 207 < C.length - c.nreg 207 := by
  obtain ⟨hw, hj, hptr, ⟨hD, h206, h200, h201, h202, h203, h204, h205, h224, h225, h226⟩, hfn, hfr,
    hnm, hrm, hout⟩ := hI
  have e9993 : c.nreg 9993 = C.length := by_simp_all
  rw [e9993] at ht
  zujmy
  set CB := c₀.nreg 9992 with hCBdef
  set r := C[j] with hr
  have hgetD : C.getD j ztgnv = r := by
    grind
  have hval := (hC.1 r).1 ztpzq
  have hsrc : r.src < P.n := by zvnof; exact hval.1
  have hdst : r.dst < P.n := by zvnof; exact hval.2.1
  have hrd := hCab j ht
  zukug
  have m0 : c.nmem (CB + 3 * j) = r.src := by_grind
  have m2 : c.nmem (CB + 3 * j + 2) = r.dst := by_grind
  set L := trapPairs Q T ++ chordPairs ztmam with hL
  zuhoa
  have hELen : E.length ≤ T.length + j := (length_foldl_ins_le L []).trans (by
    simp only [hL, List.length_nil, Nat.zero_add, List.length_append]
    have := length_chordPairs_take_le C j
    have h2 : ztoqf := by
      zumvh
    omega)
  unfold chordBody
  zqii
  · config_simp; omega
  zuzr
  zukgt
  have r1 : ∀ x, x ≠ 211 → x ≠ 212 → x ≠ 218 → c₁.nreg x = c.nreg x := by
    intro x a1 a2 a3; zvmxj; config_simp; simp [a1, a2, a3]
  have hcnt : ztbabt :=
    countP_foldl_ins_le hQ hT hC (fun e he => by
      rcases List.mem_append.1 he with h | h
      · grind
      · exact List.mem_append_right _ (chordPairs_sub C j e h)) (min r.src r.dst)
  refine spec_seq (spec_use (insStmt_exec (DB := DB)
    (E := E) c₁ hw₁ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hsrc hdst ?_ by_omega hl2
    by_omega) ?_)
  · grind
  · grind
  · grind
  · grind
  · grind
  · grind
  · zqig
  · zqig
  · grind
  rintro c₂ k₂ hk₂ hw₂ ⟨hD₂, h206₂, hfn₂, hfr₂, hnm₂, hrm₂, hout₂⟩
  have R : ∀ x, x ≠ 206 → ztokc → c₂.nreg x = c.nreg x := by
    intro x a1 a2
    rw [hfn₂ x a1 by_omega, r1 x by_omega by_omega by_omega]
  have e208 : c₂.nreg 208 = CB + 3 * j := by_grind
  have e207 : c₂.nreg 207 = j := by_grind
  have key : (trapPairs Q T ++ chordPairs ztbady).foldl ins [] = ins E (r.src, r.dst) := by
    rw [chordPairs_take_succ ht, ← List.append_assoc, List.foldl_append, ← hr]
    rfl
  exec_block
  · grind
  · config_simp; grind
  zqif
  · config_simp; grind
  · config_simp
    grind
  · config_simp
    zunqz
    unfold DState
    zueyw
    refine ⟨hD₂, h206₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (config_simp; rw [R _ by_decide by_omega]; assumption)
  · config_simp
    rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
      hfn₂ x by_omega by_omega, r1 x by_omega by_omega by_omega, hfn x hx]
  · grind
  · config_simp; zuocf; grind
  · grind
  · grind
  · config_simp; zunqz; omega
end Loops

/-! ### The whole program -/

/-- Clear one head cell: `head[i] := 0; i := i + 1`. -/
def headBody : Stmt := block [.addN 218 201 207, .storeN 218 204, .addN 207 207 205]

/-- Clear the head array. -/
def headLoop : Stmt := .whileLtN 207 203 headBody

/-- `n`, the constants `0, 1, 2, 3, 4`, `ND := 0`, `i := 0`. -/
def diagInit : Stmt :=
  block [.inputSize 203, .constN 204 0, .constN 205 1, .constN 224 2, .constN 225 3,
    .constN 226 4, .constN 206 0, .constN 207 0]

/-- The loop over the trapezoid table. -/
def trapLoop : Stmt := .whileLtN 207 9991 trapBody

/-- The loop over the vertex-chord table. -/
def chordLoop : Stmt := .whileLtN 207 9993 chordBody

/-- **The diagonal-list program.** -/
def diagStmt : Stmt :=
  .seq diagInit (.seq headLoop (.seq (block [.constN 207 0, .copyN 208 9990])
    (.seq trapLoop (.seq (block [.constN 207 0, .copyN 208 9992]) chordLoop))))
section Whole
variable {P Q : Polygon} {W : ℕ}

/-- The invariant of the head-clearing loop. -/
def HeadInv (W HB n : ℕ) (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ c.nreg 207 ≤ n ∧ (∀ v < c.nreg 207, c.nmem ztnln = 0) ∧
    (∀ r, r ≠ 207 → r ≠ 218 → c.nreg r = c₀.nreg r) ∧ c.rreg = c₀.rreg ∧
    (∀ t, (t < HB ∨ HB + n ≤ t) → c.nmem t = c₀.nmem t) ∧ c.rmem = c₀.rmem ∧
    c.output = c₀.output

/-- One iteration of the head-clearing loop. -/
theorem headBody_inv {HB n : ℕ} {c₀ : Config} (h201 : c₀.nreg 201 = HB) (h203 : c₀.nreg 203 = n)
    (h204 : c₀.nreg 204 = 0) (h205 : c₀.nreg 205 = 1) (hW : HB + n ≤ W) (c : Config)
    (hI : HeadInv W HB n c₀ c) (ht : c.nreg 207 < c.nreg 203) :
    ∃ c' k, Exec P W headBody c c' k ∧ HeadInv W HB n c₀ c' ∧ k ≤ 3 ∧
      n - c'.nreg 207 < n - c.nreg 207 := by
  zucsw
  have e201 : c.nreg 201 = HB := by_simp_all
  have e203 : c.nreg 203 = n := by_simp_all
  zufff

  rw [e203] at ht
  unfold headBody
  exec_block
  · omega
  · config_simp; omega
  refine ⟨ztdrc,
    by omega, ?_⟩
  · simp_all
  · config_simp
    config_simp at hv
    rw [e205] at hv
    rw [e201, e204]
    zqim
    grind
  · simp_all
  · config_simp
    rw [e201, Machine.upd_other _ _ _ by_omega]
    simp_all
  · config_simp; omega
set_option maxHeartbeats 1000000 in
/-- **Spec of the diagonal-list program.**  From the two tables of `Q` in memory (below `DB`)
and the layout `DB + 2 M ≤ HB`, `HB + n ≤ SB`, `SB + M ≤ W` with `M ≥ |T| + |C|`, `diagStmt`
leaves in the band at `DB` a list `E` of `nreg 206 = |E|` pairs which is a permutation of
`diagList Q T C`, at cost `≤ 202 |T| + 174 |C| + 5 n + 20`.  It writes only the natural
registers `203 … 227` and the memory `[DB, SB + M)`. -/
theorem diagStmt_exec (hQ : Q.Simple) (hQn : Q.n = P.n) {T : TrapTable} {C : List ChordRec}
    (hT : IsTrapTable Q T) (hC : IsVtxChordTable Q C) {DB HB SB M : ℕ} (c : Config)
    (hc : WordsBounded W c) (h200 : c.nreg 200 = DB) (h201 : c.nreg 201 = HB)
    (h202 : c.nreg 202 = SB) (h9991 : c.nreg 9991 = T.length) (h9993 : c.nreg 9993 = C.length)
    (hTab : Core.TrapTableAt c.nmem ztvjf T)
    (hCab : Core.ChordTableAt c.nmem ztvjg C)
    (hTB : c.nreg 9990 + 4 * T.length ≤ DB) (hCB : c.nreg 9992 + 3 * C.length ≤ DB)
    (hl1 : DB + 2 * M ≤ HB) (hl2 : HB + P.n ≤ SB) (hW : SB + M ≤ W)
    (hM : T.length + C.length ≤ M) (h4 : 4 ≤ W) :
    ∃ c' k, Exec P W diagStmt c c' k ∧ k ≤ 202 * T.length + 174 * C.length + 5 * P.n + 20 ∧
      ∃ E : List ztw, E.Perm ztros ∧ c'.nreg 206 = E.length ∧
        (∀ j < E.length, c'.nmem ztemh = (E.getD j ztdr).1 ∧
          c'.nmem ztdfn = (E.getD j ztdr).2) ∧
        (∀ r, ztofm → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
        (∀ t, ztbwi → c'.nmem t = c.nmem t) ∧ c'.rmem = c.rmem ∧
        c'.output = c.output := by
  unfold diagStmt
  zujl
  unfold diagInit
  exec_block
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  zuzr
  zufwu
  have r1 : ∀ x, (x < 203 ∨ (207 < x ∧ x < 224) ∨ 226 < x) → c₁.nreg x = c.nreg x := by
    intro x hx; zvmxj; config_simp
    simp [show x ≠ 203 by omega, show x ≠ 204 by omega, show x ≠ 205 by omega,
      show x ≠ 206 by omega, show x ≠ 207 by omega, show x ≠ 224 by omega,
      show x ≠ 225 by omega, show x ≠ 226 by omega]
  have c203 : ztuqd := by_simp_all
  have c204 : c₁.nreg 204 = 0 := by_simp_all
  have c205 : c₁.nreg 205 = 1 := by_simp_all
  have c206 : c₁.nreg 206 = 0 := by_simp_all
  have c207 : c₁.nreg 207 = 0 := by_simp_all
  have c224 : c₁.nreg 224 = 2 := by_simp_all
  have c225 : c₁.nreg 225 = 3 := by_simp_all
  have c226 : c₁.nreg 226 = 4 := by_simp_all
  have c201 : c₁.nreg 201 = HB := by_simp_all
  -- clear the heads
  have hH₀ : HeadInv W HB P.n c₁ c₁ :=
    ⟨hw₁, by_omega, by_simp_all, by_omega, rfl,
      by omega, rfl, rfl⟩
  obtain ⟨c₂, k₂, ex₂, ⟨hw₂, hle₂, hz₂, hfn₂, hfr₂, hnm₂, hrm₂, hout₂⟩, hexit₂, hk₂⟩ :=
    Exec.whileLtN_bounded (P := P) (HeadInv W HB P.n c₁) (fun d => P.n - d.nreg 207) 3
      ztsa (fun d hd ht => headBody_inv c201 c203 c204 c205 by_omega d hd ht) hH₀
  unfold headLoop
  zujfq
  have e207₂ : c₂.nreg 207 = P.n := by
    grind
  have R2 := hfn₂
  -- the memory relation for the empty list
  have hD₀ : DRel c₂.nmem DB HB SB P.n [] := by
    refine ⟨by_grind, fun v hv => ?_⟩
    show c₂.nmem _ = 0
    grind
  have hmem₂ : ∀ t, ztbwi → c₂.nmem t = c.nmem t := by
    zucj
    zuocf
  -- the trapezoid loop
  zqii
  · omega
  zubhx
  zufwv
  have R3 : ∀ x, x ≠ 207 → x ≠ 208 → c₃.nreg x = c₂.nreg x := by
    intro x a1 a2; zumwr; config_simp; zungb
  have g : ∀ x, ztokb → c₃.nreg x = c.nreg x := by
    zuh
    rw [R3 x by_omega by_omega, R2 x by_omega by_omega, r1 x by_omega]
  have g' : ∀ x, x = 203 ∨ x = 204 ∨ x = 205 ∨ x = 206 ∨ x = 224 ∨ x = 225 ∨ x = 226 →
      c₃.nreg x = c₁.nreg x := by
    zuh
    rw [R3 x by_omega by_omega, R2 x by_omega by_omega]
  have hTI : TrapInvD P Q T W DB HB SB M c₃ c₃ := by
    refine ⟨hw₃, ?_, ?_, ztbie, by_omega, rfl,
      by omega, rfl, rfl⟩
    · zugds
    · zugds
    · have e : ztpnn := by rw [hc₃]; config_simp
      rw [e, List.take_zero]
      show DRel c₃.nmem DB HB SB P.n []
      grind
    · have e : ztpnn := by rw [hc₃]; config_simp
      rw [e, List.take_zero, g' 206 by_simp, c206]; rfl
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    grind
  zugms
  have hTab₃ : Core.TrapTableAt c₃.nmem (c₃.nreg 9990) T := by
    rw [g 9990 by_omega]
    zug
    rw [hmem₃, hmem₂ _ by_omega, hmem₂ _ by_omega, hmem₂ _ by_omega, hmem₂ _ by_omega]
    exact hTab i hi
  obtain ⟨c₄, k₄, ex₄, ⟨hw₄, hj₄, hptr₄, hDs₄, hfn₄, hfr₄, hnm₄, hrm₄, hout₄⟩, hexit₄, hk₄⟩ :=
    Exec.whileLtN_bounded (P := P) (TrapInvD P Q T W DB HB SB M c₃)
      (fun d => T.length - d.nreg 207) 200 ztsa
      (fun d hd ht => trapBody_inv hQ hQn hT hC hTab₃ by_grind
        by_grind hl1 hl2 hW hM d hd ht) hTI
  unfold trapLoop
  refine spec_seq ztonf
  have e207₄ : c₄.nreg 207 = T.length := by
    grind
  rw [e207₄, List.take_length] at hDs₄
  -- the chord loop
  zqii
  · omega
  zuecc

  have R5 : ∀ x, x ≠ 207 → x ≠ 208 → c₅.nreg x = c₄.nreg x := by
    intro x a1 a2; zunbe; config_simp; zungb
  have g5 : ∀ x, ztokb → c₅.nreg x = c.nreg x := by
    zuh
    rw [R5 x by_omega by_omega, hfn₄ x by_omega, g x hx]
  have hCI : ChordInvD P Q T C W DB HB SB M c₅ c₅ := by
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩ := hDs₄
    refine ⟨hw₅, ?_, ?_, ztbie, by_omega, rfl,
      by omega, rfl, rfl⟩
    · zuktw
    · zuktw
    · have e : ztpnx := by rw [hc₅]; config_simp
      rw [e, List.take_zero]
      simp only [chordPairs, List.map_nil, List.append_nil]
      grind
    · have e : ztpnx := by rw [hc₅]; config_simp
      rw [e, List.take_zero]
      simp only [chordPairs, List.map_nil, List.append_nil]
      rw [R5 206 by_decide by_decide]; exact d2
    · rw [R5 200 by_decide by_decide]; exact d3
    · rw [R5 201 by_decide by_decide]; exact d4
    · rw [R5 202 by_decide by_decide]; exact d5
    · rw [R5 203 by_decide by_decide]; exact d6
    · rw [R5 204 by_decide by_decide]; exact d7
    · rw [R5 205 by_decide by_decide]; exact d8
    · rw [R5 224 by_decide by_decide]; exact d9
    · rw [R5 225 by_decide by_decide]; omega
    · rw [R5 226 by_decide by_decide]; omega
  have hmem₅ : ∀ t, ztbwi → c₅.nmem t = c.nmem t := by
    zucj
    have e : ztpnw := by zunbe
    rw [e, hnm₄ t ht, hmem₃, hmem₂ t ht]
  have hCab₅ : Core.ChordTableAt c₅.nmem (c₅.nreg 9992) C := by
    zuopx
    zug
    rw [hmem₅ _ by_omega, hmem₅ _ by_omega, hmem₅ _ by_omega]
    exact hCab i hi
  obtain ⟨c₆, k₆, ex₆, ⟨hw₆, hj₆, hptr₆, hDs₆, hfn₆, hfr₆, hnm₆, hrm₆, hout₆⟩, hexit₆, hk₆⟩ :=
    Exec.whileLtN_bounded (P := P) (ChordInvD P Q T C W DB HB SB M c₅)
      (fun d => C.length - d.nreg 207) 172 ztsa
      (fun d hd ht => chordBody_inv hQ hQn hT hC hCab₅ (by rw [g5 9993 by_omega, h9993])
        (by zuopx; omega) hl1 hl2 hW hM d hd ht) hCI
  unfold chordLoop
  refine ⟨c₆, k₆, ex₆, ?_⟩
  have e207₆ : c₆.nreg 207 = C.length := by
    rw [hfn₆ 9993 by_omega, g5 9993 by_omega, h9993] at hexit₆
    omega
  rw [e207₆, List.take_length] at hDs₆
  obtain ⟨d1, d2, -⟩ := hDs₆
  have c5_207 : ztpnx := by zunbe; config_simp
  have c3_207 : ztpnn := by zumwr; config_simp
  rw [c5_207] at hk₆
  rw [c3_207] at hk₄
  rw [c207] at hk₂
  refine ⟨by_omega, _, foldl_ins_perm T C, d2, d1.band,
    fun x hx => ?_, ?_, fun t ht => ?_, ?_, ?_⟩
  · rw [hfn₆ x by_omega, g5 x by_omega]
  · grind
  · have e := hnm₆ t ht
    rw [e, hmem₅ t ht]
  · grind
  grind
end Whole
end
end Chazelle.Final
namespace Chazelle.Final
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Core (shear shearPt shear_vtx shear_n det_shearPt YlexAgree ShearRel)
open Chazelle.EarClip (subPoly n_subPoly)
open Chazelle.Existence (WeakTriangulates)
open Chazelle.Mountain (IsMountain ylexLT ylexLE orient orient_eq sign_eq_or_eq_neg)

/-! ### The splitting is shear-invariant -/
variable (ε : ℝ) (P : Polygon)
/-- The node wedge test reads only orientation signs, which the shear preserves. -/
theorem nodeWedge_shear : nodeWedge ztsl = nodeWedge P := by
  funext σ S z w
  simp only [nodeWedge, wedgeTest, shear_vtx, det_shearPt]

/-- The copy search is the same on `P` and on `shear ε P`. -/
theorem findCopy_shear : findCopy ztsl = findCopy P := by
  funext σ S v w
  unfold findCopy
  rw [nodeWedge_shear]

/-- One splitting step is the same on `P` and on `shear ε P`. -/
theorem step_shear : step ztsl = step P := by
  funext σ S d
  simp only [step, findCopy_shear]

/-- **The linked-structure run is the same on `P` and on `shear ε P`.** -/
theorem runState_shear (σ : ℝ) (S : LState) (D : List ztw) :
    runState ztsl σ S D = runState P σ S D := by
  induction D generalizing S with
  | nil => rfl
  | cons d D ih => rw [runState_cons, runState_cons, ih, step_shear]

/-! ### Sub-polygons, rotations, mountains -/
theorem subPoly_shear (l : List ℕ) :
    subPoly ztsl l = shear ε ztdi := by
  simp only [subPoly, shear, List.map_map]
  zucr
  zucfh
  intro x _
  simp only [Function.comp, ← shear_vtx]
  rfl

/-- Rotation commutes with the shear. -/
theorem rotate_shear (R : Polygon) (s : ℕ) :
    (shear ε R).rotate s = shear ε (R.rotate s) := by
  have hn := shear_n ε R
  unfold Polygon.rotate
  zubdb
  simp only [shear_vtx]
  zujow
  rfl

/-- **Mountains transfer back from the shear.**  If every vertex of `R` is a vertex of `P`
(index `< P.n`), `YlexAgree P (shear ε P)` holds and `shear ε R` is a monotone mountain, then so
is `R`. -/
theorem isMountain_of_shear {ε : ℝ} {P R : Polygon} (hag : YlexAgree P ztsl)
    (hR : ∀ i < R.n, ∃ j < P.n, R.vtx i = P.vtx j) (hM : IsMountain ztuaf) :
    IsMountain R := by
  obtain ⟨hs, hinc⟩ := hM
  refine ztolw
  · have := Chazelle.Core.shear_simple (ε := -ε) hs
    rwa [Chazelle.Core.shear_shear] at this
  · rw [shear_n] at hinc
    have h := hinc i hi
    rw [shear_vtx, shear_vtx] at h
    obtain ⟨j, hj, e⟩ := hR i by_omega
    obtain ⟨j', hj', e'⟩ := hR _ hi
    rw [e, e'] at h ⊢
    rw [← shear_vtx, ← shear_vtx] at h
    exact (hag j j' hj hj').2 h

/-- The vertices of a rotated sub-polygon are vertices of `P`. -/
theorem vtx_rotate_subPoly {P : Polygon} {l : List ℕ} (hl : ∀ x ∈ l, x < P.n) (s : ℕ) :
    ∀ i < ((subPoly P l).rotate s).n, ∃ j < P.n, ((subPoly P l).rotate s).vtx i = P.vtx j := by
  zug
  rw [Chazelle.Existence.n_rotate, n_subPoly] at hi
  rw [Chazelle.Existence.vtx_rotate _ _ by_simp_all, n_subPoly,
    Chazelle.EarClip.vtx_subPoly_getD P l ztcv]
  exact ⟨_, hl _ (getD_mem_of_lt ztcv), rfl⟩

/-- **The mountain hypothesis of the piece triangulator transfers from `Q` to `P`.** -/
theorem mountain_transfer {ε : ℝ} {P : Polygon} (hag : YlexAgree P ztsl) {l : List ℕ}
    (hl : ∀ x ∈ l, x < P.n)
    (h : ∃ s, IsMountain ((subPoly ztsl l).rotate s) ∨
      IsMountain ((subPoly ztsl l.reverse).rotate s)) :
    ∃ s, IsMountain ztden ∨ IsMountain ztdeo := by
  obtain ⟨s, h | h⟩ := h
  · zuimp
    exact ⟨s, Or.inl (isMountain_of_shear hag (vtx_rotate_subPoly hl s) h)⟩
  · zuimp
    exact ⟨s, Or.inr (isMountain_of_shear hag
      (vtx_rotate_subPoly by_simp_all s) h)⟩

/-! ### Weak triangulations -/

/-- **Weak triangulations are transported by the shear.** -/
theorem weakTriangulates_shear {R : Polygon} {T : List Polygon.Triangle}
    (h : WeakTriangulates R T) : WeakTriangulates ztuaf T := by
  zubrk
  refine ⟨fun t ht => (Chazelle.Core.shear_validTriangle_iff R ε t).2 by_simp_all,
    by rw [shear_n]; exact h2, ?_, ?_, ?_⟩
  · rw [Chazelle.Core.shear_union_triSet, Chazelle.Core.shear_filled, h3]
  · refine h4.imp fun {s t} hd => ?_
    rw [Chazelle.Core.shear_triSet, Chazelle.Core.shear_triSet,
      Chazelle.Core.interior_image_shearPt, Chazelle.Core.interior_image_shearPt]
    exact (Set.disjoint_image_iff (Chazelle.Core.shearPt_injective ε)).2 hd
  · intro t ht i hi hv
    rw [shear_n] at hi
    rw [Chazelle.Core.shear_triSet, shear_vtx,
      (Chazelle.Core.shearPt_injective ε).mem_set_image] at hv
    rw [Chazelle.Core.shear_triVertices, shear_vtx]
    grind

/-! ### The orientation from the lowest vertex -/
section Lowest
open Chazelle.Jordan
open Chazelle.Existence (sector_subset_interior det_ne_zero_of_lexMin)
open Chazelle.Visibility (transpose transpose_n transpose_vtx transpose_simple
  mem_transpose_filled_iff)
open Chazelle.Programs (lexLE)
open Chazelle.Geometry (lerp det_cyclic)
open Chazelle.Mountain (det_swap_swap_swap swap_mem_ball_swap_iff orient_eq_of_eventually)
variable {P : Polygon}
/-- The transposed lowest vertex is lexicographically smallest. -/
theorem lexMin_transpose (hmin : ∀ i < P.n, ylexLE ztdt ztdn) :
    ∀ i, i < (transpose P).n → lexLE ((transpose P).vtx 0) ((transpose P).vtx i) := by
  zug
  zufoj

  rcases hmin i hi with h | ⟨h1, h2⟩
  · tauto
  tauto

/-- The open sector at a `(y, x)`-smallest vertex `v₀` is interior (generalises
`Chazelle.Mountain.sector_lowest_subset_interior`). -/
theorem sector_ylexMin_subset_interior {P : Polygon} (hP : P.Simple)
    (hmin : ∀ i < P.n, ylexLE ztdt ztdn) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hpos : 0 < σ * det ztwjc ztdt ztgk) :
    ∃ r > 0, ∀ y ∈ ball ztdt r,
      0 < σ * det ztwjc ztdt y → 0 < σ * det ztdt ztgk y →
        y ∈ P.filled \ P.boundary := by
  zuemy

  have hTn := transpose_n P
  zudpr
  have hposT : ztezf := by
    zuedb

  obtain ⟨r, hr, hsec⟩ := sector_subset_interior hT ztvyf hσ' hposT
  refine ztkmo
  have := hsec y.swap ztirq
    zthet
    ztiih
  rw [Set.mem_sdiff, mem_transpose_filled_iff, Chazelle.Visibility.mem_transpose_boundary_iff,
    Prod.swap_swap] at this
  grind

/-- **The orientation is the sign of the corner at a `(y, x)`-smallest vertex `0`**
(generalises `Chazelle.Mountain.mountain_orient_det`). -/
theorem orient_det_pos_of_ylexMin0 (hP : P.Simple)
    (hmin : ∀ i < P.n, ylexLE ztdt ztdn) :
    0 < orient P * det ztwjc ztdt ztgk := by
  zuoo
  have hdet : ztbamp := by
    have := det_ne_zero_of_lexMin ztwgv ztvyf
    zueea

  obtain ⟨σ, hσ, hpos⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      0 < σ * det ztwjc ztdt ztgk := by
    grind
  obtain ⟨r, hr, hsec⟩ := sector_ylexMin_subset_interior hP hmin hσ hpos
  zujr

  zuboa

  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), lerp u v zteb ∈ ball v r ∩ {x | 0 < σ * det v w x} ∧
      s ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [(tendsto_lerp_one_sub u v).eventually ztsd,
      Ioo_mem_nhdsGT ztcjf] with s hs hs01
    refine ztbabo
    show 0 < σ * det v w _
    zuekx

  zucdz

  have hor : ztuuq := by
    apply orient_eq_of_eventually hP (i := P.n - 1) by_omega (t := 1 - s)
      by_grind hσ
    zuyg

    show 0 < σ * det u v _
    zucto

  grind

/-- **The orientation from any `(y, x)`-smallest vertex `k`**:
`0 < orient P * det v_{k-1} v_k v_{k+1}` (indices modulo `n`). -/
theorem orient_det_pos_of_ylexMin (hP : P.Simple) {k : ℕ} (hk : k < P.n)
    (hmin : ∀ i < P.n, ylexLE ztjr ztdn) :
    0 < orient P * det ztbtp ztjr ztwiw := by
  zuoo
  set R := P.rotate k with hR
  have hRs := Chazelle.Existence.simple_rotate P k hP
  have hRn : R.n = P.n := by_simp_all
  have hv0 : R.vtx 0 = P.vtx k := by
    rw [hR, Chazelle.Existence.vtx_rotate P k by_omega, Nat.add_zero, Nat.mod_eq_of_lt hk]
  have hv1 : R.vtx 1 = P.vtx ztwtz := by
    rw [hR, Chazelle.Existence.vtx_rotate P k by_omega]
  have hvl : R.vtx (R.n - 1) = P.vtx (ztjze % P.n) := by
    rw [hRn, hR, Chazelle.Existence.vtx_rotate P k by_omega]
    grind
  have hminR : ∀ i < R.n, ylexLE (R.vtx 0) (R.vtx i) := by
    zug
    rw [hRn] at hi
    rw [hv0, hR, Chazelle.Existence.vtx_rotate P k hi]
    zulyx
  have h := orient_det_pos_of_ylexMin0 hRs hminR
  have hor : orient P = orient R := by
    refine Chazelle.Mountain.orient_eq_of_filled_subset hRs hP by_omega hk
      hv0 ?_ (by rw [hR, Chazelle.Existence.filled_rotate])
    rw [hRn, Nat.zero_add, Nat.mod_eq_of_lt by_grind, hv1]
  simp_all

/-- **The orientation as a computable sign.**  If `k` is a `(y, x)`-smallest vertex and `σ`
is `1` when the corner determinant at `k` is positive and `-1` otherwise, then
`σ = orient P`. -/
theorem orient_eq_of_ylexMin (hP : P.Simple) {k : ℕ} (hk : k < P.n)
    (hmin : ∀ i < P.n, ylexLE ztjr ztdn) {σ : ℝ}
    (hσ : σ = if 0 < det ztbtp ztjr ztwiw
      then 1 else -1) : orient P = σ := by
  have h := orient_det_pos_of_ylexMin hP hk hmin
  split_ifs at hσ with hd
  · zujet
    · simp_all
    · rw [ho] at h; nlinarith
  · zujet
    · simp_all
    simp_all
end Lowest
end
end Chazelle.Final
section
set_option hygiene false
local macro "zqyq" : tactic => `(tactic| by_cases hl : ylexLT (ptAt P l ztdmt) ztkwv)
local macro "zqyr" : tactic => `(tactic| rw [Machine.upd_other _ _ _ by_omega])
local macro "zqys" : tactic => `(tactic| (config_simp; omega))
local macro "zqyt" : tactic => `(tactic| (have hF' := hF
                                          obtain ⟨hFn, hFr, hFm, hFrm, hFo⟩ := hF))
local macro "zqyu" : tactic => `(tactic| (have h1 : r ≠ 85 := by_omega
                                          have h2 : ztslo := by_omega))
set_option hygiene true

/-!
# Triangulating one piece on the RAM

`pieceTriStmt` triangulates one piece of the subdivision, handed over as a **cyclic linked
list**, in time linear in its size `m`, by reorienting it into a monotone mountain listed in
increasing `ylexLT` order (`Chazelle.Final.PieceTri`) and running the verified relocatable
stack walk `Chazelle.Mountain.mountainSubStmt`.

## Input representation (fixed here; produced by the piece-splitting stage)

Natural registers (never written):
* `nreg 80 = NB`: base of the successor array, `nxt[x] = nmem (NB + x)`;
* `nreg 81 = VB`: base of the vertex array, `vtx[x] = nmem (VB + x)` (a vertex index of `P`);
* `nreg 82 = s`: a node of the piece;
* `nreg 83 = m`: the number of vertices of the piece;
* `nreg 84 = WB`: base of a work band of `4 m` cells `WB … WB + 4m - 1`.

The piece is the list `l` (`l.length = m`) with `l[i] = vtx[nxt^i s]` and `nxt^m s = s`
(`PieceInput`); the node cells `NB + nxt^i s`, `VB + nxt^i s` (`i < m`) lie outside the work
band, and every address used is `≤ W`.

## The program (`pieceTriStmt`)

```
walk:  node := s; p := WB
       while p < WB + 2m: nmem p := vtx[node]; node := nxt[node]; p := p + 1
       -- D[i] = nmem (WB + i) = l[i % m], i < 2m (the list, written twice)
min:   mp := WB; q := WB + 1
       while q < WB + m: if ylexLT (vtx D[q]) (vtx D[mp]) then mp := q;  q := q + 1
       -- i0 = mp - WB is a ylexLT-minimal position (IsMinPos)
dir:   if ylexLT (vtx D[i0 + 1]) (vtx D[i0 + m - 1])        -- DirFwd
       then a := mp, inc := 1, dec := 0 else a := mp + m, inc := 0, dec := 1
copy:  b := WB + 2m
       while b < WB + 3m: nmem b := nmem a; a := a + inc - dec; b := b + 1
       -- nmem (WB + 2m + j) = (reorient P l i0)[j], j < m
frag:  nreg 60 := WB + 2m; nreg 61 := WB + 3m; nreg 62 := m; mountainSubStmt
```

Registers written: natural `60 … 74` (the fragment uses `63 … 74`) and `85 … 94`; real
`61 … 72` (fragment) and `80 … 83`.  Memory written: only the work band.

## Costs

walk `≤ 16 m + 7`, min `≤ 16 m + 5`, dir `≤ 18`, copy `≤ 7 m + 5`, setup `4`, fragment
`≤ 73 m`: total `≤ 112 m + 39` (`pieceTri_exec`).

## Main results

* `pieceTri_exec`: on a piece that is a rotated (possibly reversed) monotone mountain, the
  program appends `T.map (relabelList l)` to the output for a weak triangulation `T` of
  `subPoly P l`, at cost `≤ 112 m + 39`, with the frame above.
* `pieceTri_exec_of_isPiece`: the same for an `IsPiece P l` of a simple polygon.
-/
namespace Chazelle.Final
open Machine Machine.Stmt Programs
open Chazelle.Mountain
open Chazelle.EarClip (subPoly relabelList n_subPoly)
open Chazelle.Existence (WeakTriangulates)
@[expose] public section
def nodeSeq (mem : ℕ → ℕ) (NB s i : ℕ) : ℕ := (fun x => mem zttal)^[i] s
variable (mem : ℕ → ℕ)
theorem nodeSeq_zero (NB s : ℕ) : nodeSeq mem NB s 0 = s := rfl
theorem nodeSeq_succ (NB s i : ℕ) :
    nodeSeq mem NB s ztg = mem (NB + nodeSeq mem NB s i) :=
  Function.iterate_succ_apply' _ _ _

/-- A cyclic list of period `m` can be read modulo `m`. -/
theorem nodeSeq_mod {mem : ℕ → ℕ} {NB s m : ℕ} (h : nodeSeq mem NB s m = s) (i : ℕ) :
    nodeSeq mem NB s i = nodeSeq mem NB s (i % m) := by
  unfold nodeSeq at *
  conv_lhs => rw [← Nat.mod_add_div i m]
  rw [Function.iterate_add_apply, Function.iterate_mul, Function.iterate_fixed h]

/-- **The input of the piece triangulator** in the configuration `c`: the piece `l` is the
cyclic linked list at `nreg 80` (successors), `nreg 81` (vertex indices) from the node
`nreg 82`, of length `nreg 83 = l.length`; its node cells lie outside the work band
`[nreg 84, nreg 84 + 4 m)`, and all addresses used are `≤ W`. -/
structure PieceInput (W : ℕ) (l : List ℕ) (c : Config) : Prop where
  len : c.nreg 83 = l.length
  cyc : nodeSeq c.nmem ztfgs ztfgu l.length = c.nreg 82
  vtx : ∀ i, i < l.length →
    c.nmem (c.nreg 81 + nodeSeq c.nmem ztfgs ztfgu i) = l.getD i 0
  nxtW : ∀ i, i < l.length → c.nreg 80 + nodeSeq c.nmem ztfgs ztfgu i ≤ W
  vtxW : ∀ i, i < l.length → c.nreg 81 + nodeSeq c.nmem ztfgs ztfgu i ≤ W
  nxtOut : ∀ i, i < l.length →
    c.nreg 80 + nodeSeq c.nmem ztfgs ztfgu i < c.nreg 84 ∨
      c.nreg 84 + 4 * l.length ≤ c.nreg 80 + nodeSeq c.nmem ztfgs ztfgu i
  vtxOut : ∀ i, i < l.length →
    c.nreg 81 + nodeSeq c.nmem ztfgs ztfgu i < c.nreg 84 ∨
      c.nreg 84 + 4 * l.length ≤ c.nreg 81 + nodeSeq c.nmem ztfgs ztfgu i
  work : c.nreg 84 + 4 * l.length ≤ W

/-! ### The frame of the reorientation phases -/

/-- The frame of the phases before the fragment: natural registers outside `85 … 94`, real
registers outside `80 … 83`, natural memory outside the work band (of `c₀`), the real memory
and the output are unchanged. -/
def PFrame (c₀ c : Config) : Prop :=
  (∀ r, (r < 85 ∨ 94 < r) → c.nreg r = c₀.nreg r) ∧
  (∀ r, ztofz → c.rreg r = c₀.rreg r) ∧
  (∀ a, (a < c₀.nreg 84 ∨ c₀.nreg 84 + 4 * c₀.nreg 83 ≤ a) → c.nmem a = c₀.nmem a) ∧
  c.rmem = c₀.rmem ∧ c.output = c₀.output
theorem pFrame_trans {c₀ c₁ c₂ : Config} (h₁ : PFrame c₀ c₁) (h₂ : PFrame c₁ c₂) :
    PFrame c₀ c₂ := by
  obtain ⟨n₁, r₁, m₁, q₁, o₁⟩ := h₁
  obtain ⟨n₂, r₂, m₂, q₂, o₂⟩ := h₂
  have e83 : c₁.nreg 83 = c₀.nreg 83 := by_simp_all
  have e84 : c₁.nreg 84 = c₀.nreg 84 := by_simp_all
  refine ⟨by_simp_all, by_simp_all,
    fun a ha => ?_, by_simp_all, by_simp_all⟩
  simp_all

/-! ### The lexicographic test -/

/-- `if ylexLT (rreg a1, rreg a2) (rreg b1, rreg b2) then t else e`: compare heights, then
abscissae. -/
def ylexTest (a1 a2 b1 b2 : ℕ) (t e : Stmt) : Stmt :=
  .ifLtR a2 b2 t (.ifLtR b2 a2 e (.ifLtR a1 b1 t e))
section ylex
variable {P : Polygon} {W : ℕ}

/-- **Spec lemma for `ylexTest`**: if both branches satisfy `post` within cost `K`, the test
does within `K + 6`. -/
theorem ylexTest_exec {a1 a2 b1 b2 : ℕ} {t e : Stmt} {K : ℕ} {post : Config → Prop}
    (c : Config)
    (ht : ylexLT ztjso ztjsp →
      ∃ c' k, Exec P W t c c' k ∧ k ≤ K ∧ post c')
    (he : ¬ ylexLT ztjso ztjsp →
      ∃ c' k, Exec P W e c c' k ∧ k ≤ K ∧ post c') :
    ∃ c' k, Exec P W (ylexTest a1 a2 b1 b2 t e) c c' k ∧ k ≤ K + 6 ∧ post c' := by
  unfold ylexTest
  by_cases h1 : c.rreg a2 < c.rreg b2
  · obtain ⟨c', k, ex, hk, hp⟩ := ht ztfft
    exact ⟨c', k + 1, .ifLtR_true h1 ex, by_omega, hp⟩
  · by_cases h2 : c.rreg b2 < c.rreg a2
    · obtain ⟨c', k, ex, hk, hp⟩ := he (fun h => by
        rcases h with h | ⟨h, -⟩ <;> dsimp only at h <;> linarith)
      exact ⟨c', k + 1 + 2, .ifLtR_false h1 (.ifLtR_true h2 ex), by_omega, hp⟩
    · have heq : c.rreg a2 = c.rreg b2 := by_grind
      by_cases h3 : c.rreg a1 < c.rreg b1
      · obtain ⟨c', k, ex, hk, hp⟩ := ht ztcgy
        exact ⟨c', k + 1 + 2 + 2, .ifLtR_false h1 (.ifLtR_false h2 (.ifLtR_true h3 ex)),
          by omega, hp⟩
      · obtain ⟨c', k, ex, hk, hp⟩ := he (fun h => by
          rcases h with h | ⟨-, h⟩ <;> dsimp only at h
          · simp_all
          simp_all)
        exact ⟨c', k + 2 + 2 + 2, .ifLtR_false h1 (.ifLtR_false h2 (.ifLtR_false h3 ex)),
          by omega, hp⟩
end ylex

/-! ### The program -/

/-- Initialisation: `nreg 88 := 1`, `node := s`, `p := WB`, `nreg 87 := WB + 2m`. -/
def ptInit : Stmt := block [.constN 88 1, .copyN 85 82, .copyN 86 84, .addN 87 84 83,
  .addN 87 87 83]

/-- One step of the walk: `nmem p := vtx[node]; node := nxt[node]; p := p + 1`. -/
def walkBody : Stmt := block [.addN 89 81 85, .loadN 89 89, .storeN 86 89, .addN 89 80 85,
  .loadN 85 89, .addN 86 86 88]

/-- The walk: `while p < WB + 2m do walkBody`. -/
def walkLoop : Stmt := .whileLtN 86 87 walkBody

/-- Initialisation of the minimum scan: `mp := WB; q := WB + 1; nreg 87 := WB + m`. -/
def minInit : Stmt := block [.copyN 90 84, .addN 86 84 88, .addN 87 84 83]

/-- Reading the two vertices `vtx D[q]` (into `rreg 80, 81`) and `vtx D[mp]`
(into `rreg 82, 83`). -/
def minRead : Stmt := block [.loadN 89 86, .loadN 91 90, .readX 80 89, .readY 81 89,
  .readX 82 91, .readY 83 91]

/-- `if ylexLT (vtx D[q]) (vtx D[mp]) then mp := q`. -/
def minUpdate : Stmt := ylexTest 80 81 82 83 (.instr (.copyN 90 86)) .skip

/-- One step of the minimum scan. -/
def minBody : Stmt := .seq minRead (.seq minUpdate (.instr (.addN 86 86 88)))

/-- The minimum scan: `while q < WB + m do minBody`. -/
def minLoop : Stmt := .whileLtN 86 87 minBody

/-- Reading the successor `vtx D[i0 + 1]` (into `rreg 80, 81`) and the predecessor
`vtx D[i0 + m - 1]` (into `rreg 82, 83`) of the minimum. -/
def dirRead : Stmt := block [.addN 89 90 88, .loadN 89 89, .addN 91 90 83, .subN 91 91 88,
  .loadN 91 91, .readX 80 89, .readY 81 89, .readX 82 91, .readY 83 91]

/-- Forward copy set-up: `a := mp; inc := 1; dec := 0`. -/
def fwdSetup : Stmt := block [.copyN 86 90, .constN 92 1, .constN 93 0]

/-- Backward copy set-up: `a := mp + m; inc := 0; dec := 1`. -/
def bwdSetup : Stmt := block [.addN 86 90 83, .constN 92 0, .constN 93 1]

/-- The direction choice. -/
def dirSel : Stmt := ylexTest 80 81 82 83 fwdSetup bwdSetup

/-- Initialisation of the copy: `b := WB + 2m; nreg 87 := WB + 3m`. -/
def copyInit : Stmt := block [.addN 94 84 83, .addN 94 94 83, .addN 87 94 83]

/-- One step of the copy: `nmem b := nmem a; a := a + inc - dec; b := b + 1`. -/
def copyBody : Stmt := block [.loadN 89 86, .storeN 94 89, .addN 86 86 92, .subN 86 86 93,
  .addN 94 94 88]

/-- The copy: `while b < WB + 3m do copyBody`. -/
def copyLoop : Stmt := .whileLtN 94 87 copyBody

/-- The inputs of the fragment: `base := WB + 2m`, `sbase := WB + 3m`, `m`. -/
def fragInit : Stmt := block [.addN 60 84 83, .addN 60 60 83, .addN 61 60 83, .copyN 62 83]

/-- **The piece triangulator.** -/
def pieceTriStmt : Stmt :=
  .seq ztsqi (.seq ztsqg (.seq ztspv
    (.seq ztspu ztsqf)))

/-! ### Phase 1: the walk -/

/-- The invariant of the walk, relative to the configuration `c₀` at the start of the phase:
`p = nreg 86`, `node = nreg 85 = nxt^(p - WB) s` (in the memory of `c₀`), and the cells
`WB + k`, `k < p - WB`, hold `l[k % m]`. -/
def WalkInv (W : ℕ) (l : List ℕ) (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ PFrame c₀ c ∧ c.nreg 88 = 1 ∧
    c.nreg 87 = c₀.nreg 84 + 2 * l.length ∧ c₀.nreg 84 ≤ c.nreg 86 ∧
    c.nreg 86 ≤ c₀.nreg 84 + 2 * l.length ∧
    c.nreg 85 = nodeSeq c₀.nmem ztvme ztvmf ztdmt ∧
    ∀ k, k < c.nreg 86 - c₀.nreg 84 → c.nmem (c₀.nreg 84 + k) = l.getD (k % l.length) 0
section walk
variable {P : Polygon} {W : ℕ} {l : List ℕ}
set_option maxHeartbeats 800000 in
/-- **One step of the walk** preserves `WalkInv`, costs `6` and advances `p`. -/
theorem walkBody_inv {c₀ : Config} (hin : PieceInput W l c₀) (c : Config)
    (hI : WalkInv W l c₀ c) (ht : c.nreg 86 < c.nreg 87) :
    ∃ c' k, Exec P W walkBody c c' k ∧ WalkInv W l c₀ c' ∧ k ≤ 6 ∧
      c₀.nreg 84 + 2 * l.length - c'.nreg 86 < c₀.nreg 84 + 2 * l.length - c.nreg 86 := by
  obtain ⟨hw, hF, h88, h87, hlo, hhi, h85, htab⟩ := hI
  zqyt
  have e80 : c.nreg 80 = c₀.nreg 80 := by_simp_all
  have e81 : c.nreg 81 = c₀.nreg 81 := by_simp_all
  have e83 := hin.len
  zugcz
  have hm0 : ztmso := by_omega
  have him : ztdmt % l.length < l.length := Nat.mod_lt _ hm0
  have hnode : c.nreg 85 =
      nodeSeq c₀.nmem ztvme ztvmf ztzzi := by
    rw [h85, nodeSeq_mod hin.cyc]
  have hvW := hin.vtxW _ him
  have hnW := hin.nxtW _ him
  have hvO := hin.vtxOut _ him
  have hnO := hin.nxtOut _ him
  have hW := hin.work
  rw [← hnode] at hvW hnW hvO hnO
  have hvmem : c.nmem (c.nreg 81 + c.nreg 85) = l.getD ztzzi 0 := by
    rw [e81, hFm _ by_omega, hnode]
    exact hin.vtx _ him
  have hne : c.nreg 80 + c.nreg 85 ≠ c.nreg 86 := by_omega
  have hnmem : c.nmem (c.nreg 80 + c.nreg 85) = c₀.nmem (c₀.nreg 80 + c.nreg 85) := by
    grind
  unfold walkBody
  exec_block
  · omega
  · zqys
  · zqys
  · refine ⟨⟨by_omega, pFrame_trans hF' ztgoy,
      by tauto, by_tauto, by config_simp; omega,
      by config_simp; omega, ?_, ?_⟩, by_omega, by config_simp; omega⟩
    · zqyu
      have h3 : r ≠ 89 := by_omega
      zubmk
    · config_simp
      rw [Machine.upd_other _ _ _ (by rw [hFn 84 by_omega, hFn 83 by_omega] at ha; omega)]
    · config_simp
      rw [Machine.upd_other _ _ _ hne, hnmem, h88,
        show c.nreg 86 + 1 - c₀.nreg 84 = c.nreg 86 - c₀.nreg 84 + 1 by omega, nodeSeq_succ,
        h85]
    · zugf
      config_simp at hk
      rw [h88] at hk
      config_simp
      by_cases hk' : k = c.nreg 86 - c₀.nreg 84
      · rw [show c₀.nreg 84 + k = c.nreg 86 by omega, Machine.upd_same, hvmem, hk']
      · zqyr
        grind

/-- **Spec lemma for the walk phase** `ptInit; walkLoop`: cost `≤ 16 m + 7`; afterwards the
cells `WB + i`, `i < 2m`, hold `l[i % m]`, `nreg 88 = 1`, within the frame `PFrame`. -/
theorem walkPhase_exec (c : Config) (hc : WordsBounded W c) (hin : PieceInput W l c)
    (hm1 : 1 ≤ l.length) :
    ∃ c' k, Exec P W ztsqi c c' k ∧ k ≤ 16 * l.length + 7 ∧ PFrame c c' ∧
      c'.nreg 88 = 1 ∧
      ∀ i, i < 2 * l.length → c'.nmem zthvd = l.getD ztdho 0 := by
  zuhxt

  unfold ptInit
  refine spec_seq ?_
  exec_block
  · omega
  · zqys
  · zqys
  refine spec_imp (Exec.whileLtN_bounded _
    (fun d => c.nreg 84 + 2 * l.length - d.nreg 86) 6 ztsa
    (walkBody_inv (P := P) hin) ?_) ?_
  · refine ⟨by_omega, ztdxh,
      by config_simp, by config_simp; omega, by_simp, by_simp,
      ?_, ?_⟩
    · zqyu
      have h3 : ztslp := by_omega
      have h4 : r ≠ 88 := by_omega
      simp_all
    · config_simp; rw [Nat.sub_self]; rfl
    simp
  · rintro c' k ⟨⟨hw, hF, h88, h87, hlo, hhi, h85, htab⟩, hexit, hk⟩
    config_simp at hk
    grind
end walk

/-! ### Phase 2: the minimum scan -/
section minimum
variable {P : Polygon} {W : ℕ} {l : List ℕ}
variable (c : Config)
/-- **Spec lemma for the update of the minimum**: cost `≤ 7`; `mp := q` exactly when
`(rreg 80, rreg 81) <_ylex (rreg 82, rreg 83)`; nothing else changes. -/
theorem minUpdate_exec (hc : WordsBounded W c) :
    ∃ c' k, Exec P W minUpdate c c' k ∧ k ≤ 7 ∧
      (ylexLT ztgho ztghp → c'.nreg 90 = c.nreg 86) ∧
      (¬ ylexLT ztgho ztghp → c'.nreg 90 = c.nreg 90) ∧
      (∀ r, r ≠ 90 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold minUpdate
  zulor
  · refine ⟨_, 1, Exec.copyN hc 90 86, le_rfl, by_simp_all,
      by simp_all, by_simp_all, rfl, rfl, rfl, rfl⟩
  · exact ⟨c, 0, .skip hc, by_omega, by_simp_all, by_omega, by_omega, rfl,
      rfl, rfl, rfl⟩

/-- **Spec lemma for one step of the minimum scan**: cost `≤ 14`; `mp := q` exactly when
`vtx (nmem q) <_ylex vtx (nmem mp)`; `q := q + nreg 88`; natural registers other than
`86, 89, 90, 91`, real registers outside `80 … 83`, memories and output unchanged. -/
theorem minBody_exec (hc : WordsBounded W c) (hW : c.nreg 86 + c.nreg 88 ≤ W) :
    ∃ c' k, Exec P W minBody c c' k ∧ k ≤ 14 ∧
      (ylexLT ztmbz ztmca →
        c'.nreg 90 = c.nreg 86) ∧
      (¬ ylexLT ztmbz ztmca →
        c'.nreg 90 = c.nreg 90) ∧
      c'.nreg 86 = c.nreg 86 + c.nreg 88 ∧
      (∀ r, r ≠ 86 → r ≠ 89 → r ≠ 90 → r ≠ 91 → c'.nreg r = c.nreg r) ∧
      (∀ r, ztofz → c'.rreg r = c.rreg r) ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold minBody minRead
  refine spec_seq ?_
  exec_block
  refine spec_seq (spec_use (minUpdate_exec _ ‹_›) ?_)
  intro c₁ k₁ hk₁ hw₁ ⟨hlt, hnlt, hfr, hrr, hnm, hrm, hout⟩
  config_simp at hlt
  config_simp at hnlt
  config_simp at hfr
  config_simp at hrr
  config_simp at hnm
  config_simp at hrm
  config_simp at hout
  simp only [Prod.mk.eta] at hlt hnlt
  have hn86 : c₁.nreg 86 = c.nreg 86 := by_simp_all
  have hn88 : c₁.nreg 88 = c.nreg 88 := by_simp_all
  refine spec_instr (Exec.addN hw₁ 86 86 88 by_omega) fun _ => ?_
  refine ⟨by_omega, fun h => ?_, fun h => ?_, ?_, fun r h86 h89 h90 h91 => ?_, fun r hr => ?_,
    hnm, hrm, hout⟩
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · config_simp; zvnhk
    simp [show r ≠ 80 by omega, show r ≠ 81 by omega, show r ≠ 82 by omega,
      show r ≠ 83 by omega]

/-- The invariant of the minimum scan, relative to the configuration `c₀` at the start of the
phase: `q = nreg 86`, `mp = nreg 90 < q`, and position `mp - WB` is `ylexLT`-minimal among the
positions `< q - WB`. -/
def MinInv (P : Polygon) (W : ℕ) (l : List ℕ) (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ PFrame c₀ c ∧ c.nmem = c₀.nmem ∧ c.nreg 88 = 1 ∧
    c.nreg 87 = c₀.nreg 84 + l.length ∧ c₀.nreg 84 < c.nreg 86 ∧
    c.nreg 86 ≤ c₀.nreg 84 + l.length ∧ c₀.nreg 84 ≤ c.nreg 90 ∧ c.nreg 90 < c.nreg 86 ∧
    ∀ j, j < c.nreg 86 - c₀.nreg 84 →
      ¬ ylexLT ztruq ztkwv

/-- Reading the doubled table `D[i] = l[i % m]` at an address of the first copy. -/
theorem tab_read {c₀ c : Config} (htab : ∀ i, i < 2 * l.length →
      c₀.nmem ztfqt = l.getD ztdho 0)
    (hnm : c.nmem = c₀.nmem) {a : ℕ} (hlo : c₀.nreg 84 ≤ a) (hhi : a < c₀.nreg 84 + l.length) :
    P.vtx ztvhc = ptAt P l ztrko := by
  rw [hnm, show a = c₀.nreg 84 + ztrko by omega, htab _ by_omega,
    Nat.mod_eq_of_lt by_omega, Nat.add_sub_cancel_left]
  rfl
set_option maxHeartbeats 400000 in
/-- **One step of the minimum scan** preserves `MinInv`, costs `≤ 14` and advances `q`. -/
theorem minBody_inv {c₀ : Config} (hW : c₀.nreg 84 + 4 * l.length ≤ W)
    (htab : ∀ i, i < 2 * l.length → c₀.nmem ztfqt = l.getD ztdho 0)
    (c : Config) (hI : MinInv P W l c₀ c) (ht : c.nreg 86 < c.nreg 87) :
    ∃ c' k, Exec P W minBody c c' k ∧ MinInv P W l c₀ c' ∧ k ≤ 14 ∧
      c₀.nreg 84 + l.length - c'.nreg 86 < c₀.nreg 84 + l.length - c.nreg 86 := by
  obtain ⟨hw, hF, hnm, h88, h87, hlo, hhi, hmlo, hmhi, hmin⟩ := hI
  zugcz
  obtain ⟨c', k, ex, hk, hlt, hnlt, h86', hfn, hfr, hnm', hrm', hout'⟩ :=
    minBody_exec (P := P) c hw by_omega
  have eq : P.vtx _ = ptAt P l ztdmt :=
    tab_read htab hnm by_omega by_omega
  have em : P.vtx _ = ptAt P l _ :=
    tab_read htab hnm by_omega by_omega
  rw [eq, em] at hlt hnlt
  have hF' : PFrame c c' := ⟨by_grind,
    by omega, by_simp_all, hrm', hout'⟩
  refine ⟨c', k, ex, ⟨ex.wb_right, pFrame_trans hF hF', by_simp_all, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩, hk, ?_⟩
  · simp_all
  · simp_all
  · omega
  · omega
  · zqyq
    · grind
    simp_all
  · zqyq
    · grind
    grind
  · zun
    rw [h86', h88] at hj
    zqyq
    · rw [hlt hl]
      rcases Nat.lt_or_ge j _ with hj' | hj'
      · exact fun h' => hmin j hj' (ylexLT_trans h' hl)
      · rw [show j = c.nreg 86 - c₀.nreg 84 by omega]
        exact ylexLT_irrefl _
    grind
  omega

/-- **Spec lemma for the minimum phase** `minInit; minLoop`: cost `≤ 16 m + 5`; afterwards
`mp = nreg 90 ≥ WB` and `mp - WB` is a minimum position of `l` (`IsMinPos`); the memory is
unchanged, `nreg 88 = 1`, within `PFrame`. -/
theorem minPhase_exec (hc : WordsBounded W c) (hm1 : 1 ≤ l.length)
    (h83 : c.nreg 83 = l.length) (hW : c.nreg 84 + 4 * l.length ≤ W) (h88 : c.nreg 88 = 1)
    (htab : ∀ i, i < 2 * l.length → c.nmem zthvd = l.getD ztdho 0) :
    ∃ c' k, Exec P W ztsqg c c' k ∧ k ≤ 16 * l.length + 5 ∧ PFrame c c' ∧
      c'.nmem = c.nmem ∧ c'.nreg 88 = 1 ∧ c.nreg 84 ≤ c'.nreg 90 ∧
      IsMinPos P l (c'.nreg 90 - c.nreg 84) := by
  unfold minInit
  refine spec_seq ?_
  exec_block
  · zqys
  · zqys
  refine spec_imp (Exec.whileLtN_bounded _
    (fun d => c.nreg 84 + l.length - d.nreg 86) 14 ztsa
    (minBody_inv (P := P) hW htab) ?_) ?_
  · refine ⟨by_omega, ztdxh, rfl,
      by simp_all, by_simp_all, by_simp_all,
      by simp_all, by_simp, by_simp_all, ?_⟩
    · zujyf
      have h2 : ztslp := by_omega
      have h3 : r ≠ 90 := by_omega
      simp_all
    · zun
      config_simp at hj
      config_simp
      zuksa
      rw [show j = 0 by omega, Nat.sub_self]
      exact ylexLT_irrefl _
  · rintro c' k ⟨⟨hw, hF, hnm, h88', h87, hlo, hhi, hmlo, hmhi, hmin⟩, hexit, hk⟩
    config_simp at hk
    rw [h88] at hk
    rw [h87] at hexit
    refine ⟨by_omega, hF, hnm, h88', hmlo, by_omega, by_grind⟩
end minimum

/-! ### Phase 3: the direction -/
section direction
variable {P : Polygon} {W : ℕ} {l : List ℕ}
variable (c : Config)
/-- **Spec lemma for the direction choice**: cost `≤ 9`; forward set-up
(`a := mp, inc := 1, dec := 0`) when `(rreg 80, rreg 81) <_ylex (rreg 82, rreg 83)`, backward
set-up (`a := mp + m, inc := 0, dec := 1`) otherwise; nothing else changes. -/
theorem dirSel_exec (hc : WordsBounded W c) (h1 : 1 ≤ W)
    (hW : c.nreg 90 + c.nreg 83 ≤ W) :
    ∃ c' k, Exec P W dirSel c c' k ∧ k ≤ 9 ∧
      (ylexLT ztgho ztghp →
        c'.nreg 86 = c.nreg 90 ∧ c'.nreg 92 = 1 ∧ c'.nreg 93 = 0) ∧
      (¬ ylexLT ztgho ztghp →
        c'.nreg 86 = c.nreg 90 + c.nreg 83 ∧ c'.nreg 92 = 0 ∧ c'.nreg 93 = 1) ∧
      (∀ r, r ≠ 86 → r ≠ 92 → r ≠ 93 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dirSel
  zulor
  · unfold fwdSetup
    exec_block
    · omega
    · omega
    simp_all
  · unfold bwdSetup
    exec_block
    · zugkh
    · omega
    · omega
    simp_all
set_option maxHeartbeats 400000 in
/-- **Spec lemma for the direction phase** `dirRead; dirSel`: with `mp = nreg 90`,
`i0 = mp - WB < m`: cost `≤ 18`; forward set-up iff `DirFwd P l i0`. -/
theorem dirPhase_exec (hc : WordsBounded W c) (hm1 : 1 ≤ l.length)
    (h83 : c.nreg 83 = l.length) (hW : c.nreg 84 + 4 * l.length ≤ W) (h88 : c.nreg 88 = 1)
    (htab : ∀ i, i < 2 * l.length → c.nmem zthvd = l.getD ztdho 0)
    (hlo : c.nreg 84 ≤ c.nreg 90) (hi0 : c.nreg 90 - c.nreg 84 < l.length) :
    ∃ c' k, Exec P W ztspv c c' k ∧ k ≤ 18 ∧ PFrame c c' ∧ c'.nmem = c.nmem ∧
      c'.nreg 88 = 1 ∧ c'.nreg 90 = c.nreg 90 ∧
      (DirFwd P l ztera →
        c'.nreg 86 = c.nreg 90 ∧ c'.nreg 92 = 1 ∧ c'.nreg 93 = 0) ∧
      (¬ DirFwd P l ztera →
        c'.nreg 86 = c.nreg 90 + l.length ∧ c'.nreg 92 = 0 ∧ c'.nreg 93 = 1) := by
  have hq : ∀ a, c.nreg 84 ≤ a → a - c.nreg 84 < 2 * l.length →
      P.vtx ztvhc = ptAt P l (ztrkn % l.length) := by
    intro a ha1 ha2
    rw [show a = c.nreg 84 + ztrkn by omega, htab _ ha2, Nat.add_sub_cancel_left]
    rfl
  have enx : P.vtx (c.nmem (c.nreg 90 + c.nreg 88)) =
      ptAt P l ((c.nreg 90 - c.nreg 84 + 1) % l.length) := by
    rw [hq _ by_omega by_omega, h88, show c.nreg 90 + 1 - c.nreg 84 =
      c.nreg 90 - c.nreg 84 + 1 by omega]
  have epr : P.vtx (c.nmem (c.nreg 90 + c.nreg 83 - c.nreg 88)) =
      ptAt P l ((c.nreg 90 - c.nreg 84 + l.length - 1) % l.length) := by
    rw [hq _ by_omega by_omega, h88, h83, show c.nreg 90 + l.length - 1 - c.nreg 84 =
      c.nreg 90 - c.nreg 84 + l.length - 1 by omega]
  unfold dirRead
  refine spec_seq ?_
  exec_block
  · omega
  · zqys
  refine spec_use (dirSel_exec _ ‹_› by_omega (by config_simp; omega)) ?_
  intro c' k hk hw' ⟨hf, hb, hfn, hrr, hnm, hrm, hout⟩
  config_simp at hf
  config_simp at hb
  config_simp at hfn
  config_simp at hrr
  config_simp at hnm
  config_simp at hrm
  config_simp at hout
  simp only [Prod.mk.eta] at hf hb
  rw [enx, epr] at hf hb
  rw [h83] at hb
  refine ⟨by_omega, ⟨fun r hr => ?_, fun r hr => ?_, by_grind, hrm, hout⟩, hnm,
    ?_, ?_, hf, hb⟩
  · rw [hfn r by_omega by_omega by_omega]
    simp [show r ≠ 89 by omega, show r ≠ 91 by omega]
  · zvnhk
    simp [show r ≠ 80 by omega, show r ≠ 81 by omega, show r ≠ 82 by omega,
      show r ≠ 83 by omega]
  · rw [hfn 88 by_omega by_omega by_omega]; tauto
  · rw [hfn 90 by_omega by_omega by_omega]; config_simp
end direction

/-! ### Phase 4: the copy -/

/-- The invariant of the copy, relative to the configuration `c₀` at the start of the phase
(after the direction set-up), with `WB = nreg 84`, `mp = nreg 90`, `i0 = mp - WB`:
`b = nreg 94 ∈ [WB + 2m, WB + 3m]`, `j = b - (WB + 2m)` entries copied, the source pointer
`a = nreg 86` is `mp + j` (forward) or `mp + m - j` (backward), the doubled table is intact,
and `nmem (WB + 2m + j') = (reorient P l i0)[j']` for `j' < j`. -/
def CopyInv (P : Polygon) (W : ℕ) (l : List ℕ) (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ PFrame c₀ c ∧ c.nreg 88 = 1 ∧
    c.nreg 87 = c₀.nreg 84 + 3 * l.length ∧ c₀.nreg 84 + 2 * l.length ≤ c.nreg 94 ∧
    c.nreg 94 ≤ c₀.nreg 84 + 3 * l.length ∧
    (DirFwd P l ztdnf →
      c.nreg 86 = c₀.nreg 90 + ztbzt ∧
        c.nreg 92 = 1 ∧ c.nreg 93 = 0) ∧
    (¬ DirFwd P l ztdnf →
      c.nreg 86 + ztbzt = c₀.nreg 90 + l.length ∧
        c.nreg 92 = 0 ∧ c.nreg 93 = 1) ∧
    (∀ i, i < 2 * l.length → c.nmem ztfqt = c₀.nmem ztfqt) ∧
    ∀ j, j < c.nreg 94 - ztpaj →
      c.nmem (c₀.nreg 84 + 2 * l.length + j) = (reorient P l ztdnf).getD j 0
section copy
variable {P : Polygon} {W : ℕ} {l : List ℕ}
set_option maxHeartbeats 800000 in
/-- **One step of the copy** preserves `CopyInv`, costs `5` and advances `b`. -/
theorem copyBody_inv {c₀ : Config} (h83 : c₀.nreg 83 = l.length)
    (hW : c₀.nreg 84 + 4 * l.length ≤ W)
    (htab : ∀ i, i < 2 * l.length → c₀.nmem ztfqt = l.getD ztdho 0)
    (hlo : c₀.nreg 84 ≤ c₀.nreg 90) (hi0 : c₀.nreg 90 - c₀.nreg 84 < l.length)
    (c : Config) (hI : CopyInv P W l c₀ c) (ht : c.nreg 94 < c.nreg 87) :
    ∃ c' k, Exec P W copyBody c c' k ∧ CopyInv P W l c₀ c' ∧ k ≤ 5 ∧
      c₀.nreg 84 + 3 * l.length - c'.nreg 94 < c₀.nreg 84 + 3 * l.length - c.nreg 94 := by
  obtain ⟨hw, hF, h88, h87, hblo, hbhi, hfwd, hbwd, hD, hT⟩ := hI
  zqyt
  have e83 : c.nreg 83 = c₀.nreg 83 := by_grind
  have e84 : c.nreg 84 = c₀.nreg 84 := by_grind
  zugcz
  have hval : c.nmem (c.nreg 86) = (reorient P l ztdnf).getD
      ztbzt 0 := by
    zuiro
    · obtain ⟨e86, -, -⟩ := hfwd hd
      rw [show c.nreg 86 = c₀.nreg 84 + (c₀.nreg 90 - c₀.nreg 84 +
          ztbzt) by omega, hD _ by_omega,
        htab _ by_omega]
      zumue
      rw [ite_eq_left hd, getD_fwdList _ _ by_omega]
    · obtain ⟨e86, -, -⟩ := hbwd hd
      rw [show c.nreg 86 = c₀.nreg 84 + (c₀.nreg 90 - c₀.nreg 84 + l.length -
          ztbzt) by omega, hD _ by_omega,
        htab _ by_omega]
      zumue
      rw [ite_eq_right hd, getD_bwdList _ _ by_omega]
  have hside : c.nreg 86 + c.nreg 92 ≤ W := by
    zuiro
    · grind
    grind
  unfold copyBody
  exec_block
  · tauto
  · zqys
  · refine ⟨⟨by_omega, pFrame_trans hF' ztgoy,
      by tauto, by_tauto, by config_simp; omega,
      by config_simp; omega, fun hd => ?_, fun hd => ?_, fun i hi => ?_, fun j hj => ?_⟩,
      by omega, by config_simp; omega⟩
    · zujyf
      have h2 : r ≠ 89 := by_omega
      have h3 : r ≠ 94 := by_omega
      zubmk
    · config_simp
      zqyr
    · obtain ⟨e86, e92, e93⟩ := hfwd hd
      config_simp
      omega
    · obtain ⟨e86, e92, e93⟩ := hbwd hd
      config_simp
      omega
    · config_simp
      zqyr
      grind
    · config_simp at hj
      zuksa
      config_simp
      by_cases hj' : j = c.nreg 94 - ztpaj
      · rw [show c₀.nreg 84 + 2 * l.length + j = c.nreg 94 by omega, Machine.upd_same, hval,
          hj']
      · zqyr
        grind

/-- **Spec lemma for the copy phase** `copyInit; copyLoop`: after the direction set-up, the
cells `WB + 2m + j` (`j < m`) receive `(reorient P l i0)[j]`; cost `≤ 7 m + 5`; `PFrame`. -/
theorem copyPhase_exec (c : Config) (hc : WordsBounded W c) (h83 : c.nreg 83 = l.length)
    (hW : c.nreg 84 + 4 * l.length ≤ W) (h88 : c.nreg 88 = 1)
    (htab : ∀ i, i < 2 * l.length → c.nmem zthvd = l.getD ztdho 0)
    (hlo : c.nreg 84 ≤ c.nreg 90) (hi0 : c.nreg 90 - c.nreg 84 < l.length)
    (hfwd : DirFwd P l ztera →
      c.nreg 86 = c.nreg 90 ∧ c.nreg 92 = 1 ∧ c.nreg 93 = 0)
    (hbwd : ¬ DirFwd P l ztera →
      c.nreg 86 = c.nreg 90 + l.length ∧ c.nreg 92 = 0 ∧ c.nreg 93 = 1) :
    ∃ c' k, Exec P W ztspu c c' k ∧ k ≤ 7 * l.length + 5 ∧ PFrame c c' ∧
      ∀ j, j < l.length → c'.nmem (c.nreg 84 + 2 * l.length + j) =
        (reorient P l ztera).getD j 0 := by
  unfold copyInit
  refine spec_seq ?_
  exec_block
  · omega
  · zqys
  · zqys
  refine spec_imp (Exec.whileLtN_bounded _
    (fun d => c.nreg 84 + 3 * l.length - d.nreg 94) 5 ztsa
    (copyBody_inv (P := P) h83 hW htab hlo hi0) ?_) ?_
  · refine ⟨by_omega, ztdxh,
      by simp_all, by config_simp; omega, by config_simp; omega,
      by config_simp; omega, fun hd => ?_, fun hd => ?_, by_simp_all, ?_⟩
    · have h1 : ztslp := by_omega
      have h2 : r ≠ 94 := by_omega
      simp_all
    · obtain ⟨e86, e92, e93⟩ := hfwd hd
      config_simp
      omega
    · obtain ⟨e86, e92, e93⟩ := hbwd hd
      config_simp
      omega
    · zun
      config_simp at hj
      omega
  · rintro c' k ⟨⟨hw, hF, h88', h87, hblo, hbhi, -, -, -, hT⟩, hexit, hk⟩
    config_simp at hk
    grind
end copy

/-! ### Phase 5: the stack walk, and the whole program -/
section main
variable {P : Polygon} {W : ℕ}

/-- **Spec lemma for the last phase** `fragInit; mountainSubStmt`: with the reoriented list `l'`
(a mountain) in the cells `WB + 2m + j`, the fragment appends `T.map (relabelList l')` for a
weak triangulation `T` of `subPoly P l'`, at cost `≤ 73 m + 4`, using the stack band
`[WB + 3m, WB + 4m)`. -/
theorem fragPhase_exec {l' : List ℕ} (c : Config) (hc : WordsBounded W c)
    (h83 : c.nreg 83 = l'.length) (hW : c.nreg 84 + 4 * l'.length ≤ W)
    (hM : IsMountain ztubg)
    (htab : ∀ j, j < l'.length → c.nmem (c.nreg 84 + 2 * l'.length + j) = l'.getD j 0) :
    ∃ c' k, Exec P W ztsqf c c' k ∧ k ≤ 73 * l'.length + 4 ∧
      (∃ T, WeakTriangulates ztubg T ∧ c'.output = c.output ++ T.map (relabelList l')) ∧
      (∀ r, (r < 60 ∨ 74 < r) → c'.nreg r = c.nreg r) ∧
      ztbos ∧
      (∀ a, (a < c.nreg 84 + 3 * l'.length ∨ c.nreg 84 + 4 * l'.length ≤ a) →
        c'.nmem a = c.nmem a) ∧
      c'.rmem = c.rmem := by
  unfold fragInit
  refine spec_seq ?_
  exec_block
  · omega
  · zqys
  · zqys
  obtain ⟨c', k, T, ex, hk, hT, hout, hn, hr, hnm, hrm⟩ :=
    mountainSub_exec_weak (P := P) (W := W) hM _ ‹_›
      (fun i hi => by
        config_simp
        grind)
      by_simp_all ztmbv
      (by config_simp; omega) (by config_simp; omega)
  refine ⟨c', k, ex, by_omega, by_grind, fun r hr' => ?_, fun r hr' => ?_,
    fun a ha => ?_, hrm⟩
  · rw [hn r by_omega]
    simp [show r ≠ 60 by omega, show r ≠ 61 by omega, show r ≠ 62 by omega]
  · simp_all
  · rw [hnm a (by config_simp; omega)]
set_option maxHeartbeats 800000 in
/-- **The piece triangulator.**  Let the piece `l` be given as a cyclic linked list
(`PieceInput W l c`, registers `80 … 84`), and let it be a rotated, possibly reversed,
monotone mountain (the conclusion of `Chazelle.Mountain.piece_isMountain`).  Then
`pieceTriStmt` runs with cost `≤ 112 m + 39` (`m = l.length`) and appends to the output
`T.map (relabelList l)` for a weak triangulation `T` of `subPoly P l` (triangles in original
vertex indices).  **Frame:** natural registers outside `60 … 74` and `85 … 94` (in particular
the inputs `80 … 84`), real registers outside `61 … 72` and `80 … 83`, the natural memory
outside the work band `[WB, WB + 4m)` (in particular the linked arrays) and the real memory
are unchanged. -/
theorem pieceTri_exec {l : List ℕ}
    (hmount : ∃ s, IsMountain ztden ∨
      IsMountain ztdeo)
    (c : Config) (hc : WordsBounded W c) (hin : PieceInput W l c) :
    ∃ c' k, Exec P W pieceTriStmt c c' k ∧ k ≤ 112 * l.length + 39 ∧
      (∃ T, WeakTriangulates ztdi T ∧ c'.output = c.output ++ T.map ztbux) ∧
      (∀ r, (r < 60 ∨ (74 < r ∧ r < 85) ∨ 94 < r) → c'.nreg r = c.nreg r) ∧
      (∀ r, (r < 61 ∨ (72 < r ∧ r < 80) ∨ 83 < r) → c'.rreg r = c.rreg r) ∧
      (∀ a, (a < c.nreg 84 ∨ c.nreg 84 + 4 * l.length ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rmem = c.rmem := by
  have h3 : 3 ≤ l.length := by
    zugqs
    · have := h.1.1
      simp_all
    · have := h.1.1
      simp_all
  zuhxt

  -- phase 1
  obtain ⟨c₁, k₁, ex₁, hk₁, hF₁, h88₁, htab₁⟩ := walkPhase_exec (P := P) c hc hin by_omega
  have e83₁ : c₁.nreg 83 = l.length := by rw [hF₁.1 83 by_omega, h83]
  have e84₁ := hF₁.1 84 by_omega
  rw [← e84₁] at htab₁
  -- phase 2
  obtain ⟨c₂, k₂, ex₂, hk₂, hF₂, hnm₂, h88₂, hlo₂, hmin₂⟩ := minPhase_exec (P := P) c₁
    ex₁.wb_right by_omega e83₁ by_omega h88₁ htab₁
  have e83₂ : c₂.nreg 83 = l.length := by rw [hF₂.1 83 by_omega, e83₁]
  have e84₂ := hF₂.1 84 by_omega
  have htab₂ : ∀ i, i < 2 * l.length →
      c₂.nmem (c₂.nreg 84 + i) = l.getD ztdho 0 := by
    simp_all
  -- phase 3
  obtain ⟨c₃, k₃, ex₃, hk₃, hF₃, hnm₃, h88₃, h90₃, hf₃, hb₃⟩ := dirPhase_exec (P := P) c₂
    ex₂.wb_right by_omega e83₂ by_omega h88₂ htab₂
    by_omega (by rw [e84₂]; exact hmin₂.1)
  have e83₃ : c₃.nreg 83 = l.length := by rw [hF₃.1 83 by_omega, e83₂]
  have e84₃ : c₃.nreg 84 = c₁.nreg 84 := by rw [hF₃.1 84 by_omega, e84₂]
  have htab₃ : ∀ i, i < 2 * l.length →
      c₃.nmem (c₃.nreg 84 + i) = l.getD ztdho 0 := by
    simp_all
  rw [e84₂] at hf₃ hb₃
  -- phase 4
  obtain ⟨c₄, k₄, ex₄, hk₄, hF₄, htab₄⟩ := copyPhase_exec (P := P) c₃ ex₃.wb_right e83₃
    by_omega h88₃ htab₃ by_omega
    (by rw [e84₃, h90₃]; exact hmin₂.1) by_grind
    by_grind
  rw [e84₃, h90₃] at htab₄
  have hF := pFrame_trans hF₁ (pFrame_trans hF₂ (pFrame_trans hF₃ hF₄))
  have e83₄ : c₄.nreg 83 = l.length := by rw [hF.1 83 by_omega, h83]
  have e84₄ := hF.1 84 by_omega
  -- phase 5
  have hlen := length_reorient P l ztqkl
  have hM := isMountain_reorient hmount hmin₂
  obtain ⟨c₅, k₅, ex₅, hk₅, ⟨T, hT, hout⟩, hn₅, hr₅, hnm₅, hrm₅⟩ :=
    fragPhase_exec (P := P) (W := W) (l' := reorient P l ztqkl) c₄
      ex₄.wb_right by_omega by_omega hM
      ztjwa
  obtain ⟨T', hT', heq⟩ := goodTri_piece_of_mountain hmin₂ ⟨T, hT, rfl⟩
  rw [hlen] at hk₅
  rw [e84₄, hlen] at hnm₅
  refine ⟨c₅, _, Exec.seq ex₁ (Exec.seq ex₂ (Exec.seq ex₃ (Exec.seq ex₄ ex₅))), by_omega,
    ⟨T', hT', by rw [hout, heq, hF.2.2.2.2]⟩, fun r hr => ?_, fun r hr => ?_, fun a ha => ?_,
    by rw [hrm₅, hF.2.2.2.1]⟩
  · rw [hn₅ r by_omega, hF.1 r by_omega]
  · rw [hr₅ r by_omega, hF.2.1 r by_omega]
  · rw [hnm₅ a by_omega, hF.2.2.1 a by_omega]
