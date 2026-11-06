module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepPrimBool
public import Chazelle.Core.NFLocateChain

/-!
# Sweep RAM primitives (WP-D2), part 2: kernel bits and the walk vertices of a chain model

Building blocks shared by all primitives of `docs/design-merge-v2.md` §9.6.

* `copies_exec`: a block of register copies with disjoint sources and targets.
* `kbit a b d op dst`: one run of the sign kernel (`SignK.signProg`) on the symbolic points held in
  the slots `a`, `b`, `d` (three registers each, `SymPtIn` layout), test `op`; the answer bit goes
  to `dst` (`kbit_exec`).  Every geometric test of the primitives is a `kbit`.
* **The chain environment** `CEnv`: the chain descriptor at the address in register `50200` read
  into the registers of `NFLoc` (host handle `50060`, start `50052`, edges `50053`, top index
  `50054`, orientation bit `50055`, constants), and the number of host points in `50087`
  (`pHead`, `pHead_exec`).
* `tvLoad dst`: the symbolic point of the walk vertex `6 + i` of `chainModel C` (a vertex of the
  tour, `i ≤ 2m`, `i` in register `50120`) into the slot `dst` (`tvLoad_exec`).

Registers: all in the bands `bSign` (the kernel, `10000 … 10499`) and `bLocate` (`NFLoc`'s
`50030 … 50099`, and `50100 … 50999` for the primitives).
-/

namespace Chazelle.Core

namespace SweepPrim

open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open Chazelle.Chain (sideE)

@[expose] public section

/-! ## Copy blocks -/

/-- A block of copies `dst := src`. -/
def copies (l : List (ℕ × ℕ)) : List Instr := l.map fun p => .copyN p.1 p.2

/-- **A block of copies** with targets distinct from all sources and pairwise distinct. -/
theorem copies_exec {P : Polygon} {W : ℕ} : ∀ (l : List (ℕ × ℕ)) (c : Config), WordsBounded W c →
    (∀ p ∈ l, ∀ q ∈ l, p.1 ≠ q.2) → (l.map Prod.fst).Nodup →
    ∃ c', Exec P W (block (copies l)) c c' l.length ∧ (∀ p ∈ l, c'.nreg p.1 = c.nreg p.2) ∧
      (∀ r, r ∉ l.map Prod.fst → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem ∧ c'.output = c.output
  | [], c, hw, _, _ => ⟨c, Exec.block_nil hw, by simp, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | (a, b) :: l, c, hw, hd, hnd => by
    have e₁ := Exec.copyN (P := P) hw a b
    have hnd' : a ∉ l.map Prod.fst ∧ (l.map Prod.fst).Nodup := List.nodup_cons.1 hnd
    obtain ⟨c', e, h1, h2, h3, h4, h5, h6⟩ := copies_exec l _ e₁.wb_right
      (fun p hp q hq => hd p (List.mem_cons_of_mem _ hp) q (List.mem_cons_of_mem _ hq))
      hnd'.2
    refine ⟨c', Exec.block_cons e₁ e, ?_, ?_, h3, h4, h5, h6⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · rw [h2 _ hnd'.1]; simp
      · have hne : a ≠ p.2 := hd (a, b) (by simp) p (List.mem_cons_of_mem _ hp)
        rw [h1 p hp]; simp [Ne.symm hne]
    · intro r hr
      simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [h2 r hr.2]; simp [hr.1]

/-! ## One kernel bit -/

/-- **One sign-kernel bit**: the points of the slots `a`, `b`, `d`, the test `op`; the answer bit
into `dst`. -/
def kbit (a b d op dst : ℕ) : Stmt :=
  .seq (block (copies [(10000, a), (10001, a + 1), (10002, a + 2), (10003, b), (10004, b + 1),
      (10005, b + 2), (10006, d), (10007, d + 1), (10008, d + 2)]))
    (.seq (.instr (.constN 10009 op)) (.seq signProg (.instr (.copyN dst 10010))))

/-- The registers written by `kbit _ _ _ _ dst`. -/
def Bkb (dst r : ℕ) : Bool := Bk r || r == dst

theorem wr_signProg : wr Bk signProg = true := by decide

theorem wr_kbit (a b d op dst : ℕ) : wr (Bkb dst) (kbit a b d op dst) = true := by
  have h := wr_mono wr_signProg (B' := Bkb dst) (fun r hr => by core_grind)
  simp_all [kbit, copies, List.map_cons, List.map_nil, block_cons, block_nil, wr, wrOK, Bkb, Bk]

/-- **Execution of one kernel bit** (at most `241` steps). -/
theorem kbit_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) {a b d op dst : ℕ} (ha : 10500 ≤ a) (hb : 10500 ≤ b) (hd : 10500 ≤ d)
    (_hdst : 10500 ≤ dst) (hop : op ≤ 3) {sa sb sd : SymPt} (hla : sa.Lt P.n) (hlb : sb.Lt P.n)
    (hld : sd.Lt P.n) (hsa : SymPtIn c a sa) (hsb : SymPtIn c b sb) (hsd : SymPtIn c d sd) :
    ∃ c' k, Exec P W (kbit a b d op dst) c c' k ∧ k ≤ 241 ∧ FrameB (Bkb dst) c c' ∧
      c'.nreg dst ≤ 1 ∧
      (c'.nreg dst = 1 ↔ SignTest op (sa.eval (Qof P)) (sb.eval (Qof P)) (sd.eval (Qof P))) := by
  obtain ⟨c₁, e₁, h1, _h2, _h3, _h4, _h5, _h6⟩ := copies_exec (P := P)
    [(10000, a), (10001, a + 1), (10002, a + 2), (10003, b), (10004, b + 1),
      (10005, b + 2), (10006, d), (10007, d + 1), (10008, d + 2)] c hw
    (by intro p hp q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        grind <;> simp )
    (by simp)
  have w₁ := e₁.wb_right
  have i1 : SymPtIn c₁ 10000 sa := symPtIn_copy hsa (h1 (10000, a) (by simp))
    (h1 (10001, a + 1) (by simp)) (h1 (10002, a + 2) (by simp))
  have i2 : SymPtIn c₁ 10003 sb := symPtIn_copy hsb (h1 (10003, b) (by simp))
    (h1 (10004, b + 1) (by simp)) (h1 (10005, b + 2) (by simp))
  have i3 : SymPtIn c₁ 10006 sd := symPtIn_copy hsd (h1 (10006, d) (by simp))
    (h1 (10007, d + 1) (by simp)) (h1 (10008, d + 2) (by simp))
  have e₂ := Exec.constN (P := P) w₁ 10009 op (by omega)
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg 10009 op } with hc₂
  have w₂ : WordsBounded W c₂ := e₂.wb_right
  have k2 : ∀ r, r ≠ 10009 → c₂.nreg r = c₁.nreg r := fun r hr => by rw [hc₂]; simp [hr]
  have j1 : SymPtIn c₂ 10000 sa := symPtIn_copy i1 (k2 _ (by omega)) (k2 _ (by omega))
    (k2 _ (by omega))
  have j2 : SymPtIn c₂ 10003 sb := symPtIn_copy i2 (k2 _ (by omega)) (k2 _ (by omega))
    (k2 _ (by omega))
  have j3 : SymPtIn c₂ 10006 sd := symPtIn_copy i3 (k2 _ (by omega)) (k2 _ (by omega))
    (k2 _ (by omega))
  have o2 : c₂.nreg 10009 = op := by rw [hc₂]; simp
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, bit₃, sig₃⟩ := sig_exec (P := P) c₂ w₂ hG hW (by omega) hla hlb
    hld j1 j2 j3
  have w₃ := e₃.wb_right
  have e₄ := Exec.copyN (P := P) w₃ dst 10010
  have ex : Exec P W (kbit a b d op dst) c _ (9 + (1 + (k₃ + 1))) :=
    .seq e₁ (.seq e₂ (.seq e₃ e₄))
  refine ⟨_, _, ex, by omega, exec_frameB ex (wr_kbit a b d op dst), ?_, ?_⟩
  all_goals (grind [upd_same])

/-! ## The chain environment -/

/-- The registers the chain environment keeps. -/
def envRegs : List ℕ :=
  [50032, 50052, 50053, 50054, 50055, 50060, 50061, 50067, 50068, 50069, 50081, 50082, 50083,
    50084, 50085, 50087]

/-- **The chain environment**: the chain `C` of the host `H` realised in `Qof P` is loaded in the
registers of `NFLoc` (see the module docstring); the host is well formed and addressable. -/
structure CEnv (P : Polygon) (W : ℕ) (H : Host) (C : Chain) (c : Config) : Prop where
  host : HostEnv W (c.nreg 50060) H.length c.nmem c
  hH : HostAt c.nmem (c.nreg 50060) H
  wf : HostWF P.n H
  aW : c.nreg 50060 + 3 * H.length + 4 ≤ W
  NW : 2 * (H.pts P.n).length ≤ W
  hP : C.P = H.poly (Qof P)
  r32 : c.nreg 50032 = 1
  r52 : c.nreg 50052 = C.s
  r53 : c.nreg 50053 = C.m
  r54 : c.nreg 50054 = C.topIdx
  r55 : c.nreg 50055 = 1 ↔ C.sideBeta = true
  r81 : c.nreg 50081 = 6
  r82 : c.nreg 50082 = 2
  r83 : c.nreg 50083 = 3
  r84 : c.nreg 50084 = 4
  r85 : c.nreg 50085 = 5
  r87 : c.nreg 50087 = (H.pts P.n).length
  hs : C.s < (H.pts P.n).length
  hG : GoodEnv P
  hW : P.n + 3 ≤ W
  hlen : H.length ≤ 64

namespace CEnv

variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {c c' : Config}

section
variable (h : CEnv P W H C c)
include h
theorem wb : WordsBounded W c := h.host.wb

/-- The number of points of the host polygon is the number of host points. -/
theorem n_eq : C.P.n = (H.pts P.n).length := by
  rw [h.hP]
  show ((H.pts (Qof P).n).map (SymPt.eval (Qof P))).length = _
  rw [List.length_map, show (Qof P).n = P.n from shear_n _ _]

/-- **The environment survives** a step that keeps its registers and the memory. -/
theorem keep (hw : WordsBounded W c') (hm : c'.nmem = c.nmem)
    (hr : ∀ r ∈ envRegs, c'.nreg r = c.nreg r) : CEnv P W H C c' := by
  have g := fun r (hr' : r ∈ envRegs) => hr r hr'
  have e60 : c'.nreg 50060 = c.nreg 50060 := g _ (by decide)
  refine ⟨⟨hw, ?_, ?_, ?_, ?_, ?_, rfl⟩, ?_, h.wf, ?_, h.NW, h.hP, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, h.hs, h.hG, h.hW, h.hlen⟩
  · rfl
  · rw [g _ (by decide)]; exact h.host.h61
  · rw [g _ (by decide)]; exact h.host.h67
  · rw [g _ (by decide)]; exact h.host.h68
  · rw [g _ (by decide)]; exact h.host.h69
  · ram_grind
  · ram_grind
  · rw [g _ (by decide)]; exact h.r32
  · rw [g _ (by decide)]; exact h.r52
  · rw [g _ (by decide)]; exact h.r53
  · rw [g _ (by decide)]; exact h.r54
  · rw [g _ (by decide)]; exact h.r55
  · rw [g _ (by decide)]; exact h.r81
  · rw [g _ (by decide)]; exact h.r82
  · rw [g _ (by decide)]; exact h.r83
  · rw [g _ (by decide)]; exact h.r84
  · rw [g _ (by decide)]; exact h.r85
  · rw [g _ (by decide)]; exact h.r87


end

/-- The environment survives a register frame avoiding its registers. -/
theorem frame {B : ℕ → Bool} (h : CEnv P W H C c) (hf : FrameB B c c') (hw : WordsBounded W c')
    (hB : ∀ r ∈ envRegs, B r = false) : CEnv P W H C c' :=
  h.keep hw hf.2.2.1 fun r hr => hf.1 r (hB r hr)

/-- The environment survives the host routines. -/
theorem of_host (h : CEnv P W H C c) (E : HostEnv W (c.nreg 50060) H.length c.nmem c')
    (hf : FrameB Bhost c c') : CEnv P W H C c' := by
  ram_grind

end CEnv

/-! ## Reading the descriptor -/

/-- Read the chain descriptor at the address in `50200` (see the module docstring), count the host
points into `50087`. -/
def pHead : Stmt :=
  .seq (block [.constN 50032 1, .loadN 50060 50200, .addN 50050 50200 50032, .loadN 50052 50050,
      .addN 50050 50050 50032, .loadN 50053 50050, .addN 50050 50050 50032, .loadN 50054 50050,
      .addN 50050 50050 50032, .loadN 50055 50050, .constN 50081 6, .constN 50082 2,
      .constN 50083 3, .constN 50084 4, .constN 50085 5])
    (.seq cntStmt (.instr (.copyN 50087 50063)))

/-- The registers written by `pHead`. -/
def Bhead (r : ℕ) : Bool := Bhost r || decide (50030 ≤ r ∧ r < 50100)

theorem wr_pHead : wr Bhead pHead = true := by decide

/-- **Reading a well-formed chain descriptor** (at most `12 |H| + 28` steps). -/
theorem pHead_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) {X : ℕ} (hX : c.nreg 50200 = X) {H : Host} {C : Chain}
    (hC : ChainDescAt c.nmem X (Qof P) H C) (hX5 : X + 5 ≤ W) (hlen : H.length ≤ 64)
    (hwf : HostWF P.n H) (haW : c.nmem X + 3 * H.length + 4 ≤ W) (hs : C.s < C.P.n) :
    ∃ c' k, Exec P W pHead c c' k ∧ k ≤ 12 * H.length + 28 ∧ FrameB Bhead c c' ∧
      CEnv P W H C c' := by
  obtain ⟨hHost, hP, hs', hm', hT', hb'⟩ := hC
  have hn : P.n + 3 ≤ W := by unfold hostWords at hW; omega
  have h3 : 3 ≤ P.n := hG.1.1
  have hNlen : C.P.n = (H.pts P.n).length := by
    rw [hP]
    show ((H.pts (Qof P).n).map (SymPt.eval (Qof P))).length = _
    rw [List.length_map, show (Qof P).n = P.n from shear_n _ _]
  have hN : (H.pts P.n).length ≤ 64 * P.n := by
    have := Host.pts_length_le hwf
    calc (H.pts P.n).length ≤ H.length * P.n := this
      _ ≤ 64 * P.n := Nat.mul_le_mul_right _ hlen
  have hNW : 2 * (H.pts P.n).length ≤ W := by unfold hostWords at hW; omega
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.constN 50032 1, .loadN 50060 50200,
      .addN 50050 50200 50032, .loadN 50052 50050, .addN 50050 50050 50032, .loadN 50053 50050,
      .addN 50050 50050 50032, .loadN 50054 50050, .addN 50050 50050 50032, .loadN 50055 50050,
      .constN 50081 6, .constN 50082 2, .constN 50083 3, .constN 50084 4, .constN 50085 5])
      c c₁ k₁ ∧ k₁ = 15 ∧
      (c₁.nreg 50032 = 1 ∧ c₁.nreg 50060 = c.nmem X ∧ c₁.nreg 50052 = C.s ∧
        c₁.nreg 50053 = C.m ∧ c₁.nreg 50054 = C.topIdx ∧ c₁.nreg 50055 = c.nmem (X + 4) ∧
        c₁.nreg 50081 = 6 ∧ c₁.nreg 50082 = 2 ∧ c₁.nreg 50083 = 3 ∧ c₁.nreg 50084 = 4 ∧
        c₁.nreg 50085 = 5 ∧ c₁.nmem = c.nmem) := by
    exec_block
    all_goals try omega
    all_goals try (config_simp; omega)
    refine ⟨rfl, ?_⟩
    config_simp
    rw [hX]
    refine ⟨rfl, hs', ?_, ?_, ?_⟩
    · rw [show X + 1 + 1 = X + 2 by ring]; exact hm'
    · rw [show X + 1 + 1 + 1 = X + 3 by ring]; exact hT'
    · rw [show X + 1 + 1 + 1 + 1 = X + 4 by ring]
  obtain ⟨q32, q60, q52, q53, q54, q55, q81, q82, q83, q84, q85, qm⟩ := q
  have w₁ := e₁.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, n63, E₂⟩ := cnt_exec (P := P) (n := P.n) c₁ w₁
    (by rw [qm]; exact hHost) q60 haW (by omega)
  have w₂ := e₂.wb_right
  have e₃ := Exec.copyN (P := P) w₂ 50087 50063
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 50087 (c₂.nreg 50063) } with hc₃
  have ex : Exec P W pHead c c₃ (k₁ + (k₂ + 1)) := .seq e₁ (.seq e₂ e₃)
  have g₂ := fun r (hr : Bhost r = false) => f₂.1 r hr
  have r3 : ∀ r, r ≠ 50087 → c₃.nreg r = c₂.nreg r := fun r hr => by rw [hc₃]; simp [hr]
  have r3' : ∀ r, r ≠ 50087 → Bhost r = false → c₃.nreg r = c₁.nreg r := fun r hr hb => by
    rw [r3 r hr, g₂ r hb]
  refine ⟨c₃, _, ex, by omega, exec_frameB ex wr_pHead, ?_⟩
  have m₃ : c₃.nmem = c.nmem := by rw [hc₃]; show c₂.nmem = c.nmem; rw [f₂.2.2.1, qm]
  have h60 : c₃.nreg 50060 = c.nmem X := by rw [r3' _ (by decide) (by decide), q60]
  refine ⟨⟨e₃.wb_right, rfl, by rw [r3 _ (by decide)]; exact E₂.h61,
    by rw [r3 _ (by decide)]; exact E₂.h67, by rw [r3 _ (by decide)]; exact E₂.h68,
    by rw [r3 _ (by decide)]; exact E₂.h69, rfl⟩, ?_, hwf, ?_, hNW, hP,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hc₃]; simp [n63],
    by rw [← hNlen]; exact hs, hG, hn, hlen⟩
  · rw [h60, m₃]; exact hHost
  · rw [h60]; exact haW
  · rw [r3' _ (by decide) (by decide), q32]
  · rw [r3' _ (by decide) (by decide), q52]
  · rw [r3' _ (by decide) (by decide), q53]
  · rw [r3' _ (by decide) (by decide), q54]
  · rw [r3' _ (by decide) (by decide), q55]; exact hb'
  · rw [r3' _ (by decide) (by decide), q81]
  · rw [r3' _ (by decide) (by decide), q82]
  · rw [r3' _ (by decide) (by decide), q83]
  · rw [r3' _ (by decide) (by decide), q84]
  · rw [r3' _ (by decide) (by decide), q85]

/-! ## The walk vertices of the tour -/

/-- The tour position of step `i ≤ 2m` by one conditional subtraction. -/
theorem tour_idx {m S i : ℕ} (hm : 1 ≤ m) (hS : S ≤ 2 * m) (hi : i ≤ 2 * m) :
    sideE m (if i < 2 * m - S then S + i else i - (2 * m - S)) = sideE m ((S + i) % (2 * m)) := by
  split_ifs with h
  · rw [Nat.mod_eq_of_lt (by omega)]
  · by_cases h2 : i - (2 * m - S) < 2 * m
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      grind
    · have e1 : i - (2 * m - S) = 2 * m := by omega
      have e2 : S + i = 2 * m + 2 * m := by omega
      rw [e1, e2, Nat.add_mod_right, Nat.mod_self]
      core_grind

/-- **The chain vertex index of tour step `i`** (in `50120`) into `50091`. -/
def tvIdx : Stmt :=
  .seq (.instr (.addN 50058 50053 50053))
    (.seq (.ifLtN 50055 50032 (.instr (.subN 50059 50058 50054))
        (.ifLtN 50032 50055 (.instr (.subN 50059 50058 50054)) (.instr (.copyN 50059 50054))))
      (.seq (.instr (.subN 50089 50058 50059))
        (.seq (.ifLtN 50120 50089 (.instr (.addN 50077 50059 50120))
            (.instr (.subN 50077 50120 50089)))
          (.ifLtN 50053 50077 (.instr (.subN 50091 50058 50077)) (.instr (.copyN 50091 50077))))))

/-- The registers written by `tvIdx`. -/
def Btvi (r : ℕ) : Bool := [50058, 50059, 50089, 50077, 50091].contains r

theorem wr_tvIdx : wr Btvi tvIdx = true := by decide

/-- **The chain vertex index of a tour step** (at most `16` steps). -/
theorem tvIdx_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {i : ℕ} (h120 : c.nreg 50120 = i) (hi : i ≤ 2 * C.m) :
    ∃ c' k, Exec P W tvIdx c c' k ∧ k ≤ 16 ∧ FrameB Btvi c c' ∧
      c'.nreg 50091 = C.sideIdx C.sideBeta i ∧ c'.nreg 50058 = 2 * C.m ∧
      c'.nreg 50059 = C.sideS C.sideBeta ∧ c'.nreg 50089 = 2 * C.m - C.sideS C.sideBeta ∧
      c'.nreg 50077 = (if i < 2 * C.m - C.sideS C.sideBeta then C.sideS C.sideBeta + i
        else i - (2 * C.m - C.sideS C.sideBeta)) := by
  have hw := hE.wb
  have hm1 := C.one_le
  have hmN : C.m < (H.pts P.n).length := by rw [← hE.n_eq]; exact C.m_lt
  
  set m := C.m
  set T := C.topIdx
  set S := C.sideS C.sideBeta with hSdef
  have hS2 : S ≤ 2 * m := C.sideS_lt _
  have h53 := hE.r53
  have h54 := hE.r54
  have h32 := hE.r32
  have e₁ := Exec.addN (P := P) hw 50058 50053 50053 (by ram_grind)
  set c₁ : Config := { c with nreg := upd c.nreg 50058 (c.nreg 50053 + c.nreg 50053) } with hc₁
  have w₁ : WordsBounded W c₁ := e₁.wb_right
  have q58 : c₁.nreg 50058 = 2 * m := by ram_simp <;> omega_nf
  have q : ∀ r, r ≠ 50058 → c₁.nreg r = c.nreg r := fun r hr => by simp_all
  obtain ⟨c₂, k₂, e₂, hk₂, q59, r₂⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 50055 50032
      (.instr (.subN 50059 50058 50054))
      (.ifLtN 50032 50055 (.instr (.subN 50059 50058 50054)) (.instr (.copyN 50059 50054))))
      c₁ c₂ k₂ ∧ k₂ ≤ 5 ∧ c₂.nreg 50059 = S ∧ ∀ r, r ≠ 50059 → c₂.nreg r = c₁.nreg r := by
    have b32 : c₁.nreg 50032 = 1 := by simp_all
    have b54 : c₁.nreg 50054 = T := by grind
    have hb := hE.r55
    have b55 : c₁.nreg 50055 = c.nreg 50055 := q _ (by omega)
    by_cases h0 : c.nreg 50055 < 1
    · have hβ : C.sideBeta = false := by
        simp_all
      refine spec_ifLtN_true (by omega)
        (spec_instr (Exec.subN w₁ _ _ _) fun _ => ⟨by omega, ?_, fun r hr => by simp [hr]⟩)
      config_simp; grind [Chain.sideS]
    · refine spec_ifLtN_false (by omega) ?_
      by_cases h2 : 1 < c.nreg 50055
      · have hβ : C.sideBeta = false := by
          grind
        refine spec_ifLtN_true (by omega)
          (spec_instr (Exec.subN w₁ _ _ _) fun _ => ⟨by omega, ?_, fun r hr => by simp [hr]⟩)
        config_simp; grind [Chain.sideS]
      · have hβ : C.sideBeta = true := hb.1 (by omega)
        refine spec_ifLtN_false (by omega)
          (spec_instr (Exec.copyN w₁ _ _) fun _ => ⟨by omega, ?_, fun r hr => by simp [hr]⟩)
        simp_all [Chain.sideS]
  have w₂ := e₂.wb_right
  have e₃ := Exec.subN (P := P) w₂ 50089 50058 50059
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 50089 (c₂.nreg 50058 - c₂.nreg 50059) }
    with hc₃
  have w₃ : WordsBounded W c₃ := e₃.wb_right
  have t89 : c₃.nreg 50089 = 2 * m - S := by
    rw [hc₃]; config_simp; grind
  have t : ∀ r, r ≠ 50089 → c₃.nreg r = c₂.nreg r := fun r hr => by rw [hc₃]; simp [hr]
  have t120 : c₃.nreg 50120 = i := by
    grind
  have t59 : c₃.nreg 50059 = S := by grind
  obtain ⟨c₄, k₄, e₄, hk₄, j4, r₄⟩ : ∃ c₄ k₄, Exec P W (.ifLtN 50120 50089
      (.instr (.addN 50077 50059 50120)) (.instr (.subN 50077 50120 50089))) c₃ c₄ k₄ ∧
      k₄ ≤ 3 ∧ c₄.nreg 50077 = (if i < 2 * m - S then S + i else i - (2 * m - S)) ∧
      ∀ r, r ≠ 50077 → c₄.nreg r = c₃.nreg r := by
    by_cases hc : i < 2 * m - S
    · refine spec_ifLtN_true (by omega) (spec_instr (Exec.addN w₃ _ _ _
        (by ram_grind)) fun _ =>
          ⟨by omega, ?_, fun r hr => by simp [hr]⟩)
      config_simp; grind
    · refine spec_ifLtN_false (by omega) (spec_instr (Exec.subN w₃ _ _ _)
        fun _ => ⟨by omega, ?_, fun r hr => by simp [hr]⟩)
      config_simp; grind
  have w₄ := e₄.wb_right
  set j := (if i < 2 * m - S then S + i else i - (2 * m - S)) with hj
  have u53 : c₄.nreg 50053 = m := by
    grind
  have u58 : c₄.nreg 50058 = 2 * m := by
    grind
  obtain ⟨c₅, k₅, e₅, hk₅, k91, r₅⟩ : ∃ c₅ k₅, Exec P W (.ifLtN 50053 50077
      (.instr (.subN 50091 50058 50077)) (.instr (.copyN 50091 50077))) c₄ c₅ k₅ ∧
      k₅ ≤ 3 ∧ c₅.nreg 50091 = sideE m j ∧ ∀ r, r ≠ 50091 → c₅.nreg r = c₄.nreg r := by
    rw [sideE_eq]
    by_cases hc : m < j
    · refine spec_ifLtN_true (by omega) (spec_instr (Exec.subN w₄ _ _ _)
        fun _ => ⟨by omega, ?_, fun r hr => by simp [hr]⟩)
      config_simp; grind
    · refine spec_ifLtN_false (by omega) (spec_instr (Exec.copyN w₄ _ _)
        fun _ => ⟨by omega, ?_, fun r hr => by simp [hr]⟩)
      config_simp; grind
  have ex : Exec P W tvIdx c c₅ (1 + (k₂ + (1 + (k₄ + k₅)))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  refine ⟨c₅, _, ex, by omega, exec_frameB ex wr_tvIdx, ?_, by grind,
    by grind, by grind,
    by grind⟩
  rw [k91, hj, tour_idx hm1 hS2 hi, C.sideIdx_eq]

/-- **Load the walk vertex `6 + i`** (`i` in `50120`) into the slot `dst`. -/
def tvLoad (dst : ℕ) : Stmt :=
  .seq tvIdx (.seq hostPt (block (copies [(dst, 50046), (dst + 1, 50047), (dst + 2, 50048)])))

/-- The registers written by `tvLoad dst`. -/
def Btv (dst r : ℕ) : Bool := Btvi r || Bhost r || decide (dst ≤ r ∧ r < dst + 3)

theorem wr_tvLoad (dst : ℕ) : wr (Btv dst) (tvLoad dst) = true := by
  have h1 := wr_mono wr_tvIdx (B' := Btv dst) (fun r hr => by simp_all [Btv])
  have h2 := wr_mono wr_hostPt (B' := Btv dst) (fun r hr => by simp_all [Btv])
  simp_all [tvLoad, copies, List.map_cons, List.map_nil, block_cons, block_nil, wr, wrOK, Btv]

/-- The walk vertex `6 + i` of the chain model is the chain vertex of tour step `i`. -/
theorem walk_vtx_tour (C : Chain) {i : ℕ} (hi : i ≤ 2 * C.m) :
    (chainModel C).W.vtx (i + 6) = C.vertex (C.sideIdx C.sideBeta i) :=
  C.sideWalk_vtx_tour _ hi

/-- **Loading a walk vertex of the tour** (at most `27 |H| + 40` steps): the slot `dst` receives a
symbolic point in range whose point is the walk vertex `6 + i`. -/
theorem tvLoad_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {i : ℕ} (h120 : c.nreg 50120 = i) (hi : i ≤ 2 * C.m) {dst : ℕ}
    (hdst : 50100 ≤ dst) :
    ∃ c' k, Exec P W (tvLoad dst) c c' k ∧ k ≤ 27 * H.length + 40 ∧ FrameB (Btv dst) c c' ∧
      CEnv P W H C c' ∧ ∃ sp : SymPt, SymPtIn c' dst sp ∧ sp.Lt P.n ∧
        sp.eval (Qof P) = (chainModel C).W.vtx (i + 6) ∧
        (H.pts P.n)[(C.s + C.sideIdx C.sideBeta i) % (H.pts P.n).length]? = some sp := by
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, k91, -⟩ := tvIdx_exec c hE h120 hi
  have hE₁ : CEnv P W H C c₁ := hE.frame f₁ e₁.wb_right (by decide)
  have hmN : C.m < (H.pts P.n).length := by rw [← hE.n_eq]; exact C.m_lt
  have hk : C.sideIdx C.sideBeta i < (H.pts P.n).length :=
    lt_of_le_of_lt (C.sideIdx_le _ _) hmN
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, E₂, sp, hsp, hin⟩ := hostPt_exec (P := P) c₁ hE₁.host hE₁.hH
    hE₁.wf (by have := hE₁.hW; omega) hE₁.aW hE₁.NW hE₁.r52 hE₁.r87 k91 hE₁.hs hk
  have hE₂ : CEnv P W H C c₂ := hE₁.of_host E₂ f₂
  obtain ⟨c₃, e₃, h3, h3', _h3r, h3m, _h3rm, _h3o⟩ := copies_exec (P := P)
    [(dst, 50046), (dst + 1, 50047), (dst + 2, 50048)] c₂ e₂.wb_right
    (by intro p hp q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
        grind)
    (by simp)
  have ex : Exec P W (tvLoad dst) c c₃ (k₁ + (k₂ + 3)) := .seq e₁ (.seq e₂ e₃)
  refine ⟨c₃, _, ex, by omega, exec_frameB ex (wr_tvLoad dst), ?_, sp, ?_, ?_, ?_, ?_⟩
  · refine hE₂.keep e₃.wb_right h3m fun r hr => h3' r ?_
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
    omega
  · exact symPtIn_copy hin (h3 (dst, 50046) (by simp)) (h3 (dst + 1, 50047) (by simp))
      (h3 (dst + 2, 50048) (by simp))
  · exact hostWF_pts hE.wf (by have := hE.hG.1.1; omega) _ (List.mem_of_getElem? hsp)
  · rw [walk_vtx_tour C hi, chain_vertex_host C hE.hP _ (sp := sp)]
    rw [show (Qof P).n = P.n from shear_n _ _, hE.n_eq]
    exact hsp
  · exact hsp

end

end SweepPrim

end Chazelle.Core
