module

public import Chazelle.MacT
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Core.FuseMathCut
public import Chazelle.Core.OracleQuery
public import Chazelle.Core.WalkEmbed
public import Mathlib.Data.List.GetD
public import Chazelle.Core.RestoreRound
public import Chazelle.Core.BruteCorner

namespace Chazelle.Core
namespace SweepPrim
open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open Chazelle.Chain (sideE)
@[expose] public section
def copies (l : List ztw) : List Instr := l.map fun p => .copyN p.1 p.2

/-- **A block of copies** with targets distinct from all sources and pairwise distinct. -/
theorem copies_exec {P : Polygon} {W : ℕ} : ∀ (l : List ztw) (c : Config), WordsBounded W c →
    (∀ p ∈ l, ∀ q ∈ l, p.1 ≠ q.2) → (l.map Prod.fst).Nodup →
    ∃ c', Exec P W ztgfh c c' l.length ∧ ztfcu ∧
      (∀ r, r ∉ l.map Prod.fst → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem ∧ c'.output = c.output
  | [], c, hw, _, _ => ⟨c, Exec.block_nil hw, by_simp, by_omega, rfl, rfl, rfl, rfl⟩
  | (a, b) :: l, c, hw, hd, hnd => by
    have e₁ := Exec.copyN (P := P) hw a b
    zuhfk
    obtain ⟨c', e, h1, h2, h3, h4, h5, h6⟩ := copies_exec l _ e₁.wb_right
      (fun p hp q hq => hd p ztszj q ztnmm)
      hnd'.2
    refine ⟨c', Exec.block_cons e₁ e, ?_, ?_, h3, h4, h5, h6⟩
    · zuda
      zueuz
      · rw [h2 _ hnd'.1]; simp
      · have hne := hd ztvk by_simp p by_omega
        rw [h1 p hp]; simp [Ne.symm hne]
    · zuz
      zugha
      rw [h2 r hr.2]; simp [hr.1]

/-! ## One kernel bit -/

/-- **One sign-kernel bit**: the points of the slots `a`, `b`, `d`, the test `op`; the answer bit
into `dst`. -/
def kbit (a b d op dst : ℕ) : Stmt :=
  .seq (block (copies [ztnds, ztjee, ztjef, ztndt, ztjeg,
      ztjeh, ztndu, ztjei, ztjej]))
    (.seq ztifn (.seq signProg (.instr (.copyN dst 10010))))

/-- The registers written by `kbit _ _ _ _ dst`. -/
def Bkb (dst r : ℕ) : Bool := Bk r || r == dst
theorem wr_signProg : wr Bk signProg = true := by_decide
theorem wr_kbit (a b d op dst : ℕ) : wr ztdks ztfib = true := by
  have h := wr_mono wr_signProg (B' := Bkb dst) (fun r hr => by simp [Bkb, hr])
  simp only [kbit, copies, List.map_cons, List.map_nil, block_cons, block_nil, wr, wrOK, h]
  simp [Bkb, Bk]

/-- **Execution of one kernel bit** (at most `241` steps). -/
theorem kbit_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) {a b d op dst : ℕ} (ha : 10500 ≤ a) (hb : 10500 ≤ b) (hd : 10500 ≤ d)
    (_hdst : 10500 ≤ dst) (hop : op ≤ 3) {sa sb sd : SymPt} (hla : sa.Lt P.n) (hlb : sb.Lt P.n)
    (hld : sd.Lt P.n) (hsa : SymPtIn c a sa) (hsb : SymPtIn c b sb) (hsd : SymPtIn c d sd) :
    ∃ c' k, Exec P W ztfib c c' k ∧ k ≤ 241 ∧ FrameB ztdks c c' ∧
      c'.nreg dst ≤ 1 ∧
      (c'.nreg dst = 1 ↔ SignTest op ztxhi ztxoq ztbaiq) := by
  obtain ⟨c₁, e₁, h1, _h2, _h3, _h4, _h5, _h6⟩ := copies_exec (P := P)
    [ztnds, ztjee, ztjef, ztndt, ztjeg,
      ztjeh, ztndu, ztjei, ztjej] c hw
    (by intro p hp q hq; zvmxh at hp hq
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
    by_simp
  zud
  have i1 := symPtIn_copy hsa (h1 ztnds by_simp)
    (h1 ztjee by_simp) (h1 ztjef by_simp)
  have i2 := symPtIn_copy hsb (h1 ztndt by_simp)
    (h1 ztjeg by_simp) (h1 ztjeh by_simp)
  have i3 := symPtIn_copy hsd (h1 ztndu by_simp)
    (h1 ztjei by_simp) (h1 ztjej by_simp)
  have e₂ := Exec.constN (P := P) w₁ 10009 op by_omega
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg 10009 op } with hc₂
  zue
  have k2 : ∀ r, r ≠ 10009 → c₂.nreg r = c₁.nreg r := fun r hr => by zumxp; zumwy
  have j1 : SymPtIn c₂ 10000 sa := symPtIn_copy i1 by_grind by_grind
    by_grind
  have j2 : SymPtIn c₂ 10003 sb := symPtIn_copy i2 by_grind by_grind
    by_grind
  have j3 : SymPtIn c₂ 10006 sd := symPtIn_copy i3 by_grind by_grind
    by_grind
  have o2 : c₂.nreg 10009 = op := by_rfl
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, bit₃, sig₃⟩ := sig_exec (P := P) c₂ w₂ hG hW by_omega hla hlb
    hld j1 j2 j3
  zubj
  have e₄ := Exec.copyN (P := P) w₃ dst 10010
  have ex : Exec P W ztfib c _ (9 + ztndk) :=
    .seq e₁ ztcb
  refine ⟨_, _, ex, by_omega, exec_frameB ex ztpeo, ?_, ?_⟩
  · zucac
  · zumb

/-! ## The chain environment -/

/-- The registers the chain environment keeps. -/
def envRegs : List ℕ :=
  [50032, 50052, 50053, 50054, 50055, 50060, 50061, 50067, 50068, 50069, 50081, 50082, 50083,
    50084, 50085, 50087]

/-- **The chain environment**: the chain `C` of the host `H` realised in `Qof P` is loaded in the
registers of `NFLoc` (see the module docstring); the host is well formed and addressable. -/
structure CEnv (P : Polygon) (W : ℕ) (H : Host) (C : Chain) (c : Config) : Prop where
  host : HostEnv W ztmge H.length c.nmem c
  hH : HostAt c.nmem ztmge H
  wf : HostWF P.n H
  aW : c.nreg 50060 + 3 * H.length + 4 ≤ W
  NW : 2 * (H.pts P.n).length ≤ W
  hP : C.P = H.poly zta
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
theorem wb (h : CEnv P W H C c) : WordsBounded W c := h.host.wb

/-- The number of points of the host polygon is the number of host points. -/
theorem n_eq (h : CEnv P W H C c) : C.P.n = (H.pts P.n).length := by
  rw [h.hP]
  show ((H.pts (Qof P).n).map _).length = _
  zudjs

/-- **The environment survives** a step that keeps its registers and the memory. -/
theorem keep (h : CEnv P W H C c) (hw : WordsBounded W c') (hm : c'.nmem = c.nmem)
    (hr : ∀ r ∈ envRegs, c'.nreg r = c.nreg r) : CEnv P W H C c' := by
  have g := by_omega
  have e60 : c'.nreg 50060 = c.nreg 50060 := g _ by_decide
  refine ⟨⟨hw, ?_, ?_, ?_, ?_, ?_, rfl⟩, ?_, h.wf, ?_, h.NW, h.hP, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, h.hs, h.hG, h.hW, h.hlen⟩
  · rfl
  · zumxb; exact h.host.h61
  · zumxb; exact h.host.h67
  · zumxb; exact h.host.h68
  · zumxb; exact h.host.h69
  · rw [hm, e60]; exact h.hH
  · rw [e60]; exact h.aW
  · zumxb; exact h.r32
  · zumxb; exact h.r52
  · zumxb; exact h.r53
  · zumxb; exact h.r54
  · zumxb; exact h.r55
  · zumxb; exact h.r81
  · zumxb; exact h.r82
  · zumxb; exact h.r83
  · zumxb; exact h.r84
  · zumxb; exact h.r85
  · zumxb; exact h.r87

/-- The environment survives a register frame avoiding its registers. -/
theorem frame {B : ℕ → Bool} (h : CEnv P W H C c) (hf : FrameB B c c') (hw : WordsBounded W c')
    (hB : ∀ r ∈ envRegs, B r = false) : CEnv P W H C c' :=
  h.keep hw hf.2.2.1 fun r hr => hf.1 r by_simp_all

/-- The environment survives the host routines. -/
theorem of_host (h : CEnv P W H C c) (E : HostEnv W ztmge H.length c.nmem c')
    (hf : FrameB Bhost c c') : CEnv P W H C c' := by
  zuiyj
  refine h.keep E.wb hm fun r hr => ?_
  zujs
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  all_goals first
    | exact hf.1 _ by_decide
    | (rw [E.h61, h.host.h61])
    | (rw [E.h67, h.host.h67])
    | (rw [E.h68, h.host.h68])
    | (rw [E.h69, h.host.h69])
end CEnv

/-! ## Reading the descriptor -/

/-- Read the chain descriptor at the address in `50200` (see the module docstring), count the host
points into `50087`. -/
def pHead : Stmt :=
  .seq (block [.constN 50032 1, .loadN 50060 50200, .addN 50050 50200 50032, .loadN 50052 50050,
      .addN 50050 50050 50032, .loadN 50053 50050, .addN 50050 50050 50032, .loadN 50054 50050,
      .addN 50050 50050 50032, .loadN 50055 50050, .constN 50081 6, .constN 50082 2,
      .constN 50083 3, .constN 50084 4, .constN 50085 5])
    ztkpq

/-- The registers written by `pHead`. -/
def Bhead (r : ℕ) : Bool := Bhost r || decide ztngu
theorem wr_pHead : wr Bhead pHead = true := by_decide

/-- **Reading a well-formed chain descriptor** (at most `12 |H| + 28` steps). -/
theorem pHead_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) {X : ℕ} (hX : c.nreg 50200 = X) {H : Host} {C : Chain}
    (hC : ChainDescAt c.nmem X zta H C) (hX5 : X + 5 ≤ W) (hlen : H.length ≤ 64)
    (hwf : HostWF P.n H) (haW : c.nmem X + 3 * H.length + 4 ≤ W) (hs : C.s < C.P.n) :
    ∃ c' k, Exec P W pHead c c' k ∧ k ≤ 12 * H.length + 28 ∧ FrameB Bhead c c' ∧
      CEnv P W H C c' := by
  zubhc
  have hn : ztmd := by unfold hostWords at hW; omega
  have h3 := hG.1.1
  have hNlen : ztehu := by
    zujig
    show ((H.pts (Qof P).n).map _).length = _
    zudjs
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
        c₁.nreg 50053 = C.m ∧ c₁.nreg 50054 = C.topIdx ∧ c₁.nreg 50055 = c.nmem ztjns ∧
        c₁.nreg 50081 = 6 ∧ c₁.nreg 50082 = 2 ∧ c₁.nreg 50083 = 3 ∧ c₁.nreg 50084 = 4 ∧
        c₁.nreg 50085 = 5 ∧ c₁.nmem = c.nmem) := by
    exec_block
    all_goals try omega
    all_goals try (config_simp; omega)
    zubee
    config_simp
    simp_all
  obtain ⟨q32, q60, q52, q53, q54, q55, q81, q82, q83, q84, q85, qm⟩ := q
  zud
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, n63, E₂⟩ := cnt_exec (P := P) (n := P.n) c₁ w₁
    by_simp_all q60 haW by_omega
  zue
  have e₃ := Exec.copyN (P := P) w₂ 50087 50063
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 50087 _ } with hc₃
  have ex : Exec P W pHead c c₃ _ := .seq e₁ ztcr
  zubdn
  have r3 : ∀ r, r ≠ 50087 → c₃.nreg r = c₂.nreg r := by_simp_all
  have r3' : ∀ r, r ≠ 50087 → Bhost r = false → c₃.nreg r = c₁.nreg r := by_simp_all
  refine ⟨c₃, _, ex, by_omega, exec_frameB ex wr_pHead, ?_⟩
  have m₃ : ztckd := by zumwr; show c₂.nmem = c.nmem; zungj
  have h60 : c₃.nreg 50060 = c.nmem X := by rw [r3' _ by_decide by_decide, q60]
  refine ⟨⟨e₃.wb_right, rfl, by zunha; exact E₂.h61,
    by zunha; exact E₂.h67, by zunha; exact E₂.h68,
    by zunha; exact E₂.h69, rfl⟩, ?_, hwf, ?_, hNW, hP,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by_simp_all,
    by omega, hG, hn, hlen⟩
  · simp_all
  · omega
  · rw [r3' _ by_decide by_decide, q32]
  · rw [r3' _ by_decide by_decide, q52]
  · rw [r3' _ by_decide by_decide, q53]
  · rw [r3' _ by_decide by_decide, q54]
  · rw [r3' _ by_decide by_decide, q55]; omega
  · rw [r3' _ by_decide by_decide, q81]
  · rw [r3' _ by_decide by_decide, q82]
  · rw [r3' _ by_decide by_decide, q83]
  · rw [r3' _ by_decide by_decide, q84]
  · rw [r3' _ by_decide by_decide, q85]

/-! ## The walk vertices of the tour -/

/-- The tour position of step `i ≤ 2m` by one conditional subtraction. -/
theorem tour_idx {m S i : ℕ} (hm : 1 ≤ m) (hS : S ≤ 2 * m) (hi : i ≤ 2 * m) :
    sideE m ztwss = sideE m ztzyo := by
  zus
  · zuey
  · by_cases h2 : i - ztbru < 2 * m
    · zul
      grind
    · have e1 : i - ztbru = 2 * m := by_omega
      have e2 : S + i = 2 * m + 2 * m := by_omega
      rw [e1, e2, Nat.add_mod_right, Nat.mod_self]
      zumu

/-- **The chain vertex index of tour step `i`** (in `50120`) into `50091`. -/
def tvIdx : Stmt :=
  .seq (.instr (.addN 50058 50053 50053))
    (.seq (.ifLtN 50055 50032 zteju
        ztbkh)
      (.seq ztnbx
        (.seq (.ifLtN 50120 50089 ztnar
            ztnbu)
          (.ifLtN 50053 50077 ztnby ztovl))))

/-- The registers written by `tvIdx`. -/
def Btvi (r : ℕ) : Bool := [50058, 50059, 50089, 50077, 50091].contains r
theorem wr_tvIdx : wr Btvi tvIdx = true := by_decide

/-- **The chain vertex index of a tour step** (at most `16` steps). -/
theorem tvIdx_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {i : ℕ} (h120 : c.nreg 50120 = i) (hi : i ≤ 2 * C.m) :
    ∃ c' k, Exec P W tvIdx c c' k ∧ k ≤ 16 ∧ FrameB Btvi c c' ∧
      c'.nreg 50091 = C.sideIdx C.sideBeta i ∧ c'.nreg 50058 = 2 * C.m ∧
      c'.nreg 50059 = C.sideS C.sideBeta ∧ c'.nreg 50089 = 2 * C.m - C.sideS C.sideBeta ∧
      c'.nreg 50077 = (if i < 2 * C.m - C.sideS C.sideBeta then C.sideS C.sideBeta + i
        else i - (2 * C.m - C.sideS C.sideBeta)) := by
  zuyv
  zubb
  zubqu
  zuwi
  set m := C.m
  set T := C.topIdx
  zubad
  have hS2 : ztsck := C.sideS_lt _
  have h53 := hE.r53
  have h54 := hE.r54
  have h32 := hE.r32
  have e₁ := Exec.addN (P := P) hw 50058 50053 50053 (by zunrx; have := hE.NW; omega)
  zudkx
  zud
  have q58 : ztrgj := by rw [hc₁]; config_simp; omega
  have q : ztkot := by_simp_all
  obtain ⟨c₂, k₂, e₂, hk₂, q59, r₂⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 50055 50032
      zteju
      ztbkh)
      c₁ c₂ k₂ ∧ k₂ ≤ 5 ∧ c₂.nreg 50059 = S ∧ ∀ r, r ≠ 50059 → c₂.nreg r = c₁.nreg r := by
    zujwt
    have b54 : ztuqh := by_grind
    have hb := hE.r55
    have b55 : c₁.nreg 50055 = c.nreg 50055 := by_simp_all
    by_cases h0 : c.nreg 50055 < 1
    · have hβ : ztidl := by
        simp_all
      refine spec_ifLtN_true by_omega
        ztxct
      config_simp; rw [q58, b54, hSdef]; unfold Chain.sideS; grind
    · zubv
      by_cases h2 : 1 < c.nreg 50055
      · have hβ : ztidl := by
          grind
        refine spec_ifLtN_true by_omega
          ztxct
        config_simp; rw [q58, b54, hSdef]; unfold Chain.sideS; grind
      · zukhn
        refine spec_ifLtN_false by_omega
          ztywq
        config_simp; rw [b54, hSdef]; unfold Chain.sideS; simp_all
  zue
  zuepu
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 50089 _ }
    with hc₃
  zubj
  have t89 : ztoqx := by
    simp_all
  have t : ztkou := by_simp_all
  have t120 : c₃.nreg 50120 = i := by
    simp_all
  have t59 : ztuse := by_simp_all
  obtain ⟨c₄, k₄, e₄, hk₄, j4, r₄⟩ : ∃ c₄ k₄, Exec P W (.ifLtN 50120 50089
      ztnar ztnbu) c₃ c₄ k₄ ∧
      k₄ ≤ 3 ∧ c₄.nreg 50077 = ztwss ∧
      ∀ r, r ≠ 50077 → c₄.nreg r = c₃.nreg r := by
    zugjk
    · refine spec_ifLtN_true by_omega (spec_instr (Exec.addN w₃ _ _ _
        (by rw [t59, t120]; have := hE.NW; omega)) fun _ =>
          ⟨by_omega, ?_, by_simp_all⟩)
      simp_all
    · refine spec_ifLtN_false by_omega (spec_instr ztgdp
        fun _ => ztbfk)
      config_simp; grind
  zucc
  set j := ztwss with hj
  have u53 : ztusw := by
    grind
  have u58 : ztrgm := by
    grind
  obtain ⟨c₅, k₅, e₅, hk₅, k91, r₅⟩ : ∃ c₅ k₅, Exec P W (.ifLtN 50053 50077
      ztnby ztovl) c₄ c₅ k₅ ∧
      k₅ ≤ 3 ∧ c₅.nreg 50091 = sideE m j ∧ ∀ r, r ≠ 50091 → c₅.nreg r = c₄.nreg r := by
    zugxd

    · refine spec_ifLtN_true by_omega (spec_instr ztgdq
        fun _ => ztzw)
      config_simp; grind
    · refine spec_ifLtN_false by_omega (spec_instr ztlek
        fun _ => ztzw)
      config_simp; grind
  have ex : Exec P W tvIdx c c₅ _ :=
    .seq e₁ ztbq
  refine ⟨c₅, _, ex, by_omega, exec_frameB ex wr_tvIdx, ?_, by_grind,
    by grind, by_grind,
    by grind⟩
  rw [k91, hj, tour_idx hm1 hS2 hi, C.sideIdx_eq]

/-- **Load the walk vertex `6 + i`** (`i` in `50120`) into the slot `dst`. -/
def tvLoad (dst : ℕ) : Stmt :=
  .seq tvIdx ztdes

/-- The registers written by `tvLoad dst`. -/
def Btv (dst r : ℕ) : Bool := Btvi r || Bhost r || decide ztlnb
theorem wr_tvLoad (dst : ℕ) : wr ztuwy ztqxu = true := by
  have h1 := wr_mono wr_tvIdx (B' := Btv dst) ztjwj
  have h2 := wr_mono wr_hostPt (B' := Btv dst) ztjwj
  simp only [tvLoad, copies, List.map_cons, List.map_nil, block_cons, block_nil, wr, wrOK, h1,
    h2]
  simp [Btv]

/-- The walk vertex `6 + i` of the chain model is the chain vertex of tour step `i`. -/
theorem walk_vtx_tour (C : Chain) {i : ℕ} (hi : i ≤ 2 * C.m) :
    (chainModel C).W.vtx ztcy = C.vertex ztlx :=
  C.sideWalk_vtx_tour _ hi

/-- **Loading a walk vertex of the tour** (at most `27 |H| + 40` steps): the slot `dst` receives a
symbolic point in range whose point is the walk vertex `6 + i`. -/
theorem tvLoad_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {i : ℕ} (h120 : c.nreg 50120 = i) (hi : i ≤ 2 * C.m) {dst : ℕ}
    (hdst : 50100 ≤ dst) :
    ∃ c' k, Exec P W ztqxu c c' k ∧ k ≤ 27 * H.length + 40 ∧ FrameB ztuwy c c' ∧
      CEnv P W H C c' ∧ ∃ sp : SymPt, SymPtIn c' dst sp ∧ sp.Lt P.n ∧
        sp.eval zta = (chainModel C).W.vtx ztcy ∧
        ztbkj[ztema % (H.pts P.n).length]? = some sp := by
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, k91, -⟩ := tvIdx_exec c hE h120 hi
  have hE₁ := hE.frame f₁ e₁.wb_right by_decide
  zubqu
  have hk : C.sideIdx C.sideBeta i < (H.pts P.n).length :=
    lt_of_le_of_lt ztbdw hmN
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, E₂, sp, hsp, hin⟩ := hostPt_exec (P := P) c₁ hE₁.host hE₁.hH
    hE₁.wf (by have := hE₁.hW; omega) hE₁.aW hE₁.NW hE₁.r52 hE₁.r87 k91 hE₁.hs hk
  have hE₂ := hE₁.of_host E₂ f₂
  obtain ⟨c₃, e₃, h3, h3', _h3r, h3m, _h3rm, _h3o⟩ := copies_exec (P := P)
    [ztjud, ztgii, ztgij] c₂ e₂.wb_right
    by_grind
    by_simp
  have ex : Exec P W ztqxu c c₃ (k₁ + ztocj) := .seq e₁ ztcr
  refine ⟨c₃, _, ex, by_omega, exec_frameB ex (wr_tvLoad dst), ?_, sp, ?_, ?_, ?_, ?_⟩
  · zugaq
    zujs
    zuenm

  · exact symPtIn_copy hin ztzvy ztzvw
      ztzvx
  · zueoz
  · rw [walk_vtx_tour C hi, chain_vertex_host C hE.hP _]
    zudfz

  omega
open Chazelle.Chain (sideCcw sideCross sideDot sideLeft sideLeftOf)
def SecProp (sp oP oZ b2p b2n b1p b1n a2p a2n a1p a1n : Prop) : Prop :=
  (oP ∧ ztebo ∧ ztipf) ∨
  (¬ oP ∧ ¬ oZ ∧ (ztebo ∨ ztipf)) ∨
  (oZ ∧ ((b2p ∧ a2n) ∨ (b2n ∧ a2p) ∨ (b1p ∧ a1n) ∨ (b1n ∧ a1p)) ∧ ztebo) ∨
  (oZ ∧ ((b2p ∧ a2p) ∨ (b2n ∧ a2n) ∨ (b1p ∧ a1p) ∨ (b1n ∧ a1n)) ∧
    ((b2p ∨ b2n) ∨ ((sp ∧ b1n) ∨ (¬ sp ∧ b1p))))
variable {B A : Point}
/-- For parallel vectors the two coordinate products have the same weak sign. -/
theorem prod_nonneg_of_cross_zero (h : sideCross B A = 0) :
    0 ≤ ztsvf * ztsvi := by
  unfold sideCross at h
  have : ztsvf * ztsvi = ztsvg * ztsvg := by
    grind
  zvmwk; exact mul_self_nonneg _

/-- The sign of the dot product of parallel vectors, negative case. -/
theorem dot_neg_iff_of_cross_zero (h : sideCross B A = 0) :
    sideDot B A < 0 ↔ (ztndf ∨ ztnjm ∨ ztndd ∨
      ztnjk) := by
  zuiyt

  rw [show (ztndf ∨ ztnjm ∨ ztndd ∨
      ztnjk) ↔ (B.2 * A.2 < 0 ∨ B.1 * A.1 < 0) by
    rw [mul_neg_iff, mul_neg_iff]; tauto]
  constructor
  · grind
  · rintro (h2 | h2)
    · have : B.1 * A.1 ≤ 0 := by
        zubdj
      linarith
    · have : B.2 * A.2 ≤ 0 := by
        zubdj
      linarith

/-- The sign of the dot product of parallel vectors, positive case. -/
theorem dot_pos_iff_of_cross_zero (h : sideCross B A = 0) :
    0 < sideDot B A ↔ (ztnde ∨ ztnjn ∨ ztndc ∨
      ztnjl) := by
  zuiyt

  rw [show (ztnde ∨ ztnjn ∨ ztndc ∨
      ztnjl) ↔ (0 < B.2 * A.2 ∨ 0 < B.1 * A.1) by
    rw [mul_pos_iff, mul_pos_iff]; tauto]
  constructor
  · grind
  · zudst
    · have : 0 ≤ B.1 * A.1 := by
        simp_all
      linarith
    · have : 0 ≤ B.2 * A.2 := by
        simp_all
      linarith

/-- **The left sector test for a horizontal direction** as a Boolean function of sign bits. -/
theorem sideCcw_horiz_iff (B A : Point) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    sideCcw B (ztdwb : Point) A ↔
      SecProp zttzj (0 < sideCross B A) (sideCross B A = 0) (0 < B.2) (B.2 < 0) (0 < B.1)
        (B.1 < 0) (0 < A.2) (A.2 < 0) (0 < A.1) (A.1 < 0) := by
  have hneg : sideCross B A < 0 ↔ ¬ 0 < sideCross B A ∧ ¬ sideCross B A = 0 := by
    grind
  have hBXne : sideCross B (ztdwb : Point) ≠ 0 ↔ (0 < B.2 ∨ B.2 < 0) := by
    have e : sideCross B (ztdwb : Point) = -(s * B.2) := by unfold sideCross; ring
    grind
  unfold sideCcw SecProp
  rw [hneg, hBXne]
  zukmd
  · have hBX : 0 < sideCross B (ztcei : Point) ↔ B.2 < 0 := by
      zubag
    have hXA : 0 < sideCross (ztcei : Point) A ↔ 0 < A.2 := by
      zubag
    have hdBX : sideDot B (ztcei : Point) < 0 ↔ B.1 < 0 := by
      zumuq
    zuiip
    simp only [true_and, not_true_eq_false, false_and, or_false]
    zuhtm
    · zuhlb

    simp_all
  · have hBX : 0 < sideCross B (ztcyl : Point) ↔ 0 < B.2 := by
      zubag
    have hXA : 0 < sideCross (ztcyl : Point) A ↔ A.2 < 0 := by
      zubag
    have hdBX : sideDot B (ztcyl : Point) < 0 ↔ 0 < B.1 := by
      zumuq
    zuiip
    have hn : ¬ ((-1 : ℝ) = 1) := by_norm_num
    simp only [hn, false_and, false_or, not_false_eq_true, true_and]
    zuhtm
    · zuhlb

    simp_all

/-- **The left sector of a corner for a horizontal direction** in terms of the comparisons of
the neighbours `a`, `b` with the corner `v` and the orientation of `a, v, b`. -/
theorem sideLeftOf_horiz_iff (a v b : Point) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    sideLeftOf a v b (Visibility.rayPt v s 1) ↔
      SecProp zttzj ztigq ztpaq ztojq ztnrt ztojm
        ztnrs ztojp ztnqx ztojl ztnqv := by
  zucfg
  have hx : Visibility.rayPt v s 1 - v = (ztdwb : Point) := by
    refine Prod.ext ?_ ?_ <;> simp [Visibility.rayPt]
  rw [hx, sideCcw_horiz_iff _ _ hs, Chazelle.Chain.sideCross_corner]
  simp

/-- The sector formula as a Boolean formula over bit registers `r₀ … r₁₀` (in the order of the
arguments of `SecProp`). -/
def secBF (sp oP oZ b2p b2n b1p b1n a2p a2n a1p a1n : ℕ) : BF :=
  let v := BF.var
  let bx := BF.or (.and ztgms ztkgm) (.and ztzan ztkgn)
  let xa := BF.or (.and ztgms ztmpe) (.and ztzan ztmpd)
  let dn := BF.or (.or (.and ztkgn ztmpd) (.and ztkgm ztmpe))
    (.or (.and ztmpg ztqyb) (.and ztmpf ztqyc))
  let dp := BF.or (.or (.and ztkgn ztmpe) (.and ztkgm ztmpd))
    (.or (.and ztmpg ztqyc) (.and ztmpf ztqyb))
  let nz := BF.or ztkgn ztkgm
  let dbxn := BF.or (.and ztgms ztmpf) (.and ztzan ztmpg)
  .or (.or (.and ztqyd (.and bx xa)) (.and (.not ztqyd) (.and (.not ztmph) (.or bx xa))))
    (.or (.and ztmph (.and dn bx)) (.and ztmph (.and dp (.or nz dbxn))))

/-- The Boolean formula evaluates to the sector formula. -/
theorem secBF_eval (v : ℕ → Bool) (sp oP oZ b2p b2n b1p b1n a2p a2n a1p a1n : ℕ) :
    (secBF sp oP oZ b2p b2n b1p b1n a2p a2n a1p a1n).eval v = true ↔
      SecProp ztgms ztqyd ztmph ztkgn ztkgm ztmpg ztmpf ztmpe ztmpd ztqyc
        ztqyb := by
  simp only [secBF, BF.eval, SecProp, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    Bool.not_eq_true]
  grind

/-- The variables of the sector formula. -/
theorem secBF_vars {p : ℕ → Prop} {sp oP oZ b2p b2n b1p b1n a2p a2n a1p a1n : ℕ}
    (h : ∀ r ∈ [sp, oP, oZ, b2p, b2n, b1p, b1n, a2p, a2n, a1p, a1n], p r) :
    (secBF sp oP oZ b2p b2n b1p b1n a2p a2n a1p a1n).VarsOK p := by
  zvmwt at h
  zubtz
  trivial
end
end SweepPrim
end Chazelle.Core
section
set_option hygiene false
local macro "zqbce" : tactic => `(tactic| (have hd : ztixs := by_linarith
                                           set x := ((chainModel C).W.vtx _).1))
local macro "zqbcf" : tactic => `(tactic| (have hE₅ := hE₄.frame f₅ e₅.wb_right by_decide
                                           have hE₆ := hE₅.frame f₆ w₆ by_decide
                                           zuivw
                                           have hlen := hE.hlen))
local macro "zqbcg" : tactic => `(tactic| (have e₁ := Exec.subN (P := P) hE.wb 50120 50121 50032
                                           have hE₁ := hE.step e₁ by_decide))
local macro "zqbch" : tactic => `(tactic| (have e₃ := Exec.copyN (P := P) e₂.wb_right 50120 50121
                                           have hE₃ := hE₂.step e₃ by_decide))
local macro "zqbci" : tactic => `(tactic| refine spec_ifLtN_true by_simp_all (spec_skip w ⟨by_omega, ?_, ?_⟩))
set_option hygiene true

/-!
# Sweep RAM primitives (WP-D2), part 4: the left sector at a tour vertex on the RAM

`secAt` decides, for the vertex `6 + i` (`i ≤ 2m`, register `50121`) of the walk of the chain
model `chainModel C` and the direction code `σ` (register `50203`, `dirOf σ = ±1`), whether the
point `rayPt v (dirOf σ) 1` lies in the open left sector of the walk at the vertex
(`secAt_exec`); the answer bit goes to `50110`.

The neighbours of the vertex are tour vertices (`secGen`, `1 ≤ i < 2m`), or the top of the slit
(`secFirst`, `i = 0`, before the vertex; `secLast`, `i = 2m`, after it).  The top of the slit is
not a symbolic point; it lies straight above the vertex (the top of the chain), so its comparison
bits are constants and the orientation bits are comparison bits of the other neighbour.  The ten
sign bits and the direction bit are combined by the compiled formula `secBF`
(`SweepPrimBool`, `SweepPrimSec`).

Registers: slots `50130` (before), `50133` (vertex), `50136` (after); bits `50140 … 50150`
(direction, the four comparison bits of the next vertex, of the previous vertex, orientation);
the formula at `50300 …`.
-/
namespace Chazelle.Core
namespace SweepPrim
open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open Chazelle.Chain (sideCcw sideCross sideDot sideLeft sideLeftOf)
@[expose] public section
def BitIs (c : Config) (r : ℕ) (p : Prop) : Prop := c.nreg r ≤ 1 ∧ (c.nreg r = 1 ↔ p)
theorem BitIs.of_eq {c c' : Config} {r r' : ℕ} {p : Prop} (h : BitIs c r p)
    (he : c'.nreg r' = c.nreg r) : BitIs c' r' p := by
  unfold BitIs at *; simp_all
variable {c : Config} {r : ℕ} {P : Polygon} {W : ℕ} {B : ℕ → Bool} {H : Host} {C : Chain} (σ : ℕ)
theorem BitIs.congr {p q : Prop} (h : BitIs c r p) (hpq : p ↔ q) :
    BitIs c r q := by_simp_all
theorem BitIs.dec {p : Prop} (h : BitIs c r p) :
    decide ztdmw = true ↔ p := by rw [decide_eq_true_iff]; exact h.2
theorem BitIs.const_one {p : Prop} (h : c.nreg r = 1) (hp : p) :
    BitIs c r p := ⟨by_omega, by_simp_all, by_omega⟩
theorem BitIs.const_zero {p : Prop} (h : c.nreg r = 0) (hp : ¬ p) :
    BitIs c r p := ⟨by_omega, by_simp_all, by_simp_all⟩
theorem bk_false (h : 10500 ≤ r) : Bk r = false := by
  simp only [Bk, decide_eq_false_iff_not, not_and, not_lt]; omega

/-! ## Four comparison bits -/

/-- The four comparison bits of the point of slot `x` with the point of slot `v`: heights
`v < x`, `x < v`, abscissae `v < x`, `x < v`, into `base … base + 3`. -/
def cmp4 (v x base : ℕ) : Stmt :=
  .seq (kbit v x v 1 base) (.seq (kbit x v x 1 ztfpf)
    (.seq (kbit v x v 0 ztdtw) (kbit x v x 0 zttgn)))

/-- The registers written by `cmp4 _ _ base`. -/
def B4 (base r : ℕ) : Bool := Bk r || decide (base ≤ r ∧ r < base + 4)
theorem wr_cmp4 (v x base : ℕ) : wr ztuwm ztlmb = true := by
  have h := fun (a b d op dst : ℕ) (hd : base ≤ dst ∧ dst < base + 4) =>
    wr_mono ztpeo (B' := B4 base) (fun r hr => by
      simp only [Bkb, Bool.or_eq_true, beq_iff_eq] at hr
      simp only [B4, Bool.or_eq_true, decide_eq_true_eq]
      grind)
  simp only [cmp4, wr, h _ _ _ _ _ (by omega : base ≤ base ∧ base < base + 4),
    h _ _ _ _ _ (by omega : base ≤ base + 1 ∧ base + 1 < base + 4),
    h _ _ _ _ _ (by omega : base ≤ base + 2 ∧ base + 2 < base + 4),
    h _ _ _ _ _ (by omega : base ≤ base + 3 ∧ base + 3 < base + 4), Bool.and_self]

/-- The height of a symbolic point of `Qof P`. -/
noncomputable abbrev Ys (P : Polygon) (s : SymPt) : ℝ := (s.eval zta).2
/-- The abscissa of a symbolic point of `Qof P`. -/
noncomputable abbrev Xs (P : Polygon) (s : SymPt) : ℝ := (s.eval zta).1

/-- **Four comparison bits** (at most `964` steps). -/
theorem cmp4_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) {v x base : ℕ} (hv : 10500 ≤ v) (hx : 10500 ≤ x)
    (hvb : v + 3 ≤ base) (hxb : x + 3 ≤ base) {sv sx : SymPt} (hlv : sv.Lt P.n)
    (hlx : sx.Lt P.n) (hsv : SymPtIn c v sv) (hsx : SymPtIn c x sx) :
    ∃ c' k, Exec P W ztlmb c c' k ∧ k ≤ 964 ∧ FrameB ztuwm c c' ∧
      BitIs c' base (Ys P sv < Ys P sx) ∧ BitIs c' ztfpf (Ys P sx < Ys P sv) ∧
      BitIs c' ztdtw (Xs P sv < Xs P sx) ∧ BitIs c' zttgn (Xs P sx < Xs P sv) := by
  have keep : ∀ {c₁ c₂ : Config} {dst : ℕ}, FrameB ztdks c₁ c₂ → base ≤ dst →
      ∀ {r : ℕ} {s : SymPt}, 10500 ≤ r → r + 3 ≤ base → SymPtIn c₁ r s → SymPtIn c₂ r s :=
    fun hf hd r s hr hrb hs => symPtIn_of_eq hs fun j h1 h2 => hf.1 j (by
      simp only [Bkb, bk_false (show 10500 ≤ j by omega), Bool.false_or, beq_eq_false_iff_ne]
      omega)
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, t₁⟩ := kbit_exec (op := 1) (dst := base) hG hW c hw hv hx hv by_omega by_norm_num
    hlv hlx hlv hsv hsx hsv
  have sv₁ := keep f₁ le_rfl hv hvb hsv
  have sx₁ := keep f₁ le_rfl hx hxb hsx
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, b₂, t₂⟩ := kbit_exec (op := 1) (dst := base + 1) hG hW c₁ e₁.wb_right hx hv hx by_omega
    by_norm_num hlx hlv hlx sx₁ sv₁ sx₁
  have sv₂ := keep f₂ by_omega hv hvb sv₁
  have sx₂ := keep f₂ by_omega hx hxb sx₁
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, b₃, t₃⟩ := kbit_exec (op := 0) (dst := base + 2) hG hW c₂ e₂.wb_right hv hx hv by_omega
    by_norm_num hlv hlx hlv sv₂ sx₂ sv₂
  have sv₃ := keep f₃ by_omega hv hvb sv₂
  have sx₃ := keep f₃ by_omega hx hxb sx₂
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, b₄, t₄⟩ := kbit_exec (op := 0) (dst := base + 3) hG hW c₃ e₃.wb_right hx hv hx by_omega
    by_norm_num hlx hlv hlx sx₃ sv₃ sx₃
  have ex : Exec P W ztlmb c c₄ _ :=
    .seq e₁ ztcb
  have kp : ∀ {c₁ c₂ : Config} {dst : ℕ}, FrameB ztdks c₁ c₂ → ∀ {r : ℕ}, 10500 ≤ r →
      r ≠ dst → c₂.nreg r = c₁.nreg r := fun hf r hr hne => hf.1 r (by
        simp only [Bkb, bk_false hr, Bool.false_or, beq_eq_false_iff_ne]; omega)
  refine ⟨c₄, _, ex, by_omega, exec_frameB ex (wr_cmp4 v x base), ?_, ?_, ?_, ⟨b₄, t₄⟩⟩
  · refine BitIs.of_eq ⟨b₁, t₁⟩ ?_
    grind
  · refine BitIs.of_eq ⟨b₂, t₂⟩ ?_
    rw [kp f₄ by_omega by_omega, kp f₃ by_omega by_omega]
  · exact BitIs.of_eq ⟨b₃, t₃⟩ by_grind

/-! ## Frames and preservation -/
theorem symPtIn_keep {c c' : Config} {r : ℕ} {s : SymPt} (hs : SymPtIn c r s)
    (hf : FrameB B c c') (hB : ∀ j, r ≤ j → j < r + 3 → B j = false) : SymPtIn c' r s :=
  symPtIn_of_eq hs fun j h1 h2 => hf.1 j by_simp_all
theorem BitIs.keep {c c' : Config} {r : ℕ} {p : Prop} (h : BitIs c r p)
    (hf : FrameB B c c') (hB : B r = false) : BitIs c' r p := h.of_eq (hf.1 r hB)

/-- The registers the sector procedure may write. -/
def Bsec (r : ℕ) : Bool :=
  Bk r || Bhost r || Btvi r || decide (50100 ≤ r ∧ r < 50200 ∧ r ≠ 50121) ||
    decide (50300 ≤ r ∧ r < 51000)

/-- **The ten sign bits of a corner** `a → v → b` in `50141 … 50150`. -/
def BitsOK (c : Config) (a v b : Point) : Prop :=
  BitIs c 50141 ztojq ∧ BitIs c 50142 ztnrt ∧ BitIs c 50143 ztojm ∧
    BitIs c 50144 ztnrs ∧ BitIs c 50145 ztojp ∧ BitIs c 50146 ztnqx ∧
    BitIs c 50147 ztojl ∧ BitIs c 50148 ztnqv ∧ BitIs c 50149 ztigq ∧
    BitIs c 50150 ztpaq

/-- One index instruction keeps the environment. -/
theorem CEnv.step {c : Config} (hE : CEnv P W H C c)
    {i : Instr} {c' : Config} (e : Exec P W ztbgj c c' 1)
    (hi : wr (fun r => r == 50120) ztbgj = true) : CEnv P W H C c' :=
  hE.frame (exec_frameB e hi) e.wb_right by_decide

/-! ## The general corner -/

/-- Three tour vertices `i - 1, i, i + 1` and their ten sign bits. -/
def secGen : Stmt :=
  .seq ztnbz (.seq ztkgf
    (.seq ztigj (.seq ztibk
      (.seq ztnau (.seq ztkgg
        (.seq ztrnn (.seq ztrnm
          (.seq (kbit 50130 50133 50136 2 50149) (kbit 50130 50133 50136 3 50150)))))))))
theorem wr_secGen : wr Bsec secGen = true := by_decide

/-- **The ten bits at an inner tour vertex** (`1 ≤ i < 2m`). -/
theorem secGen_exec (c : Config)
    (hE : CEnv P W H C c) {i : ℕ} (h121 : c.nreg 50121 = i) (hi1 : 1 ≤ i) (hi : i < 2 * C.m) :
    ∃ c' k, Exec P W secGen c c' k ∧ k ≤ 81 * H.length + 2600 ∧ FrameB Bsec c c' ∧
      CEnv P W H C c' ∧ BitsOK c' ((chainModel C).W.vtx ztzzk)
        ztwof ((chainModel C).W.vtx ztxyx) := by
  zucvu
  zuol
  -- previous vertex
  zqbcg
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, sa, ia, la, va, -⟩ := tvLoad_exec _ hE₁
    (i := i - 1) ztnut by_omega (dst := 50130) by_norm_num
  have r121₂ : c₂.nreg 50121 = i := by zunqx; simp_all
  -- the vertex
  zqbch
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, hE₄, sv, iv, lv, vv, -⟩ := tvLoad_exec _ hE₃
    (i := i) by_simp_all by_omega (dst := 50133) by_norm_num
  have ia₄ := symPtIn_keep (symPtIn_of_eq ia fun j h1 h2 => by
    zvmwf; grind) f₄ by_decide
  have r121₄ : c₄.nreg 50121 = i := by rw [f₄.1 _ by_decide]; simp_all
  -- the next vertex
  have e₅ := Exec.addN (P := P) e₄.wb_right 50120 50121 50032
    (by rw [r121₄, hE₄.r32]; have := hE₄.NW; have := C.m_lt; have := hE₄.n_eq; omega)
  zujze
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, hE₆, sb, ib, lb, vb, -⟩ := tvLoad_exec _ hE₅
    (i := i + 1) (by simp [r121₄, hE₄.r32]) by_omega (dst := 50136) by_norm_num
  have ia₆ := symPtIn_keep (symPtIn_of_eq ia₄ fun j h1 h2 => by
    zvmwf; grind) f₆ by_decide
  have iv₆ := symPtIn_keep (symPtIn_of_eq iv fun j h1 h2 => by
    zvmwf; grind) f₆ by_decide
  -- the bits
  obtain ⟨c₇, k₇, e₇, hk₇, f₇, b1, b2, b3, b4⟩ := cmp4_exec (base := 50141) hG hW c₆
    e₆.wb_right by_norm_num by_norm_num by_norm_num by_norm_num lv lb iv₆ ib
  have ia₇ := symPtIn_keep ia₆ f₇ by_decide
  have iv₇ := symPtIn_keep iv₆ f₇ by_decide
  have ib₇ := symPtIn_keep ib f₇ by_decide
  obtain ⟨c₈, k₈, e₈, hk₈, f₈, b5, b6, b7, b8⟩ := cmp4_exec (base := 50145) hG hW c₇
    e₇.wb_right by_norm_num by_norm_num by_norm_num by_norm_num lv la iv₇ ia₇
  have ia₈ := symPtIn_keep ia₇ f₈ by_decide
  zujaa
  have ib₈ := symPtIn_keep ib₇ f₈ by_decide
  obtain ⟨c₉, k₉, e₉, hk₉, f₉, b9, t9⟩ := kbit_exec (op := 2) (dst := 50149) hG hW c₈
    e₈.wb_right by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num la lv lb
    ia₈ iv₈ ib₈
  have ia₉ := symPtIn_keep ia₈ f₉ by_decide
  have iv₉ := symPtIn_keep iv₈ f₉ by_decide
  have ib₉ := symPtIn_keep ib₈ f₉ by_decide
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, f₁₀, b10, t10⟩ := kbit_exec (op := 3) (dst := 50150) hG hW c₉
    e₉.wb_right by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num la lv lb
    ia₉ iv₉ ib₉
  have ex : Exec P W secGen c c₁₀
      _ :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ ztncr))))))
  zuivw
  have hE₈ := hE₇.frame f₈ e₈.wb_right by_decide
  have hE₉ := hE₈.frame f₉ e₉.wb_right by_decide
  have hE₁₀ := hE₉.frame f₁₀ e₁₀.wb_right by_decide
  zubgf
  refine ⟨c₁₀, _, ex, by_omega, exec_frameB ex wr_secGen, hE₁₀, ?_⟩
  simp only [Ys, Xs, va, vv, vb] at b1 b2 b3 b4 b5 b6 b7 b8
  have t9' := t9; have t10' := t10
  simp only [SignTest, va, vv, vb] at t9' t10'
  refine ⟨((b1.keep f₈ by_decide).keep f₉ by_decide).keep f₁₀ by_decide,
    ((b2.keep f₈ by_decide).keep f₉ by_decide).keep f₁₀ by_decide,
    ((b3.keep f₈ by_decide).keep f₉ by_decide).keep f₁₀ by_decide,
    ((b4.keep f₈ by_decide).keep f₉ by_decide).keep f₁₀ by_decide,
    (b5.keep f₉ by_decide).keep f₁₀ by_decide, (b6.keep f₉ by_decide).keep f₁₀ by_decide,
    (b7.keep f₉ by_decide).keep f₁₀ by_decide, (b8.keep f₉ by_decide).keep f₁₀ by_decide,
    BitIs.keep ⟨b9, t9'⟩ f₁₀ by_decide, ⟨b10, t10'⟩⟩

/-! ## The corners at the top of the chain -/
theorem BitIs.of_bf {f : BF} {v : ℕ → Bool} {p : Prop}
    (h : c.nreg r = (f.eval v).toNat) (hv : f.eval v = true ↔ p) : BitIs c r p := by
  zuevy
  simp_all

/-- The orientation at the first top corner (`slitTop → top → b`). -/
theorem det_slitTop_first (C : Chain) (b : Point) :
    det C.slitTop C.top b = ztox * (b.1 - C.top.1) := by
  zuhpo

/-- The orientation at the last top corner (`a → top → slitTop`). -/
theorem det_slitTop_last (C : Chain) (a : Point) :
    det a C.top C.slitTop = ztox * (C.top.1 - a.1) := by
  zuhpo
theorem walk_vtx_six (C : Chain) : (chainModel C).W.vtx 6 = C.top := C.sideWalk_vtx_six _
theorem walk_vtx_last (C : Chain) : (chainModel C).W.vtx ztcc = C.top := by
  rw [walk_vtx_tour C le_rfl, ← Chain.sideTour, C.sideTour_two_m]

/-- The tour vertices `0` (the top) and `1`, the slit top before them. -/
def secFirst : Stmt :=
  .seq ztigj (.seq ztibk
    (.seq ztnau (.seq ztkgg
      (.seq ztrnn
        (.seq (block [.constN 50145 1, .constN 50146 0, .constN 50147 0, .constN 50148 0,
            .copyN 50149 50143])
          ((BF.and ztjdo ztjdp).compile 50150))))))
theorem wr_secFirst : wr Bsec secFirst = true := by_decide

/-- **The ten bits at the first visit of the top** (`i = 0`). -/
theorem secFirst_exec (c : Config)
    (hE : CEnv P W H C c) (h121 : c.nreg 50121 = 0) :
    ∃ c' k, Exec P W secFirst c c' k ∧ k ≤ 54 * H.length + 1100 ∧ FrameB Bsec c c' ∧
      CEnv P W H C c' ∧ BitsOK c' C.slitTop C.top ((chainModel C).W.vtx ztjec) := by
  zucvu
  zuol
  zubb
  have e₁ := Exec.copyN (P := P) hE.wb 50120 50121
  zumz
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, sv, iv, lv, vv, -⟩ := tvLoad_exec _ hE₁
    (i := 0) by_simp_all by_omega (dst := 50133) by_norm_num
  have r121₂ : c₂.nreg 50121 = 0 := by zunqx; simp_all
  have e₃ := Exec.addN (P := P) e₂.wb_right 50120 50121 50032
    (by rw [r121₂, hE₂.r32]; omega)
  zucls
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, hE₄, sb, ib, lb, vb, -⟩ := tvLoad_exec _ hE₃
    (i := 1) (by simp [r121₂, hE₂.r32]) by_omega (dst := 50136) by_norm_num
  have iv₄ := symPtIn_keep (symPtIn_of_eq iv fun j h1 h2 => by
    zvmwf; grind) f₄ by_decide
  obtain ⟨c₅, k₅, e₅, hk₅, f₅, b1, b2, b3, b4⟩ := cmp4_exec (base := 50141) hG hW c₄
    e₄.wb_right by_norm_num by_norm_num by_norm_num by_norm_num lv lb iv₄ ib
  zuef
  obtain ⟨c₆, k₆, e₆, hk₆, q⟩ : ∃ c₆ k₆, Exec P W (block [.constN 50145 1, .constN 50146 0,
      .constN 50147 0, .constN 50148 0, .copyN 50149 50143]) c₅ c₆ k₆ ∧ k₆ = 5 ∧
      (c₆.nreg 50145 = 1 ∧ c₆.nreg 50146 = 0 ∧ c₆.nreg 50147 = 0 ∧ c₆.nreg 50148 = 0 ∧
        c₆.nreg 50149 = c₅.nreg 50143 ∧
        ∀ r, r ≠ 50145 → r ≠ 50146 → r ≠ 50147 → r ≠ 50148 → r ≠ 50149 →
          c₆.nreg r = c₅.nreg r) := by
    exec_block
    all_goals try omega
    simp_all
  obtain ⟨q45, q46, q47, q48, q49, qr⟩ := q
  zujb
  have f₆ := exec_frameB e₆ (B := fun r => decide (50145 ≤ r ∧ r < 50150)) by_decide
  obtain ⟨c₇, k₇, e₇, hk₇, v₇, f₇⟩ := BF.compile_exec (P := P) by_omega
    (BF.and ztjdo ztjdp) 50150 c₆ w₆
    (by zuoti; refine ztbabn
        · zunaj; exact b3.1
        · zunaj; exact b4.1)
  have ex : Exec P W secFirst c c₇ _ :=
    .seq e₁ ztfc
  zqbcf
  have hsz : (BF.and ztjdo ztjdp).size = 5 := rfl
  refine ⟨c₇, _, ex, by_omega, exec_frameB ex wr_secFirst, hE₇, ?_⟩
  have v6 := walk_vtx_six C
  simp only [Ys, Xs, vv, v6, vb] at b1 b2 b3 b4
  zueqq
  have k₆₇ := fun r hr =>
    f₇.1 r ztcev
  have k₅₇ : ∀ r, r < 50145 → c₇.nreg r = c₅.nreg r := fun r hr => by
    grind
  have hb3 := b3.dec
  have hb4 := b4.dec
  refine ⟨b1.of_eq by_simp_all, b2.of_eq by_simp_all,
    b3.of_eq by_simp_all, b4.of_eq by_simp_all, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BitIs.const_one by_simp_all ztmef
  · exact BitIs.const_zero by_simp_all
      ztmeg
  · zulwu
  · zulwu
  · refine (b3.of_eq by_simp_all).congr ?_
    rw [det_slitTop_first]
    zqbce
    constructor
    · zumgr
    · zugoc
      have : ztox * (x - C.top.1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hd.le by_linarith
      linarith
  · zuevt

    rw [det_slitTop_first]
    zqbce
    have e3 : (decide (c₆.nreg 50143 = 1)) = false ↔ ¬ ztswd := by
      grind
    have e4 : (decide (c₆.nreg 50144 = 1)) = false ↔ ¬ ztudw := by
      grind
    rw [e3, e4]
    constructor
    · grind
    · zuq
      zujeq
      · linarith
      grind

/-- The tour vertices `2m - 1` and `2m` (the top), the slit top after them. -/
def secLast : Stmt :=
  .seq ztnbz (.seq ztkgf
    (.seq ztigj (.seq ztibk
      (.seq ztrnm
        (.seq (block [.constN 50141 1, .constN 50142 0, .constN 50143 0, .constN 50144 0,
            .copyN 50149 50148])
          ((BF.and ztjdq ztjdr).compile 50150))))))
theorem wr_secLast : wr Bsec secLast = true := by_decide

/-- **The ten bits at the last visit of the top** (`i = 2m`). -/
theorem secLast_exec (c : Config)
    (hE : CEnv P W H C c) (h121 : c.nreg 50121 = 2 * C.m) :
    ∃ c' k, Exec P W secLast c c' k ∧ k ≤ 54 * H.length + 1100 ∧ FrameB Bsec c c' ∧
      CEnv P W H C c' ∧ BitsOK c' ((chainModel C).W.vtx ztysq) C.top C.slitTop := by
  zucvu
  zuol
  zubb
  zqbcg
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, sa, ia, la, va, -⟩ := tvLoad_exec _ hE₁
    (i := 2 * C.m - 1) ztnut by_omega (dst := 50130) by_norm_num
  have r121₂ : c₂.nreg 50121 = 2 * C.m := by zunqx; simp_all
  zqbch
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, hE₄, sv, iv, lv, vv, -⟩ := tvLoad_exec _ hE₃
    (i := 2 * C.m) by_simp_all le_rfl (dst := 50133) by_norm_num
  have ia₄ := symPtIn_keep (symPtIn_of_eq ia fun j h1 h2 => by
    zvmwf; grind) f₄ by_decide
  obtain ⟨c₅, k₅, e₅, hk₅, f₅, b5, b6, b7, b8⟩ := cmp4_exec (base := 50145) hG hW c₄
    e₄.wb_right by_norm_num by_norm_num by_norm_num by_norm_num lv la iv ia₄
  zuef
  obtain ⟨c₆, k₆, e₆, hk₆, q⟩ : ∃ c₆ k₆, Exec P W (block [.constN 50141 1, .constN 50142 0,
      .constN 50143 0, .constN 50144 0, .copyN 50149 50148]) c₅ c₆ k₆ ∧ k₆ = 5 ∧
      (c₆.nreg 50141 = 1 ∧ c₆.nreg 50142 = 0 ∧ c₆.nreg 50143 = 0 ∧ c₆.nreg 50144 = 0 ∧
        c₆.nreg 50149 = c₅.nreg 50148 ∧
        ∀ r, r ≠ 50141 → r ≠ 50142 → r ≠ 50143 → r ≠ 50144 → r ≠ 50149 →
          c₆.nreg r = c₅.nreg r) := by
    exec_block
    all_goals try omega
    simp_all
  obtain ⟨q41, q42, q43, q44, q49, qr⟩ := q
  zujb
  have f₆ := exec_frameB e₆ (B := fun r => decide (50141 ≤ r ∧ r < 50150)) by_decide
  obtain ⟨c₇, k₇, e₇, hk₇, v₇, f₇⟩ := BF.compile_exec (P := P) by_omega
    (BF.and ztjdq ztjdr) 50150 c₆ w₆
    (by zuoti; refine ztbabn
        · zunaj; exact b7.1
        · zunaj; exact b8.1)
  have ex : Exec P W secLast c c₇ _ :=
    .seq e₁ ztfc
  zqbcf
  have hsz : (BF.and ztjdq ztjdr).size = 5 := rfl
  refine ⟨c₇, _, ex, by_omega, exec_frameB ex wr_secLast, hE₇, ?_⟩
  have vl : (chainModel C).W.vtx _ = C.top := walk_vtx_last C
  simp only [Ys, Xs, vv, vl, va] at b5 b6 b7 b8
  zueqq
  have k₆₇ := fun r hr =>
    f₇.1 r ztcev
  have hb7 := b7.dec
  have hb8 := b8.dec
  refine ⟨?_, ?_, ?_, ?_, b5.of_eq by_grind, b6.of_eq by_grind, b7.of_eq by_grind, b8.of_eq (by
    grind),
    ?_, ?_⟩
  · exact BitIs.const_one by_grind ztmef
  · exact BitIs.const_zero by_grind
      ztmeg
  · zulws
  · zulws
  · refine (b8.of_eq by_grind).congr ?_
    rw [det_slitTop_last]
    zqbce
    constructor
    · zumgr
    · zugoc
      have : ztox * (C.top.1 - x) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hd.le by_linarith
      linarith
  · zuevt

    rw [det_slitTop_last]
    zqbce
    have e7 : (decide (c₆.nreg 50147 = 1)) = false ↔ ¬ ztswd := by
      grind
    have e8 : (decide (c₆.nreg 50148 = 1)) = false ↔ ¬ ztudw := by
      grind
    rw [e7, e8]
    constructor
    · grind
    · zuq
      zujeq
      · linarith
      grind

/-! ## The sector procedure -/
theorem SecProp_congr {sp oP oZ b2p b2n b1p b1n a2p a2n a1p a1n sp' oP' oZ' b2p' b2n' b1p' b1n'
    a2p' a2n' a1p' a1n' : Prop} (h1 : sp ↔ sp') (h2 : oP ↔ oP') (h3 : oZ ↔ oZ') (h4 : b2p ↔ b2p')
    (h5 : b2n ↔ b2n') (h6 : b1p ↔ b1p') (h7 : b1n ↔ b1n') (h8 : a2p ↔ a2p') (h9 : a2n ↔ a2n')
    (h10 : a1p ↔ a1p') (h11 : a1n ↔ a1n') :
    SecProp sp oP oZ b2p b2n b1p b1n a2p a2n a1p a1n ↔
      SecProp sp' oP' oZ' b2p' b2n' b1p' b1n' a2p' a2n' a1p' a1n' := by
  simp_all

/-- The direction bit: `50140 := [σ = 1]`. -/
def spBit : Stmt :=
  .seq ztify
    (.ifLtN 50203 50032 .skip (.ifLtN 50032 50203 .skip (.instr (.constN 50140 1))))

/-- The sector formula over the bit registers. -/
def secF : BF := secBF 50140 50149 50150 50141 50142 50143 50144 50145 50146 50147 50148

/-- **The left sector at the tour vertex `6 + i`** (`i` in `50121`, direction code in `50203`;
answer bit in `50110`). -/
def secAt : Stmt :=
  .seq (.instr (.addN 50123 50053 50053))
    (.seq ztjdc
      (.seq spBit (.seq (secF.compile 50300) (.instr (.copyN 50110 50300)))))
theorem wr_secAt : wr Bsec secAt = true := by_decide

/-- The neighbours of the tour vertex `6 + i` on the walk. -/
theorem sideLeft_tour_iff (C : Chain) {i : ℕ} (hi : i ≤ 2 * C.m) (x : Point) :
    sideLeft (chainModel C).W ztcy 0 x ↔
      sideLeftOf (if i = 0 then C.slitTop else (chainModel C).W.vtx ztzzk)
        ztwof
        (if i = 2 * C.m then C.slitTop else (chainModel C).W.vtx ztxyx) x := by
  zubt
  zugtq
  zucn
  zufqt
  · zubvi
    rw [ite_eq_left rfl, ite_eq_right by_omega, hW, C.sideWalk_prev_six, C.sideWalk_next_tour _ by_omega,
      C.sideWalk_vtx_five]
  · zucqa
    by_cases h2 : i = 2 * C.m
    · rw [ite_eq_left h2, hW, C.sideWalk_prev_tour _ by_omega hi]
      zuhqi
      rw [C.sideWalk_next_last, C.sideWalk_vtx_zero]
    · rw [ite_eq_right h2, hW, C.sideWalk_prev_tour _ by_omega hi, C.sideWalk_next_tour _ by_omega]
theorem dirOf_cases : dirOf σ = 1 ∨ dirOf σ = -1 := by
  zubqi
theorem dirOf_eq_one_iff : dirOf σ = 1 ↔ σ = 1 := by
  zubqi

/-- **The left sector at a tour vertex** (at most `81 |H| + 3200` steps): the answer bit is the
truth of `rayPt v (dirOf σ) 1 ∈` the open left sector of the walk at the vertex `v = 6 + i`. -/
theorem secAt_exec (c : Config)
    (hE : CEnv P W H C c) {i : ℕ} (h121 : c.nreg 50121 = i) (hi : i ≤ 2 * C.m) :
    ∃ c' k, Exec P W secAt c c' k ∧ k ≤ 81 * H.length + 3200 ∧ FrameB Bsec c c' ∧
      CEnv P W H C c' ∧ BitIs c' 50110 (sideLeft (chainModel C).W ztcy 0
        (Visibility.rayPt ztwof ztzek 1)) := by
  zubb
  zubgf
  zuol
  set σ := c.nreg 50203 with hσ
  have e₁ := Exec.addN (P := P) hE.wb 50123 50053 50053
    (by zunkz; have := hE.NW; have := C.m_lt; have := hE.n_eq; omega)
  set c₁ : Config := { c with nreg := upd c.nreg 50123 _ } with hc₁
  have hE₁ := hE.frame (exec_frameB e₁ (B := fun r => r == 50123)
    by_decide) e₁.wb_right by_decide
  have q121 : ztuqi := by_simp_all
  have q123 : c₁.nreg 50123 = 2 * C.m := by zvmxj; simp [hE.r53]; ring
  have q32 := hE₁.r32
  -- the ten bits
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, a, b, hab, hbits⟩ : ∃ c₂ k₂, Exec P W
      ztjdc c₁ c₂ k₂ ∧
      k₂ ≤ 81 * H.length + 2610 ∧ FrameB Bsec c₁ c₂ ∧ CEnv P W H C c₂ ∧
      ∃ a b : Point, (∀ x, sideLeft (chainModel C).W ztcy 0 x ↔
        sideLeftOf a ztwof b x) ∧
        BitsOK c₂ a ztwof b := by
    zufqt
    · zubvi
      obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, hb⟩ := secFirst_exec c₁ hE₁ q121
      refine ⟨c₂, _, .ifLtN_true by_omega e₂, by_omega, f₂, hE₂, C.slitTop,
        (chainModel C).W.vtx ztjec, fun x => ?_, by rw [walk_vtx_six]; exact hb⟩
      rw [sideLeft_tour_iff C by_omega, ite_eq_left rfl, ite_eq_right by_omega]
    · by_cases h2 : i < 2 * C.m
      · obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, hb⟩ := secGen_exec c₁ hE₁ q121 by_omega h2
        refine ⟨c₂, _, .ifLtN_false by_omega
          ztbxn, by_omega, f₂, hE₂, _, _,
          fun x => ?_, hb⟩
        rw [sideLeft_tour_iff C hi, ite_eq_right h0, ite_eq_right by_omega]
      · have hi2 : i = 2 * C.m := by_omega
        obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, hb⟩ := secLast_exec c₁ hE₁ by_omega
        refine ⟨c₂, _, .ifLtN_false by_omega
          ztcry, by_omega, f₂, hE₂,
          (chainModel C).W.vtx ztysq, C.slitTop, fun x => ?_,
          by rw [hi2, walk_vtx_last]; exact hb⟩
        rw [sideLeft_tour_iff C hi, ite_eq_right h0, ite_eq_left hi2]
        simp_all
  zue
  have s₂ : c₂.nreg 50203 = σ := by
    rw [f₂.1 _ by_decide, hc₁]; rfl
  have p₂ := hE₂.r32
  -- the direction bit
  obtain ⟨c₃, k₃, e₃, hk₃, b₃, r₃⟩ : ∃ c₃ k₃, Exec P W spBit c₂ c₃ k₃ ∧ k₃ ≤ 6 ∧
      BitIs c₃ 50140 (σ = 1) ∧ ∀ r, r ≠ 50140 → c₃.nreg r = c₂.nreg r := by
    have e := Exec.constN (P := P) w₂ 50140 0 by_omega
    have w := e.wb_right
    unfold spBit
    refine spec_seq ⟨_, 1, e, ?_⟩
    by_cases hl : σ < 1
    · zqbci
      · zulwt
      simp_all
    · zudx
      by_cases hg : 1 < σ
      · zqbci
        · zulwt
        simp_all
      · refine spec_ifLtN_false by_simp_all
          (spec_instr (Exec.constN w _ _ by_omega) fun _ => ztss)
        · exact BitIs.const_one by_simp by_omega
        simp_all
  zubj
  obtain ⟨h41, h42, h43, h44, h45, h46, h47, h48, h49, h50⟩ := hbits
  have k3 : ∀ {r : ℕ} {p : Prop}, r ≠ 50140 → BitIs c₂ r p → BitIs c₃ r p :=
    fun hr h => h.of_eq by_simp_all
  -- the formula
  obtain ⟨c₄, k₄, e₄, hk₄, v₄, f₄⟩ := BF.compile_exec (P := P) by_omega secF
    50300 c₃ w₃ (secBF_vars (by
      zuz
      zuvy
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨by_norm_num, b₃.1⟩
      · exact ⟨by_norm_num, (k3 by_norm_num h49).1⟩
      · exact ⟨by_norm_num, (k3 by_norm_num h50).1⟩
      · exact ⟨by_norm_num, (k3 by_norm_num h41).1⟩
      · exact ⟨by_norm_num, (k3 by_norm_num h42).1⟩
      · exact ⟨by_norm_num, (k3 by_norm_num h43).1⟩
      · exact ⟨by_norm_num, (k3 by_norm_num h44).1⟩
      · exact ⟨by_norm_num, (k3 by_norm_num h45).1⟩
      · exact ⟨by_norm_num, (k3 by_norm_num h46).1⟩
      · exact ⟨by_norm_num, (k3 by_norm_num h47).1⟩
      · exact ⟨by_norm_num, (k3 by_norm_num h48).1⟩))
  zucc
  have e₅ := Exec.copyN (P := P) w₄ 50110 50300
  have ex : Exec P W secAt c _ _ := .seq e₁ (.seq e₂ (.seq e₃
    ztgxe))
  have hszF : secF.size = 101 := rfl
  have hE₃ := hE₂.keep w₃ (by
    have := exec_frameB e₃ (B := fun r => r == 50140) by_decide; exact this.2.2.1)
    (fun r hr => r₃ r ztcua)
  have hE₄ := hE₃.frame f₄ w₄ by_decide
  refine ⟨_, _, ex, by_omega, exec_frameB ex wr_secAt,
    hE₄.keep e₅.wb_right rfl (fun r hr => by
      zvmwf; zunjl; intro h; subst h; revert hr; decide), ?_⟩
  refine BitIs.of_bf (f := secF) (v := fun r => decide zthwd) by_simp_all ?_
  rw [secF, secBF_eval, hab, sideLeftOf_horiz_iff _ _ _ (dirOf_cases σ)]
  exact SecProp_congr (by rw [b₃.dec, dirOf_eq_one_iff]) (k3 by_norm_num h49).dec
    (k3 by_norm_num h50).dec (k3 by_norm_num h41).dec (k3 by_norm_num h42).dec
    (k3 by_norm_num h43).dec (k3 by_norm_num h44).dec (k3 by_norm_num h45).dec
    (k3 by_norm_num h46).dec (k3 by_norm_num h47).dec (k3 by_norm_num h48).dec
end
end SweepPrim
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqbla" : tactic => `(tactic| (have hDH : ztrfm := by rw [hC]; exact (goodShear_epsOf hG.2).2.1
                                           have hn : ztsar := by rw [hC]; exact shear_n _ _
                                           have hT := C.topIdx_le))
set_option hygiene true

/-!
# WP-K on the RAM, part 2: the orientation bit and the descriptor

* `bitS`: the orientation bit `sideBeta` of the chain (`0` if the top is the first vertex, else
  six sign tests and a boolean combination computed with `+` and truncated `-`: `x ∧ y = x + y - 1`,
  `x ∨ y = x + y - (x + y - 1)`, `¬ x = 1 - x`);
* `sS`: the tour start `S = sideS sideBeta`;
* `descS`: the host `Host.whole n` at `A₀` and the model descriptor at `A₀ + 4`.
-/
namespace Chazelle.Core
namespace Brute
open Machine Machine.Stmt Programs SignK WalkKey
@[expose] public section
theorem poly_whole (Q : Polygon) (hQ : 1 ≤ Q.n) : (Host.whole Q.n).poly Q = Q := by
  cases Q with
  | mk l =>
    zudgn

    zucr
    zuehb

    zubdb
    zuhrr
    · simp_all
    · zusx
      zudgm

      zuey
      zuipd

/-! ## The boolean combination of the orientation bit -/

/-- `bit := (d₊ ∧ bx ∧ ax) ∨ (¬d₊ ∧ ¬d₀ ∧ (bx ∨ ax)) ∨ (d₀ ∧ by ∧ bx) ∨ (d₀ ∧ by')`, from the
bits `d₊ = 63, d₀ = 64, bx = 65, ax = 66, by = 67, by' = 68`. -/
def logicB : Stmt :=
  .seq (andS 180069 180063 180065) (.seq (andS 180069 180069 180066)
  (.seq (notS 180070 180063) (.seq (notS 180071 180064) (.seq ztrkq
  (.seq (orS 180071 180065 180066 180072) (.seq ztrkq
  (.seq (andS 180071 180064 180067) (.seq (andS 180071 180071 180065)
  (.seq (andS 180072 180064 180068) (.seq (orS 180073 180069 180070 180074)
  (.seq (orS 180073 180073 180071 180074) (orS 180014 180073 180072 180074))))))))))))

/-- The write set of `logicB`. -/
def Blog (r : ℕ) : Bool := decide (180069 ≤ r ∧ r < 180075) || decide (r = 180014)
variable {d : ℕ} {x y : ℕ} {P : Polygon} {W : ℕ}
theorem fr1 {c c' : Config} (F : FrameB ztbaz c c') {q : ℕ}
    (hq : q ≠ d) : c'.nreg q = c.nreg q := F.1 q by_simp_all
theorem fr2 {d t : ℕ} {c c' : Config} (F : FrameB ztbqe c c') {q : ℕ}
    (hq : q ≠ d) (hq' : q ≠ t) : c'.nreg q = c.nreg q := F.1 q by_simp_all
theorem frLog1 (hd : Blog d = true) {c c' : Config}
    (F : FrameB ztbaz c c') : FrameB Blog c c' :=
  frameB_mono F fun r hr => by
    grind
theorem frLog2 {d t : ℕ} (hd : Blog d = true) (ht : Blog t = true) {c c' : Config}
    (F : FrameB ztbqe c c') : FrameB Blog c c' :=
  frameB_mono F fun r hr => by
    grind
theorem and_bit (hx : x ≤ 1) (hy : y ≤ 1) :
    x + y - 1 ≤ 1 ∧ (x + y - 1 = 1 ↔ x = 1 ∧ y = 1) := by_omega
theorem or_bit (hx : x ≤ 1) (hy : y ≤ 1) :
    ztkgz - ztqyt ≤ 1 ∧ (ztkgz - ztqyt = 1 ↔ x = 1 ∨ y = 1) := by_omega
theorem not_bit {x : ℕ} (hx : x ≤ 1) : 1 - x ≤ 1 ∧ (1 - x = 1 ↔ x = 0) := by_omega
theorem logicB_exec (hW : 8 ≤ W) (c : Config) (hw : WordsBounded W c)
    (h11 : c.nreg 180011 = 1) (b63 : c.nreg 180063 ≤ 1) (b64 : c.nreg 180064 ≤ 1)
    (b65 : c.nreg 180065 ≤ 1) (b66 : c.nreg 180066 ≤ 1) (b67 : c.nreg 180067 ≤ 1)
    (b68 : c.nreg 180068 ≤ 1) :
    ∃ c' k, Exec P W logicB c c' k ∧ k = 28 ∧ FrameB Blog c c' ∧
      c'.nreg 180014 ≤ 1 ∧
      (c'.nreg 180014 = 1 ↔
        (c.nreg 180063 = 1 ∧ c.nreg 180065 = 1 ∧ c.nreg 180066 = 1) ∨
        (c.nreg 180063 = 0 ∧ c.nreg 180064 = 0 ∧ (c.nreg 180065 = 1 ∨ c.nreg 180066 = 1)) ∨
        (c.nreg 180064 = 1 ∧ c.nreg 180067 = 1 ∧ c.nreg 180065 = 1) ∨
        (c.nreg 180064 = 1 ∧ c.nreg 180068 = 1)) := by
  zufsv
  -- A = d₊ ∧ bx ∧ ax
  obtain ⟨c1, k1, e1, hk1, v1, F1⟩ := andS_exec (P := P) W2 c hw (d := 180069) (x := 180063)
    (y := 180065) by_decide h11 b63 b65
  have B1 := and_bit b63 b65
  rw [← v1] at B1
  zuehr
  have a66 : c1.nreg 180066 = c.nreg 180066 := fr1 F1 by_decide
  obtain ⟨c2, k2, e2, hk2, v2, F2⟩ := andS_exec (P := P) W2 c1 e1.wb_right (d := 180069)
    (x := 180069) (y := 180066) by_decide o1 B1.1 by_omega
  have B2 := and_bit B1.1 (show c1.nreg 180066 ≤ 1 by rw [a66]; exact b66)
  rw [← v2, a66, B1.2] at B2
  have o2 : ztuph := by rw [fr1 F2 by_decide, o1]
  have r63 : c2.nreg 180063 = c.nreg 180063 := by rw [fr1 F2 by_decide, fr1 F1 by_decide]
  -- B = ¬d₊ ∧ ¬d₀ ∧ (bx ∨ ax)
  obtain ⟨c3, k3, e3, hk3, v3, F3⟩ := notS_exec (P := P) c2 e2.wb_right (d := 180070)
    (x := 180063) by_decide o2
  have B3 := not_bit (show c2.nreg 180063 ≤ 1 by rw [r63]; exact b63)
  rw [← v3, r63] at B3
  have o3 : c3.nreg 180011 = 1 := by rw [fr1 F3 by_decide, o2]
  have r64 : c3.nreg 180064 = c.nreg 180064 := by
    rw [fr1 F3 by_decide, fr1 F2 by_decide, fr1 F1 by_decide]
  obtain ⟨c4, k4, e4, hk4, v4, F4⟩ := notS_exec (P := P) c3 e3.wb_right (d := 180071)
    (x := 180064) by_decide o3
  have B4 := not_bit (show c3.nreg 180064 ≤ 1 by rw [r64]; exact b64)
  rw [← v4, r64] at B4
  have o4 : ztupo := by rw [fr1 F4 by_decide, o3]
  have r70 : c4.nreg 180070 = c3.nreg 180070 := fr1 F4 by_decide
  obtain ⟨c5, k5, e5, hk5, v5, F5⟩ := andS_exec (P := P) W2 c4 e4.wb_right (d := 180070)
    (x := 180070) (y := 180071) by_decide o4 by_omega B4.1
  have B5 := and_bit (show c4.nreg 180070 ≤ 1 by rw [r70]; exact B3.1) B4.1
  rw [← v5, r70, B3.2, B4.2] at B5
  zuehs
  have r65 : c5.nreg 180065 = c.nreg 180065 := by
    rw [fr1 F5 by_decide, fr1 F4 by_decide, fr1 F3 by_decide, fr1 F2 by_decide,
      fr1 F1 by_decide]
  have r66 : c5.nreg 180066 = c.nreg 180066 := by
    rw [fr1 F5 by_decide, fr1 F4 by_decide, fr1 F3 by_decide, fr1 F2 by_decide, a66]
  obtain ⟨c6, k6, e6, hk6, v6, F6⟩ := orS_exec (P := P) W2 c5 e5.wb_right (d := 180071)
    (x := 180065) (y := 180066) (t := 180072) by_decide by_decide by_decide o5
    by_omega by_omega
  have B6 := or_bit (show c5.nreg 180065 ≤ 1 by rw [r65]; exact b65)
    (show c5.nreg 180066 ≤ 1 by rw [r66]; exact b66)
  rw [← v6, r65, r66] at B6
  have o6 : ztupr := by rw [fr2 F6 by_decide by_decide, o5]
  have r70' : c6.nreg 180070 = c5.nreg 180070 := fr2 F6 by_decide by_decide
  obtain ⟨c7, k7, e7, hk7, v7, F7⟩ := andS_exec (P := P) W2 c6 e6.wb_right (d := 180070)
    (x := 180070) (y := 180071) by_decide o6 by_omega B6.1
  have B7 := and_bit (show c6.nreg 180070 ≤ 1 by rw [r70']; exact B5.1) B6.1
  rw [← v7, r70', B5.2, B6.2] at B7
  zueht
  -- C = d₀ ∧ by ∧ bx
  have s64 : c7.nreg 180064 = c.nreg 180064 := by
    rw [fr1 F7 by_decide, fr2 F6 by_decide by_decide, fr1 F5 by_decide,
      fr1 F4 by_decide, r64]
  have s67 : c7.nreg 180067 = c.nreg 180067 := by
    rw [fr1 F7 by_decide, fr2 F6 by_decide by_decide, fr1 F5 by_decide,
      fr1 F4 by_decide, fr1 F3 by_decide, fr1 F2 by_decide, fr1 F1 by_decide]
  obtain ⟨c8, k8, e8, hk8, v8, F8⟩ := andS_exec (P := P) W2 c7 e7.wb_right (d := 180071)
    (x := 180064) (y := 180067) by_decide o7 by_omega by_omega
  have B8 := and_bit (show c7.nreg 180064 ≤ 1 by rw [s64]; exact b64)
    (show c7.nreg 180067 ≤ 1 by rw [s67]; exact b67)
  rw [← v8, s64, s67] at B8
  zuehu
  have s65 : c8.nreg 180065 = c.nreg 180065 := by
    rw [fr1 F8 by_decide, fr1 F7 by_decide, fr2 F6 by_decide by_decide, r65]
  obtain ⟨c9, k9, e9, hk9, v9, F9⟩ := andS_exec (P := P) W2 c8 e8.wb_right (d := 180071)
    (x := 180071) (y := 180065) by_decide o8 B8.1 by_omega
  have B9 := and_bit B8.1 (show c8.nreg 180065 ≤ 1 by rw [s65]; exact b65)
  rw [← v9, s65, B8.2] at B9
  zuehv
  -- D = d₀ ∧ by'
  have t64 : c9.nreg 180064 = c.nreg 180064 := by
    rw [fr1 F9 by_decide, fr1 F8 by_decide, s64]
  have t68 : c9.nreg 180068 = c.nreg 180068 := by
    rw [fr1 F9 by_decide, fr1 F8 by_decide, fr1 F7 by_decide,
      fr2 F6 by_decide by_decide, fr1 F5 by_decide, fr1 F4 by_decide, fr1 F3 by_decide,
      fr1 F2 by_decide, fr1 F1 by_decide]
  obtain ⟨c10, k10, e10, hk10, v10, F10⟩ := andS_exec (P := P) W2 c9 e9.wb_right (d := 180072)
    (x := 180064) (y := 180068) by_decide o9 by_omega by_omega
  have B10 := and_bit (show c9.nreg 180064 ≤ 1 by rw [t64]; exact b64)
    (show c9.nreg 180068 ≤ 1 by rw [t68]; exact b68)
  rw [← v10, t64, t68] at B10
  have o10 : ztupd := by rw [fr1 F10 by_decide, o9]
  -- the disjunction
  have x69 : c10.nreg 180069 = c2.nreg 180069 := by
    rw [fr1 F10 by_decide, fr1 F9 by_decide, fr1 F8 by_decide, fr1 F7 by_decide,
      fr2 F6 by_decide by_decide, fr1 F5 by_decide, fr1 F4 by_decide, fr1 F3 by_decide]
  have x70 : c10.nreg 180070 = c7.nreg 180070 := by
    rw [fr1 F10 by_decide, fr1 F9 by_decide, fr1 F8 by_decide]
  have x71 : c10.nreg 180071 = c9.nreg 180071 := fr1 F10 by_decide
  obtain ⟨c11, k11, e11, hk11, v11, F11⟩ := orS_exec (P := P) W2 c10 e10.wb_right (d := 180073)
    (x := 180069) (y := 180070) (t := 180074) by_decide by_decide by_decide o10
    by_omega by_omega
  have B11 := or_bit (show c10.nreg 180069 ≤ 1 by rw [x69]; exact B2.1)
    (show c10.nreg 180070 ≤ 1 by rw [x70]; exact B7.1)
  rw [← v11, x69, x70, B2.2, B7.2] at B11
  have o11 : ztupe := by rw [fr2 F11 by_decide by_decide, o10]
  have y71 : c11.nreg 180071 = c9.nreg 180071 := by
    rw [fr2 F11 by_decide by_decide, x71]
  obtain ⟨c12, k12, e12, hk12, v12, F12⟩ := orS_exec (P := P) W2 c11 e11.wb_right (d := 180073)
    (x := 180073) (y := 180071) (t := 180074) by_decide by_decide by_decide o11
    B11.1 by_omega
  have B12 := or_bit B11.1 (show c11.nreg 180071 ≤ 1 by rw [y71]; exact B9.1)
  rw [← v12, y71, B11.2, B9.2] at B12
  have o12 : c12.nreg 180011 = 1 := by rw [fr2 F12 by_decide by_decide, o11]
  have y72 : c12.nreg 180072 = c10.nreg 180072 := by
    rw [fr2 F12 by_decide by_decide, fr2 F11 by_decide by_decide]
  obtain ⟨c13, k13, e13, hk13, v13, F13⟩ := orS_exec (P := P) W2 c12 e12.wb_right (d := 180014)
    (x := 180073) (y := 180072) (t := 180074) by_decide by_decide by_decide o12
    B12.1 by_omega
  have B13 := or_bit B12.1 (show c12.nreg 180072 ≤ 1 by rw [y72]; exact B10.1)
  rw [← v13, y72, B12.2, B10.2] at B13
  have ex : Exec P W logicB c c13 _ := .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 (.seq e6
    (.seq e7 (.seq e8 (.seq e9 (.seq e10 (.seq e11 (.seq e12 e13)))))))))))
  refine ⟨c13, _, ex, by_grind, ?_, B13.1, ?_⟩
  · have G1 := frLog1 by_decide F1
    have G2 := frLog1 by_decide F2
    have G3 := frLog1 by_decide F3
    have G4 := frLog1 by_decide F4
    have G5 := frLog1 by_decide F5
    have G6 := frLog2 by_decide by_decide F6
    have G7 := frLog1 by_decide F7
    have G8 := frLog1 by_decide F8
    have G9 := frLog1 by_decide F9
    have G10 := frLog1 by_decide F10
    have G11 := frLog2 by_decide by_decide F11
    have G12 := frLog2 by_decide by_decide F12
    have G13 := frLog2 by_decide by_decide F13
    exact (((((((((((G1.trans G2).trans G3).trans G4).trans G5).trans G6).trans G7).trans
      G8).trans G9).trans G10).trans G11).trans G12).trans G13
  · rw [B13.2]; grind

/-! ## The orientation bit -/

/-- The six tests and the combination (top index `T > 0`). -/
def bitGen : Stmt :=
  .seq (block [.addN 180060 180000 180013, .subN 180061 180060 180011, .addN 180062 180060 180011])
    (.seq ztipp
    (.seq (testS 2 ztpsd ztdyf ztjdz 180063)
    (.seq (testS 3 ztpsd ztdyf ztjdz 180064)
    (.seq (testS 0 ztdyf ztjdz ztdyf 180065)
    (.seq (testS 0 ztpsd ztdyf ztdyf 180066)
    (.seq (testS 1 ztdyf ztjdz ztdyf 180067)
    (.seq (testS 1 ztjdz ztdyf ztdyf 180068) logicB)))))))

/-- The orientation bit. -/
def bitS : Stmt := .ifLtN 180028 180013 bitGen (.instr (.constN 180014 0))

/-- The write set of `bitS`: the kernel and `180014`, `180060 … 180074`. -/
def Bbit (r : ℕ) : Bool := Bk r || decide (r = 180014 ∨ (180060 ≤ r ∧ r < 180075))
theorem frame_test_bit (hd : 180060 ≤ d ∧ d < 180075) :
    ∀ r, Bbit r = false → Bt d r = false := by
  zuz
  unfold Bbit at hr; unfold Bt
  grind

/-- A test on three vertices held in registers. -/
theorem testV_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {op : ℕ}
    (hop : op ≤ 3) {r₁ r₂ r₃ d : ℕ} (h₁ : r₁ < 10000 ∨ 10500 ≤ r₁) (h₂ : r₂ < 10000 ∨ 10500 ≤ r₂)
    (h₃ : r₃ < 10000 ∨ 10500 ≤ r₃) (c : Config) (hw : WordsBounded W c) {x₁ x₂ x₃ : ℕ}
    (e₁ : c.nreg r₁ = x₁) (e₂ : c.nreg r₂ = x₂) (e₃ : c.nreg r₃ = x₃) (l₁ : x₁ < P.n)
    (l₂ : x₂ < P.n) (l₃ : x₃ < P.n) :
    ∃ c' k, Exec P W (testS op (.v r₁) (.v r₂) (.v r₃) d) c c' k ∧ k ≤ 245 ∧
      FrameB ztjhb c c' ∧ c'.nreg d ≤ 1 ∧
      (c'.nreg d = 1 ↔ SignTest op ((Qof P).vtx x₁) ((Qof P).vtx x₂) ((Qof P).vtx x₃)) := by
  obtain ⟨c', k, e, hk, F, b, hb⟩ := testS_exec (P := P) hG hW hop (x := .v r₁) (y := .v r₂)
    (z := .v r₃) (d := d) h₁ h₂ h₃ c hw ztig
    ztig ztig
  simp only [Src.pt, SymPt.eval, e₁, e₂, e₃] at hb
  grind
theorem bt_keep {d r : ℕ} {c c' : Config} (F : FrameB ztjhb c c') (hr : r < 10000 ∨ 10500 ≤ r)
    (hd : r ≠ d) : c'.nreg r = c.nreg r := by
  apply F.1
  unfold Bt Bk
  grind
theorem bit_of {x : ℕ} {p : Prop} (hb : x ≤ 1) (h : x = 1 ↔ p) : (x = 0 ↔ ¬ p) := by
  grind

/-- The orientation bit in terms of the sign tests of `bitGen`. -/
theorem sideBeta_tests (hG : GoodEnv P) {C : Chain} (hC : C.P = Qof P)
    (hsn : C.s + C.m + 1 ≤ P.n) (hT0 : 0 < C.topIdx) :
    C.sideBeta = true ↔
      (0 < det ztbti ztwvs
          ztwvr ∧
        ((Qof P).vtx ztwi).1 < ((Qof P).vtx zttt).1 ∧
        ((Qof P).vtx ztgdh).1 < ((Qof P).vtx ztwi).1) ∨
      (¬ 0 < det ztbti ztwvs
          ztwvr ∧
        ¬ det ztbti ztwvs
          ztwvr = 0 ∧
        (((Qof P).vtx ztwi).1 < ((Qof P).vtx zttt).1 ∨
          ((Qof P).vtx ztgdh).1 < ((Qof P).vtx ztwi).1)) ∨
      (det ztbti ztwvs
          ztwvr = 0 ∧
        ((Qof P).vtx ztwi).2 < ((Qof P).vtx zttt).2 ∧
        ((Qof P).vtx ztwi).1 < ((Qof P).vtx zttt).1) ∨
      (det ztbti ztwvs
          ztwvr = 0 ∧
        ((Qof P).vtx zttt).2 < ((Qof P).vtx ztwi).2) := by
  zqbla
  have eA : C.vertex ztbap = (Qof P).vtx ztgdh := by
    have h1 : C.s + ztbap < C.P.n := by_omega
    have h2 : C.s + ztbap = C.s + C.topIdx - 1 := by_omega
    rw [vertex_eq h1, h2, hC]
  have eT : C.top = (Qof P).vtx ztwi := by
    have h1 : C.s + C.topIdx < C.P.n := by_omega
    show C.vertex C.topIdx = _
    rw [vertex_eq h1, hC]
  have eB : C.vertex ztbao = (Qof P).vtx zttt := by
    show C.P.vtx ztymh = _
    grind
  rw [sideBeta_iff hDH hT0, eA, eT, eB]
  constructor
  · grind
  grind
set_option maxHeartbeats 1000000 in
/-- **The orientation bit** for a top vertex other than the first. -/
theorem bitGen_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (hW8 : 8 ≤ W)
    {C : Chain}
    (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) (hT0 : 0 < C.topIdx) (c : Config)
    (hw : WordsBounded W c) (h0 : c.nreg 180000 = C.s) (h10 : c.nreg 180010 = P.n)
    (h11 : c.nreg 180011 = 1) (h13 : c.nreg 180013 = C.topIdx) :
    ∃ c' k, Exec P W bitGen c c' k ∧ k ≤ 1600 ∧ FrameB Bbit c c' ∧ c'.nreg 180014 ≤ 1 ∧
      ztmfd := by
  zqbla
  set T := C.topIdx with hTd
  set a := C.s with had
  -- the three indices
  obtain ⟨c₁, k₁, e₁, hk₁, q60, q61, q62, R₁⟩ : ∃ c₁ k₁, Exec P W (block [.addN 180060 180000 180013,
      .subN 180061 180060 180011, .addN 180062 180060 180011]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 180060 = a + T ∧ c₁.nreg 180061 = a + T - 1 ∧ c₁.nreg 180062 = a + T + 1 ∧
      FrameB (fun r => decide (180060 ≤ r ∧ r < 180063)) c c₁ := by
    exec_block
    · omega
    · config_simp; omega
    · refine ⟨rfl, ?_, ?_, ?_, ztgq⟩
      · simp_all
      · simp_all
      · simp_all
      · zubzq
        zudw
  zud
  have k10 : c₁.nreg 180010 = P.n := by rw [R₁.1 _ by_decide, h10]
  have k11 : c₁.nreg 180011 = 1 := by rw [R₁.1 _ by_decide, h11]
  -- the index after the top, modulo `n`
  set qb := (a + T + 1) % P.n with hqb
  have hqbn : qb < P.n := Nat.mod_lt _ by_omega
  obtain ⟨c₂, k₂, e₂, hk₂, q62', R₂⟩ : ∃ c₂ k₂, Exec P W
      ztipp c₁ c₂ k₂ ∧ k₂ ≤ 3 ∧
      c₂.nreg 180062 = qb ∧ FrameB (fun r => decide (r = 180062)) c₁ c₂ := by
    by_cases hlt : a + T + 1 < P.n
    · refine ⟨_, _, .ifLtN_true by_omega ztwd, by_omega, ?_,
        FrameB.refl _ _⟩
      rw [q62, hqb, Nat.mod_eq_of_lt hlt]
    · have hq : a + T + 1 = P.n := by_omega
      refine ⟨_, _, .ifLtN_false by_omega
        (Exec.constN w₁ 180062 0 by_omega), le_refl _, ?_, ⟨fun r hr => ?_, by_simp_all,
        rfl, rfl, rfl⟩⟩
      · simp_all
      simp_all
  zue
  have p60 : c₂.nreg 180060 = a + T := by rw [R₂.1 _ by_decide, q60]
  have p61 : c₂.nreg 180061 = a + T - 1 := by rw [R₂.1 _ by_decide, q61]
  have lt60 : a + T < P.n := by_omega
  have lt61 : a + T - 1 < P.n := by_omega
  -- six tests
  obtain ⟨c₃, k₃, e₃, hk₃, F₃, b63, t63⟩ := testV_exec (P := P) hG hW (op := 2) by_omega
    (r₁ := 180061) (r₂ := 180060) (r₃ := 180062) (d := 180063) ztbh
    ztbh ztbh c₂ w₂ p61 p60 q62' lt61 lt60 hqbn
  have p60₃ : c₃.nreg 180060 = a + T := by rw [bt_keep F₃ by_omega by_omega, p60]
  have p61₃ : c₃.nreg 180061 = a + T - 1 := by rw [bt_keep F₃ by_omega by_omega, p61]
  have p62₃ : c₃.nreg 180062 = qb := by rw [bt_keep F₃ by_omega by_omega, q62']
  obtain ⟨c₄, k₄, e₄, hk₄, F₄, b64, t64⟩ := testV_exec (P := P) hG hW (op := 3) by_omega
    (r₁ := 180061) (r₂ := 180060) (r₃ := 180062) (d := 180064) ztbh
    ztbh ztbh c₃ e₃.wb_right p61₃ p60₃ p62₃ lt61 lt60 hqbn
  have p60₄ : c₄.nreg 180060 = a + T := by rw [bt_keep F₄ by_omega by_omega, p60₃]
  have p61₄ : c₄.nreg 180061 = a + T - 1 := by
    rw [bt_keep F₄ by_omega by_omega, p61₃]
  have p62₄ : c₄.nreg 180062 = qb := by rw [bt_keep F₄ by_omega by_omega, p62₃]
  obtain ⟨c₅, k₅, e₅, hk₅, F₅, b65, t65⟩ := testV_exec (P := P) hG hW (op := 0) by_omega
    (r₁ := 180060) (r₂ := 180062) (r₃ := 180060) (d := 180065) ztbh
    ztbh ztbh c₄ e₄.wb_right p60₄ p62₄ p60₄ lt60 hqbn lt60
  have p60₅ : c₅.nreg 180060 = a + T := by rw [bt_keep F₅ by_omega by_omega, p60₄]
  have p61₅ : c₅.nreg 180061 = a + T - 1 := by
    rw [bt_keep F₅ by_omega by_omega, p61₄]
  have p62₅ : c₅.nreg 180062 = qb := by rw [bt_keep F₅ by_omega by_omega, p62₄]
  obtain ⟨c₆, k₆, e₆, hk₆, F₆, b66, t66⟩ := testV_exec (P := P) hG hW (op := 0) by_omega
    (r₁ := 180061) (r₂ := 180060) (r₃ := 180060) (d := 180066) ztbh
    ztbh ztbh c₅ e₅.wb_right p61₅ p60₅ p60₅ lt61 lt60 lt60
  have p60₆ : c₆.nreg 180060 = a + T := by rw [bt_keep F₆ by_omega by_omega, p60₅]
  have p62₆ : c₆.nreg 180062 = qb := by rw [bt_keep F₆ by_omega by_omega, p62₅]
  obtain ⟨c₇, k₇, e₇, hk₇, F₇, b67, t67⟩ := testV_exec (P := P) hG hW (op := 1) by_omega
    (r₁ := 180060) (r₂ := 180062) (r₃ := 180060) (d := 180067) ztbh
    ztbh ztbh c₆ e₆.wb_right p60₆ p62₆ p60₆ lt60 hqbn lt60
  have p60₇ : c₇.nreg 180060 = a + T := by rw [bt_keep F₇ by_omega by_omega, p60₆]
  have p62₇ : c₇.nreg 180062 = qb := by rw [bt_keep F₇ by_omega by_omega, p62₆]
  obtain ⟨c₈, k₈, e₈, hk₈, F₈, b68, t68⟩ := testV_exec (P := P) hG hW (op := 1) by_omega
    (r₁ := 180062) (r₂ := 180060) (r₃ := 180060) (d := 180068) ztbh
    ztbh ztbh c₇ e₇.wb_right p62₇ p60₇ p60₇ hqbn lt60 lt60
  -- bits in `c₈`
  have B63 : c₈.nreg 180063 = c₃.nreg 180063 := by
    rw [bt_keep F₈ by_omega by_omega, bt_keep F₇ by_omega by_omega,
      bt_keep F₆ by_omega by_omega, bt_keep F₅ by_omega by_omega,
      bt_keep F₄ by_omega by_omega]
  have B64 : c₈.nreg 180064 = c₄.nreg 180064 := by
    rw [bt_keep F₈ by_omega by_omega, bt_keep F₇ by_omega by_omega,
      bt_keep F₆ by_omega by_omega, bt_keep F₅ by_omega by_omega]
  have B65 : c₈.nreg 180065 = c₅.nreg 180065 := by
    rw [bt_keep F₈ by_omega by_omega, bt_keep F₇ by_omega by_omega,
      bt_keep F₆ by_omega by_omega]
  have B66 : c₈.nreg 180066 = c₆.nreg 180066 := by
    rw [bt_keep F₈ by_omega by_omega, bt_keep F₇ by_omega by_omega]
  have B67 : c₈.nreg 180067 = c₇.nreg 180067 := bt_keep F₈ by_omega by_omega
  have K11 : c₈.nreg 180011 = 1 := by
    rw [bt_keep F₈ by_omega by_omega, bt_keep F₇ by_omega by_omega,
      bt_keep F₆ by_omega by_omega, bt_keep F₅ by_omega by_omega,
      bt_keep F₄ by_omega by_omega, bt_keep F₃ by_omega by_omega,
      R₂.1 _ by_decide, k11]
  obtain ⟨c₉, k₉, e₉, hk₉, F₉, b14, t14⟩ := logicB_exec (P := P) hW8 c₈ e₈.wb_right K11
    by_omega by_omega by_omega
    by_omega by_omega b68
  rw [B63, B64, B65, B66, B67] at t14
  have ex : Exec P W bitGen c c₉ _ :=
    .seq e₁ ztqr
  refine ⟨c₉, _, ex, by_omega, ?_, b14, ?_⟩
  · have G1 : FrameB Bbit c c₁ := frameB_mono R₁ fun r hr => by
      zulaw
    have G2 : FrameB Bbit c₁ c₂ := frameB_mono R₂ fun r hr => by
      zulaw
    have G9 : FrameB Bbit c₈ c₉ := frameB_mono F₉ fun r hr => by
      unfold Bbit at hr; unfold Blog
      grind
    exact (((((((G1.trans G2).trans (frameB_mono F₃ zthwt)).trans
      (frameB_mono F₄ zthwt)).trans
      (frameB_mono F₅ zthwt)).trans
      (frameB_mono F₆ zthwt)).trans
      (frameB_mono F₇ zthwt)).trans
      (frameB_mono F₈ zthwt)).trans G9
  · zvnhd at t63 t64 t65 t66 t67 t68
    rw [t14, sideBeta_tests hG hC hsn hT0]
    have n63 := bit_of b63 t63
    have n64 := bit_of b64 t64
    rw [n63, n64, t63, t64, t65, t66, t67, t68]
end
end Brute
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqblr" : tactic => `(tactic| (intro i hi
                                           rw [hVlen] at hi))
local macro "zqbls" : tactic => `(tactic| have : ztcrc := by_grind)
local macro "zqblt" : tactic => `(tactic| (set M := interiorModel Q with hMdef
                                           have hM := walkAx_interiorModel hQ
                                           zuglo
                                           have hfin := hFam.1))
set_option hygiene true

/-!
# WP-M (H1, part 4): the host polygon of a region of an interior submap is simple

For a simple polygon `Q`, a nonempty chord family `F` of the interior model `I = interiorModel Q`
and a region `U` of `F`, the **host polygon** `regionHost Q F U` lists the walk points of the
host keys of `U` (`DownHost.hostKeys`) in increasing key order.  It is the boundary `R*` of `U`
(arcs of `U` and its exit chords).  **`regionHost_simple`: it is a simple polygon** (obligation
H1 of `docs/design-downphase.md`).  No distinct-heights hypothesis is needed.

Proof: `DownHost.KeyHost.simple` (part 1) with the edges classified by `DownHost.gap` (part 3):
an edge whose key interval lies in an arc of `U` contains no walk vertex strictly inside, so it
is a piece of one walk edge (`arcEdge_of_noVertex`); otherwise it is a chord of `F`.  Two chord
edges are distinct chords (their key pairs differ, `N ≥ 3`), hence disjoint in the interior.  At
least three host keys exist (`three_le`): an arc of `U` has two, and the exit chord at its end
has a third end unless the arc lies in one walk edge, which the chord would then overlap.
-/
namespace Chazelle.Core
namespace DownHost
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft SideClean SideSectorIn ChordSystem
  freeIn regionsIn sideLeft_edge TouchesIn)
open Chazelle.Jordan (offset nrm sqLen sqLen_pos det_offset eventually_offset_mem convex_det_pos)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext lerp_mem_segment)
variable {M : Model}

/-- **Every region is faced at a non-cut position inside a walk edge** (`WalkAx.exists_faces`
with the non-cut property: the position is at a height that is no chord height). -/
theorem exists_faces_nc (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {U : Set Point} (hU : U ∈ M.regions F) :
    ∃ (p : ℕ) (t : ℝ), p < M.W.n ∧ 0 < t ∧ t < 1 ∧ ¬ M.IsCut F ztk ∧ M.Faces p t U := by
  zudr
  zufue
  zutj

  -- a point of `U` at a generic height
  set B : Set ℝ := {y | ∃ i < M.W.n, (M.W.vtx i).2 = y} ∪ {y | ∃ c ∈ F, ∃ x ∈ c, x.2 = y}
    with hB
  have hBfin : B.Finite := by
    refine Set.Finite.union ?_ (WalkAx.finite_chord_heights hsys)
    have : ztwpy := by
      rfl
    zuces
  zunj

  have hzU : ztmxh := by
    apply hball
    zufv
    zubet

  zubdr
  zuehk

  have hzc : ztebl := by
    grind
  zucs

  -- the segment from `z` to `q` (half-open) is in `U`

  have hLc : ztulg :=
    isPreconnected_Ico.image _ (by fun_prop : Continuous fun s' : ℝ => (ztbtb : Point)).continuousOn
  have hLF : ztgua := by
    zuvn
    tauto
  zukhl
  have hLU : ztpkn := by
    zuczk

  -- a half-disk on the left of the edge at `q` is free
  zukfc
  zuba

  have hHF : ztmtg := by
    zunr

    · zudkb
    · zuedy
  -- a point of the segment lies in the half-disk
  have hq0 : zthot := by
    zucqj
  zucx

  have hw : ztxsx := by
    zujx
    · zufv
      zujt

    · zufbr
      have e : ztwoj := by
        zubzu
      zuexh

  zukgq
  have hHU : ztsbq := by
    zuczl

  refine ztiol
  · rintro ⟨c, hc, p', t', hA', heq⟩
    obtain ⟨rfl, rfl⟩ := key_inj ht.1.le ht.2 hA'.2.1 hA'.2.2.1 heq
    exact hyB (Or.inr ⟨c, hc, _, hA'.2.2.2.1, by zvnck⟩)
  zukg

/-! ## Walk points of keys -/
theorem lerp_lerp (u v : Point) (t t' s : ℝ) :
    lerp ztcnw (lerp u v t') s = lerp u v (t + s * ztkft) := by
  zubvl

/-- The walk point of a key `x ∈ [0, n)`: position `(⌊x⌋, x - ⌊x⌋)`. -/
noncomputable def hostPt (W : Polygon) (x : ℝ) : Point := sidePt W ⌊x⌋₊ ztpep
theorem floor_add {p : ℕ} {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) : ⌊(p : ℝ) + t⌋₊ = p := by
  zuorn
  simp_all
theorem hostPt_eq (W : Polygon) {p : ℕ} {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    hostPt W ztk = sidePt W p t := by
  unfold hostPt; rw [floor_add ht ht1]; simp
theorem sidePt_one (W : Polygon) (p : ℕ) : sidePt W p 1 = W.vtx ztwjb := by
  zufdr

/-- **An arc edge**: two keys `a ≠ b` with no walk vertex key strictly between them (cyclically)
span a piece of one walk edge, all of whose points are walk points with keys in the closed
interval from `a` to `b`. -/
theorem arcEdge_of_noVertex (W : Polygon) {a b : ℝ} (ha0 : 0 ≤ a) (han : a < W.n) (hb0 : 0 ≤ b)
    (hbn : b < W.n) (_hab : a ≠ b) (hnv : ∀ k : ℕ, k < W.n → ¬ sideInArc a b k) :
    ∀ z ∈ Chazelle.segment (hostPt W a) (hostPt W b), ∃ p, p < W.n ∧ ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧
      z = sidePt W p t ∧ (if a < b then a ≤ p + t ∧ p + t ≤ b else a ≤ p + t ∨ p + t ≤ b) := by
  zuhoj
  have hp := Nat.floor_le ha0
  have hp1 := Nat.lt_floor_add_one a
  have hpn : p < W.n := by
    have : ztphc := by_grind
    simp_all
  zujyv
  -- the end `b` on the same walk edge `p`
  obtain ⟨t'', ht''a, ht''1, hB, hkey⟩ : ∃ t'' : ℝ, a - p < t'' ∧ t'' ≤ 1 ∧
      hostPt W b = sidePt W p t'' ∧
      (if a < b then b = p + t'' else b = 0 ∧ p + 1 = W.n ∧ t'' = 1) := by
    zufrd
    · have hbp : ztsdq := by
        zubq

        have hk : zteie := by
          zqbls
          zufc
        zulvu
        zuxb
      refine ⟨b - p, by_linarith, by_linarith, ?_, by_simp_all⟩
      zukky
      · have := hostPt_eq W (p := p) (t := b - p) by_linarith by_linarith
        simp_all
      · have hk : zteie := by
          zulgm
          zufc
        zujwy
        rw [e, hostPt_eq W le_rfl one_pos, Chazelle.Chain.sidePt_zero,
          show ((p + 1 : ℕ) : ℝ) + 0 - p = 1 by push_cast; ring, sidePt_one,
          Nat.mod_eq_of_lt hk]
    · have hb0' : b = 0 := by
        zumv
        have hbpos : ztrzh := by_grind
        zulvt
        zuxb
      have hpn1 : ztskp := by
        zumv
        zukcw
        zulvu
        zuxb
      refine ⟨1, by_linarith, le_rfl, ?_, by_simp_all⟩
      rw [hb0', show (0 : ℝ) = ((0 : ℕ) : ℝ) + 0 by simp, hostPt_eq W le_rfl one_pos,
        Chazelle.Chain.sidePt_zero, sidePt_one, hpn1, Nat.mod_self]
  -- the points of the segment
  zugh
  rw [hA, hB] at hz
  zubxv
  have hlerp : lerp (sidePt W p _) (sidePt W p t'') s =
      sidePt W p (a - p + s * ztzyg) := lerp_lerp _ _ _ _ _
  zugva
  set u := a - p + s * ztzyg with hu
  have hu0 : a - p ≤ u := by_nlinarith
  have hu1 : u ≤ t'' := by_nlinarith
  rcases (hu1.trans ht''1).lt_or_eq with hlt1 | heq1
  · grind
  · have ht1 : t'' = 1 := by_grind
    refine ⟨ztr % W.n, Nat.mod_lt _ by_omega, 0, le_rfl, one_pos, ?_, ?_⟩
    · rw [heq1, sidePt_one, Chazelle.Chain.sidePt_zero]
    · split_ifs at hkey ⊢ with hab'
      · have hk : zteie := by
          zqbls
          zufc
        rw [Nat.mod_eq_of_lt hk, hkey, ht1]; grind
      · rw [hkey.2.1, Nat.mod_self, hkey.1]; simp

/-! ## Sorted keys -/

/-- The host keys of `U` in increasing order. -/
noncomputable def hostKeyList (M : Model) (F : Set ztf) (U : Set Point) : List ℝ := by
  classical
  exact if h : (hostKeys M F U).Finite then h.toFinset.sort ztkhr else []

/-- **The host polygon of the region `U`**: the walk points of its host keys, in increasing
key order. -/
noncomputable def hostPts (M : Model) (F : Set ztf) (U : Set Point) : List Point :=
  (hostKeyList M F U).map (hostPt M.W)
theorem hostKeyList_eq {F : Set ztf} {U : Set Point} (h : (hostKeys M F U).Finite) :
    hostKeyList M F U = h.toFinset.sort ztkhr := by
  classical
  unfold hostKeyList; zunvj

/-- A strictly sorted list: no element lies strictly (cyclically) between two consecutive
entries. -/
theorem sorted_gap {L : List ℝ} (hmono : ∀ i j, i < j → j < L.length → L.getD i 0 < L.getD j 0)
    (h2 : 2 ≤ L.length) {i : ℕ} (hi : i < L.length) {x : ℝ} (hx : x ∈ L) :
    ¬ sideInArc ztszd (L.getD (ztg % L.length) 0) x := by
  zufyn
  have hxj : L[j] = L.getD j 0 := by_simp_all
  rw [hxj]
  have hle : ∀ a b, a < L.length → b < L.length → L.getD a 0 < L.getD b 0 → a < b := by
    zubto
    zudxc
    rcases (not_lt.1 h').lt_or_eq with h'' | rfl
    · grind
    grind
  zufdq
  by_cases hi1 : i + 1 < L.length
  · rw [Nat.mod_eq_of_lt hi1, ite_eq_left by_grind]
    grind
  · have e : ztg % L.length = 0 := by rw [show i + 1 = L.length by omega, Nat.mod_self]
    rw [e, ite_eq_right by_grind]
    grind

/-- Index arithmetic: with at least three entries, two distinct consecutive pairs of a cyclic
list are distinct as sets. -/
theorem pair_ne {N i j : ℕ} (hN : 3 ≤ N) (hi : i < N) (hj : j < N) (hij : i ≠ j)
    (h1 : j = i ∨ j = ztg % N) (h2 : ztl % N = i ∨ ztl % N = ztg % N) : False := by
  have hs : ∀ k, k < N → (k + 1 < N ∧ zts % N = k + 1) ∨ (k + 1 = N ∧ zts % N = 0) := by
    zugf
    rcases Nat.lt_or_ge zts N with h | h
    · zulem
    · exact Or.inr ⟨by_omega, by rw [show k + 1 = N by omega, Nat.mod_self]⟩
  rcases hs i hi with ⟨hi1, ei⟩ | ⟨hi1, ei⟩ <;> rcases hs j hj with ⟨hj1, ej⟩ | ⟨hj1, ej⟩ <;>
    rw [ei] at h1 h2 <;> rw [ej] at h2 <;> omega

/-! ## The host polygon of a region of the interior model -/
variable {Q : Polygon} {F : Set (Set Point)} {U : Set Point}

/-- Attachment keys of a chord are the keys of its two attachments. -/
theorem attach_key_cases (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {pa pb pc : ℕ}
    {ta tb tc : ℝ} (hA : SideAttach M.W c pa ta) (hB : SideAttach M.W c pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) (hC : SideAttach M.W c pc tc) :
    (pc : ℝ) + tc = pa + ta ∨ (pc : ℝ) + tc = pb + tb := by
  obtain ⟨e, -, -, -, -, -, hother⟩ := hM.attach_other_end hc hA
  by_cases h : sidePt M.W pc tc = sidePt M.W pa ta
  · obtain ⟨rfl, rfl⟩ := hM.attach_unique hc hC hA h
    simp
  · have h1 := hother pc tc hC h
    have h2 := hother pb tb hB by_grind
    obtain ⟨rfl, rfl⟩ := hM.attach_unique hc hC hB ztmkm
    simp

/-- **At least three host keys.** -/
theorem three_le (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q F) (hne : F.Nonempty)
    (hU : U ∈ (interiorModel Q).regions F) :
    ∃ x ∈ hostKeys ztd F U, ∃ y ∈ hostKeys ztd F U,
      ∃ z ∈ hostKeys ztd F U, x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  zqblt
  have hGM : ztsbo := Or.inr by_grind
  obtain ⟨p, t, hp, ht0, ht1, hcut, hfac⟩ := exists_faces_nc hM hF hfin hU
  obtain ⟨X, hX, l, r, harc, hin⟩ :=
    WalkEmbed.exists_arc_around hGM hFam by_positivity hcut
  have hXU := WalkAx.faces_unique hX hU (harc.2.2.2.2.2.2 p t hp ht0 ht1 hin) hfac
  zulsx
  have hl : l ∈ hostKeys M F X := by
    obtain ⟨c, ⟨hc, ht⟩, p', t', hA, h⟩ := hM.exists_exit_at_start hF hfin hne hU harc
    exact Or.inl ⟨c, hc, ht, p', t', hA, h⟩
  obtain ⟨c, ⟨hc, htc⟩, p₂, t₂, hA₂, hr⟩ := hM.exists_exit_at_end hF hfin hne hU harc
  have hrk : r ∈ hostKeys M F X := Or.inl ⟨c, hc, htc, p₂, t₂, hA₂, hr⟩
  have hlr := (WalkAx.arc_cuts hne harc).2.2
  by_cases hmid : ∃ x ∈ hostKeys M F X, sideInArc l r x
  · obtain ⟨x, hx, hxin⟩ := hmid
    exact ⟨l, hl, r, hrk, x, hx, hlr, fun h => not_sideInArc_left l r by_simp_all,
      fun h => not_sideInArc_right l r by_simp_all⟩
  push Not at hmid
  obtain ⟨pb, tb, hB, hBne⟩ := hM.other_attach ztlz hA₂
  have hf : (pb : ℝ) + tb ∈ hostKeys M F X := Or.inl ztioc
  have hfr : (pb : ℝ) + tb ≠ r := by
    zvnel; exact WalkAx.key_ne_of_pt_ne hB hA₂ hBne
  by_cases hfl : (pb : ℝ) + tb = l
  · exfalso
    -- the arc lies in one walk edge, and the chord `c` would overlap it
    have hb : 0 ≤ l ∧ l < M.W.n ∧ 0 ≤ r ∧ r < M.W.n :=
      ⟨harc.1, harc.2.1, harc.2.2.1, harc.2.2.2.1⟩
    have hnv : ∀ k : ℕ, k < M.W.n → ¬ sideInArc l r k := fun k hk hkin =>
      hmid k (Or.inr ⟨k, hk, rfl, l, r, harc, hkin⟩) hkin
    have hseg := arcEdge_of_noVertex M.W hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hlr hnv
    obtain ⟨-, -, hopen, -, -⟩ := hM.attach_seg ztlz hA₂ hB by_grind
    zufvn
    have hPr : sidePt M.W p₂ t₂ = hostPt M.W r := by rw [hr, hostPt_eq M.W hA₂.2.1 hA₂.2.2.1]
    have hPl : sidePt M.W pb tb = hostPt M.W l := by rw [← hfl, hostPt_eq M.W hB.2.1 hB.2.2.1]
    rw [hPr, hPl] at hmidD
    have hmem : lerp ztobd ztobc ztcn ∈
        Chazelle.segment ztobc ztobd := by
      rw [Chazelle.Geometry.segment_comm]
      exact lerp_mem_segment _ _ by_norm_num by_norm_num
    obtain ⟨q, hq, τ, hτ0, hτ1, hzq, -⟩ := hseg _ hmem
    have hbd : lerp ztobd ztobc ztcn ∈ M.W.boundary := by
      rw [hzq]; exact sidePt_mem_boundary hq hτ0 hτ1.le
    have hWb : M.W.boundary = Q.boundary := (FactsInterior.interiorWalk_spec hQ).2.1
    rw [hWb] at hbd
    exact hmidD.2 hbd
  grind

/-- **H1: the host polygon of a region of an interior submap is simple.**  For a simple polygon
`Q`, a nonempty chord family `F` of the interior model and a region `U` of `F`, the walk points
of the host keys of `U`, in increasing key order, form a simple polygon (the boundary `R*` of
`U`). -/
theorem hostPts_simple (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q F)
    (hne : F.Nonempty) (hU : U ∈ (interiorModel Q).regions F) :
    (⟨hostPts ztd F U⟩ : Polygon).Simple := by
  zqblt
  have hWspec := FactsInterior.interiorWalk_spec hQ
  zuccw
  set L := hostKeyList M F U with hLdef
  have hL : L = hS.toFinset.sort _ := hostKeyList_eq hS
  have hmemL : ∀ x, x ∈ L ↔ x ∈ hostKeys M F U := by
    intro x; rw [hL, Finset.mem_sort, Set.Finite.mem_toFinset]
  have hsorted : L.Pairwise ztkhr := by zvnlm; simp
  have hnodup : L.Nodup := by zvnlm; simp
  set N := L.length with hN
  have hmono : ∀ i j, i < j → j < N → L.getD i 0 < L.getD j 0 := by
    zulna
    rw [List.getD_eq_getElem _ _ by_omega, List.getD_eq_getElem _ _ hj]
    refine lt_of_le_of_ne (List.pairwise_iff_getElem.1 hsorted i j by_omega hj hij) ?_
    grind
  have hN3 : ztkzq := by
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := three_le hQ hFam hne hU
    rw [hN, hL, Finset.length_sort]
    exact Finset.two_lt_card.2 ⟨x, by_simp_all, y, by_simp_all, z, by_simp_all,
      hxy, hxz, hyz⟩
  set κ : ℕ → ℝ := fun i => L.getD i 0 with hκ
  have hinj : ∀ i j, i < N → j < N → κ i = κ j → i = j := by
    simp_all
  have hκmem : ∀ i, i < N → κ i ∈ hostKeys M F U := by
    grind
  have hsucc : ∀ i, i < N → ztg % N < N := fun i _ => Nat.mod_lt _ by_omega
  have hVlen : (hostPts M F U).length = N := by simp [hostPts, hLdef, hN]
  have hVget : ∀ i, i < N → (hostPts M F U).getD i ztdr = hostPt M.W ztmpo := by
    zug
    have hi' : i < (hostPts M F U).length := by_omega
    zujgq
    simp only [hostPts, List.getElem_map, hκ]
    zuews
  have hWb : M.W.boundary = Q.boundary := hWspec.2.1
  have hbd : ∀ z ∈ M.D, z ∉ M.W.boundary := by
    intro z hz hzb; rw [hWb] at hzb; exact hz.2 hzb
  -- the classification of the edges
  have hcases : ∀ i, i < N →
      (∀ z ∈ Chazelle.segment ztczs ztwng,
        ∃ p, p < M.W.n ∧ ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ z = sidePt M.W p t ∧
          InKeyIv κ N i ztdj) ∨
      (∃ c ∈ F, c = Chazelle.segment ztczs ztwng ∧
        (∀ s ∈ Ioo (0 : ℝ) 1,
          lerp ztczs ztwng s ∈ M.D) ∧
        (∃ (p : ℕ) (t : ℝ), SideAttach M.W c p t ∧ (p : ℝ) + t = κ i) ∧
        (∃ (p : ℕ) (t : ℝ), SideAttach M.W c p t ∧ (p : ℝ) + t = κ ztxan) ∧
        ∀ (p : ℕ) (t : ℝ), SideAttach M.W c p t →
          (p : ℝ) + t = κ i ∨ (p : ℝ) + t = κ ztxan) := by
    zug
    zukfq
    have hab : κ i ≠ κ _ := fun h => by
      have := hinj _ _ hi hsi h
      zuhsn
      · zufu
      · rw [show i + 1 = N by omega, Nat.mod_self] at this; omega
    have hgapS : ∀ x ∈ hostKeys M F U, ¬ sideInArc ztmpo ztbasr x :=
      fun x hx => sorted_gap hmono by_omega hi by_grind
    rcases gap hM hF hfin hne hU ztjyf zttow hab hgapS with
      ⟨a', b', harc', hsub⟩ | ⟨c, hc, p, p', t, t', hA, hB, ha, hb, hAB⟩
    · left
      have hnv : ∀ k : ℕ, k < M.W.n → ¬ sideInArc _ _ k :=
        fun k hk hkin => hgapS k (Or.inr ⟨k, hk, rfl, a', b', harc', hsub k hkin⟩) hkin
      have hb1 := hostKeys_bounds ztjyf
      have hb2 := hostKeys_bounds zttow
      zugh
      obtain ⟨p, hp, t, ht0, ht1, hzp, hkey⟩ :=
        arcEdge_of_noVertex M.W hb1.1 hb1.2 hb2.1 hb2.2 hab hnv z hz
      refine ⟨p, hp, t, ht0, ht1, hzp, ?_⟩
      unfold InKeyIv
      zuhsn
      · zubel
        zvnnn at hkey
        grind
      · zubmd
        rw [show i + 1 = N by omega, Nat.mod_self] at hkey
        grind
    · right
      have hPa : hostPt M.W ztmpo = sidePt M.W p t := by rw [ha, hostPt_eq M.W hA.2.1 hA.2.2.1]
      have hPb : hostPt M.W ztbasr = sidePt M.W p' t' := by
        zubyq
      zubbw
      rw [hPa, hPb]
      refine ⟨c, hc, hcab, hopen, ⟨p, t, hA, ha.symm⟩, ⟨p', t', hB, hb.symm⟩, ?_⟩
      intro pc tc hC
      zucpu
      exact attach_key_cases hM ztlz hA hB hAB hC
  -- an edge of the chord kind is not an arc edge
  have hnotarc : ∀ i, i < N →
      (∀ s : ℝ, 0 < s → s < 1 →
        lerp ztczs ztwng s ∈ M.D) →
      ¬ (∀ z ∈ Chazelle.segment ztczs ztwng,
        ∃ p, p < M.W.n ∧ ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ z = sidePt M.W p t ∧
          InKeyIv κ N i ztdj) := by
    intro i hi hD harc
    obtain ⟨p, hp, t, ht0, ht1, hzp, -⟩ := harc _ (lerp_mem_segment _ _ (show (0 : ℝ) ≤ 1 / 2 by
      norm_num) by_norm_num)
    exact hbd _ (hD _ by_norm_num by_norm_num)
      ztpcg
  refine KeyHost.simple (W := M.W) (pp := fun i => ⌊κ i⌋₊)
    (tt := fun i => κ i - ⌊κ i⌋₊) ⟨?_, hWspec.1, ?_, ?_, ?_, ?_, ?_, hbd, ?_, ?_⟩
  · omega
  · zqblr
    have hb := hostKeys_bounds ztjyf
    zuepf
    zufc
  · zqblr
    have hb := hostKeys_bounds ztjyf
    show 0 ≤ κ i - ⌊κ i⌋₊
    linarith [Nat.floor_le hb.1]
  · zuhgt
    show κ i - ⌊κ i⌋₊ < 1
    linarith [Nat.lt_floor_add_one ztmpo]
  · zqblr
    tauto
  · zulna
    rw [hVlen] at hj
    unfold keyOf; grind
  · zqblr
    unfold ArcEdge ChordEdge keyOf
    simp only [add_sub_cancel]
    rw [hVlen, hVget i hi, hVget _ by_grind]
    rcases hcases i hi with h | ⟨c, -, -, hopen, -⟩
    · grind
    · exact Or.inr fun s hs0 hs1 => hopen s ztdxi
  · intro i j hi hj hij hci hcj s s' hs0 hs1 hs0' hs1'
    rw [hVlen] at hi hj
    unfold ChordEdge at hci hcj
    rw [hVlen] at hci hcj ⊢
    rw [hVget i hi, hVget _ (hsucc i hi)] at hci ⊢
    rw [hVget j hj, hVget _ (hsucc j hj)] at hcj ⊢
    rcases hcases i hi with h | ⟨ci, hci', hcieq, -, ⟨pi₁, ti₁, hAi₁, hki₁⟩, ⟨pi₂, ti₂, hAi₂, hki₂⟩,
      hallI⟩
    · exact absurd h (hnotarc i hi hci)
    rcases hcases j hj with h | ⟨cj, hcj', hcjeq, -, ⟨pj₁, tj₁, hAj₁, hkj₁⟩, ⟨pj₂, tj₂, hAj₂, hkj₂⟩,
      hallJ⟩
    · exact absurd h (hnotarc j hj hcj)
    zudii
    by_cases hcc : ci = cj
    · zulat
      have e1 := hallI pj₁ tj₁ hAj₁
      have e2 := hallI pj₂ tj₂ hAj₂
      rw [hkj₁] at e1
      rw [hkj₂] at e2
      have hsj := hsucc j hj
      zukfq
      refine pair_ne hN3 hi hj hij ?_ ?_
      · zukkj
        · exact Or.inl (hinj _ _ hj hi e)
        · exact Or.inr (hinj _ _ hj hsi e)
      · zukkk
        · exact Or.inl (hinj _ _ hsj hi e)
        · exact Or.inr (hinj _ _ hsj hsi e)
    · have hz1 : lerp ztczs ztwng s ∈ ci := by
        rw [hcieq]; exact lerp_mem_segment _ _ hs0.le hs1.le
      have hz2 : lerp (hostPt M.W (κ j)) (hostPt M.W (κ ztwwp)) s' ∈ cj := by
        rw [hcjeq]; exact lerp_mem_segment _ _ hs0'.le hs1'.le
      zvnbk at hz1
      exact chord_disj hM hF hfin hci' hcj' hcc hz1 hz2 (hcj s' hs0' hs1')
end
end DownHost
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqbcj" : tactic => `(tactic| (set M := chainModel J.whole with hMdef
                                           set M' := chainModel C' with hM'def
                                           have hM : ztgpz := walkAx_chainModel hP))
local macro "zqbck" : tactic => `(tactic| (rw [← hp₁, ← ht₁] at hA₁
                                           exact ⟨c', hc', hA₁⟩))
local macro "zqbcl" : tactic => `(tactic| have hs0 : ztcfv := hs3)
local macro "zqbcm" : tactic => `(tactic| (obtain ⟨hp, htt⟩ := Chazelle.Chain.sideKey_inj ht.1.le ht.2 hA₀.2.1 hA₀.2.2.1 hk₀
                                           rw [← hp, ← htt] at hA₀))
local macro "zqbcn" : tactic => `(tactic| exact ⟨e, he, hA.sideAttach_subset hn hn' hd hdt' hc hec hqe, hec⟩)
local macro "zqbco" : tactic => `(tactic| exact eq_of_ends hM ztvtv hfc hcuw by_grind by_grind)
local macro "zqbcp" : tactic => `(tactic| (intro e; have := congrArg Prod.fst e; zvnap at this; linarith))
local macro "zqbcq" : tactic => `(tactic| obtain ⟨hg, hg', hLn, hLn', hA, -⟩ := hpc)
local macro "zqbcr" : tactic => `(tactic| (have hn' : 0 < (chainModel C').W.n := by rw [WalkEmbed.cm_n]; omega))
set_option hygiene true

/-!
# The degree of the revised fusion, part 3: pieces and the one-region-per-piece argument

Let `J` be a junction, `C = J.whole`, `S' = J.fusion S₁ S₂ ∪ glueChords J`, and let a *piece* be a
stretch of the walk `W` of `C` agreeing with the walk `W'` of a side chain `C'` (`PieceAt`).

* `chord_transfer`: a chord of `Sᵢ` attached at a position of a piece gives a chord of `S'`
  attached at the same offset and contained in it (the fused chord at its endpoint, or a shared
  chord).
* `one_piece`: **the positions of one region `R` of `S'` inside a piece all face one region of
  `Sᵢ`** — a chord of `Sᵢ` separating two of them would give a chord of `S'` separating them.
-/
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft TouchesIn)
open Chazelle.Visibility (rayPt)
open Chazelle.Geometry (lerp)
open WalkEmbed FuseMath
namespace FuseDeg
variable (J : Merge.Junction)

/-- **A piece**: the walk of `C` from vertex `g` and the walk of the side chain `C'` from vertex
`g'` agree along `L` edges, and counted edges of the first are counted edges of the second. -/
def PieceAt (C' : Chain) (g g' L : ℕ) : Prop :=
  g < (chainModel J.whole).W.n ∧ g' < (chainModel C').W.n ∧ L < (chainModel J.whole).W.n ∧
    L ≤ (chainModel C').W.n ∧ Agree (chainModel J.whole).W (chainModel C').W g g' L ∧
    ∀ d, d < L → (chainModel J.whole).counted ztwmx →
      (chainModel C').counted ztwqv

/-- **Chord transfer along an agreement**: a chord of `Sᵢ` attached at an offset of an agreeing
stretch gives a chord of `S'` attached at the same offset of the walk of `C` and contained in
it. -/
theorem chord_transfer (hP : J.P.Simple) {C' : Chain} (hP' : C'.P.Simple)
    {Si S' : Set ztf} (hsub : Si ⊆ Merge.augChords C')
    (hend : ∀ c ∈ Si, ztqh ∧
      ztqi)
    (hends : ∀ c ∈ Si, Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom)
    (hshared : J.sharedChords ⊆ S')
    {g g' L : ℕ} (hA : Agree (chainModel J.whole).W (chainModel C').W g g' L)
    {d : ℕ} (hd : d < L) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (hdt : 0 < (d : ℝ) + t)
    {c : Set Point} (hcS : c ∈ Si)
    (hc : SideAttach (chainModel C').W c ztwqv t) :
    ∃ f ∈ S', SideAttach (chainModel J.whole).W f ztwmx t ∧
      f ⊆ c := by
  zuog

  have hdt' : ztgaz := fun h => by
    zucpr
  zufal

  have hq := hc.2.2.2.1
  have hqd : ztslh := (walkAx_chainModel hP').trace _ hc.1 t ht ht1.le
  obtain ⟨y, a, b, hH, hy, hceq, hl, hr⟩ := Merge.augChords_spec ztvwj
  have hqe : ztyza := by
    zubwm
    rw [hceq] at hq'
    obtain ⟨hq2, hqa, hqb⟩ := hq'
    zugab
    · zubui
      · exact absurd ztwl
          hqd
      grind
    grind
  zucgw

  · obtain ⟨r, hr0, hsec⟩ := hc.2.2.2.2
    zudoh
    obtain ⟨σ, hσ, hdir, hsubc⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        sideLeft W' p' t ztruz ∧ Merge.shoot J.whole q σ ⊆ c := by
      zuioq
      zusv
      zuchb

      · refine ⟨1, Or.inl rfl, (sideLeft_rayPt hε0).1 ztgke, ?_⟩
        · show rayPt q 1 ε ∈ c
          rw [hceq, hqa]; refine ztkw <;> zvnap <;> linarith
        · zqbcp
        · zuhkz
        · rw [hqa, hceq]
          exact Merge.shoot_subset_pos J.whole hab by_grind
      · refine ⟨-1, Or.inr rfl, (sideLeft_rayPt hε0).1 ztgke, ?_⟩
        · show rayPt q _ ε ∈ c
          rw [hceq, hqb]; refine ztkw <;> zvnap <;> linarith
        · zqbcp
        · zuhky
        · rw [hqb, hceq]
          exact Merge.shoot_subset_neg J.whole hab by_grind
    have hl2 : ztbalp := by
      zuika
    zuerm

    obtain ⟨hfree, hAt⟩ := sideAttach_shoot hP zthp ht ht1 hσ
      ztlid hl2
    zujjw
    refine ⟨_, hshared ztbkb, hAt, ?_⟩
    have e := hv.symm
    show Merge.shoot J.whole _ σ ⊆ c
    grind
  · zudrf

    · zuchs

      zqbcn
    · zucht

      zqbcn
variable {M : Model}
/-- The endpoints of an admissible chord are its only points off the domain. -/
theorem seg_end (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) :
    ∃ u w : Point, c = Chazelle.segment u w ∧ ∀ z ∈ c, z ∉ M.D → z = u ∨ z = w := by
  obtain ⟨u, w, -, hcuw, -, hopc, -, -⟩ := hM.ends c hc
  refine ⟨u, w, hcuw, fun z hz hzD => ?_⟩
  rw [hcuw] at hz
  zuje
  zunl
  · zuqy
    · simp_all
    simp_all
  · zuhha

/-- An admissible chord contained in another and containing both of its endpoints is equal to
it. -/
theorem eq_of_ends (hM : WalkAx M) {f c : Set Point} (hf : f ∈ M.Adm)
    (hfc : f ⊆ c) {u w : Point} (hcuw : c = Chazelle.segment u w) (hu : u ∈ f) (hw : w ∈ f) :
    f = c := by
  obtain ⟨a, b, -, hfab, -⟩ := hM.ends f hf
  refine le_antisymm hfc ?_
  rw [hcuw]
  exact Geometry.segment_subset_of_convex (hfab ▸ Geometry.segment_convex a b) hu hw

/-- **The core of `one_piece`**: no chord of `Sᵢ` separates the side positions of two non-cut
positions of a piece faced by one region of `S'`. -/
theorem one_piece_core (hP : J.P.Simple) {C' : Chain} (hP' : C'.P.Simple) {Q : Polygon}
    {Si S' : Set ztf} (hSi : (chainModel C').ChordFamily Q Si)
    (hS'A : S' ⊆ (chainModel J.whole).Adm) (hS' : S'.Finite)
    (hend : ∀ c ∈ Si, ztqh ∧
      ztqi)
    (hends : ∀ c ∈ Si, Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom)
    (hshared : J.sharedChords ⊆ S')
    {g g' L : ℕ} (hpc : PieceAt J C' g g' L) {R : Set Point}
    (hR : R ∈ (chainModel J.whole).regions S')
    {d₁ d₂ : ℕ} {t₁ t₂ : ℝ} (hd₁ : d₁ < L) (hd₂ : d₂ < L) (ht₁ : t₁ ∈ Ioo (0 : ℝ) 1)
    (ht₂ : t₂ ∈ Ioo (0 : ℝ) 1) (hlt : (d₁ : ℝ) + t₁ < d₂ + t₂)
    (hc₁ : ¬ (chainModel J.whole).IsCut S' ztxqh)
    (hc₂ : ¬ (chainModel J.whole).IsCut S' ztxqj)
    (hf₁ : (chainModel J.whole).Faces ztysk t₁ R)
    (hf₂ : (chainModel J.whole).Faces ztysv t₂ R)
    {c : Set Point} (hc : c ∈ Si)
    (hsep : (chainModel C').Separates c ((zthhk % (chainModel C').W.n : ℕ) + t₁)
      ((ztjwx % (chainModel C').W.n : ℕ) + t₂)) : False := by
  zqbcq
  zqbcj
  have hM' := walkAx_chainModel hP'
  zucqo
  zukzv
  zuqi
  zucau

  have hkey : ∀ {N p : ℕ}, p < N → ∀ {t : ℝ}, 0 ≤ t → t < 1 →
      0 ≤ (p : ℝ) + t ∧ (p : ℝ) + t < N := by
    intro N p hp t ht ht1
    have : (p : ℝ) + 1 ≤ N := by exact_mod_cast hp
    exact ztomv
  have hLR : ztdrn := fun {d t} hd ht => by
    zuhve

  have hdL : ∀ {d : ℕ} {t : ℝ}, 0 ≤ t → (d : ℝ) + t < d₂ + t₂ → d < L := fun {d t} ht h => by
    have h' := hLR hd₂ ht₂.2
    zulgs
    zufc
  set k₁ : ℝ := (ztcac % n : ℕ) + t₁ with hk₁
  set k₂ : ℝ := (ztdur % n : ℕ) + t₂ with hk₂
  set k₁' : ℝ := (zthhk % n' : ℕ) + t₁ with hk₁'
  set k₂' : ℝ := (ztjwx % n' : ℕ) + t₂ with hk₂'
  have ho₁ : off n g k₁ = d₁ + t₁ := off_key hg by_omega ht₁.1.le ht₁.2
  have ho₂ : off n g k₂ = d₂ + t₂ := off_key hg by_omega ht₂.1.le ht₂.2
  have ho₁' : off n' g' k₁' = d₁ + t₁ := off_key hg' by_omega ht₁.1.le ht₁.2
  have ho₂' : off n' g' k₂' = d₂ + t₂ := off_key hg' by_omega ht₂.1.le ht₂.2
  have hK₁ := hkey (Nat.mod_lt ztcac hn) ht₁.1.le ht₁.2
  have hK₂ := hkey ztzun ht₂.1.le ht₂.2
  have hK₁' := hkey (Nat.mod_lt zthhk hn') ht₁.1.le ht₁.2
  have hK₂' := hkey (Nat.mod_lt ztjwx hn') ht₂.1.le ht₂.2
  -- the side positions are not cuts of `Sᵢ`
  have hnc : ∀ {d : ℕ} {t : ℝ}, d < L → t ∈ Ioo (0 : ℝ) 1 →
      ¬ M.IsCut S' ztwuf → ¬ M'.IsCut Si ((zthr % n' : ℕ) + t) := by
    rintro d t hd ht hnc ⟨c₀, hc₀, p₀, t₀, hA₀, hk₀⟩
    zqbcm
    obtain ⟨f, hf, hAf, -⟩ := chord_transfer J hP hP' hSi.2.1 hend hends hshared hA hd ht.1.le
      ht.2 (by have := ht.1; positivity) hc₀ hA₀
    exact hnc ztkky
  have hnc₁ := hnc hd₁ ht₁ hc₁
  have hnc₂ := hnc hd₂ ht₂ hc₂
  -- the case of a chord of `Sᵢ` with an end strictly between the two positions
  have inside : ∀ {pa pb : ℕ} {ta tb : ℝ}, SideAttach M'.W c pa ta → SideAttach M'.W c pb tb →
      sidePt M'.W pa ta ≠ sidePt M'.W pb tb →
      (sideInArc ztbf ztbd k₁' ↔ ¬ sideInArc ztbf ztbd k₂') →
      (d₁ : ℝ) + t₁ < off n' g' ztbf → off n' g' ztbf < d₂ + t₂ → False := by
    intro pa pb ta tb hA' hB' hne hiff h1 h2
    set dA := dOf n' g' pa with hdA
    have hpa := add_dOf hg' hA'.1
    have hoA : off n' g' _ = dA + ta := off_key' hg' hA'.1 hA'.2.1 hA'.2.2.1
    rw [hoA] at h1 h2
    have hdAL := hdL hA'.2.1 h2
    have hA'' : SideAttach M'.W c ((g' + dA) % n') ta := by_grind
    have hdA0 : (0 : ℝ) < dA + ta := by zunff
    obtain ⟨f, hf, hAf, hfc⟩ := chord_transfer J hP hP' hSi.2.1 hend hends hshared hA hdAL
      hA'.2.1 hA'.2.2.1 hdA0 hc hA''
    obtain ⟨pf, tf, hBf, hBfne⟩ := hM.other_attach ztvtv hAf
    have hoA_W : off n g _ = dA + ta :=
      off_key hg by_omega hA'.2.1 hA'.2.2.1
    have hKA := hkey (Nat.mod_lt zttkn hn) hA'.2.1 hA'.2.2.1
    have hKF := hkey hBf.1 hBf.2.1 hBf.2.2.1
    have hofk : off n g _ = dOf n g pf + tf := off_key' hg hBf.1 hBf.2.1 hBf.2.2.1
    -- the other end of `f` is outside the interval of the two positions
    have hof : off n g ztbbc < d₁ + t₁ ∨ d₂ + t₂ < off n g ztbbc := by
      zubaj

      obtain ⟨hlo, hhi⟩ := hno
      have hf1 : (pf : ℝ) + tf ≠ k₁ := fun h => hc₁ ztkkz
      have hf2 : (pf : ℝ) + tf ≠ k₂ := fun h => hc₂ ztkkz
      have hlo' : d₁ + t₁ < off n g _ := lt_of_le_of_ne hlo fun h =>
        hf1 (off_inj ztdys hgR hKF.1 hKF.2 hK₁.1 hK₁.2 by_grind)
      have hhi' : off n g _ < d₂ + t₂ := lt_of_le_of_ne hhi fun h =>
        hf2 (off_inj ztdys hgR hKF.1 hKF.2 hK₂.1 hK₂.2 by_grind)
      set dF := dOf n g pf with hdF
      have hpf := add_dOf hg hBf.1
      rw [hofk] at hlo' hhi'
      have hdFL := hdL hBf.2.1 hhi'
      have hBf' : SideAttach M.W f ((g + dF) % n) tf := by_grind
      have hdF1 : tf = 0 → 1 ≤ dF := by
        zubww
        rw [h0, add_zero] at hlo'
        have : (0 : ℝ) < dF := by zunff
        zufc
      have hBi :=
        (hA.sideAttach_iff hn hn' hdFL hdF1 f).1 hBf'
      have hptF :=
        hA.sidePt_eq hdFL tf
      have hptA :=
        hA.sidePt_eq hdAL ta
      obtain ⟨u, w, hcuw, hends2⟩ := seg_end hM' ztqpq
      have hzA := hends2 _ hA'.2.2.2.1 (hM'.trace pa hA'.1 ta hA'.2.1 hA'.2.2.1.le)
      have hzB := hends2 _ hB'.2.2.2.1 (hM'.trace pb hB'.1 tb hB'.2.1 hB'.2.2.1.le)
      have hzF := hends2 _ (hfc hBi.2.2.2.1)
        (hM'.trace _ hBi.1 tf hBi.2.1 hBi.2.2.1.le)
      have hAF : sidePt M'.W pa ta ≠ sidePt M'.W ztmyx tf := by
        grind
      have hBF : sidePt M'.W pb tb = sidePt M'.W ztmyx tf := by
        rcases hzA with h | h <;> rcases hzB with h' | h' <;> rcases hzF with h'' | h''
        all_goals first | exact h'.trans h''.symm | (exfalso; exact by_grind) |
          (exfalso; exact by_grind)
      -- `f` contains both ends of `c`, so `f = c`
      have hAf' : sidePt M'.W pa ta ∈ f := by
        rw [← hpa, ← hptA]; exact hAf.2.2.2.1
      have hFf : sidePt M'.W _ tf ∈ f := hBi.2.2.2.1
      have hfeq : f = c := by
        rcases hzA with h | h <;> rcases hzF with h'' | h''
        · grind
        · zqbco
        · zqbco
        grind
      rw [hfeq] at hBi
      obtain ⟨hpb, htb⟩ := hM'.attach_unique ztqpq hB' hBi hBF
      have hoB : off n' g' ztbd = dF + tf := by
        rw [hpb, htb]; exact off_key hg' by_omega hBi.2.1 hBi.2.2.1
      zuego

      have hsame := off_same_side_in ztqak hg'R hKA'.1 hKA'.2 hKB'.1 hKB'.2
        hK₁'.1 hK₁'.2 hK₂'.1 hK₂'.2 (Chazelle.Core.WalkAx.key_ne_of_pt_ne hA' hB' hne)
        by_grind
        by_grind
      grind
    -- so `f` separates the two positions in the walk of `C`
    have hsepf : M.Separates f k₁ k₂ := by
      refine ⟨zttkn % n, pf, ta, tf, hAf, hBf, Ne.symm hBfne, ?_⟩
      exact off_sep ztdys hgR hKA.1 hKA.2 hKF.1 hKF.2 hK₁.1 hK₁.2 hK₂.1 hK₂.2
        by_grind
        by_grind
    exact ((hM.eq_iff_not_separates hS'A hS' hR hR zthp zthp ht₁ ht₂
      hc₁ hc₂ hf₁ hf₂).1 rfl) f hf hsepf
  obtain ⟨pa, pb, ta, tb, hA', hB', hne, hiff⟩ := hsep
  zuego

  have hAB := Chazelle.Core.WalkAx.key_ne_of_pt_ne hA' hB' hne
  have hA1 : (pa : ℝ) + ta ≠ k₁' := fun h => hnc₁ ztkjk
  have hA2 : (pa : ℝ) + ta ≠ k₂' := fun h => hnc₂ ztkjk
  have hB1 : (pb : ℝ) + tb ≠ k₁' := fun h => hnc₁ ztkjn
  have hB2 : (pb : ℝ) + tb ≠ k₂' := fun h => hnc₂ ztkjn
  have hoffne : ∀ {x y : ℝ}, 0 ≤ x → x < n' → 0 ≤ y → y < n' → x ≠ y →
      off n' g' x ≠ off n' g' y := fun hx hxn hy hyn hxy h =>
    hxy (off_inj ztqak hg'R hx hxn hy hyn h)
  by_cases hin : (d₁ : ℝ) + t₁ < off n' g' ztbf ∧ off n' g' ztbf < d₂ + t₂
  · exact inside hA' hB' hne hiff hin.1 hin.2
  by_cases hin' : (d₁ : ℝ) + t₁ < off n' g' ztbd ∧ off n' g' ztbd < d₂ + t₂
  · refine inside hB' hA' ztnr ?_ hin'.1 hin'.2
    rw [sideInArc_compl zteno (Ne.symm hB1) ztvao,
      sideInArc_compl zteno (Ne.symm hB2) ztvap]
    grind
  have hA1' := hoffne hKA'.1 hKA'.2 hK₁'.1 hK₁'.2 hA1
  have hA2' := hoffne hKA'.1 hKA'.2 hK₂'.1 hK₂'.2 hA2
  have hB1' := hoffne hKB'.1 hKB'.2 hK₁'.1 hK₁'.2 hB1
  have hB2' := hoffne hKB'.1 hKB'.2 hK₂'.1 hK₂'.2 hB2
  rw [ho₁'] at hA1' hB1'
  rw [ho₂'] at hA2' hB2'
  have hsame := off_same_side ztqak hg'R hKA'.1 hKA'.2 hKB'.1 hKB'.2
    hK₁'.1 hK₁'.2 hK₂'.1 hK₂'.2 hAB by_grind
    (by
      zukvj
      zufm
      exact hin ztsr)
    (by
      zukvj
      zufm
      exact hin' ztsr)
  grind

/-- A non-cut position of a piece has a non-cut side position. -/
theorem side_not_cut (hP : J.P.Simple) {C' : Chain} (hP' : C'.P.Simple)
    {Si S' : Set ztf} (hsub : Si ⊆ Merge.augChords C')
    (hend : ∀ c ∈ Si, ztqh ∧
      ztqi)
    (hends : ∀ c ∈ Si, Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom)
    (hshared : J.sharedChords ⊆ S')
    {g g' L : ℕ} (hA : Agree (chainModel J.whole).W (chainModel C').W g g' L)
    {d : ℕ} (hd : d < L) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hnc : ¬ (chainModel J.whole).IsCut S' ztwvv) :
    ¬ (chainModel C').IsCut Si ztxqk := by
  rintro ⟨c₀, hc₀, p₀, t₀, hA₀, hk₀⟩
  zqbcm
  obtain ⟨f, hf, hAf, -⟩ := chord_transfer J hP hP' hsub hend hends hshared hA hd ht.1.le
    ht.2 (by have := ht.1; positivity) hc₀ hA₀
  exact hnc ztkky
theorem separates_symm {M : Model} {c : Set Point} {x y : ℝ} (h : M.Separates c x y) :
    M.Separates c y x := by
  obtain ⟨pa, pb, ta, tb, hA, hB, hne, hiff⟩ := h
  refine ⟨pa, pb, ta, tb, hA, hB, hne, ?_⟩
  simp_all

/-- **One region of `Sᵢ` per piece**: two non-cut positions of a piece faced by one region of
`S'` have side positions facing one region of `Sᵢ`. -/
theorem one_piece (hP : J.P.Simple) {C' : Chain} (hP' : C'.P.Simple) {Q : Polygon}
    {Si S' : Set ztf} (hSi : (chainModel C').ChordFamily Q Si)
    (hS'A : S' ⊆ (chainModel J.whole).Adm) (hS' : S'.Finite)
    (hend : ∀ c ∈ Si, ztqh ∧
      ztqi)
    (hends : ∀ c ∈ Si, Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom)
    (hshared : J.sharedChords ⊆ S')
    {g g' L : ℕ} (hpc : PieceAt J C' g g' L) {R : Set Point}
    (hR : R ∈ (chainModel J.whole).regions S')
    {d₁ d₂ : ℕ} {t₁ t₂ : ℝ} (hd₁ : d₁ < L) (hd₂ : d₂ < L) (ht₁ : t₁ ∈ Ioo (0 : ℝ) 1)
    (ht₂ : t₂ ∈ Ioo (0 : ℝ) 1)
    (hc₁ : ¬ (chainModel J.whole).IsCut S' ztxqh)
    (hc₂ : ¬ (chainModel J.whole).IsCut S' ztxqj)
    (hf₁ : (chainModel J.whole).Faces ztysk t₁ R)
    (hf₂ : (chainModel J.whole).Faces ztysv t₂ R)
    {U₁ U₂ : Set Point} (hU₁ : U₁ ∈ (chainModel C').regions Si)
    (hU₂ : U₂ ∈ (chainModel C').regions Si)
    (hg₁ : (chainModel C').Faces (zthhk % (chainModel C').W.n) t₁ U₁)
    (hg₂ : (chainModel C').Faces (ztjwx % (chainModel C').W.n) t₂ U₂) : U₁ = U₂ := by
  have hA := hpc.2.2.2.2.1
  zqbcr
  have hnc₁ := side_not_cut J hP hP' hSi.2.1 hend hends hshared hA hd₁ ht₁ hc₁
  have hnc₂ := side_not_cut J hP hP' hSi.2.1 hend hends hshared hA hd₂ ht₂ hc₂
  refine ((walkAx_chainModel hP').eq_iff_not_separates hSi.2.1 hSi.1 hU₁ hU₂ ztdtl
    ztdtl ht₁ ht₂ hnc₁ hnc₂ hg₁ hg₂).2 fun c hc hsep => ?_
  rcases lt_trichotomy ((d₁ : ℝ) + t₁) (d₂ + t₂) with h | h | h
  · exact one_piece_core J hP hP' hSi hS'A hS' hend hends hshared hpc hR hd₁ hd₂ ht₁ ht₂ h
      hc₁ hc₂ hf₁ hf₂ hc hsep
  · obtain ⟨rfl, rfl⟩ := Chazelle.Chain.sideKey_inj ht₁.1.le ht₁.2 ht₂.1.le ht₂.2 h
    obtain ⟨pa, pb, ta, tb, hA0, hB0, hne0, hiff0⟩ := hsep
    simp_all
  · exact one_piece_core J hP hP' hSi hS'A hS' hend hends hshared hpc hR hd₂ hd₁ ht₂ ht₁ h
      hc₂ hc₁ hf₂ hf₁ hc (separates_symm hsep)

/-- The data of one side of the junction used by the piece arguments. -/
structure SideOK (C' : Chain) (Q : Polygon) (Si S' : Set ztf) : Prop where
  simple : C'.P.Simple
  fam : (chainModel C').ChordFamily Q Si
  endm : ∀ c ∈ Si, ztqh ∧
    ztqi
  ends : ∀ c ∈ Si, Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom
  shared : J.sharedChords ⊆ S'
  adm : S' ⊆ (chainModel J.whole).Adm
  fin : S'.Finite

/-- A faced non-cut position of a piece has its side position facing the region `U` of `Sᵢ`
faced at one reference position. -/
theorem faces_ref (hP : J.P.Simple) {C' : Chain} {Q : Polygon} {Si S' : Set ztf}
    (hS : SideOK J C' Q Si S') {g g' L : ℕ} (hpc : PieceAt J C' g g' L) {R : Set Point}
    (hR : R ∈ (chainModel J.whole).regions S') {d₀ : ℕ} {t₀ : ℝ} (hd₀ : d₀ < L)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ (chainModel J.whole).IsCut S' ztxqi)
    (hf₀ : (chainModel J.whole).Faces ztysp t₀ R)
    {U : Set Point} (hU : U ∈ (chainModel C').regions Si)
    (hg₀ : (chainModel C').Faces ztjck t₀ U)
    {d : ℕ} {t : ℝ} (hd : d < L) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hnc : ¬ (chainModel J.whole).IsCut S' ztwvv)
    (hf : (chainModel J.whole).Faces ztwmx t R) :
    (chainModel C').Faces ztwqv t U := by
  zqbcr
  have hnc' := side_not_cut J hP hS.simple hS.fam.2.1 hS.endm hS.ends hS.shared hpc.2.2.2.2.1 hd ht
    hnc
  obtain ⟨U₁, hU₁, hg₁⟩ := (walkAx_chainModel hS.simple).exists_faces_of_not_cut hS.fam.2.1
    hS.fam.1 ztdtl ht hnc'
  rw [one_piece J hP hS.simple hS.fam hS.adm hS.fin hS.endm hS.ends hS.shared hpc hR hd hd₀ ht ht₀
    hnc hnc₀ hf hf₀ hU₁ hU hg₁ hg₀] at hg₁
  omega

/-- **The positions of type (I)**: at a position of a piece next to which `R` is faced and at
whose side position a chord of `Sᵢ` is attached, some exit chord of the region `U` of `Sᵢ` faced
by `R`'s positions in the piece is attached. -/
theorem piece_I (hP : J.P.Simple) {C' : Chain} {Q : Polygon} {Si S' : Set ztf}
    (hS : SideOK J C' Q Si S') {g g' L : ℕ} (hpc : PieceAt J C' g g' L) {R : Set Point}
    (hR : R ∈ (chainModel J.whole).regions S') {d₀ : ℕ} {t₀ : ℝ} (hd₀ : d₀ < L)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ (chainModel J.whole).IsCut S' ztxqi)
    (hf₀ : (chainModel J.whole).Faces ztysp t₀ R)
    {U : Set Point} (hU : U ∈ (chainModel C').regions Si)
    (hg₀ : (chainModel C').Faces ztjck t₀ U)
    {d : ℕ} {t : ℝ} (hd : d < L) (ht0 : 0 ≤ t) (ht1 : t < 1) (hdt : 0 < (d : ℝ) + t)
    (hne : S'.Nonempty)
    (hadj : Adj ztbm S' R ztwmx t)
    {c : Set Point} (hc : c ∈ Si)
    (hcA : SideAttach (chainModel C').W c ztwqv t) :
    ∃ c' ∈ exits ztbmo Si U,
      SideAttach (chainModel C').W c' ztwqv t := by
  zqbcj
  zuhek
  have hn : ztbiy := by rw [hMdef, WalkEmbed.cm_n]; omega
  have hn' : ztrzf := by rw [hM'def, WalkEmbed.cm_n]; omega
  zuioh
  set p' := zthr % M'.W.n with hp'
  have hfaced : ∀ {d₁ : ℕ} {t₁ : ℝ}, d₁ < L → t₁ ∈ Ioo (0 : ℝ) 1 →
      ¬ M.IsCut S' ztxdh → M.Faces ztxyu t₁ R →
      M'.Faces (zthhk % M'.W.n) t₁ U :=
    (faces_ref J hP hS hpc hR hd₀ ht₀ hnc₀ hf₀ hU hg₀)
  zuejs
  · zuegk
    have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), M'.Faces p' ztuf U := by
      filter_upwards [h1, eventually_not_cut_after hM hS.adm hS.fin ztdj,
        self_mem_nhdsWithin, Ioo_mem_nhdsGT ztcqc]
        with s hs1 hs2 hs3 hs4
      zqbcl
      refine hfaced hd ztomq ?_ hs1
      grind
    obtain ⟨r', harc'⟩ := arc_start_of_faced hM' hS.fam.2.1 hS.fam.1 hc hcA hU h2
    obtain ⟨c', hc', p₁, t₁, hA₁, hk⟩ :=
      hM'.exists_exit_at_start hS.fam.2.1 hS.fam.1 ztzx hU harc'
    obtain ⟨hp₁, ht₁⟩ := Chazelle.Chain.sideKey_inj ht0 ht1 hA₁.2.1 hA₁.2.2.1 hk
    zqbck
  · zucox
    · zuegl
      have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), M'.Faces p' ztfuw U := by
        filter_upwards [h1, eventually_not_cut_before hM hS.adm hS.fin ztdj,
          self_mem_nhdsWithin, Ioo_mem_nhdsGT ht0'] with s hs1 hs2 hs3 hs4
        zqbcl
        refine hfaced hd by_grind ?_ hs1
        grind
      obtain ⟨l', harc'⟩ := arc_end_of_faced hM' hS.fam.2.1 hS.fam.1 hc hcA ht0' hU h2
      obtain ⟨c', hc', p₁, t₁, hA₁, hk⟩ :=
        hM'.exists_exit_at_end hS.fam.2.1 hS.fam.1 ztzx hU harc'
      obtain ⟨hp₁, ht₁⟩ := Chazelle.Chain.sideKey_inj ht0 ht1 hA₁.2.1 hA₁.2.2.1 hk
      zqbck
    · zultg
      have hd1 : 1 ≤ d := by
        zulgr
        zufc
      zucvo

      have hpm' :=
        mod_pred_mod hn' g' hd1
      zukvn
      have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), M'.Faces ((p' + M'.W.n - 1) % M'.W.n) zteb U := by
        rw [hpm']
        filter_upwards [h1, eventually_not_cut_before hM hS.adm hS.fin
          ztxfo, self_mem_nhdsWithin, Ioo_mem_nhdsGT one_pos]
          with s hs1 hs2 hs3 hs4
        zqbcl
        refine hfaced by_omega by_grind ?_ hs1
        grind
      obtain ⟨l', harc'⟩ := arc_end_of_faced_zero hM' hS.fam.2.1 hS.fam.1 hc hcA hU h2
      obtain ⟨c', hc', p₁, t₁, hA₁, hk⟩ :=
        hM'.exists_exit_at_end hS.fam.2.1 hS.fam.1 ztzx hU harc'
      obtain ⟨hp₁, ht₁⟩ := Chazelle.Chain.sideKey_inj le_rfl one_pos hA₁.2.1 hA₁.2.2.1 hk
      zqbck

/-- The chords of `S'` of type (I) in a piece: attached at an offset in `(0, L)` next to which `R`
is faced, where a chord of `Sᵢ` is attached at the side position. -/
def TypeI (C' : Chain) (Si S' : Set ztf) (R : Set Point) (g g' L : ℕ) :
    Set ztf :=
  {f | f ∈ S' ∧ ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧ t < 1 ∧ 0 < (d : ℝ) + t ∧
    SideAttach (chainModel J.whole).W f ztwmx t ∧
    Adj ztbm S' R ztwmx t ∧
    ∃ c ∈ Si, SideAttach (chainModel C').W c ztwqv t}

/-- **At most `4 D` chords of type (I) per piece**: their side positions carry exit chords of the
one region of `Sᵢ` faced there (`piece_I`), which has at most `D` exit chords, each attached at
at most two keys. -/
theorem typeI_ncard_le (hP : J.P.Simple) {C' : Chain} {Q : Polygon} {Si S' : Set ztf}
    (hS : SideOK J C' Q Si S') {g g' L : ℕ} (hpc : PieceAt J C' g g' L) {R : Set Point}
    (hR : R ∈ (chainModel J.whole).regions S') {D : ℕ}
    (hdeg : (chainModel C').DegLe Si D) : (TypeI J C' Si S' R g g' L).ncard ≤ 4 * D := by
  zumen
  zqbcq
  zqbcj
  zuhek
  zuiy
  zukea
  rcases (TypeI J C' Si S' R g g' L).eq_empty_or_nonempty with h0 | ⟨f₀, hf₀, d₀', t₀', hd₀',
    ht₀', ht₀'1, hdt₀', -, hadj₀, -⟩
  · simp_all
  have hne : S'.Nonempty := ⟨f₀, hf₀⟩
  -- a reference position and the region of `Sᵢ` it faces
  obtain ⟨d₀, t₀, hd₀, ht₀, hc₀, hf₀'⟩ : ∃ (d₀ : ℕ) (t₀ : ℝ), d₀ < L ∧ t₀ ∈ Ioo (0 : ℝ) 1 ∧
      ¬ M.IsCut S' ((ztdhi % M.W.n : ℕ) + t₀) ∧ M.Faces ztxyw t₀ R := by
    rcases adj_near hM hS.adm hS.fin hne ht₀' ht₀'1 hdt₀' hadj₀ with h | h
    · obtain ⟨d, t, hd, ht, -, -, h3, h4⟩ := h _ (lt_add_one _)
      grind
    grind
  have hnc₀' := side_not_cut J hP hS.simple hS.fam.2.1 hS.endm hS.ends hS.shared hA hd₀ ht₀ hc₀
  obtain ⟨U, hU, hg₀⟩ := hM'.exists_faces_of_not_cut hS.fam.2.1 hS.fam.1 ztdtl ht₀
    hnc₀'
  -- the side keys
  set K' : Set ℝ := {k | ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧ t < 1 ∧ 0 < (d : ℝ) + t ∧
    Adj M S' R ztwje t ∧
    (∃ c ∈ Si, SideAttach M'.W c ztbaag t) ∧ k = (zthr % M'.W.n : ℕ) + t}
    with hK'
  have hcutsfin := hM'.finite_cuts hS.fam.2.1 hS.fam.1
  have hUnion : (⋃ c ∈ exits M' Si U, attKeys M' c) ⊆ {x | M'.IsCut Si x} := by
    zuh
    simp only [Set.mem_iUnion] at hx
    obtain ⟨c, ⟨hc, -⟩, p, t, hAc, rfl⟩ := hx
    exact ⟨c, hc, p, t, hAc, rfl⟩
  have hK'sub : K' ⊆ ⋃ c ∈ exits M' Si U, attKeys M' c := by
    rintro k ⟨d, t, hd, ht, ht1, hdt, hadj, ⟨c, hc, hcA⟩, rfl⟩
    obtain ⟨c', hc', hA'⟩ := piece_I J hP hS hpc' hR hd₀ ht₀ hc₀ hf₀' hU hg₀ hd ht ht1 hdt hne
      hadj hc hcA
    zucqw
    exact ⟨c', hc', _, t, hA', rfl⟩
  have hK'fin := hcutsfin.subset (hK'sub.trans hUnion)
  have hexits : (exits M' Si U).ncard ≤ D := hdeg U hU
  have hK'le : K'.ncard ≤ 2 * D := by
    refine (Set.ncard_le_ncard hK'sub (hcutsfin.subset hUnion)).trans ?_
    refine (ncard_attKeys_union_le hM' (fun c hc => hS.fam.2.1 hc.1)
      (hS.fam.1.subset fun c hc => hc.1)).trans ?_
    omega
  -- the chords at one side key
  have hat : ∀ k : ℝ, {f | f ∈ S' ∧ ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧ t < 1 ∧
      k = (zthr % M'.W.n : ℕ) + t ∧ SideAttach M.W f ztwje t}.ncard ≤ 2 := by
    zugoi
    by_cases h : ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧ t < 1 ∧ k = (zthr % M'.W.n : ℕ) + t
    · obtain ⟨d₁, t₁, hd₁, ht₁, ht₁1, hk₁⟩ := h
      refine le_trans (Set.ncard_le_ncard ?_ (hS.fin.subset fun f hf => hf.1))
        (ncard_at_le hM hS.adm hS.fin ztxyu t₁)
      rintro f ⟨hf, d, t, hd, ht, ht1, hk, hAf⟩
      obtain ⟨hp, rfl⟩ := Chazelle.Chain.sideKey_inj ht ht1 ht₁ ht₁1 (hk.symm.trans hk₁)
      have := add_mod_inj by_grind by_grind hp
      zumo
      exact ⟨hf, hAf⟩
    · have : {f | f ∈ S' ∧ ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧ t < 1 ∧
          k = (zthr % M'.W.n : ℕ) + t ∧ SideAttach M.W f ztwje t} = ∅ := by
        ext f
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_exists]
        intro _ d t hd ht ht1 hk _
        exact h ⟨d, t, hd, ht, ht1, hk⟩
      zuedz
  have hsub : TypeI J C' Si S' R g g' L ⊆ ⋃ k ∈ K', {f | f ∈ S' ∧ ∃ (d : ℕ) (t : ℝ), d < L ∧
      0 ≤ t ∧ t < 1 ∧ k = (zthr % M'.W.n : ℕ) + t ∧
      SideAttach M.W f ztwje t} := by
    rintro f ⟨hf, d, t, hd, ht, ht1, hdt, hAf, hadj, hc⟩
    zucqw
    exact ⟨_, ⟨d, t, hd, ht, ht1, hdt, hadj, hc, rfl⟩, hf, d, t, hd, ht, ht1, rfl, hAf⟩
  calc (TypeI J C' Si S' R g g' L).ncard
      ≤ (⋃ k ∈ K', {f | f ∈ S' ∧ ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧ t < 1 ∧
          k = (zthr % M'.W.n : ℕ) + t ∧ SideAttach M.W f _ t}).ncard :=
        Set.ncard_le_ncard hsub (hS.fin.subset (by
          simp))
    _ ≤ 2 * K'.ncard := ncard_biUnion_le_mul hK'fin _ fun k _ => hat k
    _ ≤ 4 * D := by_omega
