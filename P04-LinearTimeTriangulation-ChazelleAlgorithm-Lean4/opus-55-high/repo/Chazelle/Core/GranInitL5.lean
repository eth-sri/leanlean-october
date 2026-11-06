module

public import Chazelle.MacT
public import Chazelle.Core.GranInitL3
public import Chazelle.Chain.Submap
public import Chazelle.Core.BruteCorner
public import Chazelle.Core.GranRamBody
public import Chazelle.Core.OracleQuery

section
set_option hygiene false
local macro "zqbgr" : tactic => `(tactic| (obtain ⟨a1, a2, a3⟩ := ih₁ hs
                                           obtain ⟨b1, b2, b3⟩ := ih₂ hs
                                           exact by_simp_all))
set_option hygiene true

/-!
# WP-F, init part 10: the ring positions of the chord ends and the counts

For every chord record `i < K`: `nd0 i` and `nd1 i`, the positions of the sequence table whose
start keys are the keys of the two ends of the chord (`posStmt`, a binary search), and the
counts `cnt` of the positions (`ndLoop_exec`).
-/
namespace Chazelle.Core
namespace Gran
open Machine Machine.Stmt Programs SignK
@[expose] public section
def natOK : Instr → Bool
  | .inputSize _ | .constN _ _ | .copyN _ _ | .addN _ _ _ | .subN _ _ _ | .loadN _ _
  | .storeN _ _ => true
  | _ => false

/-- Every instruction of the statement is natural. -/
def natOnly : Stmt → Bool
  | .skip => true
  | .instr i => natOK i
  | .seq s t => natOnly s && natOnly t
  | .ifLtN _ _ t e => natOnly t && natOnly e
  | .ifLtR _ _ t e => natOnly t && natOnly e
  | .whileLtN _ _ b => natOnly b
  | .whileLtR _ _ b => natOnly b
variable {P : Polygon} {W : ℕ}
/-- **A natural-only statement** changes no real register, no real memory and no output. -/
theorem exec_natOnly {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hs : natOnly s = true) :
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  induction h with
  | skip _ => exact by_simp_all
  | @instr ins c c' _ he _ _ =>
    simp only [natOnly] at hs
    cases ins <;> simp only [natOK, Bool.false_eq_true] at hs <;>
      zvncw at he <;>
      subst he <;>
      zufeo
  | seq _ _ ih₁ ih₂ =>
    simp only [natOnly, Bool.and_eq_true] at hs
    obtain ⟨a1, a2, a3⟩ := ih₁ hs.1
    obtain ⟨b1, b2, b3⟩ := ih₂ hs.2
    zufeo
  | ifLtN_true _ _ ih =>
    zufbs
  | ifLtN_false _ _ ih =>
    zufbt
  | ifLtR_true _ _ ih =>
    zufbs
  | ifLtR_false _ _ ih =>
    zufbt
  | whileLtN_false _ _ => exact by_simp_all
  | whileLtN_true _ _ _ ih₁ ih₂ =>
    zqbgr
  | whileLtR_false _ _ => exact by_simp_all
  | whileLtR_true _ _ _ ih₁ ih₂ =>
    zqbgr

/-! ## Counting -/
theorem cntInit_succ (i : ℕ) (f g : ℕ → ℕ) (j : ℕ) :
    cntInit ztg f g j = cntInit i f g j + (if f i = j then 1 else 0) +
      (if g i = j then 1 else 0) := by
  zumse
  rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert]
  have h1 : i ∉ Finset.filter ztnzl ztmbb := by_simp
  have h2 : i ∉ Finset.filter ztnzm ztmbb := by_simp
  split_ifs with a b b
  · rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2]; ring
  · rw [Finset.card_insert_of_notMem h1]; ring
  · rw [Finset.card_insert_of_notMem h2]; ring
  · ring
theorem cntInit_congr {i : ℕ} {f g f' g' : ℕ → ℕ} (hf : ∀ u, u < i → f' u = f u)
    (hg : ∀ u, u < i → g' u = g u) (j : ℕ) : cntInit i f' g' j = cntInit i f g j := by
  zumse
  zugjz
  · zubfo
  · zubfo

/-! ## The program -/

/-- The left end of chord `r70` (`r71 = CB + 5 i`): the query `⟨lp, h + 1⟩`. -/
def ndA : Stmt := block [.copyN 50000 90000, .copyN 50001 90001, .loadN 90090 90071,
  .addN 90091 90090 90019, .addN 90074 90071 90019, .loadN 50002 90074, .copyN 50003 90091]

/-- Store the position `lr 105 - 1` in the array at `r bs` and count it. -/
def ndStore (bs : ℕ) : Stmt := block [.subN 90092 50105 90019, .addN 90072 bs 90070,
  .storeN 90072 90092, .addN 90072 90038 90092, .loadN 90093 90072, .addN 90093 90093 90019,
  .storeN 90072 90093]

/-- The right end: the query `⟨rp, h + 1⟩`. -/
def ndC : Stmt := block [.copyN 50000 90000, .copyN 50001 90001, .addN 90074 90071 90021,
  .loadN 50002 90074, .copyN 50003 90091]

/-- Advance. -/
def ndE : Stmt := block [.addN 90071 90071 90076, .addN 90070 90070 90019]

/-- One chord. -/
def ndBody : Stmt :=
  .seq ndA (.seq (.seq posStmt (ndStore 90033)) (.seq ndC (.seq (.seq posStmt (ndStore 90034)) ndE)))

/-- The chord loop of the positions. -/
def ndLoop : Stmt := .seq zthso
  (.whileLtN 90070 90010 ndBody)

/-- Search and store: the position of the key of `x` into `r bs + i`, counted. -/
def srchStore (bs : ℕ) : Stmt := .seq posStmt (ndStore bs)
theorem band_ne {r : ℕ} (h : 90000 ≤ r) (h' : r < 100000) :
    bandOf r ∉ ({bLocate, bSign} : Finset ℕ) := by
  unfold bandOf bLocate bSign; simp; omega
theorem srchStore_exec {W MD NFH b0 : ℕ} {M : Model} {N : NF} {x : WPos}
    {c : Config} (hw : WordsBounded W c) {bs BS i Cb : ℕ}
    (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (hGM : GoodModel M)
    (hwf : ModelDescWF P b0 c.nmem MD) (hMD : ModelDescAt c.nmem MD zta M)
    (hNW : NFWithin c.nmem NFH b0 N) (hNF : IsNF M zta N) (hne : (N.F M zta).Nonempty)
    (h50 : c.nreg 50000 = MD) (h51 : c.nreg 50001 = NFH) (h52 : c.nreg 50002 = x.edge)
    (h53 : c.nreg 50003 = x.hgt) (hx : ProperPos M zta P.n x) (hx1 : x.hgt ≠ 0)
    (hcut : M.IsCut ztwiv ztwzj) (he : x.edge < M.W.n)
    (hbs : bs ≠ 90072 ∧ bs ≠ 90092 ∧ bs ≠ 90093 ∧ bs ≠ 50105 ∧ bs ≠ 90019 ∧ bs ≠ 90070 ∧
      bs ≠ 90038 ∧ 90000 ≤ bs ∧ bs < 100000)
    (hBS : c.nreg bs = BS) (h70 : c.nreg 90070 = i) (h38 : c.nreg 90038 = Cb)
    (h19 : c.nreg 90019 = 1) (hb0 : b0 ≤ c.nreg ALLOC)
    (hdis : ∀ v, v < N.arcs.length → BS + i ≠ Cb + v)
    (hroom : c.nreg ALLOC + NFLoc.locCost 5100 N.arcs.length ≤ W)
    (hBW : BS + i ≤ W) (hCW : Cb + N.arcs.length ≤ c.nreg ALLOC)
    (hcntW : ∀ v, v < N.arcs.length → c.nmem ztnke + 1 ≤ W) :
    ∃ c' k v, Exec P W (srchStore bs) c c' k ∧ k ≤ NFLoc.locCost 5100 N.arcs.length + 7 ∧
      v < N.arcs.length ∧ pk M zta N v = M.key zta x ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a =
        upd (upd c.nmem ztsvk v) ztnke (c.nmem ztnke + 1) a) ∧
      (∀ r, bandOf r ∉ ({bLocate, bSign} : Finset ℕ) → r ≠ ALLOC → r ≠ 90072 → r ≠ 90092 →
        r ≠ 90093 → c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ ({bLocate, bSign} : Finset ℕ) → c'.rreg r = c.rreg r) ∧
      ztgo ∧ c'.output = c.output ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hbs
  have hA0 : ztrzg := by
    obtain ⟨j, hj, -⟩ := cut_pk hNF hGM hcut; omega
  zuiwo
  obtain ⟨hNB, hNAB, hNSB⟩ := NFLoc.nfWithin_bounds hNW hNF hA0
  obtain ⟨hDW, hCWf⟩ := NFLoc.locChainWF_of hwf by_omega hWh
  zufgh
  have hst : ∀ j, j < N.arcs.length → ProperPos M _ P.n (N.arc j).s := fun j hj => by
    zubtr
    have := (hpp j hj).1
    zuc
    rwa [hQn] at this
  have hxe : x = ztbig := by rw [h52, h53]
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, t0, tlt, tpk⟩ := pos_exec (P := P) (W := W) (c := c) hw
    ⟨hG, hW3, by zunjx; exact hDW, by zunjx; exact hCWf, M, by zunjx; exact hMD,
      by rw [h52]; exact he⟩ hG hW3 (M := M) (N := N) (by zunjx; exact hMD) hGM
    (by zuovg; exact hN) hNF hne (by rw [← hxe]; exact hx) (by zunrx; exact hx1)
    (by rw [← hxe]; exact hcut) hst ztheq ztheq
    ztheq hroom
  rw [← hxe] at tpk
  obtain ⟨fr, frr, fm, frm, fo, fa1, fa2⟩ := F₁
  zud
  have g := fun r h1 h2 =>
    fr r ztnrw ztu
  have c19 : ztgas := by rw [g _ by_norm_num by_norm_num, h19]
  have c70 : c₁.nreg 90070 = i := by rw [g _ by_norm_num by_norm_num, h70]
  have c38 : c₁.nreg 90038 = Cb := by rw [g _ by_norm_num by_norm_num, h38]
  have cbs : c₁.nreg bs = BS := by rw [g _ b8 b9, hBS]
  have hne' := hdis _ tlt
  obtain ⟨c₂, k₂, e₂, hk₂, q⟩ : ∃ c₂ k₂, Exec P W (ndStore bs) c₁ c₂ k₂ ∧ k₂ = 7 ∧
      (c₂.nmem = upd (upd c₁.nmem ztsvk ztlmm) ztztc
        (c₁.nmem ztztc + 1) ∧
        ∀ r, r ≠ 90072 → r ≠ 90092 → r ≠ 90093 → c₂.nreg r = c₁.nreg r) := by
    unfold ndStore
    exec_block
    · simp (disch := omega) only [Machine.upd_other, cbs, c70]
      omega
    · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, c38, c19]
      omega
    · simp (disch := omega) only [Machine.upd_same,
        Machine.upd_other, cbs, c70, c38, c19]
      zumyx
      exact hcntW _ tlt
    · refine ⟨rfl, ?_, fun r a1 a2 a3 => ?_⟩
      · simp (disch := omega) only [Machine.upd_other, cbs, c70, c38, c19]
      · zup
  obtain ⟨q1, q2⟩ := q
  have NO := exec_natOnly e₂ (by simp [ndStore, natOnly, natOK, block])
  have a2' : zteic :=
    q2 _ ztu ztu ztu
  refine ⟨c₂, _, c₁.nreg 50105 - 1, .seq e₁ e₂, by_omega, tlt, tpk, fun a ha => ?_,
    fun r a1 a2 a3 a4 a5 => ?_, fun r hr => ?_, fun a ha => ?_, ?_, by zuoyj; exact fa1, ?_⟩
  · rw [q1, fm _ by_omega]
    zuby
    split_ifs
    · rfl
    · rfl
    · exact fm a ha
  · rw [q2 r a3 a4 a5]; exact fr r a1 a2
  · rw [NO.1]; exact frr r hr
  · rw [NO.2.1]; exact frm a ha
  · rw [NO.2.2]; exact fo
  · zuoyj; omega

/-! ## The query setups -/
theorem ndA_exec (c : Config) (hw : WordsBounded W c) {MD NFH p h lp : ℕ}
    (h00 : c.nreg 90000 = MD) (h01 : c.nreg 90001 = NFH) (h71 : c.nreg 90071 = p)
    (h19 : c.nreg 90019 = 1) (hh : c.nmem p = h) (hlp : c.nmem ztr = lp)
    (hb : p + 1 ≤ W) (hhW : h + 1 ≤ W) :
    ∃ c' k, Exec P W ndA c c' k ∧ k = 7 ∧ c'.nreg 50000 = MD ∧ c'.nreg 50001 = NFH ∧
      c'.nreg 50002 = lp ∧ c'.nreg 50003 = h + 1 ∧ c'.nreg 90091 = h + 1 ∧ c'.nmem = c.nmem ∧
      (∀ r, r ≠ 50000 → r ≠ 50001 → r ≠ 50002 → r ≠ 50003 → r ≠ 90090 → r ≠ 90091 →
        r ≠ 90074 → c'.nreg r = c.nreg r) := by
  unfold ndA
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h00, h01, h71, h19, hh]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl, fun r a1 a2 a3 a4 a5 a6 a7 => ?_⟩ <;>
    simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, h00, h01, h71, h19, hh, hlp]
theorem ndC_exec (c : Config) (hw : WordsBounded W c) {MD NFH p rp : ℕ}
    (h00 : c.nreg 90000 = MD) (h01 : c.nreg 90001 = NFH) (h71 : c.nreg 90071 = p)
    (h21 : c.nreg 90021 = 2) (hrp : c.nmem ztcao = rp) (hb : p + 2 ≤ W) :
    ∃ c' k, Exec P W ndC c c' k ∧ k = 5 ∧ c'.nreg 50000 = MD ∧ c'.nreg 50001 = NFH ∧
      c'.nreg 50002 = rp ∧ c'.nreg 50003 = c.nreg 90091 ∧ c'.nmem = c.nmem ∧
      (∀ r, r ≠ 50000 → r ≠ 50001 → r ≠ 50002 → r ≠ 50003 → r ≠ 90074 →
        c'.nreg r = c.nreg r) := by
  unfold ndC
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h00, h01, h71, h21]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, fun r a1 a2 a3 a4 a5 => ?_⟩ <;>
    simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, h00, h01, h71, h21, hrp]
theorem ndE_exec (c : Config) (hw : WordsBounded W c) {p i : ℕ}
    (h71 : c.nreg 90071 = p) (h70 : c.nreg 90070 = i) (h76 : c.nreg 90076 = 5)
    (h19 : c.nreg 90019 = 1) (hb : p + 5 ≤ W) (hi : i + 1 ≤ W) :
    ∃ c' k, Exec P W ndE c c' k ∧ k = 2 ∧ c'.nreg 90071 = p + 5 ∧ c'.nreg 90070 = i + 1 ∧
      c'.nmem = c.nmem ∧ ztgsn := by
  unfold ndE
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h71, h70, h76, h19]; omega)
  refine ⟨rfl, ?_, ?_, rfl, fun r a1 a2 => ?_⟩ <;>
    simp (disch := omega) only [Machine.upd_same, Machine.upd_other, h71, h70,
      h76, h19]

/-! ## The loop -/

/-- The facts of the environment of the position search loop. -/
structure NdEnv (P : Polygon) (W MD NFH CB : ℕ) (d : Dm) (M : Model) (N : NF) (c₀ : Config) :
    Prop where
  hG : GoodEnv P
  hWh : hostWords P.n ≤ W
  hGM : GoodModel M
  hNF : IsNF M zta N
  hne : (N.F M zta).Nonempty
  hK : d.K = N.nChords
  hA : d.A = N.arcs.length
  bases : Bases c₀ d
  r00 : c₀.nreg 90000 = MD
  r01 : c₀.nreg 90001 = NFH
  r10 : c₀.nreg 90010 = N.nChords
  r13 : c₀.nreg 90013 = CB
  r19 : c₀.nreg 90019 = 1
  r21 : c₀.nreg 90021 = 2
  alloc : c₀.nreg ALLOC = d.b0 + d.oEnd
  wf : ModelDescWF P d.b0 c₀.nmem MD
  desc : ModelDescAt c₀.nmem MD zta M
  nfw : NFWithin c₀.nmem NFH d.b0 N
  chords : ∀ i, i < N.nChords → c₀.nmem ztblv = (N.chord i).h ∧
    c₀.nmem ztbye = (N.chord i).lp ∧ c₀.nmem ztbyf = (N.chord i).rp
  cbB : CB + 5 * N.nChords ≤ d.b0
  room : c₀.nreg ALLOC + N.nChords * zteky ≤ W
  cnt0 : ∀ j, j < N.arcs.length → c₀.nmem ztgib = 0

/-- The invariant of the position search loop. -/
structure NdI (P : Polygon) (W : ℕ) (d : Dm) (M : Model) (N : NF) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  i_le : c.nreg 90070 ≤ N.nChords
  ptr : c.nreg 90071 = c₀.nreg 90013 + 5 * c.nreg 90070
  c76 : c.nreg 90076 = 5
  r9 : ∀ r, 90000 ≤ r → r < 100000 → Binit r = false → c.nreg r = c₀.nreg r
  fr : ∀ r, bandOf r ∉ ({bLocate, bSign, bGran} : Finset ℕ) → r ≠ ALLOC → c.nreg r = c₀.nreg r
  frr : ∀ r, bandOf r ∉ ({bLocate, bSign} : Finset ℕ) → c.rreg r = c₀.rreg r
  frm : ∀ a, a < c₀.nreg ALLOC → c.rmem a = c₀.rmem a
  fro : c.output = c₀.output
  al1 : c₀.nreg ALLOC ≤ c.nreg ALLOC
  al2 : c.nreg ALLOC ≤ c₀.nreg ALLOC +
    c.nreg 90070 * zteky
  nd0 : ∀ u, u < c.nreg 90070 → c.nmem ztchp < N.arcs.length ∧
    pk M zta N (c.nmem ztchp) = M.key zta (N.chord u).lpos
  nd1 : ∀ u, u < c.nreg 90070 → c.nmem ztchq < N.arcs.length ∧
    pk M zta N (c.nmem ztchq) = M.key zta (N.chord u).rpos
  cnt : ∀ j, j < N.arcs.length → c.nmem ztgib =
    cntInit zterb ztxgv
      ztxgw j
  mem : ∀ a, a < c₀.nreg ALLOC → ztjnx →
    zteor → c.nmem a = c₀.nmem a
theorem cntInit_le (i : ℕ) (f g : ℕ → ℕ) (j : ℕ) : cntInit i f g j ≤ 2 * i := by
  zumse
  have h1 := Finset.card_filter_le ztmbb ztnzl
  have h2 := Finset.card_filter_le ztmbb ztnzm
  rw [Finset.card_range] at h1 h2
  omega
set_option maxHeartbeats 4000000 in
theorem ndBody_exec {W MD NFH CB : ℕ} {d : Dm} {M : Model} {N : NF}
    {c₀ c : Config} (hE : NdEnv P W MD NFH CB d M N c₀) (hI : NdI P W d M N c₀ c)
    (ht : c.nreg 90070 < N.nChords) :
    ∃ c' k, Exec P W ndBody c c' k ∧ NdI P W d M N c₀ c' ∧
      k ≤ 2 * NFLoc.locCost 5100 N.arcs.length + 30 ∧ c'.nreg 90070 = c.nreg 90070 + 1 ∧
      c'.nreg ALLOC ≤ c.nreg ALLOC + k := by
  obtain ⟨hw, hle, hp, h76, r9, fr, frr, frm, fro, al1, al2, hnd0, hnd1, hcnt, hm⟩ := hI
  zuf
  zufhv

  have hK := hE.hK
  have hA := hE.hA
  have hal := hE.alloc
  have hcb := hE.cbB
  have hroom := hE.room
  set L := NFLoc.locCost 5100 N.arcs.length with hL
  zukzl
  zukzh
  generalize hii : c.nreg 90070 = i at ht hle hp al2 hnd0 hnd1 hcnt
  have hi1 : ztg * ztcsj ≤ K * ztcsj := Nat.mul_le_mul_right _ by_omega
  have hmi : i * ztcsj + ztcsj = ztg * ztcsj := by_ring
  have hK1 : 30 ≤ K * ztcsj := by
    zulgl
    omega
  zuc
  -- memory below `b0`
  have hb0 : ∀ a, a < d.b0 → c.nmem a = c₀.nmem a := fun a ha =>
    hm a by_omega zteem zteem
  obtain ⟨ch0, ch1, ch2⟩ := hE.chords i ht
  rw [hE.r13] at hp
  have v0 : c.nmem ztblv = (N.chord i).h := by rw [hb0 _ by_omega, ch0]
  have v1 : c.nmem ztbye = (N.chord i).lp := by rw [hb0 _ by_omega, ch1]
  have v2 : c.nmem ztbyf = (N.chord i).rp := by rw [hb0 _ by_omega, ch2]
  have hBc := hE.bases.frame fun q a1 a2 => r9 q by_omega by_omega
    ztbjn
  have c00 : c.nreg 90000 = MD := by rw [r9 _ by_norm_num by_norm_num by_decide, hE.r00]
  have c01 : c.nreg 90001 = NFH := by rw [r9 _ by_norm_num by_norm_num by_decide, hE.r01]
  have c19 : zthoj := by rw [r9 _ by_norm_num by_norm_num by_decide, hE.r19]
  have c21 : ztuok := by rw [r9 _ by_norm_num by_norm_num by_decide, hE.r21]
  have hhlt : ztpgr := by
    zubts
    zvnof; exact hh i ht
  have hWP : ztmd := by have := hE.hWh; unfold hostWords at this; omega
  -- 1. the left query
  obtain ⟨c₁, k₁, e₁, hk₁, a00, a01, a02, a03, a91, am, ar⟩ := ndA_exec (P := P) c hw c00 c01 hp
    c19 v0 v1 by_omega by_omega
  zud
  have g₁ : ∀ r, 90000 ≤ r → r < 100000 → Binit r = false → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 => ar r by_omega by_omega by_omega by_omega
      ztxe ztxe ztxe
  have hA₁ : ztdc := ar _ ztu
    ztu ztu ztu
    ztu ztu ztu
  have hag₁ : ∀ a, a < d.b0 → c₁.nmem a = c₀.nmem a := fun a ha => by rw [am, hb0 a ha]
  obtain ⟨hdesc₁, hwf₁⟩ := desc_agree' hE.wf hE.desc hag₁
  have hNW₁ := hE.nfw.transport hag₁
  have hi' := ht
  have hlp := lpos_proper hE.hNF hi'
  zvmxg at hlp
  obtain ⟨c₂, k₂, x0, e₂, hk₂, x0lt, x0pk, M2, R2, RR2, RM2, O2, A21, A22⟩ :=
    srchStore_exec (P := P) (W := W) (b0 := d.b0) (M := M) (N := N) (x := (N.chord i).lpos)
    (c := c₁) w₁ (bs := 90033) (BS := d.b0 + d.oNd0) (i := i) (Cb := d.b0 + d.oCnt) hE.hG hE.hWh
    hE.hGM hwf₁ hdesc₁ hNW₁ hE.hNF hE.hne a00 a01 a02 a03 hlp (by zuovm)
    (lkey_cut hE.hNF hi') (attach_l hE.hNF hi').1
    ⟨by_decide, by_decide, by_decide, by_decide, by_decide, by_decide, by_decide, by_decide,
      by decide⟩
    (by rw [g₁ _ by_norm_num by_norm_num by_decide, hBc.bNd0])
    (by rw [ar 90070 by_decide by_decide by_decide by_decide by_decide by_decide
      by_decide, hii])
    (by rw [g₁ _ by_norm_num by_norm_num by_decide, hBc.bCnt])
    (by rw [g₁ _ by_norm_num by_norm_num by_decide, c19]) by_omega
    ztqog by_omega by_omega by_omega
    (fun v hv => by
      rw [am, hcnt v hv]
      have := cntInit_le i ztxgv
        ztxgw v
      omega)
  zue
  have g₂ : ∀ r, 90000 ≤ r → r < 100000 → Binit r = false → c₂.nreg r = c.nreg r :=
    fun r h1 h2 h3 => by
      rw [R2 r ztnrw ztu ztxe
        ztxe ztxe, g₁ r h1 h2 h3]
  have c2_71 : ztoqw := by
    rw [R2 _ ztepf ztu by_decide
      by_decide by_decide, ar _ by_decide by_decide by_decide by_decide by_decide
      by_decide by_decide, hp]
  have c2_91 : c₂.nreg 90091 = (N.chord i).h + 1 := by
    rw [R2 _ ztepf ztu by_decide
      by_decide by_decide, a91]
  have c2_70 : zturn := by
    rw [R2 _ ztepf ztu by_decide
      by_decide by_decide, ar _ by_decide by_decide by_decide by_decide by_decide
      by_decide by_decide, hii]
  have m2b : ∀ a, a < d.b0 → c₂.nmem a = c₀.nmem a := fun a ha => by
    rw [M2 a by_omega, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
      hag₁ a ha]
  -- 2. the right query
  obtain ⟨c₃, k₃, e₃, hk₃, b00, b01, b02, b03, bm, br⟩ := ndC_exec (P := P) c₂ w₂
    (by rw [g₂ _ by_norm_num by_norm_num by_decide, c00])
    (by rw [g₂ _ by_norm_num by_norm_num by_decide, c01]) c2_71
    (by rw [g₂ _ by_norm_num by_norm_num by_decide, c21])
    (by rw [m2b _ by_omega, ch2]) by_omega
  rw [c2_91] at b03
  zubj
  have hA₃ : ztbox := br _ ztu
    ztu ztu ztu
    ztu
  have hag₃ : ztkoe := fun a ha => by rw [bm, m2b a ha]
  obtain ⟨hdesc₃, hwf₃⟩ := desc_agree' hE.wf hE.desc hag₃
  have hNW₃ := hE.nfw.transport hag₃
  have hrp := rpos_proper hE.hNF hi'
  zvmxg at hrp
  have g₃ : ∀ r, 90000 ≤ r → r < 100000 → Binit r = false → c₃.nreg r = c.nreg r :=
    fun r h1 h2 h3 => by
      rw [br r by_omega by_omega by_omega by_omega ztxe,
        g₂ r h1 h2 h3]
  obtain ⟨c₄, k₄, x1, e₄, hk₄, x1lt, x1pk, M4, R4, RR4, RM4, O4, A41, A42⟩ :=
    srchStore_exec (P := P) (W := W) (b0 := d.b0) (M := M) (N := N) (x := (N.chord i).rpos)
    (c := c₃) w₃ (bs := 90034) (BS := d.b0 + d.oNd1) (i := i) (Cb := d.b0 + d.oCnt) hE.hG hE.hWh
    hE.hGM hwf₃ hdesc₃ hNW₃ hE.hNF hE.hne b00 b01 b02 b03 hrp (by zuovn)
    (rkey_cut hE.hNF hi') (attach_r hE.hNF hi').1
    ⟨by_decide, by_decide, by_decide, by_decide, by_decide, by_decide, by_decide, by_decide,
      by decide⟩
    (by rw [g₃ _ by_norm_num by_norm_num by_decide, hBc.bNd1])
    (by rw [br _ by_decide by_decide by_decide by_decide by_decide, c2_70])
    (by rw [g₃ _ by_norm_num by_norm_num by_decide, hBc.bCnt])
    (by rw [g₃ _ by_norm_num by_norm_num by_decide, c19]) by_omega
    ztqog by_omega by_omega by_omega
    (fun v hv => by
      rw [bm, M2 _ by_omega, am]
      have hc := hcnt v hv
      have hc' := hcnt x0 x0lt
      have := cntInit_le i ztxgv
        ztxgw v
      have := cntInit_le i ztxgv
        ztxgw x0
      have hK30 : K * 30 ≤ K * ztcsj := by_grind
      zuby
      split_ifs <;> omega)
  zucc
  have g₄ : ∀ r, 90000 ≤ r → r < 100000 → Binit r = false → c₄.nreg r = c.nreg r :=
    fun r h1 h2 h3 => by
      rw [R4 r ztnrw ztu ztxe
        ztxe ztxe, g₃ r h1 h2 h3]
  have c4_71 : c₄.nreg 90071 = CB + 5 * i := by
    rw [R4 _ ztepf ztu by_decide
      by_decide by_decide, br _ by_decide by_decide by_decide by_decide by_decide,
      c2_71]
  have c4_70 : c₄.nreg 90070 = i := by
    rw [R4 _ ztepf ztu by_decide
      by_decide by_decide, br _ by_decide by_decide by_decide by_decide by_decide,
      c2_70]
  have c4_76 : c₄.nreg 90076 = 5 := by
    rw [R4 _ ztepf ztu by_decide
      by_decide by_decide, br _ by_decide by_decide by_decide by_decide by_decide,
      R2 _ ztepf ztu by_decide
      by_decide by_decide, ar _ by_decide by_decide by_decide by_decide by_decide
      by_decide by_decide, h76]
  -- 3. advance
  obtain ⟨c₅, k₅, e₅, hk₅, d71, d70, dm, dr⟩ := ndE_exec (P := P) c₄ w₄ c4_71 c4_70 c4_76
    (by rw [g₄ _ by_norm_num by_norm_num by_decide, c19]) by_omega by_omega
  -- the memory
  set m1 := upd (upd c.nmem ztjtk x0) ztqlb
    (c.nmem ztqlb + 1) with hm1
  have H2 : ∀ a, a < c₁.nreg ALLOC → c₂.nmem a = m1 a := fun a ha => by rw [M2 a ha, am]
  have M5 : ∀ a, a < c₀.nreg ALLOC → c₅.nmem a =
      upd (upd m1 ztjtl x1) ztqlc (m1 ztqlc + 1) a := by
    zuge
    rw [dm, M4 a by_omega, bm]
    zuby
    split_ifs
    · rw [H2 _ by_omega]
    · rfl
    · exact H2 a by_omega
  have NA := exec_natOnly e₁ (by simp [ndA, natOnly, natOK, block])
  have NC := exec_natOnly e₃ (by simp [ndC, natOnly, natOK, block])
  have NE := exec_natOnly e₅ (by simp [ndE, natOnly, natOK, block])
  have hA₅ : ztcrj := dr _ ztu
    ztu
  refine ⟨c₅, _, .seq e₁ ztbq,
    ⟨e₅.wb_right, by_omega, by rw [d71, d70, hE.r13]; ring, ?_, fun r h1 h2 h3 => ?_,
      fun r h1 h2 => ?_, fun r h1 => ?_, fun a ha => ?_, ?_, ?_, ?_,
      fun u hu => ?_, fun u hu => ?_, fun j hj => ?_, fun a ha b1 b2 => ?_⟩, ?_,
    by rw [d70], by_omega⟩
  · rw [dr _ by_decide by_decide, c4_76]
  · have h3' := h3
    zvnuz at h3'
    rw [dr r by_omega by_omega, g₄ r h1 h2 h3, r9 r h1 h2 h3]
  · have hb9 : ztlyz := by
      intro h; apply h1; simp only [bandOf, bGran, Finset.mem_insert, Finset.mem_singleton]
      omega
    have h15 : bandOf r ∉ ({bLocate, bSign} : Finset ℕ) := by
      intro h; apply h1
      simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
      zuy
      · zueou
      · zulyc
    have hn5 : ¬ ztdfc := by
      intro h; apply h15; simp only [bandOf, bLocate, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [dr r by_omega by_omega, R4 r h15 h2 by_omega by_omega by_omega,
      br r by_omega by_omega by_omega by_omega by_omega,
      R2 r h15 h2 by_omega by_omega by_omega,
      ar r by_omega by_omega by_omega by_omega by_omega by_omega by_omega,
      fr r h1 h2]
  · rw [NE.1, RR4 r h1, NC.1, RR2 r h1, NA.1, frr r h1]
  · rw [NE.2.1, RM4 a by_omega, NC.2.1, RM2 a by_omega, NA.2.1, frm a ha]
  · rw [NE.2.2, O4, NC.2.2, O2, NA.2.2, fro]
  · omega
  · rw [d70, ← hL]; omega
  · zukqm
    rw [M5 _ by_omega, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
      hm1]
    zujtz
    · zulth
      zumyl; zumzo
      exact ⟨x0lt, x0pk⟩
    · zucw
      exact hnd0 u by_omega
  · zukqm
    zunmg
    zujtz
    · zulth
      zuvz
      exact ⟨x1lt, x1pk⟩
    · rw [Machine.upd_other _ _ _ by_omega, hm1, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega]
      exact hnd1 u by_omega
  · -- the counts
    have f0 : ∀ u, u < i → c₅.nmem ztchp = c.nmem ztchp := by
      zubgt
      rw [M5 _ by_omega, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        hm1, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega]
    have g0 : ∀ u, u < i → c₅.nmem ztchq = c.nmem ztchq := by
      zubgt
      rw [M5 _ by_omega, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        hm1, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega]
    have fi : c₅.nmem ztjtk = x0 := by
      rw [M5 _ by_omega, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        hm1, Machine.upd_other _ _ _ by_omega]; simp
    have gi : c₅.nmem ztjtl = x1 := by
      zunmg; simp
    rw [d70, cntInit_succ, cntInit_congr f0 g0, fi, gi, ← hcnt j hj, M5 _ by_omega, hm1]
    by_cases e1 : x1 = j
    · zumpy
      by_cases e0 : x0 = x1
      · zumpx
        simp (disch := omega) only [Machine.upd_same, ite_true]
      · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, ite_true, e0, ite_false]
    · by_cases e0 : x0 = j
      · zumpx
        simp (disch := omega) only [Machine.upd_same, Machine.upd_other, ite_true, e1, ite_false]
      · simp (disch := omega) only [Machine.upd_other, e1, e0, ite_false,
          Nat.add_zero]
  · rw [M5 _ ha, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega, hm1,
      Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega]
    exact hm a ha b1 b2
  · omega
theorem ndLoop_exec {W MD NFH CB : ℕ} {d : Dm} {M : Model} {N : NF} {c₀ : Config}
    (hw : WordsBounded W c₀) (hE : NdEnv P W MD NFH CB d M N c₀) (hW5 : 5 ≤ W) :
    ∃ c' k, Exec P W ndLoop c₀ c' k ∧
      k ≤ N.nChords * ztgyi + 5 ∧
      NdI P W d M N c₀ c' ∧ c'.nreg 90070 = N.nChords ∧ c'.nreg ALLOC ≤ c₀.nreg ALLOC + k := by
  obtain ⟨c₁, k₁, e₁, hk₁, q, q0⟩ : ∃ c₁ k₁, Exec P W (block [.constN 90070 0, .copyN 90071 90013,
      .constN 90076 5]) c₀ c₁ k₁ ∧ k₁ = 3 ∧ NdI P W d M N c₀ c₁ ∧ c₁.nreg 90070 = 0 := by
    exec_block
    · omega
    · omega
    · refine ⟨rfl, ⟨by assumption, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, fun r h1 h2 => ?_,
        by simp_all, by_simp_all, rfl, ?_, ?_, fun u hu => ?_, fun u hu => ?_,
        fun j hj => ?_, by_simp_all⟩, ?_⟩
      · config_simp; omega
      · config_simp; omega
      · config_simp
      · zvnuz at h3
        config_simp; simp only [upd]; split_ifs <;> first | rfl | omega
      · have : r < 90000 ∨ 100000 ≤ r := by
          by_contra hc; apply h1; simp only [bandOf, bGran, Finset.mem_insert,
            Finset.mem_singleton]; omega
        config_simp; simp only [upd]; split_ifs <;> first | rfl | omega
      · config_simp; simp only [upd, ALLOC]; simp
      · config_simp; simp only [upd, ALLOC]; simp
      · zulah
      · zulah
      · config_simp; rw [hE.cnt0 j hj]; simp [cntInit]
      · config_simp
  obtain ⟨c', k, e, I', hx, hk, hA'⟩ := SortR.whileLtN_potential_lb (P := P) (W := W)
    (a := 90070) (b := 90010) (body := ndBody) (NdI P W d M N c₀)
    (fun c => (N.nChords - c.nreg 90070) * ztgyi)
    ztesf ztpf
    (fun c I ht => by
      have t : c.nreg 90070 < N.nChords := by
        rw [I.r9 90010 by_norm_num by_norm_num by_decide, hE.r10] at ht; exact ht
      obtain ⟨c', k, e, I', hk, hi, ha⟩ := ndBody_exec (P := P) hE I t
      refine ⟨c', k, e, I', ?_, ha⟩
      zumni
      have : N.nChords - c.nreg 90070 = (N.nChords - (c.nreg 90070 + 1)) + 1 := by_omega
      rw [this, Nat.add_mul, one_mul]
      omega) q
  have hK' : c'.nreg 90070 = N.nChords := by
    rw [I'.r9 90010 by_norm_num by_norm_num by_decide, hE.r10] at hx
    have := I'.i_le; omega
  refine ⟨c', _, .seq e₁ e, ?_, I', hK', ?_⟩
  · rw [q0, Nat.sub_zero] at hk
    omega
  · have h1 := q.al1
    have h2 := q.al2
    rw [q0, Nat.zero_mul, Nat.add_zero] at h2
    omega
end
end Gran
end Chazelle.Core
end
section
set_option hygiene false
local macro "zquq" : tactic => `(tactic| obtain ⟨hnc, htw⟩ := h.word)
local macro "zqur" : tactic => `(tactic| simp only [e1, e2] at this)
local macro "zqus" : tactic => `(tactic| obtain ⟨pa, pb, ta, tb, hA, hB, hAB, ka, kb⟩ := h.att_lo_hi hi')
local macro "zqut" : tactic => `(tactic| obtain ⟨pa, pb, ta, tb, hA, hB, hAB, ka, kb⟩ := h.att_lo_hi hj)
local macro "zquu" : tactic => `(tactic| (have hs := h.sorted; rw [hsplit] at hs; have hnd := h.nodup; rw [hsplit, nodup_append] at hnd))
local macro "zquv" : tactic => `(tactic| obtain ⟨p, t, hp, ht0, ht1, hcut, hf⟩ := h.walk.exists_faces_nc h.adm h.finite hU)
local macro "zquw" : tactic => `(tactic| (rw [e1'] at hregU; rw [e2'] at hregD; rw [hregU, hregD]))
local macro "zqux" : tactic => `(tactic| (have n1 := hy _ ztqow; have n2 := hy _ ztqox))
set_option hygiene true

/-!
# WP-C (BuildNF): the regions of a submap are the labels of the stack pass

Let `L` be a valid chord list (`ChordTriplesOK`) of a walk-axiom model, and `S` an ordering of
its attachment events (`BuildOrder.events`) sorted by `BuildSort.EvLe` (key, then the tie rule);
`w = S.map fst` is its chord word, a parenthesis word (`BuildOrder.parenthesis_of_sorted`).  For a
non-cut key `y`, `gapLabel S y` is the label of the stack pass after the events with key below
`y`: the innermost chord whose key interval contains `y` (`none` for the root).

## Results

* `faces_same_iff`: two non-cut positions inside walk edges face the same region iff their keys
  have the same gap label;
* `side_labels`: for chord `i`, whose first event in `S` is at position `|u|` (`S = u ++ e :: v`),
  the region faced at non-cut keys with label `label w (|u| + 1) = some i` is the region below
  the chord if its first event is its left endpoint (`key lpos < key rpos`) and above it
  otherwise, and the region faced at keys with label `label w |u|` (the label before the chord's
  opening event, i.e. its parent) is the other side.

These are the facts that make the stack pass compute the region records of the normal form: the
regions are the `K + 1` labels, and chord `i` has the sides `some i` (inside) and the label before
its opening event (outside), `up`/`dn` fixed by the orientation of its first event.
-/
namespace Chazelle.Core
namespace BuildRegions
@[expose] public section
open Set List
open Chazelle.Chain (SideAttach sideInArc sidePt sideKey_inj TouchesIn)
open BuildSort (Ev EvLe cycDist cntBelow)
open BuildOrder (events evPair chordSet mem_events event_data getD_mem chordSet_inj chordSet_mem)

/-! ## The context -/

/-- The chord family of a triple list. -/
def famOf (M : Model) (Q : Polygon) (L : List zte) : Set ztf :=
  {c | ∃ x ∈ L, c = (recOf x).toSet M Q}

/-- **A sorted event list** of a valid chord list in a walk-axiom model. -/
structure Ctx (M : Model) (Q : Polygon) (L : List zte) (S : List Ev) : Prop where
  walk : WalkAx M
  valid : ChordTriplesOK M Q L
  perm : S.Perm ztrpi
  sorted : S.Pairwise ztmaw
variable {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {S : List Ev}

/-- The record of chord `i`. -/
def crec (L : List zte) (i : ℕ) : CRec := recOf ztwrk

/-- The key of the left endpoint of chord `i`. -/
noncomputable def kl (M : Model) (Q : Polygon) (L : List zte) (i : ℕ) : ℝ :=
  M.key Q (crec L i).lpos

/-- The key of the right endpoint of chord `i`. -/
noncomputable def kr (M : Model) (Q : Polygon) (L : List zte) (i : ℕ) : ℝ :=
  M.key Q (crec L i).rpos

/-- The event of the left endpoint of chord `i`. -/
noncomputable def eL (M : Model) (Q : Polygon) (L : List zte) (i : ℕ) : Ev :=
  ztila

/-- The event of the right endpoint of chord `i`. -/
noncomputable def eR (M : Model) (Q : Polygon) (L : List zte) (i : ℕ) : Ev :=
  (i, kr M Q L i, kl M Q L i)
theorem evPair_eq (M : Model) (Q : Polygon) (L : List zte) (i : ℕ) :
    evPair M Q L i = [eL M Q L i, eR M Q L i] := rfl

/-- The smaller key of chord `i`. -/
noncomputable def lo (M : Model) (Q : Polygon) (L : List zte) (i : ℕ) : ℝ :=
  min ztciq ztcir

/-- The larger key of chord `i`. -/
noncomputable def hi (M : Model) (Q : Polygon) (L : List zte) (i : ℕ) : ℝ :=
  max ztciq ztcir

/-- The first event of chord `i` (the one with the smaller key). -/
noncomputable def e1 (M : Model) (Q : Polygon) (L : List zte) (i : ℕ) : Ev :=
  (i, lo M Q L i, hi M Q L i)

/-- The second event of chord `i`. -/
noncomputable def e2 (M : Model) (Q : Polygon) (L : List zte) (i : ℕ) : Ev :=
  (i, hi M Q L i, lo M Q L i)

/-- **The gap label** of a key `y`: the label of the stack pass after the events with key below
`y`. -/
noncomputable def gapLabel (S : List Ev) (y : ℝ) : Option ℕ :=
  BuildStack.label ztbuq (cntBelow S y)

/-- Chord `j` is nested in chord `i`'s closed key interval... reversed: `i` lies within `j`. -/
def Within (M : Model) (Q : Polygon) (L : List zte) (i j : ℕ) : Prop :=
  lo M Q L j ≤ lo M Q L i ∧ hi M Q L i ≤ hi M Q L j

/-- **The region of a label**: the region faced at the non-cut keys with that gap label (the
empty set for a label that no non-cut key has). -/
noncomputable def reg (M : Model) (Q : Polygon) (L : List zte) (S : List Ev)
    (ℓ : Option ℕ) : Set Point := by
  classical
  exact if hh : ∃ U ∈ M.regions zthh, ∃ (p : ℕ) (t : ℝ), p < M.W.n ∧ 0 < t ∧ t < 1 ∧
      ¬ M.IsCut zthh ztk ∧ gapLabel S ztk = ℓ ∧ M.Faces p t U
    then hh.choose else ∅

/-- The labels of the stack pass over `K` chords: the root `none` and `some i`, `i < K`. -/
def LabelOK (K : ℕ) (ℓ : Option ℕ) : Prop := ∀ i, ℓ = some i → i < K
namespace Ctx
variable (h : Ctx M Q L S)
include h
theorem mem_iff (e : Ev) : e ∈ S ↔ e ∈ events M Q L := h.perm.mem_iff
theorem finite : (famOf M Q L).Finite := h.valid.1.1
theorem adm : famOf M Q L ⊆ M.Adm := h.valid.1.2.1
variable {i : ℕ} {y : ℝ} {j : ℕ} {u v : List Ev} {p : ℕ} {t : ℝ}
/-- The attachment of the left endpoint of chord `i`. -/
theorem attL (hi : i < L.length) :
    SideAttach M.W ztrz (crec L i).lp ztmbp := by
  have := h.valid.2.2.1 _ ztdoo
  exact this.1

/-- The attachment of the right endpoint of chord `i`. -/
theorem attR (hi : i < L.length) :
    SideAttach M.W ztrz (crec L i).rp ztgec := by
  have := h.valid.2.2.1 _ ztdoo
  exact this.2

/-- The left endpoint is left of the right endpoint. -/
theorem pos_lt (hi : i < L.length) :
    (M.pos Q (crec L i).lpos).1 < (M.pos Q (crec L i).rpos).1 := by
  have := h.valid.2.2.1 _ ztdoo
  exact BuildOrder.endpoints h.walk (h.adm ztdcw) this
theorem pts_ne (hi : i < L.length) :
    sidePt M.W (crec L i).lp ztmbp ≠
      sidePt M.W (crec L i).rp ztgec := by
  zudii
  have hlt := h.pos_lt hi
  have : M.pos Q (crec L i).lpos = M.pos Q (crec L i).rpos := heq
  simp_all
theorem kl_ne_kr (hi : i < L.length) : kl M Q L i ≠ kr M Q L i :=
  WalkAx.key_ne_of_pt_ne ztvrp ztvrq (h.pts_ne hi)
omit h in
theorem key_bounds {pa : ℕ} {ta : ℝ} {c : Set Point} (hA : SideAttach M.W c pa ta) :
    0 ≤ (pa : ℝ) + ta ∧ (pa : ℝ) + ta < M.W.n := by
  have : ztehp := by exact_mod_cast hA.1
  zubkc
theorem kl_bounds (hi : i < L.length) : 0 ≤ kl M Q L i ∧ kl M Q L i < M.W.n :=
  key_bounds ztvrp
theorem kr_bounds (hi : i < L.length) : 0 ≤ kr M Q L i ∧ kr M Q L i < M.W.n :=
  key_bounds ztvrq
theorem eL_mem (hi : i < L.length) : eL M Q L i ∈ S :=
  (h.mem_iff _).2 ztmmm
theorem eR_mem (hi : i < L.length) : eR M Q L i ∈ S :=
  (h.mem_iff _).2 ztmmm
theorem eL_ne_eR (hi : i < L.length) : eL M Q L i ≠ eR M Q L i := by
  zudii
  apply h.kl_ne_kr hi
  have := congrArg (fun e : Ev => e.2.1) heq
  tauto

/-- Every event is the left or the right event of its chord. -/
theorem mem_cases {e : Ev} (he : e ∈ S) :
    e.1 < L.length ∧ (e = eL M Q L e.1 ∨ e = eR M Q L e.1) := by
  obtain ⟨i, hi, he⟩ := mem_events.1 ((h.mem_iff e).1 he)
  rw [evPair_eq] at he
  rcases mem_cons.1 he with rfl | he
  · tauto
  · zvojs at he; subst he; tauto
theorem events_nodup : (events M Q L).Nodup := by
  unfold events
  rw [nodup_flatMap]
  refine ztonn
  · rw [evPair_eq, nodup_cons, List.mem_singleton]
    refine ⟨?_, nodup_singleton _⟩
    exact h.eL_ne_eR ztqtk
  · refine (nodup_range).pairwise_of_forall_ne fun i _ j _ hij => ?_
    rw [Function.onFun, disjoint_iff_ne]
    zubtp
    rw [evPair_eq] at ha hb
    have hfst : ∀ k, ∀ x ∈ [eL M Q L k, eR M Q L k], x.1 = k := by
      intro k x hx
      zvmxh at hx
      rcases hx with rfl | rfl <;> rfl
    grind
theorem nodup : S.Nodup := h.perm.nodup_iff.2 h.events_nodup
theorem lo_lt_hi (hi' : i < L.length) : lo M Q L i < hi M Q L i := by
  unfold lo hi
  rcases lt_or_gt_of_ne ztvrw with h1 | h1
  · simp_all
  simp_all
theorem lo_bounds (hi' : i < L.length) : 0 ≤ lo M Q L i ∧ lo M Q L i < M.W.n := by
  unfold lo
  exact ⟨le_min (h.kl_bounds hi').1 (h.kr_bounds hi').1,
    (min_le_left _ _).trans_lt (h.kl_bounds hi').2⟩
theorem hi_bounds (hi' : i < L.length) : 0 ≤ hi M Q L i ∧ hi M Q L i < M.W.n := by
  unfold hi
  exact ⟨(h.kl_bounds hi').1.trans by_simp_all,
    max_lt (h.kl_bounds hi').2 (h.kr_bounds hi').2⟩
omit h in
/-- The first and second events are the left and right events, in key order. -/
theorem e1_e2_cases (_h : Ctx M Q L S) (i : ℕ) :
    (kl M Q L i < kr M Q L i ∧ e1 M Q L i = eL M Q L i ∧ e2 M Q L i = eR M Q L i) ∨
      (kr M Q L i ≤ kl M Q L i ∧ e1 M Q L i = eR M Q L i ∧ e2 M Q L i = eL M Q L i) := by
  unfold e1 e2 eL eR lo hi
  grind
theorem e1_mem (hi' : i < L.length) : e1 M Q L i ∈ S := by
  rcases h.e1_e2_cases i with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ <;> zvmwp
  · exact h.eL_mem hi'
  · exact h.eR_mem hi'
theorem e2_mem (hi' : i < L.length) : e2 M Q L i ∈ S := by
  rcases h.e1_e2_cases i with ⟨-, -, h1⟩ | ⟨-, -, h1⟩ <;> zvmwp
  · exact h.eR_mem hi'
  · exact h.eL_mem hi'
theorem e1_ne_e2 (hi' : i < L.length) : e1 M Q L i ≠ e2 M Q L i := by
  zudii
  have := congrArg (fun e : Ev => e.2.1) heq
  zqur
  exact (h.lo_lt_hi hi').ne this

/-- Every event of chord `j` is its first or its second event. -/
theorem mem_cases' {f : Ev} (hf : f ∈ S) :
    f.1 < L.length ∧ (f = e1 M Q L f.1 ∨ f = e2 M Q L f.1) := by
  obtain ⟨hlt, hc⟩ := h.mem_cases hf
  refine ⟨hlt, ?_⟩
  rcases h.e1_e2_cases f.1 with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
  · simp_all
  grind

/-- The attachments of chord `i` at its two keys, in key order. -/
theorem att_lo_hi (hi' : i < L.length) :
    ∃ (pa pb : ℕ) (ta tb : ℝ), SideAttach M.W ztrz pa ta ∧
      SideAttach M.W ztrz pb tb ∧ sidePt M.W pa ta ≠ sidePt M.W pb tb ∧
      (pa : ℝ) + ta = lo M Q L i ∧ (pb : ℝ) + tb = hi M Q L i := by
  rcases h.e1_e2_cases i with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · have hlo := min_eq_left h0.le
    have hhi := max_eq_right h0.le
    exact ⟨_, _, _, _, h.attL hi', h.attR hi', h.pts_ne hi', by_tauto, by_tauto⟩
  · have hlo := min_eq_right h0
    have hhi := max_eq_left h0
    exact ⟨_, _, _, _, h.attR hi', h.attL hi', Ne.symm (h.pts_ne hi'), by_tauto,
      by tauto⟩

/-- **No crossing**, in key order. -/
theorem no_cross_keys {i j : ℕ} (hi' : i < L.length) (hj : j < L.length) (hij : i ≠ j) :
    ¬ (lo M Q L i < lo M Q L j ∧ lo M Q L j < hi M Q L i ∧ hi M Q L i < hi M Q L j) := by
  zuei
  zqus
  obtain ⟨pc, pd, tc, td, hC, hD, -, kc, kd⟩ := h.att_lo_hi hj
  have hne := fun e => hij (chordSet_inj h.valid hi' hj e)
  apply h.walk.no_cross h.adm h.finite zterh ztdnb hne hA hB hAB hC hD
  rw [ka, kb, kc, kd]
  zulkk
  zuiq

/-- **Distinct chords have distinct key pairs.** -/
theorem keys_ne {i j : ℕ} (hi' : i < L.length) (hj : j < L.length) (hij : i ≠ j) :
    ¬ (lo M Q L i = lo M Q L j ∧ hi M Q L i = hi M Q L j) := by
  zubf
  zqus
  obtain ⟨pc, pd, tc, td, hC, hD, hCD, kc, kd⟩ := h.att_lo_hi hj
  obtain ⟨rfl, rfl⟩ := sideKey_inj hA.2.1 hA.2.2.1 hC.2.1 hC.2.2.1 (by rw [ka, kc, h1])
  obtain ⟨rfl, rfl⟩ := sideKey_inj hB.2.1 hB.2.2.1 hD.2.1 hD.2.2.1 (by rw [kb, kd, h2])
  have e1 := (h.walk.attach_seg (h.adm zterh) hA hB hAB).1
  have e2 := (h.walk.attach_seg ztxxg hC hD hCD).1
  exact hij (chordSet_inj h.valid hi' hj ztqmh)

/-- The keys of the events are cut keys: a non-cut key is no event key. -/
theorem key_ne_of_not_cut (hy : ¬ M.IsCut zthh y) : ∀ e ∈ S, e.2.1 ≠ y := by
  intro e he hey
  obtain ⟨hi', hc⟩ := h.mem_cases he
  apply hy
  rcases hc with hc | hc <;> zvnmd at hey
  · exact ⟨_, chordSet_mem hi', _, _, h.attL hi', hey.symm⟩
  · exact ⟨_, chordSet_mem hi', _, _, h.attR hi', hey.symm⟩
omit h in
/-- Every chord of the family is a chord of the list. -/
theorem fam_cases (_h : Ctx M Q L S) {c : Set Point} (hc : c ∈ famOf M Q L) :
    ∃ j < L.length, c = chordSet M Q L j := by
  zucyc
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
  refine ztdqs
  unfold chordSet
  simp_all

/-! ## Open chords at a key -/

/-- **Chord `j` is open at a non-event key `y`** iff `y` is strictly between its keys. -/
theorem open_iff (hy : ∀ e ∈ S, e.2.1 ≠ y) {j : ℕ} (hj : j < L.length) :
    ((S.filter ztdnx).map Prod.fst).count j = 1 ↔
      lo M Q L j < y ∧ y < hi M Q L j := by
  rw [BuildSort.count_two (j := j) (h.nodup.filter _) ztvrt rfl rfl
    (fun f hf hfj => by
      have := (h.mem_cases' ztvyx).2
      simp_all)]
  have m1 : (j, lo M Q L j, hi M Q L j) ∈ S := h.e1_mem hj
  have m2 : (j, hi M Q L j, lo M Q L j) ∈ S := h.e2_mem hj
  simp only [e1, e2, mem_filter, decide_eq_true_eq, m1, m2, true_and]
  have hlh := h.lo_lt_hi hj
  grind

/-- A chord index beyond the list is never open. -/
theorem count_ge (hj : L.length ≤ j) :
    ((S.filter ztdnx).map Prod.fst).count j = 0 := by
  zuelj

  have := (h.mem_cases ztvyx).1
  omega

/-! ## Gap labels -/

/-- The chord word of the sorted events is a parenthesis word. -/
theorem word : BuildStack.NoCross ztbuq ∧ BuildStack.Twice ztbuq :=
  BuildOrder.parenthesis_of_sorted h.walk h.valid h.perm h.sorted

/-- **Two non-event keys have the same gap label iff every chord contains both or neither.** -/
theorem gapLabel_eq_iff {y y' : ℝ} (hy : ∀ e ∈ S, e.2.1 ≠ y) (hy' : ∀ e ∈ S, e.2.1 ≠ y') :
    gapLabel S y = gapLabel S y' ↔ ∀ j < L.length,
      (lo M Q L j < y ∧ y < hi M Q L j ↔ lo M Q L j < y' ∧ y' < hi M Q L j) := by
  zquq
  unfold gapLabel
  rw [BuildStack.label_eq_iff htw hnc, BuildSort.take_map_cntBelow h.sorted hy,
    BuildSort.take_map_cntBelow h.sorted hy']
  constructor
  · zumgf
    rw [← h.open_iff hy hj, ← h.open_iff hy' hj]
    simp_all
  · intro H j
    zuebv
    · rw [h.open_iff hy hj, h.open_iff hy' hj]; simp_all
    · rw [h.count_ge hj, h.count_ge hj]

/-- A key strictly inside a chord's arc from its smaller to its larger key. -/
theorem sideInArc_lo_hi (hj : j < L.length) (y : ℝ) :
    sideInArc ztkai ztjxx y ↔ lo M Q L j < y ∧ y < hi M Q L j := by
  unfold sideInArc; rw [ite_eq_left (h.lo_lt_hi hj)]

/-- A key outside a chord's closed key interval is in its arc from the larger to the smaller key. -/
theorem sideInArc_hi_lo (hj : j < L.length) {y : ℝ} (h1 : y < lo M Q L j ∨ hi M Q L j < y) :
    sideInArc ztjxx ztkai y := by
  unfold sideInArc; rw [ite_eq_right (not_lt.2 (h.lo_lt_hi hj).le)]; tauto

/-- **Two non-cut positions face the same region iff their keys have the same gap label.** -/
theorem faces_same_iff {p p' : ℕ} {t t' : ℝ} {U U' : Set Point}
    (hU : U ∈ M.regions zthh) (hU' : U' ∈ M.regions zthh)
    (hp : p < M.W.n) (hp' : p' < M.W.n) (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    (hcut : ¬ M.IsCut zthh ztk) (hcut' : ¬ M.IsCut zthh ztjg)
    (hf : M.Faces p t U) (hf' : M.Faces p' t' U') :
    U = U' ↔ gapLabel S ztk = gapLabel S ztjg := by
  zuesp
  have hy' := h.key_ne_of_not_cut hcut'
  rw [h.walk.eq_iff_not_separates h.adm h.finite hU hU' hp hp' ht ht' hcut hcut' hf hf',
    h.gapLabel_eq_iff hy hy']
  have hsep : ∀ j < L.length, (M.Separates (chordSet M Q L j) ztk ztjg ↔
      ¬ (lo M Q L j < p + t ∧ p + t < hi M Q L j ↔
        lo M Q L j < p' + t' ∧ p' + t' < hi M Q L j)) := by
    zun
    zqut
    zqux
    have n3 := hy' _ ztqow
    have n4 := hy' _ ztqox
    simp only [e1, e2] at n1 n2 n3 n4
    rw [h.walk.separates_iff ztxxg hA hB hAB by_grind
      by_grind by_grind by_grind,
      ka, kb, h.sideInArc_lo_hi hj, h.sideInArc_lo_hi hj]
    tauto
  constructor
  · zumgf
    have := H _ ztdnb
    grind
  · intro H c hc
    zufyp
    grind

/-! ## Nesting: the prefix before a chord's first event -/

/-- **The chords open just before the first event of chord `i`** are the chords containing it. -/
theorem prefix_open {i j : ℕ} (hsplit : S = u ++ e1 M Q L i :: v)
    (hi' : i < L.length) (hj : j < L.length) (hij : j ≠ i) :
    (u.map Prod.fst).count j = 1 ↔ Within M Q L i j := by
  zquu
  have hmemS : ∀ f, f ∈ S → f ∈ u ++ e1 M Q L i :: v := by_grind
  rw [BuildSort.count_two (j := j) hnd.1 ztvrt rfl rfl
    (fun f hf hfj => by
      have := (h.mem_cases' ztjyd).2
      grind)]
  have hne1 : e1 M Q L j ≠ e1 M Q L i := fun he => hij ztnxe
  have hne2 : e2 M Q L j ≠ e1 M Q L i := fun he => hij ztnxe
  have hsp1 := BuildSort.mem_split_of_ne (hmemS _ ztqow) hne1
  have hsp2 := BuildSort.mem_split_of_ne (hmemS _ ztqox) hne2
  have hdisj : ∀ f, f ∈ u → f ∉ v := by_grind
  zulkk
  have hlhj := h.lo_lt_hi hj
  have hbi := (h.hi_bounds hi').2
  have haj := (h.lo_bounds hj).1
  have hcyc1 : ∀ x : ℕ, x < L.length → cycDist M.W.n _ _ =
      hi M Q L x - lo M Q L x := fun x hx => by
    unfold cycDist; rw [ite_eq_left (h.lo_lt_hi hx)]
  have hcyc2 : ∀ x : ℕ, x < L.length → cycDist M.W.n _ _ =
      lo M Q L x - hi M Q L x + M.W.n := fun x hx => by
    unfold cycDist; rw [ite_eq_right (not_lt.2 (h.lo_lt_hi hx).le)]
  constructor
  · zuchg
    by_cases h1 : e1 M Q L j ∈ u
    · have h2 : ztpop := by
        grind
      have h2v := hsp2.resolve_left h2
      have le1 := BuildSort.evLe_of_mem_left hs h1
      have le2 := BuildSort.evLe_of_mem_right hs h2v
      unfold EvLe at le1 le2
      zugzh
      rw [hcyc1 i hi', hcyc1 j hj] at le1
      rw [hcyc2 j hj, hcyc1 i hi'] at le2
      zuevy
      rcases le1 with h3 | ⟨h3, h4⟩
      · rcases le2 with h5 | ⟨h5, h6⟩
        · by_contra h7
          exact h.no_cross_keys hj hi' hij by_grind
        grind
      grind
    · have h2 : e2 M Q L j ∈ u := by
        grind
      zulhk
      have le1 := BuildSort.key_le_of_evLe ztnjr
      have le2 := BuildSort.key_le_of_evLe (BuildSort.evLe_of_mem_right hs h1v)
      zugzh
      grind
  · zukol
    have h2 : ztpop := by
      zukji
      have := BuildSort.key_le_of_evLe ztnjr
      zqur
      linarith
    have h1 : e1 M Q L j ∈ u := by
      by_contra h1
      zulhk
      have le := BuildSort.evLe_of_mem_right hs h1v
      unfold EvLe at le
      simp only [e1] at le
      rw [hcyc1 i hi', hcyc1 j hj] at le
      rcases le with h3 | ⟨h3, h4⟩
      · linarith
      · exact h.keys_ne hi' hj ztjko by_grind
    grind

/-- **A region touching chord `i`, faced at a non-cut key `y`**: for every other chord `j`, `y` is
strictly inside `j` iff `i` lies within `j`. -/
theorem touch_within {U : Set Point} (hU : U ∈ M.regions zthh) {p : ℕ} {t : ℝ}
    (hp : p < M.W.n) (ht : t ∈ Ioo (0 : ℝ) 1) (hcut : ¬ M.IsCut zthh ztk)
    (hf : M.Faces p t U) {i j : ℕ} (hi' : i < L.length) (hj : j < L.length) (hij : j ≠ i)
    (htouch : TouchesIn M.D ztrz U) :
    (lo M Q L j < p + t ∧ p + t < hi M Q L j) ↔ Within M Q L i j := by
  zuesp
  zqut
  obtain ⟨pc, pd, tc, td, hC, hD, -, kc, kd⟩ := h.att_lo_hi hi'
  have hne : chordSet M Q L i ≠ chordSet M Q L j := fun e => hij (chordSet_inj h.valid hj hi' e.symm)
  zqux
  simp only [e1, e2] at n1 n2
  have hlhi := h.lo_lt_hi hi'
  constructor
  · zulmv
    by_contra hw
    unfold Within at hw
    have hout : ∃ (q : ℕ) (τ : ℝ), SideAttach M.W ztrz q τ ∧
        sideInArc ztbd ztbf zttwq := by
      zukxe
      by_cases h1 : lo M Q L j ≤ lo M Q L i
      · have h2 : hi M Q L j < hi M Q L i := by_simp_all
        exact ⟨pd, td, hD, by rw [kd]; exact h.sideInArc_hi_lo hj ztffu⟩
      · exact ⟨pc, tc, hC, by rw [kc]; exact h.sideInArc_hi_lo hj by_simp_all⟩
    obtain ⟨q, τ, hQ, hq⟩ := hout
    exact h.walk.not_touches_of_split h.adm h.finite zterh ztdnb hne
      hA hB hAB hU hp ht (by rw [ka, kb, h.sideInArc_lo_hi hj]; omega) hf hQ hq htouch
  · zukol
    by_contra hin
    have hy' : sideInArc ztjxx ztkai ztk := by
      apply h.sideInArc_hi_lo hj
      grind
    have hin2 : ∃ (q : ℕ) (τ : ℝ), SideAttach M.W ztrz q τ ∧
        sideInArc ztbf ztbd zttwq := by
      zukxe
      rcases hw1.lt_or_eq with h1 | h1
      · exact ⟨pc, tc, hC, by rw [kc, h.sideInArc_lo_hi hj]; grind⟩
      · have h2 :=
          lt_of_le_of_ne hw2 fun h2 => h.keys_ne hi' hj ztjko by_simp_all
        exact ⟨pd, td, hD, by rw [kd, h.sideInArc_lo_hi hj]; simp_all⟩
    obtain ⟨q, τ, hQ, hq⟩ := hin2
    exact h.walk.not_touches_of_split h.adm h.finite zterh ztdnb hne
      hB hA zteno hU hp ht by_simp_all hf hQ hq htouch

/-! ## The region of a label -/

/-- **Every non-cut position faces the region of its gap label.** -/
theorem faces_reg (hp : p < M.W.n) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hcut : ¬ M.IsCut zthh ztk) :
    reg M Q L S ztxxf ∈ M.regions zthh ∧
      M.Faces p t (reg M Q L S ztxxf) := by
  classical
  obtain ⟨U, hU, hf⟩ := h.walk.exists_faces_of_not_cut h.adm h.finite hp ht hcut
  have hh : ∃ U ∈ M.regions _, ∃ (p' : ℕ) (t' : ℝ), p' < M.W.n ∧ 0 < t' ∧ t' < 1 ∧
      ¬ M.IsCut _ ztjg ∧ gapLabel S ztjg = gapLabel S _ ∧
        M.Faces p' t' U := ⟨U, hU, p, t, hp, ht.1, ht.2, hcut, rfl, hf⟩
  have hreg : reg M Q L S ztxxf = hh.choose := by
    unfold reg; grind
  obtain ⟨hU', p', t', hp', ht0', ht1', hcut', hlab, hf'⟩ := hh.choose_spec
  have heq : hh.choose = U :=
    (h.faces_same_iff hU' hU hp' hp by_grind ht hcut' hcut hf' hf).2 hlab
  rw [hreg, heq]
  zubfo

/-- The region faced at a non-cut position is the region of its gap label. -/
theorem reg_eq_of_faces (hp : p < M.W.n) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hcut : ¬ M.IsCut zthh ztk) {U : Set Point} (hU : U ∈ M.regions zthh)
    (hf : M.Faces p t U) : reg M Q L S ztxxf = U := by
  obtain ⟨hR, hfR⟩ := h.faces_reg hp ht hcut
  exact WalkAx.faces_unique hR hU hfR hf
omit h in
/-- The prefix of the chord word before the event at the end of `u`. -/
theorem take_word (_h : Ctx M Q L S) {u v : List Ev} {e : Ev} (hsplit : S = u ++ e :: v) :
    (S.map Prod.fst).take u.length = u.map Prod.fst := by
  simp_all
omit h in
theorem take_word_succ (_h : Ctx M Q L S) {u v : List Ev} {e : Ev} (hsplit : S = u ++ e :: v) :
    (S.map Prod.fst).take ztfva = u.map Prod.fst ++ [e.1] := by
  grind

/-- The first event of a chord is not in the prefix before it, nor is its second event. -/
theorem count_prefix_self {i : ℕ} (hsplit : S = u ++ e1 M Q L i :: v)
    (hi' : i < L.length) : (u.map Prod.fst).count i = 0 := by
  zquu
  rw [BuildSort.count_two (j := i) hnd.1 (h.e1_ne_e2 hi') rfl rfl
    (fun f hf hfj => by
      have := (h.mem_cases' ztjyd).2
      grind)]
  have h1 : e1 M Q L i ∉ u := by_grind
  have h2 : e2 M Q L i ∉ u := by
    zukji
    have := BuildSort.key_le_of_evLe ztnjr
    zqur
    linarith [h.lo_lt_hi hi']
  grind

/-- The chord indices of the prefix are chords of the list. -/
theorem count_prefix_ge {e : Ev} (hsplit : S = u ++ e :: v) {j : ℕ}
    (hj : L.length ≤ j) : (u.map Prod.fst).count j = 0 := by
  zuelj

  have := (h.mem_cases ztjyd).1
  omega

/-- **The label right after the first event of chord `i` is `some i`.** -/
theorem label_first {i : ℕ} (hsplit : S = u ++ e1 M Q L i :: v)
    (hi' : i < L.length) : BuildStack.label ztbuq ztfva = some i := by
  zquq
  rw [BuildStack.label_eq htw hnc, h.take_word_succ hsplit, show (e1 M Q L i).1 = i from rfl,
    BuildStack.openList_snoc_open (h.count_prefix_self hsplit hi')]
  rfl

/-- **A region touching chord `i` on the outside** has the label before the first event of `i`. -/
theorem label_outside {i : ℕ} (hsplit : S = u ++ e1 M Q L i :: v)
    (hi' : i < L.length) {U : Set Point} (hU : U ∈ M.regions zthh) {p : ℕ} {t : ℝ}
    (hp : p < M.W.n) (ht : t ∈ Ioo (0 : ℝ) 1) (hcut : ¬ M.IsCut zthh ztk)
    (hf : M.Faces p t U) (htouch : TouchesIn M.D ztrz U)
    (hout : ¬ (lo M Q L i < p + t ∧ p + t < hi M Q L i)) :
    gapLabel S ztk = BuildStack.label ztbuq u.length := by
  zquq
  zuesp
  unfold gapLabel
  rw [BuildStack.label_eq_iff htw hnc, BuildSort.take_map_cntBelow h.sorted hy,
    h.take_word hsplit]
  zujbf
  zuebv
  · zukrm
    zubsz
    · zuhqj

    · rw [h.prefix_open hsplit hi' hj hji]
      zufsd
  · rw [h.count_ge hj, h.count_prefix_ge hsplit hj]

/-- **A region touching chord `i` on the inside** has the label `some i`. -/
theorem label_inside {i : ℕ} (hsplit : S = u ++ e1 M Q L i :: v)
    (hi' : i < L.length) {U : Set Point} (hU : U ∈ M.regions zthh) {p : ℕ} {t : ℝ}
    (hp : p < M.W.n) (ht : t ∈ Ioo (0 : ℝ) 1) (hcut : ¬ M.IsCut zthh ztk)
    (hf : M.Faces p t U) (htouch : TouchesIn M.D ztrz U)
    (hin : lo M Q L i < p + t ∧ p + t < hi M Q L i) :
    gapLabel S ztk = BuildStack.label ztbuq ztfva := by
  zquq
  zuesp
  unfold gapLabel
  rw [BuildStack.label_eq_iff htw hnc, BuildSort.take_map_cntBelow h.sorted hy,
    h.take_word_succ hsplit, show (e1 M Q L i).1 = i from rfl]
  zujbf
  rw [count_append, count_singleton']
  zuebv
  · zukrm
    zubsz
    · zuhqj

    · rw [ite_eq_right (Ne.symm hji), add_zero, h.prefix_open hsplit hi' hj hji]
      zufsd
  · have hji : i ≠ j := by_omega
    rw [h.count_ge hj, h.count_prefix_ge hsplit hj, ite_eq_right hji]

/-! ## The two sides of a chord -/

/-- **The two sides of chord `i`** are the regions of the labels right after (inside) and right
before (outside) its first event: if its first event is its left endpoint, the inside is below
the chord and the outside above; otherwise the inside is above and the outside below. -/
theorem sides {i : ℕ} (hsplit : S = u ++ e1 M Q L i :: v)
    (hi' : i < L.length) :
    reg M Q L S (BuildStack.label ztbuq ztfva) ∈ M.regions zthh ∧
      reg M Q L S (BuildStack.label ztbuq u.length) ∈ M.regions zthh ∧
      (kl M Q L i < kr M Q L i →
        M.BelowOf ztrz ztybd ∧
        M.AboveOf ztrz ztybc) ∧
      (kr M Q L i < kl M Q L i →
        M.AboveOf ztrz ztybd ∧
        M.BelowOf ztrz ztybc) := by
  set c := chordSet M Q L i with hc
  have hcF : c ∈ famOf M Q L := chordSet_mem hi'
  zuesh
  obtain ⟨Up, Dn, hUp, hDn, -, hside, htouch⟩ := chordSides_of_system hsys hcF
  have hAbove : M.AboveOf c Up := fun z hz hzD => by_simp_all
  have hBelow : M.BelowOf c Dn := fun z hz hzD => by_simp_all
  obtain ⟨pu, tu, hpu, htu0, htu1, hcu, hfu⟩ := h.walk.exists_faces_nc h.adm h.finite hUp
  obtain ⟨pd, td, hpd, htd0, htd1, hcd, hfd⟩ := h.walk.exists_faces_nc h.adm h.finite hDn
  have htU : TouchesIn M.D c Up := by_simp_all
  have htD : TouchesIn M.D c Dn := by_simp_all
  -- the attachments and the midpoints
  have hA := h.attL hi'
  have hB := h.attR hi'
  have hAB := h.pts_ne hi'
  set pl := sidePt M.W (crec L i).lp _ with hpl
  set pr := sidePt M.W (crec L i).rp _ with hpr
  obtain ⟨hcab, hy, hopen, -, -⟩ := h.walk.attach_seg (h.adm hcF) hA hB hAB
  have hlt : pl.1 < pr.1 := h.pos_lt hi'
  have hmid : Geometry.lerp pl pr ztcn ∈ c := by
    zvmyh; exact Geometry.lerp_mem_segment _ _ by_norm_num by_norm_num
  have hmidD : Geometry.lerp pl pr ztcn ∈ M.D := by_grind
  have hmid' : Geometry.lerp pr pl ztcn ∈ c := by
    rw [hcab, Geometry.segment_comm]; exact Geometry.lerp_mem_segment _ _ by_norm_num by_norm_num
  have hmidD' : Geometry.lerp pr pl ztcn ∈ M.D :=
    WalkAx.open_rev hopen _ by_grind
  -- `Up` is not faced strictly between the left and the right endpoint
  have hnU : ¬ sideInArc ztciq ztcir (pu + tu) := by
    zulmv
    refine h.walk.not_left_of_after h.adm hcF hA hB hAB hUp hpu by_grind hin hfu ?_
    refine (eventually_mul_pos (hAbove _ hmid hmidD) zteau).mono fun δ hδ => ?_
    rw [Chazelle.Core.offset_mid_ab hy]; exact hδ
  -- `Dn` is not faced strictly between the right and the left endpoint
  have hnD : ¬ sideInArc ztcir ztciq zttwd := by
    zulmv
    refine h.walk.not_left_of_after h.adm hcF hB hA zteno hDn hpd by_grind hin hfd ?_
    refine (eventually_mul_pos (hBelow _ hmid' hmidD') zteau).mono fun δ hδ => ?_
    rw [Chazelle.Core.offset_mid_ab hy.symm]
    grind
  -- the keys differ from the non-cut keys
  have nU1 := h.key_ne_of_not_cut hcu _ ztvru
  have nU2 := h.key_ne_of_not_cut hcu _ ztvrv
  have nD1 := h.key_ne_of_not_cut hcd _ ztvru
  have nD2 := h.key_ne_of_not_cut hcd _ ztvrv
  simp only [eL, eR] at nU1 nU2 nD1 nD2
  have hregU := h.reg_eq_of_faces hpu by_grind hcu hUp hfu
  have hregD := h.reg_eq_of_faces hpd by_grind hcd hDn hfd
  rcases lt_or_gt_of_ne ztvrw with hk | hk
  · have hlo : lo M Q L i = kl M Q L i := min_eq_left hk.le
    have hhi : hi M Q L i = kr M Q L i := max_eq_right hk.le
    -- `Up` outside, `Dn` inside
    have hUout : ¬ (lo M Q L i < pu + tu ∧ pu + tu < hi M Q L i) := by
      zuolp; intro h'; apply hnU; unfold sideInArc; grind
    have hDin : lo M Q L i < pd + td ∧ pd + td < hi M Q L i := by
      zubva
      unfold sideInArc at hnD; grind
    have e1' := h.label_outside hsplit hi' hUp hpu by_grind hcu hfu htU hUout
    have e2' := h.label_inside hsplit hi' hDn hpd by_grind hcd hfd htD hDin
    zquw
    exact ⟨hDn, hUp, by_grind, by_grind⟩
  · have hlo : lo M Q L i = kr M Q L i := min_eq_right hk.le
    have hhi : hi M Q L i = kl M Q L i := max_eq_left hk.le
    -- `Up` inside, `Dn` outside
    have hUin : lo M Q L i < pu + tu ∧ pu + tu < hi M Q L i := by
      zubva
      unfold sideInArc at hnU; grind
    have hDout : ¬ (lo M Q L i < pd + td ∧ pd + td < hi M Q L i) := by
      zuolp; intro h'; apply hnD; unfold sideInArc; grind
    have e1' := h.label_inside hsplit hi' hUp hpu by_grind hcu hfu htU hUin
    have e2' := h.label_outside hsplit hi' hDn hpd by_grind hcd hfd htD hDout
    zquw
    exact ⟨hUp, hDn, by_grind, by_grind⟩

/-! ## Regions and labels correspond -/

/-- Every label of the stack pass is a label of a chord of the list, or the root. -/
theorem label_ok (m : ℕ) : LabelOK L.length (BuildStack.label ztbuq m) := by
  zquq
  intro i hl
  rw [BuildStack.label_eq htw hnc] at hl
  have hi := BuildStack.mem_openList.1 (mem_of_mem_head? hl)
  have hmem :=
    mem_of_mem_take (count_pos_iff.1 (by omega : 0 < ((S.map Prod.fst).take m).count i))
  obtain ⟨f, hf, rfl⟩ := mem_map.1 hmem
  exact (h.mem_cases hf).1
omit h in
/-- A region of a label is faced at a non-cut key with that label. -/
theorem reg_realized {ℓ : Option ℕ} (hr : reg M Q L S ℓ ∈ M.regions zthh) :
    ∃ (p : ℕ) (t : ℝ), p < M.W.n ∧ 0 < t ∧ t < 1 ∧ ¬ M.IsCut zthh ztk ∧
      gapLabel S ztk = ℓ ∧ M.Faces p t (reg M Q L S ℓ) := by
  classical
  by_cases hh : ∃ U ∈ M.regions zthh, ∃ (p : ℕ) (t : ℝ), p < M.W.n ∧ 0 < t ∧ t < 1 ∧
      ¬ M.IsCut zthh ztk ∧ gapLabel S ztk = ℓ ∧ M.Faces p t U
  · have hreg : reg M Q L S ℓ = hh.choose := by unfold reg; grind
    grind
  · have hreg : reg M Q L S ℓ = ∅ := by unfold reg; grind
    rw [hreg] at hr
    obtain ⟨x, hx⟩ := Chazelle.Chain.regionsIn_nonempty hr
    grind

/-- The first event of the sorted list is the first event of its chord. -/
theorem first_split (hK : 0 < L.length) :
    ∃ i < L.length, ∃ v, S = [] ++ e1 M Q L i :: v := by
  zufll
  · exact absurd (hS ▸ h.e1_mem hK) (List.not_mem_nil)
  · have hf : f ∈ S := by_simp_all
    obtain ⟨hi, hc⟩ := h.mem_cases' hf
    refine ⟨f.1, hi, v, ?_⟩
    zunk
    · grind
    · exfalso
      have hs := h.sorted
      rw [hS, pairwise_cons] at hs
      have h1 : e1 M Q L f.1 ∈ v := by
        have := h.e1_mem hi
        rw [hS, mem_cons] at this
        exact this.resolve_left fun he => h.e1_ne_e2 hi by_grind
      have := BuildSort.key_le_of_evLe (hs.1 _ h1)
      zvnmd at this
      zqur
      linarith [h.lo_lt_hi hi]

/-- **The regions of the labels are exactly the regions of the submap, each once.** -/
theorem regions_corr :
    (∀ ℓ, LabelOK L.length ℓ → reg M Q L S ℓ ∈ M.regions zthh) ∧
      (∀ ℓ ℓ', LabelOK L.length ℓ → LabelOK L.length ℓ' → reg M Q L S ℓ = reg M Q L S ℓ' →
        ℓ = ℓ') ∧
      (∀ U ∈ M.regions zthh, ∃ ℓ, LabelOK L.length ℓ ∧ reg M Q L S ℓ = U) := by
  zquq
  zuesh
  have hmemR : ∀ ℓ, LabelOK L.length ℓ → reg M Q L S ℓ ∈ M.regions zthh := by
    zulnr
    rcases ℓ with _ | i
    · -- the root
      zujcu
      · -- no chord: every non-cut position has the root label
        obtain ⟨hfin, hcard⟩ := hsys.regionsIn_finite_ncard h.walk.preconn h.walk.nonempty subset_rfl
        have hne : ztrzb :=
          Set.nonempty_of_ncard_ne_zero (by
            zuhcg
            omega)
        obtain ⟨U, hU⟩ := hne
        zquv
        have hS : ztumc := by
          zufll
          · rfl
          · have := (h.mem_cases (by simp_all : f ∈ S)).1; omega
        have hlab : ztzqf := by
          unfold gapLabel; zvojf; rfl
        have := (h.faces_reg hp by_simp_all hcut).1
        simp_all
      · obtain ⟨i, hi, v, hsplit⟩ := h.first_split hK
        have := (h.sides hsplit hi).2.1
        tauto
    · have hi := hℓ i rfl
      obtain ⟨u, v, hsplit⟩ := List.append_of_mem (h.e1_mem hi)
      have := (h.sides hsplit hi).1
      rwa [h.label_first hsplit hi] at this
  refine ⟨hmemR, fun ℓ ℓ' hℓ hℓ' heq => ?_, fun U hU => ?_⟩
  · obtain ⟨p, t, hp, ht0, ht1, hcut, hlab, hf⟩ := reg_realized (hmemR ℓ hℓ)
    obtain ⟨p', t', hp', ht0', ht1', hcut', hlab', hf'⟩ := reg_realized (hmemR ℓ' hℓ')
    rw [← hlab, ← hlab']
    exact (h.faces_same_iff by_simp_all by_simp_all hp hp' by_simp_all by_simp_all hcut hcut'
      hf hf').1 heq
  · zquv
    refine ⟨gapLabel S _, h.label_ok _, h.reg_eq_of_faces hp by_simp_all hcut hU hf⟩
end Ctx
end
end BuildRegions
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqbgu" : tactic => `(tactic| (obtain ⟨c', k, ex, hk, hb1, hb⟩ := H
                                           exact ⟨c', k, ex, hk, exec_frameB ex by_decide, hb1, hb⟩))
local macro "zqbgv" : tactic => `(tactic| (zunzy
                                           simp only [SignTest, SymPt.eval, BetterC, xe, ee, ← he, ← heb, hhz]
                                           grind))
local macro "zqbgw" : tactic => `(tactic| have hQn : ztx := shear_n _ _)
local macro "zqbgx" : tactic => `(tactic| (unfold bestOf
                                           rw [R₆ 120050 by_decide by_decide, R₆ 120052 by_decide by_decide]
                                           exact hbo₅))
local macro "zqbgy" : tactic => `(tactic| obtain ⟨c₁, e₁, v₁, -⟩ := const_exec hw 120063 1 by_omega)
local macro "zqbgz" : tactic => `(tactic| (zunzy
                                           simp only [SignTest, SymPt.eval, Ahead, xe]
                                           grind))
local macro "zqbha" : tactic => `(tactic| obtain ⟨c', k, ex, hk, hb', hv⟩ := H)
set_option hygiene true

/-!
# Lemma 3.6 (WP-H), RAM part 2: testing one edge of the chain

`edgeT` tests the chain edge `ci` (register `120060`) against the query ray and keeps the best
hit so far (registers `120050` flag, `120051` its edge of `Q`, `120052` its chain edge):

1. `e := (s + ci) mod n`, `e₁ := (e + 1) mod n` (`120061`, `120062`);
2. the height of the ray (vertex `hz`, register `120023`) is in the range of edge `e`: `hz = e`,
   `hz = e₁`, or two height tests with the sign kernel (`120063`);
3. the point of the edge at that height is ahead of the origin (always for a box origin; one
   abscissa test otherwise) (`120066`);
4. it improves on the best hit (one abscissa test) (`120067`); then it becomes the best hit.

Registers read: `120010` `n`, `120011` the constant `1`, `120015` `s`, `120023` `hz`, `120024`
the direction bit (`1`: rightwards), `120025 … 120027` the origin (kind `0, 1`: a symbolic point;
`2`: a box point), `120048` the constant `2`.  Main result: `edgeT_exec`.
-/
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ
@[expose] public section
def modSub (r nr : ℕ) : Stmt := .ifLtN r nr .skip ztnch

/-- Run `S` if registers `a` and `b` are equal, `T` otherwise. -/
def ifEq (a b : ℕ) (S T : Stmt) : Stmt := .ifLtN a b T (.ifLtN b a T S)
theorem modSub_exec {P : Polygon} {W : ℕ} {r nr : ℕ} (_hr : r ≠ nr) (c : Config)
    (hw : WordsBounded W c) (hv : c.nreg r < 2 * c.nreg nr) :
    ∃ c' k, Exec P W (modSub r nr) c c' k ∧ k ≤ 3 ∧ c'.nreg r = c.nreg r % c.nreg nr ∧
      ztbiv ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold modSub
  zucfj
  · refine spec_ifLtN_true h (spec_skip hw ⟨by_omega, Nat.mod_eq_of_lt h |>.symm, by_omega,
      rfl, rfl, rfl, rfl⟩)
  · refine spec_ifLtN_false h (spec_instr ztpyg fun _ => ?_)
    refine ⟨by_omega, ?_, fun r' h' => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
      zul
    simp_all

/-! ## The semantics of one test -/
section Sem
variable (Q : Polygon) (s hz : ℕ) (σ : ℝ) (zo : Option Point)

/-- The edge of `Q` of chain edge `ci`. -/
def eIdx (n s ci : ℕ) : ℕ := (s + ci) % n

/-- The point at abscissa `x` is ahead of the origin (`none`: a box origin, always ahead). -/
def Ahead (x : ℝ) : Prop :=
  match zo with
  | none => True
  | some z => (σ = 1 ∧ z.1 < x) ∨ (σ = -1 ∧ x < z.1)

/-- **The ray hits chain edge `ci`** (height in range, point ahead). -/
def HitC (ci : ℕ) : Prop :=
  Spans Q ztcda hz ∧ Ahead σ zo (xe Q ztcda hz)

/-- **The hit on chain edge `ci` comes before the hit on `cb`.** -/
def BetterC (ci cb : ℕ) : Prop :=
  (σ = 1 ∧ xe Q ztcda hz < xe Q ztrpa hz) ∨
    (σ = -1 ∧ xe Q ztrpa hz < xe Q ztcda hz)
open Classical in
/-- **One step of the scan**: the new best chain edge. -/
noncomputable def upd1 (best : Option ℕ) (ci : ℕ) : Option ℕ :=
  if HitC Q s hz σ zo ci ∧ (∀ cb, best = some cb → BetterC Q s hz σ ci cb) then some ci else best
end Sem

/-- The best chain edge held in the registers. -/
def bestOf (c : Config) : Option ℕ := if c.nreg 120050 = 1 then some zthuh else none

/-- The best-hit registers are consistent. -/
def BestOK (n s mb : ℕ) (c : Config) : Prop :=
  c.nreg 120050 ≤ 1 ∧ (c.nreg 120050 = 1 → c.nreg 120051 = eIdx n s zthuh ∧
    c.nreg 120052 < mb)

/-- The direction of a direction bit. -/
noncomputable def sgnOf (b : ℕ) : ℝ := if b = 1 then 1 else -1

/-- **The origin registers** `120025 …` describe the origin `zo` (`none`: a box origin). -/
def OriginOK (P : Polygon) (c : Config) (zo : Option Point) : Prop :=
  (c.nreg 120025 = 2 ∧ zo = none) ∨
    (c.nreg 120025 < 2 ∧ ∃ p : SymPt, p.Lt P.n ∧ SymPtIn c 120025 p ∧ zo = some (p.eval zta))

/-- **The constants the edge test reads.** -/
structure EConst (P : Polygon) (s hz : ℕ) (σb : ℕ) (zo : Option Point) (c : Config) : Prop where
  n : c.nreg 120010 = P.n
  one : c.nreg 120011 = 1
  two : c.nreg 120048 = 2
  rs : c.nreg 120015 = s
  rhz : c.nreg 120023 = hz
  rσ : c.nreg 120024 = σb
  σle : σb ≤ 1
  org : OriginOK P c zo
  s_lt : s < P.n
  hz_lt : hz < P.n

/-- The registers written by the edge test. -/
def BE (r : ℕ) : Bool :=
  Bk r || decide (120050 ≤ r ∧ r ≤ 120052) || decide (120061 ≤ r ∧ r ≤ 120067)

/-! ## The program -/

/-- The height range test (`120063 := 1` iff the height of `hz` is in the range of `e`). -/
def spansS : Stmt :=
  let gen : Stmt :=
    .seq (sgnS 1 ztcpi zthql ztcpi)
      (.seq (.instr (.copyN 120064 10010))
        (.seq (sgnS 1 zthql ztuwa ztcpi)
          (.seq (.instr (.copyN 120065 10010))
            (ifEq 120064 120065 ztfem ztoti))))
  ifEq 120023 120061 ztfem
    (ifEq 120023 120062 ztfem gen)

/-- The ahead test (`120066`). -/
def aheadS : Stmt :=
  .ifLtN 120025 120048
    (.ifLtN 120024 120011
      (.seq (sgnS 0 ztdrv ztfez ztcpi)
        ztouw)
      (.seq (sgnS 0 ztfez ztdrv ztcpi)
        ztouw))
    (.instr (.constN 120066 1))

/-- Take the tested edge as the best hit. -/
def takeS : Stmt := block [.constN 120050 1, .copyN 120051 120061, .copyN 120052 120060]

/-- The comparison with the best hit (`120067`), then the update. -/
def betterS : Stmt :=
  .ifLtN 120050 120011 takeS
    (.seq (.ifLtN 120024 120011
        (.seq (sgnS 0 ztdru ztdrv ztcpi)
          ztoux)
        (.seq (sgnS 0 ztdrv ztdru ztcpi)
          ztoux))
      (.ifLtN 120067 120011 .skip takeS))

/-- **The edge test.** -/
def edgeT : Stmt :=
  .seq (.instr (.addN 120061 120015 120060)) (.seq (modSub 120061 120010)
    (.seq (.instr (.addN 120062 120061 120011)) (.seq (modSub 120062 120010)
      (.seq spansS (.ifLtN 120063 120011 .skip
        (.seq aheadS (.ifLtN 120066 120011 .skip betterS)))))))
theorem wr_edgeT : wr BE edgeT = true := by_decide
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ
@[expose] public section

/-! ## Execution lemmas -/
section Exec
variable {P : Polygon} {W : ℕ}
variable {a b : ℕ} {S T : Stmt} {c c' : Config} {k : ℕ}
theorem ifEq_eq_exec (h : c.nreg a = c.nreg b)
    (hS : Exec P W S c c' k) : Exec P W ztqrh c c' ztqsd :=
  .ifLtN_false by_omega (.ifLtN_false by_omega hS)
theorem ifEq_ne_exec (h : c.nreg a ≠ c.nreg b)
    (hT : Exec P W T c c' k) : ∃ k', Exec P W ztqrh c c' k' ∧ k' ≤ k + 3 := by
  zujk
  · tauto
  · exact ⟨_, .ifLtN_false by_omega (.ifLtN_true hgt hT), by_omega⟩

/-- The value of a `copyN` after a statement. -/
theorem copy_exec {c : Config} (hw : WordsBounded W c) (r a : ℕ) :
    ∃ c', Exec P W ztdsf c c' 1 ∧ c'.nreg r = c.nreg a ∧
      ztbiv :=
  ⟨_, Exec.copyN hw r a, by config_simp, by_simp_all⟩
theorem const_exec {c : Config} (hw : WordsBounded W c) (r v : ℕ) (hv : v ≤ W) :
    ∃ c', Exec P W ztcyq c c' 1 ∧ c'.nreg r = v ∧
      ztbiv :=
  ⟨_, Exec.constN hw r v hv, by config_simp, by_simp_all⟩

/-- **The height range test.** -/
theorem spansS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (hD : DistinctHeights zta)
    (c : Config) (hw : WordsBounded W c) (he : c.nreg 120061 < P.n)
    (he1 : c.nreg 120062 = (c.nreg 120061 + 1) % P.n) (hhz : c.nreg 120023 < P.n) :
    ∃ c' k, Exec P W spansS c c' k ∧ k ≤ 520 ∧ FrameB BE c c' ∧ c'.nreg 120063 ≤ 1 ∧
      (c'.nreg 120063 = 1 ↔ Spans zta ztvhi ztvhh) := by
  zqbgw
  zuiz
  set e := c.nreg 120061 with he_def
  set e1 := c.nreg 120062 with he1_def
  set hz := c.nreg 120023 with hz_def
  have he1n : e1 < P.n := by zuots; exact Nat.mod_lt _ hn
  have hsp := spans_iff _ hD (show e < (Qof P).n by omega) (show hz < (Qof P).n by omega)
  rw [hQn, ← he1] at hsp
  suffices H : ∃ c' k, Exec P W spansS c c' k ∧ k ≤ 520 ∧ c'.nreg 120063 ≤ 1 ∧
      (c'.nreg 120063 = 1 ↔ Spans _ e hz) by
    zqbgu
  by_cases h1 : hz = e
  · zqbgy
    refine ⟨c₁, _, ifEq_eq_exec h1 e₁,
      by omega, by rw [v₁], ?_⟩
    simp_all
  by_cases h2 : hz = e1
  · zqbgy
    obtain ⟨k', ex', hk'⟩ := ifEq_ne_exec h1
      (ifEq_eq_exec h2 e₁)
    refine ⟨c₁, k', ex', by_omega, by rw [v₁], ?_⟩
    simp_all
  -- two height tests
  have hl : ∀ i, i < P.n → (SymPt.vtx i).Lt P.n := fun i hi => hi
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, s₁⟩ := sgnS_exec (P := P) hG hW 1 by_norm_num
    ztcpi zthql ztcpi c hw by_decide by_decide by_decide
    rfl rfl rfl zttnt (hl _ hhz) zttnt
  obtain ⟨c₂, e₂, v₂, r₂⟩ := copy_exec (P := P) e₁.wb_right 120064 10010
  have g₂ := fun r hr hr' =>
    (r₂ r hr').trans ztjwt
  have x61 : c₂.nreg 120061 = e := g₂ _ by_decide by_decide
  have x62 : c₂.nreg 120062 = e1 := g₂ _ by_decide by_decide
  have x23 : c₂.nreg 120023 = hz := g₂ _ by_decide by_decide
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, b₃, s₃⟩ := sgnS_exec (P := P) hG hW 1 by_norm_num
    zthql ztuwa ztcpi c₂ e₂.wb_right by_decide by_decide by_decide
    rfl rfl rfl by_simp_all by_simp_all
    by_simp_all
  obtain ⟨c₄, e₄, v₄, r₄⟩ := copy_exec (P := P) e₃.wb_right 120065 10010
  rw [x61, x62, x23] at s₃
  simp only [SignTest, SymPt.eval] at s₁ s₃
  have t1 : c₄.nreg 120064 = c₁.nreg 10010 := by
    rw [r₄ _ by_decide, f₃.1 _ by_decide, v₂]
  have t2 := v₄
  have ne1 := hD hz e by_omega by_omega h1
  have ne2 := hD hz e1 by_omega by_omega h2
  -- the final comparison of the two bits
  obtain ⟨c₅, k₅, e₅, hk₅, u₅, v₅⟩ : ∃ c₅ k₅, Exec P W (ifEq 120064 120065
      ztfem ztoti) c₄ c₅ k₅ ∧ k₅ ≤ 6 ∧
      c₅.nreg 120063 ≤ 1 ∧ (c₅.nreg 120063 = 1 ↔ c₁.nreg 10010 = c₃.nreg 10010) := by
    by_cases hq : c₄.nreg 120064 = c₄.nreg 120065
    · obtain ⟨c₅, e₅, v₅, -⟩ := const_exec e₄.wb_right 120063 1 by_omega
      refine ⟨c₅, _, ifEq_eq_exec hq e₅, by_omega, by rw [v₅], ?_⟩
      omega
    · obtain ⟨c₅, e₅, v₅, -⟩ := const_exec e₄.wb_right 120063 0 by_omega
      obtain ⟨k', ex', hk'⟩ := ifEq_ne_exec hq e₅
      refine ⟨c₅, k', ex', by_omega, by_omega, ?_⟩
      omega
  have ex : Exec P W _
      c c₅ _ := .seq e₁ ztbq
  obtain ⟨k₆, ex₆, hk₆⟩ := ifEq_ne_exec (S := .instr ztsoo) h2 ex
  obtain ⟨k₇, ex₇, hk₇⟩ := ifEq_ne_exec (S := .instr ztsoo) h1 ex₆
  refine ⟨c₅, k₇, ex₇, by_omega, u₅, ?_⟩
  rw [v₅, hsp]
  simp only [h1, h2, false_or, or_self]
  constructor
  · intro hq
    by_cases ha : ((Qof P).vtx e).2 < ((Qof P).vtx hz).2
    · grind
    · have h0 : ztupx := by_grind
      right
      refine zthma
      grind
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · grind
    grind

/-- **The ahead test.** -/
theorem aheadS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {σb : ℕ} {zo : Option Point}
    (c : Config) (hw : WordsBounded W c) (he : c.nreg 120061 < P.n) (hhz : c.nreg 120023 < P.n)
    (hone : c.nreg 120011 = 1) (htwo : c.nreg 120048 = 2) (hσ : c.nreg 120024 = σb) (hσ1 : σb ≤ 1)
    (horg : OriginOK P c zo) :
    ∃ c' k, Exec P W aheadS c c' k ∧ k ≤ 250 ∧ FrameB BE c c' ∧ c'.nreg 120066 ≤ 1 ∧
      (c'.nreg 120066 = 1 ↔ Ahead ztevk zo (xe zta ztvhi ztvhh)) := by
  suffices H : ∃ c' k, Exec P W aheadS c c' k ∧ k ≤ 250 ∧ c'.nreg 120066 ≤ 1 ∧
      (c'.nreg 120066 = 1 ↔ Ahead _ zo _) by
    zqbgu
  rcases horg with ⟨hk2, rfl⟩ | ⟨hk2, p, hp, hpin, rfl⟩
  · obtain ⟨c₁, e₁, v₁, -⟩ := const_exec hw 120066 1 by_omega
    exact ⟨c₁, _, .ifLtN_false by_omega e₁, by_omega, by rw [v₁], by_tauto⟩
  · have hle : (SymPt.onEdge _ _).Lt P.n := ⟨he, hhz⟩
    have hlv : ztrff := he
    zujtv
    · zugno
      obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, s₁⟩ := sgnS_exec hG hW 0 by_norm_num
        ztdrv ztfez ztcpi c hw by_decide by_decide
        by_decide rfl hpin rfl hle hp hlv
      zuean
      refine ⟨c₂, _, .ifLtN_true by_omega (.ifLtN_true by_omega ztyv), by_omega,
        by omega, ?_⟩
      zqbgz
    · zugnp
      obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, s₁⟩ := sgnS_exec hG hW 0 by_norm_num
        ztfez ztdrv ztcpi c hw by_decide by_decide
        by_decide hpin rfl rfl hp hle hlv
      zuean
      refine ⟨c₂, _, .ifLtN_true by_omega (.ifLtN_false by_omega ztyv), by_omega,
        by omega, ?_⟩
      zqbgz

/-- **Taking the tested edge.** -/
theorem takeS_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W takeS c c' k ∧ k ≤ 3 ∧ c'.nreg 120050 = 1 ∧
      c'.nreg 120051 = c.nreg 120061 ∧ c'.nreg 120052 = c.nreg 120060 := by
  unfold takeS
  exec_block
  · omega
  simp
open Classical in
/-- **The comparison with the best hit, and the update.** -/
theorem betterS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {s hz σb : ℕ} (c : Config)
    (hw : WordsBounded W c) (he : c.nreg 120061 = eIdx P.n s ztmfr)
    (hn : 0 < P.n) (hhz : c.nreg 120023 = hz) (hhzn : hz < P.n) (hone : c.nreg 120011 = 1)
    (hσ : c.nreg 120024 = σb) (hσ1 : σb ≤ 1) {mb : ℕ} (hcim : c.nreg 120060 < mb)
    (hb : BestOK P.n s mb c) :
    ∃ c' k, Exec P W betterS c c' k ∧ k ≤ 260 ∧ FrameB BE c c' ∧ BestOK P.n s mb c' ∧
      bestOf c' = if (∀ cb, bestOf c = some cb → BetterC zta s hz ztevk
        ztmfr cb) then some (c.nreg 120060) else bestOf c := by
  zqbgw
  suffices H : ∃ c' k, Exec P W betterS c c' k ∧ k ≤ 260 ∧ BestOK P.n s mb c' ∧
      bestOf c' = if (∀ cb, bestOf c = some cb → BetterC zta s hz ztevk
        ztmfr cb) then some _ else bestOf c by
    zqbha
    exact ⟨c', k, ex, hk, exec_frameB ex by_decide, hb', hv⟩
  set ci := c.nreg 120060 with hci
  have hen : c.nreg 120061 < P.n := by zvmxm; exact Nat.mod_lt _ hn
  -- taking the edge
  have take : ∀ d : Config, WordsBounded W d → d.nreg 120060 = ci →
      d.nreg 120061 = eIdx P.n s ci →
      ∃ d' k, Exec P W takeS d d' k ∧ k ≤ 3 ∧ BestOK P.n s mb d' ∧ bestOf d' = some ci := by
    intro d hd h60 h61
    obtain ⟨d', k, ex, hk, v50, v51, v52⟩ := takeS_exec (P := P) d hd by_omega
    refine ⟨d', k, ex, hk, ztomu, ?_⟩
    zubqh
  by_cases hf : c.nreg 120050 < 1
  · have hnone : ztunc := by unfold bestOf; simp_all
    obtain ⟨c', k, ex, hk, hb', hv⟩ := take c hw rfl he
    refine ⟨c', _, .ifLtN_true by_omega ex, by_omega, hb', ?_⟩
    simp_all
  · have hf1 : c.nreg 120050 = 1 := by have := hb.1; omega
    have hsome : ztzpe := by unfold bestOf; simp_all
    have heb := (hb.2 hf1).1
    have hebn : c.nreg 120051 < P.n := by rw [heb]; exact Nat.mod_lt _ hn
    have hl1 : ztlww := ⟨hebn, by_omega⟩
    have hl2 : ztlww := ⟨hen, by_omega⟩
    have hlv : ztrff := hen
    -- the comparison bit
    obtain ⟨c₂, k₂, e₂, hk₂, g₂, u₂, v₂⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 120024 120011
        _
        _) c c₂ k₂ ∧ k₂ ≤ 250 ∧
        (∀ r, Bk r = false → r ≠ 120067 → c₂.nreg r = c.nreg r) ∧ c₂.nreg 120067 ≤ 1 ∧
        (c₂.nreg 120067 = 1 ↔ BetterC zta s hz ztevk ci zthuh) := by
      have ee : ∀ x, eIdx (Qof P).n s x = eIdx P.n s x := by_simp_all
      zujtv
      · zugno
        obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, s₁⟩ := sgnS_exec hG hW 0 by_norm_num
          ztdru ztdrv ztcpi c hw by_decide by_decide
          by_decide rfl rfl rfl hl1 hl2 hlv
        zueao
        refine ⟨c₂, _, .ifLtN_true by_omega ztyv, by_omega,
          fun r hr hr' => (r₂ r hr').trans ztjwt, by_omega, ?_⟩
        zqbgv
      · zugnp
        obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, s₁⟩ := sgnS_exec hG hW 0 by_norm_num
          ztdrv ztdru ztcpi c hw by_decide by_decide
          by_decide rfl rfl rfl hl2 hl1 hlv
        zueao
        refine ⟨c₂, _, .ifLtN_false by_omega ztyv, by_omega,
          fun r hr hr' => (r₂ r hr').trans ztjwt, by_omega, ?_⟩
        zqbgv
    have c60 : c₂.nreg 120060 = ci := g₂ _ by_decide by_decide
    have c61 := (g₂ _ by_decide by_decide).trans he
    have c11 := (g₂ _ by_decide by_decide).trans hone
    have hb₂ : BestOK P.n s mb c₂ := by
      refine ⟨by rw [g₂ _ by_decide by_decide]; omega, fun h => ?_⟩
      rw [g₂ _ by_decide by_decide] at h ⊢
      rw [g₂ _ by_decide by_decide]
      exact hb.2 h
    have hbo₂ : ztmue := by
      zulbi
      rw [g₂ 120050 by_decide by_decide, g₂ 120052 by_decide by_decide]
    have hall : (∀ cb, bestOf c = some cb → BetterC zta s hz ztevk ci cb) ↔
        BetterC zta s hz ztevk ci zthuh := by
      grind
    by_cases hbt : c₂.nreg 120067 < 1
    · refine ⟨c₂, _, .ifLtN_false by_omega (.seq e₂ (.ifLtN_true by_omega
        ztdyc)), by_omega, hb₂, ?_⟩
      grind
    · obtain ⟨c₃, k₃, e₃, hk₃, hb₃, hv₃⟩ := take c₂ e₂.wb_right c60 c61
      refine ⟨c₃, _, .ifLtN_false by_omega (.seq e₂ (.ifLtN_false by_omega
        e₃)), by_omega, hb₃, ?_⟩
      grind
theorem add_exec {c : Config} (hw : WordsBounded W c) (r a b : ℕ) (h : c.nreg a + c.nreg b ≤ W) :
    ∃ c', Exec P W ztder c c' 1 ∧ c'.nreg r = c.nreg a + c.nreg b ∧
      ztbiv ∧ c'.nmem = c.nmem :=
  ⟨_, Exec.addN hw r a b h, by config_simp, by_simp_all, rfl⟩

/-- The origin registers survive a statement that does not write them. -/
theorem originOK_congr {zo : Option Point}
    (h : ∀ r, 120025 ≤ r → r ≤ 120027 → c'.nreg r = c.nreg r) (ho : OriginOK P c zo) :
    OriginOK P c' zo := by
  rcases ho with ⟨h1, h2⟩ | ⟨h1, p, hp, hin, h2⟩
  · zudxj
  · refine Or.inr ⟨by_simp_all, p, hp, ?_, h2⟩
    cases p with
    | vtx i =>
      zuipf
      rw [h _ le_rfl by_norm_num, h 120026 by_norm_num by_norm_num]; exact hin
    | onEdge e h' =>
      zuipf
      rw [h _ le_rfl by_norm_num, h 120026 by_norm_num by_norm_num,
        h 120027 by_norm_num le_rfl]; exact hin

/-- **The edge test** of chain edge `ci` (register `120060`). -/
theorem edgeT_exec (hG : GoodEnv P) (hW : 2 * P.n + 3 ≤ W) (hD : DistinctHeights zta)
    {s hz σb : ℕ} {zo : Option Point} (c : Config) (hw : WordsBounded W c)
    (hc : EConst P s hz σb zo c) (hci : c.nreg 120060 < P.n) {mb : ℕ} (hcim : c.nreg 120060 < mb)
    (hb : BestOK P.n s mb c) :
    ∃ c' k, Exec P W edgeT c c' k ∧ k ≤ 1100 ∧ FrameB BE c c' ∧ BestOK P.n s mb c' ∧
      bestOf c' = upd1 zta s hz ztevk zo ztchc ztmfr := by
  zqbgw
  zuiz
  have hsn := hc.s_lt
  suffices H : ∃ c' k, Exec P W edgeT c c' k ∧ k ≤ 1100 ∧ BestOK P.n s mb c' ∧
      bestOf c' = upd1 _ s hz _ zo _ _ by
    zqbha
    exact ⟨c', k, ex, hk, exec_frameB ex wr_edgeT, hb', hv⟩
  -- e := (s + ci) mod n
  obtain ⟨c₁, e₁, v₁, r₁, -⟩ := add_exec (P := P) hw 120061 120015 120060
    (by rw [hc.rs]; omega)
  rw [hc.rs] at v₁
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, r₂, -⟩ := modSub_exec (P := P) (r := 120061) (nr := 120010)
    by_decide c₁ e₁.wb_right (by rw [v₁, r₁ _ by_decide, hc.n]; omega)
  rw [v₁, r₁ _ by_decide, hc.n] at v₂
  obtain ⟨c₃, e₃, v₃, r₃, -⟩ := add_exec (P := P) e₂.wb_right 120062 120061 120011 (by
    rw [v₂, r₂ _ by_decide, r₁ _ by_decide, hc.one]
    have := Nat.mod_lt ztrwr hn; omega)
  rw [v₂, r₂ _ by_decide, r₁ _ by_decide, hc.one] at v₃
  obtain ⟨c₄, k₄, e₄, hk₄, v₄, r₄, -⟩ := modSub_exec (P := P) (r := 120062) (nr := 120010)
    by_decide c₃ e₃.wb_right (by
      rw [v₃, r₃ _ by_decide, r₂ _ by_decide, r₁ _ by_decide, hc.n]
      have := Nat.mod_lt ztrwr hn; omega)
  rw [v₃, r₃ _ by_decide, r₂ _ by_decide, r₁ _ by_decide, hc.n] at v₄
  set ci := c.nreg 120060 with hci_def
  have R₄ : ∀ r, r ≠ 120061 → r ≠ 120062 → c₄.nreg r = c.nreg r := by_simp_all
  have x61 : c₄.nreg 120061 = eIdx P.n s ci := by rw [r₄ _ by_decide, r₃ _ by_decide]; exact v₂
  have x62 : c₄.nreg 120062 = (c₄.nreg 120061 + 1) % P.n := by_grind
  have hen : eIdx P.n s ci < P.n := Nat.mod_lt _ hn
  have x23 := (R₄ _ by_decide by_decide).trans hc.rhz
  have e0 : Exec P W _ c c₄
      _ := .seq e₁ ztcb
  -- the height range
  obtain ⟨c₅, k₅, e₅, hk₅, -, u₅, v₅⟩ := spansS_exec (P := P) hG by_omega hD c₄ e₄.wb_right
    by_omega x62 (by rw [x23]; exact hc.hz_lt)
  have f₅ := exec_frameB e₅ (B := fun r => Bk r || decide (120063 ≤ r ∧ r ≤ 120065)) by_decide
  have R₅ : ∀ r, Bk r = false → (r < 120063 ∨ 120065 < r) → c₅.nreg r = c₄.nreg r :=
    fun r h1 h2 => f₅.1 r by_grind
  rw [x61, x23] at v₅
  have hQe : eIdx (Qof P).n s ci = eIdx P.n s ci := by zvmxg
  have hbo₅ : ztmuh := by
    zulbi
    rw [R₅ 120050 by_decide by_omega, R₅ 120052 by_decide by_omega,
      R₄ 120050 by_decide by_decide, R₄ 120052 by_decide by_decide]
  have hb₅ : BestOK P.n s mb c₅ := by
    zucku
    rw [R₅ 120050 by_decide by_omega, R₅ 120052 by_decide by_omega,
      R₅ 120051 by_decide by_omega, R₄ 120050 by_decide by_decide,
      R₄ 120052 by_decide by_decide, R₄ 120051 by_decide by_decide]
    zulfi
  have G₅ : ∀ r, Bk r = false → (r < 120061 ∨ 120065 < r) → c₅.nreg r = c.nreg r :=
    fun r h1 h2 => (R₅ r h1 by_omega).trans (R₄ r by_omega by_omega)
  have c11 := (G₅ _ by_decide by_omega).trans hc.one
  by_cases hsp : c₅.nreg 120063 < 1
  · -- not in range: nothing changes
    have hnsp : ¬ Spans zta ztroz hz := by_grind
    refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.ifLtN_true
      by_omega ztuvn))))), by_omega, hb₅, ?_⟩
    zulvd
    grind
  have hsp1 : Spans _ _ hz := v₅.1 by_omega
  -- ahead
  have x61' := (R₅ _ by_decide by_omega).trans x61
  have x23' := (R₅ _ by_decide by_omega).trans x23
  obtain ⟨c₆, k₆, e₆, hk₆, -, u₆, v₆⟩ := aheadS_exec (P := P) hG by_omega (σb := σb) (zo := zo)
    c₅ e₅.wb_right by_omega (by rw [x23']; exact hc.hz_lt) c11
    ((G₅ _ by_decide by_omega).trans hc.two) ((G₅ _ by_decide by_omega).trans hc.rσ)
    hc.σle (originOK_congr (fun r h1 h2 => G₅ r (by
      simp only [Bk, decide_eq_false_iff_not, not_and, not_lt]; omega) by_omega) hc.org)
  rw [x61', x23'] at v₆
  have f₆ := exec_frameB e₆ (B := fun r => Bk r || decide (r = 120066)) by_decide
  have R₆ : ∀ r, Bk r = false → r ≠ 120066 → c₆.nreg r = c₅.nreg r :=
    fun r h1 h2 => f₆.1 r by_grind
  have c11' := (R₆ _ by_decide by_decide).trans c11
  by_cases hah : c₆.nreg 120066 < 1
  · have hna : ¬ Ahead ztevk zo (xe zta ztroz hz) := by_grind
    refine ⟨c₆, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.ifLtN_false
      by_omega (.seq e₆ (.ifLtN_true by_omega
        (.skip e₆.wb_right)))))))),
      by omega, ?_, ?_⟩
    · zucku
      rw [R₆ 120050 by_decide by_decide, R₆ 120052 by_decide by_decide,
        R₆ 120051 by_decide by_decide]
      exact hb₅
    · zulvd
      rw [hQe, ite_eq_right by_grind]
      zqbgx
  have hah1 : Ahead _ zo _ := v₆.1 by_omega
  -- the comparison and the update
  have G₆ : ∀ r, Bk r = false → (r < 120061 ∨ 120066 < r) → c₆.nreg r = c.nreg r :=
    fun r h1 h2 => (R₆ r h1 by_omega).trans (G₅ r h1 by_omega)
  obtain ⟨c₇, k₇, e₇, hk₇, -, hb₇, v₇⟩ := betterS_exec (P := P) hG by_omega (s := s) (hz := hz)
    (σb := σb) c₆ e₆.wb_right (by
      rw [R₆ _ by_decide by_decide, x61', G₆ _ by_decide by_omega]) hn
    ((R₆ _ by_decide by_decide).trans x23') hc.hz_lt c11'
    ((G₆ _ by_decide by_omega).trans hc.rσ) hc.σle (mb := mb)
      (by rw [G₆ _ by_decide by_omega]; omega) (by
      zucku
      rw [R₆ 120050 by_decide by_decide, R₆ 120052 by_decide by_decide,
        R₆ 120051 by_decide by_decide]
      exact hb₅)
  have c60 : c₆.nreg 120060 = ci := G₆ _ by_decide by_omega
  have hbo₆ : bestOf c₆ = bestOf c := by
    zqbgx
  rw [c60, hbo₆] at v₇
  refine ⟨c₇, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.ifLtN_false
    by_omega (.seq e₆ (.ifLtN_false by_omega e₇))))))),
    by omega, hb₇, ?_⟩
  zumpd
  zulvd
  zuoft
  by_cases hall : ∀ cb, bestOf c = some cb → BetterC zta s hz ztevk ci cb
  · grind
  grind
end Exec
end
end OracleR
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqzn" : tactic => `(tactic| (simp only [upd]; grind))
local macro "zqzo" : tactic => `(tactic| have m₁' : ztdbm := by_grind)
local macro "zqzp" : tactic => `(tactic| (have w₁ := e₁.wb_right
                                          have fr₁ : zthoe := exec_frameB e₁ by_decide))
set_option hygiene true

/-!
# WP-G, part 15: the upward dyadic sweep on the RAM

`dyUp emit` hands the blocks of a dyadic cover of `[q₀, q₀ + L)` to `emit`, as pieces of the walk
from the vertex `c₀` (`dyUp_exec`): at most `2 (log₂ L + 1)` pieces, chained from `c₀` to
`c₀ + L`, each valid by the hypothesis `hblk` on blocks.
-/
namespace Chazelle.Core
namespace ShootCut
open Machine Machine.Stmt Programs SignK NFLoc
@[expose] public section
variable {P : Polygon} {W : ℕ} (emit : Stmt)
/-- **A block piece** in the registers. -/
theorem pcBlock_exec (c : Config) (hw : WordsBounded W c) (x dir : ℕ)
    (hx : x < 150050 ∨ 150059 ≤ x) (hdir : dir ≤ W)
    (h90 : c.nreg 150090 = 0)
    (hwW : c.nreg 150085 + c.nreg 150084 ≤ W)
    (hent : 0 < c.nreg 150082 → c.nreg 150034 + c.nreg 150082 ≤ W ∧
      c.nmem ztjru + 3 * c.nreg 150077 ≤ W) :
    ∃ c' k, Exec P W (pcBlock x dir) c c' k ∧ k ≤ 15 ∧
      c'.nreg 150050 = c.nreg 150085 ∧ c'.nreg 150051 = 0 ∧
      c'.nreg 150052 = c.nreg 150085 + c.nreg 150084 ∧ c'.nreg 150053 = 0 ∧
      c'.nreg 150054 = (if 0 < c.nreg 150082 then 1 else 0) ∧
      (0 < c.nreg 150082 → c'.nreg 150055 =
        c.nmem ztjru + 3 * c.nreg 150077) ∧
      c'.nreg 150056 = c.nreg x ∧ c'.nreg 150057 = dir ∧ c'.nreg 150058 = c.nreg 150084 ∧
      (∀ r, zteux → r ≠ 150075 → r ≠ 150076 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem := by
  obtain ⟨c₁, k₁, e₁, hk₁, v50, v51, v52, v53, v56, v57, v58, r₁, m₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 150050 150085, .constN 150051 0, .addN 150052 150085 150084,
        .constN 150053 0, .copyN 150056 x, .constN 150057 dir, .copyN 150058 150084]) c c₁ k₁ ∧
      k₁ = 7 ∧ c₁.nreg 150050 = c.nreg 150085 ∧ c₁.nreg 150051 = 0 ∧
      c₁.nreg 150052 = c.nreg 150085 + c.nreg 150084 ∧ c₁.nreg 150053 = 0 ∧
      c₁.nreg 150056 = c.nreg x ∧ c₁.nreg 150057 = dir ∧ c₁.nreg 150058 = c.nreg 150084 ∧
      (∀ r, zteux → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem := by
    exec_block
    all_goals first | (config_simp; omega) | exact hdir | skip
    · refine ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp, ?_, by config_simp,
        by config_simp, fun r hr => ?_, rfl⟩
      · config_simp
        zuky
        · simp [upd, show x ≠ 150050 by omega, show x ≠ 150051 by omega, show x ≠ 150052 by omega,
            show x ≠ 150053 by omega]
        · simp [upd, show x ≠ 150050 by omega, show x ≠ 150051 by omega, show x ≠ 150052 by omega,
            show x ≠ 150053 by omega]
      · zqzn
  zud
  have a90 : c₁.nreg 150090 = 0 := by_simp_all
  have a82 : c₁.nreg 150082 = c.nreg 150082 := by_simp_all
  have a34 : c₁.nreg 150034 = c.nreg 150034 := by_simp_all
  have a77 : c₁.nreg 150077 = c.nreg 150077 := by_simp_all
  by_cases hg : 0 < c.nreg 150082
  · obtain ⟨hA1, hA2⟩ := hent hg
    obtain ⟨c₂, k₂, e₂, hk₂, v54, v55, r₂, m₂⟩ : ∃ c₂ k₂, Exec P W (block [.constN 150054 1,
        .addN 150075 150034 150082, .loadN 150076 150075, .addN 150055 150076 150077,
        .addN 150055 150055 150077, .addN 150055 150055 150077]) c₁ c₂ k₂ ∧ k₂ = 6 ∧
        c₂.nreg 150054 = 1 ∧
        c₂.nreg 150055 = c.nmem ztjru + 3 * c.nreg 150077 ∧
        (∀ r, r ≠ 150054 → r ≠ 150055 → r ≠ 150075 → r ≠ 150076 → c₂.nreg r = c₁.nreg r) ∧
        c₂.nmem = c₁.nmem := by
      exec_block
      all_goals first | (config_simp; omega) | (config_simp; rw [a34, a82, m₁, a77]; omega) | skip
      · refine ⟨rfl, by config_simp, ?_, fun r h1 h2 h3 h4 => ?_, rfl⟩
        · config_simp; grind
        simp_all
    refine ⟨c₂, k₁ + ztcaj, .seq e₁ ztbxn, by_omega,
      ?_, ?_, ?_, ?_, ?_, by_omega, ?_, ?_, ?_, fun r hr h1 h2 => ?_, by_simp_all⟩
    · simp_all
    · simp_all
    · simp_all
    · simp_all
    · simp_all
    · simp_all
    · simp_all
    · simp_all
    grind
  · refine ⟨_, k₁ + ztgxh, .seq e₁ (.ifLtN_false by_omega
      (Exec.constN w₁ 150054 0 by_omega)), by_omega, ?_, ?_, ?_, ?_, ?_, by_omega,
      ?_, ?_, ?_, fun r hr h1 h2 => ?_, by_omega⟩
    all_goals config_simp
    · omega
    · omega
    · omega
    · omega
    · simp_all
    · omega
    · omega
    · omega
    · zurj

/-! ## The static context of a sweep -/

/-- The tables and bounds a sweep reads: the halving table at `Hb`, the powers of two at `Pb`
(up to `2^(tg + 1)`), all below `A₀ ≤ W`; the registers `34 … 36`, `90`, `91`. -/
structure SwEnv (n W A₀ Tb Hb Pb tg : ℕ) (m₀ : ℕ → ℕ) : Prop where
  half : ∀ x, x ≤ n → m₀ (Hb + x) = x / 2 ∧ Hb + x < A₀
  pow : ∀ j, j ≤ tg + 1 → m₀ ztnnv = 2 ^ j ∧ Pb + j < A₀
  aW : A₀ ≤ W

/-- The registers of the sweep that stay fixed. -/
def SwRegs (Tb Hb Pb : ℕ) (m₀ : ℕ → ℕ) (A₀ : ℕ) (c₀c : Config) (d : Config) : Prop :=
  ztecz ∧ (∀ r, 150000 ≤ r → r < 150044 → d.nreg r = c₀c.nreg r) ∧
    d.nreg 150090 = 0 ∧ d.nreg 150091 = 1 ∧ d.nreg 150034 = Tb ∧ d.nreg 150035 = Hb ∧
    d.nreg 150036 = Pb

/-- The piece of the block `(g, b)` of an upward sweep from `q₀` at the walk vertex `c₀`. -/
def upPc (c₀ q₀ g b e : ℕ) : Pc :=
  ⟨⟨c₀ + ztnrl, 0⟩, ⟨c₀ + ztnrl + 2 ^ g, 0⟩, if 0 < g then 1 else 0, e,
    b * 2 ^ g, 1, 2 ^ g⟩

/-- The validity of the blocks, as the sweep needs it. -/
def UpBlocks (Pv : Pc → Prop) (m₀ : ℕ → ℕ) (W A₀ Tb c₀ q₀ L : ℕ) : Prop :=
  ∀ g b, q₀ ≤ b * 2 ^ g → ztds * 2 ^ g ≤ q₀ + L →
    ztezp ∧
      ∀ e, ztgqn → Pv (upPc c₀ q₀ g b e)

/-- The invariant of the ascending sweep. -/
def UpA (W : ℕ) (Pv : Pc → Prop) (I : List Pc → Config → Prop) (ps₀ : List Pc)
    (m₀ : ℕ → ℕ) (A₀ Tb Hb Pb tg q₀ L c₀ : ℕ) (cc d : Config) : Prop :=
  WordsBounded W d ∧ SwRegs Tb Hb Pb m₀ A₀ cc d ∧
    ∃ x g ps', d.nreg 150080 = x ∧ d.nreg 150081 = q₀ + L ∧ d.nreg 150082 = g ∧
      x = d.nreg 150083 * 2 ^ g ∧ d.nreg 150084 = 2 ^ g ∧ d.nreg 150085 = c₀ + ztcwz ∧
      d.nreg 150087 = x + 2 ^ g ∧ d.nreg 150088 = q₀ + L + 1 ∧ q₀ ≤ x ∧ x ≤ q₀ + L ∧
      I ztcdl d ∧ Chained ztcxt ps' ztxzk ∧ ztbqq ∧
      ps'.length ≤ g ∧ ztyfa ∧ g ≤ tg + 1
theorem pow_le_of_le {g L tg : ℕ} (h : 2 ^ g ≤ L) (hL : L ≤ 2 ^ tg) : g ≤ tg :=
  (Nat.pow_le_pow_iff_right by_omega).1 (h.trans hL)

/-- The end of a step of the ascending sweep: double the block size. -/
theorem upATail_exec {W A₀ Pb g x : ℕ} {m₀ : ℕ → ℕ} (d : Config)
    (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a) (h36 : d.nreg 150036 = Pb)
    (h82 : d.nreg 150082 = g) (h80 : d.nreg 150080 = x) (h91 : d.nreg 150091 = 1)
    (hpow : m₀ ztzuq = 2 ^ ztbs ∧ Pb + ztbs < A₀) (hA : A₀ ≤ W)
    (hxW : x + 2 ^ ztbs ≤ W) :
    ∃ d' k, Exec P W (block [.addN 150082 150082 150091, .addN 150075 150036 150082,
        .loadN 150084 150075, .copyN 150083 150086, .addN 150087 150080 150084]) d d' k ∧
      k = 5 ∧ d'.nreg 150082 = g + 1 ∧ d'.nreg 150084 = 2 ^ ztbs ∧
      d'.nreg 150083 = d.nreg 150086 ∧ d'.nreg 150087 = x + 2 ^ ztbs ∧
      (∀ r, r ≠ 150075 → r ≠ 150082 → r ≠ 150083 → r ≠ 150084 → r ≠ 150087 →
        d'.nreg r = d.nreg r) ∧ d'.nmem = d.nmem := by
  zulla
  exec_block
  all_goals first | (config_simp; rw [h82, h91]; omega) | (config_simp; rw [h82, h91, h36]; omega) |
    (config_simp; rw [h82, h91, h80, h36, hm _ hpow.2, hpow.1]; omega) | skip
  simp_all

/-- Building the invariant of the ascending sweep. -/
theorem mkUpA {Pv : Pc → Prop} {I : List Pc → Config → Prop} {ps₀ : List Pc}
    {m₀ : ℕ → ℕ} {A₀ Tb Hb Pb tg q₀ L c₀ : ℕ} {cc d : Config} (x g : ℕ) (ps' : List Pc)
    (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a)
    (hk : ∀ r, 150000 ≤ r → r < 150044 → d.nreg r = cc.nreg r) (h90 : d.nreg 150090 = 0)
    (h91 : d.nreg 150091 = 1) (h34 : d.nreg 150034 = Tb) (h35 : d.nreg 150035 = Hb)
    (h36 : d.nreg 150036 = Pb) (h80 : d.nreg 150080 = x) (h81 : d.nreg 150081 = q₀ + L)
    (h82 : d.nreg 150082 = g) (hx : x = d.nreg 150083 * 2 ^ g) (h84 : d.nreg 150084 = 2 ^ g)
    (h85 : d.nreg 150085 = c₀ + ztcwz) (h87 : d.nreg 150087 = x + 2 ^ g)
    (h88 : d.nreg 150088 = q₀ + L + 1) (hqx : q₀ ≤ x) (hxy : x ≤ q₀ + L)
    (hI : I ztcdl d) (hch : Chained ztcxt ps' ztxzk)
    (hv : ∀ pc ∈ ps', Pv pc) (hlen : ps'.length ≤ g) (hg : g = 0 ∨ 2 ^ ztfe ≤ L)
    (hgt : g ≤ tg + 1) : UpA W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d :=
  ⟨hw, ⟨hm, hk, h90, h91, h34, h35, h36⟩, x, g, ps', h80, h81, h82, hx, h84, h85, h87, h88, hqx,
    hxy, hI, hch, hv, hlen, hg, hgt⟩

/-- The tail block of a step of the ascending sweep. -/
def upATail : Stmt := block [.addN 150082 150082 150091, .addN 150075 150036 150082,
  .loadN 150084 150075, .copyN 150083 150086, .addN 150087 150080 150084]

/-- The odd branch of a step of the ascending sweep. -/
def upAOdd (emit : Stmt) : Stmt :=
  .seq ztigi
    (.seq ztoej
      (.seq emit (block [.addN 150080 150080 150084, .addN 150085 150085 150084,
        .addN 150086 150086 150091])))
theorem upABody_eq : upABody emit =
    .seq ztbus
      (.seq (.ifLtN 150075 150083 ztqxw .skip) upATail) := rfl

/-- **After the optional block**: the tail re-establishes the invariant with `g + 1`. -/
theorem upA_after {W A₀ K : ℕ} {emit : Stmt} {Pv : Pc → Prop}
    {I : List Pc → Config → Prop} (hE : EmitOK P W emit A₀ Pv I K) {m₀ : ℕ → ℕ}
    {Tb Hb Pb tg q₀ L c₀ : ℕ} {ps₀ : List Pc} {cc : Config}
    (env : SwEnv P.n W A₀ Tb Hb Pb tg m₀) (hW : c₀ + L + 2 ≤ W) (hW' : 3 * L + 2 * P.n + 4 ≤ W)
    (hqL : q₀ + L ≤ P.n) (d₅ : Config) (w₅ : WordsBounded W d₅) (x' h' g : ℕ) (ps'' : List Pc)
    (hgt : g ≤ tg) (hgL : 2 ^ g ≤ L)
    (m₅ : ∀ a, a < A₀ → d₅.nmem a = m₀ a) (s₅ : ∀ r, 150000 ≤ r → r < 150044 → d₅.nreg r = cc.nreg r)
    (a90 : d₅.nreg 150090 = 0) (a91 : d₅.nreg 150091 = 1) (a34 : d₅.nreg 150034 = Tb)
    (a35 : d₅.nreg 150035 = Hb) (a36 : d₅.nreg 150036 = Pb) (a82 : d₅.nreg 150082 = g)
    (a80 : d₅.nreg 150080 = x') (a81 : d₅.nreg 150081 = q₀ + L)
    (a85 : d₅.nreg 150085 = c₀ + ztkha) (a88 : d₅.nreg 150088 = q₀ + L + 1)
    (hx' : x' = h' * 2 ^ ztbs) (a86 : d₅.nreg 150086 = h') (hq' : q₀ ≤ x') (hx'L : x' ≤ q₀ + L)
    (hI₅ : I ztlru d₅) (hch₅ : Chained ztcxt ps'' ztzii)
    (hv₅ : ∀ pc ∈ ps'', Pv pc) (hl₅ : ps''.length ≤ g + 1) :
    ∃ d₆ k₆, Exec P W upATail d₅ d₆ k₆ ∧ k₆ = 5 ∧
      UpA W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d₆ ∧ d₆.nreg 150082 = g + 1 := by
  zudzl

  obtain ⟨d₆, k₆, e₆, hk₆, b82, b84, b83, b87, r₆, m₆⟩ := upATail_exec (P := P) (x := x') d₅ w₅
    m₅ a36 a82 a80 a91 ztuhz env.aW by_omega
  zuffo

  refine ⟨d₆, k₆, e₆, hk₆, mkUpA x' _ ps'' e₆.wb_right
    ztxl
    by_grind
    by_grind
    by_grind
    by_grind
    by_grind
    by_grind
    by_grind
    by_grind
    b82 by_grind b84
    by_grind b87
    by_grind hq' hx'L
    (hE.stable _ _ _ hI₅ fr₆) hch₅ hv₅ hl₅ by_grind by_omega, b82⟩

/-- **The odd branch**: the block `(g, qq)` is handed to `emit`. -/
theorem upA_odd {W A₀ K : ℕ} {emit : Stmt} {Pv : Pc → Prop}
    {I : List Pc → Config → Prop} (hE : EmitOK P W emit A₀ Pv I K) {m₀ : ℕ → ℕ}
    {Tb q₀ L c₀ : ℕ} {ps : List Pc} (hblk : UpBlocks Pv m₀ W A₀ Tb c₀ q₀ L)
    (hW : c₀ + L + 2 ≤ W) (hW' : 3 * L + 4 ≤ W) (hA : A₀ ≤ W) (hqW : q₀ + L ≤ W) {x g qq : ℕ}
    (d₁ : Config) (w₁ : WordsBounded W d₁) (hm : ∀ a, a < A₀ → d₁.nmem a = m₀ a)
    (h90 : d₁.nreg 150090 = 0) (h91 : d₁.nreg 150091 = 1) (h34 : d₁.nreg 150034 = Tb)
    (h80 : d₁.nreg 150080 = x) (h82 : d₁.nreg 150082 = g) (h83 : d₁.nreg 150083 = qq)
    (h84 : d₁.nreg 150084 = 2 ^ g) (h85 : d₁.nreg 150085 = c₀ + ztcwz)
    (hx : x = qq * 2 ^ g) (hqx : q₀ ≤ x) (hxy : x + 2 ^ g ≤ q₀ + L) (hI : I ps d₁)
    (h86 : d₁.nreg 150086 + 1 ≤ W) :
    ∃ d₅ k₅ e, Exec P W ztqxw d₁ d₅ k₅ ∧ k₅ ≤ K + 20 ∧ Pv (upPc c₀ q₀ g qq e) ∧
      I (ps ++ [upPc c₀ q₀ g qq e]) d₅ ∧ d₅.nreg 150080 = x + 2 ^ g ∧
      d₅.nreg 150085 = c₀ + ztcwz + 2 ^ g ∧ d₅.nreg 150086 = d₁.nreg 150086 + 1 ∧
      (∀ r, (ztbdq ∨ r = 150081 ∨ r = 150082 ∨ r = 150088 ∨
        r = 150090 ∨ r = 150091 ∨ r = 150083) → d₅.nreg r = d₁.nreg r) ∧
      ztiui := by
  zubdt
  obtain ⟨hblk1, hblk2⟩ := hblk g qq by_omega (by
    grind)
  have ex₂ := Exec.copyN (P := P) w₁ 150077 150083
  set d₂ := ({ d₁ with nreg := upd d₁.nreg 150077 _ } : Config) with hd₂
  zujag
  have g2 : ∀ r, r ≠ 150077 → d₂.nreg r = d₁.nreg r := by_simp_all
  have n77 : d₂.nreg 150077 = qq := by_simp_all
  have nm : d₂.nmem = d₁.nmem := rfl
  obtain ⟨d₃, k₃, e₃, hk₃, v50, v51, v52, v53, v54, v55, v56, v57, v58, r₃, m₃⟩ :=
    pcBlock_exec (P := P) d₂ w₂ 150080 1 ztbh by_omega
      by_simp_all
      by_grind (fun hg => by
        grind)
  rw [g2 _ by_omega] at v50 v52 v54 v56 v58 v55
  rw [g2 _ by_omega] at v52
  set pc := upPc c₀ q₀ g qq ztvpj with hpc
  have hpcR : PcRegs d₃ pc := by
    refine ztfaf
    · zuoay; zunec
    · zuntp; zunec
    · zugxi
    · rw [v56, h80, hpc]; zunec
    · zuina
  zuiyy
  have fr₃ : ztuku := (exec_frameB ex₂ by_decide).trans ztduk
  zubxl
  zucc
  have back : ∀ r, Keep r → r ≠ 150077 → zteux → r ≠ 150075 → r ≠ 150076 →
      d₄.nreg r = d₁.nreg r := by_grind
  have q80 : d₄.nreg 150080 = x := by rw [back _ ztbh by_omega by_omega
    by_omega by_omega, h80]
  have q84 : ztrgq := by rw [back _ ztbh by_omega by_omega
    by_omega by_omega, h84]
  have q85 : d₄.nreg 150085 = c₀ + ztcwz := by rw [back _ ztbh by_omega
    by_omega by_omega by_omega, h85]
  have q91 : ztuua := by rw [back _ ztbh by_omega by_omega
    by_omega by_omega, h91]
  have q86 : d₄.nreg 150086 = d₁.nreg 150086 := by
    rw [back _ ztbh by_omega by_omega by_omega by_omega]
  obtain ⟨d₅, k₅, e₅, hk₅, a80, a85, a86, r₅, m₅⟩ : ∃ d₅ k₅, Exec P W
      (block [.addN 150080 150080 150084, .addN 150085 150085 150084,
        .addN 150086 150086 150091]) d₄ d₅ k₅ ∧ k₅ = 3 ∧ d₅.nreg 150080 = x + 2 ^ g ∧
      d₅.nreg 150085 = c₀ + ztcwz + 2 ^ g ∧ d₅.nreg 150086 = d₄.nreg 150086 + 1 ∧
      (∀ r, r ≠ 150080 → r ≠ 150085 → r ≠ 150086 → d₅.nreg r = d₄.nreg r) ∧
      d₅.nmem = d₄.nmem := by
    exec_block
    all_goals first | (config_simp; rw [q80, q84]; omega) | (config_simp; rw [q85, q84]; omega) |
      (config_simp; rw [q86, q91]; omega) | skip
    refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl⟩
    · config_simp; omega
    · config_simp; omega
    · config_simp; rw [q91]
    · zqzn
  refine ⟨d₅, 1 + ztlg, d₃.nreg 150055, .seq ex₂ ztbpd, by_omega,
    hpv, hE.stable _ _ _ hI₄ zttjx, a80, a85, by_omega, ?_, ?_⟩
  · zuz
    rw [r₅ r by_omega by_omega by_omega, back r ztii by_omega by_omega
      by_omega by_omega]
  grind

/-- **One step of the ascending sweep.** -/
theorem upABody_exec {W A₀ K : ℕ} {emit : Stmt} {Pv : Pc → Prop}
    {I : List Pc → Config → Prop} (hE : EmitOK P W emit A₀ Pv I K) {m₀ : ℕ → ℕ}
    {Tb Hb Pb tg q₀ L c₀ : ℕ} {ps₀ : List Pc} {cc d : Config}
    (env : SwEnv P.n W A₀ Tb Hb Pb tg m₀) (hblk : UpBlocks Pv m₀ W A₀ Tb c₀ q₀ L)
    (hqL : q₀ + L ≤ P.n) (hLtg : L ≤ 2 ^ tg) (hW : c₀ + L + 2 ≤ W) (hW' : 3 * L + 2 * P.n + 4 ≤ W)
    (hI : UpA W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d)
    (ht : d.nreg 150087 < d.nreg 150088) :
    ∃ d' k, Exec P W (upABody emit) d d' k ∧ UpA W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d' ∧
      k ≤ K + 40 ∧ Nat.log 2 L + 1 - d'.nreg 150082 < Nat.log 2 L + 1 - d.nreg 150082 := by
  obtain ⟨hw, ⟨hm, hk0, h90, h91, h34, h35, h36⟩, x, g, ps', h80, h81, h82, hx, h84, h85, h87,
    h88, hqx, hxy, hI', hch, hv, hlen, hg1, hgtg⟩ := hI
  zuiim
  zubdt
  zudde

  have hqqx : d.nreg 150083 ≤ x := by zvnly; exact Nat.le_mul_of_pos_right _ hp
  zuegn

  -- the half of `qq`
  obtain ⟨d₁, k₁, e₁, hk₁, o75, o86, r₁, m₁⟩ : ∃ d₁ k₁, Exec P W (block [.addN 150075 150035 150083,
      .loadN 150086 150075, .addN 150075 150086 150086]) d d₁ k₁ ∧ k₁ = 3 ∧
      d₁.nreg 150075 = d.nreg 150083 / 2 + d.nreg 150083 / 2 ∧
      d₁.nreg 150086 = d.nreg 150083 / 2 ∧
      ztgsj ∧ d₁.nmem = d.nmem := by
    exec_block
    all_goals first | (config_simp; rw [h35, hm _ by_omega, hh1]; omega) |
      (config_simp; rw [h35]; omega) | skip
    refine zticq
    · config_simp; grind
    · config_simp; grind
    · zqzn
  zqzp
  zugnr
  zqzo
  rw [upABody_eq]
  zudwz
  · obtain ⟨d₅, k₅, e, e₅, hk₅, hpv, hI₅, a80, a85, a86, r₅, m₅⟩ := upA_odd hE
      hblk by_omega by_omega hA by_omega d₁ w₁ m₁'
      by_grind by_grind
      by_grind by_grind
      by_grind by_grind
      by_grind by_grind
      hx hqx by_omega ztcij by_omega
    have kk : ∀ r, (ztbdq ∨ r = 150081 ∨ r = 150082 ∨ r = 150088 ∨
        r = 150090 ∨ r = 150091) → d₅.nreg r = d.nreg r := fun r hr => by
      zugfh
    zuef
    obtain ⟨d₆, k₆, e₆, hk₆, hU, b82⟩ := upA_after hE env hW hW' hqL d₅ w₅ _
      (d.nreg 150083 / 2 + 1) g _ hgt hgL
      ztxl
      ztgjp
      by_grind by_grind
      by_grind by_grind
      by_grind by_grind a80
      by_grind ztheo
      by_grind
      (by zuonp; have : ztyuq := by_omega
          grind)
      by_omega by_omega by_omega ztljc
      (by
        have h2 := hch.append (upPc c₀ q₀ g ztmii e) (by zunec)
        have he : (upPc c₀ q₀ g ztmii e).e = ⟨c₀ + (x + 2 ^ g - q₀), 0⟩ := by
          simp only [upPc, ← hx, WPos.mk.injEq, and_true]; omega
        grind)
      (fun p hp => by
        zutk
        · grind
        grind)
      ztbaw
    exact ⟨d₆, k₁ + ztzzq, .seq e₁ (.seq (.ifLtN_true (by
        grind) e₅) e₆), hU, by_omega,
      by omega⟩
  · obtain ⟨d₆, k₆, e₆, hk₆, hU, b82⟩ := upA_after hE env hW hW' hqL d₁ w₁ x
      _ g ps' hgt hgL m₁'
      ztfyg
      by_grind by_grind
      by_grind by_grind
      by_grind by_grind
      by_grind by_grind
      by_grind by_grind
      (by zuonp; have : ztzjh := by_omega
          grind)
      o86 hqx hxy ztcij hch hv by_omega
    exact ⟨d₆, k₁ + ztzzd, .seq e₁ (.seq (.ifLtN_false (by
        grind) (.skip w₁)) e₆), hU, by_omega,
      by omega⟩

/-! ## The descending sweep of the upward cover -/

/-- The invariant of the descending sweep. -/
def UpB (W : ℕ) (Pv : Pc → Prop) (I : List Pc → Config → Prop) (ps₀ : List Pc)
    (m₀ : ℕ → ℕ) (A₀ Tb Hb Pb tg q₀ L c₀ : ℕ) (cc d : Config) : Prop :=
  WordsBounded W d ∧ SwRegs Tb Hb Pb m₀ A₀ cc d ∧
    ∃ x g ps', d.nreg 150080 = x ∧ d.nreg 150081 = q₀ + L ∧ d.nreg 150082 = g ∧
      x = d.nreg 150083 * 2 ^ g ∧ d.nreg 150085 = c₀ + ztcwz ∧
      d.nreg 150088 = q₀ + L + 1 ∧ q₀ ≤ x ∧ x ≤ q₀ + L ∧ q₀ + L < x + 2 ^ g ∧
      I ztcdl d ∧ Chained ztcxt ps' ztxzk ∧ ztbqq ∧
      ps'.length + g ≤ 2 * ztbdz ∧ g ≤ tg + 1 ∧ 2 ^ g ≤ 2 * L + 1
theorem upBBody_eq : upBBody emit =
    .seq (block [.subN 150082 150082 150091, .addN 150075 150036 150082, .loadN 150084 150075,
      .addN 150083 150083 150083, .copyN 150086 150083, .addN 150087 150080 150084])
    ztfmi := rfl

/-- **One step of the descending sweep.** -/
theorem upBBody_exec {W A₀ K : ℕ} {emit : Stmt} {Pv : Pc → Prop}
    {I : List Pc → Config → Prop} (hE : EmitOK P W emit A₀ Pv I K) {m₀ : ℕ → ℕ}
    {Tb Hb Pb tg q₀ L c₀ : ℕ} {ps₀ : List Pc} {cc d : Config}
    (env : SwEnv P.n W A₀ Tb Hb Pb tg m₀) (hblk : UpBlocks Pv m₀ W A₀ Tb c₀ q₀ L)
    (hqL : q₀ + L ≤ P.n) (hW : c₀ + L + 2 ≤ W) (hW' : 3 * L + 2 * P.n + 4 ≤ W)
    (hI : UpB W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d)
    (ht : d.nreg 150090 < d.nreg 150082) :
    ∃ d' k, Exec P W (upBBody emit) d d' k ∧ UpB W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d' ∧
      k ≤ K + 40 ∧ d'.nreg 150082 < d.nreg 150082 := by
  obtain ⟨hw, ⟨hm, hk0, h90, h91, h34, h35, h36⟩, x, g, ps', h80, h81, h82, hx, h85,
    h88, hqx, hxy, hyx, hI', hch, hv, hlen, hgt, hgb⟩ := hI
  zusm

  have hx2 : x = zthjo * 2 ^ g' := by_grind
  have hqqx : qq + qq ≤ x := by rw [hx2]; exact Nat.le_mul_of_pos_right _ hp
  have hxn : x ≤ P.n := by_omega
  zukce
  obtain ⟨d₁, k₁, e₁, hk₁, o82, o84, o83, o86, o87, r₁, m₁⟩ : ∃ d₁ k₁, Exec P W
      (block [.subN 150082 150082 150091, .addN 150075 150036 150082, .loadN 150084 150075,
        .addN 150083 150083 150083, .copyN 150086 150083, .addN 150087 150080 150084])
      d d₁ k₁ ∧ k₁ = 6 ∧ d₁.nreg 150082 = g' ∧ d₁.nreg 150084 = 2 ^ g' ∧
      d₁.nreg 150083 = qq + qq ∧ d₁.nreg 150086 = qq + qq ∧ d₁.nreg 150087 = x + 2 ^ g' ∧
      (∀ r, r ≠ 150075 → r ≠ 150082 → r ≠ 150083 → r ≠ 150084 → r ≠ 150086 → r ≠ 150087 →
        d₁.nreg r = d.nreg r) ∧ d₁.nmem = d.nmem := by
    exec_block
    all_goals first | (config_simp; rw [h82, h91, Nat.add_sub_cancel, h36]; omega) |
      (config_simp; omega) |
      (config_simp; rw [h82, h91, Nat.add_sub_cancel, h36, h80, hm _ by_omega, hp1]; omega) | skip
    refine zteha
    · config_simp; omega
    · config_simp; grind
    · rfl
    · rfl
    · config_simp; grind
    · zqzn
  zqzp
  have k : ∀ r, (ztbdq ∨ r = 150080 ∨ r = 150081 ∨ r = 150085 ∨ r = 150088 ∨
      r = 150090 ∨ r = 150091) → d₁.nreg r = d.nreg r := by_grind
  zqzo
  rw [upBBody_eq]
  -- the final copy
  have fin : ∀ (d₅ : Config) (k₅ x' : ℕ) (ps'' : List Pc),
      Exec P W (.ifLtN 150087 150088 ztqxw .skip) d₁ d₅ k₅ → k₅ ≤ K + 22 →
      (∀ a, a < A₀ → d₅.nmem a = m₀ a) →
      (∀ r, (ztbdq ∨ r = 150081 ∨ r = 150082 ∨ r = 150088 ∨ r = 150090 ∨
        r = 150091) → d₅.nreg r = d₁.nreg r) →
      d₅.nreg 150080 = x' → d₅.nreg 150085 = c₀ + ztkha → x' = d₅.nreg 150086 * 2 ^ g' →
      q₀ ≤ x' → x' ≤ q₀ + L → q₀ + L < x' + 2 ^ g' → I ztlru d₅ →
      Chained ztcxt ps'' ztzii → (∀ pc ∈ ps'', Pv pc) →
      ps''.length ≤ ps'.length + 1 →
      ∃ d' k, Exec P W (.seq (block [.subN 150082 150082 150091, .addN 150075 150036 150082,
        .loadN 150084 150075, .addN 150083 150083 150083, .copyN 150086 150083,
        .addN 150087 150080 150084])
        ztfmi)
        d d' k ∧ UpB W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ cc d' ∧ k ≤ K + 40 ∧
        d'.nreg 150082 < g' + 1 := by
    intro d₅ k₅ x' ps'' e₅ hk₅ m₅ k₅' a80 a85 hx' hq' hx'L hy' hI₅ hch₅ hv₅ hl₅
    zuef
    have e₆ := Exec.copyN (P := P) w₅ 150083 150086
    set d₆ := ({ d₅ with nreg := upd d₅.nreg 150083 _ } : Config) with hd₆
    zudcu
    have kk : ∀ r, (ztbdq ∨ r = 150081 ∨ r = 150088 ∨
        r = 150090 ∨ r = 150091) → d₆.nreg r = d.nreg r := fun r hr => by
      rw [g6 r by_omega, k₅' r by_omega, k r by_omega]
    refine ⟨d₆, k₁ + ztett, .seq e₁ ztcsd, ⟨e₆.wb_right,
      ⟨by_omega, fun r h1 h2 => (kk r by_omega).trans by_grind,
        by zumxu; omega, by zumxu; omega,
        by zumxu; omega, by zumxu; omega,
        by zumxu; omega⟩,
      x', g', ps'', by zunfs; omega, by zumxu; omega,
      by rw [g6 _ by_omega, k₅' _ by_omega]; omega,
      by simp [hd₆]; omega, by zunfs; omega,
      by zumxu; omega, hq', hx'L, hy',
      hE.stable _ _ _ hI₅ ztnyb, hch₅, hv₅, by_omega, by_omega, by_omega⟩,
      by omega, by rw [g6 _ by_omega, k₅' _ by_omega, o82]; omega⟩
  zuhth
  · rw [o87, k _ by_omega, h88] at hodd
    obtain ⟨d₅, k₅, e, e₅, hk₅, hpv, hI₅, a80, a85, a86, r₅, m₅⟩ := upA_odd hE hblk by_omega by_omega hA by_omega d₁ w₁ m₁'
      by_grind by_grind
      by_grind by_grind o82 o83 o84
      by_grind hx2 hqx by_omega ztcij
      by_omega
    obtain ⟨d', k', ex, hU, hk', hg'⟩ := fin d₅ _ _
      (ps' ++ [upPc c₀ q₀ g' zthjo e])
      (.ifLtN_true (by rw [o87, k _ by_omega, h88]; omega) e₅) by_omega
      (fun a ha => by zuonn; exact m₁' a ha) (fun r hr => r₅ r by_omega) a80
      ztheo by_grind by_omega by_omega
      by_omega by_grind
      (by
        have h2 := hch.append (upPc c₀ q₀ g' zthjo e) (by simp [upPc, ← hx2])
        have he : (upPc c₀ q₀ g' zthjo e).e = ⟨c₀ + (x + 2 ^ g' - q₀), 0⟩ := by
          simp only [upPc, ← hx2, WPos.mk.injEq, and_true]; omega
        grind)
      (fun p hp => by
        zutk
        · exact hv p hp
        · zvnns at hp; grind)
      by_simp
    exact ztkko
  · have hodd' := hodd
    rw [o87, k _ by_omega, h88] at hodd'
    obtain ⟨d', k', ex, hU, hk', hg'⟩ := fin d₁ 2 x ps' ztzrt by_omega
      m₁' by_omega (by rw [k _ by_omega, h80]) (by rw [k _ by_omega, h85])
      by_grind hqx hxy by_omega ztcij hch hv by_omega
    exact ztkko

/-! ## The upward cover -/
theorem dyUp_eq : dyUp emit =
    .seq (block [.copyN 150080 150070, .addN 150081 150070 150071, .addN 150088 150081 150091,
      .constN 150082 0, .copyN 150083 150070, .constN 150084 1, .copyN 150085 150040,
      .addN 150087 150080 150084])
    (.seq ztncy
      ztzsi) := rfl

/-- **The upward dyadic cover** of `[q₀, q₀ + L)` from the walk vertex `c₀`. -/
theorem dyUp_exec {W A₀ K : ℕ} {emit : Stmt} {Pv : Pc → Prop}
    {I : List Pc → Config → Prop} (hE : EmitOK P W emit A₀ Pv I K) {m₀ : ℕ → ℕ}
    {Tb Hb Pb tg q₀ L c₀ : ℕ} {ps₀ : List Pc} (c : Config)
    (env : SwEnv P.n W A₀ Tb Hb Pb tg m₀) (hblk : UpBlocks Pv m₀ W A₀ Tb c₀ q₀ L)
    (hqL : q₀ + L ≤ P.n) (hLtg : L ≤ 2 ^ tg) (hW : c₀ + L + 2 ≤ W) (hW' : 3 * L + 2 * P.n + 4 ≤ W)
    (hw : WordsBounded W c) (hm : ∀ a, a < A₀ → c.nmem a = m₀ a)
    (h90 : c.nreg 150090 = 0) (h91 : c.nreg 150091 = 1) (h34 : c.nreg 150034 = Tb)
    (h35 : c.nreg 150035 = Hb) (h36 : c.nreg 150036 = Pb) (h70 : c.nreg 150070 = q₀)
    (h71 : c.nreg 150071 = L) (h40 : c.nreg 150040 = c₀) (hI : I ps₀ c) :
    ∃ c' k ps', Exec P W ztvph c c' k ∧ k ≤ ztlu * ztbdz + 20 ∧
      I ztcdl c' ∧ Chained ztcxt ps' ztrbq ∧ ztbqq ∧
      ps'.length ≤ 2 * ztbdz ∧ c'.nreg 150040 = c₀ + L ∧
      ztfjj ∧
      c'.nreg 150090 = 0 ∧ c'.nreg 150091 = 1 ∧ ztiud := by
  zumbh
  obtain ⟨c₁, k₁, e₁, hk₁, o80, o81, o88, o82, o83, o84, o85, o87, r₁, m₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 150080 150070, .addN 150081 150070 150071,
        .addN 150088 150081 150091, .constN 150082 0, .copyN 150083 150070, .constN 150084 1,
        .copyN 150085 150040, .addN 150087 150080 150084]) c c₁ k₁ ∧ k₁ = 8 ∧
      c₁.nreg 150080 = q₀ ∧ c₁.nreg 150081 = q₀ + L ∧ c₁.nreg 150088 = q₀ + L + 1 ∧
      c₁.nreg 150082 = 0 ∧ c₁.nreg 150083 = q₀ ∧ c₁.nreg 150084 = 1 ∧ c₁.nreg 150085 = c₀ ∧
      c₁.nreg 150087 = q₀ + 1 ∧
      ztgsf ∧ c₁.nmem = c.nmem := by
    exec_block
    all_goals first | (config_simp; rw [h70, h71]; omega) | (config_simp; rw [h70, h71, h91]; omega) |
      (config_simp; rw [h70]; omega) | omega | skip
    refine ztedw
    all_goals first | (config_simp; rw [h70, h71, h91]) | (config_simp; rw [h70, h71]) |
      (config_simp; rw [h70]) | (config_simp; rw [h40]) | config_simp | skip
    zqzn
  zud
  have hA0 : UpA W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ c c₁ :=
    mkUpA q₀ 0 [] w₁ by_simp_all
      by_grind by_simp_all
      by_simp_all by_simp_all
      by_simp_all by_simp_all o80 o81 o82
      by_omega by_omega by_omega by_omega o88 le_rfl
      by_omega (by rw [List.append_nil]; exact hE.stable _ _ _ hI ztduj)
      (by zupbe) by_simp by_simp ztp by_omega
  -- phase A
  obtain ⟨c₂, k₂, e₂, hA2, hx₂, hk₂⟩ := Exec.whileLtN_bounded (P := P) (a := 150087) (b := 150088)
    (body := upABody emit) (UpA W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ c)
    ztjvs ztjje ztoe (fun d hd ht => by
      obtain ⟨d', k, ex, hU, hk, hμ⟩ := upABody_exec hE env hblk hqL hLtg hW hW' hd ht
      grind) hA0
  obtain ⟨w₂, ⟨m₂, s₂, a90, a91, a34, a35, a36⟩, x, g, ps', a80, a81, a82, ax, a84, a85, a87, a88,
    aqx, axy, aI, ach, av, alen, ag1, agt⟩ := hA2
  zuigw
  have hglog : ztpou := by
    zudrx
    · omega
    · zujct
      · grind
      · have := Nat.le_log_of_pow_le by_norm_num h; omega
  have hB0 : UpB W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ c c₂ :=
    ⟨w₂, ⟨m₂, s₂, a90, a91, a34, a35, a36⟩, x, g, ps', a80, a81, a82, ax, a85, a88, aqx, axy,
      by omega, aI, ach, av, by_omega, agt, by
        zueva
        · grind
        · zudrx
          · omega
          · zufeu
            omega⟩
  -- phase B
  obtain ⟨c₃, k₃, e₃, hB3, hx₃, hk₃⟩ := Exec.whileLtN_bounded (P := P) (a := 150090) (b := 150082)
    (body := upBBody emit) (UpB W Pv I ps₀ m₀ A₀ Tb Hb Pb tg q₀ L c₀ c)
    ztqnn ztjje ztoe (fun d hd ht => by
      obtain ⟨d', k, ex, hU, hk, hμ⟩ := upBBody_exec hE env hblk hqL hW hW' hd ht
      grind) hB0
  obtain ⟨w₃, ⟨m₃, s₃, b90, b91, b34, b35, b36⟩, x₃, g₃, ps₃, b80, b81, b82, bx, b85, b88,
    bqx, bxy, byx, bI, bch, bv, blen, bgt, bgb⟩ := hB3
  zucek

  have hxL : x₃ = q₀ + L := by_grind
  zuffl
  refine ⟨_, k₁ + ztdhs, ps₃, ?_, ?_,
    hE.stable _ _ _ bI ztjuw, by rw [hxL] at bch; simpa using bch, bv,
    by omega, by config_simp; grind, fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
  · rw [dyUp_eq]; exact .seq e₁ ztcb
  · zucax

    have hk2' : ztyyv :=
      le_trans hk₂ by_simp
    have hk3' : ztyyw :=
      le_trans hk₃ (by zupbf; have := Nat.mul_le_mul_left ztfnt hglog; omega)
    grind
  · config_simp
    rw [upd_other _ _ _ h3, s₃ r h1 h2]
  · config_simp; omega
  · config_simp; omega
  omega
