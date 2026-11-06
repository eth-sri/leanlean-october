module

public import Chazelle.Core.GranInitL4

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

/-! ## Natural-only statements -/

/-- A natural instruction (no real register, real memory or output effect). -/
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

/-- **A natural-only statement** changes no real register, no real memory and no output. -/
theorem exec_natOnly {P : Polygon} {W : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hs : natOnly s = true) :
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  induction h with
  | skip _ => exact ⟨rfl, rfl, rfl⟩
  | @instr ins c c' _ he _ _ =>
    simp only [natOnly] at hs
    cases ins <;> simp only [natOK, Bool.false_eq_true] at hs <;>
      simp only [Instr.effect, Option.some.injEq] at he <;>
      subst he <;>
      exact ⟨rfl, rfl, rfl⟩
  | seq _ _ ih₁ ih₂ =>
    simp only [natOnly, Bool.and_eq_true] at hs
    obtain ⟨a1, a2, a3⟩ := ih₁ hs.1
    obtain ⟨b1, b2, b3⟩ := ih₂ hs.2
    exact ⟨b1.trans a1, b2.trans a2, b3.trans a3⟩
  | ifLtN_true _ _ ih =>
    simp only [natOnly, Bool.and_eq_true] at hs; exact ih hs.1
  | ifLtN_false _ _ ih =>
    simp only [natOnly, Bool.and_eq_true] at hs; exact ih hs.2
  | ifLtR_true _ _ ih =>
    simp only [natOnly, Bool.and_eq_true] at hs; exact ih hs.1
  | ifLtR_false _ _ ih =>
    simp only [natOnly, Bool.and_eq_true] at hs; exact ih hs.2
  | whileLtN_false _ _ => exact ⟨rfl, rfl, rfl⟩
  | whileLtN_true _ _ _ ih₁ ih₂ =>
    obtain ⟨a1, a2, a3⟩ := ih₁ hs
    obtain ⟨b1, b2, b3⟩ := ih₂ hs
    exact ⟨b1.trans a1, b2.trans a2, b3.trans a3⟩
  | whileLtR_false _ _ => exact ⟨rfl, rfl, rfl⟩
  | whileLtR_true _ _ _ ih₁ ih₂ =>
    obtain ⟨a1, a2, a3⟩ := ih₁ hs
    obtain ⟨b1, b2, b3⟩ := ih₂ hs
    exact ⟨b1.trans a1, b2.trans a2, b3.trans a3⟩

/-! ## Counting -/

theorem cntInit_succ (i : ℕ) (f g : ℕ → ℕ) (j : ℕ) :
    cntInit (i + 1) f g j = cntInit i f g j + (if f i = j then 1 else 0) +
      (if g i = j then 1 else 0) := by
  unfold cntInit
  rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert]
  have h1 : i ∉ Finset.filter (fun u => f u = j) (Finset.range i) := by simp
  have h2 : i ∉ Finset.filter (fun u => g u = j) (Finset.range i) := by simp
  split_ifs with a b b
  · rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2]; ring
  · rw [Finset.card_insert_of_notMem h1]; ring
  · rw [Finset.card_insert_of_notMem h2]; ring
  · ring

theorem cntInit_congr {i : ℕ} {f g f' g' : ℕ → ℕ} (hf : ∀ u, u < i → f' u = f u)
    (hg : ∀ u, u < i → g' u = g u) (j : ℕ) : cntInit i f' g' j = cntInit i f g j := by
  unfold cntInit
  congr 2
  · exact Finset.filter_congr fun u hu => by rw [hf u (Finset.mem_range.1 hu)]
  · exact Finset.filter_congr fun u hu => by rw [hg u (Finset.mem_range.1 hu)]

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
def ndLoop : Stmt := .seq (block [.constN 90070 0, .copyN 90071 90013, .constN 90076 5])
  (.whileLtN 90070 90010 ndBody)

/-- Search and store: the position of the key of `x` into `r bs + i`, counted. -/
def srchStore (bs : ℕ) : Stmt := .seq posStmt (ndStore bs)

theorem band_ne {r : ℕ} (h : 90000 ≤ r) (h' : r < 100000) :
    bandOf r ∉ ({bLocate, bSign} : Finset ℕ) := by
  unfold bandOf bLocate bSign; simp; omega

theorem srchStore_exec {P : Polygon} {W MD NFH b0 : ℕ} {M : Model} {N : NF} {x : WPos}
    {c : Config} (hw : WordsBounded W c) {bs BS i Cb : ℕ}
    (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (hGM : GoodModel M)
    (hwf : ModelDescWF P b0 c.nmem MD) (hMD : ModelDescAt c.nmem MD (Qof P) M)
    (hNW : NFWithin c.nmem NFH b0 N) (hNF : IsNF M (Qof P) N) (hne : (N.F M (Qof P)).Nonempty)
    (h50 : c.nreg 50000 = MD) (h51 : c.nreg 50001 = NFH) (h52 : c.nreg 50002 = x.edge)
    (h53 : c.nreg 50003 = x.hgt) (hx : ProperPos M (Qof P) P.n x) (hx1 : x.hgt ≠ 0)
    (hcut : M.IsCut (N.F M (Qof P)) (M.key (Qof P) x)) (he : x.edge < M.W.n)
    (hbs : bs ≠ 90072 ∧ bs ≠ 90092 ∧ bs ≠ 90093 ∧ bs ≠ 50105 ∧ bs ≠ 90019 ∧ bs ≠ 90070 ∧
      bs ≠ 90038 ∧ 90000 ≤ bs ∧ bs < 100000)
    (hBS : c.nreg bs = BS) (h70 : c.nreg 90070 = i) (h38 : c.nreg 90038 = Cb)
    (h19 : c.nreg 90019 = 1) (hb0 : b0 ≤ c.nreg ALLOC)
    (hdis : ∀ v, v < N.arcs.length → BS + i ≠ Cb + v)
    (hroom : c.nreg ALLOC + NFLoc.locCost 5100 N.arcs.length ≤ W)
    (hBW : BS + i ≤ W) (hCW : Cb + N.arcs.length ≤ c.nreg ALLOC)
    (hcntW : ∀ v, v < N.arcs.length → c.nmem (Cb + v) + 1 ≤ W) :
    ∃ c' k v, Exec P W (srchStore bs) c c' k ∧ k ≤ NFLoc.locCost 5100 N.arcs.length + 7 ∧
      v < N.arcs.length ∧ pk M (Qof P) N v = M.key (Qof P) x ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a =
        upd (upd c.nmem (BS + i) v) (Cb + v) (c.nmem (Cb + v) + 1) a) ∧
      (∀ r, bandOf r ∉ ({bLocate, bSign} : Finset ℕ) → r ≠ ALLOC → r ≠ 90072 → r ≠ 90092 →
        r ≠ 90093 → c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ ({bLocate, bSign} : Finset ℕ) → c'.rreg r = c.rreg r) ∧
      (∀ a, a < c.nreg ALLOC → c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hbs
  have hA0 : 0 < N.arcs.length := by
    obtain ⟨j, hj, -⟩ := cut_pk hNF hGM hcut; omega
  have hN : NFAt c.nmem NFH N := hNW.holds
  obtain ⟨hNB, hNAB, hNSB⟩ := NFLoc.nfWithin_bounds hNW hNF hA0
  obtain ⟨hDW, hCWf⟩ := NFLoc.locChainWF_of hwf (by omega) hWh
  have hW3 : P.n + 3 ≤ W := by unfold hostWords at hWh; omega
  have hst : ∀ j, j < N.arcs.length → ProperPos M (Qof P) P.n (N.arc j).s := fun j hj => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hpp⟩ := hNF
    have := (hpp j hj).1
    have hQn : (Qof P).n = P.n := shear_n _ _
    rwa [hQn] at this
  have hxe : x = ⟨c.nreg 50002, c.nreg 50003⟩ := by rw [h52, h53]
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, t0, tlt, tpk⟩ := pos_exec (P := P) (W := W) (c := c) hw
    ⟨hG, hW3, by rw [h50]; exact hDW, by rw [h50]; exact hCWf, M, by rw [h50]; exact hMD,
      by rw [h52]; exact he⟩ hG hW3 (M := M) (N := N) (by rw [h50]; exact hMD) hGM
    (by rw [h51]; exact hN) hNF hne (by rw [← hxe]; exact hx) (by rw [h53]; exact hx1)
    (by rw [← hxe]; exact hcut) hst (by rw [h51]; omega) (by rw [h51]; omega)
    (by rw [h51]; omega) hroom
  rw [← hxe] at tpk
  obtain ⟨fr, frr, fm, frm, fo, fa1, fa2⟩ := F₁
  have w₁ := e₁.wb_right
  have g : ∀ r, 90000 ≤ r → r < 100000 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    fr r (band_ne h1 h2) (by unfold ALLOC; omega)
  have c19 : c₁.nreg 90019 = 1 := by rw [g _ (by norm_num) (by norm_num), h19]
  have c70 : c₁.nreg 90070 = i := by rw [g _ (by norm_num) (by norm_num), h70]
  have c38 : c₁.nreg 90038 = Cb := by rw [g _ (by norm_num) (by norm_num), h38]
  have cbs : c₁.nreg bs = BS := by rw [g _ b8 b9, hBS]
  have hne' := hdis (c₁.nreg 50105 - 1) tlt
  obtain ⟨c₂, k₂, e₂, hk₂, q⟩ : ∃ c₂ k₂, Exec P W (ndStore bs) c₁ c₂ k₂ ∧ k₂ = 7 ∧
      (c₂.nmem = upd (upd c₁.nmem (BS + i) (c₁.nreg 50105 - 1)) (Cb + (c₁.nreg 50105 - 1))
        (c₁.nmem (Cb + (c₁.nreg 50105 - 1)) + 1) ∧
        ∀ r, r ≠ 90072 → r ≠ 90092 → r ≠ 90093 → c₂.nreg r = c₁.nreg r) := by
    unfold ndStore
    exec_block
    · simp (disch := omega) only [Machine.upd_other, cbs, c70]
      omega
    · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, c38, c19]
      omega
    · simp (disch := omega) only [Machine.upd_same,
        Machine.upd_other, cbs, c70, c38, c19]
      rw [fm _ (by omega)]
      exact hcntW _ tlt
    · refine ⟨rfl, ?_, fun r a1 a2 a3 => ?_⟩
      · simp (disch := omega) only [Machine.upd_other, cbs, c70, c38, c19]
      · simp (disch := omega) only [Machine.upd_other]
  obtain ⟨q1, q2⟩ := q
  have NO := exec_natOnly e₂ (by simp [ndStore, natOnly, natOK, block])
  have a2' : c₂.nreg ALLOC = c₁.nreg ALLOC :=
    q2 _ (by unfold ALLOC; omega) (by unfold ALLOC; omega) (by unfold ALLOC; omega)
  refine ⟨c₂, _, c₁.nreg 50105 - 1, .seq e₁ e₂, by omega, tlt, tpk, fun a ha => ?_,
    fun r a1 a2 a3 a4 a5 => ?_, fun r hr => ?_, fun a ha => ?_, ?_, by rw [a2']; exact fa1, ?_⟩
  · rw [q1, fm (Cb + (c₁.nreg 50105 - 1)) (by omega)]
    simp only [upd]
    split_ifs
    · rfl
    · rfl
    · exact fm a ha
  · rw [q2 r a3 a4 a5]; exact fr r a1 a2
  · rw [NO.1]; exact frr r hr
  · rw [NO.2.1]; exact frm a ha
  · rw [NO.2.2]; exact fo
  · rw [a2']; omega

/-! ## The query setups -/

theorem ndA_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {MD NFH p h lp : ℕ}
    (h00 : c.nreg 90000 = MD) (h01 : c.nreg 90001 = NFH) (h71 : c.nreg 90071 = p)
    (h19 : c.nreg 90019 = 1) (hh : c.nmem p = h) (hlp : c.nmem (p + 1) = lp)
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

theorem ndC_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {MD NFH p rp : ℕ}
    (h00 : c.nreg 90000 = MD) (h01 : c.nreg 90001 = NFH) (h71 : c.nreg 90071 = p)
    (h21 : c.nreg 90021 = 2) (hrp : c.nmem (p + 2) = rp) (hb : p + 2 ≤ W) :
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

theorem ndE_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {p i : ℕ}
    (h71 : c.nreg 90071 = p) (h70 : c.nreg 90070 = i) (h76 : c.nreg 90076 = 5)
    (h19 : c.nreg 90019 = 1) (hb : p + 5 ≤ W) (hi : i + 1 ≤ W) :
    ∃ c' k, Exec P W ndE c c' k ∧ k = 2 ∧ c'.nreg 90071 = p + 5 ∧ c'.nreg 90070 = i + 1 ∧
      c'.nmem = c.nmem ∧ (∀ r, r ≠ 90070 → r ≠ 90071 → c'.nreg r = c.nreg r) := by
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
  hNF : IsNF M (Qof P) N
  hne : (N.F M (Qof P)).Nonempty
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
  desc : ModelDescAt c₀.nmem MD (Qof P) M
  nfw : NFWithin c₀.nmem NFH d.b0 N
  chords : ∀ i, i < N.nChords → c₀.nmem (CB + 5 * i) = (N.chord i).h ∧
    c₀.nmem (CB + 5 * i + 1) = (N.chord i).lp ∧ c₀.nmem (CB + 5 * i + 2) = (N.chord i).rp
  cbB : CB + 5 * N.nChords ≤ d.b0
  room : c₀.nreg ALLOC + N.nChords * (2 * NFLoc.locCost 5100 N.arcs.length + 30) ≤ W
  cnt0 : ∀ j, j < N.arcs.length → c₀.nmem (d.b0 + d.oCnt + j) = 0

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
    c.nreg 90070 * (2 * NFLoc.locCost 5100 N.arcs.length + 30)
  nd0 : ∀ u, u < c.nreg 90070 → c.nmem (d.b0 + d.oNd0 + u) < N.arcs.length ∧
    pk M (Qof P) N (c.nmem (d.b0 + d.oNd0 + u)) = M.key (Qof P) (N.chord u).lpos
  nd1 : ∀ u, u < c.nreg 90070 → c.nmem (d.b0 + d.oNd1 + u) < N.arcs.length ∧
    pk M (Qof P) N (c.nmem (d.b0 + d.oNd1 + u)) = M.key (Qof P) (N.chord u).rpos
  cnt : ∀ j, j < N.arcs.length → c.nmem (d.b0 + d.oCnt + j) =
    cntInit (c.nreg 90070) (fun u => c.nmem (d.b0 + d.oNd0 + u))
      (fun u => c.nmem (d.b0 + d.oNd1 + u)) j
  mem : ∀ a, a < c₀.nreg ALLOC → (a < d.b0 + d.oNd0 ∨ d.b0 + d.oDeg ≤ a) →
    (a < d.b0 + d.oCnt ∨ d.b0 + d.oNxt ≤ a) → c.nmem a = c₀.nmem a

theorem cntInit_le (i : ℕ) (f g : ℕ → ℕ) (j : ℕ) : cntInit i f g j ≤ 2 * i := by
  unfold cntInit
  have h1 := Finset.card_filter_le (Finset.range i) (fun u => f u = j)
  have h2 := Finset.card_filter_le (Finset.range i) (fun u => g u = j)
  rw [Finset.card_range] at h1 h2
  omega

set_option maxHeartbeats 4000000 in
theorem ndBody_exec {P : Polygon} {W MD NFH CB : ℕ} {d : Dm} {M : Model} {N : NF}
    {c₀ c : Config} (hE : NdEnv P W MD NFH CB d M N c₀) (hI : NdI P W d M N c₀ c)
    (ht : c.nreg 90070 < N.nChords) :
    ∃ c' k, Exec P W ndBody c c' k ∧ NdI P W d M N c₀ c' ∧
      k ≤ 2 * NFLoc.locCost 5100 N.arcs.length + 30 ∧ c'.nreg 90070 = c.nreg 90070 + 1 ∧
      c'.nreg ALLOC ≤ c.nreg ALLOC + k := by
  obtain ⟨hw, hle, hp, h76, r9, fr, frr, frm, fro, al1, al2, hnd0, hnd1, hcnt, hm⟩ := hI
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩ := d.lay
  have yN0 : d.oNd0 = 3 * d.K := rfl
  have yN1 : d.oNd1 = 4 * d.K := rfl
  have hK := hE.hK
  have hA := hE.hA
  have hal := hE.alloc
  have hcb := hE.cbB
  have hroom := hE.room
  set L := NFLoc.locCost 5100 N.arcs.length with hL
  set K := N.nChords with hKdef
  set A := N.arcs.length with hAdef
  generalize hii : c.nreg 90070 = i at ht hle hp al2 hnd0 hnd1 hcnt
  have hi1 : (i + 1) * (2 * L + 30) ≤ K * (2 * L + 30) := Nat.mul_le_mul_right _ (by omega)
  have hmi : i * (2 * L + 30) + (2 * L + 30) = (i + 1) * (2 * L + 30) := by ring
  have hK1 : 30 ≤ K * (2 * L + 30) := by
    have : 1 * 30 ≤ K * (2 * L + 30) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hQn : (Qof P).n = P.n := shear_n _ _
  -- memory below `b0`
  have hb0 : ∀ a, a < d.b0 → c.nmem a = c₀.nmem a := fun a ha =>
    hm a (by omega) (by left; omega) (by left; omega)
  obtain ⟨ch0, ch1, ch2⟩ := hE.chords i ht
  rw [hE.r13] at hp
  have v0 : c.nmem (CB + 5 * i) = (N.chord i).h := by rw [hb0 _ (by omega), ch0]
  have v1 : c.nmem (CB + 5 * i + 1) = (N.chord i).lp := by rw [hb0 _ (by omega), ch1]
  have v2 : c.nmem (CB + 5 * i + 2) = (N.chord i).rp := by rw [hb0 _ (by omega), ch2]
  have hBc : Bases c d := hE.bases.frame fun q a1 a2 => r9 q (by omega) (by omega)
    (by simp [Binit]; omega)
  have c00 : c.nreg 90000 = MD := by rw [r9 _ (by norm_num) (by norm_num) (by decide), hE.r00]
  have c01 : c.nreg 90001 = NFH := by rw [r9 _ (by norm_num) (by norm_num) (by decide), hE.r01]
  have c19 : c.nreg 90019 = 1 := by rw [r9 _ (by norm_num) (by norm_num) (by decide), hE.r19]
  have c21 : c.nreg 90021 = 2 := by rw [r9 _ (by norm_num) (by norm_num) (by decide), hE.r21]
  have hhlt : (N.chord i).h < P.n := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hh, -⟩ := hE.hNF
    rw [← hQn]; exact hh i ht
  have hWP : P.n + 3 ≤ W := by have := hE.hWh; unfold hostWords at this; omega
  -- 1. the left query
  obtain ⟨c₁, k₁, e₁, hk₁, a00, a01, a02, a03, a91, am, ar⟩ := ndA_exec (P := P) c hw c00 c01 hp
    c19 v0 v1 (by omega) (by omega)
  have w₁ := e₁.wb_right
  have g₁ : ∀ r, 90000 ≤ r → r < 100000 → Binit r = false → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 => ar r (by omega) (by omega) (by omega) (by omega)
      (by simp [Binit] at h3; omega) (by simp [Binit] at h3; omega) (by simp [Binit] at h3; omega)
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := ar _ (by unfold ALLOC; omega)
    (by unfold ALLOC; omega) (by unfold ALLOC; omega) (by unfold ALLOC; omega)
    (by unfold ALLOC; omega) (by unfold ALLOC; omega) (by unfold ALLOC; omega)
  have hag₁ : ∀ a, a < d.b0 → c₁.nmem a = c₀.nmem a := fun a ha => by rw [am, hb0 a ha]
  obtain ⟨hdesc₁, hwf₁⟩ := desc_agree' hE.wf hE.desc hag₁
  have hNW₁ : NFWithin c₁.nmem NFH d.b0 N := hE.nfw.transport hag₁
  have hi' : i < N.nChords := ht
  have hlp := lpos_proper hE.hNF hi'
  rw [hQn] at hlp
  obtain ⟨c₂, k₂, x0, e₂, hk₂, x0lt, x0pk, M2, R2, RR2, RM2, O2, A21, A22⟩ :=
    srchStore_exec (P := P) (W := W) (b0 := d.b0) (M := M) (N := N) (x := (N.chord i).lpos)
    (c := c₁) w₁ (bs := 90033) (BS := d.b0 + d.oNd0) (i := i) (Cb := d.b0 + d.oCnt) hE.hG hE.hWh
    hE.hGM hwf₁ hdesc₁ hNW₁ hE.hNF hE.hne a00 a01 a02 a03 hlp (by simp [CRec.lpos])
    (lkey_cut hE.hNF hi') (attach_l hE.hNF hi').1
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide⟩
    (by rw [g₁ _ (by norm_num) (by norm_num) (by decide), hBc.bNd0])
    (by rw [ar 90070 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hii])
    (by rw [g₁ _ (by norm_num) (by norm_num) (by decide), hBc.bCnt])
    (by rw [g₁ _ (by norm_num) (by norm_num) (by decide), c19]) (by omega)
    (fun v hv => by omega) (by omega) (by omega) (by omega)
    (fun v hv => by
      rw [am, hcnt v hv]
      have := cntInit_le i (fun u => c.nmem (d.b0 + d.oNd0 + u))
        (fun u => c.nmem (d.b0 + d.oNd1 + u)) v
      omega)
  have w₂ := e₂.wb_right
  have g₂ : ∀ r, 90000 ≤ r → r < 100000 → Binit r = false → c₂.nreg r = c.nreg r :=
    fun r h1 h2 h3 => by
      rw [R2 r (band_ne h1 h2) (by unfold ALLOC; omega) (by simp [Binit] at h3; omega)
        (by simp [Binit] at h3; omega) (by simp [Binit] at h3; omega), g₁ r h1 h2 h3]
  have c2_71 : c₂.nreg 90071 = CB + 5 * i := by
    rw [R2 _ (band_ne (by norm_num) (by norm_num)) (by unfold ALLOC; omega) (by decide)
      (by decide) (by decide), ar _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hp]
  have c2_91 : c₂.nreg 90091 = (N.chord i).h + 1 := by
    rw [R2 _ (band_ne (by norm_num) (by norm_num)) (by unfold ALLOC; omega) (by decide)
      (by decide) (by decide), a91]
  have c2_70 : c₂.nreg 90070 = i := by
    rw [R2 _ (band_ne (by norm_num) (by norm_num)) (by unfold ALLOC; omega) (by decide)
      (by decide) (by decide), ar _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hii]
  have m2b : ∀ a, a < d.b0 → c₂.nmem a = c₀.nmem a := fun a ha => by
    rw [M2 a (by omega), Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
      hag₁ a ha]
  -- 2. the right query
  obtain ⟨c₃, k₃, e₃, hk₃, b00, b01, b02, b03, bm, br⟩ := ndC_exec (P := P) c₂ w₂
    (by rw [g₂ _ (by norm_num) (by norm_num) (by decide), c00])
    (by rw [g₂ _ (by norm_num) (by norm_num) (by decide), c01]) c2_71
    (by rw [g₂ _ (by norm_num) (by norm_num) (by decide), c21])
    (by rw [m2b _ (by omega), ch2]) (by omega)
  rw [c2_91] at b03
  have w₃ := e₃.wb_right
  have hA₃ : c₃.nreg ALLOC = c₂.nreg ALLOC := br _ (by unfold ALLOC; omega)
    (by unfold ALLOC; omega) (by unfold ALLOC; omega) (by unfold ALLOC; omega)
    (by unfold ALLOC; omega)
  have hag₃ : ∀ a, a < d.b0 → c₃.nmem a = c₀.nmem a := fun a ha => by rw [bm, m2b a ha]
  obtain ⟨hdesc₃, hwf₃⟩ := desc_agree' hE.wf hE.desc hag₃
  have hNW₃ : NFWithin c₃.nmem NFH d.b0 N := hE.nfw.transport hag₃
  have hrp := rpos_proper hE.hNF hi'
  rw [hQn] at hrp
  have g₃ : ∀ r, 90000 ≤ r → r < 100000 → Binit r = false → c₃.nreg r = c.nreg r :=
    fun r h1 h2 h3 => by
      rw [br r (by omega) (by omega) (by omega) (by omega) (by simp [Binit] at h3; omega),
        g₂ r h1 h2 h3]
  obtain ⟨c₄, k₄, x1, e₄, hk₄, x1lt, x1pk, M4, R4, RR4, RM4, O4, A41, A42⟩ :=
    srchStore_exec (P := P) (W := W) (b0 := d.b0) (M := M) (N := N) (x := (N.chord i).rpos)
    (c := c₃) w₃ (bs := 90034) (BS := d.b0 + d.oNd1) (i := i) (Cb := d.b0 + d.oCnt) hE.hG hE.hWh
    hE.hGM hwf₃ hdesc₃ hNW₃ hE.hNF hE.hne b00 b01 b02 b03 hrp (by simp [CRec.rpos])
    (rkey_cut hE.hNF hi') (attach_r hE.hNF hi').1
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide⟩
    (by rw [g₃ _ (by norm_num) (by norm_num) (by decide), hBc.bNd1])
    (by rw [br _ (by decide) (by decide) (by decide) (by decide) (by decide), c2_70])
    (by rw [g₃ _ (by norm_num) (by norm_num) (by decide), hBc.bCnt])
    (by rw [g₃ _ (by norm_num) (by norm_num) (by decide), c19]) (by omega)
    (fun v hv => by omega) (by omega) (by omega) (by omega)
    (fun v hv => by
      rw [bm, M2 _ (by omega), am]
      have hc := hcnt v hv
      have hc' := hcnt x0 x0lt
      have := cntInit_le i (fun u => c.nmem (d.b0 + d.oNd0 + u))
        (fun u => c.nmem (d.b0 + d.oNd1 + u)) v
      have := cntInit_le i (fun u => c.nmem (d.b0 + d.oNd0 + u))
        (fun u => c.nmem (d.b0 + d.oNd1 + u)) x0
      have hK30 : K * 30 ≤ K * (2 * L + 30) := Nat.mul_le_mul_left _ (by omega)
      simp only [upd]
      split_ifs <;> omega)
  have w₄ := e₄.wb_right
  have g₄ : ∀ r, 90000 ≤ r → r < 100000 → Binit r = false → c₄.nreg r = c.nreg r :=
    fun r h1 h2 h3 => by
      rw [R4 r (band_ne h1 h2) (by unfold ALLOC; omega) (by simp [Binit] at h3; omega)
        (by simp [Binit] at h3; omega) (by simp [Binit] at h3; omega), g₃ r h1 h2 h3]
  have c4_71 : c₄.nreg 90071 = CB + 5 * i := by
    rw [R4 _ (band_ne (by norm_num) (by norm_num)) (by unfold ALLOC; omega) (by decide)
      (by decide) (by decide), br _ (by decide) (by decide) (by decide) (by decide) (by decide),
      c2_71]
  have c4_70 : c₄.nreg 90070 = i := by
    rw [R4 _ (band_ne (by norm_num) (by norm_num)) (by unfold ALLOC; omega) (by decide)
      (by decide) (by decide), br _ (by decide) (by decide) (by decide) (by decide) (by decide),
      c2_70]
  have c4_76 : c₄.nreg 90076 = 5 := by
    rw [R4 _ (band_ne (by norm_num) (by norm_num)) (by unfold ALLOC; omega) (by decide)
      (by decide) (by decide), br _ (by decide) (by decide) (by decide) (by decide) (by decide),
      R2 _ (band_ne (by norm_num) (by norm_num)) (by unfold ALLOC; omega) (by decide)
      (by decide) (by decide), ar _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), h76]
  -- 3. advance
  obtain ⟨c₅, k₅, e₅, hk₅, d71, d70, dm, dr⟩ := ndE_exec (P := P) c₄ w₄ c4_71 c4_70 c4_76
    (by rw [g₄ _ (by norm_num) (by norm_num) (by decide), c19]) (by omega) (by omega)
  -- the memory
  set m1 := upd (upd c.nmem (d.b0 + d.oNd0 + i) x0) (d.b0 + d.oCnt + x0)
    (c.nmem (d.b0 + d.oCnt + x0) + 1) with hm1
  have H2 : ∀ a, a < c₁.nreg ALLOC → c₂.nmem a = m1 a := fun a ha => by rw [M2 a ha, am]
  have M5 : ∀ a, a < c₀.nreg ALLOC → c₅.nmem a =
      upd (upd m1 (d.b0 + d.oNd1 + i) x1) (d.b0 + d.oCnt + x1) (m1 (d.b0 + d.oCnt + x1) + 1) a := by
    intro a ha
    rw [dm, M4 a (by omega), bm]
    simp only [upd]
    split_ifs
    · rw [H2 _ (by omega)]
    · rfl
    · exact H2 a (by omega)
  have NA := exec_natOnly e₁ (by simp [ndA, natOnly, natOK, block])
  have NC := exec_natOnly e₃ (by simp [ndC, natOnly, natOK, block])
  have NE := exec_natOnly e₅ (by simp [ndE, natOnly, natOK, block])
  have hA₅ : c₅.nreg ALLOC = c₄.nreg ALLOC := dr _ (by unfold ALLOC; omega)
    (by unfold ALLOC; omega)
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))),
    ⟨e₅.wb_right, by omega, by rw [d71, d70, hE.r13]; ring, ?_, fun r h1 h2 h3 => ?_,
      fun r h1 h2 => ?_, fun r h1 => ?_, fun a ha => ?_, ?_, ?_, ?_,
      fun u hu => ?_, fun u hu => ?_, fun j hj => ?_, fun a ha b1 b2 => ?_⟩, ?_,
    by rw [d70], by omega⟩
  · rw [dr _ (by decide) (by decide), c4_76]
  · have h3' := h3
    simp only [Binit, decide_eq_false_iff_not] at h3'
    rw [dr r (by omega) (by omega), g₄ r h1 h2 h3, r9 r h1 h2 h3]
  · have hb9 : ¬ (90000 ≤ r ∧ r < 100000) := by
      intro h; apply h1; simp only [bandOf, bGran, Finset.mem_insert, Finset.mem_singleton]
      omega
    have h15 : bandOf r ∉ ({bLocate, bSign} : Finset ℕ) := by
      intro h; apply h1
      simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    have hn5 : ¬ (50000 ≤ r ∧ r < 60000) := by
      intro h; apply h15; simp only [bandOf, bLocate, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [dr r (by omega) (by omega), R4 r h15 h2 (by omega) (by omega) (by omega),
      br r (by omega) (by omega) (by omega) (by omega) (by omega),
      R2 r h15 h2 (by omega) (by omega) (by omega),
      ar r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      fr r h1 h2]
  · rw [NE.1, RR4 r h1, NC.1, RR2 r h1, NA.1, frr r h1]
  · rw [NE.2.1, RM4 a (by omega), NC.2.1, RM2 a (by omega), NA.2.1, frm a ha]
  · rw [NE.2.2, O4, NC.2.2, O2, NA.2.2, fro]
  · omega
  · rw [d70, ← hL]; omega
  · rw [d70] at hu
    rw [M5 _ (by omega), Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
      hm1]
    by_cases hui : u = i
    · subst hui
      rw [Machine.upd_other _ _ _ (by omega)]; simp only [Machine.upd_same]
      exact ⟨x0lt, x0pk⟩
    · rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega)]
      exact hnd0 u (by omega)
  · rw [d70] at hu
    rw [M5 _ (by omega), Machine.upd_other _ _ _ (by omega)]
    by_cases hui : u = i
    · subst hui
      simp only [Machine.upd_same]
      exact ⟨x1lt, x1pk⟩
    · rw [Machine.upd_other _ _ _ (by omega), hm1, Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (by omega)]
      exact hnd1 u (by omega)
  · -- the counts
    have f0 : ∀ u, u < i → c₅.nmem (d.b0 + d.oNd0 + u) = c.nmem (d.b0 + d.oNd0 + u) := by
      intro u hu
      rw [M5 _ (by omega), Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
        hm1, Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega)]
    have g0 : ∀ u, u < i → c₅.nmem (d.b0 + d.oNd1 + u) = c.nmem (d.b0 + d.oNd1 + u) := by
      intro u hu
      rw [M5 _ (by omega), Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
        hm1, Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega)]
    have fi : c₅.nmem (d.b0 + d.oNd0 + i) = x0 := by
      rw [M5 _ (by omega), Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
        hm1, Machine.upd_other _ _ _ (by omega)]; simp
    have gi : c₅.nmem (d.b0 + d.oNd1 + i) = x1 := by
      rw [M5 _ (by omega), Machine.upd_other _ _ _ (by omega)]; simp
    rw [d70, cntInit_succ, cntInit_congr f0 g0, fi, gi, ← hcnt j hj, M5 _ (by omega), hm1]
    by_cases e1 : x1 = j
    · subst e1
      by_cases e0 : x0 = x1
      · subst e0
        simp (disch := omega) only [Machine.upd_same, ite_true]
      · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, ite_true, e0, ite_false]
    · by_cases e0 : x0 = j
      · subst e0
        simp (disch := omega) only [Machine.upd_same, Machine.upd_other, ite_true, e1, ite_false]
      · simp (disch := omega) only [Machine.upd_other, e1, e0, ite_false,
          Nat.add_zero]
  · rw [M5 _ ha, Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega), hm1,
      Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega)]
    exact hm a ha b1 b2
  · omega

theorem ndLoop_exec {P : Polygon} {W MD NFH CB : ℕ} {d : Dm} {M : Model} {N : NF} {c₀ : Config}
    (hw : WordsBounded W c₀) (hE : NdEnv P W MD NFH CB d M N c₀) (hW5 : 5 ≤ W) :
    ∃ c' k, Exec P W ndLoop c₀ c' k ∧
      k ≤ N.nChords * (2 * NFLoc.locCost 5100 N.arcs.length + 32) + 5 ∧
      NdI P W d M N c₀ c' ∧ c'.nreg 90070 = N.nChords ∧ c'.nreg ALLOC ≤ c₀.nreg ALLOC + k := by
  obtain ⟨c₁, k₁, e₁, hk₁, q, q0⟩ : ∃ c₁ k₁, Exec P W (block [.constN 90070 0, .copyN 90071 90013,
      .constN 90076 5]) c₀ c₁ k₁ ∧ k₁ = 3 ∧ NdI P W d M N c₀ c₁ ∧ c₁.nreg 90070 = 0 := by
    exec_block
    · omega
    · omega
    · refine ⟨rfl, ⟨by assumption, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, fun r h1 h2 => ?_,
        fun r _ => rfl, fun a _ => rfl, rfl, ?_, ?_, fun u hu => ?_, fun u hu => ?_,
        fun j hj => ?_, fun a _ _ _ => rfl⟩, ?_⟩
      · config_simp; omega
      · config_simp; omega
      · config_simp
      · simp only [Binit, decide_eq_false_iff_not] at h3
        config_simp; simp only [upd]; split_ifs <;> first | rfl | omega
      · have : r < 90000 ∨ 100000 ≤ r := by
          by_contra hc; apply h1; simp only [bandOf, bGran, Finset.mem_insert,
            Finset.mem_singleton]; omega
        config_simp; simp only [upd]; split_ifs <;> first | rfl | omega
      · config_simp; simp only [upd, ALLOC]; simp
      · config_simp; simp only [upd, ALLOC]; simp
      · simp [upd] at hu
      · simp [upd] at hu
      · config_simp; rw [hE.cnt0 j hj]; simp [cntInit]
      · config_simp
  obtain ⟨c', k, e, I', hx, hk, hA'⟩ := SortR.whileLtN_potential_lb (P := P) (W := W)
    (a := 90070) (b := 90010) (body := ndBody) (NdI P W d M N c₀)
    (fun c => (N.nChords - c.nreg 90070) * (2 * NFLoc.locCost 5100 N.arcs.length + 32))
    (fun c => c.nreg ALLOC) (fun _ h => h.wb)
    (fun c I ht => by
      have t : c.nreg 90070 < N.nChords := by
        rw [I.r9 90010 (by norm_num) (by norm_num) (by decide), hE.r10] at ht; exact ht
      obtain ⟨c', k, e, I', hk, hi, ha⟩ := ndBody_exec (P := P) hE I t
      refine ⟨c', k, e, I', ?_, ha⟩
      rw [hi]
      have : N.nChords - c.nreg 90070 = (N.nChords - (c.nreg 90070 + 1)) + 1 := by omega
      rw [this, Nat.add_mul, one_mul]
      omega) q
  have hK' : c'.nreg 90070 = N.nChords := by
    rw [I'.r9 90010 (by norm_num) (by norm_num) (by decide), hE.r10] at hx
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
