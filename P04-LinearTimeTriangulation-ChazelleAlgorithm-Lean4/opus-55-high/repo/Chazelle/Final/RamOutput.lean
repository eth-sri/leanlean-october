module

public import Chazelle.MacT
public import Chazelle.Core.SweepIoQry
public import Chazelle.Final.RamSplit
public import Chazelle.Core.FactsAttach
public import Chazelle.Core.NFDecompBfs
public import Chazelle.Core.SpecNF
public import Chazelle.Core.ShootCutShPt
public import Chazelle.Core.NFBuildRegFill
public import Chazelle.Core.BruteRam3
public import Chazelle.Core.NFBuildArcs
public import Chazelle.Core.DownPhaseDrvBTopMain

section
set_option hygiene false
local macro "zqbbp" : tactic => `(tactic| (refine spec_name fun c₁ hc₁ => ?_
                                           have hw₁ : ztidr := by_simp_all))
local macro "zqbbq" : tactic => `(tactic| rw [h249, h242, h241, Machine.upd_other _ _ _ by_omega, (hB z hzN).2, hx1])
local macro "zqbbr" : tactic => `(tactic| have hl : 0 < d.length := by_omega)
local macro "zqbbs" : tactic => `(tactic| (set x := d.getD _ 0 with hx
                                           have hxd : x ∈ d := getD_mem_of_lt ztbpn))
local macro "zqbbt" : tactic => `(tactic| (config_simp; grind))
set_option hygiene true

/-!
# The output pass on the RAM

After the splitting (`Chazelle.Final.splitStmt`) the work area holds the final linked structure
`S` (vertex band `VB`, successor band `NB`, nodes `0 … NN - 1`), whose cycles are the pieces of
the subdivision (`runState_spec`).  `outStmt` visits the nodes `z = 0, 1, …, NN - 1` with a mark
array `MB`: when `z` is unmarked, it walks its cycle marking every node and counting its length
`m`, then runs the piece triangulator `pieceTriStmt` (`Chazelle.Final.RamPieceTri`) on the cycle
from `z`.  Every cycle is thus triangulated exactly once (from its smallest node); the total
cost is linear in `NN` since the lengths of the cycles sum to `NN`.

## Layout

Inputs (natural registers): `nreg 240 = NN`, `241 = MB` (mark array, `NN` cells),
`249 = NB`, `250 = VB`, `251 = WB` (work band of the piece triangulator, `4 NN` cells).
Registers written: natural `242 … 248`, `60 … 94` (the piece triangulator), real `61 … 83`.
Memory written: `[MB, MB + NN)` and `[WB, WB + 4 NN)`.
-/
namespace Chazelle.Final
open Machine Machine.Stmt Programs
open Chazelle.EarClip (subPoly relabelList n_subPoly)
open Chazelle.Existence (WeakTriangulates)
open Chazelle.Mountain (IsPiece)
@[expose] public section
variable {cs : List (List ℕ)} {S : LState}
theorem disj_of_nodup_flatten (h : cs.flatten.Nodup) {c d : List ℕ}
    (hc : c ∈ cs) (hd : d ∈ cs) (hne : c ≠ d) {y : ℕ} (hy : y ∈ c) : y ∉ d := by
  induction cs with
  | nil => exact absurd hc List.not_mem_nil
  | cons a rest ih =>
    rw [List.flatten_cons, List.nodup_append] at h
    obtain ⟨-, h2, h3⟩ := h
    rcases List.mem_cons.1 hc with rfl | hc' <;> rcases List.mem_cons.1 hd with rfl | hd'
    · simp_all
    · intro hyd
      zuiti
    · intro hyd
      exact h3 y hyd y ztmbl rfl
    · simp_all

/-- Nonempty lists with a duplicate-free concatenation are pairwise distinct. -/
theorem nodup_of_nodup_flatten (h : cs.flatten.Nodup)
    (hne : ∀ c ∈ cs, c ≠ []) : cs.Nodup := by
  induction cs with
  | nil => exact List.nodup_nil
  | cons a rest ih =>
    zuivb
    rw [List.flatten_cons, List.nodup_append] at h'
    obtain ⟨-, h2, h3⟩ := h'
    refine List.nodup_cons.2 ⟨fun ha => ?_, by_simp_all⟩
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil a by_simp_all
    zuiti

/-- The cycles of a representation are pairwise distinct. -/
theorem Repr.nodup_cs {cs : List ztul} (hR : Repr S cs) : cs.Nodup :=
  nodup_of_nodup_flatten hR.nodup fun c hc => (hR.cyc c hc).1

/-- Distinct cycles of a representation are disjoint. -/
theorem Repr.disj {cs : List ztul} (hR : Repr S cs) {c d : List ℕ}
    (hc : c ∈ cs) (hd : d ∈ cs) (hne : c ≠ d) {y : ℕ} (hy : y ∈ c) : y ∉ d :=
  disj_of_nodup_flatten hR.nodup hc hd hne hy

/-- Every node lies on a cycle of the representation. -/
theorem Repr.exists_cyc {cs : List ztul} (hR : Repr S cs) {y : ℕ}
    (hy : y < S.cnt) : ∃ c ∈ cs, y ∈ c := by
  obtain ⟨c, hc, hyc⟩ := List.mem_flatten.1 ((hR.mem y).2 hy)
  grind

/-- The members of the cycles are nodes. -/
theorem Repr.lt_cnt {cs : List ztul} (hR : Repr S cs) {c : List ℕ}
    (hc : c ∈ cs) {y : ℕ} (hy : y ∈ c) : y < S.cnt :=
  (hR.mem y).1 ztmbl

/-- A cycle of a representation has no repeated node. -/
theorem Repr.nodup_cyc {cs : List ztul} (hR : Repr S cs) {c : List ℕ}
    (hc : c ∈ cs) : c.Nodup :=
  (List.nodup_flatten.1 hR.nodup).1 c hc

/-- The node sequence read in memory is the successor iteration. -/
theorem nodeSeq_eq_iterate {mem : ℕ → ℕ} {NB : ℕ} {S : LState} {c : List ℕ} (hc : IsCyc S c)
    (hmem : ∀ y ∈ c, mem ztjkf = S.nxt y) {i : ℕ} (hi : i < c.length) :
    ∀ s, nodeSeq mem NB ztcus s = c.getD ztmza 0 := by
  zufve
  zumhi
  induction s with
  | zero => rw [nodeSeq_zero, Nat.add_zero, Nat.mod_eq_of_lt hi]
  | succ s ih =>
    rw [nodeSeq_succ, ih, hmem _ ztbahx,
      (hc.2 _ ztbpn).1, Nat.mod_add_mod, Nat.add_assoc]

/-- The walk from position `i` of a cycle, read as vertices. -/
theorem walk_map_getD {c : List ℕ} (hc : IsCyc S c) {i : ℕ} (hi : i < c.length)
    {s : ℕ} (hs : s < c.length) :
    ((walk S ztcus c.length).map S.vtx).getD s 0 = S.vtx (c.getD ztmza 0) := by
  rw [walk_eq_rotate hc hi, List.map_rotate, getD_rotate_of_lt i by_simp_all,
    List.length_map, getD_map_of_lt S.vtx ztcv, Nat.add_comm s i]

/-! ### Counting marks -/

/-- Marking the (distinct, previously unmarked) positions of `c` lowers the number of unmarked
positions by `c.length`. -/
theorem countP_mark {NN : ℕ} {f g : ℕ → ℕ} {c : List ℕ} (hc : c.Nodup) (hlt : ∀ y ∈ c, y < NN)
    (hf : ∀ y ∈ c, f y = 0) (hg1 : ∀ y ∈ c, g y = 1) (hg2 : ∀ y < NN, y ∉ c → g y = f y) :
    (List.range NN).countP ztfcd + c.length =
      (List.range NN).countP ztddb := by
  classical
  rw [List.countP_eq_countP_filter_add _ ztqok
      ztzfw,
    List.countP_eq_countP_filter_add _ ztddb
      ztzfw]
  have hlen : ((List.range NN).filter fun y => decide ztdwm).length = c.length := by
    have hp : ((List.range NN).filter fun y => decide ztdwm).Perm c := by
      rw [List.perm_ext_iff_of_nodup ((List.nodup_range).filter _) hc]
      simp_all
    exact hp.length_eq
  have h1 : ((List.range NN).filter fun y => decide ztdwm).countP
      ztfcd = 0 := by
    simp_all
  have h2 : ((List.range NN).filter fun y => decide ztdwm).countP
      ztddb = c.length := by
    rw [← hlen, List.countP_eq_length]
    simp_all
  have h3 : ((List.range NN).filter fun y => !decide ztdwm).countP
      ztfcd =
      ((List.range NN).filter fun y => !decide ztdwm).countP ztddb := by
    apply List.countP_congr
    simp_all
  rw [h1, h2, h3]
  omega

/-! ### The programs -/

/-- Clear one mark: `mark[z] := 0; z := z + 1`. -/
def clearBody : Stmt := block [.addN 248 241 242, .storeN 248 243, .addN 242 242 244]

/-- Clear the mark array. -/
def clearLoop : Stmt := .whileLtN 242 240 clearBody

/-- One step around a cycle: `mark[x] := 1; m := m + 1; x := nxt[x]; t := mark[x]`. -/
def ringBody : Stmt :=
  block [.addN 248 241 246, .storeN 248 244, .addN 247 247 244, .addN 248 249 246, .loadN 246 248,
    .addN 248 241 246, .loadN 245 248]

/-- Walk around the cycle until a marked node. -/
def ringLoop : Stmt := .whileLtN 245 244 ringBody

/-- Mark the cycle of `z`, count its length `m`, and triangulate it. -/
def pieceOut : Stmt :=
  .seq (block [.addN 248 241 242, .storeN 248 244, .constN 247 1, .addN 248 249 242, .loadN 246 248,
      .addN 248 241 246, .loadN 245 248])
    (.seq ringLoop (.seq (block [.copyN 80 249, .copyN 81 250, .copyN 82 242, .copyN 83 247,
      .copyN 84 251]) pieceTriStmt))

/-- One node of the output pass: if unmarked, triangulate its cycle. -/
def outBody : Stmt :=
  .seq (block [.addN 248 241 242, .loadN 245 248])
    (.seq (.ifLtN 245 244 pieceOut .skip) (block [.addN 242 242 244]))

/-- The loop over the nodes. -/
def outLoop : Stmt := .whileLtN 242 240 outBody

/-- **The output pass.** -/
def outStmt : Stmt :=
  .seq (block [.constN 243 0, .constN 244 1, .constN 242 0])
    (.seq clearLoop (.seq (block [.constN 242 0]) outLoop))
section Ram
variable {P : Polygon} {W : ℕ}

/-- The invariant of the clearing loop. -/
def ClearInv (W MB NN : ℕ) (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ c.nreg 242 ≤ NN ∧ (∀ y < c.nreg 242, c.nmem ztbyu = 0) ∧
    (∀ r, r ≠ 242 → r ≠ 248 → c.nreg r = c₀.nreg r) ∧ c.rreg = c₀.rreg ∧
    ztfjq ∧ c.rmem = c₀.rmem ∧
    c.output = c₀.output

/-- One iteration of the mark-clearing loop. -/
theorem clearBody_inv {MB NN : ℕ} {c₀ : Config} (h240 : c₀.nreg 240 = NN)
    (h241 : c₀.nreg 241 = MB) (h243 : c₀.nreg 243 = 0) (h244 : c₀.nreg 244 = 1)
    (hW : MB + NN ≤ W) (c : Config) (hI : ClearInv W MB NN c₀ c) (ht : c.nreg 242 < c.nreg 240) :
    ∃ c' k, Exec P W clearBody c c' k ∧ ClearInv W MB NN c₀ c' ∧ k ≤ 3 ∧
      NN - c'.nreg 242 < NN - c.nreg 242 := by
  zucsw
  have e240 : c.nreg 240 = NN := by_simp_all
  have e241 : ztuny := by_simp_all
  have e243 : c.nreg 243 = 0 := by_simp_all
  have e244 : ztunz := by_simp_all
  rw [e240] at ht
  unfold clearBody
  exec_block
  · omega
  · config_simp; omega
  refine ⟨ztdrc,
    by omega, ?_⟩
  · simp_all
  · config_simp
    config_simp at hv
    rw [e244] at hv
    rw [e241, e243]
    zudi
    grind
  · simp_all
  · config_simp
    rw [e241, Machine.upd_other _ _ _ by_omega]
    simp_all
  · config_simp; omega

/-- The invariant of the walk around the cycle `d` from position `i` (`z = d[i]`), relative to
the configuration `c₀` before the cycle is marked. -/
def RingInv (W MB NN : ℕ) (d : List ℕ) (i : ℕ) (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ 1 ≤ c.nreg 247 ∧ c.nreg 247 ≤ d.length ∧
    c.nreg 246 = d.getD ((i + c.nreg 247) % d.length) 0 ∧ c.nreg 245 = c.nmem (MB + c.nreg 246) ∧
    (∀ y < NN, c.nmem ztbyu =
      if ∃ s < c.nreg 247, y = d.getD zteiz 0 then 1 else c₀.nmem ztbyu) ∧
    (∀ r, r ≠ 245 → r ≠ 246 → r ≠ 247 → r ≠ 248 → c.nreg r = c₀.nreg r) ∧ c.rreg = c₀.rreg ∧
    ztfjq ∧ c.rmem = c₀.rmem ∧
    c.output = c₀.output

/-- The node at position `(i + s) % len` of a duplicate-free cycle determines `s < len`. -/
theorem getD_cyc_inj {d : List ℕ} (hd : d.Nodup) {i s s' : ℕ} (hs : s < d.length)
    (hs' : s' < d.length) (h : d.getD zteiz 0 = d.getD ((i + s') % d.length) 0) :
    s = s' := by
  zqbbr
  have e := getD_inj_of_nodup hd ztbpn ztbpn h
  have hm := e
  exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' i hm) hs hs'

/-- One step of the walk around a cycle preserves `RingInv`. -/
theorem ringBody_inv {MB NN NB : ℕ} {S : LState} {d : List ℕ} {i : ℕ} {c₀ : Config}
    (hcyc : IsCyc S d) (_hnd : d.Nodup) (_hi : i < d.length) (hdlt : ∀ y ∈ d, y < NN)
    (hlen : d.length ≤ NN) (_hd0 : ∀ y ∈ d, c₀.nmem ztbyu = 0) (hnxt : ∀ y < NN, c₀.nmem ztjkf = S.nxt y)
    (hNB : NB + NN ≤ MB) (hW : MB + NN ≤ W)
    (h241 : c₀.nreg 241 = MB) (h244 : c₀.nreg 244 = 1) (h249 : c₀.nreg 249 = NB)
    (c : Config) (hI : RingInv W MB NN d i c₀ c) (ht : c.nreg 245 < c.nreg 244) :
    ∃ c' k, Exec P W ringBody c c' k ∧ RingInv W MB NN d i c₀ c' ∧ k ≤ 7 ∧
      d.length - c'.nreg 247 < d.length - c.nreg 247 := by
  obtain ⟨hw, hm1, hml, h246, h245, hmark, hfn, hfr, hnm, hrm, hout⟩ := hI
  zqbbr
  have e241 : ztuny := by
    grind
  have e244 : ztunz := by
    grind
  have e249 : c.nreg 249 = NB := by
    grind
  set m := c.nreg 247 with hmdef
  zqbbs
  have hxN : x < NN := by_grind
  -- the test: `x` is unmarked, so `m < len`
  have hmlt : m < d.length := by
    zucux
    have hm : m = d.length := by_omega
    have : c.nmem zttaf = 1 := by
      rw [hmark x hxN, ite_eq_left ⟨0, by_omega, by rw [hx, hm, Nat.add_zero, Nat.add_mod_right]⟩]
    grind
  have hnx : c.nmem zttal = S.nxt x := by rw [hnm _ by_omega]; grind
  have hx' : S.nxt x = d.getD (ztzwd % d.length) 0 := by
    rw [hx, (hcyc.2 _ ztbpn).1, Nat.mod_add_mod, Nat.add_assoc]
  unfold ringBody
  exec_block
  · omega
  · config_simp; omega
  · config_simp; omega
  · config_simp
    rw [e249, e241, h246, Machine.upd_other _ _ _ by_omega, hnx, hx']
    have := hdlt _ (getD_mem_of_lt (Nat.mod_lt ztzwd hl))
    omega
  refine ⟨⟨by_omega, ?_, ?_, ?_, ?_, fun y hy => ?_, fun r h1 h2 h3 h4 => ?_, hfr, fun t ht' => ?_,
    hrm, hout⟩, by_omega, ?_⟩
  · config_simp; omega
  · config_simp; omega
  · config_simp
    rw [e249, e241, h246, e244, Machine.upd_other _ _ _ by_omega, hnx, hx']
  · zqbbt
  · config_simp
    rw [e241, h246, e244]
    by_cases hyx : y = x
    · rw [hyx, Machine.upd_same, ite_eq_left by_grind]
    · rw [Machine.upd_other _ _ _ by_omega, hmark y hy]
      by_cases hex : ∃ s < m, y = d.getD zteiz 0
      · obtain ⟨s, hs, hys⟩ := hex
        rw [ite_eq_left ⟨s, hs, hys⟩, ite_eq_left ztrem]
      · zueys
        zuifu
        by_cases hsm : s = m
        · grind
        · exact hex ztrem
  · config_simp; simp only [Machine.upd_apply, h1, h2, h3, h4, ite_false]
    grind
  · config_simp
    rw [e241, h246, Machine.upd_other _ _ _ (by have := hdlt x hxd; omega)]
    grind
  · config_simp; omega

/-- The positions `(i + s) % len`, `s < len`, enumerate the cycle. -/
theorem exists_pos_iff {d : List ℕ} {i : ℕ} (hi : i < d.length) (y : ℕ) :
    (∃ s < d.length, y = d.getD zteiz 0) ↔ y ∈ d := by
  zqbbr
  constructor
  · rintro ⟨s, -, rfl⟩; exact getD_mem_of_lt (Nat.mod_lt _ hl)
  · intro hy
    obtain ⟨j, hj, rfl⟩ := exists_getD_of_mem hy
    refine ⟨ztqsb % d.length, Nat.mod_lt _ hl, ?_⟩
    rw [Nat.add_mod_mod, show i + ztqsb = j + d.length by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hj]

/-- The standing hypotheses of the output pass. -/
structure OutCtx (P Q : Polygon) (W : ℕ) (S : LState) (cs : List ztul)
    (NN MB NB VB WB : ℕ) : Prop where
  simple : Q.Simple
  shear : ∃ ε, Q = Core.shear ε P ∧ Core.YlexAgree P Q
  enum : ∃ D, Split.EnumDiags Q D ∧
    List.Perm ztghv (Split.splitAll (List.range Q.n) D)
  repr : Repr S cs
  cnt : S.cnt = NN
  lay1 : VB + NN ≤ MB
  lay2 : NB + NN ≤ MB
  lay3 : MB + NN ≤ WB
  lay4 : WB + 4 * NN ≤ W

/-- The node bands in memory. -/
def Bands (mem : ℕ → ℕ) (S : LState) (NN NB VB : ℕ) : Prop :=
  ∀ y < NN, mem zttdy = S.vtx y ∧ mem ztjkf = S.nxt y
variable {Q : Polygon}
set_option maxHeartbeats 1000000 in
/-- **Spec of one piece**: mark the cycle `d` of `z = d[i]` (unmarked), and triangulate it. -/
theorem pieceOut_exec {S : LState} {cs : List ztul} {NN MB NB VB WB : ℕ}
    (hX : OutCtx P Q W S cs NN MB NB VB WB) {d : List ℕ} (hd : d ∈ cs) {i : ℕ}
    (hi : i < d.length) (c : Config) (hc : WordsBounded W c) (hB : Bands c.nmem S NN NB VB)
    (_h240 : c.nreg 240 = NN) (h241 : c.nreg 241 = MB) (h242 : c.nreg 242 = d.getD i 0)
    (_h243 : c.nreg 243 = 0) (h244 : c.nreg 244 = 1) (h249 : c.nreg 249 = NB)
    (h250 : c.nreg 250 = VB) (h251 : c.nreg 251 = WB) (hd0 : ∀ y ∈ d, c.nmem ztbyu = 0) :
    ∃ c' k, Exec P W pieceOut c c' k ∧ k ≤ 121 * d.length + 44 ∧
      (∀ y < NN, c'.nmem ztbyu = if y ∈ d then 1 else c.nmem ztbyu) ∧
      (∃ T, WeakTriangulates (subPoly Q ztipg) T ∧
        c'.output = c.output ++ T.map (relabelList ztipg)) ∧
      (∀ r, ztgln → c'.nreg r = c.nreg r) ∧
      (∀ t, (t < MB ∨ MB + NN ≤ t) → (t < WB ∨ WB + 4 * NN ≤ t) → c'.nmem t = c.nmem t) := by
  classical
  obtain ⟨hQ, ⟨ε, hQe, hag⟩, ⟨D, hD, hp⟩, hR, hcnt, hl1, hl2, hl3, hl4⟩ := hX
  have hcyc := hR.cyc d hd
  have hnd := hR.nodup_cyc hd
  zqbbr
  have hdlt : ∀ y ∈ d, y < NN := fun y hy => hcnt ▸ hR.lt_cnt hd hy
  have hlen : d.length ≤ NN := by
    have := (List.subperm_of_subset hnd (fun y hy => List.mem_range.2 (hdlt y hy))).length_le
    simp_all
  set z := d.getD i 0 with hz
  have hzd : z ∈ d := getD_mem_of_lt hi
  have hzN : z < NN := by_simp_all
  have hx1 : S.nxt z = d.getD (ztg % d.length) 0 := by
    rw [hz, (hcyc.2 i hi).1]
  unfold pieceOut
  refine spec_seq ?_
  exec_block
  · omega
  · omega
  · config_simp; omega
  · config_simp
    zqbbq
    have := hdlt _ (getD_mem_of_lt ztzuo)
    omega
  zqbbp
  have hI₁ : RingInv W MB NN d i c c₁ := by
    refine ⟨hw₁, ?_, ?_, ?_, ?_, fun y hy => ?_, fun r h1 h2 h3 h4 => ?_, ?_, fun t ht => ?_, ?_,
      ?_⟩
    · simp_all
    · zvmxj; tauto
    · rw [hc₁]; config_simp
      zqbbq
    · simp_all
    · rw [hc₁]; config_simp
      rw [h241, h242, h244]
      by_cases hyz : y = z
      · rw [hyz, Machine.upd_same, ite_eq_left ⟨0, by_omega, by rw [Nat.add_zero, Nat.mod_eq_of_lt hi]⟩]
      · rw [Machine.upd_other _ _ _ by_omega, ite_eq_right]
        zuifu
        have : s = 0 := by_omega
        zumo
        rw [Nat.add_zero, Nat.mod_eq_of_lt hi] at hys
        omega
    · simp_all
    · zumnc
    · zvmxj; config_simp; rw [h241, h242, Machine.upd_other _ _ _ by_omega]
    · zumnc
    simp_all
  have hnxt : ∀ y < NN, c.nmem _ = S.nxt y := fun y hy => (hB y hy).2
  obtain ⟨c₂, k₂, ex₂, ⟨hw₂, hm1, hml, h246, h245, hmark, hfn₂, hfr₂, hnm₂, hrm₂, hout₂⟩, hexit₂,
    hk₂⟩ := Exec.whileLtN_bounded _ (fun d' => d.length - d'.nreg 247)
      7 ztsa (ringBody_inv hcyc hnd hi hdlt hlen hd0 hnxt hl2
        by_omega h241 h244 h249) hI₁
  unfold ringLoop
  zujfq
  have e244₂ : c₂.nreg 244 = 1 := by
    rw [hfn₂ 244 by_decide by_decide by_decide by_decide, h244]
  have hmeq : c₂.nreg 247 = d.length := by
    zuct
    have hlt : c₂.nreg 247 < d.length := by_omega
    zqbbs
    have hmx : c₂.nmem zttaf = 0 := by
      rw [hmark x by_grind, ite_eq_right, hd0 x hxd]
      rintro ⟨s, hs, hxs⟩
      have := getD_cyc_inj hnd hlt by_omega hxs
      omega
    grind
  have hmark₂ : ∀ y < NN, c₂.nmem ztbyu = if y ∈ d then 1 else c.nmem ztbyu := by
    zusy
    rw [hmark y hy, hmeq]
    by_cases h : y ∈ d
    · rw [ite_eq_left ((exists_pos_iff hi y).2 h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h ((exists_pos_iff hi y).1 h')), ite_eq_right h]
  have e242 : c₂.nreg 242 = z := by
    rw [hfn₂ 242 by_decide by_decide by_decide by_decide, h242]
  refine spec_seq ?_
  exec_block
  zubhx
  zufwv
  set l := (walk S z d.length).map S.vtx with hldef
  have hll : l.length = d.length := by rw [hldef, List.length_map, walk_eq_rotate hcyc hi,
    List.length_rotate]
  zugms
  have e80 : c₃.nreg 80 = NB := by
    zumwr; config_simp; rw [hfn₂ 249 by_decide by_decide by_decide by_decide, h249]
  have e81 : c₃.nreg 81 = VB := by
    zumwr; config_simp; rw [hfn₂ 250 by_decide by_decide by_decide by_decide, h250]
  have e82 : c₃.nreg 82 = z := by zumwr; tauto
  have e83 : c₃.nreg 83 = d.length := by zumwr; tauto
  have e84 : c₃.nreg 84 = WB := by
    zumwr; config_simp; rw [hfn₂ 251 by_decide by_decide by_decide by_decide, h251]
  have hband₃ : ∀ y < NN, c₃.nmem zttdy = S.vtx y ∧ c₃.nmem ztjkf = S.nxt y := by
    zusy
    rw [hmem₃, hnm₂ _ by_omega, hnm₂ _ by_omega]
    zulyl
  have hseq : ∀ s, nodeSeq c₃.nmem NB z s = d.getD _ 0 :=
    nodeSeq_eq_iterate hcyc (fun y hy => (hband₃ y by_grind).2) hi
  have hseqN : ∀ s, nodeSeq c₃.nmem NB z s < NN := fun s => by
    rw [hseq]; exact hdlt _ ztbahx
  have hin : PieceInput W l c₃ := by
    refine ⟨by_omega, ?_, fun s hs => ?_, fun s _ => ?_, fun s _ => ?_, fun s _ => ?_,
      fun s _ => ?_, ?_⟩ <;> (try simp only [e80, e81, e82, e84])
    · rw [hll, hseq, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
    · rw [hll] at hs
      rw [(hband₃ _ (hseqN s)).1, hseq, hldef, walk_map_getD hcyc hi hs]
    · have := hseqN s; omega
    · have := hseqN s; omega
    · have := hseqN s; omega
    · have := hseqN s; omega
    omega
  -- the piece: a mountain in `Q`, hence (transfer) in `P`
  have hpiece : IsPiece Q l := isPiece_walk hQ hD hR hp hd hi
  have hQn : ztlaf := by zuoft; exact Core.shear_n ε P
  have hmount := mountain_transfer (ε := ε) by_grind
    (fun x hx => hQn ▸ hpiece.lt x hx) (by rw [← hQe]; exact Chazelle.Mountain.piece_isMountain hQ hpiece)
  obtain ⟨c₄, k₄, ex₄, hk₄, ⟨T, hT, hout₄⟩, hfn₄, -, hnm₄, -⟩ :=
    pieceTri_exec hmount c₃ hw₃ hin
  refine ⟨c₄, k₄, ex₄, ?_, fun y hy => ?_, ⟨T, ?_, ?_⟩, fun r hr => ?_, fun t ht1 ht2 => ?_⟩
  · have e : c₁.nreg 247 = 1 := by zvmxj; config_simp
    omega
  · rw [hnm₄ _ by_omega, hmem₃, hmark₂ y hy]
  · rw [hQe, subPoly_shear]; exact weakTriangulates_shear ε hT
  · grind
  · rw [hfn₄ r by_omega, hc₃]; config_simp
    simp only [Machine.upd_apply, show r ≠ 80 by omega, show r ≠ 81 by omega,
      show r ≠ 82 by omega, show r ≠ 83 by omega, show r ≠ 84 by omega, ite_false]
    rw [hfn₂ r by_omega by_omega by_omega by_omega]
  · rw [hnm₄ _ by_omega, hmem₃, hnm₂ t ht1]
open Classical in
/-- The invariant of the output loop, relative to its entry configuration `c₀`: the cycles
`done` containing a node `< z` have been marked and triangulated, in the order of `acc`. -/
def OutInv (Q : Polygon) (W : ℕ) (S : LState) (cs : List ztul) (NN MB NB VB WB : ℕ)
    (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ c.nreg 242 ≤ NN ∧ c.nreg 240 = NN ∧ c.nreg 241 = MB ∧ c.nreg 243 = 0 ∧
    c.nreg 244 = 1 ∧ c.nreg 249 = NB ∧ c.nreg 250 = VB ∧ c.nreg 251 = WB ∧
    Bands c.nmem S NN NB VB ∧
    ∃ done : List ztul, done.Nodup ∧ (∀ d ∈ done, d ∈ cs) ∧
      (∀ d ∈ cs, d ∈ done ↔ ∃ y ∈ d, y < c.nreg 242) ∧
      (∀ y < NN, c.nmem ztbyu = if ∃ d ∈ done, y ∈ d then 1 else 0) ∧
      ∃ acc : List ztpzo,
        List.Forall₂ (fun d p => ∃ r, p.1 = (d.map S.vtx).rotate r) done acc ∧
        (∀ p ∈ acc, WeakTriangulates (subPoly Q p.1) p.2) ∧
        c.output = c₀.output ++ acc.flatMap ztmjv

/-- The potential of the output loop. -/
def outPot (NN MB : ℕ) (c : Config) : ℕ :=
  70 * (NN - c.nreg 242) + 130 * (List.range NN).countP (fun y => decide (c.nmem ztbyu = 0))
set_option maxHeartbeats 1000000 in
theorem outBody_inv {S : LState} {cs : List ztul} {NN MB NB VB WB : ℕ}
    (hX : OutCtx P Q W S cs NN MB NB VB WB) {c₀ : Config} (c : Config)
    (hI : OutInv Q W S cs NN MB NB VB WB c₀ c) (ht : c.nreg 242 < c.nreg 240) :
    ∃ c' k, Exec P W outBody c c' k ∧ OutInv Q W S cs NN MB NB VB WB c₀ c' ∧
      outPot NN MB c' + k + 2 ≤ outPot NN MB c := by
  classical
  obtain ⟨hw, hz, h240, h241, h243, h244, h249, h250, h251, hB, done, hdn, hdcs, hdiff, hmark, acc,
    hF, hT, hout⟩ := hI
  zuhxg

  rw [h240] at ht
  set z := c.nreg 242 with hzdef
  zuhzb

  unfold outBody
  refine spec_seq ?_
  exec_block
  · omega
  zqbbp
  have r1 : ∀ r, r ≠ 245 → r ≠ 248 → c₁.nreg r = c.nreg r := by
    simp_all
  have e245 : c₁.nreg 245 = c.nmem ztnmw := by zvmxj; config_simp; grind
  have hmem₁ : ztwh := by zvmxj
  by_cases hmz : ∃ d ∈ done, z ∈ d
  · -- already marked: skip
    have hm1 : c.nmem ztnmw = 1 := by_grind
    zuiuv
    refine spec_seq (spec_ifLtN_false by_omega zthkn)
    exec_block
    · grind
    refine ⟨⟨by_omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, done, hdn, hdcs, fun d hd => ?_,
      fun y hy => ?_, acc, hF, hT, ?_⟩, ?_⟩
    all_goals first
      | (config_simp; zunli; assumption)
      | skip
    · zqbbt
    · grind
    · config_simp
      rw [r1 242 by_decide by_decide, r1 244 by_decide by_decide, h244, hdiff d hd]
      constructor
      · grind
      · zuekv

        · grind
        · zugnl

          obtain ⟨d', hd', hzd'⟩ := hmz
          zujtg
          · grind
          · exact absurd hy (hR.disj zttnj hd ztvaw hzd')
    · grind
    · grind
    · unfold outPot
      config_simp
      grind
  · -- a new cycle
    have hm0 : c.nmem ztnmw = 0 := by_grind
    obtain ⟨d, hd, hzd⟩ := hR.exists_cyc (y := z) by_omega
    have hdnd : d ∉ done := by_grind
    obtain ⟨i, hi, hdi⟩ := exists_getD_of_mem hzd
    have hd0 : ∀ y ∈ d, c.nmem ztbyu = 0 := by
      zusy
      rw [hmark y ztjxp, ite_eq_right]
      rintro ⟨d', hd', hyd'⟩
      zujtg
      · grind
      · exact hR.disj hd zttnj hdd hy hyd'
    zuiuv
    refine spec_seq ztoia
    refine spec_use (pieceOut_exec hX hd hi c₁ hw₁ by_grind
      by_grind
      by_grind
      by_grind
      by_grind
      by_omega
      by_grind
      by_grind
      by_grind
      ztqol) ?_
    rintro c₂ k₂ hk₂ hw₂ ⟨hmark₂, ⟨T, hT₂, hout₂⟩, hfn₂, hnm₂⟩
    have R2 : ∀ r, ztgln → c₂.nreg r = c.nreg r := by
      intro r hr; grind
    exec_block
    · grind
    have hlenN : d.length ≤ NN := by
      have := (List.subperm_of_subset ztvtq
        (fun y hy => List.mem_range.2 ztjxp)).length_le
      grind
    have hcntm := countP_mark
      (g := fun y => c₂.nmem _) ztvtq
      (fun y hy => hcnt ▸ hR.lt_cnt hd hy) hd0
      (fun y hy => by rw [hmark₂ y ztjxp, ite_eq_left hy])
      (fun y hy hyd => by_grind)
    refine ⟨⟨by_omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, done ++ [d], ?_, ?_, fun d' hd' => ?_,
      fun y hy => ?_, acc ++ [((walk S (d.getD i 0) d.length).map S.vtx, T)], ?_, ?_, ?_⟩, ?_⟩
    · zqbbt
    · zqbbt
    · zqbbt
    · zqbbt
    · zqbbt
    · zqbbt
    · zqbbt
    · zqbbt
    · config_simp
      zusy
      rw [hnm₂ _ (Or.inl (by have := hX.lay1; omega)) (Or.inl (by have := hX.lay1; omega)),
        hnm₂ _ (Or.inl (by have := hX.lay2; omega)) (Or.inl (by have := hX.lay2; omega)), hmem₁]
      zulyl
    · exact List.nodup_append.2 ⟨hdn, List.nodup_singleton _, fun a ha b hb => by
        grind⟩
    · intro d' hd'
      zujck
      · grind
      grind
    · config_simp
      rw [R2 242 by_omega, R2 244 by_omega, h244, List.mem_append, List.mem_singleton,
        hdiff d' hd']
      constructor
      · rintro (⟨y, hy, hyz⟩ | rfl)
        · grind
        grind
      · zuekv

        · grind
        · right
          zugnl

          by_contra hdd
          exact hR.disj hd hd' ztvaw hzd hy
    · config_simp
      rw [hmark₂ y hy, hmem₁, hmark y hy]
      by_cases hyd : y ∈ d
      · rw [ite_eq_left hyd, ite_eq_left ⟨d, by_grind, hyd⟩]
      · rw [ite_eq_right hyd]
        zucr
        apply propext
        constructor
        · grind
        · rintro ⟨d', hd', hy'⟩
          zujck
          · grind
          grind
    · refine List.rel_append hF (List.Forall₂.cons ⟨i, ?_⟩ List.Forall₂.nil)
      rw [walk_eq_rotate (hR.cyc d hd) hi, List.map_rotate]
    · zuda
      rcases List.mem_append.1 hp with h | h
      · grind
      grind
    · config_simp
      rw [hout₂, hc₁]; config_simp
      rw [hout, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    · unfold outPot
      config_simp
      rw [R2 242 by_omega, R2 244 by_omega, h244]
      omega
set_option maxHeartbeats 1000000 in
/-- **Spec of the output pass**: from a configuration holding the final structure (`Bands`) with
the output-pass registers set, `outStmt` appends a triangulation `X` of `Q` to the output, at cost
`≤ 205 NN + 10`. -/
theorem outStmt_exec {S : LState} {cs : List ztul} {NN MB NB VB WB : ℕ}
    (hX : OutCtx P Q W S cs NN MB NB VB WB) (c : Config) (hc : WordsBounded W c)
    (hB : Bands c.nmem S NN NB VB) (h240 : c.nreg 240 = NN) (h241 : c.nreg 241 = MB)
    (h249 : c.nreg 249 = NB) (h250 : c.nreg 250 = VB) (h251 : c.nreg 251 = WB) (hW1 : 1 ≤ W) :
    ∃ c' k, Exec P W outStmt c c' k ∧ k ≤ 205 * NN + 10 ∧
      ∃ X, Q.Triangulates X ∧ c'.output = c.output ++ X := by
  classical
  zuhxg

  have hl1 := hX.lay1
  have hl2 := hX.lay2
  zuhzb

  unfold outStmt
  refine spec_seq ?_
  exec_block
  · omega
  · omega
  · omega
  zqbbp
  have r1 : ∀ r, r ≠ 242 → r ≠ 243 → r ≠ 244 → c₁.nreg r = c.nreg r := by
    simp_all
  have c243 : c₁.nreg 243 = 0 := by_simp_all
  have c244 : c₁.nreg 244 = 1 := by_simp_all
  have hCI : ClearInv W MB NN c₁ c₁ := ⟨hw₁, by_simp_all,
    by simp_all, by_omega, rfl,
    by omega, rfl, rfl⟩
  obtain ⟨c₂, k₂, ex₂, ⟨hw₂, hz₂, hzero, hfn₂, hfr₂, hnm₂, hrm₂, hout₂⟩, hexit₂, hk₂⟩ :=
    Exec.whileLtN_bounded _ (fun d => NN - d.nreg 242) 3
      ztsa (clearBody_inv by_simp_all by_simp_all c243 c244
        by_omega) hCI
  unfold clearLoop
  zujfq
  have e242₂ : c₂.nreg 242 = NN := by
    grind
  refine spec_seq ?_
  exec_block
  · omega
  zubhx
  zukgu
  have r3 : ∀ r, r ≠ 242 → r ≠ 248 → c₃.nreg r = c₁.nreg r := by
    simp_all
  have hI₀ : OutInv Q W S cs NN MB NB VB WB c₃ c₃ := by
    refine ⟨hw₃, by_simp_all, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, [],
      List.nodup_nil, by_simp_all, fun d hd => ?_, fun y hy => ?_, [],
      List.Forall₂.nil, by_simp_all, by_simp⟩
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · zusy
      zugku
      rw [e, hnm₂ _ by_omega, hnm₂ _ by_omega]
      have e1 : ztwh := by zvmxj
      zvmxy; exact hB y hy
    · have e : c₃.nreg 242 = 0 := by_simp_all
      grind
    · zugku
      grind
  obtain ⟨c₄, k₄, ex₄, ⟨hw₄, hz₄, h240₄, -, -, -, -, -, -, -, done, hdn, hdcs, hdiff, -, acc, hF,
    hT, hout₄⟩, hexit₄, hk₄⟩ := Exec.whileLtN_potential
      _ _ ztsa
      (outBody_inv hX) hI₀
  unfold outLoop
  refine ⟨c₄, k₄, ex₄, ?_, ?_⟩
  · have hpot : outPot NN MB c₃ ≤ 200 * NN := by
      unfold outPot
      have := List.countP_le_length (p := fun y => decide (c₃.nmem ztbyu = 0))
        (l := List.range NN)
      grind
    omega
  · -- all cycles are done
    have e242₄ : c₄.nreg 242 = NN := by_omega
    have hall : ∀ d ∈ cs, d ∈ done := by
      zuip
      rw [hdiff d hd, e242₄]
      obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil d (hR.cyc d hd).1
      exact ⟨y, hy, hcnt ▸ hR.lt_cnt hd hy⟩
    have hperm : done.Perm cs := by
      rw [List.perm_ext_iff_of_nodup hdn hR.nodup_cs]
      grind
    obtain ⟨D, hD, hp⟩ := hX.enum
    have hrot : List.Forall₂ ztjwc (done.map (List.map S.vtx))
        acc := by
      rw [List.forall₂_map_left_iff]
      exact hF
    refine ⟨_, triangulates_of_pairs hX.simple hD by_grind hrot hT, ?_⟩
    grind
end Ram
end
end Chazelle.Final
end
namespace Chazelle.Final
open Machine Machine.Stmt Programs
open Chazelle.EarClip (detInto detInto_exec)
open Chazelle.Mountain (ylexLT ylexLE orient)
open Chazelle.Core (shear shear_vtx det_shearPt ShearRel YlexAgree)
@[expose] public section
def orMinBody : Stmt :=
  .seq (block [.readX 230 232, .readY 231 232, .readX 232 231, .readY 233 231])
    (.seq ztibu (.instr (.addN 232 232 233)))

/-- The minimum scan over `i = 1 … n - 1`. -/
def orMinLoop : Stmt := .whileLtN 232 230 orMinBody

/-- `prev := (best + n - 1) % n`, `next := (best + 1) % n`, the corner determinant into
`rreg 240`, and the sign into `rreg 100`. -/
def orSign : Stmt :=
  .seq (block [.constN 235 0])
    (.seq (.ifLtN 235 231 ztnbq ztnbp)
      (.seq (block [.addN 236 231 233])
        (.seq ztipr
          (.seq (block [.readX 234 234, .readY 235 234, .readX 236 231, .readY 237 231,
              .readX 238 236, .readY 239 236])
            (.seq (detInto 240 241 242 234 235 236 237 238 239)
              (.seq (block [.constR 100 (-1), .constR 243 0])
                (.ifLtR 243 240 (.instr (.constR 100 1)) .skip)))))))

/-- **The orientation program.** -/
def orientStmt : Stmt :=
  .seq (block [.inputSize 230, .constN 231 0, .constN 232 1, .constN 233 1])
    (.seq orMinLoop orSign)
section Orient
variable {P : Polygon} {W : ℕ}

/-- The invariant of the minimum scan. -/
def OrInv (P : Polygon) (W : ℕ) (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ 1 ≤ c.nreg 232 ∧ c.nreg 232 ≤ P.n ∧ c.nreg 231 < c.nreg 232 ∧
    c.nreg 230 = P.n ∧ c.nreg 233 = 1 ∧
    (∀ i < c.nreg 232, ¬ ylexLT ztdn ztqbi) ∧
    (∀ r, (r < 231 ∨ 232 < r) → c.nreg r = c₀.nreg r) ∧
    (∀ r, (r < 230 ∨ 233 < r) → c.rreg r = c₀.rreg r) ∧
    c.nmem = c₀.nmem ∧ c.rmem = c₀.rmem ∧ c.output = c₀.output

/-- One iteration of the minimum scan preserves `OrInv`. -/
theorem orMinBody_inv {c₀ c : Config} (hI : OrInv P W c₀ c) (ht : c.nreg 232 < c.nreg 230) :
    ∃ c' k, Exec P W orMinBody c c' k ∧ OrInv P W c₀ c' ∧ k ≤ 12 ∧
      P.n - c'.nreg 232 < P.n - c.nreg 232 := by
  classical
  obtain ⟨hw, h1, hle, hlt, h230, h233, hmin, hfn, hfr, hnm, hrm, hout⟩ := hI
  rw [h230] at ht
  unfold orMinBody
  refine spec_seq ?_
  exec_block
  zuzr
  zufwu
  have e1 : c₁.nreg = c.nreg := by zvmxj
  have ex : (c₁.rreg 230, c₁.rreg 231) = P.vtx ztvib := by_simp_all
  have ey : (c₁.rreg 232, c₁.rreg 233) = P.vtx (c.nreg 231) := by_simp_all
  have hupd : ∃ c₂ k₂, Exec P W ztibu c₁ c₂ k₂ ∧
      k₂ ≤ 1 + 6 ∧ (c₂.nreg 231 = if ylexLT (P.vtx ztvib) ztqbi
        then c.nreg 232 else c.nreg 231) ∧ (∀ r, r ≠ 231 → c₂.nreg r = c.nreg r) ∧
        c₂.rreg = c₁.rreg ∧ c₂.nmem = c₁.nmem ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    refine ylexTest_exec c₁ ztep ztep
    · zuihw
      refine ⟨_, 1, Exec.copyN hw₁ 231 232, le_rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
      · simp_all
      simp_all
    · zuihw
      refine ⟨c₁, 0, Exec.skip hw₁, by_omega, ?_, by_simp_all, rfl, rfl, rfl, rfl⟩
      simp_all
  refine spec_seq (spec_use hupd ?_)
  rintro c₂ k₂ hk₂ hw₂ ⟨h231, hfn₂, hfr₂, hnm₂, hrm₂, hout₂⟩
  have e232 : c₂.nreg 232 = c.nreg 232 := by_grind
  have e233 : c₂.nreg 233 = 1 := by_grind
  refine spec_instr (Exec.addN hw₂ 232 232 233 (by rw [e232, e233]; have := hw.1 230; omega))
    fun hw₃ => ?_
  refine ⟨⟨hw₃, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_⟩,
    by omega, ?_⟩
  · config_simp; omega
  · config_simp; omega
  · config_simp; grind
  · config_simp; grind
  · tauto
  · config_simp at hi
    rw [e232, e233] at hi
    config_simp
    rw [h231]
    split_ifs with hy
    · zuhgj
      by_cases hic : i = c.nreg 232
      · subst hic; exact Chazelle.Mountain.ylexLT_irrefl _ h'
      · exact hmin i by_omega (Chazelle.Mountain.ylexLT_trans h' hy)
    grind
  · config_simp
    rw [Machine.upd_other _ _ _ by_omega, hfn₂ r by_omega]
    grind
  · config_simp
    rw [hfr₂, hc₁]; config_simp
    rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
      Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega]
    grind
  · grind
  · grind
  · grind
  · config_simp; omega

/-- **Spec of the orientation program**: with `Q` simple and related to `P` by a shear, cost
`≤ 14 n + 45`, and `rreg 100 = orient Q`; only the natural registers `230 … 236` and the real
registers `100`, `230 … 243` change. -/
theorem orientStmt_exec {Q : Polygon} (hPQ : ShearRel P Q) (hQ : Q.Simple) (c : Config)
    (hc : WordsBounded W c) (hW : P.n ≤ W) :
    ∃ c' k, Exec P W orientStmt c c' k ∧ k ≤ 14 * P.n + 45 ∧ c'.rreg 100 = orient Q ∧
      (∀ r, zthjv → c'.nreg r = c.nreg r) ∧
      (∀ r, r ≠ 100 → ztofq → c'.rreg r = c.rreg r) ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨ε, -, hQe, hag⟩ := hPQ
  zudov
  have hQn : ztlaf := by zuoft; exact Chazelle.Core.shear_n ε P
  have hn : ztgah := by_omega
  unfold orientStmt
  refine spec_seq ?_
  exec_block
  · zugkh
  · omega
  · omega
  · omega
  zuzr
  have hI₀ : OrInv P W c₁ c₁ := by
    refine ⟨by_simp_all, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, by_omega,
      by simp_all, rfl, rfl, rfl⟩
    · simp_all
    · rw [hc₁]; config_simp; omega
    · simp_all
    · simp_all
    · simp_all
    · zvmxj at hi ⊢; config_simp at hi; config_simp
      zudgv
      zumo
      exact Chazelle.Mountain.ylexLT_irrefl _
  obtain ⟨c₂, k₂, ex₂, ⟨hw₂, -, hle₂, hlt₂, h230₂, h233₂, hmin₂, hfn₂, hfr₂, hnm₂, hrm₂, hout₂⟩,
    hexit₂, hk₂⟩ := Exec.whileLtN_bounded (P := P) (OrInv P W c₁) (fun d => P.n - d.nreg 232) 12
      ztsa (fun d hd ht => orMinBody_inv hd ht) hI₀
  unfold orMinLoop
  zujfq
  rw [h230₂] at hexit₂
  have e232 : c₂.nreg 232 = P.n := by_omega
  set k := c₂.nreg 231 with hk
  have hkn : k < P.n := by_omega
  have hminP : ∀ i < P.n, ¬ ylexLT _ _ := fun i hi => hmin₂ i by_omega
  -- the sign
  unfold orSign
  refine spec_seq ?_
  exec_block
  · omega
  zubhx
  zukgu
  have r3 : ∀ r, r ≠ 235 → c₃.nreg r = c₂.nreg r := by
    simp_all
  have hprev : ∃ c₄ k₄, Exec P W (.ifLtN 235 231 ztnbq
      ztnbp) c₃ c₄ k₄ ∧ k₄ ≤ 3 ∧
      c₄.nreg 234 = ztjze % P.n ∧ (∀ r, r ≠ 234 → c₄.nreg r = c₃.nreg r) ∧
      c₄.rreg = c₃.rreg ∧ c₄.nmem = c₃.nmem ∧ c₄.rmem = c₃.rmem ∧ c₄.output = c₃.output := by
    have e235 : c₃.nreg 235 = 0 := by_simp_all
    by_cases hk0 : 0 < k
    · refine spec_ifLtN_true by_simp_all
        (spec_instr (Exec.subN hw₃ 234 231 233) fun _ => ?_)
      refine ⟨by_omega, ?_, by_simp_all, rfl, rfl, rfl, rfl⟩
      config_simp
      rw [r3 231 by_decide, r3 233 by_decide, h233₂, ← hk,
        show k + P.n - 1 = ztie + P.n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
    · refine spec_ifLtN_false by_simp_all
        (spec_instr (Exec.subN hw₃ 234 230 233) fun _ => ?_)
      refine ztcfp
      config_simp
      rw [r3 230 by_decide, r3 233 by_decide, h233₂, h230₂,
        show k = 0 by omega, Nat.zero_add, Nat.mod_eq_of_lt by_omega]
  refine spec_seq (spec_use hprev ?_)
  rintro c₄ k₄ hk₄ hw₄ ⟨h234, hfn₄, hfr₄, hnm₄, hrm₄, hout₄⟩
  have r4 : ∀ r, r ≠ 234 → r ≠ 235 → c₄.nreg r = c₂.nreg r := by_grind
  refine spec_seq ?_
  exec_block
  · grind
  zuecc

  have hnext : ∃ c₆ k₆, Exec P W ztipr c₅ c₆ k₆ ∧
      k₆ ≤ 3 ∧ c₆.nreg 236 = zts % P.n ∧ (∀ r, r ≠ 236 → c₆.nreg r = c₅.nreg r) ∧
      c₆.rreg = c₅.rreg ∧ c₆.nmem = c₅.nmem ∧ c₆.rmem = c₅.rmem ∧ c₆.output = c₅.output := by
    have e236 : c₅.nreg 236 = k + 1 := by
      rw [hc₅]; config_simp; grind
    have e230 : c₅.nreg 230 = P.n := by
      rw [hc₅]; config_simp; grind
    by_cases hk1 : k + 1 < P.n
    · refine spec_ifLtN_true by_omega ztoid
      exact ⟨by_omega, by rw [e236, Nat.mod_eq_of_lt hk1], by_omega, rfl, rfl, rfl, rfl⟩
    · refine spec_ifLtN_false by_omega
        (spec_instr (Exec.constN hw₅ 236 0 ztbg) fun _ => ?_)
      refine ztcfp
      config_simp
      rw [show k + 1 = P.n by omega, Nat.mod_self]
  refine spec_seq (spec_use hnext ?_)
  rintro c₆ k₆ hk₆ hw₆ ⟨h236, hfn₆, hfr₆, hnm₆, hrm₆, hout₆⟩
  have e234₆ : c₆.nreg 234 = ztjze % P.n := by
    rw [hfn₆ 234 by_decide, hc₅]; tauto
  have e231₆ : c₆.nreg 231 = k := by
    rw [hfn₆ 231 by_decide, hc₅]; config_simp; rw [r4 231 by_decide by_decide]
  refine spec_seq ?_
  exec_block
  refine spec_name fun c₇ hc₇ => ?_
  have hw₇ : WordsBounded W c₇ := by_grind
  refine spec_seq (spec_use (detInto_exec 240 241 242 234 235 236 237 238 239
    by_decide by_decide by_decide
    ztjwk c₇ hw₇) ?_)
  rintro c₈ k₈ hk₈ hw₈ ⟨hdet, hfr₈, hn₈, hnm₈, hrm₈, hout₈⟩
  have hdetv : c₈.rreg 240 = det ztbtp ztjr
      ztwiw := by
    rw [hdet, hc₇]; config_simp; grind
  refine spec_seq ?_
  exec_block
  refine spec_name fun c₉ hc₉ => ?_
  have hw₉ : WordsBounded W c₉ := by_grind
  have e243 : c₉.rreg 243 = 0 := by zungz; simp
  have e240 : c₉.rreg 240 = c₈.rreg 240 := by zungz; config_simp
  -- the orientation of `Q`
  have hkQ : ztsjy := by_omega
  have hminQ : ∀ i < Q.n, ylexLE ztbda ztdli := by
    zug
    have h1 : ¬ ylexLT _ _ := fun h =>
      hminP i by_omega ((hag i k by_omega by_omega).2 h)
    rcases Chazelle.Mountain.ylexLT_trichotomy ztbda ztdli with h | h | h
    · exact Chazelle.Mountain.ylexLE_of_ylexLT h
    · zvmwc; exact Chazelle.Mountain.ylexLE_refl _
    grind
  have hdetQ : det (Q.vtx ((k + Q.n - 1) % Q.n)) ztbda ztwoh =
      det ztbtp ztjr ztwiw := by
    rw [hQn, hQe, shear_vtx, shear_vtx, shear_vtx, det_shearPt]
  have hor := orient_eq_of_ylexMin hQ hkQ hminQ (by rw [hdetQ])
  have hfr_all : ∀ r, r ≠ 100 → ztofq → c₉.rreg r = c.rreg r := by
    intro r h100 hr
    zungz; config_simp
    rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ h100,
      hfr₈ r by_omega by_omega by_omega, hc₇]
    config_simp
    rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
      Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
      Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega, hfr₆, hc₅]
    config_simp
    rw [hfr₄, hc₃]
    config_simp
    rw [hfr₂ r by_omega, hc₁]
  have hfn_all : ∀ r, zthjv → c₉.nreg r = c.nreg r := by
    zuz
    zungz; config_simp; rw [hn₈, hc₇]; config_simp
    rw [hfn₆ r by_omega, hc₅]; config_simp
    rw [Machine.upd_other _ _ _ by_omega, r4 r by_omega by_omega, hfn₂ r by_omega, hc₁]
    config_simp
    rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
      Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega]
  have hmem9 : c₉.nmem = c.nmem := by
    grind
  have hrm9 : c₉.rmem = c.rmem := by
    grind
  have hout9 : c₉.output = c.output := by
    grind
  have hk₂' : k₂ ≤ 14 * P.n := by
    have e : c₁.nreg 232 = 1 := by zvmxj; config_simp
    omega
  by_cases hpos : 0 < det ztbtp ztjr ztwiw
  · refine spec_ifLtR_true by_grind
      (spec_instr (Exec.constR hw₉ 100 1) fun _ => ?_)
    refine ⟨by_omega, ?_, fun r hr => ?_, fun r h1 hr => ?_, ?_, ?_, ?_⟩
    · config_simp; grind
    · config_simp; exact hfn_all r hr
    · config_simp; rw [Machine.upd_other _ _ _ h1]; exact hfr_all r h1 hr
    · omega
    · omega
    omega
  · refine spec_ifLtR_false by_grind (spec_skip hw₉ ?_)
    refine ⟨by_omega, ?_, hfn_all, hfr_all, hmem9, hrm9, hout9⟩
    rw [hor, ite_eq_right hpos, hc₉]; simp
end Orient
end
end Chazelle.Final
namespace Chazelle.Final
open Machine Machine.Stmt Programs
open Chazelle.Split (EnumDiags)
open Chazelle.Mountain (orient)
@[expose] public section
def finalStmt : Stmt :=
  .seq (block [.inputSize 252, .addN 253 9991 9993, .copyN 200 9999, .addN 201 200 253,
      .addN 201 201 253, .addN 202 201 252])
    (.seq diagStmt (.seq orientStmt
      (.seq (block [.addN 100 202 253, .copyN 101 200, .copyN 102 206])
        (.seq splitStmt
          (.seq (block [.copyN 240 115, .addN 241 109 252, .copyN 249 106, .copyN 250 105,
            .addN 251 241 240]) outStmt)))))

/-- Enumerations of the inserted diagonals are closed under permutation. -/
theorem EnumDiags.perm {Q : Polygon} {D D' : List ztw} (h : EnumDiags Q D)
    (hp : D.Perm D') : EnumDiags Q D' where
  sound d hd := h.sound d (hp.mem_iff.2 hd)
  complete d hd := by
    rcases h.complete d hd with h1 | h1
    · grind
    grind
  distinct := hp.pairwise h.distinct fun {a b} hab =>
    ⟨fun e => hab.1 e.symm, fun e => hab.2 by_simp_all⟩

/-- The final-stage input is no longer than the two tables together. -/
theorem diagList_length_le_tables (Q : Polygon) (T : TrapTable) (C : List ChordRec) :
    (diagList Q T C).length ≤ T.length + C.length := by
  unfold diagList
  have h1 := (List.dedup_sublist ((trapPairs Q T ++ chordPairs C).map sortPair)).length_le
  have h2 : ztoqf := by
    zumvh
  zuivk
  grind
set_option maxHeartbeats 4000000 in
/-- **The final stage** (`Chazelle.Core.FinalStageSpec`): from any configuration holding valid
tables of a simple polygon `Q` related to the input `P` by a shear, `finalStmt` emits a
triangulation of `Q` in at most `10000 (n + 1)` steps, using the memory `[A, A + 100 (n + 1))`
above the allocator `A`. -/
theorem finalStage : Core.FinalStageSpec := by
  classical
  refine ⟨finalStmt, 10000, 100, ?_⟩
  intro P Q hP hQ hPQ W c hc hready hroom
  obtain ⟨T, Cs, hT, hC, h9991, hTab, h9993, hCab, hTB, hCB, hout0⟩ := hready
  have hPQ' := hPQ
  obtain ⟨ε, -, hQe, hag⟩ := hPQ'
  have hQn : ztlaf := hPQ.n_eq
  have hn3 : ztgah := hQn ▸ hQ.1
  have hTL : T.length ≤ 2 * P.n + 1 := hQn ▸ hT.length_le hQ
  have hCL : Cs.length ≤ 2 * P.n := hQn ▸ hC.length_le
  set A := c.nreg Core.ALLOC with hA
  set M := T.length + Cs.length with hM
  change c.nreg 9991 = T.length at h9991
  change c.nreg 9993 = Cs.length at h9993
  change Core.TrapTableAt c.nmem ztvjf T at hTab
  change Core.ChordTableAt c.nmem ztvjg Cs at hCab
  change c.nreg 9990 + 4 * T.length ≤ c.nreg 9999 at hTB
  change c.nreg 9992 + 3 * Cs.length ≤ c.nreg 9999 at hCB
  zufti
  have hW : A + 100 * ztju ≤ W := hroom
  have hML : M ≤ 4 * P.n + 1 := by_omega
  -- 1. the layout
  unfold finalStmt
  refine spec_seq ?_
  exec_block
  · omega
  · config_simp; omega
  · config_simp; omega
  · config_simp; omega
  · config_simp; omega
  zuzr
  zufwu
  have r1 : ∀ r, r ≠ 200 → r ≠ 201 → r ≠ 202 → r ≠ 252 → r ≠ 253 → c₁.nreg r = c.nreg r := by
    simp_all
  have c200 : c₁.nreg 200 = A := by_simp_all
  have c201 : c₁.nreg 201 = A + 2 * M := by
    rw [hc₁]; config_simp; omega
  have c202 : c₁.nreg 202 = A + 2 * M + P.n := by
    simp_all
  have c252 : c₁.nreg 252 = P.n := by_simp_all
  have c253 : c₁.nreg 253 = M := by_simp_all
  zucwy
  -- 2. the diagonal list
  refine spec_seq (spec_use (diagStmt_exec (P := P) (Q := Q) (W := W) hQ hQn hT hC
    (DB := A) (HB := A + 2 * M) (SB := A + 2 * M + P.n) (M := M) c₁ hw₁ c200 c201 c202
    by_simp_all
    by_simp_all
    by_simp_all
    by_simp_all
    by_simp_all
    by_simp_all
    le_rfl le_rfl by_omega le_rfl by_omega) ?_)
  rintro c₂ k₂ hk₂ hw₂ ⟨E, hE, h206, hband, hfn₂, hfr₂, hnm₂, hrm₂, hout₂⟩
  have hED : EnumDiags Q E := EnumDiags.perm (enumDiags_diagList hQ hT hC) hE.symm
  have hElen : E.length ≤ M := hE.length_eq ▸ diagList_length_le_tables Q T Cs
  have hElen' : E.length ≤ 4 * P.n + 1 := hQn ▸ (hE.length_eq ▸ diagList_length_le hQ hT hC)
  have hElt : ∀ d ∈ E, d.1 < P.n ∧ d.2 < P.n ∧ d.1 ≠ d.2 := by
    zuip
    have := diagList_lt hQ hT hC (hE.mem_iff.1 hd)
    omega
  set ND := E.length with hND
  set NN := P.n + 2 * ND with hNN
  set B := A + 2 * M + P.n + M with hB
  -- 3. the orientation
  refine spec_seq (spec_use (orientStmt_exec (P := P) (W := W) hPQ hQ c₂ hw₂ by_omega) ?_)
  rintro c₃ k₃ hk₃ hw₃ ⟨hσ₃, hfn₃, hfr₃, hnm₃, hrm₃, hout₃⟩
  have R3 : ∀ r, ztofm → zthjv → c₃.nreg r = c₁.nreg r := by
    grind
  -- 4. the splitting registers
  refine spec_seq ?_
  exec_block
  · grind
  refine spec_name fun c₄ hc₄ => ?_
  have hw₄ : WordsBounded W c₄ := by_grind
  have c4_100 : c₄.nreg 100 = B := by
    rw [hc₄]; config_simp; grind
  have c4_101 : c₄.nreg 101 = A := by
    rw [hc₄]; config_simp; grind
  have c4_102 : c₄.nreg 102 = ND := by
    rw [hc₄]; config_simp; grind
  have c4σ : c₄.rreg 100 = orient Q := by zunbf; omega
  have m4 : c₄.nmem = c₂.nmem := by_grind
  -- 5. the splitting
  have hband₄ : ∀ j < ND, c₄.nmem (A + 2 * j) = (E.getD j ztdr).1 ∧
      c₄.nmem (A + 2 * j + 1) = (E.getD j ztdr).2 := by
    grind
  refine spec_seq (spec_use (splitStmt_exec (P := P) (W := W) (B := B) (DB := A) (ND := ND)
    (NN := NN) (σ := orient Q) (D := E) c₄ hw₄ c4_100 c4_101 c4_102 c4σ rfl rfl hElt by_omega
    hband₄ ztec by_omega by_omega) ?_)
  rintro c₅ k₅ hk₅ hw₅ ⟨hS₅, h115, hfn₅, hfr₅, hnm₅, hrm₅, hout₅⟩
  -- 6. the output registers
  have e252 : c₅.nreg 252 = P.n := by
    rw [hfn₅ 252 by_omega, hc₄]; config_simp
    rw [R3 252 by_omega by_omega, c252]
  refine spec_seq ?_
  exec_block
  · config_simp; zuopt; omega
  · config_simp; zuoce; omega
  refine spec_name fun c₆ hc₆ => ?_
  have hw₆ : WordsBounded W c₆ := by_grind
  -- the structure and its cycles (for `Q`)
  set S := runState P ztgld zteag E with hSdef
  obtain ⟨cs, hR, hp⟩ := runState_spec hQ hED
  have hSQ : runState Q ztgld (initState Q.n) E = S := by
    rw [hSdef, hQn, hQe, runState_shear]
  rw [hSQ] at hR hp
  have hcnt : S.cnt = NN := by
    rw [hSdef, cnt_runState]; rfl
  have hX : OutCtx P Q W S cs NN (B + 4 * NN + P.n) ztsvc B (B + 4 * NN + P.n + NN) :=
    { simple := hQ
      shear := ⟨ε, hQe, hag⟩
      enum := ⟨E, hED, hp⟩
      repr := hR
      cnt := hcnt
      lay1 := by_omega
      lay2 := by_omega
      lay3 := by_omega
      lay4 := by_omega }
  have m6 : ztlar := by zumys
  have hBands : Bands c₆.nmem S NN ztsvc B := by
    zusy
    zupcb
    exact ⟨hS₅.mem.vtx y by_omega, hS₅.mem.nxt y by_omega⟩
  refine spec_use (outStmt_exec (P := P) (W := W) hX c₆ hw₆ hBands
    (by zumys; tauto)
    (by zumys; config_simp; zuopt)
    (by zumys; config_simp; exact hS₅.r106)
    (by zumys; config_simp; exact hS₅.r105)
    (by zumys; config_simp; zuoce) by_omega) ?_
  rintro c₇ k₇ hk₇ hw₇ ⟨X, hX7, hout₇⟩
  zujx
  · -- the cost
    have hrc : runCost P ztgld zteag E ≤ 2 * 11 * E.length := by
      refine runCost_le E zteag (fun d hd => (hElt d hd).2.2) fun v => ?_
      have h1 := length_cop_init P.n v
      have h2 := countP_diagList_le hQ hT hC v
      rw [← hE.countP_eq] at h2
      omega
    have hk₂' : k₂ ≤ 202 * T.length + 174 * Cs.length + 5 * P.n + 20 := hk₂
    nlinarith
  · grind
end
end Chazelle.Final
namespace Chazelle.Core
namespace DrvT
open Machine Machine.Stmt Programs BuildRam
@[expose] public section
def saveN : Stmt := block [.copyN 190230 230, .copyN 190231 231, .copyN 190232 232,
  .copyN 190233 233, .copyN 190234 234, .copyN 190235 235, .copyN 190236 236]

/-- Save the real registers `100`, `230 … 243`. -/
def saveR : Stmt := block [.copyR 190100 100, .copyR 190230 230, .copyR 190231 231,
  .copyR 190232 232, .copyR 190233 233, .copyR 190234 234, .copyR 190235 235,
  .copyR 190236 236, .copyR 190237 237, .copyR 190238 238, .copyR 190239 239,
  .copyR 190240 240, .copyR 190241 241, .copyR 190242 242, .copyR 190243 243]

/-- Restore the natural registers. -/
def restN : Stmt := block [.copyN 230 190230, .copyN 231 190231, .copyN 232 190232,
  .copyN 233 190233, .copyN 234 190234, .copyN 235 190235, .copyN 236 190236]

/-- Restore the real registers. -/
def restR : Stmt := block [.copyR 100 190100, .copyR 230 190230, .copyR 231 190231,
  .copyR 232 190232, .copyR 233 190233, .copyR 234 190234, .copyR 235 190235,
  .copyR 236 190236, .copyR 237 190237, .copyR 238 190238, .copyR 239 190239,
  .copyR 240 190240, .copyR 241 190241, .copyR 242 190242, .copyR 243 190243]

/-- The bit: `190001 := (0 < orient Q)`. -/
def bitO : Stmt := .seq (block [.constR 190300 0, .constN 190001 0])
  (.ifLtR 190300 100 (.instr (.constN 190001 1)) .skip)

/-- **The `LeftInside` bit** into register `190001`. -/
def orientT : Stmt :=
  .seq saveN (.seq saveR (.seq Final.orientStmt (.seq bitO (.seq restN restR))))

/-- The registers of band `19`. -/
def B19 (r : ℕ) : Bool := decide (190000 ≤ r ∧ r < 200000)

/-- The registers of the bit. -/
def Bbit (r : ℕ) : Bool := decide (r = 190001 ∨ r = 190300)

/-- The natural registers restored. -/
def BrN (r : ℕ) : Bool := decide (230 ≤ r ∧ r ≤ 236)

/-- The real registers restored. -/
def BrR (r : ℕ) : Bool := decide (r = 100 ∨ ztnfz)
theorem wrM_saveN : wrM B19 saveN = true := by_decide
theorem wrM_saveR : wrM B19 saveR = true := by_decide
theorem wrM_bitO : wrM Bbit bitO = true := by_decide
theorem wrM_restN : wrM BrN restN = true := by_decide
theorem wrM_restR : wrM BrR restR = true := by_decide
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 2000000 in
theorem saveN_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W saveN c c' k ∧ k = 7 ∧
      ztxil ∧
      FrameM B19 c c' ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem := by
  obtain ⟨c', k, e, hk, h1, h2, hm⟩ : ∃ c' k, Exec P W saveN c c' k ∧ k = 7 ∧
      ztxil ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem := by
    unfold saveN
    exec_block
    refine ztiwn
    interval_cases i <;> config_simp
  exact ⟨c', k, e, hk, h1, exec_frameM e wrM_saveN, h2, hm⟩
set_option maxHeartbeats 2000000 in
theorem saveR_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W saveR c c' k ∧ k = 15 ∧
      ztybn ∧
      FrameM B19 c c' ∧ c'.nreg = c.nreg ∧ c'.nmem = c.nmem := by
  obtain ⟨c', k, e, hk, h1, h2, hm⟩ : ∃ c' k, Exec P W saveR c c' k ∧ k = 15 ∧
      ztybn ∧
      c'.nreg = c.nreg ∧ c'.nmem = c.nmem := by
    unfold saveR
    exec_block
    refine ztkms
    rcases hi with rfl | ⟨h1, h2⟩
    · config_simp
    · interval_cases i <;> config_simp
  exact ⟨c', k, e, hk, h1, exec_frameM e wrM_saveR, h2, hm⟩
set_option maxHeartbeats 2000000 in
theorem restN_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W restN c c' k ∧ k = 7 ∧
      ztxik ∧
      FrameM BrN c c' ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem := by
  obtain ⟨c', k, e, hk, h1, h2, hm⟩ : ∃ c' k, Exec P W restN c c' k ∧ k = 7 ∧
      ztxik ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem := by
    unfold restN
    exec_block
    refine ztiwn
    interval_cases i <;> config_simp
  exact ⟨c', k, e, hk, h1, exec_frameM e wrM_restN, h2, hm⟩
set_option maxHeartbeats 2000000 in
theorem restR_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W restR c c' k ∧ k = 15 ∧
      ztybm ∧
      FrameM BrR c c' ∧ c'.nreg = c.nreg ∧ c'.nmem = c.nmem := by
  obtain ⟨c', k, e, hk, h1, h2, hm⟩ : ∃ c' k, Exec P W restR c c' k ∧ k = 15 ∧
      ztybm ∧
      c'.nreg = c.nreg ∧ c'.nmem = c.nmem := by
    unfold restR
    exec_block
    refine ztkms
    rcases hi with rfl | ⟨h1, h2⟩
    · config_simp
    · interval_cases i <;> config_simp
  exact ⟨c', k, e, hk, h1, exec_frameM e wrM_restR, h2, hm⟩
theorem bitO_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W bitO c c' k ∧ k ≤ 4 ∧ c'.nreg 190001 ≤ 1 ∧
      ztlkf ∧ c'.rreg 100 = c.rreg 100 ∧
      FrameM Bbit c c' ∧ c'.nmem = c.nmem := by
  obtain ⟨c', k, e, hk, h1, h2, h3, hm⟩ : ∃ c' k, Exec P W bitO c c' k ∧ k ≤ 4 ∧
      c'.nreg 190001 ≤ 1 ∧ ztlkf ∧ c'.rreg 100 = c.rreg 100 ∧
      c'.nmem = c.nmem := by
    unfold bitO
    refine spec_seq ?_
    exec_block
    · omega
    by_cases h : (0 : ℝ) < c.rreg 100
    · zucix
      refine spec_instr (Exec.constN ‹WordsBounded _ _› _ _ hW) fun _ => ?_
      simp_all
    · zupb
      refine spec_skip ‹WordsBounded _ _› ?_
      simp_all
  exact ⟨c', k, e, hk, h1, h2, h3, exec_frameM e wrM_bitO, hm⟩

/-- **The `LeftInside` bit.** -/
theorem orientT_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W orientT c c' k ∧ k ≤ 14 * P.n + 120 ∧
      c'.nreg 190001 ≤ 1 ∧ (c'.nreg 190001 = 1 ↔ Mountain.LeftInside zta) ∧
      FrameM B19 c c' ∧ c'.nmem = c.nmem := by
  zucm
  obtain ⟨c₀, k₀, e₀, hk₀, s1, F₀, rr₀, m₀⟩ := saveN_exec (P := P) c hw
  obtain ⟨c₁, k₁, e₁, hk₁, s2, F₁, nr₁, m₁⟩ := saveR_exec (P := P) c₀ e₀.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, ho, f2n, f2r, m₂, rm₂, o₂⟩ :=
    Final.orientStmt_exec (shearRel_Qof hG.2) hQ c₁ e₁.wb_right by_omega
  obtain ⟨c₃, k₃, e₃, hk₃, b1, b2, b3, F₃, m₃⟩ := bitO_exec (P := P) c₂ e₂.wb_right by_omega
  obtain ⟨c₄, k₄, e₄, hk₄, r1, F₄, rr₄, m₄⟩ := restN_exec (P := P) c₃ e₃.wb_right
  obtain ⟨c₅, k₅, e₅, hk₅, r2, F₅, nr₅, m₅⟩ := restR_exec (P := P) c₄ e₄.wb_right
  refine ⟨c₅, k₀ + ztbamf,
    .seq e₀ ztyoe, by_omega, ?_, ?_,
    ⟨fun r hr => ?_, fun r hr => ?_, ?_, ?_⟩, by_grind⟩
  · rw [nr₅, F₄.1 _ by_decide]; exact b1
  · rw [nr₅, F₄.1 _ by_decide, b2, ho]
    unfold Mountain.orient
    grind
  · -- natural registers outside band `19`
    zueet

    rw [nr₅]
    by_cases hres : 230 ≤ r ∧ r ≤ 236
    · rw [r1 r hres.1 hres.2, F₃.1 ztjep ztggh,
        f2n ztjep by_omega, nr₁, s1 r hres.1 hres.2]
    · rw [F₄.1 r (by unfold BrN; grind), F₃.1 r ztggh,
        f2n r by_omega, nr₁, F₀.1 r ztqfr]
  · -- real registers outside band `19`
    zueet

    by_cases hres : r = 100 ∨ ztnfz
    · rw [r2 r hres, rr₄, F₃.2.1 ztjep ztggh,
        f2r ztjep by_omega by_omega, s2 r hres, rr₀]
    · rw [F₅.2.1 r (by unfold BrR; grind), rr₄, F₃.2.1 r ztggh,
        f2r r by_omega by_omega, F₁.2.1 r ztqfr, rr₀]
  · rw [F₅.2.2.1, F₄.2.2.1, F₃.2.2.1, rm₂, F₁.2.2.1, F₀.2.2.1]
  · rw [F₅.2.2.2, F₄.2.2.2, F₃.2.2.2, o₂, F₁.2.2.2, F₀.2.2.2]
end exec
end
end DrvT
end Chazelle.Core
namespace Chazelle.Core
namespace DrvT
open Machine Machine.Stmt Programs BuildRam
@[expose] public section
def i0F (li : Bool) (m tS : ℕ) : ℕ :=
  if li then (if 0 < ztcez then 2 * m - ztcez
    else 0)
  else (if m < ztcez then 2 * m + m - ztcez
    else m - ztcez)
theorem sideS_le_two_m (C : Chain) (β : Bool) : C.sideS β ≤ 2 * C.m := by
  have := C.topIdx_le
  unfold Chain.sideS; grind

/-- **The formula is `i0`.** -/
theorem i0F_eq (C : Chain) (li : Bool) : i0F li C.m ztboi = i0 C li := by
  zubt
  have hS := sideS_le_two_m C C.sideBeta
  have hsA : TourA.sA C C.sideBeta = if C.sideS C.sideBeta < 2 * C.m then C.sideS C.sideBeta
      else 0 := by
    rw [sA_eq]
    zus
    · zubql
    · rw [show C.sideS C.sideBeta = 2 * C.m by omega, Nat.mod_self]
  zumol
  zuhfp
  unfold i0F
  rw [← hsA]
  cases li
  · zuma
    zus
    · zupd
    · rw [show 3 * C.m - TourA.sA C C.sideBeta = (C.m - TourA.sA C C.sideBeta) + 2 * C.m by
        omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
  · zuwa
    zus
    · zuey
    · rw [show TourA.sA C C.sideBeta = 0 by omega, Nat.sub_zero, Nat.mod_self]

/-! ## The program -/

/-- `s := 0`, `m := n - 1`. -/
def c0Pre : Stmt :=
  block [.constN 180000 0, .inputSize 190002, .constN 190017 1, .subN 180001 190002 190017]

/-- The shift from the tour start. -/
def c0Calc : Stmt :=
  .seq (block [.constN 190005 0, .constN 190006 6, .constN 190012 0, .copyN 190010 180001])
  (.seq ztipn
  (.seq (.ifLtN 190005 190001
      (.seq ztotu
        ztifi)
      (.ifLtN 180001 190012 ztiqm
        ztnbm))
  (.seq (block [.addN 190014 190013 190006, .addN 190015 190014 180001])
    (.ifLtN 190005 190001 (.instr (.constN 190016 0)) (.instr (.copyN 190016 180001))))))

/-- **The shift of the top chain.** -/
def c0S : Stmt := .seq c0Pre (.seq Brute.setupS c0Calc)

/-- The registers of `c0Calc`. -/
def Bcalc (r : ℕ) : Bool := decide (190005 ≤ r ∧ r ≤ 190016)
theorem wrM_c0Calc : wrM Bcalc c0Calc = true := by_decide

/-- The registers of `c0S`. -/
def Bc0 (r : ℕ) : Bool := Brute.Bm r || B19 r

/-- The registers of `c0Pre`. -/
def Bpre (r : ℕ) : Bool := decide (r = 180000 ∨ r = 180001 ∨ r = 190002 ∨ r = 190017)
theorem wrM_c0Pre' : wrM Bpre c0Pre = true := by_decide
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 2000000 in
theorem c0Calc_exec (c : Config) (hw : WordsBounded W c) {m tS : ℕ} {li : Bool}
    (h01 : c.nreg 180001 = m) (h12 : c.nreg 180012 = 2 * m) (h15 : c.nreg 180015 = tS)
    (hb : c.nreg 190001 = if li then 1 else 0) (_htS : tS ≤ 2 * m) (hW : 3 * m + 6 ≤ W) :
    ∃ c' k, Exec P W c0Calc c c' k ∧ k ≤ 20 ∧ c'.nreg 190010 = m ∧
      c'.nreg 190014 = i0F li m tS + 6 ∧ c'.nreg 190015 = i0F li m tS + 6 + m ∧
      c'.nreg 190016 = ztpci ∧ FrameM Bcalc c c' ∧ c'.nmem = c.nmem := by
  obtain ⟨c', k, e, hk, h1, h2, h3, h4, hm⟩ : ∃ c' k, Exec P W c0Calc c c' k ∧ k ≤ 20 ∧
      c'.nreg 190010 = m ∧ c'.nreg 190014 = i0F li m tS + 6 ∧
      c'.nreg 190015 = i0F li m tS + 6 + m ∧ c'.nreg 190016 = ztpci ∧
      c'.nmem = c.nmem := by
    unfold c0Calc
    refine spec_seq ?_
    exec_block
    · omega
    · omega
    · omega
    -- `sA`
    zujl
    set sA := if tS < 2 * m then tS else 0 with hsA
    have hsA2 : sA < 2 * m ∨ (sA = 0) := by_grind
    obtain ⟨c₁, k₁, e₁, hk₁, v12, g₁, m₁⟩ : ∃ c₁ k₁, Exec P W
        ztipn
        { pc := c.pc, nreg := upd ztibl 190010
            ztvhu, rreg := c.rreg, nmem := c.nmem, rmem := c.rmem,
            output := c.output } c₁ k₁ ∧ k₁ ≤ 2 ∧ c₁.nreg 190012 = sA ∧
        (∀ r, r ≠ 190012 → c₁.nreg r = (upd ztibl
          190010 ztvhu) r) ∧ c₁.nmem = c.nmem := by
      by_cases h : tS < 2 * m
      · zuek
        zujfo
        simp_all
      · zudx
        zumka
        simp_all
    refine ztcbs
    zud
    have g : ∀ r, r ≠ 190012 → r ≠ 190005 → r ≠ 190006 → r ≠ 190010 →
        c₁.nreg r = c.nreg r := by_simp_all
    have v05 : c₁.nreg 190005 = 0 := by_simp_all
    have v06 : c₁.nreg 190006 = 6 := by_simp_all
    have v10 : c₁.nreg 190010 = m := by_simp_all
    have v01 : c₁.nreg 180001 = m := by_simp_all
    have v12' : c₁.nreg 180012 = 2 * m := by_simp_all
    have vb : ztmvc := by
      simp_all
    -- `i0`
    zujl
    obtain ⟨c₂, k₂, e₂, hk₂, v13, g₂, m₂⟩ : ∃ c₂ k₂, Exec P W
        (.ifLtN 190005 190001
          (.seq ztotu
            ztifi)
          (.ifLtN 180001 190012 ztiqm
            ztnbm)) c₁ c₂ k₂ ∧ k₂ ≤ 8 ∧
        c₂.nreg 190013 = i0F li m tS ∧
        (∀ r, r ≠ 190013 → r ≠ 190007 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem := by
      cases li
      · -- not `LeftInside`
        zudx
        by_cases h : m < sA
        · zudd
          exec_block
          · omega
          refine ⟨by_omega, ?_, fun r a1 a2 => by config_simp; zungb, rfl⟩
          config_simp
          rw [v12', v01, v12]
          zuhao
        · zubv
          refine spec_instr ztpya fun _ => ?_
          refine ztext
          config_simp
          rw [v01, v12]
          zuhao
      · -- `LeftInside`
        zuek
        zujl
        zujfl
        by_cases h : 0 < sA
        · zuek
          refine spec_instr ztpya fun _ => ?_
          refine ztext
          config_simp
          rw [v12', v12]
          unfold i0F; simp_all
        · refine spec_ifLtN_false (by config_simp; omega) ?_
          zumka
          refine ztext
          config_simp
          zuhao
    refine ztcow
    zue
    have hi0 : i0F li m tS ≤ 2 * m := by
      zuhao
    refine spec_seq ?_
    exec_block
    · grind
    · config_simp; grind
    have w₃ := by_omega
    cases li
    · refine spec_ifLtN_false (by config_simp; grind) ?_
      zujfo
      refine ztbfj
      · config_simp; grind
      · config_simp; grind
      · config_simp; grind
      · config_simp; grind
      grind
    · refine spec_ifLtN_true (by config_simp; grind) ?_
      zujfl
      refine ztbfj
      · config_simp; grind
      · config_simp; grind
      · config_simp; grind
      · simp
      grind
  exact ⟨c', k, e, hk, h1, h2, h3, h4, exec_frameM e wrM_c0Calc, hm⟩
set_option maxHeartbeats 2000000 in
theorem c0Pre_exec (hW : P.n + 3 ≤ W) (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W c0Pre c c' k ∧ k = 4 ∧ c'.nreg 180000 = 0 ∧ c'.nreg 180001 = P.n - 1 ∧
      FrameM Bpre c c' ∧ c'.nmem = c.nmem := by
  obtain ⟨c', k, e, hk, h1, h2, hm⟩ : ∃ c' k, Exec P W c0Pre c c' k ∧ k = 4 ∧
      c'.nreg 180000 = 0 ∧ c'.nreg 180001 = P.n - 1 ∧ c'.nmem = c.nmem := by
    unfold c0Pre
    exec_block
    · omega
    · omega
    · omega
    simp
  exact ⟨c', k, e, hk, h1, h2, exec_frameM e wrM_c0Pre', hm⟩
set_option maxHeartbeats 2000000 in
/-- **The inner-side shift of the top chain.** -/
theorem c0S_exec (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) {C : Chain} (hC : TopChain P C)
    {li : Bool} (c : Config) (hw : WordsBounded W c) (hb : c.nreg 190001 = if li then 1 else 0)
    (hroom : c.nreg ALLOC + 2 * P.n + 10 ≤ W) :
    ∃ c' k, Exec P W c0S c c' k ∧ k ≤ 260 * P.n + 1950 ∧
      c'.nreg 190010 = C.m ∧ c'.nreg 190014 = c0 C li ∧ c'.nreg 190015 = c0 C li + C.m ∧
      c'.nreg 190016 = idxI li P.n 0 ∧ c'.nreg 190001 = ztfhy ∧
      FrameM Bc0 c c' ∧ zth := by
  obtain ⟨hCP, hCs, hCm⟩ := hC
  have hWn : ztmd := by_grind
  obtain ⟨c₁, k₁, e₁, hk₁, p0, p1, F₁, m₁⟩ := c0Pre_exec (P := P) hWn c hw
  have hA₁ : ztdc := F₁.1 _ by_decide
  obtain ⟨c₂, k₂, e₂, hk₂, -, hCtx, -, hlow, -, -, R₂, RR₂, rm₂, o₂⟩ :=
    Brute.setup_exec (P := P) hG by_omega
      ztdha hCP by_omega c₁ e₁.wb_right
      by_omega by_omega by_omega
  obtain ⟨-, x01, -, -, -, x12, -, x15, -⟩ := hCtx
  have hb₂ : c₂.nreg 190001 = if li then 1 else 0 := by
    rw [R₂ _ by_decide, F₁.1 _ by_decide, hb]
  obtain ⟨c₃, k₃, e₃, hk₃, v10, v14, v15, v16, F₃, m₃⟩ := c0Calc_exec (P := P) c₂ e₂.wb_right
    (m := C.m) (tS := C.sideS C.sideBeta) (li := li) x01 x12 x15 hb₂
    (sideS_le_two_m C C.sideBeta) ztdha
  have hi0 := i0F_eq C li
  refine ⟨c₃, k₁ + zttl, .seq e₁ ztcr, by_omega, v10, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v14, hi0]; rfl
  · rw [v15, hi0]; rfl
  · zuouv; unfold idxI; grind
  · rw [F₃.1 _ by_decide, hb₂]
  · refine ⟨fun r hr => ?_, fun r hr => ?_, ?_, ?_⟩
    · zufqa
      rw [F₃.1 r ztkvc, R₂ r hr.1, F₁.1 r
        zthfn]
    · zufqa
      rw [F₃.2.1 r ztkvc, RR₂ r hr.1, F₁.2.1 r
        zthfn]
    · rw [F₃.2.2.1, rm₂, F₁.2.2.1]
    · rw [F₃.2.2.2, o₂, F₁.2.2.2]
  simp_all
end exec
end
end DrvT
end Chazelle.Core
namespace Chazelle.Core
namespace DrvT
open Machine Machine.Stmt Programs BuildRam
open DownBase (rankF tw)
@[expose] public section
def fLoad : Stmt := block [.loadN 190032 190031, .addN 190031 190031 190017,
  .loadN 190033 190031, .addN 190031 190031 190017, .loadN 190034 190031,
  .addN 190031 190031 190017, .addN 190031 190031 190017, .addN 190031 190031 190017,
  .constN 190037 0]

/-- Raise the flag if the end in register `p` is inner. -/
def fTest (p : ℕ) : Stmt :=
  .ifLtN p 190014 .skip
    (.ifLtN p 190015
      (.ifLtN 190014 p ztifv
        (.ifLtN 190032 190016 ztifv
          (.ifLtN 190016 190032 ztifv .skip)))
      .skip)

/-- Map the end in register `p` into register `d`. -/
def fMap (d p : ℕ) : Stmt :=
  .seq (.instr (.copyN d 190010))
    (.ifLtN p 190014 .skip (.ifLtN p 190015 (.instr (.subN d p 190014)) .skip))

/-- Append the mapped triple. -/
def fKeep : Stmt := block [.storeN 190035 190032, .addN 190035 190035 190017,
  .storeN 190035 190038, .addN 190035 190035 190017, .storeN 190035 190039,
  .addN 190035 190035 190017, .addN 190036 190036 190017]

/-- One record. -/
def fBody : Stmt :=
  .seq fLoad (.seq (fTest 190033) (.seq (fTest 190034) (.seq (fMap 190038 190033)
    (.seq (fMap 190039 190034) (.seq ztprn
      (.instr (.addN 190030 190030 190017)))))))

/-- **The filter pass.** -/
def fLoop : Stmt := .whileLtN 190030 190023 fBody

/-! ## The memory of the pass -/

/-- The memory after `i` records: the kept triples so far at `B'`, mapped. -/
def memT (m₀ : ℕ → ℕ) (li : Bool) (n c₀ : ℕ) (L₀ : List zte) (B' i a : ℕ) : ℕ :=
  if B' ≤ a ∧ a < B' + 3 * rankF ztbdh L₀ i then tw ztkgd ztjnv
  else m₀ a

/-- The kept triple of record `i` is entry `rank i` of the filtered list. -/
theorem getD_transL {li : Bool} {n c₀ : ℕ} {L₀ : List zte} {i : ℕ}
    (hi : i < L₀.length) (hk : keepT li n c₀ ztwtp = true) :
    (transL li n c₀ L₀).getD (rankF ztbdh L₀ i) ztt =
      trT n c₀ ztwtp := by
  have hlt := DownBase.rankF_lt_length _ ztt hi hk
  have hg := DownBase.getD_filter_rank _ ztt hi hk
  unfold transL
  simp_all

/-- The memory step of a kept record. -/
theorem memT_keep {m₀ m : ℕ → ℕ} {li : Bool} {n c₀ : ℕ} {L₀ : List zte} {B' i : ℕ}
    (hm : ∀ a, m a = memT m₀ li n c₀ L₀ B' i a) (hi : i < L₀.length)
    (hk : keepT li n c₀ ztwtp = true) (a : ℕ) :
    (if a = B' + 3 * rankF ztbdh L₀ i + 2 then (trT n c₀ ztwtp).2.2
      else if a = B' + 3 * rankF ztbdh L₀ i + 1 then
        (trT n c₀ ztwtp).2.1
      else if a = B' + 3 * rankF ztbdh L₀ i then (trT n c₀ ztwtp).1
      else m a) = memT m₀ li n c₀ L₀ B' (i + 1) a := by
  zuizc
  zueyo
  set j := rankF _ L₀ i with hj
  have hg := getD_transL hi hk
  zuezw
  have htw : ∀ s, s < 3 → tw _ _ =
      if s = 0 then (trT n c₀ _).1
      else if s = 1 then (trT n c₀ _).2.1
      else (trT n c₀ _).2.2 := fun s hs => by
    zuqd

  zubyr
  unfold memT
  zubim
  zuccp
  · subst h3
    rw [ite_eq_left rfl, ite_eq_left by_omega, show B' + 3 * j + 2 - B' = 3 * j + 2 by omega,
      htw 2 by_norm_num]
    zulav
  zuccq
  · subst h4
    rw [ite_eq_right h3, ite_eq_left rfl, ite_eq_left by_omega, show B' + 3 * j + 1 - B' = 3 * j + 1 by omega,
      htw 1 by_norm_num]
    zulav
  zucup
  · subst h5
    rw [ite_eq_right h3, ite_eq_right h4, ite_eq_left rfl, ite_eq_left by_omega,
      show B' + 3 * j - B' = 3 * j + 0 by omega, htw 0 by_norm_num]
    zulav
  grind

/-- The memory of a dropped record does not change. -/
theorem memT_drop {m₀ : ℕ → ℕ} {li : Bool} {n c₀ : ℕ} {L₀ : List zte} {B' i : ℕ}
    (hi : i < L₀.length) (hk : keepT li n c₀ ztwtp = false) (a : ℕ) :
    memT m₀ li n c₀ L₀ B' i a = memT m₀ li n c₀ L₀ B' ztg a := by
  zuizc
  zugdz
  zunu
  unfold memT; zvnel

/-! ## The pieces of one record -/
section exec
variable {P : Polygon} {W : ℕ}
variable (c : Config)
set_option maxHeartbeats 4000000 in
theorem fLoad_exec (hw : WordsBounded W c) {a : ℕ} (h31 : c.nreg 190031 = a)
    (h17 : c.nreg 190017 = 1) (haW : a + 5 ≤ W) :
    ∃ c' k, Exec P W fLoad c c' k ∧ k = 9 ∧ c'.nreg 190032 = c.nmem a ∧
      c'.nreg 190033 = c.nmem ztdf ∧ c'.nreg 190034 = c.nmem ztvj ∧
      c'.nreg 190031 = a + 5 ∧ c'.nreg 190037 = 0 ∧
      (∀ r, r ≠ 190031 → r ≠ 190032 → r ≠ 190033 → r ≠ 190034 → r ≠ 190037 →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  unfold fLoad
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h31, h17]; omega)
  simp_all

/-- **The test of an end.** -/
theorem fTest_exec (hw : WordsBounded W c) (hW : 1 ≤ W) {li : Bool} {n c₀ p : ℕ}
    (_hp : p ≠ 190037) (_hp1 : p ≠ 190014) (_hp2 : p ≠ 190015)
    (h14 : c.nreg 190014 = c₀) (h15 : c.nreg 190015 = c₀ + ztkl)
    (h16 : c.nreg 190016 = idxI li n 0) :
    ∃ c' k, Exec P W (fTest p) c c' k ∧ k ≤ 10 ∧
      c'.nreg 190037 = (if innerE li n c₀ (c.nreg 190032) ztfgw = true then 1
        else c.nreg 190037) ∧
      ztivf ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hset : ∃ c' k, Exec P W _ c c' k ∧ k = 1 ∧
      c'.nreg 190037 = 1 ∧ ztivf ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output :=
    ⟨_, _, Exec.constN hw 190037 1 hW, rfl, by_simp, by_simp_all, rfl, rfl, rfl,
      rfl⟩
  obtain ⟨cs, ks, es, hks, vs, gs, ms, rrs, rms, os⟩ := hset
  unfold fTest innerE
  by_cases h1 : c.nreg p < c.nreg 190014
  · refine ⟨c, _, .ifLtN_true h1 ztjd, by_omega, ?_, by_omega, rfl, rfl, rfl, rfl⟩
    simp_all
  by_cases h2 : c.nreg p < c.nreg 190015
  · by_cases h3 : c.nreg 190014 < c.nreg p
    · refine ⟨cs, _, .ifLtN_false h1 (.ifLtN_true h2 (.ifLtN_true h3 es)), by_omega, ?_, gs,
        ms, rrs, rms, os⟩
      grind
    · by_cases h4 : c.nreg 190032 < c.nreg 190016
      · refine ⟨cs, _, .ifLtN_false h1 (.ifLtN_true h2 (.ifLtN_false h3 (.ifLtN_true h4 es))),
          by omega, ?_, gs, ms, rrs, rms, os⟩
        grind
      · by_cases h5 : c.nreg 190016 < c.nreg 190032
        · refine ⟨cs, _, .ifLtN_false h1 (.ifLtN_true h2 (.ifLtN_false h3 (.ifLtN_false h4
            (.ifLtN_true h5 es)))), by_omega, ?_, gs, ms, rrs, rms, os⟩
          grind
        · refine ⟨c, _, .ifLtN_false h1 (.ifLtN_true h2 (.ifLtN_false h3 (.ifLtN_false h4
            (.ifLtN_false h5 ztjd)))), by_omega, ?_, by_omega, rfl, rfl, rfl, rfl⟩
          grind
  · refine ⟨c, _, .ifLtN_false h1 ztzrp, by_omega, ?_, by_omega,
      rfl, rfl, rfl, rfl⟩
    simp_all

/-- **The map of an end.** -/
theorem fMap_exec (hw : WordsBounded W c) {n c₀ d p : ℕ}
    (hd1 : d ≠ 190014) (hd2 : d ≠ 190015) (hdp : d ≠ p) (_hd3 : d ≠ 190010)
    (h10 : c.nreg 190010 = n - 1) (h14 : c.nreg 190014 = c₀)
    (h15 : c.nreg 190015 = c₀ + ztkl) :
    ∃ c' k, Exec P W (fMap d p) c c' k ∧ k ≤ 6 ∧ c'.nreg d = mapE n c₀ ztfgw ∧
      ztivi ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have e₁ := Exec.copyN (P := P) hw d 190010
  set c₁ : Config := { c with nreg := upd c.nreg d _ } with hc₁
  zud
  have g₁ : ∀ r, r ≠ d → c₁.nreg r = c.nreg r := by_simp_all
  have v₁ : c₁.nreg d = n - 1 := by_simp_all
  have q14 : c₁.nreg 190014 = c₀ := by_grind
  have q15 : c₁.nreg 190015 = c₀ + ztkl := by_grind
  have qp : c₁.nreg p = c.nreg p := by_grind
  unfold fMap mapE
  by_cases h1 : c₁.nreg p < c₁.nreg 190014
  · refine ⟨c₁, _, .seq e₁ (.ifLtN_true h1 ztwd), by_omega, ?_, g₁, rfl, rfl, rfl, rfl⟩
    simp_all
  by_cases h2 : c₁.nreg p < c₁.nreg 190015
  · have e₂ := Exec.subN (P := P) w₁ d p 190014
    refine ⟨_, _, .seq e₁ (.ifLtN_false h1 (.ifLtN_true h2 e₂)), by_omega, ?_,
      fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · simp_all
    simp_all
  · refine ⟨c₁, _, .seq e₁ (.ifLtN_false h1 (.ifLtN_false h2 ztwd)), by_omega, ?_, g₁,
      rfl, rfl, rfl, rfl⟩
    simp_all
set_option maxHeartbeats 4000000 in
/-- **Append a triple.** -/
theorem fKeep_exec (hw : WordsBounded W c) {w j : ℕ} (h35 : c.nreg 190035 = w)
    (h36 : c.nreg 190036 = j) (h17 : c.nreg 190017 = 1) (hwW : w + 3 ≤ W) (hjW : j + 1 ≤ W) :
    ∃ c' k, Exec P W fKeep c c' k ∧ k = 7 ∧ c'.nreg 190035 = w + 3 ∧ c'.nreg 190036 = j + 1 ∧
      (∀ r, r ≠ 190035 → r ≠ 190036 → c'.nreg r = c.nreg r) ∧
      (∀ a, c'.nmem a = if a = w + 2 then c.nreg 190039 else if a = w + 1 then c.nreg 190038
        else if a = w then c.nreg 190032 else c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fKeep
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h35, h36, h17]; omega)
  refine zteza
  all_goals simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h35, h36, h17]
  rfl
end exec
end
end DrvT
end Chazelle.Core
namespace Chazelle.Core
namespace DrvT
open Machine Machine.Stmt Programs BuildRam
open DownBase (rankF tw)
@[expose] public section
structure FInv (m₀ : ℕ → ℕ) (li : Bool) (n c₀ : ℕ) (L₀ : List zte) (CB B' : ℕ)
    (cI d : Config) : Prop where
  i_le : d.nreg 190030 ≤ L₀.length
  rK : d.nreg 190023 = L₀.length
  r31 : d.nreg 190031 = CB + 5 * d.nreg 190030
  r35 : d.nreg 190035 = B' + 3 * rankF ztbdh L₀ ztqlj
  r36 : d.nreg 190036 = rankF ztbdh L₀ ztqlj
  r10 : d.nreg 190010 = n - 1
  r14 : d.nreg 190014 = c₀
  r15 : d.nreg 190015 = c₀ + ztkl
  r16 : d.nreg 190016 = idxI li n 0
  r17 : d.nreg 190017 = 1
  r18 : d.nreg 190018 = 0
  fr : ∀ r, zthjr → d.nreg r = cI.nreg r
  rr : d.rreg = cI.rreg
  rm : d.rmem = cI.rmem
  out : d.output = cI.output
  mem : ∀ a, d.nmem a = memT m₀ li n c₀ L₀ B' ztqlj a

/-- The records of the chord area: `(h, lp, rp)` of record `i` at `CB + 5 i`. -/
def RecsT (m : ℕ → ℕ) (CB : ℕ) (L₀ : List zte) : Prop :=
  ∀ i, i < L₀.length → m ztblv = (L₀.getD i ztt).1 ∧
    m ztbye = (L₀.getD i ztt).2.1 ∧ m ztbyf = (L₀.getD i ztt).2.2
section exec
variable {P : Polygon} {W : ℕ}
variable {m₀ : ℕ → ℕ} {li : Bool} {n c₀ : ℕ} {L₀ : List (ℕ × ℕ × ℕ)} {CB B' : ℕ}
set_option maxHeartbeats 8000000 in
/-- **One record.** -/
theorem fBody_exec
    (hR : RecsT m₀ CB L₀) (hCB : L₀.length = 0 ∨ CB + 5 * L₀.length ≤ B')
    (hBW : B' + 3 * L₀.length + 3 ≤ W) {cI d : Config} (hw : WordsBounded W d)
    (hI : FInv m₀ li n c₀ L₀ CB B' cI d) (ht : d.nreg 190030 < d.nreg 190023) :
    ∃ d' k, Exec P W fBody d d' k ∧ WordsBounded W d' ∧ FInv m₀ li n c₀ L₀ CB B' cI d' ∧
      d'.nreg 190030 = d.nreg 190030 + 1 ∧ 3 ≤ k ∧ k ≤ 52 := by
  zufnc

  set i := d.nreg 190030 with hi
  zuiol
  set j := rankF ztbdh L₀ i with hj
  have hle := DownBase.rankF_le ztbdh L₀ i
  zufki
  have hmL : ztdxt := fun q hq => by
    zuocy; unfold memT; grind
  zudk
  clear hCB
  -- load
  obtain ⟨d₁, k₁, e₁, hk₁, v32, v33, v34, v31, v37, r₁, m₁, rr₁, rm₁, o₁⟩ :=
    fLoad_exec (P := P) d hw hI.r31 hI.r17 by_omega
  rw [← hi] at v32 v33 v34 v31
  zucdc

  rw [hm0, l1] at v32
  rw [hmL 1 by_norm_num, l2] at v33
  rw [hmL 2 by_norm_num, l3] at v34
  have g₁ : ∀ r, (r < 190031 ∨ 190037 < r) → d₁.nreg r = d.nreg r := by_grind
  -- the two tests
  obtain ⟨d₂, k₂, e₂, hk₂, v₂, r₂, m₂, rr₂, rm₂, o₂⟩ := fTest_exec (P := P) d₁ e₁.wb_right hW1
    (li := li) (n := n) (c₀ := c₀) (p := 190033) by_norm_num by_norm_num by_norm_num
    (by rw [g₁ _ by_norm_num, hI.r14]) (by rw [g₁ _ by_norm_num, hI.r15])
    (by rw [g₁ _ by_norm_num, hI.r16])
  obtain ⟨d₃, k₃, e₃, hk₃, v₃, r₃, m₃, rr₃, rm₃, o₃⟩ := fTest_exec (P := P) d₂ e₂.wb_right hW1
    (li := li) (n := n) (c₀ := c₀) (p := 190034) by_norm_num by_norm_num by_norm_num
    (by rw [r₂ _ by_norm_num, g₁ _ by_norm_num, hI.r14])
    (by rw [r₂ _ by_norm_num, g₁ _ by_norm_num, hI.r15])
    (by rw [r₂ _ by_norm_num, g₁ _ by_norm_num, hI.r16])
  have hflag : d₃.nreg 190037 = if keepT li n c₀ x = true then 1 else 0 := by
    rw [v₃, r₂ _ by_norm_num, r₂ _ by_norm_num, v₂, v37, v32, v33, v34]
    unfold keepT
    grind
  -- the two maps
  obtain ⟨d₄, k₄, e₄, hk₄, v₄, r₄, m₄, rr₄, rm₄, o₄⟩ := fMap_exec (P := P) d₃ e₃.wb_right
    (n := n) (c₀ := c₀) (d := 190038) (p := 190033) by_norm_num by_norm_num by_norm_num
    by_norm_num
    (by rw [r₃ _ by_norm_num, r₂ _ by_norm_num, g₁ _ by_norm_num, hI.r10])
    (by rw [r₃ _ by_norm_num, r₂ _ by_norm_num, g₁ _ by_norm_num, hI.r14])
    (by rw [r₃ _ by_norm_num, r₂ _ by_norm_num, g₁ _ by_norm_num, hI.r15])
  obtain ⟨d₅, k₅, e₅, hk₅, v₅, r₅, m₅, rr₅, rm₅, o₅⟩ := fMap_exec (P := P) d₄ e₄.wb_right
    (n := n) (c₀ := c₀) (d := 190039) (p := 190034) by_norm_num by_norm_num by_norm_num
    by_norm_num
    (by rw [r₄ _ by_norm_num, r₃ _ by_norm_num, r₂ _ by_norm_num, g₁ _ by_norm_num,
      hI.r10])
    (by rw [r₄ _ by_norm_num, r₃ _ by_norm_num, r₂ _ by_norm_num, g₁ _ by_norm_num,
      hI.r14])
    (by rw [r₄ _ by_norm_num, r₃ _ by_norm_num, r₂ _ by_norm_num, g₁ _ by_norm_num,
      hI.r15])
  -- registers of `d₅`
  have g5 : ∀ r, r ≠ 190031 → r ≠ 190032 → r ≠ 190033 → r ≠ 190034 → r ≠ 190037 →
      r ≠ 190038 → r ≠ 190039 → d₅.nreg r = d.nreg r := by_grind
  have e32 : d₅.nreg 190032 = x.1 := by
    grind
  have e38 : d₅.nreg 190038 = mapE n c₀ x.2.1 := by
    grind
  have e39 : d₅.nreg 190039 = mapE n c₀ x.2.2 := by
    grind
  have f5 : d₅.nreg 190037 = if keepT li n c₀ x = true then 1 else 0 := by
    grind
  have hm5 : d₅.nmem = d.nmem := by_grind
  -- the branch
  obtain ⟨d₆, k₆, e₆, hk₆, hk₆', g6, mem6, n35, n36, rr₆, rm₆, o₆⟩ : ∃ d₆ k₆,
      Exec P W ztprn d₅ d₆ k₆ ∧ 1 ≤ k₆ ∧ k₆ ≤ 8 ∧
      (∀ r, r ≠ 190035 → r ≠ 190036 → d₆.nreg r = d₅.nreg r) ∧
      (∀ a, d₆.nmem a = memT m₀ li n c₀ L₀ B' ztg a) ∧
      d₆.nreg 190035 = B' + 3 * rankF ztbdh L₀ ztg ∧
      d₆.nreg 190036 = rankF ztbdh L₀ ztg ∧
      d₆.rreg = d₅.rreg ∧ d₆.rmem = d₅.rmem ∧ d₆.output = d₅.output := by
    have h18 : d₅.nreg 190018 = 0 := by
      rw [g5 _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
        by_norm_num by_norm_num, hI.r18]
    have h35 : d₅.nreg 190035 = B' + 3 * j := by
      rw [g5 _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
        by_norm_num by_norm_num, hI.r35]
    have h36 : d₅.nreg 190036 = j := by
      rw [g5 _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
        by_norm_num by_norm_num, hI.r36]
    have h17 : d₅.nreg 190017 = 1 := by
      rw [g5 _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
        by_norm_num by_norm_num, hI.r17]
    have hr := DownBase.rankF_succ ztbdh ztt ht
    cases hk : keepT li n c₀ x
    · zukup
      zvnhh at f5
      have hn : ¬ d₅.nreg 190018 < d₅.nreg 190037 := by_omega
      zuvt
      zunu
      refine ⟨d₅, _, .ifLtN_false hn ztuvn, by_omega, by_omega,
        by omega, fun a => ?_, by_omega, by_omega, rfl, rfl, rfl⟩
      zugvc
      exact memT_drop ht by_omega a
    · zukup
      simp only [ite_true] at f5
      have hp : d₅.nreg 190018 < d₅.nreg 190037 := by_omega
      have hjK : ztsjl := by
        omega
      obtain ⟨d₆, k₆, e₆', hk₆, w35, w36, r₆, mm₆, rr₆, rm₆, o₆⟩ :=
        fKeep_exec d₅ e₅.wb_right h35 h36 h17 by_omega by_omega
      zuvt
      zufbp
      refine ⟨d₆, _, .ifLtN_true hp e₆', by_omega, by_omega, r₆, fun a => ?_,
        by omega, by_omega, rr₆, rm₆, o₆⟩
      rw [mm₆, e32, e38, e39, hm5]
      have := memT_keep (hI.mem) ht
        by_omega a
      rw [← hi, ← hj] at this
      zuhnz
      rfl
  -- the increment
  have h30 : d₆.nreg 190030 = i := by
    grind
  have h17' : d₆.nreg 190017 = 1 := by
    rw [g6 _ by_norm_num by_norm_num, g5 _ by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num by_norm_num by_norm_num, hI.r17]
  have e₇ := Exec.addN (P := P) e₆.wb_right 190030 190030 190017 by_omega
  set d₇ : Config := { d₆ with nreg := upd d₆.nreg 190030 _ }
    with hd₇
  have g7 : ∀ r, r ≠ 190030 → d₇.nreg r = d₆.nreg r := fun r hr => by zunsa; zumwy
  have v7 : d₇.nreg 190030 = i + 1 := by zunsa; simp [h30, h17']
  have g : ∀ r, zthjr → d₇.nreg r = d.nreg r := fun r hr => by
    rw [g7 r by_omega, g6 r by_omega by_omega,
      g5 r by_omega by_omega by_omega by_omega by_omega by_omega by_omega]
  have X' : Exec P W fBody d d₇ _ :=
    .seq e₁ ztfc
  refine zthmx
  refine ⟨by_omega, by zunhi, ?_, ?_, ?_,
    by rw [g _ by_norm_num, hI.r10], by rw [g _ by_norm_num, hI.r14],
    by rw [g _ by_norm_num, hI.r15], by rw [g _ by_norm_num, hI.r16],
    by grind, by rw [g _ by_norm_num, hI.r18],
    fun r hr => by zunac, ?_, ?_, ?_, fun a => ?_⟩
  · rw [v7, g7 _ by_norm_num, g6 _ by_norm_num by_norm_num, r₅ _ by_norm_num,
      r₄ _ by_norm_num, r₃ _ by_norm_num, r₂ _ by_norm_num, v31]
    ring
  · grind
  · grind
  · show d₆.rreg = cI.rreg; rw [rr₆, rr₅, rr₄, rr₃, rr₂, rr₁, hI.rr]
  · show d₆.rmem = cI.rmem; rw [rm₆, rm₅, rm₄, rm₃, rm₂, rm₁, hI.rm]
  · show d₆.output = cI.output; rw [o₆, o₅, o₄, o₃, o₂, o₁, hI.out]
  grind

/-- **The filter pass.** -/
theorem fLoop_exec
    (hR : RecsT m₀ CB L₀) (hCB : L₀.length = 0 ∨ CB + 5 * L₀.length ≤ B')
    (hBW : B' + 3 * L₀.length + 3 ≤ W) {cI d : Config} (hw : WordsBounded W d)
    (hI : FInv m₀ li n c₀ L₀ CB B' cI d) (h0 : d.nreg 190030 = 0) :
    ∃ d' k, Exec P W fLoop d d' k ∧ WordsBounded W d' ∧ FInv m₀ li n c₀ L₀ CB B' cI d' ∧
      d'.nreg 190030 = L₀.length ∧ 3 * L₀.length ≤ k ∧ k ≤ 54 * L₀.length + 2 := by
  obtain ⟨d', k, e, ⟨hw', hI'⟩, htest, hk, hψ⟩ := SortR.whileLtN_potential_lb (P := P) (W := W)
    (a := 190030) (b := 190023) (body := fBody)
    (fun d => WordsBounded W d ∧ FInv m₀ li n c₀ L₀ CB B' cI d)
    (fun d => 54 * (L₀.length - d.nreg 190030)) (fun d => 3 * d.nreg 190030) ztoe
    (fun d ⟨hwd, hId⟩ ht => by
      obtain ⟨d', k, e, hw', hI', hi', hk1, hk2⟩ := fBody_exec hR hCB hBW hwd hId ht
      have := hId.rK
      refine ztkkq
      · omega
      omega)
    ⟨hw, hI⟩
  zucdb

  · omega
  omega
end exec
end
end DrvT
end Chazelle.Core
namespace Chazelle.Core
namespace DrvT
open Machine Machine.Stmt Programs BuildRam
open DownBase (rankF tw)
@[expose] public section
def fSetup : Stmt := block [.copyN 190021 9999, .constN 190017 1, .constN 190018 0,
  .constN 190041 6, .addN 190022 190021 190041, .loadN 190023 230002, .constN 190042 3,
  .addN 190040 230002 190042, .loadN 190024 190040, .storeN 190021 190017,
  .addN 190040 190021 190017, .storeN 190040 190001, .addN 190043 190023 190023,
  .addN 190043 190043 190023, .addN 9999 190022 190043, .constN 190030 0,
  .copyN 190031 190024, .copyN 190035 190022, .constN 190036 0]

/-- **The filter procedure.** -/
def filtS : Stmt := .seq fSetup fLoop

/-- **A robust normal form lies below the bound**: its header and its chord records. -/
theorem nfAt_robust_bound {A : ℕ} {m : ℕ → ℕ} {B : ℕ} {N : NF}
    (h : Robust A m (fun m' => NFAt m' B N)) :
    B + 11 < A ∧ ∀ i, i < N.chords.length → m ztkh + 5 * i + 4 < A := by
  have h1 : B + 11 < A := by
    zux

    have := (h (Function.update m ztsvb (N.dec.length + 1)) (fun a ha => by
      grind)).2.2.2.2.1
    simp_all
  refine ⟨h1, fun i hi => ?_⟩
  zux

  set a := m ztkh + 5 * i + 4 with ha
  have hm : ∀ a', a' < A → Function.update m a ztmyd a' = m a' := fun a' ha' => by
    grind
  have hN := h _ hm
  have h3 : Function.update m a ztmyd ztkh = m ztkh := hm _ by_omega
  have := (hN.2.2.2.2.2.1 i hi).2.2.2.2
  simp_all
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 8000000 in
theorem fSetup_exec (c : Config) (hw : WordsBounded W c) {A Bn K₀ CB b : ℕ}
    (hA : c.nreg 9999 = A) (hBn : c.nreg 230002 = Bn) (hBnA : Bn + 11 < A)
    (hK : c.nmem Bn = K₀) (hCB : c.nmem ztjgx = CB) (hb : c.nreg 190001 = b)
    (hroom : A + 6 + 3 * K₀ + 10 ≤ W) :
    ∃ c' k, Exec P W fSetup c c' k ∧ k = 19 ∧ c'.nreg 190021 = A ∧ c'.nreg 190022 = A + 6 ∧
      c'.nreg 190023 = K₀ ∧ c'.nreg 190024 = CB ∧ c'.nreg 190017 = 1 ∧ c'.nreg 190018 = 0 ∧
      c'.nreg 9999 = A + 6 + 3 * K₀ ∧ c'.nreg 190030 = 0 ∧ c'.nreg 190031 = CB ∧
      c'.nreg 190035 = A + 6 ∧ c'.nreg 190036 = 0 ∧
      (∀ r, ztofl → r ≠ 9999 → c'.nreg r = c.nreg r) ∧
      (∀ a, c'.nmem a = if a = A + 1 then b else if a = A then 1 else c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAW : ztpio := by_omega
  unfold fSetup
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hA, hBn, hK, hCB, hb]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r a1 a2 => ?_, fun a => ?_, rfl,
    rfl, rfl⟩
  all_goals simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hA, hBn, hK, hCB, hb]
  zubqj
  rfl

/-- The records of a robust normal form, as triples. -/
theorem recsT_of_nfAt {A : ℕ} {m m' : ℕ → ℕ} {B : ℕ} {N : NF}
    (h : Robust A m (fun m'' => NFAt m'' B N)) (hm : ∀ a, a < A → m' a = m a) :
    RecsT m' ztbaid ztddq := by
  obtain ⟨-, hrec⟩ := nfAt_robust_bound h
  have hN := h.holds
  zug
  have hi' : i < N.chords.length := by unfold triplesOf at hi; simp_all
  obtain ⟨e1, e2, e3, -, -⟩ := hN.2.2.2.2.2.1 i hi'
  have hb := hrec i hi'
  have hg : (triplesOf N).getD i ztt = ztgbh := by
    unfold triplesOf NF.chord
    simp_all
  grind

/-- The list of a full pass, in memory. -/
theorem chordListAt_memT {m₀ m : ℕ → ℕ} {li : Bool} {n c₀ : ℕ} {L₀ : List zte} {B' : ℕ}
    (hm : ∀ a, m a = memT m₀ li n c₀ L₀ B' L₀.length a) :
    ChordListAt m B' ztkgd := by
  have hlen : rankF ztbdh L₀ L₀.length = (transL li n c₀ L₀).length := by
    zuovt; unfold transL; simp
  zun
  have hq : ∀ q, q < 3 → m ztnjj = tw ztkgd ztpue := by
    zuco
    zvmwi; unfold memT; grind
  zusk
  · have := hq 0 by_norm_num; rw [Nat.add_zero, Nat.add_zero] at this; zvmwk
    zumvi
  · zugvj

  · zugvk
set_option maxHeartbeats 4000000 in
/-- **The filter procedure.** -/
theorem filtS_exec (c : Config) (hw : WordsBounded W c) {N : NF} {li : Bool} {n c₀ : ℕ}
    (hN : Robust ztm c.nmem (fun m => NFAt m (c.nreg 230002) N))
    (h01 : c.nreg 190001 = if li then 1 else 0) (h10 : c.nreg 190010 = n - 1)
    (h14 : c.nreg 190014 = c₀) (h15 : c.nreg 190015 = c₀ + ztkl)
    (h16 : c.nreg 190016 = idxI li n 0)
    (hroom : c.nreg ALLOC + 3 * N.chords.length + 20 ≤ W) :
    ∃ c' k, Exec P W filtS c c' k ∧ 6 + 3 * N.chords.length ≤ k ∧
      k ≤ 54 * N.chords.length + 21 ∧
      c'.nreg 190021 = c.nreg ALLOC ∧ c'.nreg 190022 = c.nreg ALLOC + 6 ∧
      c'.nreg 190036 = (transL li n c₀ ztddq).length ∧
      c'.nreg ALLOC = c.nreg ALLOC + 6 + 3 * N.chords.length ∧
      ChordListAt c'.nmem zthve (transL li n c₀ ztddq) ∧
      c'.nmem ztm = 1 ∧ c'.nmem ztccv = ztfhy ∧
      zth ∧
      (∀ r, ztofl → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zujq
  set Bn := c.nreg 230002 with hBn
  zumcb
  obtain ⟨hBnA, -⟩ := nfAt_robust_bound hN
  zugfv
  have hlen₀ : (triplesOf N).length = K₀ := by unfold triplesOf; simp_all
  obtain ⟨c₁, k₁, e₁, hk₁, v21, v22, v23, v24, v17, v18, v99, v30, v31, v35, v36, g₁, mm₁,
    rr₁, rm₁, o₁⟩ := fSetup_exec (P := P) c hw (A := A) (Bn := Bn) (K₀ := K₀)
      (CB := c.nmem ztjgx) (b := if li then 1 else 0) rfl rfl hBnA hNA.1 rfl h01 by_omega
  have hlow₁ : ztknx := fun a ha => by
    grind
  have hR := recsT_of_nfAt hN hlow₁
  have hI₁ : FInv c₁.nmem li n c₀ ztddq (c.nmem ztjgx) ztjgk c₁ c₁ :=
    { i_le := by_omega
      rK := by_omega
      r31 := by_omega
      r35 := by rw [v35, v30]; rfl
      r36 := by rw [v36, v30]; rfl
      r10 := by_simp_all
      r14 := by_simp_all
      r15 := by_simp_all
      r16 := by_simp_all
      r17 := v17
      r18 := v18
      fr := fun _ _ => rfl
      rr := rfl
      rm := rfl
      out := rfl
      mem := fun a => by rw [v30]; unfold memT; zuocx }
  have hCB : (triplesOf N).length = 0 ∨
      c.nmem ztjgx + 5 * (triplesOf N).length ≤ A + 6 := by
    rcases Nat.eq_zero_or_pos (triplesOf N).length with h0 | hpos
    · omega
    · right
      have := (nfAt_robust_bound hN).2 ztsyu by_omega
      omega
  obtain ⟨c₂, k₂, e₂, hw₂, hI₂, h30, hk₂, hk₂'⟩ := fLoop_exec (P := P) hR hCB
    by_omega e₁.wb_right hI₁ v30
  rw [hlen₀] at hk₂ hk₂' h30
  have g₂ : ∀ r, zthjr → c₂.nreg r = c₁.nreg r := hI₂.fr
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by_omega, by_omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hI₂.rr.trans rr₁, hI₂.rm.trans rm₁, hI₂.out.trans o₁⟩
  · grind
  · grind
  · rw [hI₂.r36, h30, ← hlen₀, DownBase.rankF_length]; unfold transL; simp
  · show c₂.nreg 9999 = _; grind
  · refine chordListAt_memT (m₀ := c₁.nmem) ztrpw
    rw [hI₂.mem a, h30, hlen₀]
  · zucps
  · zucps
  · zuge
    zucps
  · zujbl
    rw [g₂ r by_omega, g₁ r hr hra]
end exec
end
end DrvT
end Chazelle.Core
namespace Chazelle.Core
namespace DrvT
open Machine Machine.Stmt Programs SignK NFLoc SortL BuildRam
open BuildNF (codeLe)
@[expose] public section
def buildT : Stmt :=
  .seq ztkrb
    (.ifLtN 43250 40002 (.seq phaseA (.seq (.instr (.copyN 190020 30005)) phaseB)) zeroCase)
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 4000000 in
/-- **The build with the event pointer**: the event list `E` at register `190020` and the normal
form `buildNF M Q L E` at register `40003`, both below the allocator. -/
theorem buildT_exec (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) {M : Model} {L : List zte} {D B : ℕ}
    (hwf : ModelDescWF P ztm c.nmem D) (hM : ModelDescAt c.nmem D zta M)
    (hgood : GoodModel M) (hok : ChordTriplesOK M zta L) (hCL : ChordListAt c.nmem B L)
    (hBL : B + 3 * L.length ≤ c.nreg ALLOC) (h0 : c.nreg 40000 = D) (h1 : c.nreg 40001 = B)
    (h2 : c.nreg 40002 = L.length)
    (hcost : c.nreg ALLOC + κBuild * ztbma + 4 ≤ W) :
    ∃ c' k, Exec P W buildT c c' k ∧
      k ≤ κBuild * ztbma + 4 ∧
      (∃ E : List ℕ, E.Perm ztct ∧ E.Pairwise ztwqj ∧
        c'.nreg 190020 + 2 * L.length ≤ c'.nreg ALLOC ∧
        seg c'.nmem (c'.nreg 190020) ztpu = E ∧
        c.nreg ALLOC ≤ c'.nreg 40003 ∧
        NFWithin c'.nmem (c'.nreg 40003) ztdo ztwni) ∧
      (∀ r, bandOf r ∉ ({bBuild, bSort, bSign} : Finset ℕ) → r ≠ ALLOC → r ≠ 190020 →
        c'.nreg r = c.nreg r) ∧
      Frame {bBuild, bSort, bSign, bTrans} c c' k := by
  zuvu
  zuce
  zubfv
  zukau
  have hKX : ztzos := Nat.le_mul_of_pos_right _ by_omega
  zullf
  have hcost' := hcost
  zumvo
  -- the first two instructions
  obtain ⟨c₀, k₀, x₀, hk₀, q20, q50, g₀, m₀⟩ : ∃ c₀ k₀, Exec P W
      ztkrb c c₀ k₀ ∧ k₀ = 2 ∧ c₀.nreg 190020 = 0 ∧
      c₀.nreg 43250 = 0 ∧ (∀ r, r ≠ 190020 → r ≠ 43250 → c₀.nreg r = c.nreg r) ∧
      c₀.nmem = c.nmem ∧ c₀.rreg = c.rreg ∧ c₀.rmem = c.rmem ∧ c₀.output = c.output := by
    exec_block
    · omega
    · omega
    simp_all
  obtain ⟨m₀, rr₀, rm₀, o₀⟩ := m₀
  zugnw
  have hc0A : ztpmq := g₀ 9999 by_norm_num by_norm_num
  by_cases hK : 0 < K
  · -- phase A
    have t₀ : ztmva := by
      simp_all
    obtain ⟨c₁, k₁, x₁, hk₁, w₁, F₁, d1, d2, d3, d4, d5, d6, d7, hrec, e1, e2, E, hE, hperm,
      hsort⟩ := phaseA_exec (P := P) hG hWn c₀ w₀ (M := M) (L := L) (D := D) (B := B)
        by_simp_all by_simp_all hok by_simp_all
        by_omega by_simp_all
        by_simp_all
        by_simp_all
        ztqgj
    zuijl
    -- the event pointer
    zucuf

    have xc := Exec.copyN (P := P) w₁ 190020 30005
    set c₁' : Config := { c₁ with nreg := upd c₁.nreg 190020 (c₁.nreg 30005) } with hc₁'
    have w₁' := xc.wb_right
    have gc : ∀ r, r ≠ 190020 → c₁'.nreg r = c₁.nreg r := fun r hr => by_simp_all
    have v20 : c₁'.nreg 190020 = SE := by_rfl
    zucct
    have hlow₁ : ztfaj := fun a ha => by
      rw [F₁.2.2.1 a by_omega, m₀]
    zuyb

    have hI : BuildNF.Input M zta L E :=
      ⟨walkAx_of_goodModel hgood, hok, hperm,
        BuildNF.sorted_of_codeLe ztqyp hok hperm hsort⟩
    have hCL₁ : ChordListAt c₁.nmem B L := fun i hi => by
      zubxj

    -- phase B
    obtain ⟨c₂, k₂, x₂, hk₂, hk₂', w₂, F₂, h40003, h9999, hlow, hNF⟩ := phaseB_exec (P := P) hG
      hWn c₁' w₁' (M := M) (L := L) (E := E) (D := D) (T := A₀) (SE := SE)
      (B := B) (H := H) hI hK by_grind by_grind
      by_grind by_grind
      by_grind by_grind
      by_grind by_rfl
      by_rfl
      zttto hM₁ hrec by_omega hCL₁ by_omega
      ztnzf by_omega
      ztkvh
    have X : Exec P W buildT c c₂ (k₀ + (k₁ + ztndl + 1)) :=
      .seq x₀ (.ifLtN_true t₀ (.seq x₁ (.seq xc x₂)))
    have h20 : c₂.nreg 190020 = SE := by rw [F₂.1 _ by_rfl, v20]
    refine ⟨c₂, _, X, ?_, ⟨E, hperm, hsort, ?_, ?_, ?_, ?_⟩, fun r hr' hra h19 => ?_, ?_⟩
    · unfold costA at hk₁; unfold κBuild
      grind
    · rw [h20, show c₂.nreg ALLOC = c₂.nreg 9999 from rfl, h9999]; omega
    · zuovl
      rw [← hE]
      zuhav
      zucfh
      grind
    · omega
    · zuexp
    · have h43 : ztppq := by
        zuhgk
      zuctn
    · zuife
      · have hr' : ztbow := fun h => hr (by
          grind)
        have h19 : r ≠ 190020 := by
          zubwx
        have h43 : ztppq := by
          zubwx
        zuctn
      · have hr' : ztbow := fun h => hr (by
          grind)
        rw [exec_frameM2 x₂ wrM2_phaseB r ztuwp, show c₁'.rreg = c₁.rreg from rfl,
          F₁.2.1 r hr', rr₀]
      · grind
      · rw [F₂.2.2.1, show c₁'.rmem = c₁.rmem from rfl,
          F₁.2.2.2.1 a by_omega, rm₀]
      · rw [F₂.2.2.2, show c₁'.output = c₁.output from rfl, F₁.2.2.2.2.1, o₀]
      · show A₀ ≤ c₂.nreg 9999; omega
      · show c₂.nreg 9999 ≤ A₀ + _; omega
  · -- `K = 0`
    zuftn
    have t₀ : ztlbq := by
      simp_all
    obtain ⟨c', k, x, hk, hk', w', F', h40003, h9999, hlow, hNF⟩ := zeroCase_exec (P := P) hWn c₀
      w₀ (M := M) (L := L) (E := []) (D := D) (H := A₀) hK0
      by_simp_all hc0A by_simp_all
      by_simp_all by_nlinarith
    have X : Exec P W buildT c c' (k₀ + ztcnq) := .seq x₀ ztnah
    have h20 : c'.nreg 190020 = 0 := by rw [F'.1 _ by_rfl, q20]
    refine ⟨c', _, X, by zuowf; unfold κBuild; omega, ⟨[], by_grind,
      List.Pairwise.nil, ?_, ?_, ?_, ?_⟩, fun r hr' hra h19 => ?_, ?_⟩
    · omega
    · zuowf; rfl
    · omega
    · zuexp
    · have h43 : ztppq := by
        zuhgk
      zugbw
    · have R' : zteij := fun r hr =>
        (exec_frameM2 x wrM2_zeroCase r hr).trans (by rw [rr₀])
      zuife
      · have hr' : ztbow := fun h => hr (by
          simp_all)
        have h19 : r ≠ 190020 := by
          zubwx
        have h43 : ztppq := by
          zubwx
        zugbw
      · have hr' : ztbow := fun h => hr (by
          simp_all)
        exact R' r ztuwp
      · simp_all
      · rw [F'.2.2.1, rm₀]
      · rw [F'.2.2.2, o₀]
      · show A₀ ≤ c'.nreg 9999; omega
      · show c'.nreg 9999 ≤ A₀ + _; omega
end exec
end
end DrvT
end Chazelle.Core
namespace Chazelle.Core
namespace DrvT
open Machine Machine.Stmt Programs BuildRam
@[expose] public section
def setB : Stmt := block [.copyN 40000 190021, .copyN 40001 190022, .copyN 40002 190036]

/-- The registers `1 … 5` of `bDownDrv`. -/
def finT : Stmt := block [.copyN 210001 190021, .copyN 210002 190022, .copyN 210003 190036,
  .copyN 210004 190020, .copyN 210005 40003]

/-- **The transition procedure.** -/
def transS : Stmt := .seq orientT (.seq c0S (.seq filtS (.seq setB (.seq buildT finT))))

/-- The cost constant of the transition. -/
def κT : ℕ := 1600000000

/-- The registers of `setB`. -/
def BsetB (r : ℕ) : Bool := decide ztngk

/-- The registers of `finT`. -/
def BfinT (r : ℕ) : Bool := decide (210001 ≤ r ∧ r ≤ 210005)
theorem wrM_setB : wrM BsetB setB = true := by_decide
theorem wrM_finT : wrM BfinT finT = true := by_decide
theorem le_gradeGran (g : ℕ) : g ≤ gradeGran g := by
  have : g ≤ g * ztcgu := Nat.le_mul_of_pos_right _ by_omega
  have h1 : ztxpt := rfl
  have h2 : ztlav := rfl
  grind

/-- **The cost of the transition.** -/
theorem trans_cost_le {n K K₀ : ℕ} (hn : 3 ≤ n) (hK : K ≤ K₀)
    (hK₀ : K₀ * ztzma ≤ 840 * ztxfv) :
    (14 * n + 120) + (260 * n + 1950) + (54 * K₀ + 21) + 3 +
      (κBuild * ztwko + 4) + 5 ≤ κT * ztkk := by
  zufak
  have hnp : ztppe := Nat.le_pow_clog by_norm_num _
  have hgp : p ≤ gradeGran p := le_gradeGran p
  have hK₀n : K₀ ≤ 1680 * n := by
    grind
  have hKpow : K ≤ 2 ^ (p + 12) := by
    grind
  have hclog : Nat.clog 2 K ≤ p + 12 := Nat.clog_le_of_le_pow hKpow
  have hKK : K * ztho ≤ 13 * ztzts := by
    calc K * ztho ≤ K * (13 * ztr) := Nat.mul_le_mul_left _ by_omega
      _ ≤ K₀ * (13 * ztfsd) := Nat.mul_le_mul hK by_omega
      _ = 13 * ztzts := by_ring
  unfold κBuild κT
  omega
section exec
variable {P : Polygon} {W : ℕ}
variable (c : Config)
set_option maxHeartbeats 1000000 in
theorem setB_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W setB c c' k ∧ k = 3 ∧ c'.nreg 40000 = c.nreg 190021 ∧
      c'.nreg 40001 = c.nreg 190022 ∧ c'.nreg 40002 = c.nreg 190036 ∧
      FrameM BsetB c c' ∧ c'.nmem = c.nmem := by
  obtain ⟨c', k, e, hk, h1, h2, h3, hm⟩ : ∃ c' k, Exec P W setB c c' k ∧ k = 3 ∧
      c'.nreg 40000 = c.nreg 190021 ∧ c'.nreg 40001 = c.nreg 190022 ∧
      c'.nreg 40002 = c.nreg 190036 ∧ c'.nmem = c.nmem := by
    unfold setB
    exec_block
    simp
  exact ⟨c', k, e, hk, h1, h2, h3, exec_frameM e wrM_setB, hm⟩
set_option maxHeartbeats 1000000 in
theorem finT_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W finT c c' k ∧ k = 5 ∧ c'.nreg 210001 = c.nreg 190021 ∧
      c'.nreg 210002 = c.nreg 190022 ∧ c'.nreg 210003 = c.nreg 190036 ∧
      c'.nreg 210004 = c.nreg 190020 ∧ c'.nreg 210005 = c.nreg 40003 ∧
      FrameM BfinT c c' ∧ c'.nmem = c.nmem := by
  obtain ⟨c', k, e, hk, h1, h2, h3, h4, h5, hm⟩ : ∃ c' k, Exec P W finT c c' k ∧ k = 5 ∧
      c'.nreg 210001 = c.nreg 190021 ∧ c'.nreg 210002 = c.nreg 190022 ∧
      c'.nreg 210003 = c.nreg 190036 ∧ c'.nreg 210004 = c.nreg 190020 ∧
      c'.nreg 210005 = c.nreg 40003 ∧ c'.nmem = c.nmem := by
    unfold finT
    exec_block
    simp
  exact ⟨c', k, e, hk, h1, h2, h3, h4, h5, exec_frameM e wrM_finT, hm⟩
end exec
end
end DrvT
end Chazelle.Core
namespace Chazelle.Core
namespace DrvT
open Machine Machine.Stmt Programs BuildRam
open BuildNF (codeLe)
open SortL (seg)
@[expose] public section
def TransCnt (cnt : ℕ → ℕ) : Prop :=
  ∀ n K K₀ : ℕ, n - 1 ≤ 2 ^ topGrade n →
    K₀ * ztzma ≤ 840 * ztxfv → K ≤ K₀ →
      K * 2 ^ Cost.ceilBeta ztcea ≤
        cnt ztcea * (2 ^ topGrade n + 2 ^ Cost.ceilBeta ztcea)

/-- The count of the driver satisfies the condition. -/
theorem transCnt_cnt {A : ℕ} (hA : 1 ≤ A) (B : ℕ) : TransCnt ztswo :=
  fun _ _ _ hn hK₀ hK => DownMath.cnt_trans hA B hn hK₀ hK
theorem mem_drvBands {b : ℕ} : b ∈ DrvR.drvBands ↔ 1 ≤ b ∧ b ≤ 24 ∧ b ≠ 23 := by
  unfold DrvR.drvBands phaseBands bCore
  grind

/-- A frame of the driver's bands from a write-set frame not touching the allocator. -/
theorem frame_drv {B : ℕ → Bool} {c c' : Config} {k : ℕ} (F : FrameM B c c')
    (hB : ∀ r, B r = true → bandOf r ∈ DrvR.drvBands) (hA : B ALLOC = false)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) : Frame DrvR.drvBands c c' k := by
  have hAA : ztble := F.1 _ hA
  have hnot : ztkoo := fun r hr => by
    grind
  exact ⟨fun r hr _ => F.1 r ztjya, fun r hr => F.2.1 r ztjya, hm,
    fun a _ => by zuowi, F.2.2.2, by rw [hAA], by_omega⟩
theorem band_of_range {r lo : ℕ} (h1 : 10000 * lo ≤ r) (h2 : r < 10000 * lo + 10000) :
    bandOf r = lo := by
  unfold bandOf; omega
section exec
variable {P : Polygon} {W : ℕ}

/-- The `LeftInside` bit as a register value. -/
theorem bit_eq {b : ℕ} {p : Prop} [Decidable p] (hb : b ≤ 1) (h : b = 1 ↔ p) :
    b = if decide p then 1 else 0 := by
  grind
variable {X : MemCtx}
set_option maxHeartbeats 8000000 in
/-- **The transition meets its contract**, for every count function satisfying the
transition count condition. -/
theorem transSpec_of {cnt : ℕ → ℕ} (hcnt : TransCnt cnt) :
    DrvR.TransSpec X cnt := by
  classical
  refine ⟨transS, κT, fun P W c hw hpre hroom => ?_⟩
  obtain ⟨hE, C, N, hC, hNr, hN⟩ := hpre
  obtain ⟨hG, hW3, hWh, -, -, -⟩ := hE
  zuewb
  zucm
  zubp
  zufvx
  have hCm : ztsaw := by have := hC.2.2; omega
  set li := decide ztzce with hli_def
  have hli : ztzjk := decide_eq_true_iff
  -- the math
  obtain ⟨hok, hdeg, hwt, hlen, hcount⟩ := trans_math hG hC hN hli
  set L := transL li P.n ztpe ztddq with hL
  zugfv
  have hFK : (N.F ztc zta).ncard = K₀ := ncard_F hN.1.2.1
  rw [hFK] at hlen hcount
  have hcost := trans_cost_le hn3 hlen hcount
  zujq
  -- 1. the bit
  obtain ⟨c₁, k₁, e₁, hk₁, b1, b2, F₁, m₁⟩ := orientT_exec hG hW3 c hw
  have hb₁ : ztmvc := bit_eq b1 b2
  have hA₁ : ztizl := F₁.1 _ by_decide
  -- 2. the shift
  obtain ⟨c₂, k₂, e₂, hk₂, v10, v14, v15, v16, v01, F₂, m₂⟩ :=
    c0S_exec hG hWh hC (li := li) c₁ e₁.wb_right hb₁ by_omega
  have hA₂ : ztlyb := by rw [F₂.1 _ by_decide, hA₁]
  have hcore₂ : c₂.nreg 230002 = c.nreg ztvlu := by
    rw [F₂.1 _ by_decide, F₁.1 _ by_decide]; rfl
  have hlow₂ : ztkny := fun a ha => by
    simp_all
  have hNr₂ : Robust zthwb c₂.nmem (fun m => NFAt m (c₂.nreg 230002) N) := by
    rw [hA₂, hcore₂]; exact hNr.transport hlow₂
  -- 3. the filter
  obtain ⟨c₃, k₃, e₃, hk₃, hk₃', f21, f22, f36, f99, fCL, fD0, fD1, fmem, fg, frr, frm, fo⟩ :=
    filtS_exec c₂ e₂.wb_right (n := P.n) (c₀ := c0 C li) hNr₂ v01 by_omega
      v14 by_omega v16 by_omega
  rw [hA₂] at f21 f22 f99 fCL fD0 fD1 fmem
  -- 4. the inputs of the build
  obtain ⟨c₄, k₄, e₄, hk₄, s0, s1, s2, F₄, m₄⟩ := setB_exec (P := P) c₃ e₃.wb_right
  have hA₄ : c₄.nreg ALLOC = A + 6 + 3 * K₀ := by rw [F₄.1 _ by_decide, f99]
  have hlenK : L.length ≤ K₀ := by
    omega
  -- 5. the build
  have hdesc : ModelDescAt c₄.nmem A zta ztwiq := by
    right
    grind
  obtain ⟨c₅, k₅, e₅, hk₅, ⟨E, hperm, hsort, hE1, hE2, hNB, hNF⟩, g₅, F₅⟩ :=
    buildT_exec hG hWh c₄ e₄.wb_right (M := interiorModel zta) (L := L) (D := A)
      (B := A + 6) (by zuovw; exact ⟨by_omega, fun h => by_grind⟩)
      hdesc (Or.inr ⟨_, hQ, rfl⟩) hok by_grind by_omega
      by_omega by_omega by_grind
      by_omega
  -- 6. the registers of the driver
  obtain ⟨c₆, k₆, e₆, hk₆, w1, w2, w3, w4, w5, F₆, m₆⟩ := finT_exec (P := P) c₅ e₅.wb_right
  have hA₆ : ztfkx := F₆.1 _ by_decide
  have h5 : ∀ r, 190021 ≤ r → r ≤ 190036 → c₅.nreg r = c₄.nreg r := fun r h1 h2 =>
    g₅ r (by rw [band_of_range (lo := 19) by_omega by_omega]; decide)
      ztu by_omega
  have r1 : c₆.nreg 210001 = A := by
    rw [w1, h5 _ by_norm_num by_norm_num, F₄.1 _ by_decide, f21]
  have r2 : c₆.nreg 210002 = A + 6 := by
    rw [w2, h5 _ by_norm_num by_norm_num, F₄.1 _ by_decide, f22]
  have r3 : c₆.nreg 210003 = L.length := by
    rw [w3, h5 _ by_norm_num by_norm_num, F₄.1 _ by_decide, f36]
  have hA₅ : c₄.nreg ALLOC ≤ c₅.nreg ALLOC := F₅.2.2.2.2.2.1
  have hlow₅ : ∀ a, a < c₄.nreg ALLOC → c₆.nmem a = c₃.nmem a := fun a ha => by
    rw [m₆, F₅.2.2.1 a ha, m₄]
  refine ⟨c₆, k₁ + zthim,
    .seq e₁ ztfv, ?_, ?_, ?_⟩
  · -- the cost
    show _ ≤ κT * ztju
    omega
  · -- the invariant `Inv(p)`
    show c₆.nreg 210001 + 6 ≤ c₆.nreg ALLOC ∧ _
    refine ⟨by_grind, ?_, L, E, ?_, ?_, ?_, ?_, ?_, hok, hperm, hsort, ?_, ?_, ?_,
      ?_⟩
    · show Robust zthwe c₆.nmem (fun m => ModelDescAt m (c₆.nreg 210001) zta
        ztwiq)
      zumov
      zubxa
      have e0 : m' A = c₄.nmem A := by
        rw [hm' A by_grind, hlow₅ A by_omega, m₄]
      have e1 : m' ztbo = c₄.nmem ztbo := by
        rw [hm' ztbo by_grind, hlow₅ ztbo by_omega, m₄]
      rcases hdesc with ⟨h0, -⟩ | ⟨h0, h1, h2⟩
      · grind
      · exact Or.inr ⟨by_omega, by_grind, h2⟩
    · show c₆.nreg 210003 = L.length; exact r3
    · show c₆.nreg 210002 + 3 * L.length ≤ c₆.nreg ALLOC
      grind
    · show Robust zthwe c₆.nmem (fun m => ChordListAt m (c₆.nreg 210002) L)
      rw [r2]
      zulng
      obtain ⟨a1, a2, a3⟩ := fCL i hi
      have hq : ∀ q, q < 3 → m' ztlds = c₃.nmem ztlds := fun q hq => by
        rw [hm' _ by_grind, hlow₅ _ by_grind]
      zusk
      · have := hq 0 by_norm_num; grind
      · rw [hq 1 by_norm_num]; exact a2
      · rw [hq 2 by_norm_num]; exact a3
    · show c₆.nreg 210004 + 2 * L.length ≤ c₆.nreg ALLOC
      omega
    · show Robust zthwe c₆.nmem (fun m => seg m ztqkt ztpu = E)
      zunsh
      zubxa
      rw [← hE2]
      zuhav
      zucfh
      grind
    · show NFWithin c₆.nmem (c₆.nreg 210005) zthwe _
      grind
    · zukpd
    · zukpd
    · exact hcnt P.n L.length K₀ zttav hcount hlenK
  · -- the frame
    have G₁ : ztmtc := frame_drv F₁ (fun r hr => by
        unfold B19 at hr; zvmwo at hr
        zunkb; omega)
      by_decide ztfrk
    have G₂ : ztiyg := frame_drv F₂ (fun r hr => by
        unfold Bc0 Brute.Bm B19 WalkKey.Bk at hr
        zufw
        rw [mem_drvBands]; unfold bandOf; omega)
      by_decide m₂
    have G₃ : ztmtd := by
      refine ⟨fun r hr hra => fg r ?_ hra, fun r _ => by rw [frr], fun a ha => fmem a
        by_grind, fun a _ => by rw [frm], fo, by_omega,
        by omega⟩
      zux

      exact hr (by zunkb; omega)
    have G₄ : ztsbi := frame_drv F₄ (fun r hr => by
        unfold BsetB at hr; zvmwo at hr
        rw [band_of_range (lo := 4) by_omega by_omega, mem_drvBands]; omega)
      by_decide (fun a _ => by rw [m₄])
    have G₅ : Frame DrvR.drvBands c₄ c₅ k₅ := F₅.mono (by
        decide) le_rfl
    have G₆ : Frame DrvR.drvBands c₅ c₆ k₆ := frame_drv F₆ (fun r hr => by
        unfold BfinT at hr; zvmwo at hr
        rw [band_of_range (lo := 21) by_omega by_omega, mem_drvBands]; omega)
      by_decide (fun a _ => by rw [m₆])
    have := G₁.trans (G₂.trans (G₃.trans (G₄.trans (G₅.trans G₆))))
    grind

/-- **The transition contract** for the count function of the driver. -/
theorem transSpec {A : ℕ} (hA : 1 ≤ A) (B : ℕ) :
    DrvR.TransSpec X ztswo :=
  transSpec_of (transCnt_cnt hA B)
end exec
end
end DrvT
end Chazelle.Core
section
set_option hygiene false
local macro "zqbjn" : tactic => `(tactic| obtain ⟨c', k, ex, hk, hR⟩ := he by_omega)
local macro "zqbjp" : tactic => `(tactic| obtain ⟨c', k, ex, hk, hR⟩ := ht by_omega)
set_option hygiene true

/-!
# Down-phase pieces (D4), part 6: dropping the wall-to-wall chords

`dropS` runs over the `K₀` chord records of the normal form at `218015` (chord area `CB`, five
words per record), reads `(h, lp, rp)` and appends the triple at the write cursor unless both
ends are on the side walls of the box (`BoxT.WallRec`: walk edges `1`, `3`).  The list
`BoxT.dropWalls (triples)` is written at the allocator `B'` (base into `218016`, length into
`218017`), and the allocator is raised past it (`dropS_exec`).

Registers: loop `218070` record index, `218071` read cursor, `218072 … 218074` the triple,
`218075` write cursor, `218076` kept count, `218077` the wall flag; `218078 = K₀`, constants
`218079 = 2`, `218080 = 4` (and `218020 = 0`, `218021 = 1`).
-/
namespace Chazelle.Core
namespace DrvP
open Machine Machine.Stmt Programs BuildRam
open DownBase (rankF tw)
@[expose] public section
def isOT (p : ℕ) (t e : Stmt) : Stmt :=
  .ifLtN p 218021 e (.ifLtN p 218079 t (.ifLtN 218079 p (.ifLtN p 218080 t e) e))

/-- Load the triple at the read cursor, advance it by `5`, clear the flag. -/
def dLoad : Stmt := block [.loadN 218072 218071, .addN 218071 218071 218021,
  .loadN 218073 218071, .addN 218071 218071 218021, .loadN 218074 218071,
  .addN 218071 218071 218021, .addN 218071 218071 218021, .addN 218071 218071 218021,
  .constN 218077 0]

/-- The wall flag. -/
def dTest : Stmt := isOT 218073 (isOT 218074 ztifx .skip) .skip

/-- Append the triple. -/
def dKeep : Stmt := block [.storeN 218075 218072, .addN 218075 218075 218021,
  .storeN 218075 218073, .addN 218075 218075 218021, .storeN 218075 218074,
  .addN 218075 218075 218021, .addN 218076 218076 218021]

/-- One record. -/
def dBody : Stmt := .seq dLoad (.seq dTest (.seq ztprr
  (block [.addN 218070 218070 218021])))

/-- The pass. -/
def dLoop : Stmt := .whileLtN 218070 218078 dBody

/-- The setup: `K₀`, `CB`, the cursors and the base of the list at the allocator. -/
def dSetup : Stmt := block [.constN 218079 2, .constN 218080 4, .loadN 218078 218015,
  .addN 218071 218015 218079, .addN 218071 218071 218021, .loadN 218071 218071,
  .copyN 218075 ALLOC, .copyN 218016 ALLOC, .constN 218076 0, .constN 218070 0]

/-- The end: the length, and the allocator past the list. -/
def dFin : Stmt := block [.copyN 218017 218076, .copyN ALLOC 218075]

/-- **The wall filter.** -/
def dropS : Stmt := .seq dSetup (.seq dLoop dFin)

/-! ## The memory of the pass -/

/-- The kept records. -/
def keepW (x : ℕ × ℕ × ℕ) : Bool := !decide (BoxT.WallRec x)
theorem dropWalls_eq (L : List zte) : BoxT.dropWalls L = L.filter keepW := rfl

/-- The memory after `i` records: the kept triples so far at `B'`. -/
def memD (m₀ : ℕ → ℕ) (L₀ : List zte) (B' i a : ℕ) : ℕ :=
  if B' ≤ a ∧ a < B' + 3 * rankF keepW L₀ i then tw (L₀.filter keepW) ztjnv else m₀ a
theorem memD_keep {m₀ m : ℕ → ℕ} {L₀ : List zte} {B' i : ℕ}
    (hm : ∀ a, m a = memD m₀ L₀ B' i a) (hi : i < L₀.length)
    (hk : keepW ztwtp = true) (a : ℕ) :
    (if a = B' + 3 * rankF keepW L₀ i + 2 then (L₀.getD i ztt).2.2
      else if a = B' + 3 * rankF keepW L₀ i + 1 then (L₀.getD i ztt).2.1
      else if a = B' + 3 * rankF keepW L₀ i then (L₀.getD i ztt).1
      else m a) = memD m₀ L₀ B' (i + 1) a := by
  zuizb
  zueyo
  zuhoh
  have hg := DownBase.getD_filter_rank keepW ztt hi hk
  zuezw
  have htw : ∀ s, s < 3 → tw _ _ =
      if s = 0 then (L₀.getD i ztt).1
      else if s = 1 then (L₀.getD i ztt).2.1
      else (L₀.getD i ztt).2.2 := fun s hs => by
    zuqd

  zubyr
  unfold memD
  zubim
  zuccp
  · subst h3
    rw [ite_eq_left rfl, ite_eq_left by_omega, show B' + 3 * j + 2 - B' = 3 * j + 2 by omega,
      htw 2 by_norm_num]
    zulav
  zuccq
  · subst h4
    rw [ite_eq_right h3, ite_eq_left rfl, ite_eq_left by_omega, show B' + 3 * j + 1 - B' = 3 * j + 1 by omega,
      htw 1 by_norm_num]
    zulav
  zucup
  · subst h5
    rw [ite_eq_right h3, ite_eq_right h4, ite_eq_left rfl, ite_eq_left by_omega,
      show B' + 3 * j - B' = 3 * j + 0 by omega, htw 0 by_norm_num]
    zulav
  grind
theorem memD_drop {m₀ : ℕ → ℕ} {L₀ : List zte} {B' i : ℕ}
    (hi : i < L₀.length) (hk : keepW ztwtp = false) (a : ℕ) :
    memD m₀ L₀ B' i a = memD m₀ L₀ B' ztg a := by
  zuizb
  zugdz
  zunu
  unfold memD; zvnel

/-! ## The pieces of one record -/
section exec
variable {P : Polygon} {W : ℕ}

/-- **The test `p ∈ {1, 3}`.** -/
theorem isOT_exec (c : Config) {p : ℕ} {t e : Stmt} {K : ℕ} {R : Config → Prop}
    (h21 : c.nreg 218021 = 1) (h79 : c.nreg 218079 = 2) (h80 : c.nreg 218080 = 4)
    (ht : ztllr → ∃ c' k, Exec P W t c c' k ∧ k ≤ K ∧ R c')
    (he : ¬ ztllr → ∃ c' k, Exec P W e c c' k ∧ k ≤ K ∧ R c') :
    ∃ c' k, Exec P W (isOT p t e) c c' k ∧ k ≤ K + 7 ∧ R c' := by
  unfold isOT
  by_cases g1 : c.nreg p < c.nreg 218021
  · zqbjn
    exact ⟨c', _, .ifLtN_true g1 ex, by_omega, hR⟩
  by_cases g2 : c.nreg p < c.nreg 218079
  · zqbjp
    exact ⟨c', _, .ifLtN_false g1 ztsph, by_omega, hR⟩
  by_cases g3 : c.nreg 218079 < c.nreg p
  · by_cases g4 : c.nreg p < c.nreg 218080
    · zqbjp
      exact ⟨c', _, .ifLtN_false g1 (.ifLtN_false g2 (.ifLtN_true g3 (.ifLtN_true g4 ex))),
        by omega, hR⟩
    · zqbjn
      exact ⟨c', _, .ifLtN_false g1 (.ifLtN_false g2 (.ifLtN_true g3 (.ifLtN_false g4 ex))),
        by omega, hR⟩
  · zqbjn
    exact ⟨c', _, .ifLtN_false g1 (.ifLtN_false g2 (.ifLtN_false g3 ex)), by_omega, hR⟩

/-- **The wall flag.** -/
theorem dTest_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) (h21 : c.nreg 218021 = 1)
    (h79 : c.nreg 218079 = 2) (h80 : c.nreg 218080 = 4) (h77 : c.nreg 218077 = 0) :
    ∃ c' k, Exec P W dTest c c' k ∧ k ≤ 22 ∧
      (c'.nreg 218077 = if BoxT.WallRec (c.nreg 218072, c.nreg 218073, c.nreg 218074) then 1
        else 0) ∧
      ztbiw ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hset : ∃ c' k, Exec P W _ c c' k ∧ k ≤ 1 ∧
      (c'.nreg 218077 = 1 ∧ ztbiw ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) :=
    ⟨_, _, Exec.constN hw 218077 1 hW, le_rfl, by_simp, by_simp_all, rfl, rfl, rfl,
      rfl⟩
  have hskip : ∃ c' k, Exec P W .skip c c' k ∧ k ≤ 8 ∧
      (c'.nreg 218077 = 0 ∧ ztbiw ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) :=
    ⟨c, 0, .skip hw, by_omega, h77, by_omega, rfl, rfl, rfl, rfl⟩
  unfold dTest BoxT.WallRec
  zubi
  by_cases hl : c.nreg 218073 = 1 ∨ c.nreg 218073 = 3
  · by_cases hr : c.nreg 218074 = 1 ∨ c.nreg 218074 = 3
    · zubek
      obtain ⟨c₁, k₁, ex₁, hk₁, h₁⟩ := isOT_exec (P := P) (W := W) c
        (t := .instr (.constN 218077 1)) (K := 8)
        (R := fun c' => c'.nreg 218077 = 1 ∧ ztbiw ∧
          c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output)
        h21 h79 h80 by_grind
        (absurd hr)
      obtain ⟨c', k, ex, hk, h⟩ := isOT_exec c
        (t := isOT 218074 _ .skip) (e := .skip)
        (R := fun c' => c'.nreg 218077 = 1 ∧ ztbiw ∧
          c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output)
        h21 h79 h80 zthwu ztveh
      grind
    · zufa
      obtain ⟨c₁, k₁, ex₁, hk₁, h₁⟩ := isOT_exec c
        h21 h79 h80 (fun h' => absurd h' hr) ztrpu
      obtain ⟨c', k, ex, hk, h⟩ := isOT_exec c
        (t := isOT 218074 ztifx .skip) (e := .skip)
        (R := fun c' => c'.nreg 218077 = 0 ∧ ztbiw ∧
          c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output)
        h21 h79 h80 zthwu ztveh
      grind
  · zufa
    obtain ⟨c', k, ex, hk, h⟩ := isOT_exec c
      (t := isOT 218074 ztifx .skip)
      h21 h79 h80 (fun h' => absurd h' hl) ztrpu
    grind
set_option maxHeartbeats 4000000 in
theorem dLoad_exec (c : Config) (hw : WordsBounded W c) {a : ℕ} (h71 : c.nreg 218071 = a)
    (h21 : c.nreg 218021 = 1) (haW : a + 5 ≤ W) :
    ∃ c' k, Exec P W dLoad c c' k ∧ k = 9 ∧ c'.nreg 218072 = c.nmem a ∧
      c'.nreg 218073 = c.nmem ztdf ∧ c'.nreg 218074 = c.nmem ztvj ∧
      c'.nreg 218071 = a + 5 ∧ c'.nreg 218077 = 0 ∧
      (∀ r, r ≠ 218071 → r ≠ 218072 → r ≠ 218073 → r ≠ 218074 → r ≠ 218077 →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  unfold dLoad
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Config.nreg_mk, Machine.upd_same,
    Machine.upd_other, h71, h21]; omega)
  simp_all
set_option maxHeartbeats 4000000 in
/-- **Append a triple.** -/
theorem dKeep_exec (c : Config) (hw : WordsBounded W c) {w j : ℕ} (h75 : c.nreg 218075 = w)
    (h76 : c.nreg 218076 = j) (h21 : c.nreg 218021 = 1) (hwW : w + 3 ≤ W) (hjW : j + 1 ≤ W) :
    ∃ c' k, Exec P W dKeep c c' k ∧ k = 7 ∧ c'.nreg 218075 = w + 3 ∧ c'.nreg 218076 = j + 1 ∧
      (∀ r, r ≠ 218075 → r ≠ 218076 → c'.nreg r = c.nreg r) ∧
      (∀ a, c'.nmem a = if a = w + 2 then c.nreg 218074 else if a = w + 1 then c.nreg 218073
        else if a = w then c.nreg 218072 else c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dKeep
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Config.nreg_mk, Machine.upd_same,
    Machine.upd_other, h75, h76, h21]; omega)
  refine zteza
  all_goals simp (disch := omega) only [Config.nreg_mk, Config.nmem_mk, Machine.upd_same,
    Machine.upd_other, h75, h76, h21]
  rfl

/-! ## The loop -/

/-- **The invariant of the wall filter.** -/
structure DInv (m₀ : ℕ → ℕ) (L₀ : List zte) (CB B' : ℕ) (cI d : Config) : Prop where
  i_le : d.nreg 218070 ≤ L₀.length
  rK : d.nreg 218078 = L₀.length
  r71 : d.nreg 218071 = CB + 5 * d.nreg 218070
  r75 : d.nreg 218075 = B' + 3 * rankF keepW L₀ ztqll
  r76 : d.nreg 218076 = rankF keepW L₀ ztqll
  r21 : d.nreg 218021 = 1
  r79 : d.nreg 218079 = 2
  r80 : d.nreg 218080 = 4
  fr : ∀ r, ztofo → d.nreg r = cI.nreg r
  rr : d.rreg = cI.rreg
  rm : d.rmem = cI.rmem
  out : d.output = cI.output
  mem : ∀ a, d.nmem a = memD m₀ L₀ B' ztqll a
variable {m₀ : ℕ → ℕ} {L₀ : List (ℕ × ℕ × ℕ)} {CB B' : ℕ}
set_option maxHeartbeats 8000000 in
/-- **One record.** -/
theorem dBody_exec
    (hR : DrvT.RecsT m₀ CB L₀) (hCB : L₀.length = 0 ∨ CB + 5 * L₀.length ≤ B')
    (hBW : B' + 3 * L₀.length + 3 ≤ W) {cI d : Config} (hw : WordsBounded W d)
    (hI : DInv m₀ L₀ CB B' cI d) (ht : d.nreg 218070 < d.nreg 218078) :
    ∃ d' k, Exec P W dBody d d' k ∧ WordsBounded W d' ∧ DInv m₀ L₀ CB B' cI d' ∧
      d'.nreg 218070 = d.nreg 218070 + 1 ∧ 3 ≤ k ∧ k ≤ 41 := by
  zufnc

  set i := d.nreg 218070 with hi
  zuiol
  zuhoh
  have hle := DownBase.rankF_le keepW L₀ i
  zufki
  have hmL : ztdxt := fun q hq => by
    zuocy; unfold memD; grind
  zudk
  clear hCB
  -- load
  obtain ⟨d₁, k₁, e₁, hk₁, v72, v73, v74, v71, v77, r₁, m₁, rr₁, rm₁, o₁⟩ :=
    dLoad_exec (P := P) d hw hI.r71 hI.r21 by_omega
  rw [← hi] at v72 v73 v74 v71
  zucdc

  rw [hm0, l1] at v72
  rw [hmL 1 by_norm_num, l2] at v73
  rw [hmL 2 by_norm_num, l3] at v74
  have g₁ : ∀ r, (r < 218071 ∨ 218077 < r) → d₁.nreg r = d.nreg r := by_grind
  -- the test
  obtain ⟨d₂, k₂, e₂, hk₂, v₂, r₂, m₂, rr₂, rm₂, o₂⟩ := dTest_exec (P := P) d₁ e₁.wb_right hW1
    (by rw [g₁ _ by_norm_num, hI.r21]) (by rw [g₁ _ by_norm_num, hI.r79])
    (by rw [g₁ _ by_norm_num, hI.r80]) v77
  rw [v72, v73, v74] at v₂
  have hx3 : ((x.1, x.2.1, x.2.2) : ℕ × ℕ × ℕ) = x := rfl
  rw [hx3] at v₂
  have g5 : ∀ r, r ≠ 218071 → r ≠ 218072 → r ≠ 218073 → r ≠ 218074 → r ≠ 218077 →
      d₂.nreg r = d.nreg r := by_grind
  have e72 : d₂.nreg 218072 = x.1 := by_grind
  have e73 : d₂.nreg 218073 = x.2.1 := by_grind
  have e74 : d₂.nreg 218074 = x.2.2 := by_grind
  have hm5 : ztmvn := by_grind
  -- the branch
  obtain ⟨d₆, k₆, e₆, hk₆, hk₆', g6, mem6, n75, n76, rr₆, rm₆, o₆⟩ : ∃ d₆ k₆,
      Exec P W ztprr d₂ d₆ k₆ ∧ 1 ≤ k₆ ∧ k₆ ≤ 8 ∧
      (∀ r, r ≠ 218075 → r ≠ 218076 → d₆.nreg r = d₂.nreg r) ∧
      (∀ a, d₆.nmem a = memD m₀ L₀ B' ztg a) ∧
      d₆.nreg 218075 = B' + 3 * rankF keepW L₀ ztg ∧
      d₆.nreg 218076 = rankF keepW L₀ ztg ∧
      d₆.rreg = d₂.rreg ∧ d₆.rmem = d₂.rmem ∧ d₆.output = d₂.output := by
    have h21 : d₂.nreg 218021 = 1 := by
      rw [g5 _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num, hI.r21]
    have h75 : d₂.nreg 218075 = B' + 3 * j := by
      rw [g5 _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num, hI.r75]
    have h76 : d₂.nreg 218076 = j := by
      rw [g5 _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num, hI.r76]
    have hr := DownBase.rankF_succ keepW ztt ht
    cases hk : keepW x
    · have hwall : BoxT.WallRec x := by
        zulbv
      rw [ite_eq_left hwall] at v₂
      have hn : ¬ d₂.nreg 218077 < d₂.nreg 218021 := by_omega
      zuvt
      zunu
      refine ⟨d₂, _, .ifLtN_false hn ztdyc, by_omega, by_omega,
        by omega, fun a => ?_, by_omega, by_omega, rfl, rfl, rfl⟩
      zugvc
      exact memD_drop ht by_omega a
    · have hwall : ¬ BoxT.WallRec x := by
        zulbv
      rw [ite_eq_right hwall] at v₂
      have hp : d₂.nreg 218077 < d₂.nreg 218021 := by_omega
      have hjK : ztsjl := by
        omega
      obtain ⟨d₆, k₆, e₆', hk₆, w75, w76, r₆, mm₆, rr₆, rm₆, o₆⟩ :=
        dKeep_exec d₂ e₂.wb_right h75 h76 h21 by_omega by_omega
      zuvt
      zufbp
      refine ⟨d₆, _, .ifLtN_true hp e₆', by_omega, by_omega, r₆, fun a => ?_,
        by omega, by_omega, rr₆, rm₆, o₆⟩
      rw [mm₆, e72, e73, e74, hm5]
      have := memD_keep (hI.mem) ht
        by_omega a
      omega
  -- the increment
  have h70 : d₆.nreg 218070 = i := by
    grind
  have h21' : d₆.nreg 218021 = 1 := by
    rw [g6 _ by_norm_num by_norm_num, g5 _ by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num, hI.r21]
  have e₇ := Exec.addN (P := P) e₆.wb_right 218070 218070 218021 by_omega
  set d₇ : Config := { d₆ with nreg := upd d₆.nreg 218070 _ }
    with hd₇
  have g7 : ∀ r, r ≠ 218070 → d₇.nreg r = d₆.nreg r := fun r hr => by zunsa; zumwy
  have v7 : d₇.nreg 218070 = i + 1 := by zunsa; simp [h70, h21']
  have g : ∀ r, ztofo → d₇.nreg r = d.nreg r := fun r hr => by
    grind
  have X' : Exec P W dBody d d₇ (k₁ + (k₂ + zttrk)) :=
    .seq e₁ (.seq e₂ (.seq e₆ ztowx))
  refine zthmx
  refine ⟨by_omega, by zunhi, ?_, ?_, ?_,
    by grind, by rw [g _ by_norm_num, hI.r79],
    by rw [g _ by_norm_num, hI.r80],
    fun r hr => by zunac, ?_, ?_, ?_, fun a => ?_⟩
  · grind
  · grind
  · grind
  · show d₆.rreg = cI.rreg; rw [rr₆, rr₂, rr₁, hI.rr]
  · show d₆.rmem = cI.rmem; rw [rm₆, rm₂, rm₁, hI.rm]
  · show d₆.output = cI.output; rw [o₆, o₂, o₁, hI.out]
  grind

/-- **The pass.** -/
theorem dLoop_exec
    (hR : DrvT.RecsT m₀ CB L₀) (hCB : L₀.length = 0 ∨ CB + 5 * L₀.length ≤ B')
    (hBW : B' + 3 * L₀.length + 3 ≤ W) {cI d : Config} (hw : WordsBounded W d)
    (hI : DInv m₀ L₀ CB B' cI d) (h0 : d.nreg 218070 = 0) :
    ∃ d' k, Exec P W dLoop d d' k ∧ WordsBounded W d' ∧ DInv m₀ L₀ CB B' cI d' ∧
      d'.nreg 218070 = L₀.length ∧ 3 * L₀.length ≤ k ∧ k ≤ 43 * L₀.length + 2 := by
  obtain ⟨d', k, e, ⟨hw', hI'⟩, htest, hk, hψ⟩ := SortR.whileLtN_potential_lb (P := P) (W := W)
    (a := 218070) (b := 218078) (body := dBody)
    (fun d => WordsBounded W d ∧ DInv m₀ L₀ CB B' cI d)
    (fun d => 43 * (L₀.length - d.nreg 218070)) (fun d => 3 * d.nreg 218070) ztoe
    (fun d ⟨hwd, hId⟩ ht => by
      obtain ⟨d', k, e, hw', hI', hi', hk1, hk2⟩ := dBody_exec hR hCB hBW hwd hId ht
      have := hId.rK
      refine ztkkq
      · omega
      omega)
    ⟨hw, hI⟩
  zucdb

  · omega
  omega
end exec

/-- The list of a full pass, in memory. -/
theorem chordListAt_memD {m₀ m : ℕ → ℕ} {L₀ : List zte} {B' : ℕ}
    (hm : ∀ a, m a = memD m₀ L₀ B' L₀.length a) :
    ChordListAt m B' ztuwx := by
  have hlen : rankF keepW L₀ L₀.length = (BoxT.dropWalls L₀).length := by
    zuovt; rfl
  zun
  have hq : ∀ q, q < 3 → m ztnjj = tw ztuwx ztpue := by
    zuco
    zvmwi; unfold memD; rw [hlen, ite_eq_left by_omega, show B' + 3 * j + q - B' = 3 * j + q by
      omega]; rfl
  zusk
  · have := hq 0 by_norm_num; rw [Nat.add_zero, Nat.add_zero] at this; zvmwk
    zumvi
  · zugvj

  · zugvk
section exec2
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 8000000 in
theorem dSetup_exec (c : Config) (hw : WordsBounded W c) {A B₀ K₀ CB : ℕ}
    (hA : c.nreg 9999 = A) (hB : c.nreg 218015 = B₀) (hBA : B₀ + 11 < A)
    (hK : c.nmem B₀ = K₀) (hCB : c.nmem ztjhd = CB) (h21 : c.nreg 218021 = 1)
    (hAW : A + 4 ≤ W) :
    ∃ c' k, Exec P W dSetup c c' k ∧ k = 10 ∧ c'.nreg 218079 = 2 ∧ c'.nreg 218080 = 4 ∧
      c'.nreg 218078 = K₀ ∧ c'.nreg 218071 = CB ∧ c'.nreg 218075 = A ∧ c'.nreg 218016 = A ∧
      c'.nreg 218076 = 0 ∧ c'.nreg 218070 = 0 ∧
      (∀ r, r ≠ 218016 → ztofp → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dSetup
  zufsx
  zui
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Config.nreg_mk, Config.nmem_mk, Machine.upd_same,
    Machine.upd_other, hA, hB, hK, hCB, h21]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r a1 a2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals simp (disch := omega) only [Config.nreg_mk, Config.nmem_mk, Machine.upd_same,
    Machine.upd_other, hA, hB, hK, hCB, h21]
set_option maxHeartbeats 4000000 in
/-- **The wall filter.** -/
theorem dropS_exec (c : Config) (hw : WordsBounded W c) {N : NF}
    (hN : Robust ztm c.nmem (fun m => NFAt m (c.nreg 218015) N))
    (h21 : c.nreg 218021 = 1) (hroom : c.nreg ALLOC + 3 * N.chords.length + 20 ≤ W) :
    ∃ c' k, Exec P W dropS c c' k ∧
      3 * (BoxT.dropWalls ztdyk).length ≤ k ∧ k ≤ 43 * N.chords.length + 20 ∧
      c'.nreg 218016 = c.nreg ALLOC ∧
      c'.nreg 218017 = (BoxT.dropWalls ztdyk).length ∧
      c'.nreg ALLOC = c.nreg ALLOC + 3 * (BoxT.dropWalls ztdyk).length ∧
      ChordListAt c'.nmem ztm (BoxT.dropWalls ztdyk) ∧
      zth ∧
      (∀ r, r ≠ 218016 → r ≠ 218017 → ztofp → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zujq
  set B₀ := c.nreg 218015 with hB₀
  zumcb
  obtain ⟨hBA, -⟩ := DrvT.nfAt_robust_bound hN
  zugfv
  have hlen₀ : (DrvT.triplesOf N).length = K₀ := by unfold DrvT.triplesOf; simp_all
  obtain ⟨c₁, k₁, e₁, hk₁, v79, v80, v78, v71, v75, v16, v76, v70, g₁, mm₁, rr₁, rm₁, o₁⟩ :=
    dSetup_exec (P := P) c hw (A := A) (B₀ := B₀) (K₀ := K₀) (CB := c.nmem ztjhd) rfl rfl
      hBA hNA.1 rfl h21 by_omega
  have hR := DrvT.recsT_of_nfAt hN (m' := c₁.nmem) by_simp_all
  have hI₁ : DInv c₁.nmem ztdyk (c.nmem ztjhd) A c₁ c₁ :=
    { i_le := by_omega
      rK := by_omega
      r71 := by_omega
      r75 := by rw [v75, v70]; rfl
      r76 := by rw [v76, v70]; rfl
      r21 := by_simp_all
      r79 := v79
      r80 := v80
      fr := by_omega
      rr := rfl
      rm := rfl
      out := rfl
      mem := fun a => by zunru; unfold memD; zuocx }
  have hCB : (DrvT.triplesOf N).length = 0 ∨
      c.nmem ztjhd + 5 * (DrvT.triplesOf N).length ≤ A := by
    rcases Nat.eq_zero_or_pos (DrvT.triplesOf N).length with h0 | hpos
    · omega
    · right
      have := (DrvT.nfAt_robust_bound hN).2 ztsyu by_omega
      omega
  obtain ⟨c₂, k₂, e₂, hw₂, hI₂, h70, hk₂, hk₂'⟩ := dLoop_exec (P := P) hR hCB
    by_omega e₁.wb_right hI₁ v70
  rw [hlen₀] at hk₂ hk₂' h70
  have g₂ := hI₂.fr
  have hcnt : c₂.nreg 218076 = (BoxT.dropWalls ztdyk).length := by
    rw [hI₂.r76, h70, ← hlen₀, DownBase.rankF_length]; rfl
  have hcur : c₂.nreg 218075 = A + 3 * (BoxT.dropWalls ztdyk).length := by
    rw [hI₂.r75, h70, ← hlen₀, DownBase.rankF_length]; rfl
  have hKle : (BoxT.dropWalls ztdyk).length ≤ K₀ := by
    rw [← hlen₀]; exact List.length_filter_le _ _
  -- the end
  obtain ⟨c₃, k₃, e₃, hk₃, v17, v99, r₃, m₃⟩ : ∃ c₃ k₃, Exec P W dFin c₂ c₃ k₃ ∧ k₃ = 2 ∧
      c₃.nreg 218017 = (BoxT.dropWalls ztdyk).length ∧
      c₃.nreg ALLOC = A + 3 * (BoxT.dropWalls ztdyk).length ∧
      (∀ r, r ≠ 218017 → r ≠ ALLOC → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    unfold dFin
    zufsx
    zui
    exec_block
    simp_all
  obtain ⟨m₃, hr₃, hrm₃, ho₃⟩ := m₃
  have ex : Exec P W dropS c c₃ _ := .seq e₁ ztcr
  refine ⟨c₃, _, ex, by_omega, by_omega, ?_, v17, v99, ?_, fun a ha => ?_, fun r h1 h2 h3 h4 => ?_,
    by rw [hr₃, hI₂.rr, rr₁], by rw [hrm₃, hI₂.rm, rm₁], by rw [ho₃, hI₂.out, o₁]⟩
  · rw [r₃ _ by_norm_num by_decide, g₂ _ by_norm_num, v16]
  · zumzp
    refine chordListAt_memD (m₀ := c₁.nmem) ztrpw
    rw [hI₂.mem a, h70, hlen₀]
  · rw [m₃, hI₂.mem, h70]; unfold memD; grind
  grind
