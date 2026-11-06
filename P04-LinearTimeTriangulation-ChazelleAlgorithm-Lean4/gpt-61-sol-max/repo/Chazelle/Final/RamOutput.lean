module

public import Chazelle.Final.Assemble
public import Chazelle.Final.Transfer
public import Chazelle.Final.RamPieceTri
public import Chazelle.Final.RamSplit

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

/-! ### Cycles of a representation -/

theorem disj_of_nodup_flatten {cs : List (List ℕ)} (h : cs.flatten.Nodup) {c d : List ℕ}
    (hc : c ∈ cs) (hd : d ∈ cs) (hne : c ≠ d) {y : ℕ} (hy : y ∈ c) : y ∉ d := by
  induction cs with
  | nil => simp_all
  | cons a rest ih =>
    rw [List.flatten_cons, List.nodup_append] at h
    obtain ⟨-, h2, h3⟩ := h
    rcases List.mem_cons.1 hc with rfl | hc' <;> rcases List.mem_cons.1 hd with rfl | hd'
    · simp_all
    · intro hyd
      exact h3 y hy y (List.mem_flatten.2 ⟨d, hd', hyd⟩) rfl
    · intro hyd
      exact h3 y hyd y (List.mem_flatten.2 ⟨c, hc', hy⟩) rfl
    grind

/-- Nonempty lists with a duplicate-free concatenation are pairwise distinct. -/
theorem nodup_of_nodup_flatten {cs : List (List ℕ)} (h : cs.flatten.Nodup)
    (hne : ∀ c ∈ cs, c ≠ []) : cs.Nodup := by
  induction cs with
  | nil => simp_all
  | cons a rest ih =>
    have h' := h
    rw [List.flatten_cons, List.nodup_append] at h'
    obtain ⟨-, h2, h3⟩ := h'
    refine List.nodup_cons.2 ⟨fun ha => ?_, ih h2 fun c hc => hne c (List.mem_cons_of_mem _ hc)⟩
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil a (hne a List.mem_cons_self)
    exact h3 y hy y (List.mem_flatten.2 ⟨a, ha, hy⟩) rfl

section
variable {S : LState} {cs : List (List ℕ)} (hR : Repr S cs)
include S cs hR
/-- The cycles of a representation are pairwise distinct. -/
theorem Repr.nodup_cs : cs.Nodup :=
  nodup_of_nodup_flatten hR.nodup fun c hc => (hR.cyc c hc).1

/-- Distinct cycles of a representation are disjoint. -/
theorem Repr.disj {c d : List ℕ}
    (hc : c ∈ cs) (hd : d ∈ cs) (hne : c ≠ d) {y : ℕ} (hy : y ∈ c) : y ∉ d :=
  disj_of_nodup_flatten hR.nodup hc hd hne hy

/-- Every node lies on a cycle of the representation. -/
theorem Repr.exists_cyc {y : ℕ}
    (hy : y < S.cnt) : ∃ c ∈ cs, y ∈ c := by
  obtain ⟨c, hc, hyc⟩ := List.mem_flatten.1 ((hR.mem y).2 hy)
  grind

section
variable {c : List ℕ} (hc : c ∈ cs)
include c hc
/-- The members of the cycles are nodes. -/
theorem Repr.lt_cnt {y : ℕ} (hy : y ∈ c) : y < S.cnt :=
  (hR.mem y).1 (List.mem_flatten.2 ⟨c, hc, hy⟩)

/-- A cycle of a representation has no repeated node. -/
theorem Repr.nodup_cyc : c.Nodup :=
  (List.nodup_flatten.1 hR.nodup).1 c hc



end

end

/-- The node sequence read in memory is the successor iteration. -/
theorem nodeSeq_eq_iterate {mem : ℕ → ℕ} {NB : ℕ} {S : LState} {c : List ℕ} (hc : IsCyc S c)
    (hmem : ∀ y ∈ c, mem (NB + y) = S.nxt y) {i : ℕ} (hi : i < c.length) :
    ∀ s, nodeSeq mem NB (c.getD i 0) s = c.getD ((i + s) % c.length) 0 := by
  have hl : 0 < c.length := by omega
  intro s
  induction s with
  | zero => rw [nodeSeq_zero, Nat.add_zero, Nat.mod_eq_of_lt hi]
  | succ s ih =>
    rw [nodeSeq_succ, ih, hmem _ (getD_mem_of_lt (Nat.mod_lt _ hl)),
      (hc.2 _ (Nat.mod_lt _ hl)).1, Nat.mod_add_mod, Nat.add_assoc]

/-- The walk from position `i` of a cycle, read as vertices. -/
theorem walk_map_getD {S : LState} {c : List ℕ} (hc : IsCyc S c) {i : ℕ} (hi : i < c.length)
    {s : ℕ} (hs : s < c.length) :
    ((walk S (c.getD i 0) c.length).map S.vtx).getD s 0 = S.vtx (c.getD ((i + s) % c.length) 0) := by
  rw [walk_eq_rotate hc hi, List.map_rotate, getD_rotate_of_lt i (by simp_all),
    List.length_map, getD_map_of_lt S.vtx (Nat.mod_lt _ (by omega)), Nat.add_comm s i]

/-! ### Counting marks -/

/-- Marking the (distinct, previously unmarked) positions of `c` lowers the number of unmarked
positions by `c.length`. -/
theorem countP_mark {NN : ℕ} {f g : ℕ → ℕ} {c : List ℕ} (hc : c.Nodup) (hlt : ∀ y ∈ c, y < NN)
    (hf : ∀ y ∈ c, f y = 0) (hg1 : ∀ y ∈ c, g y = 1) (hg2 : ∀ y < NN, y ∉ c → g y = f y) :
    (List.range NN).countP (fun y => decide (g y = 0)) + c.length =
      (List.range NN).countP (fun y => decide (f y = 0)) := by
  classical
  rw [List.countP_eq_countP_filter_add (List.range NN) (fun y => decide (g y = 0))
      (fun y => decide (y ∈ c)),
    List.countP_eq_countP_filter_add (List.range NN) (fun y => decide (f y = 0))
      (fun y => decide (y ∈ c))]
  have hlen : ((List.range NN).filter fun y => decide (y ∈ c)).length = c.length := by
    have hp : ((List.range NN).filter fun y => decide (y ∈ c)).Perm c := by
      rw [List.perm_ext_iff_of_nodup ((List.nodup_range).filter _) hc]
      simp_all
    exact hp.length_eq
  have h1 : ((List.range NN).filter fun y => decide (y ∈ c)).countP
      (fun y => decide (g y = 0)) = 0 := by
    simp_all
  have h2 : ((List.range NN).filter fun y => decide (y ∈ c)).countP
      (fun y => decide (f y = 0)) = c.length := by
    rw [← hlen, List.countP_eq_length]
    simp_all
  have h3 : ((List.range NN).filter fun y => !decide (y ∈ c)).countP
      (fun y => decide (g y = 0)) =
      ((List.range NN).filter fun y => !decide (y ∈ c)).countP (fun y => decide (f y = 0)) := by
    apply List.countP_congr
    simp_all
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
  WordsBounded W c ∧ c.nreg 242 ≤ NN ∧ (∀ y < c.nreg 242, c.nmem (MB + y) = 0) ∧
    (∀ r, r ≠ 242 → r ≠ 248 → c.nreg r = c₀.nreg r) ∧ c.rreg = c₀.rreg ∧
    (∀ t, (t < MB ∨ MB + NN ≤ t) → c.nmem t = c₀.nmem t) ∧ c.rmem = c₀.rmem ∧
    c.output = c₀.output

/-- One iteration of the mark-clearing loop. -/
theorem clearBody_inv {MB NN : ℕ} {c₀ : Config} (h240 : c₀.nreg 240 = NN)
    (h241 : c₀.nreg 241 = MB) (h243 : c₀.nreg 243 = 0) (h244 : c₀.nreg 244 = 1)
    (hW : MB + NN ≤ W) (c : Config) (hI : ClearInv W MB NN c₀ c) (ht : c.nreg 242 < c.nreg 240) :
    ∃ c' k, Exec P W clearBody c c' k ∧ ClearInv W MB NN c₀ c' ∧ k ≤ 3 ∧
      NN - c'.nreg 242 < NN - c.nreg 242 := by
  obtain ⟨hw, hi, hz, hfn, hfr, hnm, hrm, hout⟩ := hI
  have e240 : c.nreg 240 = NN := by simp_all
  have e241 : c.nreg 241 = MB := by simp_all
  have e243 : c.nreg 243 = 0 := by simp_all
  have e244 : c.nreg 244 = 1 := by simp_all
  rw [e240] at ht
  unfold clearBody
  exec_block
  · omega
  · config_simp; omega
  refine ⟨⟨‹_›, ?_, fun v hv => ?_, fun r h1 h2 => ?_, hfr, fun t ht' => ?_, hrm, hout⟩,
    by omega, ?_⟩
  · config_simp; omega
  · grind [Machine.upd_apply]
  · config_simp; simp only [Machine.upd_apply, h1, h2, ite_false]; simp_all
  · config_simp
    rw [e241, Machine.upd_other _ _ _ (by omega)]
    grind
  · config_simp; omega

/-- The invariant of the walk around the cycle `d` from position `i` (`z = d[i]`), relative to
the configuration `c₀` before the cycle is marked. -/
def RingInv (W MB NN : ℕ) (d : List ℕ) (i : ℕ) (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ 1 ≤ c.nreg 247 ∧ c.nreg 247 ≤ d.length ∧
    c.nreg 246 = d.getD ((i + c.nreg 247) % d.length) 0 ∧ c.nreg 245 = c.nmem (MB + c.nreg 246) ∧
    (∀ y < NN, c.nmem (MB + y) =
      if ∃ s < c.nreg 247, y = d.getD ((i + s) % d.length) 0 then 1 else c₀.nmem (MB + y)) ∧
    (∀ r, r ≠ 245 → r ≠ 246 → r ≠ 247 → r ≠ 248 → c.nreg r = c₀.nreg r) ∧ c.rreg = c₀.rreg ∧
    (∀ t, (t < MB ∨ MB + NN ≤ t) → c.nmem t = c₀.nmem t) ∧ c.rmem = c₀.rmem ∧
    c.output = c₀.output

/-- The node at position `(i + s) % len` of a duplicate-free cycle determines `s < len`. -/
theorem getD_cyc_inj {d : List ℕ} (hd : d.Nodup) {i s s' : ℕ} (hs : s < d.length)
    (hs' : s' < d.length) (h : d.getD ((i + s) % d.length) 0 = d.getD ((i + s') % d.length) 0) :
    s = s' := by
  have hl : 0 < d.length := by omega
  have e := getD_inj_of_nodup hd (Nat.mod_lt _ hl) (Nat.mod_lt _ hl) h
  have hm : i + s ≡ i + s' [MOD d.length] := e
  exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' i hm) hs hs'

/-- One step of the walk around a cycle preserves `RingInv`. -/
theorem ringBody_inv {MB NN NB : ℕ} {S : LState} {d : List ℕ} {i : ℕ} {c₀ : Config}
    (hcyc : IsCyc S d) (_hnd : d.Nodup) (_hi : i < d.length) (hdlt : ∀ y ∈ d, y < NN)
    (hlen : d.length ≤ NN) (_hd0 : ∀ y ∈ d, c₀.nmem (MB + y) = 0) (hnxt : ∀ y < NN, c₀.nmem (NB + y) = S.nxt y)
    (hNB : NB + NN ≤ MB) (hW : MB + NN ≤ W)
    (h241 : c₀.nreg 241 = MB) (h244 : c₀.nreg 244 = 1) (h249 : c₀.nreg 249 = NB)
    (c : Config) (hI : RingInv W MB NN d i c₀ c) (ht : c.nreg 245 < c.nreg 244) :
    ∃ c' k, Exec P W ringBody c c' k ∧ RingInv W MB NN d i c₀ c' ∧ k ≤ 7 ∧
      d.length - c'.nreg 247 < d.length - c.nreg 247 := by
  obtain ⟨hw, hm1, hml, h246, h245, hmark, hfn, hfr, hnm, hrm, hout⟩ := hI
  have hl : 0 < d.length := by omega
  have e241 : c.nreg 241 = MB := by
    rw [hfn 241 (by decide) (by decide) (by decide) (by decide), h241]
  have e244 : c.nreg 244 = 1 := by
    rw [hfn 244 (by decide) (by decide) (by decide) (by decide), h244]
  have e249 : c.nreg 249 = NB := by
    rw [hfn 249 (by decide) (by decide) (by decide) (by decide), h249]
  set m := c.nreg 247 with hmdef
  set x := d.getD ((i + m) % d.length) 0 with hx
  have hxd : x ∈ d := getD_mem_of_lt (Nat.mod_lt _ hl)
  have hxN : x < NN := hdlt x hxd
  -- the test: `x` is unmarked, so `m < len`
  have hmlt : m < d.length := by
    by_contra hge
    have hm : m = d.length := by omega
    have : c.nmem (MB + x) = 1 := by
      rw [hmark x hxN, ite_eq_left ⟨0, by omega, by rw [hx, hm, Nat.add_zero, Nat.add_mod_right]⟩]
    grind
  have hnx : c.nmem (NB + x) = S.nxt x := by rw [hnm _ (by omega)]; grind
  have hx' : S.nxt x = d.getD ((i + (m + 1)) % d.length) 0 := by
    rw [hx, (hcyc.2 _ (Nat.mod_lt _ hl)).1, Nat.mod_add_mod, Nat.add_assoc]
  unfold ringBody
  exec_block
  · omega
  · config_simp; omega
  · config_simp; omega
  · config_simp
    rw [e249, e241, h246, Machine.upd_other _ _ _ (by omega), hnx, hx']
    have := hdlt _ (getD_mem_of_lt (Nat.mod_lt (i + (m + 1)) hl))
    omega
  refine ⟨⟨‹_›, ?_, ?_, ?_, ?_, fun y hy => ?_, fun r h1 h2 h3 h4 => ?_, hfr, fun t ht' => ?_,
    hrm, hout⟩, by omega, ?_⟩
  · config_simp; omega
  · config_simp; omega
  · config_simp
    rw [e249, e241, h246, e244, Machine.upd_other _ _ _ (by omega), hnx, hx']
  · config_simp; rw [e241]
  · config_simp
    rw [e241, h246, e244]
    by_cases hyx : y = x
    · rw [hyx, Machine.upd_same, ite_eq_left ⟨m, by omega, hx⟩]
    · rw [Machine.upd_other _ _ _ (by omega), hmark y hy]
      by_cases hex : ∃ s < m, y = d.getD ((i + s) % d.length) 0
      · obtain ⟨s, hs, hys⟩ := hex
        rw [ite_eq_left ⟨s, hs, hys⟩, ite_eq_left ⟨s, by omega, hys⟩]
      · rw [ite_eq_right hex, ite_eq_right]
        rintro ⟨s, hs, hys⟩
        by_cases hsm : s = m
        · grind
        · exact hex ⟨s, by omega, hys⟩
  · config_simp; simp only [Machine.upd_apply, h1, h2, h3, h4, ite_false]
    grind
  · config_simp
    rw [e241, h246, Machine.upd_other _ _ _ (by  omega)]
    grind
  · config_simp; omega

/-- The positions `(i + s) % len`, `s < len`, enumerate the cycle. -/
theorem exists_pos_iff {d : List ℕ} {i : ℕ} (hi : i < d.length) (y : ℕ) :
    (∃ s < d.length, y = d.getD ((i + s) % d.length) 0) ↔ y ∈ d := by
  have hl : 0 < d.length := by omega
  constructor
  · rintro ⟨s, -, rfl⟩; exact getD_mem_of_lt (Nat.mod_lt _ hl)
  · intro hy
    obtain ⟨j, hj, rfl⟩ := exists_getD_of_mem hy
    refine ⟨(j + d.length - i) % d.length, Nat.mod_lt _ hl, ?_⟩
    rw [Nat.add_mod_mod, show i + (j + d.length - i) = j + d.length by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hj]

/-- The standing hypotheses of the output pass. -/
structure OutCtx (P Q : Polygon) (W : ℕ) (S : LState) (cs : List (List ℕ))
    (NN MB NB VB WB : ℕ) : Prop where
  simple : Q.Simple
  shear : ∃ ε, Q = Core.shear ε P ∧ Core.YlexAgree P Q
  enum : ∃ D, Split.EnumDiags Q D ∧
    List.Perm (cs.map (List.map S.vtx)) (Split.splitAll (List.range Q.n) D)
  repr : Repr S cs
  cnt : S.cnt = NN
  lay1 : VB + NN ≤ MB
  lay2 : NB + NN ≤ MB
  lay3 : MB + NN ≤ WB
  lay4 : WB + 4 * NN ≤ W

/-- The node bands in memory. -/
def Bands (mem : ℕ → ℕ) (S : LState) (NN NB VB : ℕ) : Prop :=
  ∀ y < NN, mem (VB + y) = S.vtx y ∧ mem (NB + y) = S.nxt y

set_option maxHeartbeats 1000000 in
/-- **Spec of one piece**: mark the cycle `d` of `z = d[i]` (unmarked), and triangulate it. -/
theorem pieceOut_exec {Q : Polygon} {S : LState} {cs : List (List ℕ)} {NN MB NB VB WB : ℕ}
    (hX : OutCtx P Q W S cs NN MB NB VB WB) {d : List ℕ} (hd : d ∈ cs) {i : ℕ}
    (hi : i < d.length) (c : Config) (hc : WordsBounded W c) (hB : Bands c.nmem S NN NB VB)
    (_h240 : c.nreg 240 = NN) (h241 : c.nreg 241 = MB) (h242 : c.nreg 242 = d.getD i 0)
    (_h243 : c.nreg 243 = 0) (h244 : c.nreg 244 = 1) (h249 : c.nreg 249 = NB)
    (h250 : c.nreg 250 = VB) (h251 : c.nreg 251 = WB) (hd0 : ∀ y ∈ d, c.nmem (MB + y) = 0) :
    ∃ c' k, Exec P W pieceOut c c' k ∧ k ≤ 121 * d.length + 44 ∧
      (∀ y < NN, c'.nmem (MB + y) = if y ∈ d then 1 else c.nmem (MB + y)) ∧
      (∃ T, WeakTriangulates (subPoly Q ((walk S (d.getD i 0) d.length).map S.vtx)) T ∧
        c'.output = c.output ++ T.map (relabelList ((walk S (d.getD i 0) d.length).map S.vtx))) ∧
      (∀ r, (r < 60 ∨ (94 < r ∧ r < 245) ∨ 248 < r) → c'.nreg r = c.nreg r) ∧
      (∀ t, (t < MB ∨ MB + NN ≤ t) → (t < WB ∨ WB + 4 * NN ≤ t) → c'.nmem t = c.nmem t) := by
  classical
  obtain ⟨hQ, ⟨ε, hQe, hag⟩, ⟨D, hD, hp⟩, hR, hcnt, hl1, hl2, hl3, hl4⟩ := hX
  have hcyc := hR.cyc d hd
  have hnd := hR.nodup_cyc hd
  have hl : 0 < d.length := by omega
  have hdlt : ∀ y ∈ d, y < NN := fun y hy => hcnt ▸ hR.lt_cnt hd hy
  have hlen : d.length ≤ NN := by
    have := (List.subperm_of_subset hnd (fun y hy => List.mem_range.2 (hdlt y hy))).length_le
    simp_all
  set z := d.getD i 0 with hz
  have hzd : z ∈ d := getD_mem_of_lt hi
  have hzN : z < NN := hdlt z hzd
  have hx1 : S.nxt z = d.getD ((i + 1) % d.length) 0 := by
    rw [hz, (hcyc.2 i hi).1]
  unfold pieceOut
  refine spec_seq ?_
  exec_block
  · omega
  · omega
  · config_simp; omega
  · config_simp
    rw [h249, h242, h241, Machine.upd_other _ _ _ (by omega), (hB z hzN).2, hx1]
    have := hdlt _ (getD_mem_of_lt (Nat.mod_lt (i + 1) hl))
    omega
  refine spec_name fun c₁ hc₁ => ?_
  have hw₁ : WordsBounded W c₁ := by grind
  have hI₁ : RingInv W MB NN d i c c₁ := by
    refine ⟨hw₁, ?_, ?_, ?_, ?_, fun y hy => ?_, fun r h1 h2 h3 h4 => ?_, ?_, fun t ht => ?_, ?_,
      ?_⟩
    · rw [hc₁]; simp
    · rw [hc₁]; config_simp; omega
    · rw [hc₁]; config_simp
      rw [h249, h242, h241, Machine.upd_other _ _ _ (by omega), (hB z hzN).2, hx1]
    · rw [hc₁]; config_simp; rw [h241]
    · rw [hc₁]; config_simp
      rw [h241, h242, h244]
      by_cases hyz : y = z
      · rw [hyz, Machine.upd_same, ite_eq_left ⟨0, by omega, by rw [Nat.add_zero, Nat.mod_eq_of_lt hi]⟩]
      · rw [Machine.upd_other _ _ _ (by omega), ite_eq_right]
        rintro ⟨s, hs, hys⟩
        have : s = 0 := by omega
        subst this
        rw [Nat.add_zero, Nat.mod_eq_of_lt hi] at hys
        omega
    · rw [hc₁]; config_simp; simp only [Machine.upd_apply, h1, h2, h3, h4, ite_false]
    · rw [hc₁]
    · rw [hc₁]; config_simp; rw [h241, h242, Machine.upd_other _ _ _ (by omega)]
    all_goals grind
  have hnxt : ∀ y < NN, c.nmem (NB + y) = S.nxt y := fun y hy => (hB y hy).2
  obtain ⟨c₂, k₂, ex₂, ⟨hw₂, hm1, hml, h246, h245, hmark, hfn₂, hfr₂, hnm₂, hrm₂, hout₂⟩, hexit₂,
    hk₂⟩ := Exec.whileLtN_bounded (P := P) (RingInv W MB NN d i c) (fun d' => d.length - d'.nreg 247)
      7 (fun _ h => h.1) (fun d' hd' ht => ringBody_inv hcyc hnd hi hdlt hlen hd0 hnxt hl2
        (by omega) h241 h244 h249 d' hd' ht) hI₁
  unfold ringLoop
  refine spec_seq ⟨c₂, k₂, ex₂, ?_⟩
  have e244₂ : c₂.nreg 244 = 1 := by
    rw [hfn₂ 244 (by decide) (by decide) (by decide) (by decide), h244]
  have hmeq : c₂.nreg 247 = d.length := by
    by_contra hne
    have hlt : c₂.nreg 247 < d.length := by omega
    set x := d.getD ((i + c₂.nreg 247) % d.length) 0 with hx
    have hxd : x ∈ d := getD_mem_of_lt (Nat.mod_lt _ hl)
    have hmx : c₂.nmem (MB + x) = 0 := by
      rw [hmark x (hdlt x hxd), ite_eq_right, hd0 x hxd]
      rintro ⟨s, hs, hxs⟩
      have := getD_cyc_inj hnd hlt (by omega) hxs
      omega
    grind
  have hmark₂ : ∀ y < NN, c₂.nmem (MB + y) = if y ∈ d then 1 else c.nmem (MB + y) := by
    intro y hy
    rw [hmark y hy, hmeq]
    by_cases h : y ∈ d
    · rw [ite_eq_left ((exists_pos_iff hi y).2 h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h ((exists_pos_iff hi y).1 h')), ite_eq_right h]
  have e242 : c₂.nreg 242 = z := by
    rw [hfn₂ 242 (by decide) (by decide) (by decide) (by decide), h242]
  refine spec_seq ?_
  exec_block
  refine spec_name fun c₃ hc₃ => ?_
  have hw₃ : WordsBounded W c₃ := by grind
  set l := (walk S z d.length).map S.vtx with hldef
  have hll : l.length = d.length := by rw [hldef, List.length_map, walk_eq_rotate hcyc hi,
    List.length_rotate]
  have hmem₃ : c₃.nmem = c₂.nmem := by rw [hc₃]
  have e80 : c₃.nreg 80 = NB := by
    rw [hc₃]; config_simp; rw [hfn₂ 249 (by decide) (by decide) (by decide) (by decide), h249]
  have e81 : c₃.nreg 81 = VB := by
    rw [hc₃]; config_simp; rw [hfn₂ 250 (by decide) (by decide) (by decide) (by decide), h250]
  have e82 : c₃.nreg 82 = z := by rw [hc₃]; config_simp; exact e242
  have e83 : c₃.nreg 83 = d.length := by rw [hc₃]; config_simp; exact hmeq
  have e84 : c₃.nreg 84 = WB := by
    rw [hc₃]; config_simp; rw [hfn₂ 251 (by decide) (by decide) (by decide) (by decide), h251]
  have hband₃ : ∀ y < NN, c₃.nmem (VB + y) = S.vtx y ∧ c₃.nmem (NB + y) = S.nxt y := by
    intro y hy
    rw [hmem₃, hnm₂ _ (by omega), hnm₂ _ (by omega)]
    exact hB y hy
  have hseq : ∀ s, nodeSeq c₃.nmem NB z s = d.getD ((i + s) % d.length) 0 :=
    nodeSeq_eq_iterate hcyc (fun y hy => (hband₃ y (hdlt y hy)).2) hi
  have hseqN : ∀ s, nodeSeq c₃.nmem NB z s < NN := fun s => by
    rw [hseq]; exact hdlt _ (getD_mem_of_lt (Nat.mod_lt _ hl))
  have hin : PieceInput W l c₃ := by
    refine ⟨by omega, ?_, fun s hs => ?_, fun s _ => ?_, fun s _ => ?_, fun s _ => ?_,
      fun s _ => ?_, ?_⟩ <;> (try simp only [e80, e81, e82, e84])
    · rw [hll, hseq, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
    · rw [hll] at hs
      rw [(hband₃ _ (hseqN s)).1, hseq, hldef, walk_map_getD hcyc hi hs]
    · have := hseqN s; omega
    · have := hseqN s; omega
    · have := hseqN s; left; omega
    · have := hseqN s; left; omega
    · rw [hll]; omega
  -- the piece: a mountain in `Q`, hence (transfer) in `P`
  have hpiece : IsPiece Q l := isPiece_walk hQ hD hR hp hd hi
  have hQn : Q.n = P.n := by rw [hQe]; exact Core.shear_n ε P
  have hmount := mountain_transfer (P := P) (ε := ε) (by rw [← hQe]; exact hag)
    (fun x hx => hQn ▸ hpiece.lt x hx) (by rw [← hQe]; exact Chazelle.Mountain.piece_isMountain hQ hpiece)
  obtain ⟨c₄, k₄, ex₄, hk₄, ⟨T, hT, hout₄⟩, hfn₄, -, hnm₄, -⟩ :=
    pieceTri_exec (P := P) (W := W) hmount c₃ hw₃ hin
  refine ⟨c₄, k₄, ex₄, ?_, fun y hy => ?_, ⟨T, ?_, ?_⟩, fun r hr => ?_, fun t ht1 ht2 => ?_⟩
  · have e : c₁.nreg 247 = 1 := by rw [hc₁]; config_simp
    rw [e] at hk₂
    rw [hll] at hk₄
    have : 9 * (d.length - 1) + 2 ≤ 9 * d.length := by omega
    omega
  · rw [hnm₄ _ (by rw [e84, hll]; omega), hmem₃, hmark₂ y hy]
  · rw [hQe, subPoly_shear]; exact weakTriangulates_shear ε hT
  · rw [hout₄, hc₃]; config_simp; rw [hout₂]
  · rw [hfn₄ r (by omega), hc₃]; config_simp
    simp only [Machine.upd_apply, show r ≠ 80 by omega, show r ≠ 81 by omega,
      show r ≠ 82 by omega, show r ≠ 83 by omega, show r ≠ 84 by omega, ite_false]
    rw [hfn₂ r (by omega) (by omega) (by omega) (by omega)]
  · rw [hnm₄ _ (by rw [e84, hll]; omega), hmem₃, hnm₂ t ht1]

open Classical in
/-- The invariant of the output loop, relative to its entry configuration `c₀`: the cycles
`done` containing a node `< z` have been marked and triangulated, in the order of `acc`. -/
def OutInv (Q : Polygon) (W : ℕ) (S : LState) (cs : List (List ℕ)) (NN MB NB VB WB : ℕ)
    (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ c.nreg 242 ≤ NN ∧ c.nreg 240 = NN ∧ c.nreg 241 = MB ∧ c.nreg 243 = 0 ∧
    c.nreg 244 = 1 ∧ c.nreg 249 = NB ∧ c.nreg 250 = VB ∧ c.nreg 251 = WB ∧
    Bands c.nmem S NN NB VB ∧
    ∃ done : List (List ℕ), done.Nodup ∧ (∀ d ∈ done, d ∈ cs) ∧
      (∀ d ∈ cs, d ∈ done ↔ ∃ y ∈ d, y < c.nreg 242) ∧
      (∀ y < NN, c.nmem (MB + y) = if ∃ d ∈ done, y ∈ d then 1 else 0) ∧
      ∃ acc : List (List ℕ × List Polygon.Triangle),
        List.Forall₂ (fun d p => ∃ r, p.1 = (d.map S.vtx).rotate r) done acc ∧
        (∀ p ∈ acc, WeakTriangulates (subPoly Q p.1) p.2) ∧
        c.output = c₀.output ++ acc.flatMap (fun p => p.2.map (relabelList p.1))

/-- The potential of the output loop. -/
def outPot (NN MB : ℕ) (c : Config) : ℕ :=
  70 * (NN - c.nreg 242) + 130 * (List.range NN).countP (fun y => decide (c.nmem (MB + y) = 0))

set_option maxHeartbeats 1000000 in
theorem outBody_inv {Q : Polygon} {S : LState} {cs : List (List ℕ)} {NN MB NB VB WB : ℕ}
    (hX : OutCtx P Q W S cs NN MB NB VB WB) {c₀ : Config} (c : Config)
    (hI : OutInv Q W S cs NN MB NB VB WB c₀ c) (ht : c.nreg 242 < c.nreg 240) :
    ∃ c' k, Exec P W outBody c c' k ∧ OutInv Q W S cs NN MB NB VB WB c₀ c' ∧
      outPot NN MB c' + k + 2 ≤ outPot NN MB c := by
  classical
  obtain ⟨hw, hz, h240, h241, h243, h244, h249, h250, h251, hB, done, hdn, hdcs, hdiff, hmark, acc,
    hF, hT, hout⟩ := hI
  have hR := hX.repr
  have hcnt := hX.cnt
  rw [h240] at ht
  set z := c.nreg 242 with hzdef
  have hl3 := hX.lay3
  have hl4 := hX.lay4
  unfold outBody
  refine spec_seq ?_
  exec_block
  · omega
  refine spec_name fun c₁ hc₁ => ?_
  have hw₁ : WordsBounded W c₁ := by grind
  have r1 : ∀ r, r ≠ 245 → r ≠ 248 → c₁.nreg r = c.nreg r := by
    intro r a b; rw [hc₁]; config_simp; simp only [Machine.upd_apply, a, b, ite_false]
  have e245 : c₁.nreg 245 = c.nmem (MB + z) := by rw [hc₁]; config_simp; rw [h241]
  have hmem₁ : c₁.nmem = c.nmem := by rw [hc₁]
  by_cases hmz : ∃ d ∈ done, z ∈ d
  · -- already marked: skip
    have hm1 : c.nmem (MB + z) = 1 := by grind
    have e244 := r1 244 (by decide) (by decide)
    refine spec_seq (spec_ifLtN_false (by omega) (spec_skip hw₁ ?_))
    exec_block
    · grind
    refine ⟨⟨‹_›, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, done, hdn, hdcs, fun d hd => ?_,
      fun y hy => ?_, acc, hF, hT, ?_⟩, ?_⟩
    all_goals first
      | (config_simp; rw [r1 _ (by decide) (by decide)]; assumption)
      | skip
    · config_simp; rw [r1 242 (by decide) (by decide), r1 244 (by decide) (by decide), h244]
      omega
    · config_simp; rw [hmem₁]; exact hB
    · config_simp
      rw [r1 242 (by decide) (by decide), r1 244 (by decide) (by decide), h244, hdiff d hd]
      constructor
      · rintro ⟨y, hy, hyz⟩; exact ⟨y, hy, by omega⟩
      · rintro ⟨y, hy, hyz⟩
        by_cases hyz' : y < z
        · exact ⟨y, hy, hyz'⟩
        · have hyz'' : y = z := by omega
          subst hyz''
          obtain ⟨d', hd', hzd'⟩ := hmz
          by_cases hdd : d = d'
          · subst hdd
            exact (hdiff d hd).1 hd'
          · exact absurd hy (hR.disj (hdcs d' hd') hd (Ne.symm hdd) hzd')
    · config_simp; rw [hmem₁]; exact hmark y hy
    · config_simp; rw [hc₁]; exact hout
    · unfold outPot
      config_simp
      rw [r1 242 (by decide) (by decide), r1 244 (by decide) (by decide), h244, hmem₁]
      omega
  · -- a new cycle
    have hm0 : c.nmem (MB + z) = 0 := by grind
    obtain ⟨d, hd, hzd⟩ := hR.exists_cyc (y := z) (by omega)
    have hdnd : d ∉ done := fun h => hmz ⟨d, h, hzd⟩
    obtain ⟨i, hi, hdi⟩ := exists_getD_of_mem hzd
    have hd0 : ∀ y ∈ d, c.nmem (MB + y) = 0 := by
      intro y hy
      rw [hmark y (hcnt ▸ hR.lt_cnt hd hy), ite_eq_right]
      rintro ⟨d', hd', hyd'⟩
      by_cases hdd : d = d'
      · grind
      · exact hR.disj hd (hdcs d' hd') hdd hy hyd'
    have e244 := r1 244 (by decide) (by decide)
    refine spec_seq (spec_ifLtN_true (by omega) ?_)
    refine spec_use (pieceOut_exec hX hd hi c₁ hw₁ (by rw [hmem₁]; exact hB)
      (by rw [r1 240 (by decide) (by decide), h240])
      (by rw [r1 241 (by decide) (by decide), h241])
      (by rw [r1 242 (by decide) (by decide), hdi])
      (by rw [r1 243 (by decide) (by decide), h243])
      (by rw [r1 244 (by decide) (by decide), h244])
      (by rw [r1 249 (by decide) (by decide), h249])
      (by rw [r1 250 (by decide) (by decide), h250])
      (by rw [r1 251 (by decide) (by decide), h251])
      (fun y hy => by rw [hmem₁]; exact hd0 y hy)) ?_
    rintro c₂ k₂ hk₂ hw₂ ⟨hmark₂, ⟨T, hT₂, hout₂⟩, hfn₂, hnm₂⟩
    have R2 : ∀ r, (r < 60 ∨ (94 < r ∧ r < 245) ∨ 248 < r) → c₂.nreg r = c.nreg r := by
      intro r hr; rw [hfn₂ r hr, r1 r (by omega) (by omega)]
    exec_block
    · rw [R2 242 (by omega), R2 244 (by omega), h244]; omega
    have hlenN : d.length ≤ NN := by
      have := (List.subperm_of_subset (hR.nodup_cyc hd)
        (fun y hy => List.mem_range.2 (hcnt ▸ hR.lt_cnt hd hy))).length_le
      rwa [List.length_range] at this
    have hcntm := countP_mark (NN := NN) (f := fun y => c.nmem (MB + y))
      (g := fun y => c₂.nmem (MB + y)) (c := d) (hR.nodup_cyc hd)
      (fun y hy => hcnt ▸ hR.lt_cnt hd hy) hd0
      (fun y hy => by rw [hmark₂ y (hcnt ▸ hR.lt_cnt hd hy), ite_eq_left hy])
      (fun y hy hyd => by rw [hmark₂ y hy, ite_eq_right hyd, hmem₁])
    refine ⟨⟨‹_›, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, done ++ [d], ?_, ?_, fun d' hd' => ?_,
      fun y hy => ?_, acc ++ [((walk S (d.getD i 0) d.length).map S.vtx, T)], ?_, ?_, ?_⟩, ?_⟩
    · config_simp; rw [R2 242 (by omega), R2 244 (by omega), h244]; omega
    · config_simp; rw [R2 240 (by omega), h240]
    · config_simp; rw [R2 241 (by omega), h241]
    · config_simp; rw [R2 243 (by omega), h243]
    · config_simp; rw [R2 244 (by omega), h244]
    · config_simp; rw [R2 249 (by omega), h249]
    · config_simp; rw [R2 250 (by omega), h250]
    · config_simp; rw [R2 251 (by omega), h251]
    · config_simp
      intro y hy
      rw [hnm₂ _ (Or.inl (by have := hX.lay1; omega)) (Or.inl (by have := hX.lay1; omega)),
        hnm₂ _ (Or.inl (by have := hX.lay2; omega)) (Or.inl (by have := hX.lay2; omega)), hmem₁]
      exact hB y hy
    · exact List.nodup_append.2 ⟨hdn, List.nodup_singleton _, fun a ha b hb => by
        rw [List.mem_singleton] at hb; subst hb; exact fun e => hdnd (e ▸ ha)⟩
    · intro d' hd'
      rcases List.mem_append.1 hd' with h | h
      · exact hdcs d' h
      · rw [List.mem_singleton] at h; subst h; exact hd
    · config_simp
      rw [R2 242 (by omega), R2 244 (by omega), h244, List.mem_append, List.mem_singleton,
        hdiff d' hd']
      constructor
      · rintro (⟨y, hy, hyz⟩ | rfl)
        · exact ⟨y, hy, by omega⟩
        · exact ⟨z, hzd, by omega⟩
      · rintro ⟨y, hy, hyz⟩
        by_cases hyz' : y < z
        · exact Or.inl ⟨y, hy, hyz'⟩
        · right
          have hyz'' : y = z := by omega
          subst hyz''
          by_contra hdd
          exact hR.disj hd hd' (Ne.symm hdd) hzd hy
    · config_simp
      rw [hmark₂ y hy, hmem₁, hmark y hy]
      by_cases hyd : y ∈ d
      · rw [ite_eq_left hyd, ite_eq_left ⟨d, List.mem_append_right _ (List.mem_singleton_self _), hyd⟩]
      · rw [ite_eq_right hyd]
        congr 1
        apply propext
        constructor
        · rintro ⟨d', hd', hy'⟩; exact ⟨d', List.mem_append_left _ hd', hy'⟩
        · rintro ⟨d', hd', hy'⟩
          rcases List.mem_append.1 hd' with h | h
          · exact ⟨d', h, hy'⟩
          · rw [List.mem_singleton] at h; subst h; exact absurd hy' hyd
    · refine List.rel_append hF (List.Forall₂.cons ⟨i, ?_⟩ List.Forall₂.nil)
      rw [walk_eq_rotate (hR.cyc d hd) hi, List.map_rotate]
    · intro p hp
      rcases List.mem_append.1 hp with h | h
      · exact hT p h
      · rw [List.mem_singleton] at h; subst h; exact hT₂
    · config_simp
      rw [hout₂, hc₁]; config_simp
      rw [hout, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    · unfold outPot
      config_simp
      rw [R2 242 (by omega), R2 244 (by omega), h244]
      
      have h3 : 3 ≤ d.length := by
         
        by_contra h3
        -- a cycle of the representation read as vertices is a piece, of length at least 3
        obtain ⟨D, hD, hp⟩ := hX.enum
        have hpc := (hD.isPiece hX.simple (hp.mem_iff.1 (List.mem_map_of_mem hd))).three_le
        rw [List.length_map] at hpc
        omega
      omega

set_option maxHeartbeats 1000000 in
/-- **Spec of the output pass**: from a configuration holding the final structure (`Bands`) with
the output-pass registers set, `outStmt` appends a triangulation `X` of `Q` to the output, at cost
`≤ 205 NN + 10`. -/
theorem outStmt_exec {Q : Polygon} {S : LState} {cs : List (List ℕ)} {NN MB NB VB WB : ℕ}
    (hX : OutCtx P Q W S cs NN MB NB VB WB) (c : Config) (hc : WordsBounded W c)
    (hB : Bands c.nmem S NN NB VB) (h240 : c.nreg 240 = NN) (h241 : c.nreg 241 = MB)
    (h249 : c.nreg 249 = NB) (h250 : c.nreg 250 = VB) (h251 : c.nreg 251 = WB) (hW1 : 1 ≤ W) :
    ∃ c' k, Exec P W outStmt c c' k ∧ k ≤ 205 * NN + 10 ∧
      ∃ X, Q.Triangulates X ∧ c'.output = c.output ++ X := by
  classical
  have hR := hX.repr
  have hcnt := hX.cnt
  have hl1 := hX.lay1
  have hl2 := hX.lay2
  have hl3 := hX.lay3
  have hl4 := hX.lay4
  unfold outStmt
  refine spec_seq ?_
  exec_block
  · omega
  · omega
  · omega
  refine spec_name fun c₁ hc₁ => ?_
  have hw₁ : WordsBounded W c₁ := by simp_all
  have r1 : ∀ r, r ≠ 242 → r ≠ 243 → r ≠ 244 → c₁.nreg r = c.nreg r := by
    simp_all
  have c243 : c₁.nreg 243 = 0 := by simp_all
  have c244 : c₁.nreg 244 = 1 := by simp_all
  have hCI : ClearInv W MB NN c₁ c₁ := ⟨hw₁, by simp_all,
    fun y hy => by simp_all, fun _ _ _ => rfl, rfl,
    fun _ _ => rfl, rfl, rfl⟩
  obtain ⟨c₂, k₂, ex₂, ⟨hw₂, hz₂, hzero, hfn₂, hfr₂, hnm₂, hrm₂, hout₂⟩, hexit₂, hk₂⟩ :=
    Exec.whileLtN_bounded (P := P) (ClearInv W MB NN c₁) (fun d => NN - d.nreg 242) 3
      (fun _ h => h.1) (fun d hd ht => clearBody_inv (by simp_all) (by simp_all) c243 c244
        (by omega) d hd ht) hCI
  unfold clearLoop
  refine spec_seq ⟨c₂, k₂, ex₂, ?_⟩
  have e242₂ : c₂.nreg 242 = NN := by
    grind
  refine spec_seq ?_
  exec_block
  · omega
  refine spec_name fun c₃ hc₃ => ?_
  have hw₃ : WordsBounded W c₃ := by grind
  have r3 : ∀ r, r ≠ 242 → r ≠ 248 → c₃.nreg r = c₁.nreg r := by
    intro r a b; rw [hc₃]; config_simp; rw [Machine.upd_other _ _ _ a, hfn₂ r a b]
  have hI₀ : OutInv Q W S cs NN MB NB VB WB c₃ c₃ := by
    refine ⟨hw₃, by rw [hc₃]; positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, [],
      List.nodup_nil, fun d hd => absurd hd List.not_mem_nil, fun d hd => ?_, fun y hy => ?_, [],
      List.Forall₂.nil, fun p hp => absurd hp List.not_mem_nil, by simp⟩
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · grind
    · intro y hy
      have e : c₃.nmem = c₂.nmem := by rw [hc₃]
      rw [e, hnm₂ _ (Or.inl (by omega)), hnm₂ _ (Or.inl (by omega))]
      have e1 : c₁.nmem = c.nmem := by rw [hc₁]
      rw [e1]; exact hB y hy
    · have e : c₃.nreg 242 = 0 := by rw [hc₃]; config_simp
      grind
    · have e : c₃.nmem = c₂.nmem := by rw [hc₃]
      grind
  obtain ⟨c₄, k₄, ex₄, ⟨hw₄, hz₄, h240₄, -, -, -, -, -, -, -, done, hdn, hdcs, hdiff, -, acc, hF,
    hT, hout₄⟩, hexit₄, hk₄⟩ := Exec.whileLtN_potential (P := P)
      (OutInv Q W S cs NN MB NB VB WB c₃) (outPot NN MB) (fun _ h => h.1)
      (fun d hd ht => outBody_inv hX d hd ht) hI₀
  unfold outLoop
  refine ⟨c₄, k₄, ex₄, ?_, ?_⟩
  · grind [outPot, List.length_range]
  · -- all cycles are done
    have e242₄ : c₄.nreg 242 = NN := by omega
    have hall : ∀ d ∈ cs, d ∈ done := by
      intro d hd
      rw [hdiff d hd, e242₄]
      obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil d (hR.cyc d hd).1
      exact ⟨y, hy, hcnt ▸ hR.lt_cnt hd hy⟩
    have hperm : done.Perm cs := by
      rw [List.perm_ext_iff_of_nodup hdn hR.nodup_cs]
      grind
    obtain ⟨D, hD, hp⟩ := hX.enum
    have hrot : List.Forall₂ (fun m' p => ∃ r, p.1 = m'.rotate r) (done.map (List.map S.vtx))
        acc := by
      grind [List.forall₂_map_left_iff]
    refine ⟨_, triangulates_of_pairs hX.simple hD ((hperm.map _).trans hp) hrot hT, ?_⟩
    grind

end Ram

end

end Chazelle.Final
