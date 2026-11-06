module

public import Chazelle.Core.DownPhaseDrvPDesc
public import Chazelle.Core.DownPhaseDrvTFiltS
public import Chazelle.Core.DownPhaseWallChain

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

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace DrvP

open Machine Machine.Stmt Programs BuildRam
open DownBase (rankF tw)

@[expose] public section

/-! ## The program -/

/-- Run `t` if register `p` holds `1` or `3`, else `e`. -/
def isOT (p : ℕ) (t e : Stmt) : Stmt :=
  .ifLtN p 218021 e (.ifLtN p 218079 t (.ifLtN 218079 p (.ifLtN p 218080 t e) e))

/-- Load the triple at the read cursor, advance it by `5`, clear the flag. -/
def dLoad : Stmt := block [.loadN 218072 218071, .addN 218071 218071 218021,
  .loadN 218073 218071, .addN 218071 218071 218021, .loadN 218074 218071,
  .addN 218071 218071 218021, .addN 218071 218071 218021, .addN 218071 218071 218021,
  .constN 218077 0]

/-- The wall flag. -/
def dTest : Stmt := isOT 218073 (isOT 218074 (.instr (.constN 218077 1)) .skip) .skip

/-- Append the triple. -/
def dKeep : Stmt := block [.storeN 218075 218072, .addN 218075 218075 218021,
  .storeN 218075 218073, .addN 218075 218075 218021, .storeN 218075 218074,
  .addN 218075 218075 218021, .addN 218076 218076 218021]

/-- One record. -/
def dBody : Stmt := .seq dLoad (.seq dTest (.seq (.ifLtN 218077 218021 dKeep .skip)
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

theorem dropWalls_eq (L : List (ℕ × ℕ × ℕ)) : BoxT.dropWalls L = L.filter keepW := rfl

/-- The memory after `i` records: the kept triples so far at `B'`. -/
def memD (m₀ : ℕ → ℕ) (L₀ : List (ℕ × ℕ × ℕ)) (B' i a : ℕ) : ℕ :=
  if B' ≤ a ∧ a < B' + 3 * rankF keepW L₀ i then tw (L₀.filter keepW) (a - B') else m₀ a

theorem memD_keep {m₀ m : ℕ → ℕ} {L₀ : List (ℕ × ℕ × ℕ)} {B' i : ℕ}
    (hm : ∀ a, m a = memD m₀ L₀ B' i a) (hi : i < L₀.length)
    (hk : keepW (L₀.getD i (0, 0, 0)) = true) (a : ℕ) :
    (if a = B' + 3 * rankF keepW L₀ i + 2 then (L₀.getD i (0, 0, 0)).2.2
      else if a = B' + 3 * rankF keepW L₀ i + 1 then (L₀.getD i (0, 0, 0)).2.1
      else if a = B' + 3 * rankF keepW L₀ i then (L₀.getD i (0, 0, 0)).1
      else m a) = memD m₀ L₀ B' (i + 1) a := by
  have hr := DownBase.rankF_succ keepW (0, 0, 0) hi
  rw [ite_eq_left hk] at hr
  set j := rankF keepW L₀ i with hj
  have hg := DownBase.getD_filter_rank keepW (0, 0, 0) hi hk
  rw [← hj] at hg
  have htw : ∀ s, s < 3 → tw (L₀.filter keepW) (3 * j + s) =
      if s = 0 then (L₀.getD i (0, 0, 0)).1
      else if s = 1 then (L₀.getD i (0, 0, 0)).2.1
      else (L₀.getD i (0, 0, 0)).2.2 := fun s hs => by
    unfold tw
    rw [show (3 * j + s) % 3 = s by omega, show (3 * j + s) / 3 = j by omega, hg]
  rw [hm a]
  unfold memD
  rw [hr]
  by_cases h3 : a = B' + 3 * j + 2
  · subst h3
    rw [ite_eq_left rfl, ite_eq_left (by omega), show B' + 3 * j + 2 - B' = 3 * j + 2 by omega,
      htw 2 (by norm_num)]
    try simp
  by_cases h4 : a = B' + 3 * j + 1
  · subst h4
    rw [ite_eq_right h3, ite_eq_left rfl, ite_eq_left (by omega), show B' + 3 * j + 1 - B' = 3 * j + 1 by omega,
      htw 1 (by norm_num)]
    try simp
  by_cases h5 : a = B' + 3 * j
  · subst h5
    rw [ite_eq_right h3, ite_eq_right h4, ite_eq_left rfl, ite_eq_left (by omega),
      show B' + 3 * j - B' = 3 * j + 0 by omega, htw 0 (by norm_num)]
    try simp
  rw [ite_eq_right h3, ite_eq_right h4, ite_eq_right h5]
  split_ifs <;> first | rfl | omega

theorem memD_drop {m₀ : ℕ → ℕ} {L₀ : List (ℕ × ℕ × ℕ)} {B' i : ℕ}
    (hi : i < L₀.length) (hk : keepW (L₀.getD i (0, 0, 0)) = false) (a : ℕ) :
    memD m₀ L₀ B' i a = memD m₀ L₀ B' (i + 1) a := by
  have hr := DownBase.rankF_succ keepW (0, 0, 0) hi
  rw [hk] at hr
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at hr
  unfold memD; rw [hr]

/-! ## The pieces of one record -/

section exec

variable {P : Polygon} {W : ℕ}

/-- **The test `p ∈ {1, 3}`.** -/
theorem isOT_exec (c : Config) {p : ℕ} {t e : Stmt} {K : ℕ} {R : Config → Prop}
    (h21 : c.nreg 218021 = 1) (h79 : c.nreg 218079 = 2) (h80 : c.nreg 218080 = 4)
    (ht : (c.nreg p = 1 ∨ c.nreg p = 3) → ∃ c' k, Exec P W t c c' k ∧ k ≤ K ∧ R c')
    (he : ¬ (c.nreg p = 1 ∨ c.nreg p = 3) → ∃ c' k, Exec P W e c c' k ∧ k ≤ K ∧ R c') :
    ∃ c' k, Exec P W (isOT p t e) c c' k ∧ k ≤ K + 7 ∧ R c' := by
  unfold isOT
  by_cases g1 : c.nreg p < c.nreg 218021
  · obtain ⟨c', k, ex, hk, hR⟩ := he (by omega)
    exact ⟨c', _, .ifLtN_true g1 ex, by omega, hR⟩
  by_cases g2 : c.nreg p < c.nreg 218079
  · obtain ⟨c', k, ex, hk, hR⟩ := ht (by omega)
    exact ⟨c', _, .ifLtN_false g1 (.ifLtN_true g2 ex), by omega, hR⟩
  by_cases g3 : c.nreg 218079 < c.nreg p
  · by_cases g4 : c.nreg p < c.nreg 218080
    · obtain ⟨c', k, ex, hk, hR⟩ := ht (by omega)
      exact ⟨c', _, .ifLtN_false g1 (.ifLtN_false g2 (.ifLtN_true g3 (.ifLtN_true g4 ex))),
        by omega, hR⟩
    · obtain ⟨c', k, ex, hk, hR⟩ := he (by omega)
      exact ⟨c', _, .ifLtN_false g1 (.ifLtN_false g2 (.ifLtN_true g3 (.ifLtN_false g4 ex))),
        by omega, hR⟩
  · obtain ⟨c', k, ex, hk, hR⟩ := he (by omega)
    exact ⟨c', _, .ifLtN_false g1 (.ifLtN_false g2 (.ifLtN_false g3 ex)), by omega, hR⟩

/-- **The wall flag.** -/
theorem dTest_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) (h21 : c.nreg 218021 = 1)
    (h79 : c.nreg 218079 = 2) (h80 : c.nreg 218080 = 4) (h77 : c.nreg 218077 = 0) :
    ∃ c' k, Exec P W dTest c c' k ∧ k ≤ 22 ∧
      (c'.nreg 218077 = if BoxT.WallRec (c.nreg 218072, c.nreg 218073, c.nreg 218074) then 1
        else 0) ∧
      (∀ r, r ≠ 218077 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hset : ∃ c' k, Exec P W (.instr (.constN 218077 1)) c c' k ∧ k ≤ 1 ∧
      (c'.nreg 218077 = 1 ∧ (∀ r, r ≠ 218077 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) :=
    ⟨_, _, Exec.constN hw 218077 1 hW, le_rfl, by simp, fun r hr => by simp [hr], rfl, rfl, rfl,
      rfl⟩
  have hskip : ∃ c' k, Exec P W .skip c c' k ∧ k ≤ 8 ∧
      (c'.nreg 218077 = 0 ∧ (∀ r, r ≠ 218077 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) :=
    ⟨c, 0, .skip hw, by omega, h77, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  unfold dTest BoxT.WallRec
  simp only
  by_cases hl : c.nreg 218073 = 1 ∨ c.nreg 218073 = 3
  · by_cases hr : c.nreg 218074 = 1 ∨ c.nreg 218074 = 3
    · rw [ite_eq_left ⟨hl, hr⟩]
      obtain ⟨c₁, k₁, ex₁, hk₁, h₁⟩ := isOT_exec (P := P) (W := W) c (p := 218074)
        (t := .instr (.constN 218077 1)) (e := .skip) (K := 8)
        (R := fun c' => c'.nreg 218077 = 1 ∧ (∀ r, r ≠ 218077 → c'.nreg r = c.nreg r) ∧
          c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output)
        h21 h79 h80 (fun _ => by
          obtain ⟨c', k, ex, hk, h⟩ := hset; exact ⟨c', k, ex, by omega, h⟩)
        (fun h' => absurd hr h')
      obtain ⟨c', k, ex, hk, h⟩ := isOT_exec (P := P) (W := W) c (p := 218073)
        (t := isOT 218074 (.instr (.constN 218077 1)) .skip) (e := .skip) (K := 15)
        (R := fun c' => c'.nreg 218077 = 1 ∧ (∀ r, r ≠ 218077 → c'.nreg r = c.nreg r) ∧
          c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output)
        h21 h79 h80 (fun _ => ⟨c₁, k₁, ex₁, by omega, h₁⟩) (fun h' => absurd hl h')
      exact ⟨c', k, ex, by omega, h⟩
    · rw [ite_eq_right (fun h => hr h.2)]
      obtain ⟨c₁, k₁, ex₁, hk₁, h₁⟩ := isOT_exec (P := P) (W := W) c (p := 218074)
        (t := .instr (.constN 218077 1)) (e := .skip) (K := 8)
        (R := fun c' => c'.nreg 218077 = 0 ∧ (∀ r, r ≠ 218077 → c'.nreg r = c.nreg r) ∧
          c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output)
        h21 h79 h80 (fun h' => absurd h' hr) (fun _ => hskip)
      obtain ⟨c', k, ex, hk, h⟩ := isOT_exec (P := P) (W := W) c (p := 218073)
        (t := isOT 218074 (.instr (.constN 218077 1)) .skip) (e := .skip) (K := 15)
        (R := fun c' => c'.nreg 218077 = 0 ∧ (∀ r, r ≠ 218077 → c'.nreg r = c.nreg r) ∧
          c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output)
        h21 h79 h80 (fun _ => ⟨c₁, k₁, ex₁, by omega, h₁⟩) (fun h' => absurd hl h')
      exact ⟨c', k, ex, by omega, h⟩
  · rw [ite_eq_right (fun h => hl h.1)]
    obtain ⟨c', k, ex, hk, h⟩ := isOT_exec (P := P) (W := W) c (p := 218073)
      (t := isOT 218074 (.instr (.constN 218077 1)) .skip) (e := .skip) (K := 8)
      (R := fun c' => c'.nreg 218077 = 0 ∧ (∀ r, r ≠ 218077 → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output)
      h21 h79 h80 (fun h' => absurd h' hl) (fun _ => hskip)
    exact ⟨c', k, ex, by omega, h⟩

set_option maxHeartbeats 4000000 in
theorem dLoad_exec (c : Config) (hw : WordsBounded W c) {a : ℕ} (h71 : c.nreg 218071 = a)
    (h21 : c.nreg 218021 = 1) (haW : a + 5 ≤ W) :
    ∃ c' k, Exec P W dLoad c c' k ∧ k = 9 ∧ c'.nreg 218072 = c.nmem a ∧
      c'.nreg 218073 = c.nmem (a + 1) ∧ c'.nreg 218074 = c.nmem (a + 2) ∧
      c'.nreg 218071 = a + 5 ∧ c'.nreg 218077 = 0 ∧
      (∀ r, r ≠ 218071 → r ≠ 218072 → r ≠ 218073 → r ≠ 218074 → r ≠ 218077 →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  unfold dLoad
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Config.nreg_mk, Machine.upd_same,
    Machine.upd_other, h71, h21]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r a1 a2 a3 a4 a5 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals simp (disch := omega) only [Config.nreg_mk, Machine.upd_same,
    Machine.upd_other, h71, h21]

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
  refine ⟨rfl, ?_, ?_, fun r a1 a2 => ?_, fun a => ?_, rfl, rfl, rfl⟩
  all_goals simp (disch := omega) only [Config.nreg_mk, Config.nmem_mk, Machine.upd_same,
    Machine.upd_other, h75, h76, h21]
  all_goals try omega
  all_goals (try simp only [Machine.upd_apply])

/-! ## The loop -/

/-- **The invariant of the wall filter.** -/
structure DInv (m₀ : ℕ → ℕ) (L₀ : List (ℕ × ℕ × ℕ)) (CB B' : ℕ) (cI d : Config) : Prop where
  i_le : d.nreg 218070 ≤ L₀.length
  rK : d.nreg 218078 = L₀.length
  r71 : d.nreg 218071 = CB + 5 * d.nreg 218070
  r75 : d.nreg 218075 = B' + 3 * rankF keepW L₀ (d.nreg 218070)
  r76 : d.nreg 218076 = rankF keepW L₀ (d.nreg 218070)
  r21 : d.nreg 218021 = 1
  r79 : d.nreg 218079 = 2
  r80 : d.nreg 218080 = 4
  fr : ∀ r, (r < 218070 ∨ 218077 < r) → d.nreg r = cI.nreg r
  rr : d.rreg = cI.rreg
  rm : d.rmem = cI.rmem
  out : d.output = cI.output
  mem : ∀ a, d.nmem a = memD m₀ L₀ B' (d.nreg 218070) a

set_option maxHeartbeats 8000000 in
/-- **One record.** -/
theorem dBody_exec {m₀ : ℕ → ℕ} {L₀ : List (ℕ × ℕ × ℕ)} {CB B' : ℕ}
    (hR : DrvT.RecsT m₀ CB L₀) (hCB : L₀.length = 0 ∨ CB + 5 * L₀.length ≤ B')
    (hBW : B' + 3 * L₀.length + 3 ≤ W) {cI d : Config} (hw : WordsBounded W d)
    (hI : DInv m₀ L₀ CB B' cI d) (ht : d.nreg 218070 < d.nreg 218078) :
    ∃ d' k, Exec P W dBody d d' k ∧ WordsBounded W d' ∧ DInv m₀ L₀ CB B' cI d' ∧
      d'.nreg 218070 = d.nreg 218070 + 1 ∧ 3 ≤ k ∧ k ≤ 41 := by
  rw [hI.rK] at ht
  have hCB' : CB + 5 * L₀.length ≤ B' := hCB.resolve_left (by omega)
  set i := d.nreg 218070 with hi
  set x := L₀.getD i (0, 0, 0) with hx
  set j := rankF keepW L₀ i with hj
  have hle := DownBase.rankF_le keepW L₀ i
  obtain ⟨l1, l2, l3⟩ := hR i ht
  have hmL : ∀ q, q < 3 → d.nmem (CB + 5 * i + q) = m₀ (CB + 5 * i + q) := fun q hq => by
    rw [hI.mem]; unfold memD; rw [ite_eq_right (by omega)]
  have hW1 : 1 ≤ W := by omega
  clear hCB
  -- load
  obtain ⟨d₁, k₁, e₁, hk₁, v72, v73, v74, v71, v77, r₁, m₁, rr₁, rm₁, o₁⟩ :=
    dLoad_exec (P := P) d hw hI.r71 hI.r21 (by omega)
  rw [← hi] at v72 v73 v74 v71
  have hm0 := hmL 0 (by norm_num)
  rw [Nat.add_zero] at hm0
  rw [hm0, l1] at v72
  rw [hmL 1 (by norm_num), l2] at v73
  rw [hmL 2 (by norm_num), l3] at v74
  have g₁ : ∀ r, (r < 218071 ∨ 218077 < r) → d₁.nreg r = d.nreg r := fun r hr =>
    r₁ r (by omega) (by omega) (by omega) (by omega) (by omega)
  -- the test
  obtain ⟨d₂, k₂, e₂, hk₂, v₂, r₂, m₂, rr₂, rm₂, o₂⟩ := dTest_exec (P := P) d₁ e₁.wb_right hW1
    (by rw [g₁ _ (by norm_num), hI.r21]) (by rw [g₁ _ (by norm_num), hI.r79])
    (by rw [g₁ _ (by norm_num), hI.r80]) v77
  rw [v72, v73, v74] at v₂
  have hx3 : ((x.1, x.2.1, x.2.2) : ℕ × ℕ × ℕ) = x := rfl
  rw [hx3] at v₂
  have g5 : ∀ r, r ≠ 218071 → r ≠ 218072 → r ≠ 218073 → r ≠ 218074 → r ≠ 218077 →
      d₂.nreg r = d.nreg r := fun r a1 a2 a3 a4 a5 => by
    rw [r₂ r a5, r₁ r a1 a2 a3 a4 a5]
  have e72 : d₂.nreg 218072 = x.1 := by rw [r₂ _ (by norm_num), v72]
  have e73 : d₂.nreg 218073 = x.2.1 := by rw [r₂ _ (by norm_num), v73]
  have e74 : d₂.nreg 218074 = x.2.2 := by rw [r₂ _ (by norm_num), v74]
  have hm5 : d₂.nmem = d.nmem := by rw [m₂, m₁]
  -- the branch
  obtain ⟨d₆, k₆, e₆, hk₆, hk₆', g6, mem6, n75, n76, rr₆, rm₆, o₆⟩ : ∃ d₆ k₆,
      Exec P W (.ifLtN 218077 218021 dKeep .skip) d₂ d₆ k₆ ∧ 1 ≤ k₆ ∧ k₆ ≤ 8 ∧
      (∀ r, r ≠ 218075 → r ≠ 218076 → d₆.nreg r = d₂.nreg r) ∧
      (∀ a, d₆.nmem a = memD m₀ L₀ B' (i + 1) a) ∧
      d₆.nreg 218075 = B' + 3 * rankF keepW L₀ (i + 1) ∧
      d₆.nreg 218076 = rankF keepW L₀ (i + 1) ∧
      d₆.rreg = d₂.rreg ∧ d₆.rmem = d₂.rmem ∧ d₆.output = d₂.output := by
    have h21 : d₂.nreg 218021 = 1 := by
      rw [g5 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), hI.r21]
    have h75 : d₂.nreg 218075 = B' + 3 * j := by
      rw [g5 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), hI.r75]
    have h76 : d₂.nreg 218076 = j := by
      rw [g5 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), hI.r76]
    have hr := DownBase.rankF_succ keepW (0, 0, 0) (L := L₀) ht
    cases hk : keepW x
    · have hwall : BoxT.WallRec x := by
        unfold keepW at hk; simpa using hk
      rw [ite_eq_left hwall] at v₂
      have hn : ¬ d₂.nreg 218077 < d₂.nreg 218021 := by rw [h21, v₂]; omega
      rw [← hx, hk] at hr
      simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at hr
      refine ⟨d₂, _, .ifLtN_false hn (.skip e₂.wb_right), by omega, by omega,
        fun _ _ _ => rfl, fun a => ?_, by rw [h75, hr], by rw [h76, hr], rfl, rfl, rfl⟩
      rw [hm5, hI.mem a, ← hi]
      exact memD_drop ht (by rw [← hx]; exact hk) a
    · have hwall : ¬ BoxT.WallRec x := by
        unfold keepW at hk; simpa using hk
      rw [ite_eq_right hwall] at v₂
      have hp : d₂.nreg 218077 < d₂.nreg 218021 := by rw [h21, v₂]; omega
      have hjK : j + 1 ≤ L₀.length := by
        have := DownBase.rankF_lt_length keepW (0, 0, 0) ht (by rw [← hx]; exact hk)
        omega
      obtain ⟨d₆, k₆, e₆', hk₆, w75, w76, r₆, mm₆, rr₆, rm₆, o₆⟩ :=
        dKeep_exec (P := P) d₂ e₂.wb_right h75 h76 h21 (by omega) (by omega)
      rw [← hx, hk] at hr
      simp only [ite_true] at hr
      refine ⟨d₆, _, .ifLtN_true hp e₆', by omega, by omega, r₆, fun a => ?_,
        by rw [w75, hr]; ring, by rw [w76, hr], rr₆, rm₆, o₆⟩
      rw [mm₆, e72, e73, e74, hm5]
      have := memD_keep (m₀ := m₀) (m := d.nmem) (B' := B') (hI.mem) ht
        (by rw [← hx]; exact hk) a
      rw [← hi, ← hj] at this
      rw [← this]
  -- the increment
  have h70 : d₆.nreg 218070 = i := by
    rw [g6 _ (by norm_num) (by norm_num), g5 _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)]
  have h21' : d₆.nreg 218021 = 1 := by
    rw [g6 _ (by norm_num) (by norm_num), g5 _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), hI.r21]
  have e₇ := Exec.addN (P := P) e₆.wb_right 218070 218070 218021 (by rw [h70, h21']; omega)
  set d₇ : Config := { d₆ with nreg := upd d₆.nreg 218070 (d₆.nreg 218070 + d₆.nreg 218021) }
    with hd₇
  have g7 : ∀ r, r ≠ 218070 → d₇.nreg r = d₆.nreg r := fun r hr => by rw [hd₇]; simp [hr]
  have v7 : d₇.nreg 218070 = i + 1 := by rw [hd₇]; simp [h70, h21']
  have g : ∀ r, (r < 218070 ∨ 218077 < r) → d₇.nreg r = d.nreg r := fun r hr => by
    rw [g7 r (by omega), g6 r (by omega) (by omega),
      g5 r (by omega) (by omega) (by omega) (by omega) (by omega)]
  have X' : Exec P W dBody d d₇ (k₁ + (k₂ + (k₆ + 1))) :=
    .seq e₁ (.seq e₂ (.seq e₆ (Exec.block_cons e₇ (Exec.block_nil e₇.wb_right))))
  refine ⟨d₇, _, X', e₇.wb_right, ?_, v7, by omega, by omega⟩
  refine ⟨by rw [v7]; omega, by rw [g _ (by norm_num), hI.rK], ?_, ?_, ?_,
    by rw [g _ (by norm_num), hI.r21], by rw [g _ (by norm_num), hI.r79],
    by rw [g _ (by norm_num), hI.r80],
    fun r hr => by rw [g r hr, hI.fr r hr], ?_, ?_, ?_, fun a => ?_⟩
  · rw [v7, g7 _ (by norm_num), g6 _ (by norm_num) (by norm_num), r₂ _ (by norm_num), v71]
    ring
  · rw [v7, g7 _ (by norm_num), n75]
  · rw [v7, g7 _ (by norm_num), n76]
  · show d₆.rreg = cI.rreg; rw [rr₆, rr₂, rr₁, hI.rr]
  · show d₆.rmem = cI.rmem; rw [rm₆, rm₂, rm₁, hI.rm]
  · show d₆.output = cI.output; rw [o₆, o₂, o₁, hI.out]
  · show d₆.nmem a = _; rw [v7, mem6]

/-- **The pass.** -/
theorem dLoop_exec {m₀ : ℕ → ℕ} {L₀ : List (ℕ × ℕ × ℕ)} {CB B' : ℕ}
    (hR : DrvT.RecsT m₀ CB L₀) (hCB : L₀.length = 0 ∨ CB + 5 * L₀.length ≤ B')
    (hBW : B' + 3 * L₀.length + 3 ≤ W) {cI d : Config} (hw : WordsBounded W d)
    (hI : DInv m₀ L₀ CB B' cI d) (h0 : d.nreg 218070 = 0) :
    ∃ d' k, Exec P W dLoop d d' k ∧ WordsBounded W d' ∧ DInv m₀ L₀ CB B' cI d' ∧
      d'.nreg 218070 = L₀.length ∧ 3 * L₀.length ≤ k ∧ k ≤ 43 * L₀.length + 2 := by
  obtain ⟨d', k, e, ⟨hw', hI'⟩, htest, hk, hψ⟩ := SortR.whileLtN_potential_lb (P := P) (W := W)
    (a := 218070) (b := 218078) (body := dBody)
    (fun d => WordsBounded W d ∧ DInv m₀ L₀ CB B' cI d)
    (fun d => 43 * (L₀.length - d.nreg 218070)) (fun d => 3 * d.nreg 218070) (fun d hd => hd.1)
    (fun d ⟨hwd, hId⟩ ht => by
      obtain ⟨d', k, e, hw', hI', hi', hk1, hk2⟩ := dBody_exec hR hCB hBW hwd hId ht
      have := hId.rK
      refine ⟨d', k, e, ⟨hw', hI'⟩, ?_, ?_⟩
      · rw [hi']; rw [this] at ht; omega
      · rw [hi']; omega)
    ⟨hw, hI⟩
  have hi := hI'.i_le
  rw [hI'.rK] at htest
  refine ⟨d', k, e, hw', hI', by omega, ?_, ?_⟩
  · rw [h0] at hψ; have : d'.nreg 218070 = L₀.length := by omega
    rw [this] at hψ; omega
  · rw [h0] at hk; omega

end exec

/-- The list of a full pass, in memory. -/
theorem chordListAt_memD {m₀ m : ℕ → ℕ} {L₀ : List (ℕ × ℕ × ℕ)} {B' : ℕ}
    (hm : ∀ a, m a = memD m₀ L₀ B' L₀.length a) :
    ChordListAt m B' (BoxT.dropWalls L₀) := by
  have hlen : rankF keepW L₀ L₀.length = (BoxT.dropWalls L₀).length := by
    rw [DownBase.rankF_length]; rfl
  intro j hj
  have hq : ∀ q, q < 3 → m (B' + 3 * j + q) = tw (BoxT.dropWalls L₀) (3 * j + q) := by
    intro q hq
    rw [hm]; unfold memD; rw [hlen, ite_eq_left (by omega), show B' + 3 * j + q - B' = 3 * j + q by
      omega]; rfl
  refine ⟨?_, ?_, ?_⟩
  · have := hq 0 (by norm_num); rw [Nat.add_zero, Nat.add_zero] at this; rw [this]
    unfold tw; rw [show 3 * j % 3 = 0 by omega, show 3 * j / 3 = j by omega]; simp
  · rw [hq 1 (by norm_num)]
    unfold tw; rw [show (3 * j + 1) % 3 = 1 by omega, show (3 * j + 1) / 3 = j by omega]; simp
  · rw [hq 2 (by norm_num)]
    unfold tw; rw [show (3 * j + 2) % 3 = 2 by omega, show (3 * j + 2) / 3 = j by omega]; simp

section exec2

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 8000000 in
theorem dSetup_exec (c : Config) (hw : WordsBounded W c) {A B₀ K₀ CB : ℕ}
    (hA : c.nreg 9999 = A) (hB : c.nreg 218015 = B₀) (hBA : B₀ + 11 < A)
    (hK : c.nmem B₀ = K₀) (hCB : c.nmem (B₀ + 3) = CB) (h21 : c.nreg 218021 = 1)
    (hAW : A + 4 ≤ W) :
    ∃ c' k, Exec P W dSetup c c' k ∧ k = 10 ∧ c'.nreg 218079 = 2 ∧ c'.nreg 218080 = 4 ∧
      c'.nreg 218078 = K₀ ∧ c'.nreg 218071 = CB ∧ c'.nreg 218075 = A ∧ c'.nreg 218016 = A ∧
      c'.nreg 218076 = 0 ∧ c'.nreg 218070 = 0 ∧
      (∀ r, r ≠ 218016 → (r < 218070 ∨ 218080 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dSetup
  have e : ALLOC = 9999 := rfl
  rw [e]
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
    (hN : Robust (c.nreg ALLOC) c.nmem (fun m => NFAt m (c.nreg 218015) N))
    (h21 : c.nreg 218021 = 1) (hroom : c.nreg ALLOC + 3 * N.chords.length + 20 ≤ W) :
    ∃ c' k, Exec P W dropS c c' k ∧
      3 * (BoxT.dropWalls (DrvT.triplesOf N)).length ≤ k ∧ k ≤ 43 * N.chords.length + 20 ∧
      c'.nreg 218016 = c.nreg ALLOC ∧
      c'.nreg 218017 = (BoxT.dropWalls (DrvT.triplesOf N)).length ∧
      c'.nreg ALLOC = c.nreg ALLOC + 3 * (BoxT.dropWalls (DrvT.triplesOf N)).length ∧
      ChordListAt c'.nmem (c.nreg ALLOC) (BoxT.dropWalls (DrvT.triplesOf N)) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 218016 → r ≠ 218017 → (r < 218070 ∨ 218080 < r) → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set A := c.nreg ALLOC
  set B₀ := c.nreg 218015
  have hNA := hN.holds
  obtain ⟨hBA, -⟩ := DrvT.nfAt_robust_bound hN
  set K₀ := N.chords.length
  have hlen₀ : (DrvT.triplesOf N).length = K₀ := by unfold DrvT.triplesOf; rw [List.length_map]
  obtain ⟨c₁, k₁, e₁, hk₁, v79, v80, v78, v71, v75, v16, v76, v70, g₁, mm₁, rr₁, rm₁, o₁⟩ :=
    dSetup_exec (P := P) c hw (A := A) (B₀ := B₀) (K₀ := K₀) (CB := c.nmem (B₀ + 3)) rfl rfl
      hBA hNA.1 rfl h21 (by omega)
  have hR := DrvT.recsT_of_nfAt hN (m' := c₁.nmem) (fun a _ => by rw [mm₁])
  have hI₁ : DInv c₁.nmem (DrvT.triplesOf N) (c.nmem (B₀ + 3)) A c₁ c₁ :=
    { i_le := by rw [v70]; omega
      rK := by rw [v78, hlen₀]
      r71 := by rw [v71, v70]; ring
      r75 := by rw [v75, v70]; simp [rankF]
      r76 := by rw [v76, v70]; simp [rankF]
      r21 := by rw [g₁ _ (by norm_num) (by norm_num), h21]
      r79 := v79
      r80 := v80
      fr := fun _ _ => rfl
      rr := rfl
      rm := rfl
      out := rfl
      mem := fun a => by rw [v70]; unfold memD; simp [rankF] }
  have hCB : (DrvT.triplesOf N).length = 0 ∨
      c.nmem (B₀ + 3) + 5 * (DrvT.triplesOf N).length ≤ A := by
    rcases Nat.eq_zero_or_pos (DrvT.triplesOf N).length with h0 | hpos
    · left; exact h0
    · right
      have := (DrvT.nfAt_robust_bound hN).2 (K₀ - 1) (by omega)
      rw [hlen₀]
      have : c.nmem (B₀ + 3) + 5 * (K₀ - 1) + 4 < A := this
      omega
  obtain ⟨c₂, k₂, e₂, hw₂, hI₂, h70, hk₂, hk₂'⟩ := dLoop_exec (P := P) hR hCB
    (by rw [hlen₀]; omega) e₁.wb_right hI₁ v70
  rw [hlen₀] at hk₂ hk₂' h70
  have g₂ : ∀ r, (r < 218070 ∨ 218077 < r) → c₂.nreg r = c₁.nreg r := hI₂.fr
  have hcnt : c₂.nreg 218076 = (BoxT.dropWalls (DrvT.triplesOf N)).length := by
    rw [hI₂.r76, h70, ← hlen₀, DownBase.rankF_length]; rfl
  have hcur : c₂.nreg 218075 = A + 3 * (BoxT.dropWalls (DrvT.triplesOf N)).length := by
    rw [hI₂.r75, h70, ← hlen₀, DownBase.rankF_length]; rfl
  have hKle : (BoxT.dropWalls (DrvT.triplesOf N)).length ≤ K₀ := by
    rw [← hlen₀]; exact List.length_filter_le _ _
  -- the end
  obtain ⟨c₃, k₃, e₃, hk₃, v17, v99, r₃, m₃⟩ : ∃ c₃ k₃, Exec P W dFin c₂ c₃ k₃ ∧ k₃ = 2 ∧
      c₃.nreg 218017 = (BoxT.dropWalls (DrvT.triplesOf N)).length ∧
      c₃.nreg ALLOC = A + 3 * (BoxT.dropWalls (DrvT.triplesOf N)).length ∧
      (∀ r, r ≠ 218017 → r ≠ ALLOC → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    unfold dFin
    have e : ALLOC = 9999 := rfl
    rw [e]
    exec_block
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; exact hcnt
    · config_simp; exact hcur
    · simp only [Config.nreg_mk, upd, ite_eq_right h1, ite_eq_right h2]
  obtain ⟨m₃, hr₃, hrm₃, ho₃⟩ := m₃
  have ex : Exec P W dropS c c₃ (k₁ + (k₂ + k₃)) := .seq e₁ (.seq e₂ e₃)
  refine ⟨c₃, _, ex, by omega, by omega, ?_, v17, v99, ?_, fun a ha => ?_, fun r h1 h2 h3 h4 => ?_,
    by rw [hr₃, hI₂.rr, rr₁], by rw [hrm₃, hI₂.rm, rm₁], by rw [ho₃, hI₂.out, o₁]⟩
  · rw [r₃ _ (by norm_num) (by decide), g₂ _ (by norm_num), v16]
  · rw [m₃]
    refine chordListAt_memD (m₀ := c₁.nmem) (fun a => ?_)
    rw [hI₂.mem a, h70, hlen₀]
  · rw [m₃, hI₂.mem, h70]; unfold memD; rw [ite_eq_right (by omega), mm₁]
  · rw [r₃ r h2 h4, g₂ r (by omega), g₁ r h1 (by omega)]

end exec2

end

end DrvP

end Chazelle.Core
