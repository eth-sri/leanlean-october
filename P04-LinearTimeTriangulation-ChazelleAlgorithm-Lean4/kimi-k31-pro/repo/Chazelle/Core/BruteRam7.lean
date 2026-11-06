module

public import Chazelle.Core.BruteRam6
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics
public import Chazelle.ChainTactics
set_option maxHeartbeats 1000000

/-!
# WP-K on the RAM, part 7: the main loop over the tour

`loopS` runs over the tour positions `i = 0 … 2m` (`180030`), keeping the tour position
`j = (S + i) mod 2m` (`180031`) and the previous tour vertex (`180033`); at each position it decides
the emissions (`cornerS`) and emits the chords (`emitS 0`, `emitS 1`).  The chord list written
so far is `pre C i` (`loopS_exec`), and `pre C (2m + 1) = bruteList C` (`pre_full`).
-/


namespace Chazelle.Core

namespace Brute

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

open Classical

/-! ## The list written so far -/

/-- The entries of the tour positions `< i`. -/
noncomputable def pre (C : Chain) (i : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range i).flatMap fun i' =>
    (if Emit C i' 0 then [trip C i' 0] else []) ++ (if Emit C i' 1 then [trip C i' 1] else [])

theorem pre_succ (C : Chain) (i : ℕ) :
    pre C (i + 1) = pre C i ++ ((if Emit C i 0 then [trip C i 0] else []) ++
      (if Emit C i 1 then [trip C i 1] else [])) := by
  classical
  urs pre [List.range_succ, List.flatMap_append]

theorem pre_length_le (C : Chain) (i : ℕ) : (pre C i).length ≤ 2 * i := by
  induction i with
  | zero => simp [pre]
  | succ i ih =>
    rw [pre_succ, List.length_append, List.length_append]
    have h1 : (if Emit C i 0 then [trip C i 0] else []).length ≤ 1 := by split_ifs <;> simp
    have h2 : (if Emit C i 1 then [trip C i 1] else []).length ≤ 1 := by split_ifs <;> simp
    omega

theorem pre_full (C : Chain) : pre C (2 * C.m + 1) = bruteList C := by
  classical
  unfold pre bruteList entries
  rw [List.filter_flatMap, List.map_flatMap]
  congr 1
  funext i
  simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]
  split_ifs <;> simp

/-- Appending a triple to a chord list in memory. -/
theorem chordList_snoc {m m' : ℕ → ℕ} {L : ℕ} {l : List (ℕ × ℕ × ℕ)} (h : ChordListAt m L l)
    (x : ℕ × ℕ × ℕ)
    (hm : m' = upd (upd (upd m (L + 3 * l.length) x.1) (L + 3 * l.length + 1) x.2.1)
      (L + 3 * l.length + 2) x.2.2) : ChordListAt m' L (l ++ [x]) := by
  intro i hi
  rw [List.length_append, List.length_singleton] at hi
  rw [hm]
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
  · have e : (l ++ [x]).getD i (0, 0, 0) = l.getD i (0, 0, 0) := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    rw [e]
    obtain ⟨h1, h2, h3⟩ := h i hi
    refine ⟨?_, ?_, ?_⟩ <;>
      simp (disch := omega) only [Machine.upd_other] <;> assumption
  · have e : (l ++ [x]).getD l.length (0, 0, 0) = x := by
      rws [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
    rw [e]
    refine ⟨?_, ?_, ?_⟩ <;> simp (disch := omega) only [Machine.upd_same, Machine.upd_other]

/-- The value of `trip`. -/
theorem trip_eq {C : Chain} {i d : ℕ} (hsn : C.s + C.m + 1 ≤ C.P.n) :
    trip C i d = (C.s + C.sideIdx C.sideBeta i,
      if d = 0 then i + 6 else farEdge C (C.sideIdx C.sideBeta i) (sig d),
      if d = 0 then farEdge C (C.sideIdx C.sideBeta i) (sig d) else i + 6) := by
  have hk := C.sideIdx_le C.sideBeta i
  unfold trip
  rw [edgeIdx_eq (by omega)]
  by_cases hd : d = 0
  · subst hd; simp [sig_zero]
  · simp [hd, sig_one hd]

/-! ## Emitting in one direction -/

/-- Emit the chord of direction `d` if its bit (`180041 + d`) is set. -/
def emitB (d : ℕ) : Stmt := .ifLtN (180041 + d) 180011 .skip (emitS d)

theorem emitB_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 8 ≤ W) (hW4 : 4 * P.n ≤ W)
    {C : Chain} (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) {d i : ℕ} (hd : d ≤ 1)
    (_hi : i ≤ 2 * C.m) (c : Config) (hw : WordsBounded W c)
    (hS : SI C (C.s + C.sideIdx C.sideBeta i) c) (hF : FI C c)
    (hb : c.nreg (180041 + d) ≤ 1) (he : c.nreg (180041 + d) = 1 ↔ Emit C i d)
    (h44 : c.nreg 180044 = i + 6) {L : ℕ} {l : List (ℕ × ℕ × ℕ)} {M : ℕ → ℕ}
    (h24 : c.nreg 180024 = L + 3 * l.length) (h19 : c.nreg 180019 = l.length)
    (hl : ChordListAt c.nmem L l) (hM : ∀ x, x < L → c.nmem x = M x)
    (hroom : L + 3 * l.length + 3 ≤ W) :
    ∃ c' k, Exec P W (emitB d) c c' k ∧ k ≤ 1602 * C.m + 290 ∧
      3 * (l ++ (if Emit C i d then [trip C i d] else [])).length ≤ 3 * l.length + k ∧
      c'.nreg 180024 = L + 3 * (l ++ (if Emit C i d then [trip C i d] else [])).length ∧
      c'.nreg 180019 = (l ++ (if Emit C i d then [trip C i d] else [])).length ∧
      ChordListAt c'.nmem L (l ++ (if Emit C i d then [trip C i d] else [])) ∧
      (∀ x, x < L → c'.nmem x = M x) ∧
      (∀ r, Bem r = false → c'.nreg r = c.nreg r) ∧ (∀ r, Bsc r = false → c'.rreg r = c.rreg r) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hk := C.sideIdx_le C.sideBeta i
  by_cases hE : Emit C i d
  · simp only [hE, ite_true]
    obtain ⟨c', k, e, hk', hk7, p24, p19, pm, R, rr, rm, o⟩ := emitS_exec (P := P) (d := d) hG hW hW4 hC
      hsn hd hk c hw hS hF (A := L + 3 * l.length) (len := l.length) (p := i + 6) h24 h19 h44
      (by omega) (by omega)
    refine ⟨c', _, .ifLtN_false (by rwo [he.2 hE, hS.2.2.1]) e, by omega,
      by sio, ?_, ?_, ?_, ?_, R, rr, rm, o⟩
    · rws [p24]; ring
    · rws [p19]
    · refine chordList_snoc hl _ ?_
      rw [pm, trip_eq (by rwx [hC, show (Qof P).n = P.n from shear_n _ _])]
    · intro x hx; rw [pm]; simp (disch := omega) only [Machine.upd_other]; exact hM x hx
  · simp only [hE, ite_false, List.append_nil]
    have h0 : c.nreg (180041 + d) = 0 := by have := mt he.1 hE; omega
    exact ⟨c, _, .ifLtN_true (by rwo [h0, hS.2.2.1]) (.skip hw), by omega, by omega, h24, h19,
      hl, hM,
      fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

/-! ## Indices and advancing -/

/-- `d := sideE m x`. -/
def sideES (d x : ℕ) : Stmt :=
  .ifLtN 180001 x (.instr (.subN d 180012 x)) (.instr (.copyN d x))

theorem sideES_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {d x m : ℕ}
    (h1 : c.nreg 180001 = m) (h12 : c.nreg 180012 = 2 * m) :
    ∃ c' k, Exec P W (sideES d x) c c' k ∧ k ≤ 3 ∧ c'.nreg d = Chain.sideE m (c.nreg x) ∧
      FrameB (fun r => decide (r = d)) c c' := by
  have fr : ∀ v, FrameB (fun r => decide (r = d)) c { c with nreg := upd c.nreg d v } := fun v =>
    ⟨fun r hr => by simp only [decide_eq_false_iff_not] at hr; simp [hr], fun r _ => rfl, rfl,
      rfl, rfl⟩
  have hse : Chain.sideE m (c.nreg x) = if m < c.nreg x then 2 * m - c.nreg x else c.nreg x := by
    unfold Chain.sideE; splao
  rw [hse]
  by_cases h : m < c.nreg x
  · exact ⟨_, _, .ifLtN_true (by rwx [h1]) (Exec.subN hw d 180012 x), by omega,
      by simp [h, h12], fr _⟩
  · exact ⟨_, _, .ifLtN_false (by rwx [h1]) (Exec.copyN hw d x), by omega,
      by simp [h], fr _⟩

/-- The indices of tour position `i`. -/
def idxS : Stmt :=
  .seq (sideES 180032 180031) (.seq (.instr (.addN 180043 180031 180011))
    (.seq (sideES 180034 180043) (block [.addN 180035 180000 180032, .addN 180036 180000 180033,
      .addN 180037 180000 180034, .addN 180044 180030 180027])))

/-- The write set of the loop body's own registers: `180030 … 180049`. -/
def Blp (r : ℕ) : Bool := decide (180030 ≤ r ∧ r < 180050)

theorem lp_one {d : ℕ} (hd : 180030 ≤ d ∧ d < 180050) {c c' : Config}
    (F : FrameB (fun r => decide (r = d)) c c') : FrameB Blp c c' :=
  frameB_mono F fun r hr => by unfold Blp at hr; sio only [decide_eq_false_iff_not] at hr ⊢

theorem idxS_exec {P : Polygon} {W : ℕ} {C : Chain} (c : Config) (hw : WordsBounded W c)
    (hsn : C.s + C.m + 1 ≤ P.n) (hW : P.n + 2 * C.m + 8 ≤ W) {i kp : ℕ} (hi : i ≤ 2 * C.m)
    (h0 : c.nreg 180000 = C.s) (h1 : c.nreg 180001 = C.m) (h11 : c.nreg 180011 = 1)
    (h12 : c.nreg 180012 = 2 * C.m) (h27 : c.nreg 180027 = 6) (h30 : c.nreg 180030 = i)
    (h31 : c.nreg 180031 = (tS C + i) % (2 * C.m)) (h33 : c.nreg 180033 = kp) (hkp : kp ≤ C.m) :
    ∃ c' k, Exec P W idxS c c' k ∧ k ≤ 12 ∧ FrameB Blp c c' ∧
      c'.nreg 180032 = C.sideIdx C.sideBeta i ∧ c'.nreg 180033 = kp ∧
      c'.nreg 180035 = C.s + C.sideIdx C.sideBeta i ∧ c'.nreg 180036 = C.s + kp ∧
      c'.nreg 180037 = C.s + C.sideIdx C.sideBeta (i + 1) ∧ c'.nreg 180044 = i + 6 ∧
      c'.nreg 180030 = i ∧ c'.nreg 180031 = c.nreg 180031 := by
  have hm := C.two_m_pos
  have hl := fun j => C.sideIdx_le C.sideBeta j
  obtain ⟨c₁, k₁, e₁, hk₁, q32, F₁⟩ := sideES_exec (P := P) (d := 180032) (x := 180031) c hw h1 h12
  rw [h31] at q32
  have e32 : c₁.nreg 180032 = C.sideIdx C.sideBeta i := by rwr [q32, Chain.sideIdx_eq]
  have r : ∀ q, q ≠ 180032 → c₁.nreg q = c.nreg q := fun q hq => fr1 F₁ hq
  have e₂ := Exec.addN (P := P) e₁.wb_right 180043 180031 180011 (by
    rw [r _ (by decide), r _ (by decide), h31, h11]; have := Nat.mod_lt (tS C + i) hm; omega)
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg 180043 (c₁.nreg 180031 + c₁.nreg 180011) }
    with hc₂
  have q43 : c₂.nreg 180043 = (tS C + i) % (2 * C.m) + 1 := by
    rw [hc₂]; simp only [Config.nreg_mk, upd_same]; rw [r _ (by decide), r _ (by decide), h31, h11]
  have r₂ : ∀ q, q ≠ 180043 → c₂.nreg q = c₁.nreg q := fun q hq => by rw [hc₂]; simp [hq]
  obtain ⟨c₃, k₃, e₃, hk₃, q34, F₃⟩ := sideES_exec (P := P) (d := 180034) (x := 180043) c₂
    e₂.wb_right (m := C.m) (by rw [r₂ _ (by decide), r _ (by decide), h1])
    (by rw [r₂ _ (by decide), r _ (by decide), h12])
  rw [q43] at q34
  have e34 : c₃.nreg 180034 = C.sideIdx C.sideBeta (i + 1) := by
    rwr [q34, Chain.sideIdx_succ]
  have r₃ : ∀ q, q ≠ 180034 → q ≠ 180043 → q ≠ 180032 → c₃.nreg q = c.nreg q := fun q h1 h2 h3 =>
    by rw [fr1 F₃ h1, r₂ q h2, r q h3]
  have k32 : c₃.nreg 180032 = C.sideIdx C.sideBeta i := by
    rw [fr1 F₃ (by decide), r₂ _ (by decide), e32]
  obtain ⟨c₄, k₄, e₄, hk₄, q35, q36, q37, q44, R₄⟩ : ∃ c₄ k₄, Exec P W
      (block [.addN 180035 180000 180032, .addN 180036 180000 180033,
        .addN 180037 180000 180034, .addN 180044 180030 180027]) c₃ c₄ k₄ ∧ k₄ = 4 ∧
      c₄.nreg 180035 = C.s + C.sideIdx C.sideBeta i ∧ c₄.nreg 180036 = C.s + kp ∧
      c₄.nreg 180037 = C.s + C.sideIdx C.sideBeta (i + 1) ∧ c₄.nreg 180044 = i + 6 ∧
      FrameB (fun r => decide (r = 180035 ∨ r = 180036 ∨ r = 180037 ∨ r = 180044)) c₃ c₄ := by
    have w := e₃.wb_right
    have a0 : c₃.nreg 180000 = C.s := by rw [r₃ _ (by decide) (by decide) (by decide), h0]
    have a33 : c₃.nreg 180033 = kp := by rw [r₃ _ (by decide) (by decide) (by decide), h33]
    have a30 : c₃.nreg 180030 = i := by rw [r₃ _ (by decide) (by decide) (by decide), h30]
    have a27 : c₃.nreg 180027 = 6 := by rw [r₃ _ (by decide) (by decide) (by decide), h27]
    have hk1 := hl i
    have hk2 := hl (i + 1)
    exec_block
    · config_simp; rwo [a0, k32]
    · config_simp; rwo [a0, a33]
    · config_simp; rwo [a0, e34]
    · config_simp; rwo [a30, a27]
    · refine ⟨rfl, ?_, ?_, ?_, ?_, ⟨fun q hq => ?_, fun q _ => rfl, rfl, rfl, rfl⟩⟩
      · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
        rw [a0, k32]
      · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
        rw [a0, a33]
      · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
        rw [a0, e34]
      · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
        rw [a30, a27]
      · simp only [decide_eq_false_iff_not, not_or] at hq
        simp (disch := omega) only [Config.nreg_mk, Machine.upd_other]
  have F₂ : FrameB Blp c₁ c₂ := lp_one (d := 180043) (by omega)
    ⟨fun q hq => r₂ q (by simpa using hq), fun _ _ => rfl, rfl, rfl, rfl⟩
  have F₄ : FrameB Blp c₃ c₄ := frameB_mono R₄ fun q hq => by
    unfold Blp at hq; sio only [decide_eq_false_iff_not] at hq ⊢
  refine ⟨c₄, _, .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega,
    (((lp_one (by omega) F₁).trans F₂).trans (lp_one (by omega) F₃)).trans F₄, ?_, ?_, q35, q36,
    q37, q44, ?_, ?_⟩
  · rw [R₄.1 _ (by decide), k32]
  · rw [R₄.1 _ (by decide), r₃ _ (by decide) (by decide) (by decide), h33]
  · rw [R₄.1 _ (by decide), r₃ _ (by decide) (by decide) (by decide), h30]
  · rw [R₄.1 _ (by decide), r₃ _ (by decide) (by decide) (by decide)]

/-- Advance to the next tour position. -/
def advS : Stmt :=
  .seq (block [.copyN 180033 180032, .addN 180030 180030 180011, .addN 180031 180031 180011])
    (.ifLtN 180031 180012 .skip (.instr (.constN 180031 0)))

theorem advS_exec {P : Polygon} {W : ℕ} {C : Chain} (c : Config) (hw : WordsBounded W c)
    (hW : 2 * C.m + 2 ≤ W) {i : ℕ} (hi : i ≤ 2 * C.m) (h11 : c.nreg 180011 = 1)
    (h12 : c.nreg 180012 = 2 * C.m) (h30 : c.nreg 180030 = i)
    (h31 : c.nreg 180031 = (tS C + i) % (2 * C.m)) :
    ∃ c' k, Exec P W advS c c' k ∧ k ≤ 6 ∧ FrameB Blp c c' ∧
      c'.nreg 180033 = c.nreg 180032 ∧ c'.nreg 180030 = i + 1 ∧
      (i + 1 ≤ 2 * C.m → c'.nreg 180031 = (tS C + (i + 1)) % (2 * C.m)) := by
  have hm := C.two_m_pos
  have hj := Nat.mod_lt (tS C + i) hm
  obtain ⟨c₁, k₁, e₁, hk₁, q33, q30, q31, R₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.copyN 180033 180032, .addN 180030 180030 180011, .addN 180031 180031 180011]) c c₁ k₁ ∧
      k₁ = 3 ∧ c₁.nreg 180033 = c.nreg 180032 ∧ c₁.nreg 180030 = i + 1 ∧
      c₁.nreg 180031 = (tS C + i) % (2 * C.m) + 1 ∧
      FrameB (fun r => decide (r = 180033 ∨ r = 180030 ∨ r = 180031)) c c₁ := by
    exec_block
    · config_simp; rwo [h30, h11]
    · config_simp; rwo [h31, h11]
    · refine ⟨rfl, ?_, ?_, ?_, ⟨fun q hq => ?_, fun q _ => rfl, rfl, rfl, rfl⟩⟩
      · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
      · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
        rw [h30, h11]
      · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
        rw [h31, h11]
      · simp only [decide_eq_false_iff_not, not_or] at hq
        simp (disch := omega) only [Config.nreg_mk, Machine.upd_other]
  have G₁ : FrameB Blp c c₁ := frameB_mono R₁ fun q hq => by
    unfold Blp at hq; sio only [decide_eq_false_iff_not] at hq ⊢
  have k12 : c₁.nreg 180012 = 2 * C.m := by rw [R₁.1 _ (by decide), h12]
  have w₁ := e₁.wb_right
  have hnext : (tS C + (i + 1)) % (2 * C.m) =
      if (tS C + i) % (2 * C.m) + 1 < 2 * C.m then (tS C + i) % (2 * C.m) + 1 else 0 := by
    have h1 : (1 : ℕ) % (2 * C.m) = 1 := Nat.mod_eq_of_lt (by have := C.one_le; omega)
    rw [← Nat.add_assoc, Nat.add_mod (tS C + i) 1, h1]
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [show (tS C + i) % (2 * C.m) + 1 = 2 * C.m by omega, Nat.mod_self]
  by_cases hlt : (tS C + i) % (2 * C.m) + 1 < 2 * C.m
  · refine ⟨c₁, _, .seq e₁ (.ifLtN_true (by rwx [q31, k12]) (.skip w₁)), by omega, G₁,
      q33, q30, fun _ => by rw [q31, hnext, ite_eq_left hlt]⟩
  · have e₂ := Exec.constN (P := P) w₁ 180031 0 (by omega)
    refine ⟨_, _, .seq e₁ (.ifLtN_false (by rwx [q31, k12]) e₂), by omega,
      G₁.trans (lp_one (d := 180031) (by omega) ⟨fun q hq => by simp only [decide_eq_false_iff_not] at hq; simp [hq],
        fun _ _ => rfl, rfl, rfl, rfl⟩), by simp [q33], by simp [q30],
      fun _ => by simp only [Config.nreg_mk, upd_same]; rw [hnext, ite_eq_right hlt]⟩

end

end Brute

end Chazelle.Core
