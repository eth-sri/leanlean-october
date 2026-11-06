module

public import Chazelle.Core.BruteRam5
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.ChainTactics
set_option maxHeartbeats 1000000

/-!
# WP-K on the RAM, part 6: the emission decision at a tour vertex

For a tour position `0 < i < 2m` with the vertex `v` (`180035`) and its walk neighbours `a`
(`180036`) and `b` (`180037`), three sign tests (`t₁ : v.y < a.y`, `t₂ : v.y < b.y`,
`t₃ : 0 < det a v b`) and a boolean combination give the two emission bits (`180041` east,
`180042` west), following `emitR` (`cornerS_exec`).
-/


namespace Chazelle.Core

namespace Brute

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-- The combination of the three corner bits `t₁ = 38`, `t₂ = 39`, `t₃ = 40` into the emission
bits `41` (east) and `42` (west). -/
def logicE : Stmt :=
  .seq (andS 180043 180038 180039) (.seq (orS 180047 180038 180039 180048)
  (.seq (notS 180047 180047) (.seq (.instr (.addN 180043 180043 180047))
  (.seq (notS 180040 180040) (.seq (andS 180049 180043 180040) (.seq (notS 180047 180043)
  (.seq (notS 180048 180039) (.seq (andS 180041 180047 180048)
  (.seq (orS 180041 180049 180041 180043) (.seq (andS 180042 180047 180039)
    (orS 180042 180049 180042 180043)))))))))))

/-- The write set of the corner decision: the kernel, `180038 … 180043` and `180047 … 180049`. -/
def Bco (r : ℕ) : Bool :=
  Bk r || decide ((180038 ≤ r ∧ r < 180044) ∨ (180047 ≤ r ∧ r < 180050))

theorem co_one {d : ℕ} (hd : (180038 ≤ d ∧ d < 180044) ∨ (180047 ≤ d ∧ d < 180050)) {c c' : Config}
    (F : FrameB (fun r => decide (r = d)) c c') : FrameB Bco c c' :=
  frameB_mono F fun r hr => by
    unfold Bco at hr
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢
    omega

theorem co_two {d t : ℕ} (hd : (180038 ≤ d ∧ d < 180044) ∨ (180047 ≤ d ∧ d < 180050)) (ht : (180038 ≤ t ∧ t < 180044) ∨ (180047 ≤ t ∧ t < 180050))
    {c c' : Config} (F : FrameB (fun r => decide (r = d ∨ r = t)) c c') : FrameB Bco c c' :=
  frameB_mono F fun r hr => by
    unfold Bco at hr
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢
    omega

theorem co_bt {d : ℕ} (hd : (180038 ≤ d ∧ d < 180044) ∨ (180047 ≤ d ∧ d < 180050)) {c c' : Config} (F : FrameB (Bt d) c c') :
    FrameB Bco c c' :=
  frameB_mono F fun r hr => by
    unfold Bco at hr; unfold Bt
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢
    exact ⟨hr.1, by omega⟩

theorem logicE_exec {P : Polygon} {W : ℕ} (hW : 8 ≤ W) (c : Config) (hw : WordsBounded W c)
    (h11 : c.nreg 180011 = 1) (b38 : c.nreg 180038 ≤ 1) (b39 : c.nreg 180039 ≤ 1)
    (b40 : c.nreg 180040 ≤ 1) :
    ∃ c' k, Exec P W logicE c c' k ∧ k ≤ 30 ∧ FrameB Bco c c' ∧
      c'.nreg 180041 ≤ 1 ∧ c'.nreg 180042 ≤ 1 ∧
      (c'.nreg 180041 = 1 ↔ ((c.nreg 180038 = 1 ↔ c.nreg 180039 = 1) ∧ c.nreg 180040 = 0) ∨
        (¬ (c.nreg 180038 = 1 ↔ c.nreg 180039 = 1) ∧ c.nreg 180039 = 0)) ∧
      (c'.nreg 180042 = 1 ↔ ((c.nreg 180038 = 1 ↔ c.nreg 180039 = 1) ∧ c.nreg 180040 = 0) ∨
        (¬ (c.nreg 180038 = 1 ↔ c.nreg 180039 = 1) ∧ c.nreg 180039 = 1)) := by
  have W2 : 2 ≤ W := by omega
  obtain ⟨c1, k1, e1, hk1, v1, F1⟩ := andS_exec (P := P) W2 c hw (d := 180043) (x := 180038)
    (y := 180039) (by decide) h11 b38 b39
  have o1 : c1.nreg 180011 = 1 := by rw [fr1 F1 (by decide), h11]
  have a38 : c1.nreg 180038 = c.nreg 180038 := fr1 F1 (by decide)
  have a39 : c1.nreg 180039 = c.nreg 180039 := fr1 F1 (by decide)
  obtain ⟨c2, k2, e2, hk2, v2, F2⟩ := orS_exec (P := P) W2 c1 e1.wb_right (d := 180047)
    (x := 180038) (y := 180039) (t := 180048) (by decide) (by decide) (by decide) o1
    (by rwx [a38]) (by rwx [a39])
  have o2 : c2.nreg 180011 = 1 := by rw [fr2 F2 (by decide) (by decide), o1]
  obtain ⟨c3, k3, e3, hk3, v3, F3⟩ := notS_exec (P := P) c2 e2.wb_right (d := 180047)
    (x := 180047) (by decide) o2
  have x43 : c3.nreg 180043 = c.nreg 180038 + c.nreg 180039 - 1 := by
    rw [fr1 F3 (by decide), fr2 F2 (by decide) (by decide), v1]
  have x47 : c3.nreg 180047 = 1 - ((c.nreg 180038 + c.nreg 180039) -
      (c.nreg 180038 + c.nreg 180039 - 1)) := by rw [v3, v2, a38, a39]
  have e4 := Exec.addN (P := P) e3.wb_right 180043 180043 180047 (by rwo [x43, x47])
  set c4 : Config := { c3 with nreg := upd c3.nreg 180043 (c3.nreg 180043 + c3.nreg 180047) }
    with hc4
  have F4 : FrameB (fun r => decide (r = 180043)) c3 c4 :=
    ⟨fun r hr => by simp only [decide_eq_false_iff_not] at hr; simp [hc4, hr], fun r _ => rfl,
      rfl, rfl, rfl⟩
  have EQ : c4.nreg 180043 ≤ 1 ∧ (c4.nreg 180043 = 1 ↔ (c.nreg 180038 = 1 ↔ c.nreg 180039 = 1)) := by
    have : c4.nreg 180043 = c3.nreg 180043 + c3.nreg 180047 := by simp [hc4]
    rwo [this, x43, x47]
  have o4 : c4.nreg 180011 = 1 := by rw [fr1 F4 (by decide), fr1 F3 (by decide), o2]
  have y40 : c4.nreg 180040 = c.nreg 180040 := by
    rw [fr1 F4 (by decide), fr1 F3 (by decide), fr2 F2 (by decide) (by decide), fr1 F1 (by decide)]
  obtain ⟨c5, k5, e5, hk5, v5, F5⟩ := notS_exec (P := P) c4 (by simpa [hc4] using e4.wb_right)
    (d := 180040) (x := 180040) (by decide) o4
  have N5 := not_bit (show c4.nreg 180040 ≤ 1 by rwx [y40])
  rw [← v5, y40] at N5
  have o5 : c5.nreg 180011 = 1 := by rw [fr1 F5 (by decide), o4]
  have z43 : c5.nreg 180043 = c4.nreg 180043 := fr1 F5 (by decide)
  obtain ⟨c6, k6, e6, hk6, v6, F6⟩ := andS_exec (P := P) W2 c5 e5.wb_right (d := 180049)
    (x := 180043) (y := 180040) (by decide) o5 (by rw [z43]; exact EQ.1) N5.1
  have A6 := and_bit (show c5.nreg 180043 ≤ 1 by rw [z43]; exact EQ.1) N5.1
  rw [← v6, z43, EQ.2, N5.2] at A6
  have o6 : c6.nreg 180011 = 1 := by rw [fr1 F6 (by decide), o5]
  have z43' : c6.nreg 180043 = c4.nreg 180043 := by rw [fr1 F6 (by decide), z43]
  obtain ⟨c7, k7, e7, hk7, v7, F7⟩ := notS_exec (P := P) c6 e6.wb_right (d := 180047)
    (x := 180043) (by decide) o6
  have N7 := not_bit (show c6.nreg 180043 ≤ 1 by rw [z43']; exact EQ.1)
  rw [← v7, z43', bit_of EQ.1 EQ.2] at N7
  have o7 : c7.nreg 180011 = 1 := by rw [fr1 F7 (by decide), o6]
  have y39 : c7.nreg 180039 = c.nreg 180039 := by
    rw [fr1 F7 (by decide), fr1 F6 (by decide), fr1 F5 (by decide), fr1 F4 (by decide),
      fr1 F3 (by decide), fr2 F2 (by decide) (by decide), a39]
  obtain ⟨c8, k8, e8, hk8, v8, F8⟩ := notS_exec (P := P) c7 e7.wb_right (d := 180048)
    (x := 180039) (by decide) o7
  have N8 := not_bit (show c7.nreg 180039 ≤ 1 by rwx [y39])
  rw [← v8, y39] at N8
  have o8 : c8.nreg 180011 = 1 := by rw [fr1 F8 (by decide), o7]
  have z47 : c8.nreg 180047 = c7.nreg 180047 := fr1 F8 (by decide)
  obtain ⟨c9, k9, e9, hk9, v9, F9⟩ := andS_exec (P := P) W2 c8 e8.wb_right (d := 180041)
    (x := 180047) (y := 180048) (by decide) o8 (by rw [z47]; exact N7.1) N8.1
  have A9 := and_bit (show c8.nreg 180047 ≤ 1 by rw [z47]; exact N7.1) N8.1
  rw [← v9, z47, N7.2, N8.2] at A9
  have o9 : c9.nreg 180011 = 1 := by rw [fr1 F9 (by decide), o8]
  have z49 : c9.nreg 180049 = c6.nreg 180049 := by
    rw [fr1 F9 (by decide), fr1 F8 (by decide), fr1 F7 (by decide)]
  obtain ⟨c10, k10, e10, hk10, v10, F10⟩ := orS_exec (P := P) W2 c9 e9.wb_right (d := 180041)
    (x := 180049) (y := 180041) (t := 180043) (by decide) (by decide) (by decide) o9
    (by rw [z49]; exact A6.1) A9.1
  have O10 := or_bit (show c9.nreg 180049 ≤ 1 by rw [z49]; exact A6.1) A9.1
  rw [← v10, z49, A6.2, A9.2] at O10
  have o10 : c10.nreg 180011 = 1 := by rw [fr2 F10 (by decide) (by decide), o9]
  have z47' : c10.nreg 180047 = c7.nreg 180047 := by
    rw [fr2 F10 (by decide) (by decide), fr1 F9 (by decide), z47]
  have y39' : c10.nreg 180039 = c.nreg 180039 := by
    rw [fr2 F10 (by decide) (by decide), fr1 F9 (by decide), fr1 F8 (by decide), y39]
  obtain ⟨c11, k11, e11, hk11, v11, F11⟩ := andS_exec (P := P) W2 c10 e10.wb_right (d := 180042)
    (x := 180047) (y := 180039) (by decide) o10 (by rw [z47']; exact N7.1)
    (by rwx [y39'])
  have A11 := and_bit (show c10.nreg 180047 ≤ 1 by rw [z47']; exact N7.1)
    (show c10.nreg 180039 ≤ 1 by rwx [y39'])
  rw [← v11, z47', y39', N7.2] at A11
  have o11 : c11.nreg 180011 = 1 := by rw [fr1 F11 (by decide), o10]
  have z49' : c11.nreg 180049 = c6.nreg 180049 := by
    rw [fr1 F11 (by decide), fr2 F10 (by decide) (by decide), z49]
  obtain ⟨c12, k12, e12, hk12, v12, F12⟩ := orS_exec (P := P) W2 c11 e11.wb_right (d := 180042)
    (x := 180049) (y := 180042) (t := 180043) (by decide) (by decide) (by decide) o11
    (by rw [z49']; exact A6.1) A11.1
  have O12 := or_bit (show c11.nreg 180049 ≤ 1 by rw [z49']; exact A6.1) A11.1
  rw [← v12, z49', A6.2, A11.2] at O12
  have g41 : c12.nreg 180041 = c10.nreg 180041 := by
    rw [fr2 F12 (by decide) (by decide), fr1 F11 (by decide)]
  have ex : Exec P W logicE c c12 (k1 + (k2 + (k3 + (1 + (k5 + (k6 + (k7 + (k8 + (k9 + (k10 +
      (k11 + k12))))))))))) :=
    .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 (.seq e6 (.seq e7 (.seq e8 (.seq e9 (.seq e10
      (.seq e11 e12))))))))))
  refine ⟨c12, _, ex, by omega, ?_, by rw [g41]; exact O10.1, O12.1, by rw [g41, O10.2],
    by rw [O12.2]⟩
  have G1 := co_one (by omega) F1
  have G2 := co_two (by omega) (by omega) F2
  have G3 := co_one (by omega) F3
  have G4 := co_one (by omega) F4
  have G5 := co_one (by omega) F5
  have G6 := co_one (by omega) F6
  have G7 := co_one (by omega) F7
  have G8 := co_one (by omega) F8
  have G9 := co_one (by omega) F9
  have G10 := co_two (by omega) (by omega) F10
  have G11 := co_one (by omega) F11
  have G12 := co_two (by omega) (by omega) F12
  exact ((((((((((G1.trans G2).trans G3).trans G4).trans G5).trans G6).trans G7).trans G8).trans
    G9).trans G10).trans G11).trans G12

/-! ## The corner decision -/

/-- The three tests and the combination. -/
def generalS : Stmt :=
  .seq (testS 1 (.v 180035) (.v 180036) (.v 180035) 180038)
    (.seq (testS 1 (.v 180035) (.v 180037) (.v 180035) 180039)
      (.seq (testS 2 (.v 180036) (.v 180035) (.v 180037) 180040) logicE))

/-- The corner decision: east only at position `0`, west only at position `2m`. -/
def cornerS : Stmt :=
  .ifLtN 180028 180030
    (.ifLtN 180030 180012 generalS (block [.constN 180041 0, .constN 180042 1]))
    (block [.constN 180041 1, .constN 180042 0])

theorem emit_general {C : Chain} (hDH : DistinctHeights C.P) {i d : ℕ} (_hi0 : 0 < i)
    (hi : i < 2 * C.m) {t1 t2 t3 : Prop} (h1 : t1 ↔ (vPt C i).2 < (prevPt C i).2)
    (h2 : t2 ↔ (vPt C i).2 < (nextPt C i).2)
    (h3 : t3 ↔ 0 < det (prevPt C i) (vPt C i) (nextPt C i)) :
    (Emit C i d ↔ ((t1 ↔ t2) ∧ ¬ t3) ∨ (¬ (t1 ↔ t2) ∧ (if d = 0 then ¬ t2 else t2))) := by
  have hne := nextPt_ne hDH (C := C) (i := i) hi.le
  unfold Emit emitR
  simp only [h1, h2, h3]
  by_cases hp : ((vPt C i).2 < (prevPt C i).2 ↔ (vPt C i).2 < (nextPt C i).2)
  · rw [ite_eq_left hp]; simp only [hp, true_and, not_true_eq_false, false_and, or_false]
  · rw [ite_eq_right hp]
    simp only [hp, false_and, false_or, not_false_eq_true, true_and]
    by_cases hd : d = 0
    · subst hd; rw [sig_zero, ite_eq_left rfl]
      constructor
      · intro h h'; exact absurd (h.1 rfl) (not_lt.2 h'.le)
      · intro h; exact ⟨fun _ => lt_of_le_of_ne (not_lt.1 h) hne, fun _ => rfl⟩
    · rw [sig_one hd, ite_eq_right hd]
      constructor
      · intro h; by_contra h'
        have := h.2 (lt_of_le_of_ne (not_lt.1 h') hne); norm_num at this
      · intro h; exact ⟨fun e => by norm_num at e, fun h' => absurd h (not_lt.2 h'.le)⟩

/-- **The corner decision** at tour position `i ≤ 2m`. -/
theorem cornerS_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 8 ≤ W) {C : Chain}
    (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) {i : ℕ} (hi : i ≤ 2 * C.m) (c : Config)
    (hw : WordsBounded W c) (h11 : c.nreg 180011 = 1) (h12 : c.nreg 180012 = 2 * C.m)
    (h28 : c.nreg 180028 = 0) (h30 : c.nreg 180030 = i)
    (h35 : c.nreg 180035 = C.s + C.sideIdx C.sideBeta i)
    (h36 : 0 < i → c.nreg 180036 = C.s + C.sideIdx C.sideBeta (i - 1))
    (h37 : i < 2 * C.m → c.nreg 180037 = C.s + C.sideIdx C.sideBeta (i + 1)) :
    ∃ c' k, Exec P W cornerS c c' k ∧ k ≤ 800 ∧ FrameB Bco c c' ∧ c'.nreg 180041 ≤ 1 ∧
      c'.nreg 180042 ≤ 1 ∧ (c'.nreg 180041 = 1 ↔ Emit C i 0) ∧
      (c'.nreg 180042 = 1 ↔ Emit C i 1) := by
  have hDH : DistinctHeights C.P := by rw [hC]; exact (goodShear_epsOf hG.2).2.1
  have hl := fun j => C.sideIdx_le C.sideBeta j
  have frc : ∀ (v1 v2 : ℕ), FrameB Bco c
      { c with nreg := upd (upd c.nreg 180041 v1) 180042 v2 } := fun v1 v2 =>
    ⟨fun r hr => by
      unfold Bco at hr; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
      simp (disch := omega) only [Config.nreg_mk, Machine.upd_other], fun r _ => rfl, rfl, rfl, rfl⟩
  by_cases hi0 : i = 0
  · subst hi0
    obtain ⟨c', k, e, hk, q41, q42, R⟩ : ∃ c' k, Exec P W
        (block [.constN 180041 1, .constN 180042 0]) c c' k ∧ k = 2 ∧ c'.nreg 180041 = 1 ∧
        c'.nreg 180042 = 0 ∧ FrameB Bco c c' := by
      exec_block
      · omega
      · omega
      · exact ⟨rfl, by config_simp, by config_simp, frc 1 0⟩
    refine ⟨c', _, .ifLtN_false (by rwo [h28, h30]) e, by omega, R, by omega, by omega,
      ?_, ?_⟩
    · rw [q41]; unfold Emit; rw [emitR_zero hDH, sig_zero]; exact ⟨fun _ => rfl, fun _ => rfl⟩
    · rw [q42]; unfold Emit; rwn [emitR_zero hDH, sig_one (by omega)]
  by_cases hil : i = 2 * C.m
  · subst hil
    obtain ⟨c', k, e, hk, q41, q42, R⟩ : ∃ c' k, Exec P W
        (block [.constN 180041 0, .constN 180042 1]) c c' k ∧ k = 2 ∧ c'.nreg 180041 = 0 ∧
        c'.nreg 180042 = 1 ∧ FrameB Bco c c' := by
      exec_block
      · omega
      · omega
      · exact ⟨rfl, by config_simp, by config_simp, frc 0 1⟩
    refine ⟨c', _, .ifLtN_true (by rwo [h28, h30])
      (.ifLtN_false (by rwo [h30, h12]) e), by omega, R, by omega, by omega, ?_, ?_⟩
    · rw [q41]; unfold Emit; rwn [emitR_two_m hDH (sig_cases 0), sig_zero]
    · rw [q42]; urs Emit [emitR_two_m hDH (sig_cases 1), sig_one (by omega)]
  -- the general case
  have lk : C.s + C.sideIdx C.sideBeta i < P.n := by have := hl i; omega
  have lp : C.s + C.sideIdx C.sideBeta (i - 1) < P.n := by have := hl (i - 1); omega
  have ln : C.s + C.sideIdx C.sideBeta (i + 1) < P.n := by have := hl (i + 1); omega
  have e36 := h36 (by omega)
  have e37 := h37 (by omega)
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, b38, t38⟩ := testV_exec (P := P) hG (by omega) (op := 1) (by omega)
    (r₁ := 180035) (r₂ := 180036) (r₃ := 180035) (d := 180038) (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr (by omega)) c hw h35 e36 h35 lk lp lk
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, b39, t39⟩ := testV_exec (P := P) hG (by omega) (op := 1) (by omega)
    (r₁ := 180035) (r₂ := 180037) (r₃ := 180035) (d := 180039) (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr (by omega)) c₁ e₁.wb_right (by rw [F₁.1 _ (by decide), h35])
    (by rw [F₁.1 _ (by decide), e37]) (by rw [F₁.1 _ (by decide), h35]) lk ln lk
  obtain ⟨c₃, k₃, e₃, hk₃, F₃, b40, t40⟩ := testV_exec (P := P) hG (by omega) (op := 2) (by omega)
    (r₁ := 180036) (r₂ := 180035) (r₃ := 180037) (d := 180040) (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr (by omega)) c₂ e₂.wb_right
    (by rw [F₂.1 _ (by decide), F₁.1 _ (by decide), e36])
    (by rw [F₂.1 _ (by decide), F₁.1 _ (by decide), h35])
    (by rw [F₂.1 _ (by decide), F₁.1 _ (by decide), e37]) lp lk ln
  have r38 : c₃.nreg 180038 = c₁.nreg 180038 := by rw [F₃.1 _ (by decide), F₂.1 _ (by decide)]
  have r39 : c₃.nreg 180039 = c₂.nreg 180039 := F₃.1 _ (by decide)
  obtain ⟨c₄, k₄, e₄, hk₄, F₄, b41, b42, t41, t42⟩ := logicE_exec (P := P) (by omega) c₃
    e₃.wb_right (by rw [F₃.1 _ (by decide), F₂.1 _ (by decide), F₁.1 _ (by decide), h11])
    (by rwx [r38]) (by rwx [r39]) b40
  rw [r38, r39] at t41 t42
  simp only [SignTest] at t38 t39 t40
  -- geometric points
  have ev : (Qof P).vtx (C.s + C.sideIdx C.sideBeta i) = vPt C i :=
    vtxQ hC hsn (by have := hl i; omega) lk
  have ep : (Qof P).vtx (C.s + C.sideIdx C.sideBeta (i - 1)) = prevPt C i := by
    rw [vtxQ hC hsn (by have := hl (i - 1); omega) lp]; unfold prevPt; rw [ite_eq_right hi0]
  have en : (Qof P).vtx (C.s + C.sideIdx C.sideBeta (i + 1)) = nextPt C i := by
    rw [vtxQ hC hsn (by have := hl (i + 1); omega) ln]; unfold nextPt; rw [ite_eq_right hil]
  rw [ev, ep] at t38
  rw [ev, en] at t39
  rw [ev, ep, en] at t40
  have n39 := bit_of b39 t39
  have n40 := bit_of b40 t40
  have ex : Exec P W cornerS c c₄ (k₁ + (k₂ + (k₃ + k₄)) + 1 + 1) :=
    .ifLtN_true (by rwo [h28, h30]) (.ifLtN_true (by rwo [h30, h12])
      (.seq e₁ (.seq e₂ (.seq e₃ e₄))))
  refine ⟨c₄, _, ex, by omega, (((co_bt (by omega) F₁).trans (co_bt (by omega) F₂)).trans
    (co_bt (by omega) F₃)).trans F₄, b41, b42, ?_, ?_⟩
  · have e40 : c₃.nreg 180040 = 0 ↔ ¬ c₃.nreg 180040 = 1 := by omega
    have e39 : c₂.nreg 180039 = 0 ↔ ¬ c₂.nreg 180039 = 1 := by omega
    rw [t41, emit_general hDH (by omega) (by omega) t38 t39 t40, ite_eq_left rfl, e40, e39]
  · have e40 : c₃.nreg 180040 = 0 ↔ ¬ c₃.nreg 180040 = 1 := by omega
    rw [t42, emit_general hDH (by omega) (by omega) t38 t39 t40, ite_eq_right (by omega), e40]

end

end Brute

end Chazelle.Core
