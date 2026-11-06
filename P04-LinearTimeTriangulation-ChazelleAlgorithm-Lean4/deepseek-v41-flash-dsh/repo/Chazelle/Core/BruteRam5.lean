module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.BruteRam4

/-!
# WP-K on the RAM, part 5: the far edge and the emission of a chord

`farS d` turns the result of the scan into `farEdge C k (sig d)` (register `180082`);
`writeS d` stores the triple `(a + k, lp, rp)` at the next address (`180024`) and counts it
(`180019`); `emitS d = scanS d ; farS d ; writeS d` (`emitS_exec`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace Brute

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-- `x mod 2m` for `x < 4m`, by one comparison. -/
def modS : Stmt := .ifLtN 180083 180012 (.instr (.copyN 180082 180083))
  (.instr (.subN 180082 180083 180012))

theorem mod_small {x M : ℕ} (_hM : 0 < M) (hx : x < 2 * M) : x % M = if x < M then x else x - M := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · Ξ Nat.mod_eq_sub_mod (⋄), Nat.mod_eq_of_lt (⋄)

theorem modS_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {M : ℕ}
    (hM : 0 < M) (h12 : c.nreg 180012 = M) (hx : c.nreg 180083 < 2 * M) :
    ∃ c' k', Exec P W modS c c' k' ∧ k' ≤ 3 ∧ c'.nreg 180082 = c.nreg 180083 % M ∧
      FrameB (fun r => decide (r = 180082)) c c' := by
  have fr : ∀ v, FrameB (fun r => decide (r = 180082)) c
      { c with nreg := upd c.nreg 180082 v } := fun v =>
    ⟨fun r hr => by simp only [decide_eq_false_iff_not] at hr; simp [hr], fun r _ => rfl, rfl,
      rfl, rfl⟩
  Ξ mod_small hM hx
  by_cases h : c.nreg 180083 < M
  · exact ⟨_, _, .ifLtN_true (by rw [h12]; exact h) (Exec.copyN hw 180082 180083), ⋄,
      ⊚ h, fr _⟩
  · exact ⟨_, _, .ifLtN_false (by rw [h12]; exact h) (Exec.subN hw 180082 180083 180012),
      ⋄, ⊚ h, h12, fr _⟩

/-- The forward tour position of the chain edge `best`. -/
def fwdS : Stmt := .seq (block [.addN 180083 180052 180012, .subN 180083 180083 180015]) modS

/-- The backward tour position. -/
def bwdS : Stmt := .seq (block [.subN 180083 180012 180011, .subN 180083 180083 180052,
  .addN 180083 180083 180012, .subN 180083 180083 180015]) modS

/-- The far walk edge. -/
def farS (d : ℕ) : Stmt :=
  .ifLtN 180051 180011 (.instr (.constN 180082 (if d = 0 then 3 else 1)))
    (.seq (block [.addN 180055 180000 180052, .addN 180080 180055 180011])
      (.seq (testS 2 (.v 180055) (.v 180080) (.v 180035) 180081)
        (.seq (.ifLtN 180081 180011 bwdS fwdS) (.instr (.addN 180082 180082 180027)))))

/-- The registers the far edge reads (beyond `SI`). -/
def FI (C : Chain) (c : Config) : Prop :=
  c.nreg 180012 = 2 * C.m ∧ c.nreg 180015 = tS C ∧ c.nreg 180027 = 6

theorem FI.keep {C : Chain} {c c' : Config} (h : FI C c) (F : FrameB Bsc c c') : FI C c' :=
  ⟨by rw [F.1 _ (⌖), h.1], by rw [F.1 _ (⌖), h.2.1], by rw [F.1 _ (by decide), h.2.2]⟩

theorem fwdS_exec {P : Polygon} {W : ℕ} {C : Chain} (c : Config) (hw : WordsBounded W c)
    (hF : FI C c) {b : ℕ} (hb : c.nreg 180052 = b) (hbm : b < C.m) (hW : 4 * C.m ≤ W) :
    ∃ c' k', Exec P W fwdS c c' k' ∧ k' ≤ 5 ∧ c'.nreg 180082 = fwdIdx C.m (tS C) b ∧
      FrameB Bsc c c' := by
  obtain ⟨h12, h15, -⟩ := hF
  have hS := C.sideS_lt C.sideBeta
  have hm := C.one_le
  obtain ⟨c₁, k₁, e₁, hk₁, q83, R₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.addN 180083 180052 180012, .subN 180083 180083 180015]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 180083 = b + 2 * C.m - tS C ∧ FrameB (fun r => decide (r = 180083)) c c₁ := by
    exec_block
    · config_simp; rw [hb, h12]; omega
    · refine ⟨rfl, ?_, ⟨fun r hr => ?_, fun r _ => rfl, rfl, rfl, rfl⟩⟩
      · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
        Ξ hb, h12, h15
      · ϴ' decide_eq_false_iff_not at hr
        simp (disch := omega) only [Config.nreg_mk, Machine.upd_other]
  obtain ⟨c₂, k₂, e₂, hk₂, q82, R₂⟩ := modS_exec (P := P) c₁ e₁.wb_right (M := 2 * C.m)
    (⋄) (Ρ fr1 R₁ (⌖), h12) (by rw [q83]; unfold tS; omega)
  refine ⟨c₂, _, .seq e₁ e₂, ⋄, by rw [q82, q83]; rfl,
    (sc_of_one (⋄) R₁).trans (sc_of_one (⋄) R₂)⟩

theorem bwdS_exec {P : Polygon} {W : ℕ} {C : Chain} (c : Config) (hw : WordsBounded W c)
    (hF : FI C c) (h11 : c.nreg 180011 = 1) {b : ℕ} (hb : c.nreg 180052 = b) (hbm : b < C.m)
    (hW : 4 * C.m ≤ W) :
    ∃ c' k', Exec P W bwdS c c' k' ∧ k' ≤ 7 ∧ c'.nreg 180082 = bwdIdx C.m (tS C) b ∧
      FrameB Bsc c c' := by
  obtain ⟨h12, h15, -⟩ := hF
  have hS := C.sideS_lt C.sideBeta
  have hm := C.one_le
  obtain ⟨c₁, k₁, e₁, hk₁, q83, R₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.subN 180083 180012 180011, .subN 180083 180083 180052,
        .addN 180083 180083 180012, .subN 180083 180083 180015]) c c₁ k₁ ∧ k₁ = 4 ∧
      c₁.nreg 180083 = 2 * C.m - 1 - b + 2 * C.m - tS C ∧
      FrameB (fun r => decide (r = 180083)) c c₁ := by
    exec_block
    · config_simp; rw [hb, h12, h11]; omega
    · refine ⟨rfl, ?_, ⟨fun r hr => ?_, fun r _ => rfl, rfl, rfl, rfl⟩⟩
      · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
        Ξ hb, h12, h15, h11
      · ϴ' decide_eq_false_iff_not at hr
        simp (disch := omega) only [Config.nreg_mk, Machine.upd_other]
  obtain ⟨c₂, k₂, e₂, hk₂, q82, R₂⟩ := modS_exec (P := P) c₁ e₁.wb_right (M := 2 * C.m)
    (⋄) (Ρ fr1 R₁ (⌖), h12) (by rw [q83]; unfold tS; omega)
  refine ⟨c₂, _, .seq e₁ e₂, ⋄, by rw [q82, q83]; rfl,
    (sc_of_one (⋄) R₁).trans (sc_of_one (⋄) R₂)⟩

theorem farEdge_none {C : Chain} {k : ℕ} {σ : ℝ} (h : scan C k σ C.m = none) :
    farEdge C k σ = if σ = 1 then 3 else 1 := by
  unfold farEdge; ϴ h

theorem farEdge_some {C : Chain} {k : ℕ} {σ : ℝ} {b : ℕ} (h : scan C k σ C.m = some b) :
    farEdge C k σ = (if 0 < det (C.vertex b) (C.vertex (b + 1)) (C.vertex k) then
      fwdIdx C.m (tS C) b else bwdIdx C.m (tS C) b) + 6 := by
  unfold farEdge; ϴ h


theorem farS_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 8 ≤ W) (hW4 : 4 * P.n ≤ W)
    {C : Chain} (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) {d k : ℕ} (hd : d ≤ 1)
    (hk : k ≤ C.m) (c : Config) (hw : WordsBounded W c) (hS : SI C (C.s + k) c) (hF : FI C c)
    (hE : Enc (c.nreg 180051) (c.nreg 180052) (scan C k (sig d) C.m)) :
    ∃ c' k', Exec P W (farS d) c c' k' ∧ k' ≤ 270 ∧ FrameB Bsc c c' ∧
      c'.nreg 180082 = farEdge C k (sig d) := by
  obtain ⟨h0, h1, h11, h35⟩ := hS
  rcases hsc : scan C k (sig d) C.m with _ | b
  · rw [hsc] at hE
    simp only [Enc] at hE
    have e := Exec.constN (P := P) hw 180082 (if d = 0 then 3 else 1) (by split_ifs <;> omega)
    refine ⟨_, _, .ifLtN_true (by rw [hE, h11]; omega) e, by omega,
      ⟨fun r hr => ?_, fun r _ => rfl, rfl, rfl, rfl⟩, ?_⟩
    · have : r ≠ 180082 := by
        unfold Bsc at hr; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr; omega
      simp [this]
    · rw [farEdge_none hsc]
      simp only [Config.nreg_mk, Machine.upd_same]
      by_cases h0 : d = 0
      · subst h0; rw [sig_zero]; simp
      · rw [ite_eq_right h0, sig_one h0, ite_eq_right (by norm_num)]
  · rw [hsc] at hE
    simp only [Enc] at hE
    obtain ⟨hf, hb⟩ := hE
    have hbm : b < C.m := (scan_some hsc).1
    obtain ⟨c₁, k₁, e₁, hk₁, q55, q80, R₁⟩ : ∃ c₁ k₁, Exec P W
        (block [.addN 180055 180000 180052, .addN 180080 180055 180011]) c c₁ k₁ ∧ k₁ = 2 ∧
        c₁.nreg 180055 = C.s + b ∧ c₁.nreg 180080 = C.s + b + 1 ∧
        FrameB (fun r => decide (r = 180055 ∨ r = 180080)) c c₁ := by
      exec_block
      · config_simp; rw [h0, hb]; omega
      · config_simp; rw [h0, hb, h11]; omega
      · refine ⟨rfl, ?_, ?_, ⟨fun r hr => ?_, fun r _ => rfl, rfl, rfl, rfl⟩⟩
        · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
          rw [h0, hb]
        · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
          rw [h0, hb, h11]
        · simp only [decide_eq_false_iff_not, not_or] at hr
          simp (disch := omega) only [Config.nreg_mk, Machine.upd_other]
    have G₁ := sc_of_two (by omega) (by omega) R₁
    obtain ⟨c₂, k₂, e₂, hk₂, F₂, b81, t81⟩ := testV_exec (P := P) hG (by omega) (op := 2)
      (by omega) (r₁ := 180055) (r₂ := 180080) (r₃ := 180035) (d := 180081) (Or.inr (by omega))
      (Or.inr (by omega)) (Or.inr (by omega)) c₁ e₁.wb_right q55 q80
      (by rw [G₁.1 _ (by decide), h35]) (by omega) (by omega) (by omega)
    simp only [SignTest] at t81
    rw [vtxQ hC hsn (by omega) (by omega), show C.s + b + 1 = C.s + (b + 1) by ring,
      vtxQ hC hsn (by omega) (by omega), vtxQ hC hsn (by omega) (by omega)] at t81
    have G₂ := G₁.trans (sc_of_bt (by omega) F₂)
    have F₂' := hF.keep G₂
    have k11 : c₂.nreg 180011 = 1 := by rw [G₂.1 _ (by decide), h11]
    have k52 : c₂.nreg 180052 = b := by rw [F₂.1 _ (by decide), fr2 R₁ (by decide) (by decide), hb]
    have hWm : 4 * C.m ≤ W := by omega
    have w₂ := e₂.wb_right
    obtain ⟨c₃, k₃, e₃, hk₃, q82, G₃⟩ : ∃ c₃ k₃, Exec P W (.ifLtN 180081 180011 bwdS fwdS) c₂ c₃ k₃ ∧
        k₃ ≤ 9 ∧ c₃.nreg 180082 = (if 0 < det (C.vertex b) (C.vertex (b + 1)) (C.vertex k) then
          fwdIdx C.m (tS C) b else bwdIdx C.m (tS C) b) ∧ FrameB Bsc c₂ c₃ := by
      by_cases hdt : 0 < det (C.vertex b) (C.vertex (b + 1)) (C.vertex k)
      · obtain ⟨c', k', e', hk', q', G'⟩ := fwdS_exec (P := P) c₂ w₂ F₂' k52 hbm hWm
        exact ⟨c', _, .ifLtN_false (by rw [t81.2 hdt, k11]; omega) e', by omega,
          by rw [q', ite_eq_left hdt], G'⟩
      · have h0' : c₂.nreg 180081 = 0 := by have := mt t81.1 hdt; omega
        obtain ⟨c', k', e', hk', q', G'⟩ := bwdS_exec (P := P) c₂ w₂ F₂' k11 k52 hbm hWm
        exact ⟨c', _, .ifLtN_true (by rw [h0', k11]; omega) e', by omega,
          by rw [q', ite_eq_right hdt], G'⟩
    have F₃' := F₂'.keep G₃
    have e₄ := Exec.addN (P := P) e₃.wb_right 180082 180082 180027 (by
      rw [q82, F₃'.2.2]
      have h1 := (fwdIdx_spec (C := C) hbm).1
      have h2 := (bwdIdx_spec (C := C) hbm).1
      split_ifs <;> omega)
    refine ⟨_, _, .ifLtN_false (by rw [hf, h11]; omega) (.seq e₁ (.seq e₂ (.seq e₃ e₄))),
      by omega, (G₂.trans G₃).trans ⟨fun r hr => ?_, fun r _ => rfl, rfl, rfl, rfl⟩, ?_⟩
    · have : r ≠ 180082 := by
        unfold Bsc at hr; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr; omega
      simp [this]
    · rw [farEdge_some hsc]
      simp only [Config.nreg_mk, Machine.upd_same]
      rw [q82, F₃'.2.2]

/-! ## Writing the triple -/

/-- Store the triple of direction `d`. -/
def writeS (d : ℕ) : Stmt :=
  .seq (putS 180024 180035) (.seq (putS 180024 (if d = 0 then 180044 else 180082))
    (.seq (putS 180024 (if d = 0 then 180082 else 180044)) (.instr (.addN 180019 180019 180011))))

/-- The write set of an emission. -/
def Bem (r : ℕ) : Bool := Bsc r || decide (r = 180024 ∨ r = 180019)

theorem writeS_exec {P : Polygon} {W : ℕ} {d : ℕ} (c : Config) (hw : WordsBounded W c) {A len : ℕ}
    (h24 : c.nreg 180024 = A) (h19 : c.nreg 180019 = len) (h11 : c.nreg 180011 = 1)
    (hA : A + 3 ≤ W) (hl : len + 1 ≤ W) :
    ∃ c' k', Exec P W (writeS d) c c' k' ∧ k' = 7 ∧ c'.nreg 180024 = A + 3 ∧
      c'.nreg 180019 = len + 1 ∧
      c'.nmem = upd (upd (upd c.nmem A (c.nreg 180035)) (A + 1)
        (c.nreg (if d = 0 then 180044 else 180082))) (A + 2)
        (c.nreg (if d = 0 then 180082 else 180044)) ∧
      (∀ r, r ≠ 180024 → r ≠ 180019 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hv1 : (if d = 0 then 180044 else 180082) ≠ 180024 := by split_ifs <;> decide
  have hv2 : (if d = 0 then 180082 else 180044) ≠ 180024 := by split_ifs <;> decide
  obtain ⟨c₁, k₁, e₁, hk₁, p₁, m₁, R₁, rr₁, rm₁, o₁⟩ := putS_exec (P := P) c hw (p := 180024)
    (v := 180035) (⌖) h11 (⋄)
  obtain ⟨c₂, k₂, e₂, hk₂, p₂, m₂, R₂, rr₂, rm₂, o₂⟩ := putS_exec (P := P) c₁ e₁.wb_right
    (p := 180024) (v := if d = 0 then 180044 else 180082) (⌖)
    (Ρ R₁ _ (⌖), h11) (by rw [p₁, h24]; omega)
  obtain ⟨c₃, k₃, e₃, hk₃, p₃, m₃, R₃, rr₃, rm₃, o₃⟩ := putS_exec (P := P) c₂ e₂.wb_right
    (p := 180024) (v := if d = 0 then 180082 else 180044) (⌖)
    (Ρ R₂ _ (⌖), R₁ _ (⌖), h11) (by rw [p₂, p₁, h24]; omega)
  have e₄ := Exec.addN (P := P) e₃.wb_right 180019 180019 180011 (by
    rw [R₃ _ (⌖), R₂ _ (⌖), R₁ _ (⌖), R₃ _ (⌖), R₂ _ (⌖),
      R₁ _ (⌖), h19, h11]; exact hl)
  refine ⟨_, _, .seq e₁ (.seq e₂ (.seq e₃ e₄)), ⋄, ?_, ?_, ?_, fun r h1 h2 => ?_,
    by simp only; rw [rr₃, rr₂, rr₁], by simp only; rw [rm₃, rm₂, rm₁],
    by simp only; rw [o₃, o₂, o₁]⟩
  · simp only [Config.nreg_mk]; Ξ upd_other _ _ _ (⌖), p₃, p₂, p₁, h24
  · ϴ Config.nreg_mk, upd_same
    rw [R₃ _ (⌖), R₂ _ (⌖), R₁ _ (⌖), R₃ _ (⌖), R₂ _ (⌖),
      R₁ _ (⌖), h19, h11]
  · ϴ Config.nreg_mk
    Ξ m₃, m₂, m₁, p₂, p₁, h24, R₂ _ hv2, R₁ _ hv2, R₁ _ hv1
  · ϴ Config.nreg_mk
    Ξ upd_other _ _ _ h2, R₃ _ h1, R₂ _ h1, R₁ _ h1

/-- **Emit the chord of `v_k` in direction `d`.** -/
def emitS (d : ℕ) : Stmt := .seq (scanS d) (.seq (farS d) (writeS d))


theorem emitS_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 8 ≤ W) (hW4 : 4 * P.n ≤ W)
    {C : Chain} (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) {d k : ℕ} (hd : d ≤ 1)
    (hk : k ≤ C.m) (c : Config) (hw : WordsBounded W c) (hS : SI C (C.s + k) c) (hF : FI C c)
    {A len p : ℕ} (h24 : c.nreg 180024 = A) (h19 : c.nreg 180019 = len) (h44 : c.nreg 180044 = p)
    (hA : A + 3 ≤ W) (hl : len + 1 ≤ W) :
    ∃ c' k', Exec P W (emitS d) c c' k' ∧ k' ≤ 1602 * C.m + 282 ∧ 7 ≤ k' ∧ c'.nreg 180024 = A + 3 ∧
      c'.nreg 180019 = len + 1 ∧
      c'.nmem = upd (upd (upd c.nmem A (C.s + k)) (A + 1)
        (if d = 0 then p else farEdge C k (sig d))) (A + 2)
        (if d = 0 then farEdge C k (sig d) else p) ∧
      (∀ r, Bem r = false → c'.nreg r = c.nreg r) ∧ (∀ r, Bsc r = false → c'.rreg r = c.rreg r) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, E₁⟩ := scanS_exec (P := P) (d := d) hG hW hC hsn hk c hw hS
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, q82⟩ := farS_exec (P := P) (d := d) hG hW hW4 hC hsn hd hk c₁
    e₁.wb_right (hS.keep F₁) (hF.keep F₁) E₁
  have G := F₁.trans F₂
  obtain ⟨c₃, k₃, e₃, hk₃, p24, p19, m₃, R₃, rr₃, rm₃, o₃⟩ := writeS_exec (P := P) (d := d) c₂
    e₂.wb_right (A := A) (len := len) (by rw [G.1 _ (by decide), h24])
    (by rw [G.1 _ (by decide), h19]) (by rw [G.1 _ (by decide), hS.2.2.1]) hA hl
  have k35 : c₂.nreg 180035 = C.s + k := by rw [G.1 _ (by decide), hS.2.2.2]
  have k44 : c₂.nreg 180044 = p := by rw [G.1 _ (by decide), h44]
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega, by omega, p24, p19, ?_, fun r hr => ?_,
    fun r hr => by rw [rr₃, G.2.1 r hr], by rw [rm₃, G.2.2.2.1], by rw [o₃, G.2.2.2.2]⟩
  · rw [m₃, G.2.2.1, k35]
    by_cases h0 : d = 0
    · subst h0; simp only [ite_true]; rw [k44, q82]
    · simp only [ite_eq_right h0]; rw [k44, q82]
  · unfold Bem at hr
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_or] at hr
    rw [R₃ r hr.2.1 hr.2.2, G.1 r hr.1]

end

end Brute

end Chazelle.Core
