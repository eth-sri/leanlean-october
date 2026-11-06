module

public import Chazelle.Core.BruteRam3
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics
set_option maxHeartbeats 1000000

/-!
# WP-K on the RAM, part 4: the far-end scan

For the vertex `v_k` (index `qk = a + k` in `180035`) and the direction of code `d` (`0` east,
`1` west), `scanS d` runs over the chain edges `j < m` (`180050`) and keeps the nearest candidate
(`found` in `180051`, `best` in `180052`), exactly as `Brute.scan` (`scanS_exec`).
-/


namespace Chazelle.Core

namespace Brute

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-! ## Geometry of the tests -/

theorem vtxQ {P : Polygon} {C : Chain} (hC : C.P = Qof P) (_hsn : C.s + C.m + 1 ≤ P.n) {j : ℕ}
    (_hj : j ≤ C.m + 1) (hjn : C.s + j < P.n) : (Qof P).vtx (C.s + j) = C.vertex j := by
  have hn : C.P.n = P.n := by rw [hC]; exact shear_n _ _
  rw [vertex_eq (by rwx [hn]), hC]

theorem edgeXQ {P : Polygon} {C : Chain} (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) {j k : ℕ}
    (hj : j < C.m) (hk : k ≤ C.m) :
    edgeXAt (Qof P) (C.s + j) (C.s + k) = edgeXk C j k := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  unfold edgeXAt edgeXk Visibility.edgeX
  rw [Nat.mod_eq_of_lt (by rwo [hQn]), vtxQ hC hsn (by omega) (by omega),
    show C.s + j + 1 = C.s + (j + 1) by ring, vtxQ hC hsn (by omega) (by omega),
    vtxQ hC hsn (by omega) (by omega)]

/-- The encoding of the scan state: `found = 0`, or `found = 1` and `best`. -/
def Enc (found best : ℕ) : Option ℕ → Prop
  | none => found = 0
  | some b => found = 1 ∧ best = b

/-! ## The statements -/

/-- The side test of candidate `j` (into `180077`). -/
def sideS (d : ℕ) : Stmt :=
  if d = 0 then testS 0 (.v 180035) (.e 180053 180035) (.v 180053) 180077
  else testS 0 (.e 180053 180035) (.v 180035) (.v 180053) 180077

/-- The nearer test (into `180078`). -/
def nearS (d : ℕ) : Stmt :=
  if d = 0 then testS 0 (.e 180053 180035) (.e 180055 180035) (.v 180053) 180078
  else testS 0 (.e 180055 180035) (.e 180053 180035) (.v 180053) 180078

/-- A candidate: take it if none was found, else if it is nearer. -/
def candS (d : ℕ) : Stmt :=
  .ifLtN 180051 180011 (block [.copyN 180052 180050, .constN 180051 1])
    (.seq (.instr (.addN 180055 180000 180052))
      (.seq (nearS d) (.ifLtN 180078 180011 .skip (.instr (.copyN 180052 180050)))))

/-- One step of the scan. -/
def scanBody (d : ℕ) : Stmt :=
  .seq (block [.addN 180053 180000 180050, .addN 180054 180053 180011])
  (.seq (testS 1 (.v 180053) (.v 180035) (.v 180053) 180056)
  (.seq (testS 1 (.v 180035) (.v 180054) (.v 180053) 180057)
  (.seq (testS 1 (.v 180054) (.v 180035) (.v 180053) 180058)
  (.seq (testS 1 (.v 180035) (.v 180053) (.v 180053) 180059)
  (.seq (andS 180056 180056 180057) (.seq (andS 180058 180058 180059)
  (.seq (orS 180076 180056 180058 180079) (.seq (sideS d) (.seq (andS 180076 180076 180077)
  (.seq (.ifLtN 180076 180011 .skip (candS d)) (.instr (.addN 180050 180050 180011))))))))))))

/-- The scan. -/
def scanS (d : ℕ) : Stmt :=
  .seq (block [.constN 180050 0, .constN 180051 0, .constN 180052 0])
    (.whileLtN 180050 180001 (scanBody d))

/-- The write set of the scan: the kernel and `180050 … 180089`. -/
def Bsc (r : ℕ) : Bool := Bk r || decide (180050 ≤ r ∧ r < 180090)

/-- The registers the scan reads. -/
def SI (C : Chain) (qk : ℕ) (c : Config) : Prop :=
  c.nreg 180000 = C.s ∧ c.nreg 180001 = C.m ∧ c.nreg 180011 = 1 ∧ c.nreg 180035 = qk

theorem SI.keep {C : Chain} {qk : ℕ} {c c' : Config} (h : SI C qk c) (F : FrameB Bsc c c') :
    SI C qk c' := by
  obtain ⟨h0, h1, h11, h35⟩ := h
  exact ⟨by rw [F.1 _ (by decide), h0], by rw [F.1 _ (by decide), h1],
    by rw [F.1 _ (by decide), h11], by rw [F.1 _ (by decide), h35]⟩

theorem sc_of_bt {d : ℕ} (hd : 180050 ≤ d ∧ d < 180090) {c c' : Config} (F : FrameB (Bt d) c c') :
    FrameB Bsc c c' :=
  frameB_mono F fun r hr => by
    unfold Bsc at hr; unfold Bt
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢
    exact ⟨hr.1, by omega⟩

theorem sc_of_one {d : ℕ} (hd : 180050 ≤ d ∧ d < 180090) {c c' : Config}
    (F : FrameB (fun r => decide (r = d)) c c') : FrameB Bsc c c' :=
  frameB_mono F fun r hr => by
    unfold Bsc at hr
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢
    omega

theorem sc_of_two {d t : ℕ} (hd : 180050 ≤ d ∧ d < 180090) (ht : 180050 ≤ t ∧ t < 180090)
    {c c' : Config} (F : FrameB (fun r => decide (r = d ∨ r = t)) c c') : FrameB Bsc c c' :=
  frameB_mono F fun r hr => by
    unfold Bsc at hr
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢
    omega

/-! ## The tests of a scan step -/

theorem sig_zero : sig 0 = 1 := rfl

theorem sig_one {d : ℕ} (hd : d ≠ 0) : sig d = -1 := by unfold sig; rw [ite_eq_right hd]

theorem sideS_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {C : Chain}
    (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) {d j k : ℕ} (hj : j < C.m) (hk : k ≤ C.m)
    (c : Config) (hw : WordsBounded W c) (h35 : c.nreg 180035 = C.s + k)
    (h53 : c.nreg 180053 = C.s + j) :
    ∃ c' k', Exec P W (sideS d) c c' k' ∧ k' ≤ 245 ∧ FrameB (Bt 180077) c c' ∧
      c'.nreg 180077 ≤ 1 ∧
      (c'.nreg 180077 = 1 ↔ 0 < sig d * (edgeXk C j k - (C.vertex k).1)) := by
  have lk : C.s + k < P.n := by omega
  have lj : C.s + j < P.n := by omega
  by_cases hd : d = 0
  · subst hd
    obtain ⟨c', k', e, hk', F, b, hb⟩ := testS_exec (P := P) hG hW (op := 0) (by omega)
      (x := .v 180035) (y := .e 180053 180035) (z := .v 180053) (d := 180077) (Or.inr (by omega))
      ⟨Or.inr (by omega), Or.inr (by omega)⟩ (Or.inr (by omega)) c hw
      (by sio only [Src.pt, SymPt.Lt]) (by sio only [Src.pt, SymPt.Lt])
      (by sio only [Src.pt, SymPt.Lt])
    simp only [Src.pt, SymPt.eval, SignTest, h35, h53] at hb
    rw [edgeXQ hC hsn hj hk, vtxQ hC hsn (by omega) lk] at hb
    refine ⟨c', k', e, hk', F, b, ?_⟩
    rw [hb, sig_zero, one_mul, sub_pos]
  · obtain ⟨c', k', e, hk', F, b, hb⟩ := testS_exec (P := P) hG hW (op := 0) (by omega)
      (x := .e 180053 180035) (y := .v 180035) (z := .v 180053) (d := 180077)
      ⟨Or.inr (by omega), Or.inr (by omega)⟩ (Or.inr (by omega)) (Or.inr (by omega)) c hw
      (by sio only [Src.pt, SymPt.Lt]) (by sio only [Src.pt, SymPt.Lt])
      (by sio only [Src.pt, SymPt.Lt])
    simp only [Src.pt, SymPt.eval, SignTest, h35, h53] at hb
    rw [edgeXQ hC hsn hj hk, vtxQ hC hsn (by omega) lk] at hb
    refine ⟨c', k', by unfold sideS; rw [ite_eq_right hd]; exact e, hk', F, b, ?_⟩
    rw [hb, sig_one hd]
    constructor <;> intro h <;> linarith

theorem nearS_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {C : Chain}
    (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) {d j b k : ℕ} (hj : j < C.m) (hb : b < C.m)
    (hk : k ≤ C.m) (c : Config) (hw : WordsBounded W c) (h35 : c.nreg 180035 = C.s + k)
    (h53 : c.nreg 180053 = C.s + j) (h55 : c.nreg 180055 = C.s + b) :
    ∃ c' k', Exec P W (nearS d) c c' k' ∧ k' ≤ 245 ∧ FrameB (Bt 180078) c c' ∧
      c'.nreg 180078 ≤ 1 ∧
      (c'.nreg 180078 = 1 ↔ sig d * edgeXk C j k < sig d * edgeXk C b k) := by
  by_cases hd : d = 0
  · subst hd
    obtain ⟨c', k', e, hk', F, b', hb'⟩ := testS_exec (P := P) hG hW (op := 0) (by omega)
      (x := .e 180053 180035) (y := .e 180055 180035) (z := .v 180053) (d := 180078)
      ⟨Or.inr (by omega), Or.inr (by omega)⟩ ⟨Or.inr (by omega), Or.inr (by omega)⟩
      (Or.inr (by omega)) c hw
      (by sio only [Src.pt, SymPt.Lt]) (by sio only [Src.pt, SymPt.Lt])
      (by sio only [Src.pt, SymPt.Lt])
    simp only [Src.pt, SymPt.eval, SignTest, h35, h53, h55] at hb'
    rw [edgeXQ hC hsn hj hk, edgeXQ hC hsn hb hk] at hb'
    refine ⟨c', k', e, hk', F, b', ?_⟩
    rw [hb', sig_zero, one_mul, one_mul]
  · obtain ⟨c', k', e, hk', F, b', hb'⟩ := testS_exec (P := P) hG hW (op := 0) (by omega)
      (x := .e 180055 180035) (y := .e 180053 180035) (z := .v 180053) (d := 180078)
      ⟨Or.inr (by omega), Or.inr (by omega)⟩ ⟨Or.inr (by omega), Or.inr (by omega)⟩
      (Or.inr (by omega)) c hw
      (by sio only [Src.pt, SymPt.Lt]) (by sio only [Src.pt, SymPt.Lt])
      (by sio only [Src.pt, SymPt.Lt])
    simp only [Src.pt, SymPt.eval, SignTest, h35, h53, h55] at hb'
    rw [edgeXQ hC hsn hj hk, edgeXQ hC hsn hb hk] at hb'
    refine ⟨c', k', by unfold nearS; rw [ite_eq_right hd]; exact e, hk', F, b', ?_⟩
    rw [hb', sig_one hd]
    constructor <;> intro h <;> linarith

/-! ## A candidate -/

/-- The update of the scan state by a candidate `j`. -/
noncomputable def upd1 (C : Chain) (k : ℕ) (σ : ℝ) (j : ℕ) : Option ℕ → Option ℕ := by
  classical
  exact fun o => match o with
    | none => some j
    | some b => if σ * edgeXk C j k < σ * edgeXk C b k then some j else some b

theorem scan_succ_cand {C : Chain} {k : ℕ} {σ : ℝ} {j : ℕ} (h : Cand C k σ j) :
    scan C k σ (j + 1) = upd1 C k σ j (scan C k σ j) := by
  classical
  show (if Cand C k σ j then _ else _) = _
  rw [ite_eq_left h]
  unfold upd1
  rcases scan C k σ j with _ | b <;> rfl

theorem scan_succ_not {C : Chain} {k : ℕ} {σ : ℝ} {j : ℕ} (h : ¬ Cand C k σ j) :
    scan C k σ (j + 1) = scan C k σ j := by
  classical
  show (if Cand C k σ j then _ else _) = _
  rw [ite_eq_right h]

theorem candS_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {C : Chain}
    (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) {d j k : ℕ} (hj : j < C.m) (hk : k ≤ C.m)
    (c : Config) (hw : WordsBounded W c) (hS : SI C (C.s + k) c) (h50 : c.nreg 180050 = j)
    (h53 : c.nreg 180053 = C.s + j) (hE : Enc (c.nreg 180051) (c.nreg 180052) (scan C k (sig d) j))
    (hsc : ∀ b, scan C k (sig d) j = some b → b < C.m) :
    ∃ c' k', Exec P W (candS d) c c' k' ∧ k' ≤ 260 ∧ FrameB Bsc c c' ∧ c'.nreg 180050 = j ∧
      Enc (c'.nreg 180051) (c'.nreg 180052) (upd1 C k (sig d) j (scan C k (sig d) j)) := by
  obtain ⟨h0, h1, h11, h35⟩ := hS
  rcases hsj : scan C k (sig d) j with _ | b
  · rw [hsj] at hE
    simp only [Enc] at hE
    obtain ⟨c', k', e, hk', q52, q51, R⟩ : ∃ c' k', Exec P W
        (block [.copyN 180052 180050, .constN 180051 1]) c c' k' ∧ k' = 2 ∧
        c'.nreg 180052 = j ∧ c'.nreg 180051 = 1 ∧
        FrameB (fun r => decide (r = 180052 ∨ r = 180051)) c c' := by
      exec_block
      · omega
      · refine ⟨rfl, ?_, ?_, ⟨fun r hr => ?_, fun r _ => rfl, rfl, rfl, rfl⟩⟩
        · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
          exact h50
        · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
        · simp only [decide_eq_false_iff_not, not_or] at hr
          simp (disch := omega) only [Config.nreg_mk, Machine.upd_other]
    refine ⟨c', _, .ifLtN_true (by rwo [hE, h11]) e, by omega, sc_of_two (by omega)
      (by omega) R, by rw [R.1 _ (by decide), h50], ?_⟩
    simp only [upd1, Enc]
    exact ⟨q51, q52⟩
  · rw [hsj] at hE
    simp only [Enc] at hE
    obtain ⟨hf, hb⟩ := hE
    have hbm := hsc b hsj
    have e₁ := Exec.addN (P := P) hw 180055 180000 180052 (by rw [h0, hb]; have := hw.1 180055; omega)
    set c₁ : Config := { c with nreg := upd c.nreg 180055 (c.nreg 180000 + c.nreg 180052) }
      with hc₁
    have R₁ : ∀ r, r ≠ 180055 → c₁.nreg r = c.nreg r := fun r hr => by rw [hc₁]; simp [hr]
    have q55 : c₁.nreg 180055 = C.s + b := by rw [hc₁]; simp [h0, hb]
    obtain ⟨c₂, k₂, e₂, hk₂, F₂, bit₂, t₂⟩ := nearS_exec (P := P) (d := d) hG hW hC hsn hj hbm hk
      c₁ e₁.wb_right (by rw [R₁ _ (by decide), h35]) (by rw [R₁ _ (by decide), h53]) q55
    have k11 : c₂.nreg 180011 = 1 := by rw [F₂.1 _ (by decide), R₁ _ (by decide), h11]
    have k50 : c₂.nreg 180050 = j := by rw [F₂.1 _ (by decide), R₁ _ (by decide), h50]
    have k52 : c₂.nreg 180052 = b := by rw [F₂.1 _ (by decide), R₁ _ (by decide), hb]
    have k51 : c₂.nreg 180051 = 1 := by rw [F₂.1 _ (by decide), R₁ _ (by decide), hf]
    have w₂ := e₂.wb_right
    have F₁ : FrameB Bsc c c₁ := ⟨fun r hr => R₁ r (by
      unfold Bsc at hr; sio only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr),
      fun r _ => rfl, rfl, rfl, rfl⟩
    by_cases hn : sig d * edgeXk C j k < sig d * edgeXk C b k
    · have e₃ := Exec.copyN (P := P) w₂ 180052 180050
      refine ⟨_, _, .ifLtN_false (by rwo [hf, h11]) (.seq e₁ (.seq e₂
        (.ifLtN_false (by rwo [t₂.2 hn, k11]) e₃))), by omega,
        (F₁.trans (sc_of_bt (by omega) F₂)).trans ⟨fun r hr => ?_, fun r _ => rfl, rfl, rfl, rfl⟩,
        ?_, ?_⟩
      · have : r ≠ 180052 := by
          unfold Bsc at hr; sio only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
        simp [this]
      · simp [k50]
      · simp only [upd1, Enc, ite_eq_left hn]
        simp [k51, k50]
    · have h0' : c₂.nreg 180078 = 0 := by have := mt t₂.1 hn; omega
      refine ⟨_, _, .ifLtN_false (by rwo [hf, h11]) (.seq e₁ (.seq e₂
        (.ifLtN_true (by rwo [h0', k11]) (.skip w₂)))), by omega,
        F₁.trans (sc_of_bt (by omega) F₂), k50, ?_⟩
      simp only [upd1, Enc, ite_eq_right hn]
      exact ⟨k51, k52⟩

/-! ## One step of the scan -/

theorem scanBody_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 8 ≤ W) {C : Chain}
    (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) {d j k : ℕ} (hj : j < C.m) (hk : k ≤ C.m)
    (c : Config) (hw : WordsBounded W c) (hS : SI C (C.s + k) c) (h50 : c.nreg 180050 = j)
    (hE : Enc (c.nreg 180051) (c.nreg 180052) (scan C k (sig d) j))
    (hsc : ∀ b, scan C k (sig d) j = some b → b < C.m) :
    ∃ c' k', Exec P W (scanBody d) c c' k' ∧ k' ≤ 1600 ∧ FrameB Bsc c c' ∧
      c'.nreg 180050 = j + 1 ∧
      Enc (c'.nreg 180051) (c'.nreg 180052) (scan C k (sig d) (j + 1)) := by
  have hS0 := hS
  obtain ⟨h0, h1, h11, h35⟩ := hS
  have lj : C.s + j < P.n := by omega
  have lj1 : C.s + j + 1 < P.n := by omega
  have lk : C.s + k < P.n := by omega
  -- indices
  obtain ⟨c₁, k₁, e₁, hk₁, q53, q54, R₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.addN 180053 180000 180050, .addN 180054 180053 180011]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 180053 = C.s + j ∧ c₁.nreg 180054 = C.s + j + 1 ∧
      FrameB (fun r => decide (r = 180053 ∨ r = 180054)) c c₁ := by
    exec_block
    · config_simp; rwo [h0, h50]
    · config_simp; rwo [h0, h50, h11]
    · refine ⟨rfl, ?_, ?_, ⟨fun r hr => ?_, fun r _ => rfl, rfl, rfl, rfl⟩⟩
      · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
        rw [h0, h50]
      · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
        rw [h0, h50, h11]
      · simp only [decide_eq_false_iff_not, not_or] at hr
        simp (disch := omega) only [Config.nreg_mk, Machine.upd_other]
  have G₁ := sc_of_two (by omega) (by omega) R₁
  have S₁ := hS0.keep G₁
  -- the four height tests
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, b56, t56⟩ := testV_exec (P := P) hG (by omega) (op := 1) (by omega)
    (r₁ := 180053) (r₂ := 180035) (r₃ := 180053) (d := 180056) (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr (by omega)) c₁ e₁.wb_right q53 S₁.2.2.2 q53 lj lk lj
  have S₂ := S₁.keep (sc_of_bt (by omega) F₂)
  have q53₂ : c₂.nreg 180053 = C.s + j := by rw [F₂.1 _ (by decide), q53]
  have q54₂ : c₂.nreg 180054 = C.s + j + 1 := by rw [F₂.1 _ (by decide), q54]
  obtain ⟨c₃, k₃, e₃, hk₃, F₃, b57, t57⟩ := testV_exec (P := P) hG (by omega) (op := 1) (by omega)
    (r₁ := 180035) (r₂ := 180054) (r₃ := 180053) (d := 180057) (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr (by omega)) c₂ e₂.wb_right S₂.2.2.2 q54₂ q53₂ lk lj1 lj
  have S₃ := S₂.keep (sc_of_bt (by omega) F₃)
  have q53₃ : c₃.nreg 180053 = C.s + j := by rw [F₃.1 _ (by decide), q53₂]
  have q54₃ : c₃.nreg 180054 = C.s + j + 1 := by rw [F₃.1 _ (by decide), q54₂]
  obtain ⟨c₄, k₄, e₄, hk₄, F₄, b58, t58⟩ := testV_exec (P := P) hG (by omega) (op := 1) (by omega)
    (r₁ := 180054) (r₂ := 180035) (r₃ := 180053) (d := 180058) (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr (by omega)) c₃ e₃.wb_right q54₃ S₃.2.2.2 q53₃ lj1 lk lj
  have S₄ := S₃.keep (sc_of_bt (by omega) F₄)
  have q53₄ : c₄.nreg 180053 = C.s + j := by rw [F₄.1 _ (by decide), q53₃]
  obtain ⟨c₅, k₅, e₅, hk₅, F₅, b59, t59⟩ := testV_exec (P := P) hG (by omega) (op := 1) (by omega)
    (r₁ := 180035) (r₂ := 180053) (r₃ := 180053) (d := 180059) (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr (by omega)) c₄ e₄.wb_right S₄.2.2.2 q53₄ q53₄ lk lj lj
  have S₅ := S₄.keep (sc_of_bt (by omega) F₅)
  simp only [SignTest] at t56 t57 t58 t59
  rw [vtxQ hC hsn (by omega) lj, vtxQ hC hsn (by omega) lk] at t56 t59
  rw [vtxQ hC hsn (by omega) lk, show C.s + j + 1 = C.s + (j + 1) by ring,
    vtxQ hC hsn (by omega) (by omega)] at t57 t58
  -- the bits in `c₅`
  have r56 : c₅.nreg 180056 = c₂.nreg 180056 := by
    rw [F₅.1 _ (by decide), F₄.1 _ (by decide), F₃.1 _ (by decide)]
  have r57 : c₅.nreg 180057 = c₃.nreg 180057 := by rw [F₅.1 _ (by decide), F₄.1 _ (by decide)]
  have r58 : c₅.nreg 180058 = c₄.nreg 180058 := F₅.1 _ (by decide)
  rw [← r56] at b56 t56
  rw [← r57] at b57 t57
  rw [← r58] at b58 t58
  have W2 : 2 ≤ W := by omega
  obtain ⟨c₆, k₆, e₆, hk₆, v₆, F₆⟩ := andS_exec (P := P) W2 c₅ e₅.wb_right (d := 180056)
    (x := 180056) (y := 180057) (by decide) S₅.2.2.1 b56 b57
  have A₆ := and_bit b56 b57
  rw [← v₆, t56, t57] at A₆
  have S₆ := S₅.keep (sc_of_one (by omega) F₆)
  obtain ⟨c₇, k₇, e₇, hk₇, v₇, F₇⟩ := andS_exec (P := P) W2 c₆ e₆.wb_right (d := 180058)
    (x := 180058) (y := 180059) (by decide) S₆.2.2.1 (by rwx [fr1 F₆ (by decide)])
    (by rwx [fr1 F₆ (by decide)])
  have A₇ := and_bit (show c₆.nreg 180058 ≤ 1 by rwx [fr1 F₆ (by decide)])
    (show c₆.nreg 180059 ≤ 1 by rwx [fr1 F₆ (by decide)])
  rw [← v₇, fr1 F₆ (by decide), fr1 F₆ (by decide), t58, t59] at A₇
  have S₇ := S₆.keep (sc_of_one (by omega) F₇)
  have x56 : c₇.nreg 180056 = c₆.nreg 180056 := fr1 F₇ (by decide)
  obtain ⟨c₈, k₈, e₈, hk₈, v₈, F₈⟩ := orS_exec (P := P) W2 c₇ e₇.wb_right (d := 180076)
    (x := 180056) (y := 180058) (t := 180079) (by decide) (by decide) (by decide) S₇.2.2.1
    (by rw [x56]; exact A₆.1) A₇.1
  have A₈ := or_bit (show c₇.nreg 180056 ≤ 1 by rw [x56]; exact A₆.1) A₇.1
  rw [← v₈, x56, A₆.2, A₇.2] at A₈
  have S₈ := S₇.keep (sc_of_two (by omega) (by omega) F₈)
  have q53₈ : c₈.nreg 180053 = C.s + j := by
    rw [fr2 F₈ (by decide) (by decide), fr1 F₇ (by decide), fr1 F₆ (by decide),
      F₅.1 _ (by decide), q53₄]
  -- the side test
  obtain ⟨c₉, k₉, e₉, hk₉, F₉, b77, t77⟩ := sideS_exec (P := P) (d := d) hG (by omega) hC hsn hj
    hk c₈ e₈.wb_right S₈.2.2.2 q53₈
  have S₉ := S₈.keep (sc_of_bt (by omega) F₉)
  have x76 : c₉.nreg 180076 = c₈.nreg 180076 := F₉.1 _ (by decide)
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, v₁₀, F₁₀⟩ := andS_exec (P := P) W2 c₉ e₉.wb_right (d := 180076)
    (x := 180076) (y := 180077) (by decide) S₉.2.2.1 (by rw [x76]; exact A₈.1) b77
  have A₁₀ := and_bit (show c₉.nreg 180076 ≤ 1 by rw [x76]; exact A₈.1) b77
  rw [← v₁₀, x76, A₈.2, t77] at A₁₀
  have S₁₀ := S₉.keep (sc_of_one (by omega) F₁₀)
  have hcand : c₁₀.nreg 180076 = 1 ↔ Cand C k (sig d) j := by
    rw [A₁₀.2]; unfold Cand Strad
    exact ⟨fun h => ⟨hj, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩
  -- the scan registers are unchanged so far
  have G₁₀ : FrameB Bsc c₁ c₁₀ := (((((((((sc_of_bt (by omega) F₂).trans (sc_of_bt (by omega) F₃)).trans
    (sc_of_bt (by omega) F₄)).trans (sc_of_bt (by omega) F₅)).trans (sc_of_one (by omega) F₆)).trans
    (sc_of_one (by omega) F₇)).trans (sc_of_two (by omega) (by omega) F₈)).trans
    (sc_of_bt (by omega) F₉)).trans (sc_of_one (by omega) F₁₀))
  have keepS : ∀ r, r = 180050 ∨ r = 180051 ∨ r = 180052 ∨ r = 180053 → c₁₀.nreg r = c₁.nreg r := by
    rintro r (rfl | rfl | rfl | rfl) <;>
    rw [fr1 F₁₀ (by decide), F₉.1 _ (by decide), fr2 F₈ (by decide) (by decide),
      fr1 F₇ (by decide), fr1 F₆ (by decide), F₅.1 _ (by decide), F₄.1 _ (by decide),
      F₃.1 _ (by decide), F₂.1 _ (by decide)]
  have p50 : c₁₀.nreg 180050 = j := by rw [keepS _ (Or.inl rfl), R₁.1 _ (by decide), h50]
  have p51 : c₁₀.nreg 180051 = c.nreg 180051 := by
    rw [keepS _ (Or.inr (Or.inl rfl)), R₁.1 _ (by decide)]
  have p52 : c₁₀.nreg 180052 = c.nreg 180052 := by
    rw [keepS _ (Or.inr (Or.inr (Or.inl rfl))), R₁.1 _ (by decide)]
  have p53 : c₁₀.nreg 180053 = C.s + j := by
    rw [keepS _ (Or.inr (Or.inr (Or.inr rfl))), q53]
  have w₁₀ := e₁₀.wb_right
  -- the branch
  obtain ⟨c₁₁, k₁₁, e₁₁, hk₁₁, F₁₁, p50', hE'⟩ : ∃ c₁₁ k₁₁, Exec P W
      (.ifLtN 180076 180011 .skip (candS d)) c₁₀ c₁₁ k₁₁ ∧ k₁₁ ≤ 262 ∧ FrameB Bsc c₁₀ c₁₁ ∧
      c₁₁.nreg 180050 = j ∧
      Enc (c₁₁.nreg 180051) (c₁₁.nreg 180052) (scan C k (sig d) (j + 1)) := by
    by_cases hc : Cand C k (sig d) j
    · obtain ⟨c', k', e', hk', F', q50', hE''⟩ := candS_exec (P := P) (d := d) hG (by omega) hC
        hsn hj hk c₁₀ w₁₀ S₁₀ p50 p53 (by rwx [p51, p52]) hsc
      refine ⟨c', _, .ifLtN_false (by rwo [hcand.2 hc, S₁₀.2.2.1]) e', by omega, F', q50',
        ?_⟩
      rwx [scan_succ_cand hc]
    · have h0' : c₁₀.nreg 180076 = 0 := by have := mt hcand.1 hc; have := A₁₀.1; omega
      refine ⟨c₁₀, _, .ifLtN_true (by rwo [h0', S₁₀.2.2.1]) (.skip w₁₀), by omega,
        FrameB.refl _ _, p50, ?_⟩
      rwx [scan_succ_not hc, p51, p52]
  have S₁₁ := S₁₀.keep F₁₁
  have e₁₂ := Exec.addN (P := P) e₁₁.wb_right 180050 180050 180011 (by
    rw [p50', S₁₁.2.2.1]; have := S₁₁.2.1; omega)
  refine ⟨_, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ (.seq e₉
    (.seq e₁₀ (.seq e₁₁ e₁₂)))))))))), by omega, ?_, ?_, ?_⟩
  · refine ((G₁.trans G₁₀).trans F₁₁).trans ⟨fun r hr => ?_, fun r _ => rfl, rfl, rfl, rfl⟩
    have : r ≠ 180050 := by
      unfold Bsc at hr; sio only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
    simp [this]
  · simp only [Config.nreg_mk, Machine.upd_same]; rw [p50', S₁₁.2.2.1]
  · simp only [Config.nreg_mk]
    rw [upd_other _ _ _ (by decide), upd_other _ _ _ (by decide)]
    exact hE'

/-- **The scan**: registers `180051, 180052` encode `scan C k σ m` (at most `1602 m + 5`
steps). -/
theorem scanS_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 8 ≤ W) {C : Chain}
    (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) {d k : ℕ} (hk : k ≤ C.m)
    (c : Config) (hw : WordsBounded W c) (hS : SI C (C.s + k) c) :
    ∃ c' k', Exec P W (scanS d) c c' k' ∧ k' ≤ 1602 * C.m + 5 ∧ FrameB Bsc c c' ∧
      Enc (c'.nreg 180051) (c'.nreg 180052) (scan C k (sig d) C.m) := by
  obtain ⟨c₁, k₁, e₁, hk₁, q50, q51, q52, R₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.constN 180050 0, .constN 180051 0, .constN 180052 0]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 180050 = 0 ∧ c₁.nreg 180051 = 0 ∧ c₁.nreg 180052 = 0 ∧ FrameB Bsc c c₁ := by
    exec_block
    · omega
    · omega
    · omega
    · refine ⟨rfl, by config_simp, by config_simp, by config_simp,
        ⟨fun r hr => ?_, fun r _ => rfl, rfl, rfl, rfl⟩⟩
      unfold Bsc at hr; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
      simp (disch := omega) only [Config.nreg_mk, Machine.upd_other]
  let I : Config → Prop := fun e => WordsBounded W e ∧ FrameB Bsc c e ∧ SI C (C.s + k) e ∧
    e.nreg 180050 ≤ C.m ∧ Enc (e.nreg 180051) (e.nreg 180052) (scan C k (sig d) (e.nreg 180050))
  have hI : I c₁ := ⟨e₁.wb_right, R₁, hS.keep R₁, by omega, by rwr [q50, q51]⟩
  obtain ⟨c₂, k₂, e₂, ⟨w₂, F₂, S₂, l₂, E₂⟩, hex, hk₂⟩ :=
    Exec.whileLtN_bounded (P := P) (W := W) (a := 180050) (b := 180001) (body := scanBody d) I
      (fun e => C.m - e.nreg 180050) 1600 (fun e he => he.1)
      (by
        intro e ⟨we, Fe, Se, le, Ee⟩ hlt
        rw [Se.2.1] at hlt
        obtain ⟨e', k', ex, hk', F', q50', E'⟩ := scanBody_exec (P := P) (d := d) hG hW hC hsn
          hlt hk e we Se rfl Ee (fun b hb => by
            have := (scan_some hb).1; omega)
        refine ⟨e', k', ex, ⟨ex.wb_right, Fe.trans F', Se.keep F', by omega, by rw [q50']; exact E'⟩,
          hk', by omega⟩)
      hI
  rw [S₂.2.1] at hex
  have hm : c₂.nreg 180050 = C.m := by omega
  rw [hm] at E₂
  refine ⟨c₂, _, .seq e₁ e₂, ?_, F₂, E₂⟩
  rwo [q50] at hk₂

end

end Brute

end Chazelle.Core
