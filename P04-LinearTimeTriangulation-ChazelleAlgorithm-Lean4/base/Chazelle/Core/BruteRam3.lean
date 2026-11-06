module

public import Chazelle.Core.BruteRam2
public import Chazelle.Core.NFLocateHost

/-!
# WP-K on the RAM, part 3: the set-up phase

`setupS = initS ; topS ; bitS ; sS ; descS`: the constants, the top index, the orientation bit,
the tour start `S`, and the host `Host.whole n` at `A₀` with the model descriptor of the chain at
`A₀ + 4` (`DescMem`, `descMem_model`).  `setup_exec` states the result as the register context
`Ctx` and the memory facts.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace Brute

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-! ## The orientation bit and the tour start -/

theorem bitS_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (hW8 : 8 ≤ W)
    {C : Chain} (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) (c : Config)
    (hw : WordsBounded W c) (h0 : c.nreg 180000 = C.s) (h10 : c.nreg 180010 = P.n)
    (h11 : c.nreg 180011 = 1) (h13 : c.nreg 180013 = C.topIdx) (h28 : c.nreg 180028 = 0) :
    ∃ c' k, Exec P W bitS c c' k ∧ k ≤ 1602 ∧ FrameB Bbit c c' ∧ c'.nreg 180014 ≤ 1 ∧
      (c'.nreg 180014 = 1 ↔ C.sideBeta = true) := by
  by_cases hT : 0 < C.topIdx
  · obtain ⟨c', k, e, hk, F, b, hb⟩ := bitGen_exec hG hW hW8 hC hsn hT c hw h0 h10 h11 h13
    exact ⟨c', _, .ifLtN_true (by rw [h28, h13]; exact hT) e, by omega, F, b, hb⟩
  · have e := Exec.constN (P := P) hw 180014 0 (by omega)
    refine ⟨_, _, .ifLtN_false (by rw [h28, h13]; exact hT) e, by omega,
      ⟨fun r hr => ?_, fun r _ => rfl, rfl, rfl, rfl⟩, by simp, ?_⟩
    · unfold Bbit at hr
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
      simp (disch := omega) only [Config.nreg_mk, Machine.upd_other]
    · rw [sideBeta_of_top_zero (by omega)]; simp

/-- The tour start: `S = T` if the bit is set, else `2m - T`. -/
def sS : Stmt := .ifLtN 180014 180011 (.instr (.subN 180015 180012 180013))
  (.instr (.copyN 180015 180013))

theorem sS_exec {P : Polygon} {W : ℕ} {C : Chain} (c : Config) (hw : WordsBounded W c)
    (h11 : c.nreg 180011 = 1) (h12 : c.nreg 180012 = 2 * C.m) (h13 : c.nreg 180013 = C.topIdx)
    (hb : c.nreg 180014 ≤ 1) (hbit : c.nreg 180014 = 1 ↔ C.sideBeta = true) :
    ∃ c' k, Exec P W sS c c' k ∧ k ≤ 3 ∧ c'.nreg 180015 = tS C ∧
      FrameB (fun r => decide (r = 180015)) c c' := by
  have fr : ∀ v, FrameB (fun r => decide (r = 180015)) c
      { c with nreg := upd c.nreg 180015 v } := fun v =>
    ⟨fun r hr => by simp only [decide_eq_false_iff_not] at hr; simp [hr], fun r _ => rfl, rfl,
      rfl, rfl⟩
  by_cases h : c.nreg 180014 < 1
  · have hf : C.sideBeta = false := by
      cases hx : C.sideBeta with
      | false => rfl
      | true => have := hbit.2 hx; omega
    refine ⟨_, _, .ifLtN_true (by rw [h11]; exact h) (Exec.subN hw 180015 180012 180013),
      by omega, ?_, fr _⟩
    simp only [Config.nreg_mk, Machine.upd_same]
    rw [h12, h13]; unfold tS Chain.sideS; rw [hf]; rfl
  · have ht : C.sideBeta = true := hbit.1 (by omega)
    refine ⟨_, _, .ifLtN_false (by rw [h11]; exact h) (Exec.copyN hw 180015 180013),
      by omega, ?_, fr _⟩
    simp only [Config.nreg_mk, Machine.upd_same]
    rw [h13]; unfold tS Chain.sideS; rw [ht]; rfl

/-! ## Stores -/

/-- Store the value register `v` at the pointer `p`, then advance the pointer. -/
def putS (p v : ℕ) : Stmt := block [.storeN p v, .addN p p 180011]

theorem putS_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {p v : ℕ}
    (_hp : p ≠ 180011) (h11 : c.nreg 180011 = 1) (hroom : c.nreg p + 1 ≤ W) :
    ∃ c' k, Exec P W (putS p v) c c' k ∧ k = 2 ∧ c'.nreg p = c.nreg p + 1 ∧
      c'.nmem = upd c.nmem (c.nreg p) (c.nreg v) ∧ (∀ r, r ≠ p → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold putS
  exec_block
  · config_simp; rw [h11]; exact hroom
  · refine ⟨rfl, ?_, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
    · simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
      rw [h11]
    · simp (disch := omega) only [Config.nreg_mk, Machine.upd_other]

/-- The host and the descriptor. -/
def descS : Stmt :=
  .seq (block [.copyN 180045 180016, .subN 180046 180010 180011])
  (.seq (putS 180045 180011) (.seq (putS 180045 180028) (.seq (putS 180045 180028)
  (.seq (putS 180045 180046) (.seq (.instr (.copyN 180017 180045))
  (.seq (putS 180045 180028) (.seq (putS 180045 180016) (.seq (putS 180045 180000)
  (.seq (putS 180045 180001) (.seq (putS 180045 180013) (.seq (putS 180045 180014)
    (block [.copyN 180018 180045, .copyN 180024 180045, .constN 180019 0]))))))))))))

/-- The memory words of the host and the descriptor at `A₀`. -/
def DescMem (P : Polygon) (C : Chain) (m : ℕ → ℕ) (A₀ : ℕ) : Prop :=
  m A₀ = 1 ∧ m (A₀ + 1) = 0 ∧ m (A₀ + 2) = 0 ∧ m (A₀ + 3) = P.n - 1 ∧ m (A₀ + 4) = 0 ∧
    m (A₀ + 5) = A₀ ∧ m (A₀ + 6) = C.s ∧ m (A₀ + 7) = C.m ∧ m (A₀ + 8) = C.topIdx ∧
    (m (A₀ + 9) = 1 ↔ C.sideBeta = true)

theorem descMem_agree {P : Polygon} {C : Chain} {m m' : ℕ → ℕ} {A₀ : ℕ} (h : DescMem P C m A₀)
    (hm : ∀ a, a < A₀ + 10 → m' a = m a) : DescMem P C m' A₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rwa [hm _ (by omega)])
    | skip

/-- **The descriptor words describe the chain model**, and are well formed below `E`. -/
theorem descMem_model {P : Polygon} {C : Chain} (hC : C.P = Qof P) (hn1 : 1 ≤ P.n)
    (hsn : C.s < P.n) {m : ℕ → ℕ} {A₀ : ℕ} (h : DescMem P C m A₀) {E : ℕ} (hE : A₀ + 10 ≤ E) :
    ModelDescAt m (A₀ + 4) (Qof P) (chainModel C) ∧ ModelDescWF P E m (A₀ + 4) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hH : HostAt m A₀ (Host.whole (Qof P).n) := by
    refine ⟨by rw [h0]; rfl, fun i hi => ?_⟩
    have hi0 : i = 0 := by simpa [Host.whole] using hi
    subst hi0
    simp only [Host.whole, List.getD_cons_zero]
    refine ⟨by simpa using h1, by simpa using h2, ?_⟩
    rw [show A₀ + 3 + 3 * 0 = A₀ + 3 by ring, h3, hQn]
  have hCD : ChainDescAt m (A₀ + 4 + 1) (Qof P) (Host.whole (Qof P).n) C :=
    ⟨by rw [show A₀ + 4 + 1 = A₀ + 5 by ring, h5]; exact hH,
      by rw [hC, poly_whole _ (by rw [hQn]; exact hn1)],
      by rw [show A₀ + 4 + 1 + 1 = A₀ + 6 by ring, h6],
      by rw [show A₀ + 4 + 1 + 2 = A₀ + 7 by ring, h7],
      by rw [show A₀ + 4 + 1 + 3 = A₀ + 8 by ring, h8],
      by rw [show A₀ + 4 + 1 + 4 = A₀ + 9 by ring]; exact h9⟩
  refine ⟨Or.inl ⟨h4, _, _, hCD, rfl⟩, by omega, fun _ => ⟨by omega, fun H C' hC' => ?_⟩⟩
  have hHH : H = Host.whole (Qof P).n := by
    have e5 : m (A₀ + 4 + 1) = A₀ := by rw [show A₀ + 4 + 1 = A₀ + 5 by ring, h5]
    have := hC'.1
    rw [e5] at this
    exact NFLoc.hostAt_unique this hH
  subst hHH
  refine ⟨by simp [Host.whole], ?_, ?_, ?_⟩
  · intro it hit
    simp only [Host.whole, List.mem_cons, List.not_mem_nil, or_false] at hit
    subst hit
    exact ⟨by omega, by omega⟩
  · rw [show A₀ + 4 + 1 = A₀ + 5 by ring, h5]; simp [Host.whole]; omega
  · have e1 : C'.s = C.s := by
      have := hC'.2.2.1; rw [show A₀ + 4 + 1 + 1 = A₀ + 6 by ring, h6] at this; exact this.symm
    have e2 : C'.P = Qof P := by rw [hC'.2.1, poly_whole _ (by rw [hQn]; exact hn1)]
    rw [e1, e2, hQn]; exact hsn

/-- The memory after the ten stores of `descS`. -/
def descMemory (m : ℕ → ℕ) (A₀ n s mm T b : ℕ) : ℕ → ℕ :=
  upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m A₀ 1)
      (A₀ + 1) 0) (A₀ + 2) 0) (A₀ + 3) (n - 1)) (A₀ + 4) 0) (A₀ + 5) A₀) (A₀ + 6) s)
      (A₀ + 7) mm) (A₀ + 8) T) (A₀ + 9) b

theorem descMemory_desc {P : Polygon} {C : Chain} (m : ℕ → ℕ) (A₀ b : ℕ)
    (hbit : b = 1 ↔ C.sideBeta = true) :
    DescMem P C (descMemory m A₀ P.n C.s C.m C.topIdx b) A₀ := by
  unfold descMemory
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := omega) only [Machine.upd_same, Machine.upd_other]
  exact hbit

theorem descMemory_below (m : ℕ → ℕ) (A₀ n s mm T b : ℕ) {a : ℕ} (ha : a < A₀) :
    descMemory m A₀ n s mm T b a = m a := by
  unfold descMemory
  simp (disch := omega) only [Machine.upd_other]

set_option maxHeartbeats 2000000 in
/-- **The host and the descriptor** at `A₀`. -/
theorem descS_exec {P : Polygon} {W : ℕ} {C : Chain} (c : Config) (hw : WordsBounded W c)
    {A₀ : ℕ} (h0 : c.nreg 180000 = C.s) (h1 : c.nreg 180001 = C.m) (h10 : c.nreg 180010 = P.n)
    (h11 : c.nreg 180011 = 1) (h13 : c.nreg 180013 = C.topIdx) (h16 : c.nreg 180016 = A₀)
    (h28 : c.nreg 180028 = 0) (hbit : c.nreg 180014 = 1 ↔ C.sideBeta = true)
    (hroom : A₀ + 10 ≤ W) :
    ∃ c' k, Exec P W descS c c' k ∧ k = 26 ∧ DescMem P C c'.nmem A₀ ∧
      (∀ a, a < A₀ → c'.nmem a = c.nmem a) ∧ c'.nreg 180017 = A₀ + 4 ∧
      c'.nreg 180018 = A₀ + 10 ∧ c'.nreg 180024 = A₀ + 10 ∧ c'.nreg 180019 = 0 ∧
      (∀ r, r ≠ 180017 → r ≠ 180018 → r ≠ 180024 → r ≠ 180019 → r ≠ 180045 → r ≠ 180046 →
        c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨d0, k0, e0, hk0, p0, q0, R0, rr0, m0, rm0, o0⟩ : ∃ d k, Exec P W
      (block [.copyN 180045 180016, .subN 180046 180010 180011]) c d k ∧ k = 2 ∧
      d.nreg 180045 = A₀ ∧ d.nreg 180046 = P.n - 1 ∧
      (∀ r, r ≠ 180045 → r ≠ 180046 → d.nreg r = c.nreg r) ∧ d.rreg = c.rreg ∧
      d.nmem = c.nmem ∧ d.rmem = c.rmem ∧ d.output = c.output := by
    exec_block
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩ <;>
      simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
    · exact h16
    · rw [h10, h11]
  have K0 : ∀ r, r ≠ 180045 → r ≠ 180046 → r ≠ 180017 → d0.nreg r = c.nreg r :=
    fun r h1 h2 _ => R0 r h1 h2
  have Q0 : d0.nreg 180046 = P.n - 1 := q0
  have u1 : d0.nreg 180011 = 1 := by rw [K0 _ (by decide) (by decide) (by decide), h11]
  have w1 : d0.nreg 180011 = c.nreg 180011 := K0 _ (by decide) (by decide) (by decide)
  obtain ⟨d1, k1, e1, hk1, p1, m1, R1, rr1, rm1, o1⟩ := putS_exec (P := P) d0 e0.wb_right
    (p := 180045) (v := 180011) (by decide) u1 (by rw [p0]; omega)
  rw [p0, w1] at m1
  rw [p0] at p1
  have K1 : ∀ r, r ≠ 180045 → r ≠ 180046 → r ≠ 180017 → d1.nreg r = c.nreg r :=
    fun r h1 h2 h3 => (R1 r h1).trans (K0 r h1 h2 h3)
  have Q1 : d1.nreg 180046 = P.n - 1 := (R1 _ (by decide)).trans Q0
  have u2 : d1.nreg 180011 = 1 := by rw [K1 _ (by decide) (by decide) (by decide), h11]
  have w2 : d1.nreg 180028 = c.nreg 180028 := K1 _ (by decide) (by decide) (by decide)
  obtain ⟨d2, k2, e2, hk2, p2, m2, R2, rr2, rm2, o2⟩ := putS_exec (P := P) d1 e1.wb_right
    (p := 180045) (v := 180028) (by decide) u2 (by rw [p1]; omega)
  rw [p1, w2] at m2
  rw [p1] at p2
  have K2 : ∀ r, r ≠ 180045 → r ≠ 180046 → r ≠ 180017 → d2.nreg r = c.nreg r :=
    fun r h1 h2 h3 => (R2 r h1).trans (K1 r h1 h2 h3)
  have Q2 : d2.nreg 180046 = P.n - 1 := (R2 _ (by decide)).trans Q1
  have u3 : d2.nreg 180011 = 1 := by rw [K2 _ (by decide) (by decide) (by decide), h11]
  have w3 : d2.nreg 180028 = c.nreg 180028 := K2 _ (by decide) (by decide) (by decide)
  obtain ⟨d3, k3, e3, hk3, p3, m3, R3, rr3, rm3, o3⟩ := putS_exec (P := P) d2 e2.wb_right
    (p := 180045) (v := 180028) (by decide) u3 (by rw [p2]; omega)
  rw [p2, w3] at m3
  rw [p2] at p3
  have K3 : ∀ r, r ≠ 180045 → r ≠ 180046 → r ≠ 180017 → d3.nreg r = c.nreg r :=
    fun r h1 h2 h3 => (R3 r h1).trans (K2 r h1 h2 h3)
  have Q3 : d3.nreg 180046 = P.n - 1 := (R3 _ (by decide)).trans Q2
  have u4 : d3.nreg 180011 = 1 := by rw [K3 _ (by decide) (by decide) (by decide), h11]
  have w4 : d3.nreg 180046 = P.n - 1 := Q3
  obtain ⟨d4, k4, e4, hk4, p4, m4, R4, rr4, rm4, o4⟩ := putS_exec (P := P) d3 e3.wb_right
    (p := 180045) (v := 180046) (by decide) u4 (by rw [p3]; omega)
  rw [p3, w4] at m4
  rw [p3] at p4
  have K4 : ∀ r, r ≠ 180045 → r ≠ 180046 → r ≠ 180017 → d4.nreg r = c.nreg r :=
    fun r h1 h2 h3 => (R4 r h1).trans (K3 r h1 h2 h3)
  have Q4 : d4.nreg 180046 = P.n - 1 := (R4 _ (by decide)).trans Q3
  have eD := Exec.copyN (P := P) e4.wb_right 180017 180045
  set dD : Config := { d4 with nreg := upd d4.nreg 180017 (d4.nreg 180045) } with hdD
  have pD : dD.nreg 180045 = A₀ + 4 := by
    rw [hdD]; simp only [Config.nreg_mk]; rw [upd_other _ _ _ (by decide)]; rw [p4]
  have qD : dD.nreg 180017 = A₀ + 4 := by
    rw [hdD]; simp only [Config.nreg_mk, upd_same]; rw [p4]
  have KD : ∀ r, r ≠ 180045 → r ≠ 180046 → r ≠ 180017 → dD.nreg r = c.nreg r := fun r h1 h2 h3 => by
    rw [hdD]; simp only [Config.nreg_mk]; rw [upd_other _ _ _ h3]; exact K4 r h1 h2 h3
  have QD : dD.nreg 180046 = P.n - 1 := by
    rw [hdD]; simp only [Config.nreg_mk]; rw [upd_other _ _ _ (by decide)]; exact Q4
  have mD : dD.nmem = d4.nmem := rfl
  have u5 : dD.nreg 180011 = 1 := by rw [KD _ (by decide) (by decide) (by decide), h11]
  have w5 : dD.nreg 180028 = c.nreg 180028 := KD _ (by decide) (by decide) (by decide)
  obtain ⟨d5, k5, e5, hk5, p5, m5, R5, rr5, rm5, o5⟩ := putS_exec (P := P) dD eD.wb_right
    (p := 180045) (v := 180028) (by decide) u5 (by rw [pD]; omega)
  rw [pD, w5] at m5
  rw [pD] at p5
  have K5 : ∀ r, r ≠ 180045 → r ≠ 180046 → r ≠ 180017 → d5.nreg r = c.nreg r :=
    fun r h1 h2 h3 => (R5 r h1).trans (KD r h1 h2 h3)
  have Q5 : d5.nreg 180046 = P.n - 1 := (R5 _ (by decide)).trans QD
  have u6 : d5.nreg 180011 = 1 := by rw [K5 _ (by decide) (by decide) (by decide), h11]
  have w6 : d5.nreg 180016 = c.nreg 180016 := K5 _ (by decide) (by decide) (by decide)
  obtain ⟨d6, k6, e6, hk6, p6, m6, R6, rr6, rm6, o6⟩ := putS_exec (P := P) d5 e5.wb_right
    (p := 180045) (v := 180016) (by decide) u6 (by rw [p5]; omega)
  rw [p5, w6] at m6
  rw [p5] at p6
  have K6 : ∀ r, r ≠ 180045 → r ≠ 180046 → r ≠ 180017 → d6.nreg r = c.nreg r :=
    fun r h1 h2 h3 => (R6 r h1).trans (K5 r h1 h2 h3)
  have Q6 : d6.nreg 180046 = P.n - 1 := (R6 _ (by decide)).trans Q5
  have u7 : d6.nreg 180011 = 1 := by rw [K6 _ (by decide) (by decide) (by decide), h11]
  have w7 : d6.nreg 180000 = c.nreg 180000 := K6 _ (by decide) (by decide) (by decide)
  obtain ⟨d7, k7, e7, hk7, p7, m7, R7, rr7, rm7, o7⟩ := putS_exec (P := P) d6 e6.wb_right
    (p := 180045) (v := 180000) (by decide) u7 (by rw [p6]; omega)
  rw [p6, w7] at m7
  rw [p6] at p7
  have K7 : ∀ r, r ≠ 180045 → r ≠ 180046 → r ≠ 180017 → d7.nreg r = c.nreg r :=
    fun r h1 h2 h3 => (R7 r h1).trans (K6 r h1 h2 h3)
  have Q7 : d7.nreg 180046 = P.n - 1 := (R7 _ (by decide)).trans Q6
  have u8 : d7.nreg 180011 = 1 := by rw [K7 _ (by decide) (by decide) (by decide), h11]
  have w8 : d7.nreg 180001 = c.nreg 180001 := K7 _ (by decide) (by decide) (by decide)
  obtain ⟨d8, k8, e8, hk8, p8, m8, R8, rr8, rm8, o8⟩ := putS_exec (P := P) d7 e7.wb_right
    (p := 180045) (v := 180001) (by decide) u8 (by rw [p7]; omega)
  rw [p7, w8] at m8
  rw [p7] at p8
  have K8 : ∀ r, r ≠ 180045 → r ≠ 180046 → r ≠ 180017 → d8.nreg r = c.nreg r :=
    fun r h1 h2 h3 => (R8 r h1).trans (K7 r h1 h2 h3)
  have Q8 : d8.nreg 180046 = P.n - 1 := (R8 _ (by decide)).trans Q7
  have u9 : d8.nreg 180011 = 1 := by rw [K8 _ (by decide) (by decide) (by decide), h11]
  have w9 : d8.nreg 180013 = c.nreg 180013 := K8 _ (by decide) (by decide) (by decide)
  obtain ⟨d9, k9, e9, hk9, p9, m9, R9, rr9, rm9, o9⟩ := putS_exec (P := P) d8 e8.wb_right
    (p := 180045) (v := 180013) (by decide) u9 (by rw [p8]; omega)
  rw [p8, w9] at m9
  rw [p8] at p9
  have K9 : ∀ r, r ≠ 180045 → r ≠ 180046 → r ≠ 180017 → d9.nreg r = c.nreg r :=
    fun r h1 h2 h3 => (R9 r h1).trans (K8 r h1 h2 h3)
  have Q9 : d9.nreg 180046 = P.n - 1 := (R9 _ (by decide)).trans Q8
  have u10 : d9.nreg 180011 = 1 := by rw [K9 _ (by decide) (by decide) (by decide), h11]
  have w10 : d9.nreg 180014 = c.nreg 180014 := K9 _ (by decide) (by decide) (by decide)
  obtain ⟨d10, k10, e10, hk10, p10, m10, R10, rr10, rm10, o10⟩ := putS_exec (P := P) d9 e9.wb_right
    (p := 180045) (v := 180014) (by decide) u10 (by rw [p9]; omega)
  rw [p9, w10] at m10
  rw [p9] at p10
  have K10 : ∀ r, r ≠ 180045 → r ≠ 180046 → r ≠ 180017 → d10.nreg r = c.nreg r :=
    fun r h1 h2 h3 => (R10 r h1).trans (K9 r h1 h2 h3)
  have Q10 : d10.nreg 180046 = P.n - 1 := (R10 _ (by decide)).trans Q9
  have q17 : d10.nreg 180017 = A₀ + 4 := by
    rw [R10 _ (by decide), R9 _ (by decide), R8 _ (by decide), R7 _ (by decide),
      R6 _ (by decide), R5 _ (by decide), qD]
  obtain ⟨d11, k11, e11, hk11, s18, s24, s19, R11, rr11, m11, rm11, o11⟩ : ∃ d k, Exec P W
      (block [.copyN 180018 180045, .copyN 180024 180045, .constN 180019 0]) d10 d k ∧ k = 3 ∧
      d.nreg 180018 = A₀ + 10 ∧ d.nreg 180024 = A₀ + 10 ∧ d.nreg 180019 = 0 ∧
      (∀ r, r ≠ 180018 → r ≠ 180024 → r ≠ 180019 → d.nreg r = d10.nreg r) ∧ d.rreg = d10.rreg ∧
      d.nmem = d10.nmem ∧ d.rmem = d10.rmem ∧ d.output = d10.output := by
    have w := e10.wb_right
    exec_block
    · omega
    · refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩ <;>
        simp (disch := omega) only [Config.nreg_mk, Machine.upd_same, Machine.upd_other]
      · rw [p10]
      · rw [p10]
  have ex : Exec P W descS c d11 (k0 + (k1 + (k2 + (k3 + (k4 + (1 + (k5 + (k6 + (k7 + (k8 +
      (k9 + (k10 + k11)))))))))))) :=
    .seq e0 (.seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq eD (.seq e5 (.seq e6 (.seq e7 (.seq e8
      (.seq e9 (.seq e10 e11)))))))))))
  have hmem : d11.nmem = descMemory c.nmem A₀ P.n C.s C.m C.topIdx (c.nreg 180014) := by
    rw [m11, m10, m9, m8, m7, m6, m5, mD, m4, m3, m2, m1, m0, h11, h28, h16, h0, h1, h13]; rfl
  refine ⟨d11, _, ex, by subst_vars; rfl, ?_, fun a ha => ?_, by rw [R11 _ (by decide) (by decide)
    (by decide), q17], s18, s24, s19, fun r h1 h2 h3 h4 h5 h6 => ?_, ?_, ?_, ?_⟩
  · rw [hmem]; exact descMemory_desc _ _ _ hbit
  · rw [hmem]; exact descMemory_below _ _ _ _ _ _ _ ha
  · rw [R11 r h2 h3 h4]; exact K10 r h5 h6 h1
  · rw [rr11, rr10, rr9, rr8, rr7, rr6, rr5, rr4, rr3, rr2, rr1, rr0]
  · rw [rm11, rm10, rm9, rm8, rm7, rm6, rm5, rm4, rm3, rm2, rm1, rm0]
  · rw [o11, o10, o9, o8, o7, o6, o5, o4, o3, o2, o1, o0]

/-! ## The set-up phase -/

/-- The register context after the set-up (see the table in `BruteRam1`). -/
def Ctx (P : Polygon) (C : Chain) (γ A₀ : ℕ) (c : Config) : Prop :=
  c.nreg 180000 = C.s ∧ c.nreg 180001 = C.m ∧ c.nreg 180002 = γ ∧ c.nreg 180010 = P.n ∧
    c.nreg 180011 = 1 ∧ c.nreg 180012 = 2 * C.m ∧ c.nreg 180013 = C.topIdx ∧
    c.nreg 180015 = tS C ∧ c.nreg 180016 = A₀ ∧ c.nreg 180017 = A₀ + 4 ∧
    c.nreg 180018 = A₀ + 10 ∧ c.nreg 180023 = C.m + 1 ∧ c.nreg 180025 = 2 * C.m + 1 ∧
    c.nreg 180026 = 3 ∧ c.nreg 180027 = 6 ∧ c.nreg 180028 = 0

/-- The registers of the context. -/
def CtxReg (r : ℕ) : Prop :=
  (180000 ≤ r ∧ r < 180003) ∨ (180010 ≤ r ∧ r < 180014) ∨ (180015 ≤ r ∧ r < 180019) ∨
    r = 180023 ∨ (180025 ≤ r ∧ r < 180029)

/-- The context survives when its registers do. -/
theorem Ctx.keep {P : Polygon} {C : Chain} {γ A₀ : ℕ} {c c' : Config} (h : Ctx P C γ A₀ c)
    (hk : ∀ r, CtxReg r → c'.nreg r = c.nreg r) : Ctx P C γ A₀ c' := by
  obtain ⟨h0, h1, h2, h10, h11, h12, h13, h15, h16, h17, h18, h23, h25, h26, h27, h28⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [hk _ (by unfold CtxReg; omega)]; assumption)

/-- The set-up phase. -/
def setupS : Stmt := .seq initS (.seq topS (.seq bitS (.seq sS descS)))

set_option maxHeartbeats 1000000 in
/-- **The set-up phase**. -/
theorem setup_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 8 ≤ W) {C : Chain}
    (hW2 : P.n + 2 * C.m + 7 ≤ W)
    (hC : C.P = Qof P) (hsn : C.s + C.m + 1 ≤ P.n) (c : Config) (hw : WordsBounded W c)
    (h0 : c.nreg 180000 = C.s) (h1 : c.nreg 180001 = C.m) (hroom : c.nreg ALLOC + 2 * C.m + 10 ≤ W) :
    ∃ c' k, Exec P W setupS c c' k ∧ k ≤ 260 * C.m + 1900 ∧ 10 ≤ k ∧
      Ctx P C (c.nreg 180002) (c.nreg ALLOC) c' ∧ DescMem P C c'.nmem (c.nreg ALLOC) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧ c'.nreg 180019 = 0 ∧
      c'.nreg 180024 = c.nreg ALLOC + 10 ∧ (∀ r, Bm r = false → c'.nreg r = c.nreg r) ∧
      (∀ r, Bm r = false → c'.rreg r = c.rreg r) ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hn : C.P.n = P.n := by rw [hC]; exact shear_n _ _
  have hDH : DistinctHeights C.P := by rw [hC]; exact (goodShear_epsOf hG.2).2.1
  set A₀ := c.nreg ALLOC with hA₀
  -- constants
  obtain ⟨c₁, k₁, e₁, hk₁, i10, i11, i12, i16, i26, i27, i28, i23, i25, F₁⟩ :=
    initS_exec (P := P) c hw (by rw [h1]; exact hW2)
  have g : ∀ r, (r < 180010 ∨ 180030 ≤ r) → c₁.nreg r = c.nreg r := fun r hr =>
    F₁.1 r (by simp only [decide_eq_false_iff_not]; omega)
  have j0 : c₁.nreg 180000 = C.s := by rw [g _ (by omega), h0]
  have j1 : c₁.nreg 180001 = C.m := by rw [g _ (by omega), h1]
  rw [h1] at i12 i23 i25
  replace i16 : c₁.nreg 180016 = A₀ := i16
  -- top index
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, t13, tmax⟩ := topS_exec (P := P) hG (by omega) c₁ e₁.wb_right
    j0 i11 i23 (by omega)
  have hT : c₂.nreg 180013 = C.topIdx := by
    refine (topIdx_eq_of_max hDH t13 fun i hi => ?_).symm
    have e1 := vertex_eq (C := C) (k := i) (by rw [hn]; omega)
    have e2 := vertex_eq (C := C) (k := c₂.nreg 180013) (by rw [hn]; omega)
    rw [e1, e2, hC]; exact tmax i hi
  have kk2 : ∀ r, Btop r = false → c₂.nreg r = c₁.nreg r := F₂.1
  -- the bit
  obtain ⟨c₃, k₃, e₃, hk₃, F₃, b14, t14⟩ := bitS_exec (P := P) hG (by omega) (by omega) hC hsn c₂
    e₂.wb_right (by rw [kk2 _ (by decide), j0]) (by rw [kk2 _ (by decide), i10])
    (by rw [kk2 _ (by decide), i11]) hT (by rw [kk2 _ (by decide), i28])
  have kk3 : ∀ r, Bbit r = false → c₃.nreg r = c₂.nreg r := F₃.1
  -- the tour start
  obtain ⟨c₄, k₄, e₄, hk₄, s15, F₄⟩ := sS_exec (P := P) (C := C) c₃ e₃.wb_right
    (by rw [kk3 _ (by decide), kk2 _ (by decide), i11])
    (by rw [kk3 _ (by decide), kk2 _ (by decide), i12])
    (by rw [kk3 _ (by decide), hT]) b14 t14
  have kk4 : ∀ r, r ≠ 180015 → c₄.nreg r = c₃.nreg r := fun r hr =>
    F₄.1 r (by simpa using hr)
  -- a register untouched since `c₁`
  have up : ∀ r, Btop r = false → Bbit r = false → r ≠ 180015 → c₄.nreg r = c₁.nreg r :=
    fun r h2 h3 h4 => by rw [kk4 r h4, kk3 r h3, kk2 r h2]
  -- the descriptor
  obtain ⟨c₅, k₅, e₅, hk₅, hD, hlow, q17, q18, q24, q19, R₅, rr₅, rm₅, o₅⟩ :=
    descS_exec (P := P) (C := C) (A₀ := A₀) c₄ e₄.wb_right
    (by rw [up _ (by decide) (by decide) (by decide), j0])
    (by rw [up _ (by decide) (by decide) (by decide), j1])
    (by rw [up _ (by decide) (by decide) (by decide), i10])
    (by rw [up _ (by decide) (by decide) (by decide), i11])
    (by rw [kk4 _ (by decide), kk3 _ (by decide), hT])
    (by rw [up _ (by decide) (by decide) (by decide), i16])
    (by rw [up _ (by decide) (by decide) (by decide), i28])
    (by rw [kk4 _ (by decide)]; exact t14) (by omega)
  have ex : Exec P W setupS c c₅ (k₁ + (k₂ + (k₃ + (k₄ + k₅)))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  -- the memory is unchanged before `descS`
  have m4 : c₄.nmem = c.nmem := by rw [F₄.2.2.1, F₃.2.2.1, F₂.2.2.1, F₁.2.2.1]
  have all5 : ∀ r, Bm r = false → c₅.nreg r = c.nreg r := by
    intro r hr
    have hr' : r < 10000 ∨ (10500 ≤ r ∧ r < 180000) ∨ 190000 ≤ r := by
      unfold Bm Bk at hr
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr; omega
    rw [R₅ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), kk4 r (by omega),
      kk3 r (by unfold Bbit Bk; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega),
      kk2 r (by unfold Btop Bk; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega),
      g r (by omega)]
  refine ⟨c₅, _, ex, by omega, by omega, ?_, hD, fun a ha => by rw [hlow a ha, m4], q19,
    q24, all5, fun r hr => ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, q17, q18, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (rw [R₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          up _ (by decide) (by decide) (by decide)]; first | assumption | rfl |
          (rw [g _ (by omega)]))
      | (rw [R₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          kk4 _ (by decide), kk3 _ (by decide)]; exact hT)
      | (rw [R₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)];
          exact s15)
  · have hr' : r < 10000 ∨ (10500 ≤ r ∧ r < 180000) ∨ 190000 ≤ r := by
      unfold Bm Bk at hr
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr; omega
    have x4 : (fun q => decide (q = 180015)) r = false := by
      simp only [decide_eq_false_iff_not]; omega
    have x3 : Bbit r = false := by
      unfold Bbit Bk; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    have x2 : Btop r = false := by
      unfold Btop Bk; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    have x1 : (fun q => decide (180010 ≤ q ∧ q < 180030)) r = false := by
      simp only [decide_eq_false_iff_not]; omega
    rw [rr₅, F₄.2.1 r x4, F₃.2.1 r x3, F₂.2.1 r x2, F₁.2.1 r x1]
  · rw [rm₅, F₄.2.2.2.1, F₃.2.2.2.1, F₂.2.2.2.1, F₁.2.2.2.1]
  · rw [o₅, F₄.2.2.2.2, F₃.2.2.2.2, F₂.2.2.2.2, F₁.2.2.2.2]

end

end Brute

end Chazelle.Core
