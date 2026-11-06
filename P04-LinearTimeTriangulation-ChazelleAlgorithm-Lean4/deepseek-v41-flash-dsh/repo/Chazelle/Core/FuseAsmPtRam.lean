module

public import Chazelle.Golf

public import Chazelle.Core.FuseAsmGeo2
public import Chazelle.Core.FuseAsmCollQ
public import Chazelle.Core.SweepPrimJun

/-!
# WP-F fusion assembly, part 17: the point queries on the RAM

* `primRun`: a primitive of `SweepPrim` run from its contract, with the frame of its written
  registers (`FrameB Bprim`: the memory, the allocator and the registers outside `Bprim` are
  kept).
* `tposS`: `50201 := 6 + tpos C k` for the chain `C` of the descriptor at `50200` and `k` in
  `50110`.
* `ptQ`: `arrivalPos` at the position `(50201, 50202)` with direction code `50203`, and, if an
  arrival position `(e', h')` is found, the query `(e', 70124 + 1, 50203)` appended at the
  allocator (the query count in `70128`).
-/

namespace Chazelle.Core

namespace FuseAsm

open Machine Machine.Stmt Programs SignK SweepPrim WalkEmbed

@[expose] public section

/-- **A primitive run from its contract.** -/
theorem primRun {s : Stmt} {Inp : Polygon → ℕ → Chain → Config → Prop}
    {Out : Polygon → Chain → Config → Config → Prop} {K : ℕ}
    (hM : Meets s primBands (PrimPre Inp) (PrimPost Out) (fun _ _ => K)) (hwr : wr Bprim s = true)
    {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hHW : hostWords P.n ≤ W) (hwf : ChainWF P (c.nreg ALLOC) c.nmem (c.nreg 50200)) {H : Host}
    {C : Chain} (hC : ChainDescAt c.nmem (c.nreg 50200) (Qof P) H C) (hin : Inp P W C c)
    (hroom : c.nreg ALLOC + K ≤ W) :
    ∃ c' k, Exec P W s c c' k ∧ k ≤ K ∧ Out P C c c' ∧ FrameB Bprim c c' := by
  obtain ⟨c', k, e, hk, hout, -⟩ := hM P W c hw ⟨hG, hHW, hwf, H, C, hC, hin⟩ hroom
  exact ⟨c', k, e, hk, hout H C hC, exec_frameB e hwr⟩

theorem frameB_alloc {c c' : Config} (h : FrameB Bprim c c') : c'.nreg ALLOC = c.nreg ALLOC :=
  h.1 ALLOC (by unfold ALLOC; decide)

theorem frameB_reg {c c' : Config} (h : FrameB Bprim c c') {r : ℕ}
    (hr : r < 10000 ∨ (10600 ≤ r ∧ r < 50000) ∨ (50200 ≤ r ∧ r < 50210) ∨ 51000 ≤ r) :
    c'.nreg r = c.nreg r :=
  h.1 r (by simp only [Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)

/-! ## The tour offset of a chain vertex -/

/-- `50201 := 6 + tpos C k` (`k` in `50110`, the descriptor address in `50200`). -/
def tposS : Stmt :=
  .seq (block [.copyN 50100 50200]) (.seq readS (.seq (block [.subN 50103 50108 50102])
    (.seq (candR 50110 50102 50103 50111) (block [.constN 50112 6, .addN 50201 50111 50112]))))

/-- The registers written by `tposS`. -/
def Btp (r : ℕ) : Bool := decide (50100 ≤ r ∧ r ≤ 50112) || r == 50201

theorem wr_tposS : wr Btp tposS = true := ⌖

theorem tposS_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {Q : Polygon}
    {H : Host} {C : Chain} (hC : ChainDescAt c.nmem (c.nreg 50200) Q H C) {k : ℕ}
    (hk : c.nreg 50110 = k) (hkm : k ≤ C.m) (hXW : c.nreg 50200 + 5 ≤ W)
    (hmW : 2 * C.m + 7 ≤ W) :
    ∃ c' k', Exec P W tposS c c' k' ∧ k' ≤ 30 ∧ c'.nreg 50201 = 6 + tpos C k ∧
      FrameB Btp c c' := by
  have h1 := C.one_le
  have e₁ := Exec.copyN (P := P) hw 50100 50200
  set c₁ : Config := { c with nreg := upd c.nreg 50100 (c.nreg 50200) } with hc₁
  have w₁ : WordsBounded W c₁ := e₁.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, r01, r02, r08, rr₂, rm₂⟩ := readS_exec (P := P) c₁ w₁
    (X := c.nreg 50200) (by rw [hc₁]; simp) (by rw [hc₁]; exact hC) hXW (by omega)
  have w₂ := e₂.wb_right
  have hS := C.sideS_lt C.sideBeta
  have e₃ := Exec.subN (P := P) w₂ 50103 50108 50102
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 50103 (c₂.nreg 50108 - c₂.nreg 50102) }
    with hc₃
  have w₃ : WordsBounded W c₃ := e₃.wb_right
  have v10 : c₃.nreg 50110 = k := by
    rw [hc₃]; simp only [upd_other _ _ _ (show (50110 : ℕ) ≠ 50103 by decide)]
    rw [rr₂ _ (by omega)]; rw [hc₁]; simp [hk]
  have v02 : c₃.nreg 50102 = C.sideS C.sideBeta := by
    rw [hc₃]; simp only [upd_other _ _ _ (show (50102 : ℕ) ≠ 50103 by decide)]; exact r02
  have v03 : c₃.nreg 50103 = 2 * C.m - C.sideS C.sideBeta := by
    rw [hc₃]; simp only [upd_same]; rw [r08, r02]
  obtain ⟨c₄, k₄, e₄, hk₄, v11, r₄⟩ := candR_exec (P := P) c₃ w₃ (j := 50110) (s := 50102)
    (d := 50103) (dst := 50111) (by rw [v10, v02, v03]; intro h; omega)
  have w₄ := e₄.wb_right
  have hc : c₄.nreg 50111 = tpos C k := by
    rw [v11, v10, v02, v03, tpos_eq_cand C (by omega)]; rfl
  have htp := tpos_lt C k
  obtain ⟨c₅, k₅, e₅, hk₅, q01, q5, qm, qrr, qrm, qo⟩ : ∃ c₅ k₅, Exec P W
      (block [.constN 50112 6, .addN 50201 50111 50112]) c₄ c₅ k₅ ∧ k₅ = 2 ∧
      c₅.nreg 50201 = 6 + tpos C k ∧
      (∀ r, r ≠ 50112 → r ≠ 50201 → c₅.nreg r = c₄.nreg r) ∧ c₅.nmem = c₄.nmem ∧
      c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output := by
    exec_block
    all_goals try omega
    all_goals try (config_simp; rw [hc]; omega)
    refine ⟨rfl, ?_, fun r a1 a2 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; rw [hc]; ring
    · simp (disch := omega) only [Machine.upd_other]
  have ex : Exec P W tposS c c₅ ((1 + 0) + (k₂ + ((1 + 0) + (k₄ + k₅)))) :=
    .seq (.seq e₁ (.skip w₁)) (.seq e₂ (.seq (.seq e₃ (.skip w₃)) (.seq e₄ e₅)))
  exact ⟨c₅, _, ex, by omega, q01, exec_frameB ex wr_tposS⟩

/-! ## One point query -/

/-- Append the query `(50211, 70124 + 1, 50203)`. -/
def ptApp : Stmt := block [.storeN ALLOC 50211, .addN ALLOC ALLOC 70105, .addN 70129 70124 70105,
  .storeN ALLOC 70129, .addN ALLOC ALLOC 70105, .storeN ALLOC 50203, .addN ALLOC ALLOC 70105,
  .addN 70128 70128 70105]

/-- **One point query.** -/
def ptQ : Stmt := .seq arrivalPos (.ifLtN 70108 50210 ptApp .skip)

/-- The outcome of a point query. -/
def PtRes (P : Polygon) (C : Chain) (e h ρ hv : ℕ) (l : List (ℕ × ℕ × ℕ)) : Prop :=
  (l = [] ∧ ∀ p t, ¬ Sweep.Arrival (chainModel C).W ((chainModel C).pos (Qof P) ⟨e, h⟩)
    (-dirOf ρ) p t) ∨
  (∃ e' h', l = [(e', hv + 1, ρ)] ∧ Sweep.Arrival (chainModel C).W
    ((chainModel C).pos (Qof P) ⟨e, h⟩) (-dirOf ρ) e' ((chainModel C).param (Qof P) ⟨e', h'⟩))

set_option maxHeartbeats 4000000 in
theorem ptQ_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hHW : hostWords P.n ≤ W) (hwf : ChainWF P (c.nreg ALLOC) c.nmem (c.nreg 50200)) {H : Host}
    {C : Chain} (hC : ChainDescAt c.nmem (c.nreg 50200) (Qof P) H C) (hin : ArrIn P W C c)
    (h05 : c.nreg 70105 = 1) (h08 : c.nreg 70108 = 0) {LB : ℕ} {pre : List (ℕ × ℕ × ℕ)}
    (hA : c.nreg ALLOC = LB + 3 * pre.length) (h28 : c.nreg 70128 = pre.length)
    (hL : ChordListAt c.nmem LB pre) (hroom : c.nreg ALLOC + 35003 ≤ W)
    (hvW : c.nreg 70124 + 1 ≤ W) (hcW : pre.length + 1 ≤ W) :
    ∃ c' k l, Exec P W ptQ c c' k ∧ k ≤ 35011 ∧ 3 * l.length ≤ k ∧ l.length ≤ 1 ∧
      c'.nreg ALLOC = LB + 3 * (pre ++ l).length ∧ c'.nreg 70128 = (pre ++ l).length ∧
      ChordListAt c'.nmem LB (pre ++ l) ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, Bprim r = false → r ≠ 70128 → r ≠ 70129 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      (∀ r, Bprim r = false → c'.rreg r = c.rreg r) ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧
      PtRes P C (c.nreg 50201) (c.nreg 50202) (c.nreg 50203) (c.nreg 70124) l := by
  obtain ⟨c₁, k₁, e₁, hk₁, hout, F₁⟩ := primRun arrivalPos_meets wr_arrivalPos c hw hG hHW hwf hC
    hin (by omega)
  have w₁ := e₁.wb_right
  have a₁ := frameB_alloc F₁
  have m₁ : c₁.nmem = c.nmem := F₁.2.2.1
  have g : ∀ r, (r < 10000 ∨ (10600 ≤ r ∧ r < 50000) ∨ (50200 ≤ r ∧ r < 50210) ∨ 51000 ≤ r) →
      c₁.nreg r = c.nreg r := fun r hr => frameB_reg F₁ hr
  obtain ⟨hf1, hyes, hno⟩ := hout
  by_cases hf : c₁.nreg 50210 = 1
  · obtain ⟨-, hpp, harr⟩ := hyes hf
    have hlt : c₁.nreg 70108 < c₁.nreg 50210 := by rw [g _ (by omega), h08, hf]; omega
    set a := LB + 3 * pre.length with ha
    have hA₁ : c₁.nreg 9999 = a := by rw [show (9999 : ℕ) = ALLOC from rfl, a₁, hA]
    have r05 : c₁.nreg 70105 = 1 := by rw [g _ (by omega), h05]
    have r24 : c₁.nreg 70124 = c.nreg 70124 := g _ (by omega)
    have r28 : c₁.nreg 70128 = pre.length := by rw [g _ (by omega), h28]
    have r03 : c₁.nreg 50203 = c.nreg 50203 := g _ (by omega)
    obtain ⟨c₂, k₂, e₂, hk₂, q⟩ : ∃ c₂ k₂, Exec P W ptApp c₁ c₂ k₂ ∧ k₂ = 8 ∧
        (c₂.nreg ALLOC = a + 3 ∧ c₂.nreg 70128 = pre.length + 1 ∧
        c₂.nmem a = c₁.nreg 50211 ∧ c₂.nmem (a + 1) = c.nreg 70124 + 1 ∧
        c₂.nmem (a + 2) = c.nreg 50203 ∧ (∀ x, (x < a ∨ a + 3 ≤ x) → c₂.nmem x = c₁.nmem x) ∧
        (∀ r, r ≠ 70128 → r ≠ 70129 → r ≠ ALLOC → c₂.nreg r = c₁.nreg r) ∧
        c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output) := by
      unfold ptApp
      exec_block
      all_goals try (simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hA₁, r05, r24, r28, ALLOC]; omega)
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, fun r a1 a2 a3 => ?_, rfl, rfl, rfl⟩
      all_goals try (simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hA₁, r05, r24, r28, r03, ALLOC])
      · have a3' : r ≠ 9999 := a3
        simp (disch := omega) only [Machine.upd_other]
    obtain ⟨q9, q28, qa, qb, qc, qm, qr, qrr, qrm, qo⟩ := q
    have ex : Exec P W ptQ c c₂ (k₁ + (k₂ + 1)) := .seq e₁ (.ifLtN_true hlt e₂)
    refine ⟨c₂, _, [(c₁.nreg 50211, c.nreg 70124 + 1, c.nreg 50203)], ex, by omega,
      by simp only [List.length_singleton]; omega, by simp,
      by rw [q9, List.length_append, List.length_singleton]; omega,
      by rw [q28, List.length_append, List.length_singleton], ?_, fun x hx => ?_,
      fun r hr a2 a3 a4 => ?_, fun r hr => ?_, by rw [qrm, F₁.2.2.2.1], by rw [qo, F₁.2.2.2.2],
      Or.inr ⟨_, _, rfl, harr⟩⟩
    · refine chordListAt_append (fun i hi => ?_) ?_ ?_ ?_
      · obtain ⟨b0, b1, b2⟩ := hL i hi
        refine ⟨?_, ?_, ?_⟩
        · rw [qm _ (Or.inl (by omega)), m₁]; exact b0
        · rw [qm _ (Or.inl (by omega)), m₁]; exact b1
        · rw [qm _ (Or.inl (by omega)), m₁]; exact b2
      · exact qa
      · exact qb
      · exact qc
    · rw [qm x (Or.inl (by omega)), m₁]
    · rw [qr r a2 a3 a4]; exact F₁.1 r hr
    · rw [qrr]; exact F₁.2.1 r hr
  · have hf0 : c₁.nreg 50210 = 0 := by omega
    have hlt : ¬ c₁.nreg 70108 < c₁.nreg 50210 := by rw [hf0]; omega
    have ex : Exec P W ptQ c c₁ (k₁ + (0 + 2)) := .seq e₁ (.ifLtN_false hlt (.skip w₁))
    refine ⟨c₁, _, [], ex, by omega, by simp, by simp, by rw [a₁, hA]; simp,
      by rw [g _ (by omega), h28]; simp, by rw [m₁]; simpa using hL, fun x _ => by rw [m₁],
      fun r hr _ _ _ => F₁.1 r hr, fun r hr => F₁.2.1 r hr, F₁.2.2.2.1, F₁.2.2.2.2,
      Or.inl ⟨rfl, hno hf⟩⟩

end

end FuseAsm

end Chazelle.Core
