module

meta import Chazelle.Programs.RamEval

public import Chazelle.Core.DownPhaseDrvBFar2
public import Chazelle.Core.DownPhaseDrvDCall3

/-!
# Down-phase base (D9), RAM: appending an emitted chord

`emitS` appends the record `vtrip li n i d w` of the vertex chord of `i = r212070` in direction
code `d = r212086` with far walk edge `w = r212097` to the new chord list `L₂` (base `B₂`) and the
buckets of its two ends (base `BK = B₂ + 3 Kmax`), reusing the appending pieces of the
restoration rounds (`DrvD.appT`, `DrvD.scanS`, `DrvD.stB`; registers `216xxx`):

* `recS`: the record into `81008 … 81010`;
* `bktS`: for `K > 0` (`K = r212012`) the arc scans of both ends (`DrvD.ScanFound`), for `K = 0`
  the bucket `0`.

`emitS_exec`: the list grows by the record, the buckets satisfy `DrvD.BktOK` (`K > 0`) or are
`0` (`K = 0`), and the memory changes only in `[B₂, B₂ + 5 Kmax)`.
-/

namespace Chazelle.Core

namespace DrvB

open Machine Machine.Stmt Programs SignK WalkKey
open BuildRam (FrameM FrameM.mono FrameM.trans FrameB.toM)
open DrvR (ivB qE)

@[expose] public section

/-! ## The program -/

/-- `ivB li n i` into `212046`. -/
def ivS : Stmt :=
  .ifLtN 212001 212011 (.instr (.copyN 212046 212070))
    (block [.subN 212046 212010 212000, .subN 212046 212046 212070])

/-- The record `vtrip li n i d w` into `81008 … 81010`. -/
def recS : Stmt :=
  .seq (.instr (.copyN 81008 212070)) (.seq ivS
    (.ifLtN 212001 212086 (block [.copyN 81009 212097, .copyN 81010 212046])
      (block [.copyN 81009 212046, .copyN 81010 212097])))

/-- The buckets of both ends: arc scans (`K > 0`) or `0` (`K = 0`). -/
def bktS : Stmt :=
  .ifLtN 212001 212012
    (.seq DrvD.scanS (.seq DrvD.stB (.seq (.instr (.copyN 216040 81010))
      (.seq DrvD.scanS DrvD.stB))))
    (.seq (.instr (.constN 216053 0)) (.seq DrvD.stB DrvD.stB))

/-- **Append the record and its buckets.** -/
def emitS : Stmt := .seq recS (.seq DrvD.appT bktS)

/-- The registers `recS` writes. -/
def Brec (r : ℕ) : Bool := decide (81008 ≤ r ∧ r ≤ 81010) || decide (r = 212046)

theorem wr_recS : wr Brec recS = true := by decide

/-- The registers `emitS` writes. -/
def Bemit (r : ℕ) : Bool := Brec r || DrvD.Bapp r

theorem bemit_rec (r : ℕ) (h : Brec r = true) : Bemit r = true := by simp [Bemit, h]

theorem bemit_app (r : ℕ) (h : DrvD.Bapp r = true) : Bemit r = true := by simp [Bemit, h]

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 2000000 in
/-- **The record.** -/
theorem recS_exec (c : Config) (hw : WordsBounded W c) {li : Bool} {n i d w : ℕ}
    (hn : c.nreg 212010 = n) (hi : c.nreg 212070 = i) (_hin : i < n) (hd : c.nreg 212086 = d)
    (hd1 : d ≤ 1) (hw97 : c.nreg 212097 = w) (hli : c.nreg 212011 = if li then 1 else 0)
    (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0) :
    ∃ c' k, Exec P W recS c c' k ∧ k ≤ 9 ∧ c'.nreg 81008 = (vtrip li n i d w).1 ∧
      c'.nreg 81009 = (vtrip li n i d w).2.1 ∧ c'.nreg 81010 = (vtrip li n i d w).2.2 ∧
      FrameB Brec c c' := by
  have e₁ := Exec.copyN (P := P) hw 81008 212070
  set c₁ : Config := { c with nreg := upd c.nreg 81008 (c.nreg 212070) } with hc₁
  have w₁ := e₁.wb_right
  have g₁ : ∀ r, r ≠ 81008 → c₁.nreg r = c.nreg r := fun r h => by rw [hc₁]; simp [h]
  -- `ivB`
  obtain ⟨c₂, k₂, e₂, hk₂, v46, g₂⟩ : ∃ c₂ k₂, Exec P W ivS c₁ c₂ k₂ ∧ k₂ ≤ 4 ∧
      c₂.nreg 212046 = ivB li n i ∧ ∀ r, r ≠ 212046 → c₂.nreg r = c₁.nreg r := by
    cases li with
    | true =>
      have a := Exec.copyN (P := P) w₁ 212046 212070
      refine ⟨_, _, .ifLtN_true (by simp_all) a,
        by omega, ?_, fun r h => by simp [h]⟩
      assumption
    | false =>
      obtain ⟨c₂, k₂, e₂, hk₂, v⟩ : ∃ c₂ k₂, Exec P W (block [.subN 212046 212010 212000,
          .subN 212046 212046 212070]) c₁ c₂ k₂ ∧ k₂ = 2 ∧ (c₂.nreg 212046 = n - 1 - i ∧
          ∀ r, r ≠ 212046 → c₂.nreg r = c₁.nreg r) := by
        ram_exec
      exact ⟨c₂, _, .ifLtN_false (by simp_all)
        e₂, by omega, by rw [v.1]; rfl, v.2⟩
  have w₂ := e₂.wb_right
  -- the ends
  have hd' : c₂.nreg 212086 = d := by simp_all
  have c1' : c₂.nreg 212001 = 0 := by simp_all
  have hw' : c₂.nreg 212097 = w := by simp_all
  have h81 : c₂.nreg 81008 = i := by
    simp_all
  rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl
  · obtain ⟨c₃, k₃, e₃, hk₃, v⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 81009 212046,
        .copyN 81010 212097]) c₂ c₃ k₃ ∧ k₃ = 2 ∧ (c₃.nreg 81009 = ivB li n i ∧
        c₃.nreg 81010 = w ∧ c₃.nreg 81008 = i) := by
      verify_block
    have ex : Exec P W recS c c₃ _ := .seq e₁ (.seq e₂ (.ifLtN_false (by rw [c1', hd']; omega) e₃))
    exact ⟨c₃, _, ex, by omega, v.2.2, v.1, v.2.1, exec_frameB ex wr_recS⟩
  · obtain ⟨c₃, k₃, e₃, hk₃, v⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 81009 212097,
        .copyN 81010 212046]) c₂ c₃ k₃ ∧ k₃ = 2 ∧ (c₃.nreg 81009 = w ∧
        c₃.nreg 81010 = ivB li n i ∧ c₃.nreg 81008 = i) := by
      verify_block
    have ex : Exec P W recS c c₃ _ := (by ram_path)
    exact ⟨c₃, _, ex, by omega, v.2.2, v.1, v.2.1, exec_frameB ex wr_recS⟩

theorem vtrip_fst (li : Bool) (n i d w : ℕ) : (vtrip li n i d w).1 = i := by
  unfold vtrip; split_ifs <;> rfl

set_option maxHeartbeats 8000000 in
/-- **Appending an emitted chord**: the record `x = vtrip li n i d w` is appended at
`B₂ + 3 |T|`, the buckets of its ends at `BK + 2 |T|`, `BK + 2 |T| + 1` (`BK = B₂ + 3 Kmax`). -/
theorem emitS_exec (_hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) {li : Bool} {i d w r K MD H A₀ B₂ Kmax : ℕ} {m₀ : ℕ → ℕ}
    {N : NF} {T : List (ℕ × (ℕ × ℕ × ℕ))}
    (hi : c.nreg 212070 = i) (hin : i < P.n) (hd : c.nreg 212086 = d) (hd1 : d ≤ 1)
    (hw97 : c.nreg 212097 = w) (hli : c.nreg 212011 = if li then 1 else 0)
    (hn : c.nreg 212010 = P.n) (hK : c.nreg 212012 = K)
    (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0)
    (d02 : c.nreg 216002 = 1) (d03 : c.nreg 216003 = 0) (d05 : c.nreg 216005 = 2)
    (d14 : c.nreg 216014 = m₀ (H + 4)) (d16 : c.nreg 216016 = m₀ (H + 7))
    (d17 : c.nreg 216017 = N.arcs.length) (d31 : c.nreg 216031 = m₀ (H + 5) + 2 + 5 * r)
    (d001 : c.nreg 210001 = MD)
    (d20 : c.nreg 216020 = T.length) (d21 : c.nreg 216021 = B₂ + 3 * T.length)
    (d22 : c.nreg 216022 = B₂ + 3 * Kmax + 2 * T.length)
    (hlow : MemEqBelow A₀ c.nmem m₀) (hA₀ : A₀ ≤ B₂) (hTK : T.length < Kmax)
    (hroom : B₂ + 5 * Kmax ≤ W) (hp : m₀ (H + 5) + 2 + 5 * r < A₀)
    (hLB : m₀ (H + 7) + m₀ (m₀ (H + 5) + 5 * r + 1) ≤ W)
    (hlist : ChordListAt c.nmem B₂ (T.map Prod.snd))
    (hbk : 0 < K → DrvD.BktOK (inputModel P) (Qof P) N T
      (fun q => c.nmem (B₂ + 3 * Kmax + q)))
    (hbk0 : K = 0 → ∀ q, q < 2 * T.length → c.nmem (B₂ + 3 * Kmax + q) = 0)
    (hnA : (N.region r).arcs.length = m₀ (m₀ (H + 5) + 5 * r))
    (hscan : 0 < K → ∀ m : ℕ → ℕ, (MemEqBelow A₀ m m₀) → (∀ a, m a ≤ W) → ∀ s, s < 2 →
      DrvD.ScanGood P W (inputModel P) N r (DrvD.endPos (vtrip li P.n i d w) s) m MD
        (m₀ (H + 4)) (m₀ (H + 7) + m₀ (m₀ (H + 5) + 5 * r + 1)))
    (hex : 0 < K → ∀ s, s < 2 → ∃ j ∈ (N.region r).arcs, DrvD.matchB N.arcs.length j
      (DrvD.tA (inputModel P) (Qof P) N (DrvD.endPos (vtrip li P.n i d w) s) j)
      (DrvD.tB (inputModel P) (Qof P) N (DrvD.endPos (vtrip li P.n i d w) s) j) = true) :
    ∃ c' k, Exec P W emitS c c' k ∧ k ≤ 2 * (DrvD.scanK + 2) * (N.region r).arcs.length + 40 ∧
      FrameM Bemit c c' ∧ WordsBounded W c' ∧
      (∀ a, (a < B₂ ∨ B₂ + 5 * Kmax ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.nreg 216020 = T.length + 1 ∧ c'.nreg 216021 = B₂ + 3 * (T.length + 1) ∧
      c'.nreg 216022 = B₂ + 3 * Kmax + 2 * (T.length + 1) ∧
      ChordListAt c'.nmem B₂ ((T ++ [(r, vtrip li P.n i d w)]).map Prod.snd) ∧
      (0 < K → DrvD.BktOK (inputModel P) (Qof P) N (T ++ [(r, vtrip li P.n i d w)])
        (fun q => c'.nmem (B₂ + 3 * Kmax + q))) ∧
      (K = 0 → ∀ q, q < 2 * (T.length + 1) → c'.nmem (B₂ + 3 * Kmax + q) = 0) := by
  set x := vtrip li P.n i d w with hx
  set t := T.length with ht
  set BK := B₂ + 3 * Kmax with hBK
  set p := m₀ (H + 5) + 2 + 5 * r with hpd
  have hW3 : P.n + 3 ≤ W := by have := hWh; unfold hostWords at this; omega
  -- 1. the record
  obtain ⟨c₁, k₁, e₁, hk₁, r1, r2, r3, f₁⟩ := recS_exec (P := P) c hw hn hi hin hd hd1 hw97 hli c0 c1
  have w₁ := e₁.wb_right
  have g₁ := f₁.1
  -- 2. the triple
  obtain ⟨c₂, k₂, e₂, hk₂, m₂, d21', d20', d42, d43, d41, d400, d40, f₂⟩ := DrvD.appT_exec (P := P)
    c₁ w₁ (d := B₂ + 3 * t) (n := t) (p := p) (LB := m₀ (H + 7))
    (by ram_rw [g₁, d21]) (by ram_rw [g₁, d20])
    (by ram_rw [g₁, d02]) (by ram_rw [g₁, d05])
    (by ram_rw [g₁, d31]) (by ram_rw [g₁, d16]) (by omega) (by omega)
    (by omega) (by ram_simp [f₁.2.2.1, show p - 1 = m₀ (H + 5) + 5 * r + 1 by omega, hlow] <;> omega)
    (by rw [r1, vtrip_fst]; omega) (by omega)
  have w₂ := e₂.wb_right
  ram_rw [f₁.2.2.1, show p - 2 = m₀ (H + 5) + 5 * r by omega, hlow, ← hnA] at d42
  ram_rw [f₁.2.2.1, show p - 1 = m₀ (H + 5) + 5 * r + 1 by omega, hlow] at d43
  rw [r1, vtrip_fst] at d41
  rw [r2] at d40
  ram_rw [g₁, d001] at d400
  have g₂ := f₂.1
  have m₂' : ∀ a, (a < B₂ + 3 * t ∨ B₂ + 3 * t + 3 ≤ a) → c₂.nmem a = c.nmem a := fun a ha => by
    ram_rw [m₂, Machine.upd_other _ _, Machine.upd_other _ _,
      Machine.upd_other _ _, f₁.2.2.1]
  -- the list
  have hL₂ : ChordListAt c₂.nmem B₂ ((T ++ [(r, x)]).map Prod.snd) := by
    rw [List.map_append]
    have hlen : (T.map Prod.snd).length = t := by rw [List.length_map]
    refine hlist.snoc (fun a h1 h2 => ?_) ?_ ?_ ?_
    · rw [hlen] at h2; exact m₂' a (by omega)
    · ram_rw [hlen, m₂, Machine.upd_other _ _, Machine.upd_other _ _,
        Machine.upd_same, r1]
    · ram_rw [hlen, m₂, Machine.upd_other _ _, Machine.upd_same, r2]
    · rw [hlen, m₂, Machine.upd_same, r3]
  have hlow₂ : MemEqBelow A₀ c₂.nmem m₀ := fun a ha => (m₂' a (by omega)).trans (hlow a ha)
  -- registers kept so far
  have K2 := fun q h1 h2 => (g₂ q h2).trans (g₁ q h1)
  have c1₂ : c₂.nreg 212001 = 0 := by ram_simp [K2, c1]
  have hK₂ : c₂.nreg 212012 = K := by ram_simp [K2, hK]
  have d22₂ : c₂.nreg 216022 = BK + 2 * t := by ram_simp [K2, d22]
  have d02₂ : c₂.nreg 216002 = 1 := by ram_simp [K2, d02]
  have hlen₂ : ((T ++ [(r, x)]).map Prod.snd).length = t + 1 := by simp [ht]
  have FM₁ := (FrameB.toM f₁).mono bemit_rec
  have FM₂ := f₂.mono fun q h => bemit_app q (DrvD.bapp_of_appT q h)
  rcases Nat.eq_zero_or_pos K with hK0 | hKp
  · -- `K = 0`: the buckets `0`
    have e₃ := Exec.constN (P := P) w₂ 216053 0 (Nat.zero_le _)
    set c₃ : Config := { c₂ with nreg := upd c₂.nreg 216053 0 } with hc₃
    have g₃ : ∀ q, q ≠ 216053 → c₃.nreg q = c₂.nreg q := fun q h => by rw [hc₃]; simp [h]
    obtain ⟨c₄, k₄, e₄, hk₄, m₄, d22₄, f₄⟩ := DrvD.stB_exec (P := P) c₃ e₃.wb_right
      (d := BK + 2 * t) (by assumption) (by assumption)
      (by omega)
    obtain ⟨c₅, k₅, e₅, hk₅, m₅, d22₅, f₅⟩ := DrvD.stB_exec (P := P) c₄ e₄.wb_right
      (d := BK + 2 * t + 1) d22₄ (by simp [f₄.1, g₃, d02₂])
      (by omega)
    have v53 : c₄.nreg 216053 = 0 := by simp [f₄.1, hc₃]
    have ex : Exec P W emitS c c₅ (k₁ + (k₂ + (1 + (k₄ + k₅) + 2))) :=
      .seq e₁ (.seq e₂ (.ifLtN_false (by simp [c1₂, hK₂, hK0]) (.seq e₃ (.seq e₄ e₅))))
    have m₅' : c₅.nmem = upd (upd c₂.nmem (BK + 2 * t) 0) (BK + 2 * t + 1) 0 := by
      rw [m₅, m₄, v53]; rfl
    have FM₃ : FrameM Bemit c₂ c₅ := (((FrameB.toM (exec_frameB e₃ (by decide :
      wr (fun q => decide (q = 216053)) (.instr (.constN 216053 0)) = true))).mono fun q h => by
        simp only [decide_eq_true_eq] at h; subst h; decide).trans
      ((f₄.mono fun q h => by simp only [decide_eq_true_eq] at h; subst h; decide).trans
        (f₅.mono fun q h => by simp only [decide_eq_true_eq] at h; subst h; decide)))
    have G5 : ∀ q, q ≠ 216053 → q ≠ 216022 → c₅.nreg q = c₂.nreg q := fun q h1 h2 => by
      rw [f₅.1 q (by simpa using h2), f₄.1 q (by simpa using h2), g₃ q h1]
    refine ⟨c₅, _, ex, ?_, FM₁.trans (FM₂.trans FM₃), e₅.wb_right, fun a ha => ?_, ?_, ?_, ?_,
      ?_, fun h => absurd hK0 (by omega), fun _ q hq => ?_⟩
    · have : 0 ≤ 2 * (DrvD.scanK + 2) * (N.region r).arcs.length := Nat.zero_le _
      omega
    · ram_rw [m₅', Machine.upd_other _ _, Machine.upd_other _ _,
        m₂' a]
    · simp [G5, d20']
    · ram_rw [G5, d21']; ring
    · rw [d22₅]; ring
    · refine hL₂.congr fun a h1 h2 => ?_
      rw [hlen₂] at h2
      ram_rw [m₅', Machine.upd_other _ _, Machine.upd_other _ _]
    · rw [m₅']
      rcases Nat.lt_or_ge q (2 * t) with hq' | hq'
      · ram_rw [Machine.upd_other _ _, Machine.upd_other _ _,
          m₂']
        exact hbk0 hK0 q hq'
      · rcases (by omega : q = 2 * t ∨ q = 2 * t + 1) with rfl | rfl
        · simp
        ram_simp [show BK + (2 * t + 1) = BK + 2 * t + 1 by ring]
  · -- `K > 0`: the arc scans
    have S1 := hscan hKp c₂.nmem hlow₂ w₂.2 0 (by norm_num)
    obtain ⟨c₃, k₃, e₃, hk₃, fd₀, f₃⟩ := DrvD.scanS_exec S1 c₂ w₂ rfl
      (by rw [d40]; rfl) (by rw [d41]; simp [DrvD.endPos, vtrip_fst, hx]) (by rw [d42])
      (by rw [d43]) (by ram_simp [K2, d14])
      (by ram_simp [K2, d17]) d02₂
      (by ram_simp [K2, d03]) (by rw [d400]) (hex hKp 0 (by norm_num))
    have w₃ := e₃.wb_right
    have g₃ := f₃.1
    obtain ⟨c₄, k₄, e₄, hk₄, m₄, d22₄, f₄⟩ := DrvD.stB_exec (P := P) c₃ w₃
      (d := BK + 2 * t) (by ram_simp [g₃, d22₂]) (by ram_simp [g₃, d02₂])
      (by omega)
    have w₄ := e₄.wb_right
    have g₄ := fun q h => f₄.1 q (by simpa using h)
    have e₅ := Exec.copyN (P := P) w₄ 216040 81010
    set c₅ : Config := { c₄ with nreg := upd c₄.nreg 216040 (c₄.nreg 81010) } with hc₅
    have w₅ := e₅.wb_right
    have g₅ : ∀ q, q ≠ 216040 → c₅.nreg q = c₄.nreg q := fun q h => by rw [hc₅]; simp [h]
    -- the memory before the second scan
    have m₄' : c₄.nmem = upd c₂.nmem (BK + 2 * t) (c₃.nreg 216053) := by rw [m₄, f₃.2.2.1]
    have hlow₅ : MemEqBelow A₀ c₅.nmem m₀ := fun a ha => by
      show c₄.nmem a = _
      ram_rw [m₄', Machine.upd_other _ _, hlow₂ a ha]
    have S2 := hscan hKp c₅.nmem hlow₅ w₅.2 1 (by norm_num)
    have K3 : ∀ q, DrvD.Bscan q = false → q ≠ 216022 → q ≠ 216040 → c₅.nreg q = c₂.nreg q :=
      fun q h1 h2 h3 => by rw [g₅ q h3, g₄ q h2, g₃ q h1]
    obtain ⟨c₆, k₆, e₆, hk₆, fd₁, f₆⟩ := DrvD.scanS_exec S2 c₅ w₅ rfl
      (by rw [hc₅]; simp only [Machine.upd_same]
          ram_rw [g₄, g₃, g₂, r3]; rfl)
      (by ram_rw [K3, d41]
          simp [DrvD.endPos, vtrip_fst, hx])
      (by ram_simp [K3, d42])
      (by ram_simp [K3, d43])
      (by ram_simp [K3, K2, d14])
      (by ram_simp [K3, K2, d17])
      (by ram_simp [K3, d02₂])
      (by ram_simp [K3, K2, d03])
      (by ram_simp [K3, d400]) (hex hKp 1 (by norm_num))
    have w₆ := e₆.wb_right
    obtain ⟨c₇, k₇, e₇, hk₇, m₇, d22₇, f₇⟩ := DrvD.stB_exec (P := P) c₆ w₆
      (d := BK + 2 * t + 1) (by ram_simp [f₆.1, g₅, d22₄])
      (by ram_simp [f₆.1, K3, d02₂])
      (by omega)
    have ex : Exec P W emitS c c₇ (k₁ + (k₂ + ((k₃ + (k₄ + (1 + (k₆ + k₇)))) + 1))) :=
      (by ram_path)
    have m₇' : c₇.nmem = upd (upd c₂.nmem (BK + 2 * t) (c₃.nreg 216053)) (BK + 2 * t + 1)
        (c₆.nreg 216053) := by
      rw [m₇, f₆.2.2.1]; show upd c₄.nmem _ _ = _; rw [m₄']
    have FM₃ := (((FrameB.toM f₃).mono fun q h => bemit_app q (DrvD.bapp_of_scan q h)).trans
      ((f₄.mono fun q h => bemit_app q (DrvD.bapp_of_22 q h)).trans
      (((FrameB.toM (exec_frameB e₅ (by decide :
        wr (fun q => decide (q = 216040)) (.instr (.copyN 216040 81010)) = true))).mono
          fun q h => bemit_app q (DrvD.bapp_of_40 q h)).trans
      (((FrameB.toM f₆).mono fun q h => bemit_app q (DrvD.bapp_of_scan q h)).trans
      (f₇.mono fun q h => bemit_app q (DrvD.bapp_of_22 q h))))))
    have G7 : ∀ q, DrvD.Bscan q = false → q ≠ 216022 → q ≠ 216040 → c₇.nreg q = c₂.nreg q :=
      fun q h1 h2 h3 => by rw [f₇.1 q (by simpa using h2), f₆.1 q h1, K3 q h1 h2 h3]
    
    refine ⟨c₇, _, ex, ?_, FM₁.trans (FM₂.trans FM₃), e₇.wb_right, fun a ha => ?_, ?_, ?_, ?_,
      ?_, fun _ => ?_, fun h => absurd h (by omega)⟩
    · have : 2 * (DrvD.scanK + 2) * (N.region r).arcs.length =
          (DrvD.scanK + 2) * (N.region r).arcs.length +
            (DrvD.scanK + 2) * (N.region r).arcs.length := by ring
      omega
    · ram_rw [m₇', Machine.upd_other _ _, Machine.upd_other _ _,
        m₂' a]
    · ram_simp [G7, d20']
    · ram_rw [G7, d21']; ring
    · rw [d22₇]; ring
    · refine hL₂.congr fun a h1 h2 => ?_
      rw [hlen₂] at h2
      ram_rw [m₇', Machine.upd_other _ _, Machine.upd_other _ _]
    · refine DrvD.BktOK.snoc (hbk hKp) (fun q hq => ?_) ?_ ?_
      · show c₇.nmem (BK + q) = c.nmem (BK + q)
        ram_rw [m₇', Machine.upd_other _ _, Machine.upd_other _ _,
          m₂']
      · show DrvD.ScanFound _ _ N r _ (c₇.nmem (BK + 2 * t))
        ram_simp [m₇'] <;> omega
      · show DrvD.ScanFound _ _ N r _ (c₇.nmem (BK + (2 * t + 1)))
        ram_simp [m₇', show BK + (2 * t + 1) = BK + 2 * t + 1 by ring] <;> reg_omega

end exec

end

end DrvB

end Chazelle.Core
