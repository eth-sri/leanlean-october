module

public import Chazelle.Core.SortRam

/-!
# Binary search on the RAM (WP-C, the core of double identification)

`searchStmt cmp` finds the **partition point** of an array of `n` items for a monotone predicate
`pr` (true on a prefix, false on the rest), decided by a procedure `cmp` with contract `PredOK`
(it reads one item in `lr 100` and writes the bit `pr item` into `lr 102`).  The machine has no
halving instruction, so the search is a binary lifting over a table of the powers `2 ^ j ≤ n`,
built first in fresh memory (the allocator grows by the table length, at most the cost).  Only
additions, subtractions and comparisons of naturals are used, and every computed value is at most
`n + 1`, an address below the new allocator, or a power `≤ n` (so no overflow of the word bound
even when `2 n` exceeds it).

Registers (band `bLocate`, `lr i = bandReg bLocate i = 50000 + i`): `lr 103` array base `A`,
`lr 104` length `n`, output `lr 105` the partition point; scratch `lr 106 … lr 116`.

Main result (`searchStmt_exec`): cost `≤ searchCost κ n = (κ + 37) (⌈log₂ n⌉ + 1)`; the output
`t ≤ n` satisfies `pr (A[j])` for `j < t` and `¬ pr (A[t])` if `t < n`; frame
`Frame (insert bLocate Bc)`.
-/

namespace Chazelle.Core

namespace SearchR

open Machine Machine.Stmt Programs SortL SortR

@[expose] public section

/-! ## The program -/

/-- Register `i` of the band of double identification. -/
def lr (i : ℕ) : ℕ := 50000 + i

/-- Constants: `one`, `p := 1`, `L := 0`, table base `T := ALLOC`, `pos := 0`, `n + 1`, `0`. -/
def srchInit : Stmt := block [.constN 50106 1, .constN 50107 1, .constN 50108 0, .copyN 50109 9999,
  .constN 50105 0, .addN 50114 50104 50106, .constN 50115 0]

/-- `T[L] := p`, `L := L + 1`, `ALLOC := ALLOC + 1`; `p := 2 p` if `2 p ≤ n`, else `p := n + 1`. -/
def tabBody : Stmt :=
  .seq (block [.addN 50110 50109 50108, .storeN 50110 50107, .addN 50108 50108 50106,
      .addN 9999 9999 50106, .subN 50116 50104 50107])
    (.ifLtN 50116 50107 (.instr (.copyN 50107 50114)) (.instr (.addN 50107 50107 50107)))

/-- The table of the powers `2 ^ j ≤ n`. -/
def tabLoop : Stmt := .whileLtN 50107 50114 tabBody

/-- Probe `A[pos + step - 1]`; move `pos` to `pos + step` if the predicate holds there. -/
def probe (cmp : Stmt) : Stmt :=
  .seq (block [.addN 50113 50105 50111, .subN 50110 50113 50106, .addN 50110 50103 50110,
      .loadN 50100 50110])
    (.seq cmp (.ifLtN 50102 50106 .skip (.instr (.copyN 50105 50113))))

/-- `i := i - 1`, `step := T[i]`; probe if `pos + step ≤ n`. -/
def liftBody (cmp : Stmt) : Stmt :=
  .seq (block [.subN 50112 50112 50106, .addN 50110 50109 50112, .loadN 50111 50110,
      .subN 50116 50104 50105])
    (.ifLtN 50116 50111 .skip (probe cmp))

/-- The binary lifting, `i = L, …, 1`. -/
def liftLoop (cmp : Stmt) : Stmt := .whileLtN 50115 50112 (liftBody cmp)

/-- **The search.** -/
def searchStmt (cmp : Stmt) : Stmt :=
  .seq srchInit (.seq tabLoop (.seq (.instr (.copyN 50112 50108)) (liftLoop cmp)))

/-- The cost bound of the search for a predicate procedure of cost `≤ κ`. -/
def searchCost (κ n : ℕ) : ℕ := (κ + 37) * (Nat.clog 2 n + 1)

/-! ## Contracts and frames -/

/-- **Contract of a predicate procedure**: from every word-bounded configuration satisfying `J`,
`cmp` runs in at most `κ` steps, keeps `J`, writes into `lr 102` the bit `pr (lr 100)`, and changes
no natural register except `lr 100 … lr 102` and those of the bands `Bc` (never `ALLOC`), no real
register outside `Bc`, no memory and no output. -/
def PredOK (P : Polygon) (W : ℕ) (cmp : Stmt) (Bc : Finset ℕ) (J : Config → Prop)
    (pr : ℕ → Bool) (κ : ℕ) : Prop :=
  ∀ c, WordsBounded W c → J c →
    ∃ c' k, Exec P W cmp c c' k ∧ k ≤ κ ∧ J c' ∧
      c'.nreg 50102 = (if pr (c.nreg 50100) then 1 else 0) ∧
      (∀ r, r ≠ 50100 → r ≠ 50101 → r ≠ 50102 → (bandOf r ∉ Bc ∨ r = ALLOC) →
        c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ Bc → c'.rreg r = c.rreg r) ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output

/-- `J` is insensitive to the writes of the search itself (registers of band `bLocate`, the
allocator, memory from `A₀` on). -/
def JStableL (J : Config → Prop) (A₀ : ℕ) : Prop :=
  ∀ c c', J c → (∀ r, bandOf r ≠ bLocate → r ≠ ALLOC → c'.nreg r = c.nreg r) →
    c'.rreg = c.rreg → (∀ a, a < A₀ → c'.nmem a = c.nmem a) → c'.rmem = c.rmem →
      c'.output = c.output → J c'

/-- A step of the search itself. -/
def SLL (A₀ : ℕ) (c c' : Config) : Prop :=
  (∀ r, bandOf r ≠ bLocate → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
    (∀ a, a < A₀ → c'.nmem a = c.nmem a) ∧ c'.rmem = c.rmem ∧ c'.output = c.output

/-- The global frame of the search relative to its entry configuration `c₀`. -/
def LocL (Bc : Finset ℕ) (A₀ : ℕ) (c₀ c : Config) : Prop :=
  (∀ r, bandOf r ∉ Bc → bandOf r ≠ bLocate → r ≠ ALLOC → c.nreg r = c₀.nreg r) ∧
    (∀ r, bandOf r ∉ Bc → c.rreg r = c₀.rreg r) ∧ (∀ a, a < A₀ → c.nmem a = c₀.nmem a) ∧
    c.rmem = c₀.rmem ∧ c.output = c₀.output

/-- The entry configuration is within the frame. -/
theorem LocL.refl (Bc : Finset ℕ) (A₀ : ℕ) (c : Config) : LocL Bc A₀ c c :=
  ⟨fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

/-- A step of the search keeps the global frame. -/
theorem LocL.sl {Bc : Finset ℕ} {A₀ : ℕ} {c₀ c c' : Config} (h : LocL Bc A₀ c₀ c)
    (h' : SLL A₀ c c') : LocL Bc A₀ c₀ c' :=
  ⟨fun r h1 h2 h3 => (h'.1 r h2 h3).trans (h.1 r h1 h2 h3),
    fun r h1 => by rw [h'.2.1]; exact h.2.1 r h1,
    fun a ha => (h'.2.2.1 a ha).trans (h.2.2.1 a ha), h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.trans h.2.2.2.2⟩

/-- The band of a register outside the band `bLocate`. -/
theorem bandOf_loc {r : ℕ} (h : bandOf r ≠ bLocate) : r < 50000 ∨ 60000 ≤ r := by
  unfold bandOf bLocate at h
  omega

/-- The predicate procedure keeps the global frame. -/
theorem LocL.cmp {Bc : Finset ℕ} {A₀ : ℕ} {c₀ c c' : Config} (h : LocL Bc A₀ c₀ c)
    (hr : ∀ r, r ≠ 50100 → r ≠ 50101 → r ≠ 50102 → (bandOf r ∉ Bc ∨ r = ALLOC) →
      c'.nreg r = c.nreg r)
    (hrr : ∀ r, bandOf r ∉ Bc → c'.rreg r = c.rreg r) (hm : c'.nmem = c.nmem)
    (hrm : c'.rmem = c.rmem) (ho : c'.output = c.output) : LocL Bc A₀ c₀ c' := by
  refine ⟨fun r h1 h2 h3 => ?_, fun r h1 => (hrr r h1).trans (h.2.1 r h1),
    fun a ha => by rw [hm]; exact h.2.2.1 a ha, hrm.trans h.2.2.2.1, ho.trans h.2.2.2.2⟩
  have := bandOf_loc h2
  exact (hr r (by omega) (by omega) (by omega) (Or.inl h1)).trans (h.1 r h1 h2 h3)

/-! ## The table of powers -/

section tab
variable {P : Polygon} {W : ℕ} {J : Config → Prop} {Bc : Finset ℕ} {A₀ : ℕ}

/-- **The invariant of the table loop**, relative to the entry configuration `c₀`. -/
structure TabInv (W : ℕ) (J : Config → Prop) (Bc : Finset ℕ) (A₀ : ℕ) (c₀ : Config) (A n : ℕ)
    (c : Config) : Prop where
  wb : WordsBounded W c
  hJ : J c
  loc : LocL Bc A₀ c₀ c
  rA : c.nreg 50103 = A
  rn : c.nreg 50104 = n
  pos0 : c.nreg 50105 = 0
  one : c.nreg 50106 = 1
  rT : c.nreg 50109 = A₀
  rn1 : c.nreg 50114 = n + 1
  zero : c.nreg 50115 = 0
  alloc : c.nreg ALLOC = A₀ + c.nreg 50108
  tab : ∀ j, j < c.nreg 50108 → c.nmem (A₀ + j) = 2 ^ j
  pow : c.nreg 50107 ≤ n → c.nreg 50107 = 2 ^ c.nreg 50108
  big : n < c.nreg 50107 → n < 2 ^ c.nreg 50108
  pn1 : c.nreg 50107 ≤ n + 1
  lb : c.nreg 50108 = 0 ∨ 2 ^ (c.nreg 50108 - 1) ≤ n
  bW : A₀ + Nat.clog 2 n + 2 ≤ W
  bn : n + 1 ≤ W

variable {c₀ : Config} {A n : ℕ}

/-- The length of the table is at most `⌈log₂ n⌉ + 1`. -/
theorem tab_len_le {L : ℕ} (h : L = 0 ∨ 2 ^ (L - 1) ≤ n) : L ≤ Nat.clog 2 n + 1 := by
  rcases h with h | h
  · omega
  · have h1 := Nat.le_log_of_pow_le (by norm_num) h
    have h2 := Nat.log_le_clog 2 n
    omega

/-- **The table loop**: the table of the powers `2 ^ j < 2 n` (`j < L`), `n < 2 ^ L`; cost
`≤ 10 (⌈log₂ n⌉ + 1) + 2`; the allocator grows by at most the cost. -/
theorem tabLoop_inv (hJs : JStableL J A₀) {c : Config} (h : TabInv W J Bc A₀ c₀ A n c)
    (hL0 : c.nreg 50108 = 0) :
    ∃ c' k, Exec P W tabLoop c c' k ∧ TabInv W J Bc A₀ c₀ A n c' ∧ n < 2 ^ c'.nreg 50108 ∧
      k ≤ 10 * (Nat.clog 2 n + 1) + 2 ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k := by
  obtain ⟨c', k, e, I', hex, hk, hψ⟩ := whileLtN_potential_lb (P := P) (a := 50107) (b := 50114)
    (TabInv W J Bc A₀ c₀ A n) (fun d => 10 * (Nat.clog 2 n + 1 - d.nreg 50108))
    (fun d => d.nreg ALLOC) (fun _ h => h.wb) (fun d hd ht => by
      have hn1 := hd.rn1
      rw [hn1] at ht
      have hp := hd.pow (by omega)
      have hlog : d.nreg 50108 ≤ Nat.clog 2 n := by
        have h1 := Nat.le_log_of_pow_le (b := 2) (by norm_num) (show 2 ^ d.nreg 50108 ≤ n by omega)
        have h2 := Nat.log_le_clog 2 n
        omega
      have hbW := hd.bW
      have hbn := hd.bn
      have hal := hd.alloc
      have hL2 : d.nreg 50108 < 2 ^ d.nreg 50108 := Nat.lt_two_pow_self
      -- the straight-line part
      obtain ⟨d₁, k₁, e₁, hk₁, q⟩ : ∃ d₁ k₁, Exec P W (block [.addN 50110 50109 50108,
          .storeN 50110 50107, .addN 50108 50108 50106, .addN 9999 9999 50106,
          .subN 50116 50104 50107]) d d₁ k₁ ∧ k₁ = 5 ∧
          (d₁.nmem = upd d.nmem (A₀ + d.nreg 50108) (d.nreg 50107) ∧
            d₁.nreg 50108 = d.nreg 50108 + 1 ∧ d₁.nreg 9999 = d.nreg 9999 + 1 ∧
            d₁.nreg 50116 = n - d.nreg 50107 ∧
            (∀ r, r ≠ 50110 → r ≠ 50108 → r ≠ 9999 → r ≠ 50116 → d₁.nreg r = d.nreg r) ∧
            d₁.rreg = d.rreg ∧ d₁.rmem = d.rmem ∧ d₁.output = d.output) := by
        have hw := hd.wb
        exec_block
        · rw [hd.rT]; omega
        · config_simp; rw [hd.one]; omega
        · config_simp; rw [hd.one, show (9999 : ℕ) = ALLOC from rfl, hal]; omega
        · refine ⟨rfl, ?_⟩
          refine ⟨by config_simp; rw [hd.rT], by config_simp; rw [hd.one],
            by config_simp; rw [hd.one], by config_simp; rw [hd.rn], fun r h1 h2 h3 h4 => ?_,
            rfl, rfl, rfl⟩
          simp [h1, h2, h3, h4]
      obtain ⟨m₁, l₁, a₁, s₁, r₁, rr₁, rm₁, o₁⟩ := q
      have w₁ := e₁.wb_right
      have p₁ : d₁.nreg 50107 = d.nreg 50107 := r₁ _ (by omega) (by omega) (by omega) (by omega)
      have n1₁ : d₁.nreg 50114 = n + 1 := (r₁ _ (by omega) (by omega) (by omega) (by omega)).trans hn1
      -- the doubling or the exit
      obtain ⟨d₂, k₂, e₂, hk₂, hp₂, r₂, m₂, rr₂, rm₂, o₂⟩ : ∃ d₂ k₂,
          Exec P W (.ifLtN 50116 50107 (.instr (.copyN 50107 50114))
            (.instr (.addN 50107 50107 50107))) d₁ d₂ k₂ ∧ k₂ ≤ 3 ∧
          (d₂.nreg 50107 = if n - d.nreg 50107 < d.nreg 50107 then n + 1
            else d.nreg 50107 + d.nreg 50107) ∧
          (∀ r, r ≠ 50107 → d₂.nreg r = d₁.nreg r) ∧ d₂.nmem = d₁.nmem ∧ d₂.rreg = d₁.rreg ∧
          d₂.rmem = d₁.rmem ∧ d₂.output = d₁.output := by
        by_cases hc : n - d.nreg 50107 < d.nreg 50107
        · obtain ⟨d₂, e₂, n₂, m₂, rr₂, rm₂, o₂⟩ := copyN_char (P := P) w₁ 50107 50114
          refine ⟨d₂, _, .ifLtN_true (by rw [s₁, p₁]; exact hc) e₂, by omega, ?_,
            fun r hr => by rw [n₂, Machine.upd_other _ _ _ hr], m₂, rr₂, rm₂, o₂⟩
          rw [n₂, Machine.upd_same, n1₁, ite_eq_left hc]
        · obtain ⟨d₂, e₂, n₂, m₂, rr₂, rm₂, o₂⟩ := addN_char (P := P) w₁ 50107 50107 50107
            (by rw [p₁]; omega)
          refine ⟨d₂, _, .ifLtN_false (by rw [s₁, p₁]; exact hc) e₂, by omega, ?_,
            fun r hr => by rw [n₂, Machine.upd_other _ _ _ hr], m₂, rr₂, rm₂, o₂⟩
          rw [n₂, Machine.upd_same, p₁, ite_eq_right hc]
      have R : ∀ r, r ≠ 50107 → r ≠ 50110 → r ≠ 50108 → r ≠ 9999 → r ≠ 50116 →
          d₂.nreg r = d.nreg r := fun r h1 h2 h3 h4 h5 => (r₂ r h1).trans (r₁ r h2 h3 h4 h5)
      have L₂ : d₂.nreg 50108 = d.nreg 50108 + 1 := (r₂ _ (by omega)).trans l₁
      have hsl : SLL A₀ d d₂ := ⟨fun r hb ha => by
          have := bandOf_loc hb
          exact R r (by omega) (by omega) (by omega) ha (by omega), rr₂.trans rr₁,
        fun x hx => by
          rw [m₂, m₁, Machine.upd_other _ _ _ (by omega)], rm₂.trans rm₁, o₂.trans o₁⟩
      refine ⟨d₂, _, .seq e₁ e₂, ?_, by rw [L₂]; omega, by
        show d₂.nreg 9999 ≤ d.nreg 9999 + (k₁ + k₂)
        rw [r₂ _ (by omega), a₁]; omega⟩
      exact
      { wb := e₂.wb_right, hJ := hJs d d₂ hd.hJ hsl.1 hsl.2.1 hsl.2.2.1 hsl.2.2.2.1 hsl.2.2.2.2,
        loc := hd.loc.sl hsl,
        rA := (R _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans hd.rA,
        rn := (R _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans hd.rn,
        pos0 := (R _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans hd.pos0,
        one := (R _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans hd.one,
        rT := (R _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans hd.rT,
        rn1 := (R _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans hn1,
        zero := (R _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans hd.zero,
        alloc := by
          show d₂.nreg 9999 = _
          rw [r₂ _ (by omega), a₁, L₂, show (9999 : ℕ) = ALLOC from rfl, hal]; omega,
        tab := fun j hj => by
          rw [L₂] at hj
          rw [m₂, m₁, Machine.upd_apply]
          by_cases hjj : j = d.nreg 50108
          · rw [ite_eq_left (by rw [hjj]), hjj, ← hp]
          · rw [ite_eq_right (by omega)]; exact hd.tab j (by omega),
        pow := fun h' => by
          rw [hp₂] at h' ⊢
          by_cases hc : n - d.nreg 50107 < d.nreg 50107
          · rw [ite_eq_left hc] at h'; omega
          · rw [ite_eq_right hc] at h' ⊢; rw [L₂, pow_succ, hp]; omega,
        big := fun h' => by
          rw [hp₂] at h'
          rw [L₂, pow_succ, ← hp]
          by_cases hc : n - d.nreg 50107 < d.nreg 50107
          · omega
          · rw [ite_eq_right hc] at h'; omega,
        pn1 := by
          rw [hp₂]
          by_cases hc : n - d.nreg 50107 < d.nreg 50107
          · rw [ite_eq_left hc]
          · rw [ite_eq_right hc]; omega,
        lb := Or.inr (by rw [L₂, Nat.add_sub_cancel, ← hp]; omega),
        bW := hbW, bn := hbn }) h
  have hL := tab_len_le I'.lb
  have hn1 := I'.rn1
  rw [hn1] at hex
  refine ⟨c', k, e, I', I'.big (by omega), by rw [hL0] at hk; omega, hψ⟩

end tab

/-! ## The binary lifting -/

section lift
variable {P : Polygon} {W : ℕ} {J : Config → Prop} {Bc : Finset ℕ} {A₀ : ℕ}

/-- **The invariant of the lifting loop**, relative to the entry configuration `c₀` and the
configuration `cT` after the table: the predicate holds below `pos`, fails at
`pos + 2 ^ i - 1` (if in range). -/
structure LiftInv (W : ℕ) (J : Config → Prop) (Bc : Finset ℕ) (A₀ : ℕ) (c₀ cT : Config)
    (pr : ℕ → Bool) (A n L : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  hJ : J c
  loc : LocL Bc A₀ c₀ c
  rA : c.nreg 50103 = A
  rn : c.nreg 50104 = n
  one : c.nreg 50106 = 1
  rT : c.nreg 50109 = A₀
  zero : c.nreg 50115 = 0
  mem : c.nmem = cT.nmem
  alloc : c.nreg ALLOC = cT.nreg ALLOC
  iL : c.nreg 50112 ≤ L
  posn : c.nreg 50105 ≤ n
  tab : ∀ j, j < L → cT.nmem (A₀ + j) = 2 ^ j
  bA : A + n ≤ A₀
  bT : A₀ + L ≤ W
  pre : ∀ j, j < c.nreg 50105 → pr (c₀.nmem (A + j)) = true
  post : c.nreg 50105 + 2 ^ c.nreg 50112 ≤ n →
    pr (c₀.nmem (A + (c.nreg 50105 + 2 ^ c.nreg 50112 - 1))) = false

variable {c₀ cT : Config} {pr : ℕ → Bool} {A n L : ℕ}

/-- **One lifting step** (cost `≤ κ + 13`). -/
theorem liftBody_inv {cmp : Stmt} {κ : ℕ} (hcmp : PredOK P W cmp Bc J pr κ)
    (hJs : JStableL J A₀) (hB : bLocate ∉ Bc)
    (hmono : ∀ i j, i ≤ j → j < n → pr (c₀.nmem (A + j)) = true → pr (c₀.nmem (A + i)) = true)
    {c : Config} (h : LiftInv W J Bc A₀ c₀ cT pr A n L c) (ht : c.nreg 50115 < c.nreg 50112) :
    ∃ c' k, Exec P W (liftBody cmp) c c' k ∧ LiftInv W J Bc A₀ c₀ cT pr A n L c' ∧
      k ≤ κ + 13 ∧ c'.nreg 50112 < c.nreg 50112 := by
  rw [h.zero] at ht
  have hiL := h.iL
  have hbT := h.bT
  have hbA := h.bA
  have hpn := h.posn
  set i := c.nreg 50112 with hi
  set pos := c.nreg 50105 with hpos
  have hstep : c.nmem (A₀ + (i - 1)) = 2 ^ (i - 1) := by rw [h.mem]; exact h.tab _ (by omega)
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.subN 50112 50112 50106,
      .addN 50110 50109 50112, .loadN 50111 50110, .subN 50116 50104 50105]) c c₁ k₁ ∧ k₁ = 4 ∧
      (c₁.nreg 50112 = i - 1 ∧ c₁.nreg 50111 = 2 ^ (i - 1) ∧ c₁.nreg 50116 = n - pos ∧
        (∀ r, r ≠ 50112 → r ≠ 50110 → r ≠ 50111 → r ≠ 50116 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    have hw := h.wb
    exec_block
    · config_simp; rw [h.rT, h.one]; omega
    · refine ⟨rfl, by config_simp; rw [h.one], by config_simp; rw [h.rT, h.one]; exact hstep,
        by config_simp; rw [h.rn], fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
      simp [h1, h2, h3, h4]
  obtain ⟨i₁, s₁, m₁, r₁, mm₁, rr₁, rm₁, o₁⟩ := q
  have w₁ := e₁.wb_right
  have sl₁ : SLL A₀ c c₁ := ⟨fun r hb _ => by
      have := bandOf_loc hb; exact r₁ r (by omega) (by omega) (by omega) (by omega), rr₁,
    fun x _ => by rw [mm₁], rm₁, o₁⟩
  have hJ₁ : J c₁ := hJs c c₁ h.hJ sl₁.1 sl₁.2.1 sl₁.2.2.1 sl₁.2.2.2.1 sl₁.2.2.2.2
  have pos₁ : c₁.nreg 50105 = pos := r₁ _ (by omega) (by omega) (by omega) (by omega)
  -- the common part of the new invariant
  have h2p : 0 < 2 ^ (i - 1) := Nat.two_pow_pos _
  have hpow : 2 ^ i = 2 ^ (i - 1) + 2 ^ (i - 1) := by
    rw [← two_mul, ← pow_succ']; congr 1; omega
  by_cases hc : n - pos < 2 ^ (i - 1)
  · -- no probe
    refine ⟨c₁, _, .seq e₁ (.ifLtN_true (by rw [m₁, s₁]; exact hc) (.skip w₁)), ?_, by omega,
      by rw [i₁]; omega⟩
    exact
    { wb := w₁, hJ := hJ₁, loc := h.loc.sl sl₁,
      rA := (r₁ _ (by omega) (by omega) (by omega) (by omega)).trans h.rA,
      rn := (r₁ _ (by omega) (by omega) (by omega) (by omega)).trans h.rn,
      one := (r₁ _ (by omega) (by omega) (by omega) (by omega)).trans h.one,
      rT := (r₁ _ (by omega) (by omega) (by omega) (by omega)).trans h.rT,
      zero := (r₁ _ (by omega) (by omega) (by omega) (by omega)).trans h.zero,
      mem := mm₁.trans h.mem,
      alloc := (r₁ _ (by decide) (by decide) (by decide) (by decide)).trans h.alloc,
      iL := by rw [i₁]; omega, posn := by rw [pos₁]; omega, tab := h.tab, bA := hbA, bT := hbT,
      pre := by rw [pos₁]; exact h.pre,
      post := by rw [pos₁, i₁]; intro h'; omega }
  · -- the probe
    have hle : pos + 2 ^ (i - 1) ≤ n := by omega
    obtain ⟨c₂, k₂, e₂, hk₂, q⟩ : ∃ c₂ k₂, Exec P W (block [.addN 50113 50105 50111,
        .subN 50110 50113 50106, .addN 50110 50103 50110, .loadN 50100 50110]) c₁ c₂ k₂ ∧
        k₂ = 4 ∧
        (c₂.nreg 50113 = pos + 2 ^ (i - 1) ∧
          c₂.nreg 50100 = c.nmem (A + (pos + 2 ^ (i - 1) - 1)) ∧
          (∀ r, r ≠ 50113 → r ≠ 50110 → r ≠ 50100 → c₂.nreg r = c₁.nreg r) ∧
          c₂.nmem = c₁.nmem ∧ c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output) := by
      exec_block
      · rw [pos₁, s₁]; omega
      · config_simp; rw [(r₁ _ (by omega) (by omega) (by omega) (by omega)).trans h.rA,
          (r₁ _ (by omega) (by omega) (by omega) (by omega)).trans h.one, pos₁, s₁]; omega
      · refine ⟨rfl, by config_simp; rw [pos₁, s₁], ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp
          rw [(r₁ _ (by omega) (by omega) (by omega) (by omega)).trans h.rA,
            (r₁ _ (by omega) (by omega) (by omega) (by omega)).trans h.one, pos₁, s₁, mm₁]
        · simp [h1, h2, h3]
    obtain ⟨t₂, x₂, r₂, mm₂, rr₂, rm₂, o₂⟩ := q
    have w₂ := e₂.wb_right
    have sl₂ : SLL A₀ c₁ c₂ := ⟨fun r hb _ => by
        have := bandOf_loc hb; exact r₂ r (by omega) (by omega) (by omega), rr₂,
      fun x _ => by rw [mm₂], rm₂, o₂⟩
    have hJ₂ : J c₂ := hJs c₁ c₂ hJ₁ sl₂.1 sl₂.2.1 sl₂.2.2.1 sl₂.2.2.2.1 sl₂.2.2.2.2
    -- the item read is the array entry
    have hx : c.nmem (A + (pos + 2 ^ (i - 1) - 1)) = c₀.nmem (A + (pos + 2 ^ (i - 1) - 1)) :=
      h.loc.2.2.1 _ (by omega)
    obtain ⟨c₃, k₃, e₃, hk₃, hJ₃, bit₃, r₃, rr₃, m₃, rm₃, o₃⟩ := hcmp c₂ w₂ hJ₂
    rw [x₂, hx] at bit₃
    have R₃ : ∀ r, bandOf r = bLocate → r ≠ 50100 → r ≠ 50101 → r ≠ 50102 →
        c₃.nreg r = c₂.nreg r := fun r hr h0 h1 h2 => r₃ r h0 h1 h2 (Or.inl (by rw [hr]; exact hB))
    have bl : ∀ r, 50000 ≤ r → r < 60000 → bandOf r = bLocate := fun r h1 h2 => by
      unfold bandOf bLocate; omega
    have loc₃ : LocL Bc A₀ c₀ c₃ := ((h.loc.sl sl₁).sl sl₂).cmp r₃ rr₃ m₃ rm₃ o₃
    -- registers after the comparator, in terms of `c`
    have K₃ : ∀ r, 50000 ≤ r → r < 60000 → r ≠ 50100 → r ≠ 50101 → r ≠ 50102 → r ≠ 50110 →
        r ≠ 50111 → r ≠ 50112 → r ≠ 50113 → r ≠ 50116 → c₃.nreg r = c.nreg r :=
      fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
        (R₃ r (bl r h1 h2) h3 h4 h5).trans ((r₂ r h9 h6 h3).trans (r₁ r h8 h6 h7 h10))
    have i₃ : c₃.nreg 50112 = i - 1 := by
      rw [R₃ _ (bl _ (by omega) (by omega)) (by omega) (by omega) (by omega),
        r₂ _ (by omega) (by omega) (by omega), i₁]
    have t₃ : c₃.nreg 50113 = pos + 2 ^ (i - 1) := by
      rw [R₃ _ (bl _ (by omega) (by omega)) (by omega) (by omega) (by omega), t₂]
    have al₃ : c₃.nreg ALLOC = c.nreg ALLOC := by
      rw [r₃ _ (by decide) (by decide) (by decide) (Or.inr rfl), r₂ _ (by decide) (by decide)
        (by decide), r₁ _ (by decide) (by decide) (by decide) (by decide)]
    have mem₃ : c₃.nmem = cT.nmem := by rw [m₃, mm₂, mm₁, h.mem]
    have one₃ : c₃.nreg 50106 = 1 :=
      (K₃ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)).trans h.one
    -- the common fields
    have base : ∀ c' : Config, WordsBounded W c' → J c' → LocL Bc A₀ c₀ c' →
        c'.nmem = cT.nmem → c'.nreg ALLOC = c.nreg ALLOC →
        (∀ r, 50000 ≤ r → r < 60000 → r ≠ 50100 → r ≠ 50101 → r ≠ 50102 → r ≠ 50105 →
          r ≠ 50110 → r ≠ 50111 → r ≠ 50112 → r ≠ 50113 → r ≠ 50116 → c'.nreg r = c.nreg r) →
        c'.nreg 50112 = i - 1 → c'.nreg 50105 ≤ n →
        (∀ j, j < c'.nreg 50105 → pr (c₀.nmem (A + j)) = true) →
        (c'.nreg 50105 + 2 ^ c'.nreg 50112 ≤ n →
          pr (c₀.nmem (A + (c'.nreg 50105 + 2 ^ c'.nreg 50112 - 1))) = false) →
        LiftInv W J Bc A₀ c₀ cT pr A n L c' :=
      fun c' hw hJ hl hm ha hr hi' hp hpre hpost =>
        { wb := hw, hJ := hJ, loc := hl,
          rA := (hr _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.rA,
          rn := (hr _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.rn,
          one := (hr _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.one,
          rT := (hr _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.rT,
          zero := (hr _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.zero,
          mem := hm, alloc := ha.trans h.alloc, iL := by rw [hi']; omega, posn := hp,
          tab := h.tab, bA := hbA, bT := hbT, pre := hpre, post := hpost }
    by_cases hp : pr (c₀.nmem (A + (pos + 2 ^ (i - 1) - 1))) = true
    · -- move
      rw [ite_eq_left hp] at bit₃
      obtain ⟨c₄, e₄, n₄, m₄, rr₄, rm₄, o₄⟩ := copyN_char (P := P) e₃.wb_right 50105 50113
      have R₄ : ∀ r, r ≠ 50105 → c₄.nreg r = c₃.nreg r := fun r hr => by
        rw [n₄, Machine.upd_other _ _ _ hr]
      have p₄ : c₄.nreg 50105 = pos + 2 ^ (i - 1) := by rw [n₄, Machine.upd_same, t₃]
      have sl₄ : SLL A₀ c₃ c₄ := ⟨fun r hb _ => by
          have := bandOf_loc hb; exact R₄ r (by omega), rr₄, fun x _ => by rw [m₄], rm₄, o₄⟩
      refine ⟨c₄, _, .seq e₁ (.ifLtN_false (by rw [m₁, s₁]; exact hc) (.seq e₂ (.seq e₃
        (.ifLtN_false (by rw [bit₃, one₃]; decide) e₄)))), ?_, by omega,
        by rw [R₄ _ (by omega), i₃]; omega⟩
      refine base c₄ e₄.wb_right (hJs c₃ c₄ hJ₃ sl₄.1 sl₄.2.1 sl₄.2.2.1 sl₄.2.2.2.1 sl₄.2.2.2.2)
        (loc₃.sl sl₄) (by rw [m₄, mem₃]) (by rw [R₄ _ (by decide), al₃])
        (fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 => (R₄ r h6).trans
          (K₃ r h1 h2 h3 h4 h5 h7 h8 h9 h10 h11))
        (by rw [R₄ _ (by omega), i₃]) (by rw [p₄]; exact hle) ?_ ?_
      · rw [p₄]
        intro j hj
        by_cases hj' : j < pos
        · exact h.pre j hj'
        · exact hmono j _ (by omega) (by omega) hp
      · rw [p₄, R₄ _ (by omega), i₃]
        intro h'
        have := h.post (show pos + 2 ^ i ≤ n by rw [hpow]; omega)
        rwa [show pos + 2 ^ (i - 1) + 2 ^ (i - 1) - 1 = pos + 2 ^ i - 1 by omega]
    · -- stay
      rw [ite_eq_right hp] at bit₃
      refine ⟨c₃, _, .seq e₁ (.ifLtN_false (by rw [m₁, s₁]; exact hc) (.seq e₂ (.seq e₃
        (.ifLtN_true (by rw [bit₃, one₃]; decide) (.skip e₃.wb_right))))), ?_, by omega,
        by rw [i₃]; omega⟩
      have p₃ : c₃.nreg 50105 = pos :=
        (K₃ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega))
      refine base c₃ e₃.wb_right hJ₃ loc₃ mem₃ al₃
        (fun r h1 h2 h3 h4 h5 _ h7 h8 h9 h10 h11 => K₃ r h1 h2 h3 h4 h5 h7 h8 h9 h10 h11)
        i₃ (by rw [p₃]; omega) (by rw [p₃]; exact h.pre) ?_
      rw [p₃, i₃]
      intro _
      simpa using hp

/-- **The lifting loop**: at the end `pos` is the partition point; cost `≤ (κ + 15) i + 2`. -/
theorem liftLoop_inv {cmp : Stmt} {κ : ℕ} (hcmp : PredOK P W cmp Bc J pr κ)
    (hJs : JStableL J A₀) (hB : bLocate ∉ Bc)
    (hmono : ∀ i j, i ≤ j → j < n → pr (c₀.nmem (A + j)) = true → pr (c₀.nmem (A + i)) = true)
    {c : Config} (h : LiftInv W J Bc A₀ c₀ cT pr A n L c) :
    ∃ c' k, Exec P W (liftLoop cmp) c c' k ∧ LiftInv W J Bc A₀ c₀ cT pr A n L c' ∧
      k ≤ (κ + 15) * c.nreg 50112 + 2 ∧
      (c'.nreg 50105 < n → pr (c₀.nmem (A + c'.nreg 50105)) = false) := by
  obtain ⟨c', k, e, I', hex, hk⟩ := Exec.whileLtN_bounded (a := 50115) (b := 50112)
    (LiftInv W J Bc A₀ c₀ cT pr A n L) (fun d => d.nreg 50112) (κ + 13) (fun _ h => h.wb)
    (fun d hd ht => by
      obtain ⟨d', k, e, I, hk, hi⟩ := liftBody_inv (P := P) hcmp hJs hB hmono hd ht
      exact ⟨d', k, e, I, hk, hi⟩) h
  refine ⟨c', k, e, I', hk, fun hlt => ?_⟩
  have hz := I'.zero
  rw [hz] at hex
  have := I'.post (by rw [show c'.nreg 50112 = 0 by omega, pow_zero]; omega)
  rwa [show c'.nreg 50112 = 0 by omega, pow_zero, Nat.add_sub_cancel] at this

end lift

/-! ## The search -/

/-- The cost bound dominates the cost of the phases. -/
theorem searchCost_ge (κ n : ℕ) :
    7 + (10 * (Nat.clog 2 n + 1) + 2) + 1 + ((κ + 15) * (Nat.clog 2 n + 1) + 2) ≤
      searchCost κ n := by
  unfold searchCost
  nlinarith

/-- **The search meets its specification** (at the level of executions).  From a word-bounded
configuration `c` satisfying `J`, with an array of `n = lr 104` items at `A = lr 103` below the
allocator, on which `pr` is monotone (true on a prefix), and room for `searchCost κ n` cells,
`searchStmt cmp` runs in at most `searchCost κ n` steps and leaves in `lr 105` the partition point
`t ≤ n`: `pr` holds at `A[j]` for `j < t` and fails at `A[t]` if `t < n`.  It keeps `J` and
respects `Frame (insert bLocate Bc)`. -/
theorem searchStmt_exec {P : Polygon} {W : ℕ} {cmp : Stmt} {Bc : Finset ℕ} {J : Config → Prop}
    {pr : ℕ → Bool} {κ : ℕ} (hcmp : PredOK P W cmp Bc J pr κ) (hB : bLocate ∉ Bc)
    {c : Config} (hw : WordsBounded W c) (hJ : J c) (hJs : JStableL J (c.nreg ALLOC))
    (hA : c.nreg 50103 + c.nreg 50104 ≤ c.nreg ALLOC)
    (hmono : ∀ i j, i ≤ j → j < c.nreg 50104 → pr (c.nmem (c.nreg 50103 + j)) = true →
      pr (c.nmem (c.nreg 50103 + i)) = true)
    (hroom : c.nreg ALLOC + searchCost κ (c.nreg 50104) ≤ W) :
    ∃ c' k, Exec P W (searchStmt cmp) c c' k ∧ k ≤ searchCost κ (c.nreg 50104) ∧ J c' ∧
      Frame (insert bLocate Bc) c c' k ∧ c'.nreg 50105 ≤ c.nreg 50104 ∧
      (∀ j, j < c'.nreg 50105 → pr (c.nmem (c.nreg 50103 + j)) = true) ∧
      (c'.nreg 50105 < c.nreg 50104 → pr (c.nmem (c.nreg 50103 + c'.nreg 50105)) = false) := by
  set A₀ := c.nreg ALLOC with hA₀
  set A := c.nreg 50103 with hAdef
  set n := c.nreg 50104 with hndef
  have hc0 : 37 * (Nat.clog 2 n + 1) ≤ searchCost κ n := by
    unfold searchCost; exact Nat.mul_le_mul_right _ (by omega)
  have hcost := searchCost_ge κ n
  -- initialisation
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W srchInit c c₁ k₁ ∧ k₁ = 7 ∧
      (c₁.nreg 50106 = 1 ∧ c₁.nreg 50107 = 1 ∧ c₁.nreg 50108 = 0 ∧ c₁.nreg 50109 = A₀ ∧
        c₁.nreg 50105 = 0 ∧ c₁.nreg 50114 = n + 1 ∧ c₁.nreg 50115 = 0 ∧
        (∀ r, r ≠ 50106 → r ≠ 50107 → r ≠ 50108 → r ≠ 50109 → r ≠ 50105 → r ≠ 50114 →
          r ≠ 50115 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    unfold srchInit
    exec_block
    · omega
    · omega
    · omega
    · omega
    · config_simp; omega
    · omega
    · refine ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp; rfl,
        by config_simp, by config_simp; rfl, by config_simp,
        fun r h1 h2 h3 h4 h5 h6 h7 => ?_, rfl, rfl, rfl, rfl⟩
      simp [h1, h2, h3, h4, h5, h6, h7]
  obtain ⟨o₁, p₁, l₁, t₁, s₁, n₁, z₁, r₁, m₁, rr₁, rm₁, out₁⟩ := q
  have sl₁ : SLL A₀ c c₁ := ⟨fun r hb _ => by
      have := bandOf_loc hb
      exact r₁ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    rr₁, fun x _ => by rw [m₁], rm₁, out₁⟩
  have T₁ : TabInv W J Bc A₀ c A n c₁ :=
    { wb := e₁.wb_right, hJ := hJs c c₁ hJ sl₁.1 sl₁.2.1 sl₁.2.2.1 sl₁.2.2.2.1 sl₁.2.2.2.2,
      loc := (LocL.refl Bc A₀ c).sl sl₁,
      rA := r₁ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      rn := r₁ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      pos0 := s₁, one := o₁, rT := t₁, rn1 := n₁, zero := z₁,
      alloc := by
        rw [l₁, r₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]; omega,
      tab := fun j hj => by rw [l₁] at hj; omega,
      pow := fun _ => by rw [p₁, l₁]; rfl, big := fun h' => by rw [l₁]; rw [p₁] at h'; simpa using h',
      pn1 := by rw [p₁]; omega, lb := Or.inl l₁, bW := by omega, bn := by omega }
  -- the table
  obtain ⟨c₂, k₂, e₂, T₂, hbig, hk₂, ha₂⟩ := tabLoop_inv (P := P) (hJs := hJs) T₁ l₁
  have hL := tab_len_le T₂.lb
  -- `i := L`
  obtain ⟨c₃, e₃, n₃, m₃, rr₃, rm₃, out₃⟩ := copyN_char (P := P) T₂.wb 50112 50108
  have R₃ : ∀ r, r ≠ 50112 → c₃.nreg r = c₂.nreg r := fun r hr => by
    rw [n₃, Machine.upd_other _ _ _ hr]
  have sl₃ : SLL A₀ c₂ c₃ := ⟨fun r hb _ => by
      have := bandOf_loc hb; exact R₃ r (by omega), rr₃, fun x _ => by rw [m₃], rm₃, out₃⟩
  have i₃ : c₃.nreg 50112 = c₂.nreg 50108 := by rw [n₃, Machine.upd_same]
  have I₃ : LiftInv W J Bc A₀ c c₃ pr A n (c₂.nreg 50108) c₃ :=
    { wb := e₃.wb_right, hJ := hJs c₂ c₃ T₂.hJ sl₃.1 sl₃.2.1 sl₃.2.2.1 sl₃.2.2.2.1 sl₃.2.2.2.2,
      loc := T₂.loc.sl sl₃, rA := (R₃ _ (by omega)).trans T₂.rA,
      rn := (R₃ _ (by omega)).trans T₂.rn, one := (R₃ _ (by omega)).trans T₂.one,
      rT := (R₃ _ (by omega)).trans T₂.rT, zero := (R₃ _ (by omega)).trans T₂.zero, mem := rfl,
      alloc := rfl, iL := by rw [i₃], posn := by rw [(R₃ _ (by omega)).trans T₂.pos0]; omega,
      tab := fun j hj => by rw [m₃]; exact T₂.tab j hj, bA := hA, bT := by omega,
      pre := fun j hj => by rw [(R₃ _ (by omega)).trans T₂.pos0] at hj; omega,
      post := fun h' => by
        rw [(R₃ _ (by omega)).trans T₂.pos0, i₃] at h'; omega }
  -- the lifting
  obtain ⟨c₄, k₄, e₄, I₄, hk₄, hfin⟩ := liftLoop_inv (P := P) hcmp hJs hB hmono I₃
  rw [i₃] at hk₄
  have loc₄ := I₄.loc
  have al₄ : c₄.nreg ALLOC = c₂.nreg ALLOC := by rw [I₄.alloc, R₃ _ (by decide)]
  have al₂ := T₂.alloc
  have al₁ := T₁.alloc
  refine ⟨c₄, _, .seq e₁ (.seq e₂ (.seq e₃ e₄)), ?_, I₄.hJ, ?_, I₄.posn, I₄.pre, hfin⟩
  · have : (κ + 15) * c₂.nreg 50108 ≤ (κ + 15) * (Nat.clog 2 n + 1) :=
      Nat.mul_le_mul_left _ hL
    omega
  · refine ⟨fun r hr ha => ?_, fun r hr => ?_, fun a ha => loc₄.2.2.1 a ha,
      fun a _ => by rw [loc₄.2.2.2.1], loc₄.2.2.2.2, by rw [al₄, al₂]; omega, ?_⟩
    · rw [Finset.mem_insert, not_or] at hr
      exact loc₄.1 r hr.2 hr.1 ha
    · rw [Finset.mem_insert, not_or] at hr
      exact loc₄.2.1 r hr.2
    · rw [al₄]
      have : c₁.nreg ALLOC = A₀ := by rw [al₁, l₁]; omega
      omega

end

end SearchR

end Chazelle.Core
