module

public import Chazelle.Core.ClusterPhase
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics
public import Chazelle.ChainTactics

/-!
# WP-I, part 21: map loops, parent arrays and binary-lifting tables

* `mapLoop`: a counted loop whose body stores the value `F j` at `bOut + j` (`F` a function
  fixed in advance, typically of the memory outside the written array) — the generic invariant,
  so that every array-producing loop needs only a lemma for its body;
* `parStmt`: the parent array `OUT[0] := 0`, `OUT[x] := VA[PA[x]]` for `1 ≤ x < n` (the parent
  vertex of a breadth-first tree from `0` whose parent darts are `PA` and tails `VA`);
* `upStmt`: the binary-lifting table `TAB[j n + x] = up^[2^j] x` (`j < L`, `x < n`) of
  `up x = PARENT[x]`.

Registers: `parStmt` `130500` (`VA`), `130501` (`PA`), `130502` (`OUT`), `130503` (`n`), scratch
`130504 … 130506`; `upStmt` `130510` (`PARENT`), `130511` (`TAB`), `130512` (`n`), `130513`
(`L`), scratch `130514 … 130519`.  Both read `130001 = 1`, `130009 = 0`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

section map

variable {P : Polygon} {W : ℕ}

/-- **Map loop.**  If from every configuration of the frame with counter `j < n` the body stores
`F j` at `bOut + j`, advances the counter and changes only registers in `Rg`, the loop stores
`F j` for all `j ∈ [j₀, n)`. -/
theorem mapLoop {ri rn : ℕ} {body : Stmt} {Rg : ℕ → Prop} (_hri : Rg ri) (hrn : ¬ Rg rn)
    {bOut n j₀ B : ℕ} (F : ℕ → ℕ) {c0 : Config} (hw0 : WordsBounded W c0)
    (hi0 : c0.nreg ri = j₀) (hn0 : c0.nreg rn = n) (hj₀ : j₀ ≤ n)
    (hbody : ∀ j c, j₀ ≤ j → j < n → WordsBounded W c → c.nreg ri = j →
      PFr Rg (fun a => bOut + j₀ ≤ a ∧ a < bOut + n) c0 c →
      ∃ c' k, Exec P W body c c' k ∧ k ≤ B ∧ c'.nreg ri = j + 1 ∧
        (∀ r, ¬ Rg r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
        c'.output = c.output ∧ c'.nmem = upd c.nmem (bOut + j) (F j)) :
    ∃ c' k, Exec P W (.whileLtN ri rn body) c0 c' k ∧ k ≤ (B + 2) * (n - j₀) + 2 ∧
      WordsBounded W c' ∧ c'.nreg ri = n ∧
      PFr Rg (fun a => bOut + j₀ ≤ a ∧ a < bOut + n) c0 c' ∧
      ∀ j, j₀ ≤ j → j < n → c'.nmem (bOut + j) = F j := by
  obtain ⟨c', k, e, hk, hw', hi', hn', hf', hI⟩ := forN (P := P) (W := W) (ri := ri) (rn := rn)
    (body := body)
    (fun j c => WordsBounded W c ∧ c.nreg ri = j ∧ c.nreg rn = n ∧
      PFr Rg (fun a => bOut + j₀ ≤ a ∧ a < bOut + n) c0 c ∧ j₀ ≤ j ∧
      ∀ i, j₀ ≤ i → i < j → c.nmem (bOut + i) = F i)
    n B (fun j c h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c hj ⟨hw, hi, hn, hf, hjj, hm⟩ => by
      obtain ⟨c', k, e, hk, hi', hr', hrr', hrm', ho', hm'⟩ := hbody j c hjj hj hw hi hf
      refine ⟨c', k, e, hk, e.wb_right, hi', by rw [hr' rn hrn, hn], ⟨fun r hr => ?_,
        hrr'.trans hf.2.1, hrm'.trans hf.2.2.1, ho'.trans hf.2.2.2.1, fun a ha => ?_⟩,
        by omega, fun i hi1 hi2 => ?_⟩
      · rw [hr' r hr]; exact hf.1 r hr
      · have hne : bOut + j ≠ a := fun h => ha (by sio only)
        rw [hm', Machine.upd_other _ _ _ hne.symm]
        exact hf.2.2.2.2 a ha
      · rw [hm', Machine.upd_apply]
        split_ifs with h
        · rw [show i = j by omega]
        · exact hm i hi1 (by omega))
    (j₀ := j₀) ⟨hw0, hi0, hn0, PFr.refl c0, le_rfl, fun i h1 h2 => by omega⟩ hj₀
  exact ⟨c', k, e, hk, hw', hi', hf', hI.2⟩

end map

/-! ## Parent arrays -/

/-- One vertex: `OUT[x] := VA[PA[x]]`, `x := x + 1`. -/
def parBody : Stmt := block [.addN 130505 130501 130504, .loadN 130506 130505,
  .addN 130505 130500 130506, .loadN 130506 130505, .addN 130505 130502 130504,
  .storeN 130505 130506, .addN 130504 130504 130001]

/-- **The parent array**: `OUT[0] := 0`, then `OUT[x] := VA[PA[x]]` for `1 ≤ x < n`. -/
def parStmt : Stmt := .seq (block [.storeN 130502 130009, .copyN 130504 130001])
  (.whileLtN 130504 130503 parBody)

/-- The scratch registers of `parStmt`. -/
def ParRG (r : ℕ) : Prop := 130504 ≤ r ∧ r ≤ 130506

section par

variable {P : Polygon} {W : ℕ}

/-- **The parent array.** -/
theorem parStmt_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    (hzero : c.nreg 130009 = 0) {bVA bPA bOut n : ℕ} (hVA : c.nreg 130500 = bVA)
    (hPA : c.nreg 130501 = bPA) (hOut : c.nreg 130502 = bOut) (hn : c.nreg 130503 = n)
    (hn1 : 1 ≤ n) (hwP : bPA + n ≤ W) (hwO : bOut + n ≤ W)
    (hdP : bOut + n ≤ bPA ∨ bPA + n ≤ bOut)
    (hVAw : ∀ x, 1 ≤ x → x < n → bVA + c.nmem (bPA + x) ≤ W ∧
      (bVA + c.nmem (bPA + x) < bOut ∨ bOut + n ≤ bVA + c.nmem (bPA + x))) :
    ∃ c' k, Exec P W parStmt c c' k ∧ k ≤ 9 * n + 4 ∧ WordsBounded W c' ∧
      PFr ParRG (fun a => bOut ≤ a ∧ a < bOut + n) c c' ∧ c'.nmem bOut = 0 ∧
      ∀ x, 1 ≤ x → x < n → c'.nmem (bOut + x) = c.nmem (bVA + c.nmem (bPA + x)) := by
  obtain ⟨c1, k1, e1, hk1, hw1, h1m, h1r, h1c, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      (block [.storeN 130502 130009, .copyN 130504 130001]) c c1 k1 ∧ k1 = 2 ∧
      WordsBounded W c1 ∧ c1.nmem = upd c.nmem bOut 0 ∧
      (∀ r, r ≠ 130504 → c1.nreg r = c.nreg r) ∧ c1.nreg 130504 = 1 ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    refine ⟨rfl, ‹_›, by config_simp; rw [hOut, hzero], fun r hr => ?_, by config_simp; exact hone,
      rfl, rfl, rfl⟩
    simp only [Machine.upd_apply, hr, ite_false]
  have hmem1 : ∀ a, a ≠ bOut → c1.nmem a = c.nmem a := by
    intro a ha; rw [h1m, Machine.upd_other _ _ _ ha]
  obtain ⟨c', k, e, hk, hw', -, hf', hI⟩ := mapLoop (P := P) (W := W) (ri := 130504)
    (rn := 130503) (body := parBody) (Rg := ParRG) (by ufo ParRG)
    (by ufo ParRG) (bOut := bOut) (n := n) (j₀ := 1) (B := 7)
    (fun x => c.nmem (bVA + c.nmem (bPA + x))) hw1 h1c
    (by rwx [h1r _ (by omega)]) hn1
    (fun j c2 hj1 hjn hw2 hi2 hf2 => by
      have r0 : ∀ r, ¬ ParRG r → c2.nreg r = c.nreg r := fun r hr =>
        (hf2.1 r hr).trans (h1r r (fun h => hr (by ruo [h] ParRG)))
      have rVA := (r0 130500 (by ufo ParRG)).trans hVA
      have rPA := (r0 130501 (by ufo ParRG)).trans hPA
      have rO := (r0 130502 (by ufo ParRG)).trans hOut
      have r1 := (r0 130001 (by ufo ParRG)).trans hone
      have m0 : ∀ a, ¬ (bOut + 1 ≤ a ∧ a < bOut + n) → a ≠ bOut → c2.nmem a = c.nmem a :=
        fun a h1 h2 => (hf2.2.2.2.2 a h1).trans (hmem1 a h2)
      have mP : c2.nmem (bPA + j) = c.nmem (bPA + j) := m0 _ (by omega) (by omega)
      obtain ⟨hwv, hdv⟩ := hVAw j hj1 hjn
      have mV : c2.nmem (bVA + c.nmem (bPA + j)) = c.nmem (bVA + c.nmem (bPA + j)) :=
        m0 _ (by omega) (by omega)
      unfold parBody
      exec_block
      · rwo [rPA, hi2]
      · config_simp; rwx [rVA, rPA, hi2, mP]
      · config_simp; rwo [rO, hi2]
      · config_simp; rwo [hi2, r1]
      · refine ⟨le_refl _, by config_simp; rw [hi2, r1], fun r hr => ?_, rfl, rfl, rfl, ?_⟩
        · simp only [Machine.upd_apply]; unfold ParRG at hr; splao
        · config_simp
          rw [rO, hi2, rVA, rPA, mP, mV])
  subst hk1
  refine ⟨c', 2 + k, .seq e1 e, by omega, hw', ⟨fun r hr => ?_, hf'.2.1.trans hrr1,
    hf'.2.2.1.trans hrm1, hf'.2.2.2.1.trans ho1, fun a ha => ?_⟩, ?_, fun x hx1 hxn => ?_⟩
  · rw [hf'.1 r hr]; exact h1r r (fun h => hr (by ruo [h] ParRG))
  · rw [hf'.2.2.2.2 a (by omega)]; exact hmem1 a (by omega)
  · rw [hf'.2.2.2.2 bOut (by omega), h1m, Machine.upd_same]
  · exact hI x hx1 hxn

end par

/-! ## Binary-lifting tables -/

/-- Row `0`, one cell: `TAB[x] := PARENT[x]`. -/
def row0Body : Stmt := block [.addN 130518 130510 130517, .loadN 130519 130518,
  .addN 130518 130511 130517, .storeN 130518 130519, .addN 130517 130517 130001]

/-- Row `j`, one cell: `TAB[j n + x] := TAB[(j-1) n + TAB[(j-1) n + x]]` (`130515` holds the base
of row `j - 1`, `130516` that of row `j`). -/
def cellBody : Stmt := block [.addN 130518 130515 130517, .loadN 130519 130518,
  .addN 130518 130515 130519, .loadN 130519 130518, .addN 130518 130516 130517,
  .storeN 130518 130519, .addN 130517 130517 130001]

/-- One row. -/
def rowBody : Stmt := .seq (.instr (.constN 130517 0)) (.seq (.whileLtN 130517 130512 cellBody)
  (block [.copyN 130515 130516, .addN 130516 130516 130512, .addN 130514 130514 130001]))

/-- **The binary-lifting table** of the parent array `PARENT`. -/
def upStmt : Stmt := .seq (.instr (.constN 130517 0)) (.seq (.whileLtN 130517 130512 row0Body)
  (.seq (block [.copyN 130515 130511, .addN 130516 130511 130512, .copyN 130514 130001])
    (.whileLtN 130514 130513 rowBody)))

/-- The scratch registers of `upStmt`. -/
def UpRG (r : ℕ) : Prop := 130514 ≤ r ∧ r ≤ 130519

section up

variable {P : Polygon} {W : ℕ}

/-- The registers of the cell loops. -/
def CellRG (r : ℕ) : Prop := 130517 ≤ r ∧ r ≤ 130519

/-- **One row of the table.** -/
theorem rowBody_exec {c0 c4 : Config} (hw4 : WordsBounded W c4) {bT n L j : ℕ}
    (up : ℕ → ℕ) (hupl : ∀ m x, x < n → up^[m] x < n)
    (hone : c4.nreg 130001 = 1) (hn : c4.nreg 130512 = n) (hj4 : c4.nreg 130514 = j)
    (h4a : c4.nreg 130515 = bT + (j - 1) * n) (h4b : c4.nreg 130516 = bT + j * n)
    (hj1 : 1 ≤ j) (hjL : j < L) (hwT : bT + L * n ≤ W) (hLW : L + 1 ≤ W) (hn1 : 1 ≤ n)
    (hf4 : PFr UpRG (fun a => bT ≤ a ∧ a < bT + L * n) c0 c4)
    (hI4 : ∀ i, i < j → ∀ x, x < n → c4.nmem (bT + i * n + x) = up^[2 ^ i] x) :
    ∃ c5 k, Exec P W rowBody c4 c5 k ∧ k ≤ 12 * n + 5 ∧ WordsBounded W c5 ∧
      c5.nreg 130514 = j + 1 ∧ c5.nreg 130515 = bT + (j + 1 - 1) * n ∧
      c5.nreg 130516 = bT + (j + 1) * n ∧
      PFr UpRG (fun a => bT ≤ a ∧ a < bT + L * n) c0 c5 ∧
      ∀ i, i < j + 1 → ∀ x, x < n → c5.nmem (bT + i * n + x) = up^[2 ^ i] x := by
  have hjn : (j - 1) * n + n = j * n := by
    rw [← Nat.succ_mul]; congr 1; omega
  have hjLn : j * n + n ≤ L * n := by
    have := Nat.mul_le_mul_right n (show j + 1 ≤ L by omega)
    rwa [Nat.succ_mul] at this
  have e0 := Exec.constN (P := P) hw4 130517 0 (by omega)
  set c5 := { c4 with nreg := upd c4.nreg 130517 0 }
  have hf5 : PFr CellRG (fun a => bT + j * n + 0 ≤ a ∧ a < bT + j * n + n) c4 c5 :=
    PFr.nreg (PFr.refl c4) (fun r hr => by
      simp only [Machine.upd_apply]; unfold CellRG at hr; splao)
  obtain ⟨c6, k6, e6, hk6, hw6, hi6, hf6, hI6⟩ := mapLoop (P := P) (W := W) (ri := 130517)
    (rn := 130512) (body := cellBody) (Rg := CellRG) (by ufo CellRG)
    (by ufo CellRG) (bOut := bT + j * n) (n := n) (j₀ := 0) (B := 7)
    (fun x => up^[2 ^ j] x) e0.wb_right (by simp [c5]) (by simp [c5, hn]) (Nat.zero_le _)
    (fun x c7 _ hxn hw7 hi7 hf7 => by
      have hf57 := hf5.trans hf7
      have r0  := hf57.1
      have ra := (r0 130515 (by ufo CellRG)).trans h4a
      have rb := (r0 130516 (by ufo CellRG)).trans h4b
      have r1 := (r0 130001 (by ufo CellRG)).trans hone
      have hx1 : c7.nmem (bT + (j - 1) * n + x) = up^[2 ^ (j - 1)] x := by
        rw [hf57.2.2.2.2 _ (by omega)]; exact hI4 (j - 1) (by omega) x hxn
      set y := up^[2 ^ (j - 1)] x
      have hyn : y < n := hupl _ x hxn
      have hx2 : c7.nmem (bT + (j - 1) * n + y) = up^[2 ^ (j - 1)] y := by
        rw [hf57.2.2.2.2 _ (by omega)]; exact hI4 (j - 1) (by omega) y hyn
      have hval : up^[2 ^ (j - 1)] y = up^[2 ^ j] x := by
        simp only [y]
        rw [← Function.iterate_add_apply]
        congr 1
        rw [← two_mul, ← pow_succ']
        congr 1; omega
      unfold cellBody
      exec_block
      · rwo [ra, hi7]
      · config_simp; rwo [ra, hi7, hx1]
      · config_simp; rwo [rb, hi7]
      · config_simp; rwo [hi7, r1]
      · refine ⟨le_refl _, by config_simp; rw [hi7, r1], fun r hr => ?_, rfl, rfl, rfl, ?_⟩
        · simp only [Machine.upd_apply]; unfold CellRG at hr; splao
        · config_simp
          rw [rb, hi7, ra, hx1, hx2, hval])
  have hf46 := hf5.trans hf6
  have r6  := hf46.1
  have rn6 := (r6 130512 (by ufo CellRG)).trans hn
  have rj6 := (r6 130514 (by ufo CellRG)).trans hj4
  have rb6 := (r6 130516 (by ufo CellRG)).trans h4b
  have r16 := (r6 130001 (by ufo CellRG)).trans hone
  obtain ⟨c7, k7, e7, hk7, hw7, h7a, h7b, h7j, h7r, hrr7, hrm7, ho7, hm7⟩ : ∃ c7 k7, Exec P W
      (block [.copyN 130515 130516, .addN 130516 130516 130512, .addN 130514 130514 130001])
      c6 c7 k7 ∧ k7 = 3 ∧ WordsBounded W c7 ∧ c7.nreg 130515 = bT + j * n ∧
      c7.nreg 130516 = bT + (j + 1) * n ∧ c7.nreg 130514 = j + 1 ∧
      (∀ r, r ≠ 130514 → r ≠ 130515 → r ≠ 130516 → c7.nreg r = c6.nreg r) ∧
      c7.rreg = c6.rreg ∧ c7.rmem = c6.rmem ∧ c7.output = c6.output ∧ c7.nmem = c6.nmem := by
    exec_block
    all_goals first
      | (config_simp; rwo [rb6, rn6])
      | (config_simp; rwo [rj6, r16])
      | skip
    · refine ⟨rfl, ‹_›, by config_simp; exact rb6, by config_simp; rwo [rb6, rn6, Nat.succ_mul],
        by config_simp; rw [rj6, r16], fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
      simp only [Machine.upd_apply, h1, h2, h3, ite_false]
  subst hk7
  refine ⟨c7, 1 + (k6 + 3), .seq e0 (.seq e6 e7), by omega, hw7, h7j,
    by rws [h7a], h7b, ⟨fun r hr => ?_, ?_, ?_, ?_, fun a ha => ?_⟩, fun i hi x hx => ?_⟩
  · rw [h7r r (by ufo UpRG at hr) (by ufo UpRG at hr)
      (by ufo UpRG at hr), r6 r (by ufo CellRG UpRG at *)]
    exact hf4.1 r hr
  · rw [hrr7, hf46.2.1, hf4.2.1]
  · rw [hrm7, hf46.2.2.1, hf4.2.2.1]
  · rw [ho7, hf46.2.2.2.1, hf4.2.2.2.1]
  · rw [hm7, hf46.2.2.2.2 a (by sio only at ha ⊢)]; exact hf4.2.2.2.2 a ha
  · rw [hm7]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have hle : i * n + n ≤ j * n := by
        have := Nat.mul_le_mul_right n (show i + 1 ≤ j by omega)
        rwa [Nat.succ_mul] at this
      rw [hf46.2.2.2.2 _ (by sio only)]
      exact hI4 i hi x hx
    · have := hI6 x (Nat.zero_le _) hx
      exact this

/-- **The binary-lifting table**: `TAB[j n + x] = up^[2^j] x` for `j < L`, `x < n`, where
`up x = PARENT[x]` maps `[0, n)` into itself; cost `≤ 12 n L + 7 L + 12`. -/
theorem upStmt_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    {bPa bT n L : ℕ} (hPa : c.nreg 130510 = bPa) (hT : c.nreg 130511 = bT)
    (hn : c.nreg 130512 = n) (hL : c.nreg 130513 = L) (hL1 : 1 ≤ L)
    (hup : ∀ x, x < n → c.nmem (bPa + x) < n) (hwPa : bPa + n ≤ W) (hwT : bT + L * n ≤ W)
    (hd : bPa + n ≤ bT ∨ bT + L * n ≤ bPa) (hLW : L + 1 ≤ W) (hn1 : 1 ≤ n) :
    ∃ c' k, Exec P W upStmt c c' k ∧ k ≤ 12 * n * L + 7 * L + 12 ∧ WordsBounded W c' ∧
      PFr UpRG (fun a => bT ≤ a ∧ a < bT + L * n) c c' ∧
      ∀ j, j < L → ∀ x, x < n →
        c'.nmem (bT + j * n + x) = (fun y => c.nmem (bPa + y))^[2 ^ j] x := by
  set up : ℕ → ℕ := fun y => c.nmem (bPa + y) with hupdef
  have hupl : ∀ m x, x < n → up^[m] x < n := by
    intro m; induction m with
    | zero => intro x hx; exact hx
    | succ m ih => intro x hx; rw [Function.iterate_succ_apply]; exact ih _ (hup x hx)
  have hLn : n ≤ L * n := Nat.le_mul_of_pos_left n (by omega)
  -- row 0
  have e0 := Exec.constN (P := P) hw 130517 0 (by omega)
  set c1 := { c with nreg := upd c.nreg 130517 0 }
  have hf1 : PFr UpRG (fun a => bT ≤ a ∧ a < bT + L * n) c c1 :=
    PFr.nreg (PFr.refl c) (fun r hr => by
      simp only [Machine.upd_apply]; unfold UpRG at hr; splao)
  obtain ⟨c2, k2, e2, hk2, hw2, -, hf2, hI2⟩ := mapLoop (P := P) (W := W) (ri := 130517)
    (rn := 130512) (body := row0Body) (Rg := UpRG) (by ufo UpRG)
    (by ufo UpRG) (bOut := bT) (n := n) (j₀ := 0) (B := 5) up e0.wb_right
    (by simp only [c1, Machine.upd_same])
    (by simp only [c1]; rwx [Machine.upd_other _ _ _ (by omega)]) (Nat.zero_le _)
    (fun j c3 _ hjn hw3 hi3 hf3 => by
      have r0 : ∀ r, ¬ UpRG r → c3.nreg r = c.nreg r := fun r hr =>
        (hf3.1 r hr).trans (hf1.1 r hr)
      have rPa := (r0 130510 (by ufo UpRG)).trans hPa
      have rT := (r0 130511 (by ufo UpRG)).trans hT
      have r1 := (r0 130001 (by ufo UpRG)).trans hone
      have mP : c3.nmem (bPa + j) = c.nmem (bPa + j) :=
        (hf3.2.2.2.2 _ (by sio only)).trans (hf1.2.2.2.2 _ (by omega))
      unfold row0Body
      exec_block
      · rwo [rPa, hi3]
      · config_simp; rwo [rT, hi3]
      · config_simp; rwo [hi3, r1]
      · refine ⟨le_refl _, by config_simp; rw [hi3, r1], fun r hr => ?_, rfl, rfl, rfl, ?_⟩
        · simp only [Machine.upd_apply]; unfold UpRG at hr; splao
        · config_simp; rw [rT, hi3, rPa, mP])
  have hf12 : PFr UpRG (fun a => bT ≤ a ∧ a < bT + L * n) c c2 :=
    hf1.trans (hf2.mono (fun _ => id) (fun a ha => by
      obtain ⟨h1, h2⟩ := ha; exact ⟨by omega, by omega⟩))
  -- the row setup
  have hr2  := hf12.1
  have rT2 := (hr2 130511 (by ufo UpRG)).trans hT
  have rn2 := (hr2 130512 (by ufo UpRG)).trans hn
  have r12 := (hr2 130001 (by ufo UpRG)).trans hone
  obtain ⟨c3, k3, e3, hk3, hw3, h3a, h3b, h3j, h3r, hrr3, hrm3, ho3, hm3⟩ : ∃ c3 k3, Exec P W
      (block [.copyN 130515 130511, .addN 130516 130511 130512, .copyN 130514 130001]) c2 c3 k3 ∧
      k3 = 3 ∧ WordsBounded W c3 ∧ c3.nreg 130515 = bT ∧ c3.nreg 130516 = bT + n ∧
      c3.nreg 130514 = 1 ∧ (∀ r, r ≠ 130514 → r ≠ 130515 → r ≠ 130516 → c3.nreg r = c2.nreg r) ∧
      c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output ∧ c3.nmem = c2.nmem := by
    exec_block
    all_goals first
      | (config_simp; rwo [rT2, rn2])
      | skip
    · refine ⟨rfl, ‹_›, by config_simp; exact rT2, by config_simp; rw [rT2, rn2], by
        config_simp; exact r12, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
      simp only [Machine.upd_apply, h1, h2, h3, ite_false]
  have hf3 : PFr UpRG (fun a => bT ≤ a ∧ a < bT + L * n) c c3 :=
    ⟨fun r hr => (h3r r (by ufo UpRG at hr) (by ufo UpRG at hr)
      (by ufo UpRG at hr)).trans (hf12.1 r hr), hrr3.trans hf12.2.1,
      hrm3.trans hf12.2.2.1, ho3.trans hf12.2.2.2.1, fun a ha => by rw [hm3]; exact hf12.2.2.2.2 a ha⟩
  -- the rows
  obtain ⟨c', k, e, hk, hw', -, -, -, -, hf', -, hrows⟩ := forN (P := P) (W := W)
    (ri := 130514) (rn := 130513) (body := rowBody)
    (fun j c4 => WordsBounded W c4 ∧ c4.nreg 130514 = j ∧ c4.nreg 130513 = L ∧
      c4.nreg 130515 = bT + (j - 1) * n ∧ c4.nreg 130516 = bT + j * n ∧
      PFr UpRG (fun a => bT ≤ a ∧ a < bT + L * n) c c4 ∧ 1 ≤ j ∧
      ∀ i, i < j → ∀ x, x < n → c4.nmem (bT + i * n + x) = up^[2 ^ i] x)
    L (12 * n + 5) (fun j c4 h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c4 hjL ⟨hw4, hj4, hL4, h4a, h4b, hf4, hj1, hI4⟩ => by
      have r0  := hf4.1
      have rn := (r0 130512 (by ufo UpRG)).trans hn
      have r1 := (r0 130001 (by ufo UpRG)).trans hone
      obtain ⟨c5, k5, e5, hk5, hw5, h5j, h5a, h5b, hf5, hI5⟩ := rowBody_exec (P := P) hw4 up hupl
        r1 rn hj4 h4a h4b hj1 hjL hwT hLW hn1 hf4 hI4
      exact ⟨c5, k5, e5, hk5, hw5, h5j, by rw [hf5.1 _ (by ufo UpRG), hL], h5a, h5b,
        hf5, by omega, hI5⟩)
    (j₀ := 1) ⟨hw3, h3j, by rw [h3r _ (by omega) (by omega) (by omega),
      hr2 _ (by ufo UpRG), hL],
      by rws [h3a], by rws [h3b], hf3, le_rfl, fun i hi x hx => by
        have : i = 0 := by omega
        subst this
        rw [hm3, Nat.zero_mul, add_zero, hI2 x (Nat.zero_le _) hx]
        simp⟩ hL1
  subst hk3
  refine ⟨c', 1 + (k2 + (3 + k)), .seq e0 (.seq e2 (.seq e3 e)), ?_, hw', hf', hrows⟩
  have hLm : (12 * n + 5 + 2) * (L - 1) + (12 * n + 7) = 12 * n * L + 7 * L := by
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    sir only [Nat.add_sub_cancel]
  omega

end up

end

end Chazelle.Core.Cluster
