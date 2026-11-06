module

public import Chazelle.Core.OracleAtFacts

/-!
# Lemma 3.6 (WP-H), RAM part 17: loading the constants of the query

`qLoad` reads the structure at `O` (register `120000`), its chain descriptor and normal form,
the query origin (`120001 … 120003`) and the direction (`120004`) into the constant registers
`120010 … 120049` of the query (`QConst`).  Main result: `qLoad_exec`.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ

@[expose] public section

/-- The small constants, and the words at `O`, `O + 1`, `O + 4 … O + 17`. -/
def qLoadA : Stmt :=
  block [.inputSize 120010, .constN 120011 1, .constN 120012 0, .constN 120048 2,
    .constN 120028 6, .copyN 120190 120000, .loadN 120013 120190, .addN 120190 120190 120011,
    .loadN 120014 120190, .addN 120190 120190 120011, .addN 120190 120190 120011,
    .addN 120190 120190 120011, .loadN 120030 120190, .addN 120190 120190 120011,
    .loadN 120031 120190, .addN 120190 120190 120011, .loadN 120032 120190,
    .addN 120190 120190 120011, .loadN 120033 120190, .addN 120190 120190 120011,
    .loadN 120034 120190, .addN 120190 120190 120011, .loadN 120035 120190,
    .addN 120190 120190 120011, .loadN 120036 120190, .addN 120190 120190 120011,
    .loadN 120037 120190, .addN 120190 120190 120011, .loadN 120038 120190,
    .addN 120190 120190 120011, .loadN 120039 120190, .addN 120190 120190 120011,
    .loadN 120040 120190, .addN 120190 120190 120011, .loadN 120041 120190,
    .addN 120190 120190 120011, .loadN 120042 120190, .addN 120190 120190 120011,
    .loadN 120049 120190]

/-- The chain descriptor and the areas of the normal form. -/
def qLoadB : Stmt :=
  block [.copyN 120190 120013, .addN 120190 120190 120011, .loadN 120015 120190,
    .addN 120190 120190 120011, .loadN 120016 120190, .addN 120190 120190 120011,
    .loadN 120017 120190, .addN 120190 120190 120011, .loadN 120018 120190,
    .addN 120019 120016 120016, .constN 120191 7, .addN 120020 120019 120191,
    .constN 120191 6, .addN 120029 120019 120191, .constN 120191 3,
    .addN 120190 120014 120191, .loadN 120043 120190, .addN 120190 120190 120011,
    .loadN 120044 120190, .addN 120190 120190 120011, .loadN 120045 120190,
    .addN 120190 120190 120011, .loadN 120046 120190, .addN 120190 120190 120011,
    .loadN 120047 120190]

/-- The derived constants: `sideS`, the top vertex, the height vertex, the direction bit, the
origin. -/
def qLoadC : Stmt :=
  .seq (ifEq 120018 120011 (.instr (.copyN 120021 120017)) (.instr (.subN 120021 120019 120017)))
    (.seq (.instr (.addN 120022 120015 120017))
      (.seq (modSub 120022 120010)
        (.seq (ifEq 120001 120011 (.instr (.copyN 120023 120003)) (.instr (.copyN 120023 120002)))
          (.seq (ifEq 120004 120011 (.instr (.constN 120024 1)) (.instr (.constN 120024 0)))
            (block [.copyN 120025 120001, .copyN 120026 120002, .copyN 120027 120003])))))

/-- **Loading the constants of the query.** -/
def qLoad : Stmt := .seq qLoadA (.seq qLoadB qLoadC)

/-- The registers written by `qLoad`. -/
def BLd (r : ℕ) : Bool := decide (120010 ≤ r ∧ r ≤ 120049) || decide (120190 ≤ r ∧ r ≤ 120191)

theorem wr_qLoad : wr BLd qLoad = true := by decide

/-- The values loaded by `qLoadA`. -/
theorem qLoadA_exec {P : Polygon} {W : ℕ} {m : ℕ → ℕ} {O E : ℕ} {V : QV} {H : Host} {C : Chain}
    {N : NF} {B : OracleBook.BookData} {k : ℕ} (hA : QAt P m O E V H C N B k) (hEW : E ≤ W)
    (c : Config) (hw : WordsBounded W c) (hm : c.nmem = m) (hO : c.nreg 120000 = O)
    (hW : P.n + 8 ≤ W) :
    ∃ c' k, Exec P W qLoadA c c' k ∧ k = 39 ∧
      c'.nreg 120010 = P.n ∧ c'.nreg 120011 = 1 ∧ c'.nreg 120012 = 0 ∧ c'.nreg 120048 = 2 ∧
      c'.nreg 120028 = 6 ∧ c'.nreg 120013 = V.D ∧ c'.nreg 120014 = V.NB ∧
      c'.nreg 120030 = V.A ∧ c'.nreg 120031 = V.POS ∧ c'.nreg 120032 = V.FL ∧
      c'.nreg 120033 = V.LAB ∧ c'.nreg 120034 = V.DL ∧ c'.nreg 120035 = V.nD ∧
      c'.nreg 120036 = V.ORD ∧ c'.nreg 120037 = V.RK ∧ c'.nreg 120038 = V.CH ∧
      c'.nreg 120039 = V.K ∧ c'.nreg 120040 = V.MD ∧ c'.nreg 120041 = V.TB ∧
      c'.nreg 120042 = V.L ∧ c'.nreg 120049 = V.μ := by
  have hOE := hA.O_le
  unfold qLoadA
  exec_block
  all_goals (config_simp; (try simp only [hO, hm, Nat.add_assoc] at *); (try norm_num); (try omega))
  exact ⟨hA.lD, hA.lNB, hA.lA, hA.lPOS, hA.lFL, hA.lLAB, hA.lDL, hA.lnD, hA.lORD, hA.lRK, hA.lCH,
    hA.lK, hA.lMD, hA.lTB, hA.lL, hA.lμ⟩

/-- The registers written by `qLoadB`. -/
def BLdB (r : ℕ) : Bool :=
  decide (120015 ≤ r ∧ r ≤ 120020) || decide (r = 120029) || decide (120043 ≤ r ∧ r ≤ 120047) ||
    decide (120190 ≤ r ∧ r ≤ 120191)

theorem wr_qLoadB : wr BLdB qLoadB = true := by decide

/-- The values loaded by `qLoadB`. -/
theorem qLoadB_exec {P : Polygon} {W : ℕ} {m : ℕ → ℕ} {O E : ℕ} {V : QV} {H : Host} {C : Chain}
    {N : NF} {B : OracleBook.BookData} {k : ℕ} (hA : QAt P m O E V H C N B k) (hEW : E ≤ W)
    (c : Config) (hw : WordsBounded W c) (hm : c.nmem = m) (h11 : c.nreg 120011 = 1)
    (h13 : c.nreg 120013 = V.D) (h14 : c.nreg 120014 = V.NB) (hmW : 2 * V.m + 7 ≤ W) :
    ∃ c' k, Exec P W qLoadB c c' k ∧ k = 25 ∧
      c'.nreg 120015 = V.s ∧ c'.nreg 120016 = V.m ∧ c'.nreg 120017 = V.tIdx ∧
      c'.nreg 120018 = V.β ∧ c'.nreg 120019 = 2 * V.m ∧ c'.nreg 120020 = 2 * V.m + 7 ∧
      c'.nreg 120029 = 2 * V.m + 6 ∧ c'.nreg 120043 = V.CB ∧ c'.nreg 120044 = V.AB ∧
      c'.nreg 120045 = V.RB ∧ c'.nreg 120046 = V.SB ∧ c'.nreg 120047 = V.LB := by
  have hD := hA.D_le
  have hNB := hA.NB_TB
  have hTB := hA.TB_le
  unfold qLoadB
  exec_block
  all_goals (config_simp; (try simp only [h11, h13, h14, hm, hA.dm, Nat.add_assoc] at *); (try norm_num); (try omega))
  exact ⟨hA.ds, hA.dt, hA.dβ, by ring, hA.nCB, hA.nAB, hA.nRB, hA.nSB, hA.nLB⟩

/-- The height vertex of a query origin. -/
def qhzOf : QOrigin → ℕ
  | .sym (.vtx i) => i
  | .sym (.onEdge _ h) => h
  | .box h => h

/-- The origin data of a query origin (`none`: a box origin). -/
noncomputable def qzoOf (Q : Polygon) : QOrigin → Option Point
  | .sym p => some (p.eval Q)
  | .box _ => none

/-- The direction bit of a direction word. -/
def σbOf (v : ℕ) : ℕ := if v = 1 then 1 else 0

/-- The registers written by `qLoadC`. -/
def BLdC (r : ℕ) : Bool := decide (120021 ≤ r ∧ r ≤ 120027)

theorem wr_qLoadC : wr BLdC qLoadC = true := by decide

/-- The derived constants of `qLoadC`. -/
theorem qLoadC_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {n s m t β : ℕ}
    (hn : c.nreg 120010 = n) (h11 : c.nreg 120011 = 1) (hs : c.nreg 120015 = s)
    (ht : c.nreg 120017 = t) (hβ : c.nreg 120018 = β) (h19 : c.nreg 120019 = 2 * m)
    (hst : s + t < 2 * n) (hsW : s + t ≤ W) (hW : 1 ≤ W) {o : QOrigin}
    (ho : QOriginIn c (bandReg bOQuery 1) o) :
    ∃ c' k, Exec P W qLoadC c c' k ∧ k ≤ 30 ∧ FrameB BLdC c c' ∧
      c'.nreg 120021 = (if β = 1 then t else 2 * m - t) ∧ c'.nreg 120022 = (s + t) % n ∧
      c'.nreg 120023 = qhzOf o ∧ c'.nreg 120024 = σbOf (c.nreg 120004) ∧
      c'.nreg 120025 = c.nreg 120001 ∧ c'.nreg 120026 = c.nreg 120002 ∧
      c'.nreg 120027 = c.nreg 120003 := by
  -- 1. sideS
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, r₁⟩ : ∃ c₁ k₁, Exec P W (ifEq 120018 120011
      (.instr (.copyN 120021 120017)) (.instr (.subN 120021 120019 120017))) c c₁ k₁ ∧ k₁ ≤ 5 ∧
      c₁.nreg 120021 = (if β = 1 then t else 2 * m - t) ∧
      (∀ r, r ≠ 120021 → c₁.nreg r = c.nreg r) := by
    by_cases hb : β = 1
    · obtain ⟨c₁, e₁, v₁, r₁⟩ := copy_exec (P := P) hw 120021 120017
      exact ⟨c₁, _, ifEq_eq_exec (by rw [hβ, h11, hb]) e₁, by omega,
        by rw [v₁, ht, ite_eq_left hb], r₁⟩
    · obtain ⟨k', e', hk'⟩ := ifEq_ne_exec (S := .instr (.copyN 120021 120017))
        (show c.nreg 120018 ≠ c.nreg 120011 by rw [hβ, h11]; exact hb)
        (Exec.subN (P := P) hw 120021 120019 120017)
      refine ⟨_, _, e', by omega, ?_, fun r hr => ?_⟩
      · config_simp; rw [h19, ht, ite_eq_right hb]
      · config_simp; rw [Machine.upd_other _ _ _ hr]
  have w₁ := e₁.wb_right
  -- 2. the top vertex
  obtain ⟨c₂, e₂, v₂, r₂, -⟩ := add_exec (P := P) w₁ 120022 120015 120017 (by
    rw [r₁ _ (by decide), r₁ _ (by decide), hs, ht]; exact hsW)
  rw [r₁ _ (by decide), r₁ _ (by decide), hs, ht] at v₂
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, r₃, -⟩ := modSub_exec (P := P) (r := 120022) (nr := 120010)
    (by decide) c₂ e₂.wb_right (by rw [v₂, r₂ _ (by decide), r₁ _ (by decide), hn]; exact hst)
  rw [v₂, r₂ _ (by decide), r₁ _ (by decide), hn] at v₃
  have R₃ : ∀ r, r ≠ 120021 → r ≠ 120022 → c₃.nreg r = c.nreg r := fun r a b =>
    (r₃ r b).trans ((r₂ r b).trans (r₁ r a))
  have w₃ := e₃.wb_right
  -- 3. the height vertex
  obtain ⟨c₄, k₄, e₄, hk₄, v₄, r₄⟩ : ∃ c₄ k₄, Exec P W (ifEq 120001 120011
      (.instr (.copyN 120023 120003)) (.instr (.copyN 120023 120002))) c₃ c₄ k₄ ∧ k₄ ≤ 5 ∧
      c₄.nreg 120023 = qhzOf o ∧ (∀ r, r ≠ 120023 → c₄.nreg r = c₃.nreg r) := by
    obtain ⟨cA, eA, vA, rA⟩ := copy_exec (P := P) w₃ 120023 120003
    obtain ⟨cB, eB, vB, rB⟩ := copy_exec (P := P) w₃ 120023 120002
    have g1 : c₃.nreg 120011 = 1 := by rw [R₃ _ (by decide) (by decide), h11]
    have g : ∀ r, 120001 ≤ r → r ≤ 120003 → c₃.nreg r = c.nreg r := fun r a b =>
      R₃ r (by omega) (by omega)
    rw [show bandReg bOQuery 1 = 120001 from rfl] at ho
    rcases o with (i | ⟨e, h⟩) | h <;> simp only [QOriginIn, SymPtIn] at ho <;> norm_num at ho
    · obtain ⟨o1, o2⟩ := ho
      obtain ⟨k', e', hk'⟩ := ifEq_ne_exec (S := .instr (.copyN 120023 120003))
        (show c₃.nreg 120001 ≠ c₃.nreg 120011 by
          rw [g1, g _ (by norm_num) (by norm_num)];  omega) eB
      refine ⟨cB, k', e', by omega, ?_, rB⟩
      rw [vB, g _ (by norm_num) (by norm_num)]; exact o2
    · obtain ⟨o1, o2, o3⟩ := ho
      refine ⟨cA, _, ifEq_eq_exec (by
        rw [g1, g _ (by norm_num) (by norm_num)]; exact o1) eA,
        by omega, ?_, rA⟩
      rw [vA, g _ (by norm_num) (by norm_num)]; exact o3
    · obtain ⟨o1, o2⟩ := ho
      obtain ⟨k', e', hk'⟩ := ifEq_ne_exec (S := .instr (.copyN 120023 120003))
        (show c₃.nreg 120001 ≠ c₃.nreg 120011 by
          rw [g1, g _ (by norm_num) (by norm_num)];  omega) eB
      refine ⟨cB, k', e', by omega, ?_, rB⟩
      rw [vB, g _ (by norm_num) (by norm_num)]; exact o2
  have w₄ := e₄.wb_right
  -- 4. the direction bit
  obtain ⟨c₅, k₅, e₅, hk₅, v₅, r₅⟩ : ∃ c₅ k₅, Exec P W (ifEq 120004 120011
      (.instr (.constN 120024 1)) (.instr (.constN 120024 0))) c₄ c₅ k₅ ∧ k₅ ≤ 5 ∧
      c₅.nreg 120024 = σbOf (c.nreg 120004) ∧ (∀ r, r ≠ 120024 → c₅.nreg r = c₄.nreg r) := by
    have g1 : c₄.nreg 120011 = 1 := by rw [r₄ _ (by decide), R₃ _ (by decide) (by decide), h11]
    have g4 : c₄.nreg 120004 = c.nreg 120004 := by
      rw [r₄ _ (by decide), R₃ _ (by decide) (by decide)]
    by_cases hd : c.nreg 120004 = 1
    · obtain ⟨cA, eA, vA, rA⟩ := const_exec (P := P) w₄ 120024 1 hW
      exact ⟨cA, _, ifEq_eq_exec (by rw [g1, g4, hd]) eA, by omega,
        by rw [vA]; unfold σbOf; rw [ite_eq_left hd], rA⟩
    · obtain ⟨cB, eB, vB, rB⟩ := const_exec (P := P) w₄ 120024 0 (by omega)
      obtain ⟨k', e', hk'⟩ := ifEq_ne_exec (S := .instr (.constN 120024 1))
        (show c₄.nreg 120004 ≠ c₄.nreg 120011 by rw [g1, g4]; exact hd) eB
      exact ⟨cB, k', e', by omega, by rw [vB]; unfold σbOf; rw [ite_eq_right hd], rB⟩
  have w₅ := e₅.wb_right
  -- 5. the origin
  obtain ⟨c₆, k₆, e₆, hk₆, v₆⟩ : ∃ c₆ k₆, Exec P W
      (block [.copyN 120025 120001, .copyN 120026 120002, .copyN 120027 120003]) c₅ c₆ k₆ ∧
      k₆ = 3 ∧ (c₆.nreg 120025 = c₅.nreg 120001 ∧ c₆.nreg 120026 = c₅.nreg 120002 ∧
        c₆.nreg 120027 = c₅.nreg 120003 ∧ ∀ r, r < 120025 ∨ 120027 < r → c₆.nreg r = c₅.nreg r) := by
    exec_block
    exact ⟨rfl, by config_simp, by config_simp, by config_simp, fun r hr => by
      config_simp; upd_solve⟩
  obtain ⟨v25, v26, v27, r₆⟩ := v₆
  have ex : Exec P W qLoadC c c₆ _ := .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆))))
  have G : ∀ r, 120001 ≤ r → r ≤ 120004 → c₅.nreg r = c.nreg r := fun r a b => by
    rw [r₅ r (by omega), r₄ r (by omega), R₃ r (by omega) (by omega)]
  refine ⟨c₆, _, ex, by omega, exec_frameB ex wr_qLoadC, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r₆ _ (by omega), r₅ _ (by decide), r₄ _ (by decide), r₃ _ (by decide),
      r₂ _ (by decide)]; exact v₁
  · rw [r₆ _ (by omega), r₅ _ (by decide), r₄ _ (by decide)]; exact v₃
  · rw [r₆ _ (by omega), r₅ _ (by decide)]; exact v₄
  · rw [r₆ _ (by omega)]; exact v₅
  · rw [v25, G _ (by norm_num) (by norm_num)]
  · rw [v26, G _ (by norm_num) (by norm_num)]
  · rw [v27, G _ (by norm_num) (by norm_num)]

/-- The values of the query: the structure's, with the origin and the direction. -/
noncomputable def qV (V : QV) (P : Polygon) (o : QOrigin) (d : ℕ) : QV :=
  { V with hz := qhzOf o, σb := σbOf d, zo := qzoOf (Qof P) o }

theorem wr_qLoadA : wr BLd qLoadA = true := by decide

/-- **Loading the constants of the query.** -/
theorem qLoad_exec {P : Polygon} {W : ℕ} {m : ℕ → ℕ} {O E : ℕ} {V : QV} {H : Host} {C : Chain}
    {N : NF} {B : OracleBook.BookData} {k : ℕ} (hA : QAt P m O E V H C N B k) (hEW : E ≤ W)
    (c : Config) (hw : WordsBounded W c) (hm : c.nmem = m) (hO : c.nreg 120000 = O)
    (hW : 8 * P.n + 32 ≤ W) {o : QOrigin} (ho : QOriginIn c (bandReg bOQuery 1) o)
    (hol : o.Lt P.n) :
    ∃ c' k, Exec P W qLoad c c' k ∧ k ≤ 100 ∧ FrameB BLd c c' ∧
      QConst P (qV V P o (c.nreg 120004)) c' := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  obtain ⟨-, -, hd1, hd2, hd3, -⟩ := hA.desc
  have hVm : V.m = C.m := by rw [← hA.dm, hd2]
  have hVs : V.s = C.s := by rw [← hA.ds, hd1]
  have hVt : V.tIdx = C.topIdx := by rw [← hA.dt, hd3]
  have hmn : C.m < P.n := by have := C.m_lt; rw [hA.CQ, hQn] at this; exact this
  have hsn : C.s < P.n := by have := hA.s_lt; rw [hA.CQ, hQn] at this; exact this
  have htl := C.topIdx_le
  obtain ⟨c₁, k₁, e₁, hk₁, a10, a11, a12, a48, a28, a13, a14, a30, a31, a32, a33, a34, a35, a36,
    a37, a38, a39, a40, a41, a42, a49⟩ := qLoadA_exec hA hEW c hw hm hO (by omega)
  have f₁ := exec_frameB e₁ wr_qLoadA
  obtain ⟨c₂, k₂, e₂, hk₂, b15, b16, b17, b18, b19, b20, b29, b43, b44, b45, b46, b47⟩ :=
    qLoadB_exec hA hEW c₁ e₁.wb_right (by rw [f₁.2.2.1, hm]) a11 a13 a14 (by omega)
  have f₂ := exec_frameB e₂ wr_qLoadB
  have g₂ : ∀ r, BLdB r = false → c₂.nreg r = c₁.nreg r := f₂.1
  have ho₂ : QOriginIn c₂ (bandReg bOQuery 1) o := by
    have hr : ∀ r, 120001 ≤ r → r ≤ 120004 → c₂.nreg r = c.nreg r := fun r a b => by
      rw [g₂ r (by simp only [BLdB, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega), f₁.1 r (by simp only [BLd, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)]
    rw [show bandReg bOQuery 1 = 120001 from rfl] at ho ⊢
    rcases o with (i | ⟨e, h⟩) | h <;> simp only [QOriginIn, SymPtIn] at ho ⊢ <;>
      norm_num at ho ⊢ <;> simp only [hr 120001 (by norm_num) (by norm_num), hr 120002 (by norm_num) (by norm_num), hr 120003 (by norm_num) (by norm_num)] <;> exact ho
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, v21, v22, v23, v24, v25, v26, v27⟩ := qLoadC_exec (P := P) c₂
    e₂.wb_right (n := P.n) (s := V.s) (m := V.m) (t := V.tIdx) (β := V.β)
    (by rw [g₂ _ (by decide)]; exact a10) (by rw [g₂ _ (by decide)]; exact a11) b15 b17 b18 b19
    (by omega) (by omega) (by omega) ho₂
  have ex : Exec P W qLoad c c₃ _ := .seq e₁ (.seq e₂ e₃)
  have f : FrameB BLd c c₃ := exec_frameB ex wr_qLoad
  -- the values after all three phases
  have K2 : ∀ r, BLdC r = false → c₃.nreg r = c₂.nreg r := f₃.1
  have K1 : ∀ r, BLdC r = false → BLdB r = false → c₃.nreg r = c₁.nreg r := fun r a b =>
    (K2 r a).trans (g₂ r b)
  have hd4 : c₂.nreg 120004 = c.nreg 120004 := by
    rw [g₂ _ (by decide), f₁.1 _ (by decide)]
  have hr0 : ∀ r, 120001 ≤ r → r ≤ 120003 → c₂.nreg r = c.nreg r := fun r a b => by
    rw [g₂ r (by simp only [BLdB, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega), f₁.1 r (by simp only [BLd, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)]
  refine ⟨c₃, _, ex, by omega, f, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [K1 _ (by decide) (by decide)]; assumption)
    | (rw [K2 _ (by decide)]; assumption)
    | skip
  · rw [v21]; exact hA.sS.symm
  · rw [v22]; exact hA.tv.symm
  · exact v23
  · rw [v24, hd4]; rfl
  · rw [hr0 _ (by norm_num) (by norm_num)] at v25 v26 v27
    rw [show bandReg bOQuery 1 = 120001 from rfl] at ho
    rcases o with (i | ⟨e, h⟩) | h <;> simp only [QOriginIn, SymPtIn] at ho <;> norm_num at ho
    · exact Or.inr ⟨by rw [v25, ho.1]; norm_num, .vtx i, hol,
        ⟨by rw [v25, ho.1], by rw [v26, ho.2]⟩, rfl⟩
    · exact Or.inr ⟨by rw [v25, ho.1]; norm_num, .onEdge e h, hol,
        ⟨by rw [v25, ho.1], by rw [v26, ho.2.1], by rw [v27, ho.2.2]⟩, rfl⟩
    · exact Or.inl ⟨by rw [v25, ho.1], rfl⟩

/-- The structure facts do not read the origin and direction of the values. -/
theorem QAt.withQ {P : Polygon} {m : ℕ → ℕ} {O E : ℕ} {V : QV} {H : Host} {C : Chain}
    {N : NF} {B : OracleBook.BookData} {k : ℕ} (hA : QAt P m O E V H C N B k) (o : QOrigin)
    (d : ℕ) : QAt P m O E (qV V P o d) H C N B k := { hA with }

/-- The value facts of the query. -/
theorem QAt.qvok {P : Polygon} {m : ℕ → ℕ} {O E : ℕ} {V : QV} {H : Host} {C : Chain}
    {N : NF} {B : OracleBook.BookData} {k : ℕ} (hA : QAt P m O E V H C N B k) {o : QOrigin}
    (hol : o.Lt P.n) (d : ℕ) : QVOK P C (qV V P o d) := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  obtain ⟨-, -, hd1, hd2, hd3, hd4⟩ := hA.desc
  have hsn : C.s < P.n := by have := hA.s_lt; rw [hA.CQ, hQn] at this; exact this
  refine ⟨hA.CQ, by show V.s = C.s; rw [← hA.ds, hd1], by show V.m = C.m; rw [← hA.dm, hd2],
    ?_, ?_, ?_, by show V.s < P.n; rw [← hA.ds, hd1]; exact hsn⟩
  · show V.sS = C.sideS C.sideBeta
    rw [hA.sS, ← hA.dβ, ← hA.dt, hd3, ← hA.dm, hd2]
    unfold Chain.sideS
    by_cases hb : C.sideBeta = true
    · rw [ite_eq_left (hd4.2 hb), ite_eq_left hb]
    · rw [ite_eq_right (fun h => hb (hd4.1 h)), ite_eq_right hb]
  · show qhzOf o < P.n
    rcases o with (i | ⟨e, h⟩) | h
    · exact hol
    · exact hol.2
    · exact hol
  · show σbOf d ≤ 1
    unfold σbOf; split_ifs <;> omega

end

end OracleR

end Chazelle.Core
