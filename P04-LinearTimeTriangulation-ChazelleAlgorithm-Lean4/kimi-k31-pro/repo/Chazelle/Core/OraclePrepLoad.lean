module

public import Chazelle.Core.OraclePrepSort
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.ConfigTactics

/-!
# Lemma 3.6 (WP-H), preprocessing part 2: loading the constants

`pLoad` reads the chain descriptor (`110000`) and the normal form (`110001`) of the
preprocessing into the constant registers of the query (`120010 …`, as `QConst` needs them for
the routines shared with the query): `n`, `1`, `0`, `2`, `6`, the descriptor, the normal form,
`s`, `m`, the top index, the orientation, `2 m`, `2 m + 7`, `2 m + 6`, `sideS`, the top vertex,
the areas of the normal form, and `A` (`120030`), `K` (`120039`).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-- The small constants and the handles. -/
def pLoadA : Stmt :=
  block [.inputSize 120010, .constN 120011 1, .constN 120012 0, .constN 120048 2,
    .constN 120028 6, .copyN 120013 110000, .copyN 120014 110001]

/-- `sideS` and the top vertex. -/
def pLoadC : Stmt :=
  .seq (ifEq 120018 120011 (.instr (.copyN 120021 120017)) (.instr (.subN 120021 120019 120017)))
    (.seq (.instr (.addN 120022 120015 120017)) (modSub 120022 120010))

/-- `A` and `K`. -/
def pLoadD : Stmt :=
  block [.addN 120190 120014 120011, .loadN 120030 120190, .loadN 120039 120014]

/-- **Loading the constants of the preprocessing.** -/
def pLoad : Stmt := .seq pLoadA (.seq qLoadB (.seq pLoadC pLoadD))

/-- The registers written by `pLoad`. -/
def BPL (r : ℕ) : Bool := decide (120010 ≤ r ∧ r ≤ 120049) || decide (120190 ≤ r ∧ r ≤ 120191)

theorem wr_pLoad : wr BPL pLoad = true := by decide

/-- The facts loaded by `pLoad`. -/
structure PLoaded (P : Polygon) (D NB s mm ti bb A K CB AB RB SB LB : ℕ) (c : Config) : Prop where
  n : c.nreg 120010 = P.n
  one : c.nreg 120011 = 1
  zero : c.nreg 120012 = 0
  two : c.nreg 120048 = 2
  six : c.nreg 120028 = 6
  rD : c.nreg 120013 = D
  rNB : c.nreg 120014 = NB
  rs : c.nreg 120015 = s
  rm : c.nreg 120016 = mm
  rti : c.nreg 120017 = ti
  rbb : c.nreg 120018 = bb
  twoM : c.nreg 120019 = 2 * mm
  nW : c.nreg 120020 = 2 * mm + 7
  tEnd : c.nreg 120029 = 2 * mm + 6
  sS : c.nreg 120021 = (if bb = 1 then ti else 2 * mm - ti)
  tv : c.nreg 120022 = (s + ti) % P.n
  rA : c.nreg 120030 = A
  rK : c.nreg 120039 = K
  rCB : c.nreg 120043 = CB
  rAB : c.nreg 120044 = AB
  rRB : c.nreg 120045 = RB
  rSB : c.nreg 120046 = SB
  rLB : c.nreg 120047 = LB

/-- **The load of the preprocessing.** -/
theorem pLoad_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    {H : Host} {C : Chain} {N : NF} (hD : ChainDescAt c.nmem (c.nreg 110000) (Qof P) H C)
    (hCQ : C.P = Qof P) (hsl : C.s < C.P.n) (hNF : NFAt c.nmem (c.nreg 110001) N)
    (hDW : c.nreg 110000 + 5 ≤ W) (hNW : c.nreg 110001 + 7 ≤ W) (hW : 8 * P.n + 32 ≤ W) :
    ∃ c' k, Exec P W pLoad c c' k ∧ k ≤ 60 ∧ FrameB BPL c c' ∧
      PLoaded P (c.nreg 110000) (c.nreg 110001) C.s C.m C.topIdx (c.nmem (c.nreg 110000 + 4))
        N.arcs.length N.chords.length (c.nmem (c.nreg 110001 + 3)) (c.nmem (c.nreg 110001 + 4))
        (c.nmem (c.nreg 110001 + 5)) (c.nmem (c.nreg 110001 + 6)) (c.nmem (c.nreg 110001 + 7)) c' := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  obtain ⟨-, -, hd1, hd2, hd3, -⟩ := hD
  have hmn : C.m < P.n := by have := C.m_lt; rw [hCQ, hQn] at this; exact this
  have hs : C.s < P.n := by rw [hCQ, hQn] at hsl; exact hsl
  have htl := C.topIdx_le
  set D := c.nreg 110000
  set NB := c.nreg 110001
  -- the constants and handles
  obtain ⟨c₁, k₁, e₁, hk₁, v₁⟩ : ∃ c₁ k₁, Exec P W pLoadA c c₁ k₁ ∧ k₁ = 7 ∧
      (c₁.nreg 120010 = P.n ∧ c₁.nreg 120011 = 1 ∧ c₁.nreg 120012 = 0 ∧ c₁.nreg 120048 = 2 ∧
        c₁.nreg 120028 = 6 ∧ c₁.nreg 120013 = D ∧ c₁.nreg 120014 = NB ∧ c₁.nmem = c.nmem) := by
    unfold pLoadA
    exec_block
    all_goals (try omega)
    exact ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp, by config_simp,
      by csr, by csr, rfl⟩
  obtain ⟨a10, a11, a12, a48, a28, a13, a14, m₁⟩ := v₁
  have f₁ := exec_frameB e₁ (B := BPL) (by decide)
  -- the chain descriptor and the areas
  obtain ⟨c₂, k₂, e₂, hk₂, v₂⟩ : ∃ c₂ k₂, Exec P W qLoadB c₁ c₂ k₂ ∧ k₂ = 25 ∧
      (c₂.nreg 120015 = C.s ∧ c₂.nreg 120016 = C.m ∧ c₂.nreg 120017 = C.topIdx ∧
        c₂.nreg 120018 = c.nmem (D + 4) ∧ c₂.nreg 120019 = 2 * C.m ∧ c₂.nreg 120020 = 2 * C.m + 7 ∧
        c₂.nreg 120029 = 2 * C.m + 6 ∧ c₂.nreg 120043 = c.nmem (NB + 3) ∧
        c₂.nreg 120044 = c.nmem (NB + 4) ∧ c₂.nreg 120045 = c.nmem (NB + 5) ∧
        c₂.nreg 120046 = c.nmem (NB + 6) ∧ c₂.nreg 120047 = c.nmem (NB + 7)) := by
    have w₁ := e₁.wb_right
    unfold qLoadB
    exec_block
    all_goals (config_simp; (try simp [a11, a13, a14, m₁, hd2, Nat.add_assoc] at *); (try norm_num); (try omega))
  obtain ⟨b15, b16, b17, b18, b19, b20, b29, b43, b44, b45, b46, b47⟩ := v₂
  have f₂ := exec_frameB e₂ (B := BLdB) wr_qLoadB
  have g₂  := f₂.1
  have w₂ := e₂.wb_right
  have m₂ : c₂.nmem = c.nmem := f₂.2.2.1.trans m₁
  -- sideS and the top vertex
  obtain ⟨c₃, k₃, e₃, hk₃, v21, v22, r₃, m₃⟩ : ∃ c₃ k₃, Exec P W pLoadC c₂ c₃ k₃ ∧ k₃ ≤ 10 ∧
      c₃.nreg 120021 = (if c.nmem (D + 4) = 1 then C.topIdx else 2 * C.m - C.topIdx) ∧
      c₃.nreg 120022 = (C.s + C.topIdx) % P.n ∧
      (∀ r, r ≠ 120021 → r ≠ 120022 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem := by
    have h11 : c₂.nreg 120011 = 1 := by rwx [g₂ _ (by decide)]
    have h10 : c₂.nreg 120010 = P.n := by rwx [g₂ _ (by decide)]
    obtain ⟨c₁', k₁', e₁', hk₁', v₁', r₁'⟩ : ∃ c₁' k₁', Exec P W (ifEq 120018 120011
        (.instr (.copyN 120021 120017)) (.instr (.subN 120021 120019 120017))) c₂ c₁' k₁' ∧
        k₁' ≤ 5 ∧ c₁'.nreg 120021 = (if c.nmem (D + 4) = 1 then C.topIdx else 2 * C.m - C.topIdx) ∧
        (∀ r, r ≠ 120021 → c₁'.nreg r = c₂.nreg r) := by
      by_cases hb : c.nmem (D + 4) = 1
      · obtain ⟨cc, ec, vc, rc⟩ := copy_exec (P := P) w₂ 120021 120017
        exact ⟨cc, _, ifEq_eq_exec (by rw [b18, h11, hb]) ec, by omega,
          by rw [vc, b17, ite_eq_left hb], rc⟩
      · obtain ⟨k', e', hk'⟩ := ifEq_ne_exec (S := .instr (.copyN 120021 120017))
          (show c₂.nreg 120018 ≠ c₂.nreg 120011 by rwx [b18, h11])
          (Exec.subN (P := P) w₂ 120021 120019 120017)
        refine ⟨_, _, e', by omega, ?_, fun r hr => ?_⟩
        · config_simp; rw [b19, b17, ite_eq_right hb]
        · config_simp; rw [Machine.upd_other _ _ _ hr]
    have w₁' := e₁'.wb_right
    obtain ⟨cA, eA, vA, rA, mA⟩ := add_exec (P := P) w₁' 120022 120015 120017 (by
      rwo [r₁' _ (by decide), r₁' _ (by decide), b15, b17])
    rw [r₁' _ (by decide), r₁' _ (by decide), b15, b17] at vA
    obtain ⟨cB, kB, eB, hkB, vB, rB, mB, -⟩ := modSub_exec (P := P) (r := 120022) (nr := 120010)
      (by decide) cA eA.wb_right (by rwo [vA, rA _ (by decide), r₁' _ (by decide), h10])
    rw [vA, rA _ (by decide), r₁' _ (by decide), h10] at vB
    have v21' : cB.nreg 120021 = (if c.nmem (D + 4) = 1 then C.topIdx else 2 * C.m - C.topIdx) := by
      rwx [rB _ (by decide), rA _ (by decide)]
    refine ⟨cB, _, .seq e₁' (.seq eA eB), by omega, v21', vB, fun r h1 h2 => ?_, ?_⟩
    · rw [rB r h2, rA r h2, r₁' r h1]
    · rw [mB, mA]
      exact exec_frameB e₁' (B := fun r => decide (r = 120021)) (by decide) |>.2.2.1
  have w₃ := e₃.wb_right
  -- `A` and `K`
  obtain ⟨c₄, k₄, e₄, hk₄, v30, v39, r₄⟩ : ∃ c₄ k₄, Exec P W pLoadD c₃ c₄ k₄ ∧ k₄ = 3 ∧
      c₄.nreg 120030 = N.arcs.length ∧ c₄.nreg 120039 = N.chords.length ∧
      (∀ r, r ≠ 120190 → r ≠ 120030 → r ≠ 120039 → c₄.nreg r = c₃.nreg r) := by
    have h14 : c₃.nreg 120014 = NB := by rwx [r₃ _ (by decide) (by decide), g₂ _ (by decide)]
    have h11 : c₃.nreg 120011 = 1 := by rwx [r₃ _ (by decide) (by decide), g₂ _ (by decide)]
    unfold pLoadD
    exec_block
    · rwo [h14, h11]
    · refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_⟩
      · config_simp; rw [h14, h11, m₃, m₂]; exact hNF.2.1
      · config_simp; rw [h14, m₃, m₂]; exact hNF.1
      · config_simp; upd_solve
  have ex : Exec P W pLoad c c₄ _ := .seq e₁ (.seq e₂ (.seq e₃ e₄))
  -- the final values
  have R4 : ∀ r, r ≠ 120190 → r ≠ 120030 → r ≠ 120039 → r ≠ 120021 → r ≠ 120022 →
      c₄.nreg r = c₂.nreg r := fun r a b c d e => by rw [r₄ r a b c, r₃ r d e]
  have R1 : ∀ r, BLdB r = false → r ≠ 120190 → r ≠ 120030 → r ≠ 120039 → r ≠ 120021 →
      r ≠ 120022 → c₄.nreg r = c₁.nreg r := fun r h a b c d e => by rw [R4 r a b c d e, g₂ r h]
  refine ⟨c₄, _, ex, by omega, exec_frameB ex wr_pLoad, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [R1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)];
       assumption)
    | (rw [R4 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; assumption)
    | (rw [r₄ _ (by decide) (by decide) (by decide)]; assumption)
    | assumption

end

end OracleR

end Chazelle.Core
