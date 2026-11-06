module

public import Chazelle.Core.OraclePrepMirror

/-!
# Lemma 3.6 (WP-H), preprocessing part 5: the analysis of a walk position on the RAM

`posA` analyses the walk position `⟨w, hc⟩` in registers `110100`, `110101`: the index of the walk
vertex `w` (`110102`), the normalised height code (`110103`), the flag of `InI` (`110104`) and the
mirrored position (`110105`, `110106`), in natural arithmetic (`vaN`, `nzN`, `inT`, `mirN`, which
are `vaIdx`, `nz`, `inTest`, `mirPos` of `OraclePrepMirror`).  `posInit` computes the constants
`6 + rT`, `11 + rT`, `12 + rT`, `11 + rT + 2 m`, `12 + rT + 2 m` it uses.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open Chazelle.Chain (sideE)
open OracleQ

@[expose] public section

/-! ## The functions computed -/

/-- The walk vertex index. -/
def vaN (s m S n w : ℕ) : ℕ := (s + sideE m ((S + (w - 6)) % (2 * m))) % n

/-- The normalised height code. -/
def nzN (va hc : ℕ) : ℕ := if hc = 0 ∨ hc = va + 1 then 0 else hc

/-- The test of the open halves of the tour range. -/
def inT (R m z w : ℕ) : Prop :=
  if z = 0 then (6 < w ∧ w < 6 + R) ∨ (6 + R < w ∧ w < 2 * m + 6) else 6 ≤ w ∧ w < 2 * m + 6

instance (R m z w : ℕ) : Decidable (inT R m z w) := by unfold inT; infer_instance

/-- The mirrored position. -/
def mirN (R m z w hc : ℕ) : ℕ × ℕ :=
  if z = 0 then ((if w ≤ 6 + R then 12 + R else 12 + R + 2 * m) - w, 0)
  else ((if w < 6 + R then 11 + R else 11 + R + 2 * m) - w, hc)

theorem nzN_eq (C : Chain) (w hc : ℕ) :
    nzN (vaN C.s C.m (C.sideS C.sideBeta) C.P.n w) hc = nz C w hc := rfl

theorem inT_eq (C : Chain) (z w : ℕ) : inT (rT C) C.m z w ↔ inTest C z w := Iff.rfl

theorem mirN_eq (C : Chain) (w hc : ℕ) :
    mirN (rT C) C.m (nz C w hc) w hc = ((mirPos C w hc).edge, (mirPos C w hc).hgt) := by
  unfold mirN mirPos mirW0 mirW1; split_ifs <;> rfl

/-- The test fails outside the tour range, whatever the code. -/
theorem not_inT {R m z w : ℕ} (hR : R < 2 * m) (h : w < 6 ∨ 2 * m + 6 ≤ w) : ¬ inT R m z w := by
  unfold inT
  by_cases hz : z = 0
  · rw [ite_eq_left hz]; omega
  · rw [ite_eq_right hz]; omega

/-! ## The constants -/

/-- The constant registers read by `posA`. -/
structure PosK (n s m S R : ℕ) (c : Config) : Prop where
  rn : c.nreg 120010 = n
  one : c.nreg 120011 = 1
  zero : c.nreg 120012 = 0
  rs : c.nreg 120015 = s
  rm : c.nreg 120016 = m
  twoM : c.nreg 120019 = 2 * m
  rS : c.nreg 120021 = S
  six : c.nreg 120028 = 6
  tEnd : c.nreg 120029 = 2 * m + 6
  k0 : c.nreg 110050 = 6 + R
  k1 : c.nreg 110051 = 11 + R
  k2 : c.nreg 110052 = 12 + R
  k3 : c.nreg 110053 = 11 + R + 2 * m
  k4 : c.nreg 110054 = 12 + R + 2 * m

theorem PosK.congr {n s m S R : ℕ} {c c' : Config} (h : PosK n s m S R c)
    (hr : ∀ r, (120010 ≤ r ∧ r ≤ 120029) ∨ (110050 ≤ r ∧ r ≤ 110054) → c'.nreg r = c.nreg r) :
    PosK n s m S R c' :=
  ⟨(hr _ (⋄)).trans h.rn, (hr _ (⋄)).trans h.one, (hr _ (⋄)).trans h.zero,
    (hr _ (⋄)).trans h.rs, (hr _ (⋄)).trans h.rm, (hr _ (⋄)).trans h.twoM,
    (hr _ (⋄)).trans h.rS, (hr _ (⋄)).trans h.six, (hr _ (⋄)).trans h.tEnd,
    (hr _ (⋄)).trans h.k0, (hr _ (⋄)).trans h.k1, (hr _ (⋄)).trans h.k2,
    (hr _ (⋄)).trans h.k3, (hr _ (⋄)).trans h.k4⟩

/-- A conditional subtraction. -/
def redS (r nr : ℕ) : Stmt := .ifLtN r nr .skip (.instr (.subN r r nr))

theorem redS_exec {P : Polygon} {W : ℕ} {r nr : ℕ} (_hr : r ≠ nr) (c : Config)
    (hw : WordsBounded W c) :
    ∃ c' k, Exec P W (redS r nr) c c' k ∧ k ≤ 3 ∧
      c'.nreg r = (if c.nreg r < c.nreg nr then c.nreg r else c.nreg r - c.nreg nr) ∧
      FrameB (fun x => decide (x = r)) c c' := by
  have hwr : wr (fun x => decide (x = r)) (redS r nr) = true := by
    simp [redS, wr, wrOK]
  unfold redS
  by_cases h : c.nreg r < c.nreg nr
  · exact ⟨c, 1, .ifLtN_true h (.skip hw), by omega, by rw [ite_eq_left h], FrameB.refl _ _⟩
  · have e := Exec.ifLtN_false (P := P) (W := W) (e := .instr (.subN r r nr)) (t := .skip) h
      (Exec.subN hw r r nr)
    refine ⟨_, _, e, by omega, by rw [ite_eq_right h]; config_simp, ?_⟩
    exact exec_frameB e (by simp [wr, wrOK])

/-- **The constants of `posA`**: `R = (4 m - 2 S) mod 2 m` and its shifts. -/
def posInit : Stmt :=
  .seq (block [.addN 110059 120019 120019, .subN 110059 110059 120021, .subN 110059 110059 120021])
    (.seq (redS 110059 120019) (.seq (redS 110059 120019)
      (block [.constN 110055 6, .constN 110056 11, .constN 110057 12,
        .addN 110050 110059 110055, .addN 110051 110059 110056, .addN 110052 110059 110057,
        .addN 110053 110051 120019, .addN 110054 110052 120019])))

/-- The registers written by `posInit`. -/
def BPI (r : ℕ) : Bool := decide (110050 ≤ r ∧ r ≤ 110059)

theorem posInit_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {m S : ℕ}
    (_hm : c.nreg 120016 = m) (h2m : c.nreg 120019 = 2 * m) (hS : c.nreg 120021 = S)
    (hSm : S ≤ 2 * m) (h1 : 1 ≤ m) (hW : 4 * m + 20 ≤ W) :
    ∃ c' k, Exec P W posInit c c' k ∧ k ≤ 30 ∧ FrameB BPI c c' ∧
      c'.nreg 110050 = 6 + (4 * m - 2 * S) % (2 * m) ∧
      c'.nreg 110051 = 11 + (4 * m - 2 * S) % (2 * m) ∧
      c'.nreg 110052 = 12 + (4 * m - 2 * S) % (2 * m) ∧
      c'.nreg 110053 = 11 + (4 * m - 2 * S) % (2 * m) + 2 * m ∧
      c'.nreg 110054 = 12 + (4 * m - 2 * S) % (2 * m) + 2 * m := by
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, r₁⟩ : ∃ c₁ k₁, Exec P W (block [.addN 110059 120019 120019,
      .subN 110059 110059 120021, .subN 110059 110059 120021]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 110059 = 4 * m - 2 * S ∧ (∀ r, r ≠ 110059 → c₁.nreg r = c.nreg r) := by
    exec_block
    · rw [h2m]; omega
    · refine ⟨rfl, ?_, fun r hr => ?_⟩
      · config_simp; rw [h2m, hS]; omega
      · config_simp; upd_solve
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, f₂⟩ := redS_exec (P := P) (r := 110059) (nr := 120019) (⌖) c₁
    e₁.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, f₃⟩ := redS_exec (P := P) (r := 110059) (nr := 120019) (⌖) c₂
    e₂.wb_right
  have g2 : c₂.nreg 120019 = 2 * m := Ρ f₂.1 _ (⌖), r₁ _ (⌖), h2m
  have g3 : c₃.nreg 120019 = 2 * m := Ρ f₃.1 _ (⌖), g2
  have hR : c₃.nreg 110059 = (4 * m - 2 * S) % (2 * m) := by
    Ξ v₃, v₂, v₁, g2, r₁ _ (⌖), h2m
    have := mod_le_two (x := 4 * m - 2 * S) (M := 2 * m) (⋄) (⋄)
    rcases this with ⟨a, b⟩ | ⟨a, d, b⟩ | ⟨a, b⟩ <;> rw [b] <;> split_ifs <;> omega
  have hRl : (4 * m - 2 * S) % (2 * m) < 2 * m := Nat.mod_lt _ (⋄)
  have w₃ := e₃.wb_right
  obtain ⟨c₄, k₄, e₄, hk₄, v₄⟩ : ∃ c₄ k₄, Exec P W (block [.constN 110055 6, .constN 110056 11,
      .constN 110057 12, .addN 110050 110059 110055, .addN 110051 110059 110056,
      .addN 110052 110059 110057, .addN 110053 110051 120019, .addN 110054 110052 120019]) c₃ c₄ k₄ ∧
      k₄ = 8 ∧ c₄.nreg = upd (upd (upd (upd (upd (upd (upd (upd c₃.nreg 110055 6) 110056 11)
        110057 12) 110050 (c₃.nreg 110059 + 6)) 110051 (c₃.nreg 110059 + 11)) 110052
        (c₃.nreg 110059 + 12)) 110053 (c₃.nreg 110059 + 11 + 2 * m)) 110054
        (c₃.nreg 110059 + 12 + 2 * m) := by
    exec_block
    · omega
    · omega
    · omega
    · config_simp; omega
    · config_simp; omega
    · config_simp; omega
    · config_simp; rw [g3]; omega
    · config_simp; rw [g3]; omega
    · refine ⟨rfl, ?_⟩
      config_simp
      Ξ g3
  refine ⟨c₄, _, .seq e₁ (.seq e₂ (.seq e₃ e₄)), ⋄, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have f₄ := exec_frameB e₄ (B := BPI) (⌖)
    have f₁ := exec_frameB e₁ (B := BPI) (⌖)
    exact f₁.trans ((FrameB.mono f₂ fun r h => by simp at h; subst h; decide).trans
      ((FrameB.mono f₃ fun r h => by simp at h; subst h; decide).trans f₄))
  all_goals rw [v₄]; config_simp; rw [hR]; omega

/-! ## The analysis -/

/-- The walk vertex index into `110102`. -/
def vaS : Stmt :=
  .seq (block [.subN 110107 110100 120028, .addN 110107 110107 120021])
    (.seq (redS 110107 120019) (.seq (redS 110107 120019)
      (.seq (.ifLtN 120016 110107 (.instr (.subN 110107 120019 110107)) .skip)
        (.seq (.instr (.addN 110102 120015 110107)) (redS 110102 120010)))))

/-- The normalised code into `110103`. -/
def nzS : Stmt :=
  .seq (.instr (.addN 110108 110102 120011))
    (.ifLtN 120012 110101
      (ifEq 110101 110108 (.instr (.constN 110103 0)) (.instr (.copyN 110103 110101)))
      (.instr (.constN 110103 0)))

/-- The flag of the open halves into `110104`. -/
def flagS : Stmt :=
  .ifLtN 120012 110103
    (.ifLtN 110100 120028 (.instr (.constN 110104 0))
      (.ifLtN 110100 120029 (.instr (.constN 110104 1)) (.instr (.constN 110104 0))))
    (.ifLtN 120028 110100
      (.ifLtN 110100 110050 (.instr (.constN 110104 1))
        (.ifLtN 110050 110100
          (.ifLtN 110100 120029 (.instr (.constN 110104 1)) (.instr (.constN 110104 0)))
          (.instr (.constN 110104 0))))
      (.instr (.constN 110104 0)))

/-- The mirrored position into `110105`, `110106`. -/
def mirS : Stmt :=
  .ifLtN 120012 110103
    (.seq (.ifLtN 110100 110050 (.instr (.subN 110105 110051 110100))
        (.instr (.subN 110105 110053 110100)))
      (.instr (.copyN 110106 110101)))
    (.seq (.ifLtN 110050 110100 (.instr (.subN 110105 110054 110100))
        (.instr (.subN 110105 110052 110100)))
      (.instr (.constN 110106 0)))

/-- **The analysis of the walk position in `110100`, `110101`.** -/
def posA : Stmt :=
  .ifLtN 120029 110100 (block [.constN 110103 0, .constN 110104 0])
    (.seq vaS (.seq nzS (.seq flagS mirS)))

/-- The registers written by `posA`. -/
def BPA (r : ℕ) : Bool := decide (110102 ≤ r ∧ r ≤ 110108)

theorem wr_posA : wr BPA posA = true := ⌖

theorem sideE_eq_ite (m j : ℕ) : sideE m j = if m < j then 2 * m - j else j := by
  unfold sideE; split_ifs <;> omega

theorem vaS_exec {P : Polygon} {W : ℕ} {n s m S R : ℕ} {c : Config} (hw : WordsBounded W c)
    (hk : PosK n s m S R c) (h1 : 1 ≤ m) (hmn : m < n) (hsn : s < n) (hS : S ≤ 2 * m)
    (hw7 : c.nreg 110100 ≤ 2 * m + 6) (hW : 4 * n + 20 ≤ W) :
    ∃ c' k, Exec P W vaS c c' k ∧ k ≤ 20 ∧
      FrameB (fun r => decide (r = 110102 ∨ r = 110107)) c c' ∧
      c'.nreg 110102 = vaN s m S n (c.nreg 110100) := by
  obtain ⟨w, hwd⟩ : ∃ w, c.nreg 110100 = w := ⟨_, rfl⟩
  rw [hwd] at hw7 ⊢
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, r₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.subN 110107 110100 120028, .addN 110107 110107 120021]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 110107 = S + (w - 6) ∧ (∀ r, r ≠ 110107 → c₁.nreg r = c.nreg r) := by
    exec_block
    · config_simp; rw [hwd, hk.six, hk.rS]; omega
    · refine ⟨rfl, ?_, fun r hr => ?_⟩
      · config_simp; rw [hwd, hk.six, hk.rS]; omega
      · config_simp; upd_solve
  have hk₁ : PosK n s m S R c₁ := hk.congr fun r hr => r₁ r (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, f₂⟩ := redS_exec (P := P) (r := 110107) (nr := 120019) (by decide)
    c₁ e₁.wb_right
  have hk₂' : PosK n s m S R c₂ := hk₁.congr fun r hr => f₂.1 r (by simp; omega)
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, f₃⟩ := redS_exec (P := P) (r := 110107) (nr := 120019) (by decide)
    c₂ e₂.wb_right
  have hk₃' : PosK n s m S R c₃ := hk₂'.congr fun r hr => f₃.1 r (by simp; omega)
  have hx : c₃.nreg 110107 = (S + (w - 6)) % (2 * m) := by
    rw [v₃, v₂, v₁, hk₂'.twoM, hk₁.twoM]
    have := mod_le_two (x := S + (w - 6)) (M := 2 * m) (by omega) (by omega)
    rcases this with ⟨a, b⟩ | ⟨a, d, b⟩ | ⟨a, b⟩ <;> rw [b] <;> split_ifs <;> omega
  have hxl : (S + (w - 6)) % (2 * m) < 2 * m := Nat.mod_lt _ (by omega)
  obtain ⟨x, hxd⟩ : ∃ x, (S + (w - 6)) % (2 * m) = x := ⟨_, rfl⟩
  rw [hxd] at hx hxl
  have w₃ := e₃.wb_right
  -- the side index
  obtain ⟨c₄, k₄, e₄, hk₄, v₄, f₄⟩ : ∃ c₄ k₄, Exec P W
      (.ifLtN 120016 110107 (.instr (.subN 110107 120019 110107)) .skip) c₃ c₄ k₄ ∧ k₄ ≤ 3 ∧
      c₄.nreg 110107 = sideE m x ∧ FrameB (fun r => decide (r = 110107)) c₃ c₄ := by
    rw [sideE_eq_ite]
    by_cases h : m < x
    · have ht : c₃.nreg 120016 < c₃.nreg 110107 := by rw [hk₃'.rm, hx]; exact h
      have e := Exec.ifLtN_true (P := P) (W := W) (e := .skip)
        (t := .instr (.subN 110107 120019 110107)) ht (Exec.subN w₃ 110107 120019 110107)
      refine ⟨_, _, e, by omega, ?_, exec_frameB e (by decide)⟩
      rw [ite_eq_left h]; config_simp; rw [hk₃'.twoM, hx]
    · have ht : ¬ c₃.nreg 120016 < c₃.nreg 110107 := by rw [hk₃'.rm, hx]; exact h
      have e := Exec.ifLtN_false (P := P) (W := W) (t := .instr (.subN 110107 120019 110107))
        (e := .skip) ht (.skip w₃)
      exact ⟨_, _, e, by omega, by rw [ite_eq_right h, hx], FrameB.refl _ _⟩
  have hk₄' : PosK n s m S R c₄ := hk₃'.congr fun r hr => f₄.1 r (by simp; omega)
  have hy : sideE m x ≤ m := Chazelle.Chain.sideE_le hxl.le
  obtain ⟨c₅, e₅, v₅, r₅, -⟩ := add_exec (P := P) e₄.wb_right 110102 120015 110107
    (by rw [hk₄'.rs, v₄]; omega)
  rw [hk₄'.rs, v₄] at v₅
  have hk₅ : PosK n s m S R c₅ := hk₄'.congr fun r hr => r₅ r (by omega)
  obtain ⟨c₆, k₆, e₆, hk₆, v₆, f₆⟩ := redS_exec (P := P) (r := 110102) (nr := 120010) (by decide)
    c₅ e₅.wb_right
  have ex : Exec P W vaS c c₆ _ := .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆))))
  refine ⟨c₆, _, ex, by omega, exec_frameB ex (by decide), ?_⟩
  rw [v₆, v₅, hk₅.rn]
  show _ = (s + sideE m ((S + (w - 6)) % (2 * m))) % n
  rw [hxd]
  split_ifs with h
  · rw [Nat.mod_eq_of_lt h]
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem nzS_exec {P : Polygon} {W : ℕ} {n s m S R : ℕ} {c : Config} (hw : WordsBounded W c)
    (hk : PosK n s m S R c) {va : ℕ} (hva : c.nreg 110102 = va) (hvn : va < n) (hW : n + 1 ≤ W) :
    ∃ c' k, Exec P W nzS c c' k ∧ k ≤ 10 ∧
      FrameB (fun r => decide (r = 110103 ∨ r = 110108)) c c' ∧
      c'.nreg 110103 = nzN va (c.nreg 110101) := by
  obtain ⟨c₁, e₁, v₁, r₁, -⟩ := add_exec (P := P) hw 110108 110102 120011
    (by rw [hva, hk.one]; omega)
  Ξ' hva, hk.one at v₁
  have w₁ := e₁.wb_right
  have hk₁ : PosK n s m S R c₁ := hk.congr fun r hr => r₁ r (⋄)
  have hh : c₁.nreg 110101 = c.nreg 110101 := r₁ _ (⌖)
  obtain ⟨hc, hcd⟩ : ∃ hc, c.nreg 110101 = hc := ⟨_, rfl⟩
  Ξ' hcd at hh ⊢
  unfold nzS nzN
  have f₁ : FrameB (fun r => decide (r = 110103 ∨ r = 110108)) c c₁ :=
    exec_frameB e₁ (⌖)
  by_cases h0 : hc = 0
  · have ht : ¬ c₁.nreg 120012 < c₁.nreg 110101 := by rw [hk₁.zero, hh, h0]; exact Nat.lt_irrefl 0
    have e := Exec.ifLtN_false (P := P) (W := W) (t := ifEq 110101 110108 (.instr (.constN 110103 0))
      (.instr (.copyN 110103 110101))) (e := .instr (.constN 110103 0)) ht
      (Exec.constN w₁ 110103 0 (Nat.zero_le _))
    have ex := Exec.seq e₁ e
    refine ⟨_, _, ex, ⋄, exec_frameB ex (⌖), ?_⟩
    rw [ite_eq_left (Or.inl h0)]; config_simp
  · have hpos : c₁.nreg 120012 < c₁.nreg 110101 := by rw [hk₁.zero, hh]; omega
    by_cases hv : hc = va + 1
    · have hq : c₁.nreg 110101 = c₁.nreg 110108 := Ρ hh, v₁, hv
      have e := Exec.ifLtN_true (P := P) (W := W) (t := ifEq 110101 110108 (.instr (.constN 110103 0))
        (.instr (.copyN 110103 110101))) (e := .instr (.constN 110103 0)) hpos
        (ifEq_eq_exec hq (Exec.constN w₁ 110103 0 (Nat.zero_le _)))
      have ex := Exec.seq e₁ e
      refine ⟨_, _, ex, ⋄, exec_frameB ex (⌖), ?_⟩
      rw [ite_eq_left (Or.inr hv)]; config_simp
    · have hq : c₁.nreg 110101 ≠ c₁.nreg 110108 := by rw [hh, v₁]; exact hv
      obtain ⟨k', e', hk'⟩ := ifEq_ne_exec (P := P) (W := W) (S := .instr (.constN 110103 0))
        hq (Exec.copyN w₁ 110103 110101)
      have ex := Exec.seq e₁ (Exec.ifLtN_true (e := .instr (.constN 110103 0)) hpos e')
      refine ⟨_, _, ex, ⋄, exec_frameB ex (⌖), ?_⟩
      rw [ite_eq_right (⋄)]; config_simp; exact hh

theorem flagS_exec {P : Polygon} {W : ℕ} {n s m S R : ℕ} {c : Config} (hw : WordsBounded W c)
    (hk : PosK n s m S R c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W flagS c c' k ∧ k ≤ 12 ∧ FrameB (fun r => decide (r = 110104)) c c' ∧
      c'.nreg 110104 = if inT R m (c.nreg 110103) (c.nreg 110100) then 1 else 0 := by
  obtain ⟨z, hz⟩ : ∃ z, c.nreg 110103 = z := ⟨_, rfl⟩
  obtain ⟨w, hwd⟩ : ∃ w, c.nreg 110100 = w := ⟨_, rfl⟩
  Ξ hz, hwd
  have hwr : wr (fun r => decide (r = 110104)) flagS = true := ⌖
  suffices H : ∃ c' k, Exec P W flagS c c' k ∧ k ≤ 12 ∧
      c'.nreg 110104 = if inT R m z w then 1 else 0 by
    obtain ⟨c', k, ex, hk', hv⟩ := H
    exact ⟨c', k, ex, hk', exec_frameB ex hwr, hv⟩
  have c0 := Exec.constN (P := P) hw 110104 0 (Nat.zero_le _)
  have c1 := Exec.constN (P := P) hw 110104 1 hW
  unfold flagS inT
  by_cases h0 : z = 0
  · ϴ h0, ite_true
    refine spec_ifLtN_false (by rw [hk.zero, hz, h0]; exact Nat.lt_irrefl 0) ?_
    by_cases a1 : 6 < w
    · refine spec_ifLtN_true (by rw [hk.six, hwd]; exact a1) ?_
      by_cases a2 : w < 6 + R
      · refine spec_ifLtN_true (by rw [hk.k0, hwd]; exact a2) ⟨_, _, c1, ?_⟩
        refine ⟨⋄, ?_⟩; config_simp; Ξ ite_eq_left (Or.inl ⟨a1, a2⟩)
      · refine spec_ifLtN_false (by rw [hk.k0, hwd]; exact a2) ?_
        by_cases a3 : 6 + R < w
        · refine spec_ifLtN_true (by rw [hk.k0, hwd]; exact a3) ?_
          by_cases a4 : w < 2 * m + 6
          · refine spec_ifLtN_true (by rw [hk.tEnd, hwd]; exact a4) ⟨_, _, c1, ?_⟩
            refine ⟨⋄, ?_⟩; config_simp; Ξ ite_eq_left (Or.inr ⟨a3, a4⟩)
          · refine spec_ifLtN_false (by rw [hk.tEnd, hwd]; exact a4) ⟨_, _, c0, ?_⟩
            refine ⟨⋄, ?_⟩; config_simp; Ξ ite_eq_right (⋄)
        · refine spec_ifLtN_false (by rw [hk.k0, hwd]; exact a3) ⟨_, _, c0, ?_⟩
          refine ⟨⋄, ?_⟩; config_simp; Ξ ite_eq_right (⋄)
    · refine spec_ifLtN_false (by rw [hk.six, hwd]; exact a1) ⟨_, _, c0, ?_⟩
      refine ⟨⋄, ?_⟩; config_simp; Ξ ite_eq_right (⋄)
  · ϴ h0, ite_false
    refine spec_ifLtN_true (by rw [hk.zero, hz]; omega) ?_
    by_cases a1 : w < 6
    · refine spec_ifLtN_true (by rw [hk.six, hwd]; exact a1) ⟨_, _, c0, ?_⟩
      refine ⟨⋄, ?_⟩; config_simp; Ξ ite_eq_right (⋄)
    · refine spec_ifLtN_false (by rw [hk.six, hwd]; exact a1) ?_
      by_cases a2 : w < 2 * m + 6
      · refine spec_ifLtN_true (by rw [hk.tEnd, hwd]; exact a2) ⟨_, _, c1, ?_⟩
        refine ⟨⋄, ?_⟩; config_simp; Ξ ite_eq_left ⟨⋄, a2⟩
      · refine spec_ifLtN_false (by rw [hk.tEnd, hwd]; exact a2) ⟨_, _, c0, ?_⟩
        refine ⟨⋄, ?_⟩; config_simp; Ξ ite_eq_right (⋄)

theorem mirS_exec {P : Polygon} {W : ℕ} {n s m S R : ℕ} {c : Config} (hw : WordsBounded W c)
    (hk : PosK n s m S R c) :
    ∃ c' k, Exec P W mirS c c' k ∧ k ≤ 8 ∧
      FrameB (fun r => decide (r = 110105 ∨ r = 110106)) c c' ∧
      (c'.nreg 110105, c'.nreg 110106) =
        mirN R m (c.nreg 110103) (c.nreg 110100) (c.nreg 110101) := by
  obtain ⟨z, hz⟩ : ∃ z, c.nreg 110103 = z := ⟨_, rfl⟩
  obtain ⟨w, hwd⟩ : ∃ w, c.nreg 110100 = w := ⟨_, rfl⟩
  obtain ⟨hc, hcd⟩ : ∃ hc, c.nreg 110101 = hc := ⟨_, rfl⟩
  Ξ hz, hwd, hcd
  have hwr : wr (fun r => decide (r = 110105 ∨ r = 110106)) mirS = true := ⌖
  suffices H : ∃ c' k, Exec P W mirS c c' k ∧ k ≤ 8 ∧
      (c'.nreg 110105, c'.nreg 110106) = mirN R m z w hc by
    obtain ⟨c', k, ex, hk', hv⟩ := H
    exact ⟨c', k, ex, hk', exec_frameB ex hwr, hv⟩
  unfold mirS mirN
  by_cases h0 : z = 0
  · Ξ ite_eq_left h0
    refine spec_ifLtN_false (by rw [hk.zero, hz, h0]; exact Nat.lt_irrefl 0) ?_
    by_cases a : 6 + R < w
    · have e1 := Exec.subN (P := P) hw 110105 110054 110100
      have e2 := Exec.constN (P := P) e1.wb_right 110106 0 (Nat.zero_le _)
      refine ⟨_, _, .seq (.ifLtN_true (by rw [hk.k0, hwd]; exact a) e1) e2, ⋄, ?_⟩
      rw [ite_eq_right (⋄)]; config_simp; Ξ hk.k4, hwd
    · have e1 := Exec.subN (P := P) hw 110105 110052 110100
      have e2 := Exec.constN (P := P) e1.wb_right 110106 0 (Nat.zero_le _)
      refine ⟨_, _, .seq (.ifLtN_false (by rw [hk.k0, hwd]; exact a) e1) e2, ⋄, ?_⟩
      rw [ite_eq_left (⋄)]; config_simp; Ξ hk.k2, hwd
  · Ξ ite_eq_right h0
    refine spec_ifLtN_true (by rw [hk.zero, hz]; omega) ?_
    by_cases a : w < 6 + R
    · have e1 := Exec.subN (P := P) hw 110105 110051 110100
      have e2 := Exec.copyN (P := P) e1.wb_right 110106 110101
      refine ⟨_, _, .seq (.ifLtN_true (by rw [hk.k0, hwd]; exact a) e1) e2, ⋄, ?_⟩
      rw [ite_eq_left a]; config_simp; Ξ hk.k1, hwd, hcd
    · have e1 := Exec.subN (P := P) hw 110105 110053 110100
      have e2 := Exec.copyN (P := P) e1.wb_right 110106 110101
      refine ⟨_, _, .seq (.ifLtN_false (by rw [hk.k0, hwd]; exact a) e1) e2, ⋄, ?_⟩
      rw [ite_eq_right a]; config_simp; Ξ hk.k3, hwd, hcd

/-- **The analysis of a walk position.** -/
theorem posA_exec {P : Polygon} {W : ℕ} {n s m S R : ℕ} {c : Config} (hw : WordsBounded W c)
    (hk : PosK n s m S R c) (h1 : 1 ≤ m) (hmn : m < n) (hsn : s < n) (hS : S ≤ 2 * m)
    (hR : R < 2 * m) (hW : 4 * n + 20 ≤ W) :
    ∃ c' k, Exec P W posA c c' k ∧ k ≤ 60 ∧ FrameB BPA c c' ∧
      c'.nreg 110104 = (if inT R m (c'.nreg 110103) (c.nreg 110100) then 1 else 0) ∧
      (c.nreg 110100 ≤ 2 * m + 6 →
        c'.nreg 110102 = vaN s m S n (c.nreg 110100) ∧
        c'.nreg 110103 = nzN (vaN s m S n (c.nreg 110100)) (c.nreg 110101) ∧
        (c'.nreg 110105, c'.nreg 110106) =
          mirN R m (c'.nreg 110103) (c.nreg 110100) (c.nreg 110101)) := by
  obtain ⟨w, hwd⟩ : ∃ w, c.nreg 110100 = w := ⟨_, rfl⟩
  Ξ hwd
  unfold posA
  by_cases hout : 2 * m + 6 < w
  · have ht : c.nreg 120029 < c.nreg 110100 := by rw [hk.tEnd, hwd]; exact hout
    obtain ⟨c', k, ex, hk', v⟩ : ∃ c' k, Exec P W (block [.constN 110103 0, .constN 110104 0]) c c' k ∧
        k = 2 ∧ c'.nreg 110103 = 0 ∧ c'.nreg 110104 = 0 := by
      exec_block
      · omega
      · omega
      · exact ⟨rfl, by config_simp, by config_simp⟩
    have ex' := Exec.ifLtN_true (e := .seq vaS (.seq nzS (.seq flagS mirS))) ht ex
    refine ⟨c', _, ex', ⋄, exec_frameB ex' wr_posA, ?_, fun h => absurd h (⋄)⟩
    Ξ v.2, v.1, ite_eq_right (not_inT hR (Or.inr (⋄)))
  · push Not at hout
    have hw7 : c.nreg 110100 ≤ 2 * m + 6 := by rw [hwd]; exact hout
    obtain ⟨c₁, k₁, e₁, hk₁, f₁, v₁⟩ := vaS_exec (P := P) hw hk h1 hmn hsn hS hw7 (⋄)
    have K₁ : PosK n s m S R c₁ := hk.congr fun r hr => f₁.1 r (by simp; omega)
    have hva : vaN s m S n w < n := Nat.mod_lt _ (⋄)
    Ξ' hwd at v₁
    obtain ⟨c₂, k₂, e₂, hk₂, f₂, v₂⟩ := nzS_exec (P := P) e₁.wb_right K₁ v₁ hva (⋄)
    have K₂ : PosK n s m S R c₂ := K₁.congr fun r hr => f₂.1 r (by simp; omega)
    obtain ⟨c₃, k₃, e₃, hk₃, f₃, v₃⟩ := flagS_exec (P := P) e₂.wb_right K₂ (⋄)
    have K₃ : PosK n s m S R c₃ := K₂.congr fun r hr => f₃.1 r (by simp; omega)
    obtain ⟨c₄, k₄, e₄, hk₄, f₄, v₄⟩ := mirS_exec (P := P) e₃.wb_right K₃
    have ex : Exec P W (.seq vaS (.seq nzS (.seq flagS mirS))) c c₄ _ :=
      .seq e₁ (.seq e₂ (.seq e₃ e₄))
    have ht : ¬ c.nreg 120029 < c.nreg 110100 := by rw [hk.tEnd, hwd]; omega
    have ex' := Exec.ifLtN_false (P := P) (W := W) (t := block [.constN 110103 0, .constN 110104 0])
      ht ex
    -- register bookkeeping
    have g100 : ∀ d : Config, (d = c₁ ∨ d = c₂ ∨ d = c₃) → d.nreg 110100 = w ∧
        d.nreg 110101 = c.nreg 110101 := by
      have a1 : c₁.nreg 110100 = w := Ρ f₁.1 _ (⌖), hwd
      have b1 : c₁.nreg 110101 = c.nreg 110101 := f₁.1 _ (⌖)
      have a2 : c₂.nreg 110100 = w := Ρ f₂.1 _ (⌖), a1
      have b2 : c₂.nreg 110101 = c.nreg 110101 := Ρ f₂.1 _ (⌖), b1
      have a3 : c₃.nreg 110100 = w := Ρ f₃.1 _ (⌖), a2
      have b3 : c₃.nreg 110101 = c.nreg 110101 := Ρ f₃.1 _ (⌖), b2
      rintro d (rfl | rfl | rfl)
      · exact ⟨a1, b1⟩
      · exact ⟨a2, b2⟩
      · exact ⟨a3, b3⟩
    have z4 : c₄.nreg 110103 = nzN (vaN s m S n w) (c.nreg 110101) := by
      Ξ f₄.1 _ (⌖), f₃.1 _ (⌖), v₂, (g100 c₁ (Or.inl rfl)).2
    refine ⟨c₄, _, ex', ⋄, exec_frameB ex' wr_posA, ?_, fun _ => ⟨?_, z4, ?_⟩⟩
    · rw [f₄.1 110104 (⌖), v₃, (g100 c₂ (Or.inr (Or.inl rfl))).1,
        f₄.1 110103 (⌖), f₃.1 110103 (⌖)]
    · Ξ f₄.1 _ (⌖), f₃.1 _ (⌖), f₂.1 _ (⌖), v₁
    · rw [v₄, (g100 c₃ (Or.inr (Or.inr rfl))).1, (g100 c₃ (Or.inr (Or.inr rfl))).2,
        f₄.1 110103 (⌖)]

end

end OracleR

end Chazelle.Core
