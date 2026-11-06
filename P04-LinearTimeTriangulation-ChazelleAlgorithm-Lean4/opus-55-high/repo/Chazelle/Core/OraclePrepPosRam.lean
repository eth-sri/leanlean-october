module

public import Chazelle.MacT
public import Chazelle.Core.DownPhaseOracleArc

namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open Chazelle.Chain (sideE)
open OracleQ
@[expose] public section
def vaN (s m S n w : ℕ) : ℕ := (s + sideE m (ztypv % ztdk)) % n

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
    nzN (vaN C.s C.m ztboi C.P.n w) hc = nz C w hc := rfl
theorem inT_eq (C : Chain) (z w : ℕ) : inT ztkdv C.m z w ↔ inTest C z w := Iff.rfl
theorem mirN_eq (C : Chain) (w hc : ℕ) :
    mirN ztkdv C.m ztrua w hc = ((mirPos C w hc).edge, (mirPos C w hc).hgt) := by
  unfold mirN mirPos mirW0 mirW1; grind

/-- The test fails outside the tour range, whatever the code. -/
theorem not_inT {R m z w : ℕ} (hR : R < 2 * m) (h : w < 6 ∨ 2 * m + 6 ≤ w) : ¬ inT R m z w := by
  unfold inT
  grind

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
    (hr : ∀ r, (120010 ≤ r ∧ r ≤ 120029) ∨ ztndy → c'.nreg r = c.nreg r) :
    PosK n s m S R c' :=
  ⟨(hr _ by_omega).trans h.rn, (hr _ by_omega).trans h.one, (hr _ by_omega).trans h.zero,
    (hr _ by_omega).trans h.rs, (hr _ by_omega).trans h.rm, (hr _ by_omega).trans h.twoM,
    (hr _ by_omega).trans h.rS, (hr _ by_omega).trans h.six, (hr _ by_omega).trans h.tEnd,
    (hr _ by_omega).trans h.k0, (hr _ by_omega).trans h.k1, (hr _ by_omega).trans h.k2,
    (hr _ by_omega).trans h.k3, (hr _ by_omega).trans h.k4⟩

/-- A conditional subtraction. -/
def redS (r nr : ℕ) : Stmt := .ifLtN r nr .skip ztnch
variable {P : Polygon} {W : ℕ}
theorem redS_exec {r nr : ℕ} (_hr : r ≠ nr) (c : Config)
    (hw : WordsBounded W c) :
    ∃ c' k, Exec P W zttym c c' k ∧ k ≤ 3 ∧
      c'.nreg r = (if c.nreg r < c.nreg nr then c.nreg r else c.nreg r - c.nreg nr) ∧
      FrameB ztloy c c' := by
  have hwr : wr ztloy zttym = true := by
    simp [redS, wr, wrOK]
  unfold redS
  zucfj
  · exact ⟨c, 1, .ifLtN_true h ztjd, by_omega, by_simp_all, FrameB.refl _ _⟩
  · have e := Exec.ifLtN_false (P := P) (t := .skip) h
      ztpyg
    refine ⟨_, _, e, by_omega, by_simp_all, ?_⟩
    exact exec_frameB e by_tauto

/-- **The constants of `posA`**: `R = (4 m - 2 S) mod 2 m` and its shifts. -/
def posInit : Stmt :=
  .seq (block [.addN 110059 120019 120019, .subN 110059 110059 120021, .subN 110059 110059 120021])
    (.seq zttyk (.seq zttyk
      (block [.constN 110055 6, .constN 110056 11, .constN 110057 12,
        .addN 110050 110059 110055, .addN 110051 110059 110056, .addN 110052 110059 110057,
        .addN 110053 110051 120019, .addN 110054 110052 120019])))

/-- The registers written by `posInit`. -/
def BPI (r : ℕ) : Bool := decide (110050 ≤ r ∧ r ≤ 110059)
theorem posInit_exec {c : Config} (hw : WordsBounded W c) {m S : ℕ}
    (_hm : c.nreg 120016 = m) (h2m : c.nreg 120019 = 2 * m) (hS : c.nreg 120021 = S)
    (hSm : S ≤ 2 * m) (h1 : 1 ≤ m) (hW : 4 * m + 20 ≤ W) :
    ∃ c' k, Exec P W posInit c c' k ∧ k ≤ 30 ∧ FrameB BPI c c' ∧
      c'.nreg 110050 = 6 + ztbxx % ztdk ∧
      c'.nreg 110051 = 11 + ztbxx % ztdk ∧
      c'.nreg 110052 = 12 + ztbxx % ztdk ∧
      c'.nreg 110053 = 11 + ztbxx % ztdk + 2 * m ∧
      c'.nreg 110054 = 12 + ztbxx % ztdk + 2 * m := by
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, r₁⟩ : ∃ c₁ k₁, Exec P W (block [.addN 110059 120019 120019,
      .subN 110059 110059 120021, .subN 110059 110059 120021]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 110059 = 4 * m - 2 * S ∧ (∀ r, r ≠ 110059 → c₁.nreg r = c.nreg r) := by
    exec_block
    · omega
    · zuhjd
      · config_simp; omega
      simp_all
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, f₂⟩ := redS_exec (P := P) (r := 110059) (nr := 120019) by_decide c₁
    e₁.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, f₃⟩ := redS_exec (P := P) (r := 110059) (nr := 120019) by_decide c₂
    e₂.wb_right
  have g2 : c₂.nreg 120019 = 2 * m := by rw [f₂.1 _ by_decide, r₁ _ by_decide, h2m]
  have g3 : c₃.nreg 120019 = 2 * m := by rw [f₃.1 _ by_decide, g2]
  have hR : c₃.nreg 110059 = ztbxx % ztdk := by
    rw [v₃, v₂, v₁, g2, r₁ _ by_decide, h2m]
    have := mod_le_two (x := 4 * m - 2 * S) (M := 2 * m) by_omega by_omega
    grind
  have hRl : ztbxx % ztdk < 2 * m := by_grind
  zubj
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
    · config_simp; omega
    · config_simp; omega
    grind
  refine ⟨c₄, _, .seq e₁ ztcb, by_omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have f₄ := exec_frameB e₄ (B := BPI) by_decide
    have f₁ := exec_frameB e₁ (B := BPI) by_decide
    exact f₁.trans ((FrameB.mono f₂ fun r h => by simp at h; subst h; decide).trans
      ((FrameB.mono f₃ fun r h => by simp at h; subst h; decide).trans f₄))
  all_goals zuntf; config_simp; rw [hR]; omega

/-! ## The analysis -/

/-- The walk vertex index into `110102`. -/
def vaS : Stmt :=
  .seq ztiqv
    (.seq zttyl (.seq zttyl
      (.seq ztiff
        (.seq (.instr (.addN 110102 120015 110107)) (redS 110102 120010)))))

/-- The normalised code into `110103`. -/
def nzS : Stmt :=
  .seq (.instr (.addN 110108 110102 120011))
    (.ifLtN 120012 110101
      (ifEq 110101 110108 ztifo ztigf)
      ztifo)

/-- The flag of the open halves into `110104`. -/
def flagS : Stmt :=
  .ifLtN 120012 110103
    (.ifLtN 110100 120028 ztdry
      ztyzn)
    (.ifLtN 120028 110100
      (.ifLtN 110100 110050 ztifp
        (.ifLtN 110050 110100
          ztyzn
          ztdry))
      ztdry)

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
    (.seq vaS ztnct)

/-- The registers written by `posA`. -/
def BPA (r : ℕ) : Bool := decide (110102 ≤ r ∧ r ≤ 110108)
theorem wr_posA : wr BPA posA = true := by_decide
theorem sideE_eq_ite (m j : ℕ) : sideE m j = if m < j then 2 * m - j else j := by
  zumu
theorem vaS_exec {n s m S R : ℕ} {c : Config} (hw : WordsBounded W c)
    (hk : PosK n s m S R c) (h1 : 1 ≤ m) (hmn : m < n) (hsn : s < n) (hS : S ≤ 2 * m)
    (hw7 : c.nreg 110100 ≤ 2 * m + 6) (hW : 4 * n + 20 ≤ W) :
    ∃ c' k, Exec P W vaS c c' k ∧ k ≤ 20 ∧
      FrameB (fun r => decide (r = 110102 ∨ r = 110107)) c c' ∧
      c'.nreg 110102 = vaN s m S n ztgha := by
  zubpn
  rw [hwd] at hw7 ⊢
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, r₁⟩ : ∃ c₁ k₁, Exec P W
      ztiqv c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 110107 = S + ztvu ∧ (∀ r, r ≠ 110107 → c₁.nreg r = c.nreg r) := by
    exec_block
    · config_simp; rw [hwd, hk.six, hk.rS]; omega
    · zuhjd
      · config_simp; rw [hwd, hk.six, hk.rS]; omega
      simp_all
  zuiyg
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, f₂⟩ := redS_exec (P := P) (r := 110107) (nr := 120019) by_decide
    c₁ e₁.wb_right
  have hk₂' := hk₁.congr fun r hr => f₂.1 r by_grind
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, f₃⟩ := redS_exec (P := P) (r := 110107) (nr := 120019) by_decide
    c₂ e₂.wb_right
  have hk₃' := hk₂'.congr fun r hr => f₃.1 r by_grind
  have hx : c₃.nreg 110107 = ztypv % ztdk := by
    rw [v₃, v₂, v₁, hk₂'.twoM, hk₁.twoM]
    have := mod_le_two (x := S + ztvu) (M := 2 * m) by_omega by_omega
    grind
  have hxl : ztypv % ztdk < 2 * m := Nat.mod_lt _ by_omega
  obtain ⟨x, hxd⟩ : ∃ x, (S + (w - 6)) % (2 * m) = x := by_grind
  rw [hxd] at hx hxl
  zubj
  -- the side index
  obtain ⟨c₄, k₄, e₄, hk₄, v₄, f₄⟩ : ∃ c₄ k₄, Exec P W
      ztiff c₃ c₄ k₄ ∧ k₄ ≤ 3 ∧
      c₄.nreg 110107 = sideE m x ∧ FrameB (fun r => decide (r = 110107)) c₃ c₄ := by
    rw [sideE_eq_ite]
    by_cases h : m < x
    · have ht : c₃.nreg 120016 < c₃.nreg 110107 := by zuoml; exact h
      have e := Exec.ifLtN_true (P := P) (e := .skip) ht (Exec.subN w₃ 110107 120019 110107)
      refine ⟨_, _, e, by_omega, ?_, exec_frameB e by_decide⟩
      zvnbq; config_simp; rw [hk₃'.twoM, hx]
    · have ht : ¬ c₃.nreg 120016 < c₃.nreg 110107 := by zuoml; exact h
      have e := Exec.ifLtN_false (P := P) (t := .instr (.subN 110107 120019 110107)) ht ztpsb
      exact ⟨_, _, e, by_omega, by_grind, FrameB.refl _ _⟩
  have hk₄' := hk₃'.congr fun r hr => f₄.1 r by_grind
  have hy := Chazelle.Chain.sideE_le hxl.le
  obtain ⟨c₅, e₅, v₅, r₅, -⟩ := add_exec (P := P) e₄.wb_right 110102 120015 110107
    (by rw [hk₄'.rs, v₄]; omega)
  rw [hk₄'.rs, v₄] at v₅
  have hk₅ : PosK n s m S R c₅ := hk₄'.congr by_grind
  obtain ⟨c₆, k₆, e₆, hk₆, v₆, f₆⟩ := redS_exec (P := P) (r := 110102) (nr := 120010) by_decide
    c₅ e₅.wb_right
  have ex : Exec P W vaS c c₆ _ := .seq e₁ ztfv
  refine ⟨c₆, _, ex, by_omega, exec_frameB ex by_decide, ?_⟩
  rw [v₆, v₅, hk₅.rn]
  show _ = (s + sideE m _) % n
  rw [hxd]
  zus
  · zukp
  · zul
theorem nzS_exec {n s m S R : ℕ} {c : Config} (hw : WordsBounded W c)
    (hk : PosK n s m S R c) {va : ℕ} (hva : c.nreg 110102 = va) (hvn : va < n) (hW : n + 1 ≤ W) :
    ∃ c' k, Exec P W nzS c c' k ∧ k ≤ 10 ∧
      FrameB ztijz c c' ∧
      c'.nreg 110103 = nzN va ztjrs := by
  obtain ⟨c₁, e₁, v₁, r₁, -⟩ := add_exec (P := P) hw 110108 110102 120011
    (by rw [hva, hk.one]; omega)
  rw [hva, hk.one] at v₁
  zud
  zuiyg
  have hh : ztsfx := by_simp_all
  zugpj
  rw [hcd] at hh ⊢
  unfold nzS nzN
  have f₁ : FrameB ztijz c c₁ :=
    exec_frameB e₁ by_decide
  by_cases h0 : hc = 0
  · have ht : ¬ c₁.nreg 120012 < c₁.nreg 110101 := by_omega
    have e := Exec.ifLtN_false (P := P) (t := ifEq 110101 110108 ztifo
      ztigf) ht
      ztzbt
    zuhdw

  · have hpos : c₁.nreg 120012 < c₁.nreg 110101 := by rw [hk₁.zero, hh]; omega
    by_cases hv : hc = va + 1
    · have hq : c₁.nreg 110101 = c₁.nreg 110108 := by_omega
      have e := Exec.ifLtN_true (P := P) (t := ifEq 110101 110108 _
        ztigf) (e := .instr (.constN 110103 0)) hpos
        (ifEq_eq_exec hq ztzbt)
      zuhdw

    · have hq : c₁.nreg 110101 ≠ c₁.nreg 110108 := by_omega
      obtain ⟨k', e', hk'⟩ := ifEq_ne_exec
        hq (Exec.copyN w₁ 110103 110101)
      have ex := Exec.seq e₁ (Exec.ifLtN_true (e := .instr (.constN 110103 0)) hpos e')
      refine ztdwz
      simp_all
theorem flagS_exec {n s m S R : ℕ} {c : Config} (hw : WordsBounded W c)
    (hk : PosK n s m S R c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W flagS c c' k ∧ k ≤ 12 ∧ FrameB ztloj c c' ∧
      c'.nreg 110104 = if inT R m ztvhf ztgha then 1 else 0 := by
  zugra
  zubpn
  rw [hz, hwd]
  have hwr : wr ztloj flagS = true := by_decide
  suffices H : ∃ c' k, Exec P W flagS c c' k ∧ k ≤ 12 ∧
      c'.nreg 110104 = if inT R m z w then 1 else 0 by
    zudqx

  have c0 := Exec.constN (P := P) hw 110104 0 ztbg
  have c1 := Exec.constN (P := P) hw 110104 1 hW
  unfold flagS inT
  zujsl
  · simp only [h0, ite_true]
    zubv
    by_cases a1 : 6 < w
    · refine spec_ifLtN_true ztdci ?_
      by_cases a2 : w < 6 + R
      · refine spec_ifLtN_true ztktn zthme
        simp_all
      · refine spec_ifLtN_false ztktn ?_
        by_cases a3 : 6 + R < w
        · refine spec_ifLtN_true ztkto ?_
          by_cases a4 : w < 2 * m + 6
          · refine spec_ifLtN_true ztktq zthme
            simp_all
          · refine spec_ifLtN_false ztktq ztdiw
            simp_all
        · refine spec_ifLtN_false ztkto ztdiw
          simp_all
    · refine spec_ifLtN_false ztdci ztdiw
      refine zteh; config_simp; grind
  · simp only [h0, ite_false]
    zumjx
    by_cases a1 : w < 6
    · refine spec_ifLtN_true ztdci ztdiw
      simp_all
    · refine spec_ifLtN_false ztdci ?_
      by_cases a2 : w < 2 * m + 6
      · refine spec_ifLtN_true ztktp zthme
        simp_all
      · refine spec_ifLtN_false ztktp ztdiw
        simp_all
theorem mirS_exec {n s m S R : ℕ} {c : Config} (hw : WordsBounded W c)
    (hk : PosK n s m S R c) :
    ∃ c' k, Exec P W mirS c c' k ∧ k ≤ 8 ∧
      FrameB ztika c c' ∧
      ztggw =
        mirN R m ztvhf ztgha ztjrs := by
  zugra
  zubpn
  zugpj
  rw [hz, hwd, hcd]
  have hwr : wr ztika mirS = true := by_decide
  suffices H : ∃ c' k, Exec P W mirS c c' k ∧ k ≤ 8 ∧
      ztggw = mirN R m z w hc by
    zudqx

  unfold mirS mirN
  zujsl
  · zuhmd
    zubv
    by_cases a : 6 + R < w
    · have e1 := Exec.subN (P := P) hw 110105 110054 110100
      zuepr
      refine ztxlz
      zvmyd; config_simp; rw [hk.k4, hwd]
    · have e1 := Exec.subN (P := P) hw 110105 110052 110100
      zuepr
      refine ztxly
      zunab; config_simp; rw [hk.k2, hwd]
  · zucqa
    zumjx
    by_cases a : w < 6 + R
    · have e1 := Exec.subN (P := P) hw 110105 110051 110100
      zuffe
      refine ztxlz
      rw [ite_eq_left a]; config_simp; rw [hk.k1, hwd, hcd]
    · have e1 := Exec.subN (P := P) hw 110105 110053 110100
      zuffe
      refine ztxly
      rw [ite_eq_right a]; config_simp; rw [hk.k3, hwd, hcd]

/-- **The analysis of a walk position.** -/
theorem posA_exec {n s m S R : ℕ} {c : Config} (hw : WordsBounded W c)
    (hk : PosK n s m S R c) (h1 : 1 ≤ m) (hmn : m < n) (hsn : s < n) (hS : S ≤ 2 * m)
    (hR : R < 2 * m) (hW : 4 * n + 20 ≤ W) :
    ∃ c' k, Exec P W posA c c' k ∧ k ≤ 60 ∧ FrameB BPA c c' ∧
      c'.nreg 110104 = (if inT R m ztvfy ztgha then 1 else 0) ∧
      (c.nreg 110100 ≤ 2 * m + 6 →
        c'.nreg 110102 = vaN s m S n ztgha ∧
        c'.nreg 110103 = nzN (vaN s m S n ztgha) ztjrs ∧
        ztggw =
          mirN R m ztvfy ztgha ztjrs) := by
  zubpn
  rw [hwd]
  unfold posA
  by_cases hout : 2 * m + 6 < w
  · have ht : c.nreg 120029 < c.nreg 110100 := by zuomm; omega
    obtain ⟨c', k, ex, hk', v⟩ : ∃ c' k, Exec P W (block [.constN 110103 0, .constN 110104 0]) c c' k ∧
        k = 2 ∧ c'.nreg 110103 = 0 ∧ c'.nreg 110104 = 0 := by
      exec_block
      · omega
      · omega
      simp
    have ex' := Exec.ifLtN_true (e := .seq vaS ztnct) ht ex
    refine ⟨c', _, ex', by_omega, exec_frameB ex' wr_posA, ?_, by_simp_all⟩
    rw [v.2, v.1, ite_eq_right (not_inT hR by_omega)]
  · push Not at hout
    have hw7 : c.nreg 110100 ≤ 2 * m + 6 := by_omega
    obtain ⟨c₁, k₁, e₁, hk₁, f₁, v₁⟩ := vaS_exec hw hk h1 hmn hsn hS hw7 by_omega
    have K₁ := hk.congr fun r hr => f₁.1 r by_grind
    have hva : vaN s m S n w < n := Nat.mod_lt _ by_omega
    rw [hwd] at v₁
    obtain ⟨c₂, k₂, e₂, hk₂, f₂, v₂⟩ := nzS_exec e₁.wb_right K₁ v₁ hva by_omega
    have K₂ := K₁.congr fun r hr => f₂.1 r by_grind
    obtain ⟨c₃, k₃, e₃, hk₃, f₃, v₃⟩ := flagS_exec e₂.wb_right K₂ by_omega
    have K₃ := K₂.congr fun r hr => f₃.1 r by_grind
    obtain ⟨c₄, k₄, e₄, hk₄, f₄, v₄⟩ := mirS_exec e₃.wb_right K₃
    have ex : ztiyf :=
      .seq e₁ ztcb
    have ht : ¬ c.nreg 120029 < c.nreg 110100 := by zuomm; omega
    have ex' := Exec.ifLtN_false (t := block [.constN 110103 0, .constN 110104 0])
      ht ex
    -- register bookkeeping
    have g100 : ∀ d : Config, (d = c₁ ∨ d = c₂ ∨ d = c₃) → d.nreg 110100 = w ∧
        d.nreg 110101 = c.nreg 110101 := by
      have a1 : c₁.nreg 110100 = w := by rw [f₁.1 _ by_decide, hwd]
      have b1 : ztsfx := f₁.1 _ by_decide
      have a2 : c₂.nreg 110100 = w := by rw [f₂.1 _ by_decide, a1]
      have b2 : c₂.nreg 110101 = c.nreg 110101 := by rw [f₂.1 _ by_decide, b1]
      have a3 : c₃.nreg 110100 = w := by rw [f₃.1 _ by_decide, a2]
      have b3 : c₃.nreg 110101 = c.nreg 110101 := by rw [f₃.1 _ by_decide, b2]
      simp_all
    have z4 : c₄.nreg 110103 = nzN (vaN s m S n w) ztjrs := by
      rw [f₄.1 _ by_decide, f₃.1 _ by_decide, v₂, (g100 c₁ ztp).2]
    refine ⟨c₄, _, ex', by_omega, exec_frameB ex' wr_posA, ?_, fun _ => ⟨?_, z4, ?_⟩⟩
    · rw [f₄.1 110104 by_decide, v₃, (g100 c₂ by_simp_all).1,
        f₄.1 110103 by_decide, f₃.1 110103 by_decide]
    · rw [f₄.1 _ by_decide, f₃.1 _ by_decide, f₂.1 _ by_decide, v₁]
    · rw [v₄, (g100 c₃ by_simp_all).1, (g100 c₃ by_simp_all).2,
        f₄.1 110103 by_decide]
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ
@[expose] public section
def mdBody : Stmt := block [.addN 110035 120013 110039, .loadN 110036 110035, .addN 110037 110033 110039]

/-- **The model descriptor**: six words at the allocator, `0` then the chain descriptor. -/
def mdS : Stmt :=
  .seq (block [.copyN 120040 9999, .constN 110030 6, .addN 9999 9999 110030, .constN 110031 0,
      .storeN 120040 110031, .addN 110033 120040 120011, .constN 110038 5])
    (scatS 110039 110038 120011 110037 110036 mdBody)

/-- The registers written by `mdS`. -/
def BMD (r : ℕ) : Bool := decide ztyc || decide (r = 120040) || decide (110030 ≤ r ∧ r ≤ 110039)
variable {P : Polygon} {W : ℕ} {c : Config}
theorem mdS_exec (hw : WordsBounded W c) {D A₀ : ℕ}
    (hD : c.nreg 120013 = D) (h1 : c.nreg 120011 = 1) (hA : c.nreg 9999 = A₀) (hDA : D + 5 ≤ A₀)
    (hW : A₀ + 6 ≤ W) :
    ∃ c' k, Exec P W mdS c c' k ∧ k ≤ 60 ∧ PF BMD A₀ c c' ∧ c'.nreg 9999 = A₀ + 6 ∧
      c'.nreg 120040 = A₀ ∧ c'.nmem A₀ = 0 ∧ ∀ i, i < 5 → c'.nmem (A₀ + 1 + i) = c.nmem ztbyg := by
  obtain ⟨c₁, k₁, e₁, hk₁, n₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 120040 9999,
      .constN 110030 6, .addN 9999 9999 110030, .constN 110031 0, .storeN 120040 110031,
      .addN 110033 120040 120011, .constN 110038 5]) c c₁ k₁ ∧ k₁ = 7 ∧
      c₁.nreg = upd (upd (upd (upd (upd (upd c.nreg 120040 A₀) 110030 6) 9999 ztsux) 110031 0)
        110033 ztfnc) 110038 5 ∧
      c₁.nmem = upd c.nmem A₀ 0 ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    · omega
    · simp_all
    · omega
    · config_simp; omega
    · omega
    simp_all
  have hr₁ : ∀ r, BMD r = false → c₁.nreg r = c.nreg r := fun r hr => by
    zuggi
    zulc
  have v₃₃ : c₁.nreg 110033 = A₀ + 1 := by_simp_all
  have v₃₈ : c₁.nreg 110038 = 5 := by_simp_all
  have v₁₃ : c₁.nreg 120013 = D := by_simp_all
  have v₁₁ : ztdxr := by_simp_all
  -- the copy loop
  let J : Config → Prop := JK c₁ (fun r => decide (r = 110033) || decide (r = 120013)) A₀
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, rr₂, mm₂, rm₂, o₂, -, -⟩ := scatS_exec (P := P) (W := W)
    (ri := 110039) (rn := 110038) (r1 := 120011) (ra := 110037) (rv := 110036) (body := mdBody)
    (B := fun r => decide (110035 ≤ r ∧ r ≤ 110037)) by_decide by_decide by_decide
    by_decide by_decide J A₀
    (fun d d' hJ hr hm => JK.stable (rs := [110039]) (fun r hr' => by
      grind) hJ (fun r a b => hr r a by_simp_all) hm)
    (n := 5) (κ := 3) (fun i => A₀ + 1 + i) (fun i => c.nmem ztbyg) ztbeo
    (fun i d hi hJ hwd hri => by
      have g33 : d.nreg 110033 = A₀ + 1 := by rw [hJ.1 _ by_decide, v₃₃]
      have g13 : d.nreg 120013 = D := by rw [hJ.1 _ by_decide, v₁₃]
      have gm : d.nmem ztbyg = c.nmem ztbyg := by
        rw [hJ.2 _ by_omega, m₁, upd_other _ _ _ by_omega]
      obtain ⟨d', k', e', hk', v1, v2⟩ : ∃ d' k', Exec P W mdBody d d' k' ∧ k' = 3 ∧
          d'.nreg 110037 = A₀ + 1 + i ∧ d'.nreg 110036 = c.nmem ztbyg := by
        unfold mdBody
        exec_block
        · omega
        · config_simp; omega
        simp_all
      exact zthmu)
    e₁.wb_right ztdkz v₃₈ v₁₁ by_omega
  refine ⟨c₂, _, .seq e₁ e₂, by_omega, ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_,
    by simp_all, by_simp_all⟩, ?_, ?_, ?_, fun i hi => ?_⟩
  · zuggi
    zunkm; exact hr₁ r (by simp [BMD]; omega)
  · rw [rr₂ r (by simp only [BMD, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢; omega),
      rr₁]
  · rw [mm₂, scat_below by_grind ha, m₁, upd_other _ _ _ by_omega]
  · simp_all
  · simp_all
  · rw [mm₂, scat_other by_grind, m₁, upd_same]
  · zuoyz
    exact scat_at hi by_grind

/-! ## The inverse of the arc-sequence table -/

/-- The inverse body: address `POS + σ p`, value `p`. -/
def posBody : Stmt :=
  block [.addN 110045 120046 110049, .loadN 110044 110045, .addN 110047 120031 110044,
    .copyN 110046 110049]

/-- **The inverse table**: `POS[σ p] := p` for `p < A`, with `σ` the table at `SB` (`120046`). -/
def posTS : Stmt :=
  .seq (block [.copyN 120031 9999, .addN 9999 9999 120030])
    (scatS 110049 120030 120011 110047 110046 posBody)

/-- The registers written by `posTS`. -/
def BPT (r : ℕ) : Bool := decide ztyc || decide zttxj || decide (110044 ≤ r ∧ r ≤ 110049)
theorem posTS_exec (hw : WordsBounded W c) {SB A A₀ : ℕ}
    {σ : ℕ → ℕ} (hSB : c.nreg 120046 = SB) (hA : c.nreg 120030 = A) (h1 : c.nreg 120011 = 1)
    (hAl : c.nreg 9999 = A₀) (hseq : ∀ p, p < A → c.nmem zteoc = σ p) (hSA : SB + A ≤ A₀)
    (hW : A₀ + 2 * A ≤ W) (hlt : ∀ p, p < A → σ p < A)
    (hinj : ∀ p q, p < A → q < A → σ p = σ q → p = q)
    (hsurj : ∀ j, j < A → ∃ p, p < A ∧ σ p = j) :
    ∃ c' k, Exec P W posTS c c' k ∧ k ≤ 8 * A + 5 ∧ PF BPT A₀ c c' ∧ c'.nreg 9999 = A₀ + A ∧
      c'.nreg 120031 = A₀ ∧ ∀ j, j < A → c'.nmem ztdst < A ∧ σ (c'.nmem ztdst) = j := by
  obtain ⟨c₁, k₁, e₁, hk₁, n₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 120031 9999,
      .addN 9999 9999 120030]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg = upd (upd c.nreg 120031 A₀) 9999 (A₀ + A) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    · config_simp; omega
    grind
  have hr₁ : ∀ r, BPT r = false → c₁.nreg r = c.nreg r := fun r hr => by
    zuggj
    zulc
  have v31 : c₁.nreg 120031 = A₀ := by zuncb; config_simp
  have v46 : ztpmt := by rw [hr₁ _ by_decide, hSB]
  have v30 : ztpms := by rw [hr₁ _ by_decide, hA]
  have v11 : ztdxr := by rw [hr₁ _ by_decide, h1]
  let J : Config → Prop := JK c₁ (fun r => decide zttxj || decide ztogf) A₀
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, rr₂, mm₂, rm₂, o₂, -, -⟩ := scatS_exec (P := P) (W := W)
    (ri := 110049) (rn := 120030) (r1 := 120011) (ra := 110047) (rv := 110046) (body := posBody)
    (B := fun r => decide (110044 ≤ r ∧ r ≤ 110047)) by_decide by_decide by_decide
    by_decide by_decide J A₀
    (fun d d' hJ hr hm => JK.stable (rs := [110049]) (fun r hr' => by
      grind) hJ (fun r a b => hr r a by_grind) hm)
    (n := A) (κ := 4) (fun p => A₀ + σ p) (fun p => p) ztbeo
    (fun i d hi hJ hwd hri => by
      have g31 : d.nreg 120031 = A₀ := by rw [hJ.1 _ by_decide, v31]
      have g46 : ztpoa := by rw [hJ.1 _ by_decide, v46]
      have gm : d.nmem ztnpe = σ i := by rw [hJ.2 _ by_omega, m₁, hseq i hi]
      have hσ := hlt i hi
      obtain ⟨d', k', e', hk', v1, v2⟩ : ∃ d' k', Exec P W posBody d d' k' ∧ k' = 4 ∧
          d'.nreg 110047 = A₀ + σ i ∧ d'.nreg 110046 = i := by
        unfold posBody
        exec_block
        · omega
        · config_simp; zuntd; omega
        · zuknv
          · config_simp; zuntd
          tauto
      exact zthmu)
    e₁.wb_right ztdkz v30 v11 by_omega
  refine ⟨c₂, _, .seq e₁ e₂, by_nlinarith, ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_,
    by grind, by_grind⟩, ?_, ?_, fun j hj => ?_⟩
  · zuggj
    zunkm; exact hr₁ r (by simp [BPT]; omega)
  · rw [rr₂ r (by simp only [BPT, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢; omega),
      rr₁]
  · zugwm
  · rw [r₂ _ by_decide by_decide, n₁]; config_simp
  · grind
  · obtain ⟨p, hp, hpj⟩ := hsurj j hj
    have := scat_at (m := c₁.nmem) (g := fun p => A₀ + σ p) (f := fun p => p) hp
      by_grind
    try simp only at this
    rw [mm₂, ← hpj, this]
    omega

/-! ## The table of powers -/

/-- The body of the table loop: `TB[j] := x`, `x := 2 x`, `j := j + 1`. -/
def tbBody : Stmt :=
  block [.addN 110042 120041 120042, .storeN 110042 110040, .addN 110040 110040 110040,
    .addN 120042 120042 120011]

/-- **The table of powers** `2 ^ j` for `2 ^ j ≤ A + K` at the allocator (`120041`), its length
`L = ⌈log₂ (A + K + 1)⌉` in `120042`. -/
def tbS : Stmt :=
  .seq (block [.copyN 120041 9999, .constN 120042 0, .constN 110040 1, .addN 110041 120030 120039,
      .addN 110041 110041 120011])
    (.seq (.whileLtN 110040 110041 tbBody) (.instr (.addN 9999 9999 120042)))

/-- The registers written by `tbS`. -/
def BTB (r : ℕ) : Bool :=
  decide ztyc || decide (r = 120041) || decide (r = 120042) || decide (110040 ≤ r ∧ r ≤ 110042)
theorem clog_succ_le (x : ℕ) : Nat.clog 2 zthf ≤ Nat.clog 2 x + 1 := by
  rw [Nat.clog_le_iff_le_pow by_norm_num, pow_succ]
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have := Nat.le_pow_clog (by norm_num : 1 < 2) x
    omega
theorem tbS_exec (hw : WordsBounded W c) {A K A₀ : ℕ}
    (hA : c.nreg 120030 = A) (hK : c.nreg 120039 = K) (h1 : c.nreg 120011 = 1)
    (hAl : c.nreg 9999 = A₀) (hW : A₀ + 2 * ztsus + 4 ≤ W) :
    ∃ c' k, Exec P W tbS c c' k ∧ k ≤ 8 * Nat.clog 2 ztcsr + 12 ∧ PF BTB A₀ c c' ∧
      c'.nreg 9999 = A₀ + Nat.clog 2 ztcsr ∧ c'.nreg 120041 = A₀ ∧
      c'.nreg 120042 = Nat.clog 2 ztcsr ∧
      (∀ j, j < Nat.clog 2 ztcsr → c'.nmem ztdst = 2 ^ j) ∧
      A < 2 ^ Nat.clog 2 ztcsr ∧ K < 2 ^ Nat.clog 2 ztcsr := by
  set Lf := Nat.clog 2 _ with hLf
  have hLpow : A + K + 1 ≤ 2 ^ Lf := Nat.le_pow_clog by_norm_num _
  have hLle : Lf ≤ A + K + 1 := by
    zufnd

  obtain ⟨c₁, k₁, e₁, hk₁, n₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 120041 9999,
      .constN 120042 0, .constN 110040 1, .addN 110041 120030 120039,
      .addN 110041 110041 120011]) c c₁ k₁ ∧ k₁ = 5 ∧
      c₁.nreg = upd (upd (upd (upd c.nreg 120041 A₀) 120042 0) 110040 1) 110041 ztcsr ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    · omega
    · omega
    · config_simp; omega
    · config_simp; omega
    simp_all
  have hr₁ : ∀ r, BTB r = false → c₁.nreg r = c.nreg r := fun r hr => by
    zuggm
    zulc
  -- the loop
  let I : Config → Prop := fun d => WordsBounded W d ∧ ∃ j, d.nreg 120042 = j ∧
    d.nreg 110040 = 2 ^ j ∧ j ≤ Lf ∧ ztgno ∧
    (∀ r, r ≠ 110040 → r ≠ 110042 → r ≠ 120042 → d.nreg r = c₁.nreg r) ∧
    ztiuh ∧ d.rreg = c₁.rreg ∧ d.rmem = c₁.rmem ∧
    d.output = c₁.output
  have I₁ : ztkzz := ⟨e₁.wb_right, 0, by_simp_all, by_simp_all,
    Nat.zero_le _, by_omega, by_omega,
    by omega, rfl, rfl, rfl⟩
  obtain ⟨c₂, k₂, e₂, ⟨w₂, j, hj, hx, hjL, htab, hr₂, hm₂, rr₂, rm₂, o₂⟩, hstop, hk₂⟩ :=
    Exec.whileLtN_potential (P := P) (W := W) (a := 110040) (b := 110041) (body := tbBody) I
      (fun d => ztrjx * 7) ztesk
      (fun d ⟨hwd, j, hj, hx, hjL, htab, hr, hm, rr, rm, o⟩ ht => by
        have g41 : d.nreg 120041 = A₀ := by_simp_all
        have g11 : ztuti := by_simp_all
        have gl : d.nreg 110041 = A + K + 1 := by
          simp_all
        rw [hx, gl] at ht
        have hjl : j < Lf := by_grind
        obtain ⟨d', k', e', hk', n', m', rr', rm', o'⟩ : ∃ d' k', Exec P W tbBody d d' k' ∧ k' = 4 ∧
            d'.nreg = upd (upd (upd d.nreg 110042 ztdst) 110040 (2 ^ j + 2 ^ j)) 120042 ztl ∧
            d'.nmem = upd d.nmem ztdst ztssr ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧
            d'.output = d.output := by
          unfold tbBody
          exec_block
          · omega
          · config_simp; omega
          · config_simp; omega
          grind
        refine ⟨d', k', e', ⟨e'.wb_right, j + 1, by_simp_all, ?_, by_omega,
          fun t ht' => ?_, fun r a b c' => ?_, fun a ha => ?_, by_simp_all, by_simp_all,
          by simp_all⟩, ?_⟩
        · rw [n']; config_simp; omega
        · zugwb
          zuidr
          · zurj
          · rw [show t = j by omega, upd_same]
        · simp_all
        · rw [m', upd_other _ _ _ by_omega]; simp_all
        · show (Lf - d'.nreg 120042) * 7 + k' + 2 ≤ ztrjx * 7
          rw [hj, show d'.nreg 120042 = j + 1 by rw [n']; config_simp]
          omega)
      I₁
  -- the end of the loop
  have gl : c₂.nreg 110041 = A + K + 1 := by
    simp_all
  rw [hx, gl] at hstop
  have hjL' : j = Lf := by
    have : Lf ≤ j := by rw [hLf, Nat.clog_le_iff_le_pow by_norm_num]; omega
    omega
  subst hjL'
  zujwq
  have a42 : c₁.nreg 120042 = 0 := by_simp_all
  rw [a42, Nat.sub_zero] at hk₂
  have g9 : zturo := by_simp_all
  have e₃ := Exec.addN (P := P) w₂ 9999 9999 120042 by_omega
  refine ⟨_, _, .seq e₁ ztcr, by_omega, ⟨fun r hr => ?_, fun r _ => ?_, fun a ha => ?_,
    fun a _ => by_grind, by_grind⟩, ?_, ?_, ?_, fun t ht => ?_,
    by omega, by_omega⟩
  · zuggm
    config_simp
    rw [upd_other _ _ _ by_omega, hr₂ r by_omega by_omega by_omega]
    exact hr₁ r (by simp [BTB]; omega)
  · grind
  · grind
  · config_simp; omega
  · config_simp; rw [hr₂ _ by_decide by_decide by_decide, n₁]; config_simp
  · config_simp; exact hj
  grind
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ
@[expose] public section
noncomputable def fpos (ρ : ℕ → ℕ) (p : ℕ) : ℕ := by
  classical
  exact Nat.find (by simp_all : ∃ q, ρ q = ρ p)
variable (ρ : ℕ → ℕ) (A : ℕ) {P : Polygon} {W : ℕ} {c : Config}
theorem fpos_spec (p : ℕ) :
    ρ (fpos ρ p) = ρ p ∧ fpos ρ p ≤ p ∧ ∀ q, ρ q = ρ p → fpos ρ p ≤ q := by
  classical
  unfold fpos
  refine ⟨by_grind, Nat.find_min' _ rfl, fun q hq => ?_⟩
  exact Nat.find_min' _ hq
open Classical in
/-- The star chord of spine position `p`. -/
noncomputable def starOf (ρ : ℕ → ℕ) (p : ℕ) : Option ztw :=
  if fpos ρ p + 2 ≤ p then some ztqna else none

/-- **The inner chords.** -/
noncomputable def starList (ρ : ℕ → ℕ) (A : ℕ) : List ztw := emitted ztwfc A
theorem mem_starList {ρ : ℕ → ℕ} {A : ℕ} {c : ℕ × ℕ} :
    c ∈ starList ρ A ↔ c.2 < A ∧ c.1 = fpos ρ c.2 ∧ fpos ρ c.2 + 2 ≤ c.2 := by
  unfold starList
  zulqm

  · rintro ⟨j, hj, hφ⟩
    unfold starOf at hφ
    grind
  · zuei
    refine ⟨c.2, h1, ?_⟩
    unfold starOf
    grind

/-- Emitted pairs whose second component is the index have no repetition. -/
theorem emitted_nodup {φ : ℕ → Option ztw} (h : ∀ i x, φ i = some x → x.2 = i) (n : ℕ) :
    (emitted φ n).Nodup := by
  zulbq

  rw [← h a b hb, ← h a' b hb']
theorem starList_nodup : (starList ρ A).Nodup :=
  emitted_nodup (fun i x hx => by
    unfold starOf at hx; grind) A
theorem starList_length : (starList ρ A).length ≤ A :=
  emitted_length_le _ A

/-- **The star chords are complete**: every spine position is its region's first, or joined to it
by a star chord or a spine edge. -/
theorem starList_complete {A p : ℕ} (hp : p < A) :
    fpos ρ p = p ∨ ztqna ∈ starList ρ A ∨ p = fpos ρ p + 1 := by
  have := (fpos_spec ρ p).2.1
  by_cases h : fpos ρ p + 2 ≤ p
  · exact Or.inr (Or.inl (mem_starList.2 by_simp_all))
  · omega

/-! ## The region of a spine position -/

/-- `110065 := ρ p` for the spine position `p` in `110063`: `AB[5 SB[p]]` (scratch `110064`). -/
def rgS : Stmt :=
  block [.addN 110064 120046 110063, .loadN 110064 110064, .addN 110065 110064 110064,
    .addN 110065 110065 110065, .addN 110065 110065 110064, .addN 110065 110065 120044,
    .loadN 110065 110065]

/-- The memory facts of the arc and sequence tables. -/
structure RgMem (m : ℕ → ℕ) (AB SB A : ℕ) (σ rg : ℕ → ℕ) : Prop where
  seq : ∀ p, p < A → m zteoc = σ p
  σ_lt : ∀ p, p < A → σ p < A
  reg : ∀ j, j < A → m (AB + 5 * j) = rg j
theorem rgS_exec {d : Config} (hwd : WordsBounded W d) {AB SB A p : ℕ}
    {σ rg : ℕ → ℕ} (hM : RgMem d.nmem AB SB A σ rg) (hAB : d.nreg 120044 = AB)
    (hSB : d.nreg 120046 = SB) (hp : d.nreg 110063 = p) (hpA : p < A) (hSW : SB + A ≤ W)
    (hAW : AB + 5 * A ≤ W) :
    ∃ d' k, Exec P W rgS d d' k ∧ k = 7 ∧
      FrameB (fun r => decide (r = 110064 ∨ r = 110065)) d d' ∧ d'.nreg 110065 = rg ztibw := by
  have hσ := hM.σ_lt p hpA
  have hs := hM.seq p hpA
  have hr := hM.reg _ hσ
  obtain ⟨d', k, e, hk, v⟩ : ∃ d' k, Exec P W rgS d d' k ∧ k = 7 ∧ d'.nreg 110065 = rg (σ p) := by
    unfold rgS
    exec_block
    · omega
    · config_simp; grind
    · config_simp; grind
    · config_simp; grind
    · config_simp; grind
    · zubee
      config_simp; grind
  exact ⟨d', k, e, hk, exec_frameB e by_decide, v⟩

/-! ## The first position of each region -/

/-- The body: `p := A - 1 - i`, address `FR + ρ p`, value `p`. -/
def frBody : Stmt :=
  .seq ztiqu
    (.seq rgS ztjol)

/-- **The table of first positions** at the allocator (`110060`), `R` words (`R` in `110061`). -/
def frS : Stmt :=
  .seq (block [.addN 110062 120014 120048, .loadN 110061 110062, .copyN 110060 9999,
      .addN 9999 9999 110061])
    (scatS 110069 120030 120011 110067 110066 frBody)

/-- The registers written by `frS`. -/
def BFR (r : ℕ) : Bool := decide ztyc || decide (110060 ≤ r ∧ r ≤ 110069)
theorem frS_exec (hw : WordsBounded W c) {NB AB SB A R A₀ : ℕ}
    {σ rg : ℕ → ℕ} (hM : RgMem c.nmem AB SB A σ rg) (hNB : c.nreg 120014 = NB)
    (h2 : c.nreg 120048 = 2) (hR : c.nmem ztnng = R) (hAB : c.nreg 120044 = AB)
    (hSB : c.nreg 120046 = SB) (hA : c.nreg 120030 = A) (h1 : c.nreg 120011 = 1)
    (hAl : c.nreg 9999 = A₀) (hNBA : NB + 2 < A₀) (hSA : SB + A ≤ A₀) (hABA : AB + 5 * A ≤ A₀)
    (hρR : ∀ p, p < A → rg ztibw < R) (hW : A₀ + R + A ≤ W) :
    ∃ c' k, Exec P W frS c c' k ∧ k ≤ 16 * A + 8 ∧ PF BFR A₀ c c' ∧ c'.nreg 9999 = A₀ + R ∧
      c'.nreg 110060 = A₀ ∧
      ∀ p, p < A → c'.nmem (A₀ + rg ztibw) = fpos ztcdf p := by
  zuenh
  obtain ⟨c₁, k₁, e₁, hk₁, n₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W (block [.addN 110062 120014 120048,
      .loadN 110061 110062, .copyN 110060 9999, .addN 9999 9999 110061]) c c₁ k₁ ∧ k₁ = 4 ∧
      c₁.nreg = upd (upd (upd (upd c.nreg 110062 ztnng) 110061 R) 110060 A₀) 9999 (A₀ + R) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    · omega
    · config_simp; grind
    simp_all
  have hr₁ : ztjbg := fun r hr => by
    zuggg
    zulc
  have v60 : c₁.nreg 110060 = A₀ := by_simp_all
  zucba

  let K : ℕ → Bool := fun r => decide zttxi || decide zttxk || decide ztogf ||
    decide (r = 120030) || decide ztoge
  zufxs
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, rr₂, mm₂, rm₂, o₂, -, -⟩ := scatS_exec (P := P) (W := W)
    (ri := 110069) (rn := 120030) (r1 := 120011) (ra := 110067) (rv := 110066) (body := frBody)
    (B := fun r => decide (110063 ≤ r ∧ r ≤ 110067)) by_decide by_decide by_decide
    by_decide by_decide J A₀
    (fun d d' hJ hr hm => JK.stable (rs := [110069]) (fun r hr' => by
      grind) hJ
      ztdod hm)
    (n := A) (κ := 12) (fun i => A₀ + ρ ztelo) (fun i => A - 1 - i) ztbeo
    (fun i d hi hJ hwd hri => by
      have g60 : d.nreg 110060 = A₀ := by zunzu
      zubnk

      have g30 : d.nreg 120030 = A := by rw [hJ.1 _ by_decide, v30]
      have g11 : ztuti := by rw [hJ.1 _ by_decide, v11]
      have hMd : ztpld := ⟨fun p hp => by
          zuncd; exact hM.seq p hp, hM.σ_lt,
        fun j hj => by zuncd; exact hM.reg j hj⟩
      obtain ⟨d₁, k₁', e₁', hk₁', n₁', -⟩ : ∃ d₁ k₁', Exec P W
          ztiqu d d₁ k₁' ∧ k₁' = 2 ∧
          d₁.nreg = upd d.nreg 110063 ztelo ∧ True := by
        exec_block
        simp_all
      have f₁' : ∀ r, r ≠ 110063 → d₁.nreg r = d.nreg r := by_simp_all
      have hm₁' :=
        (exec_frameB e₁' (B := fun r => decide (r = 110063)) by_decide).2.2.1
      obtain ⟨d₂, k₂', e₂', hk₂', f₂', v₂'⟩ := rgS_exec (P := P) e₁'.wb_right (p := A - 1 - i)
        (by rw [hm₁']; omega) by_simp_all
        by_simp_all by_simp_all by_omega by_omega
        by_omega
      have hρl := hρR ztelo by_omega
      obtain ⟨d₃, k₃', e₃', hk₃', v67, v66⟩ : ∃ d₃ k₃', Exec P W
          ztjol d₂ d₃ k₃' ∧ k₃' = 2 ∧
          d₃.nreg 110067 = A₀ + ρ ztelo ∧ d₃.nreg 110066 = A - 1 - i := by
        have a60 : d₂.nreg 110060 = A₀ := by rw [f₂'.1 _ by_decide, f₁' _ by_decide, g60]
        have a63 : d₂.nreg 110063 = A - 1 - i := by rw [f₂'.1 _ by_decide, n₁']; config_simp
        zumfy
        exec_block
        · omega
        simp_all
      have ex : Exec P W frBody d d₃ _ := .seq e₁' (.seq e₂' e₃')
      exact ⟨d₃, _, ex, by_omega, exec_frameB ex by_decide, v67, v66⟩)
    e₁.wb_right ztdkz v30 v11 by_omega
  refine ⟨c₂, _, .seq e₁ e₂, by_nlinarith, ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_,
    by grind, by_grind⟩, ?_, ?_, fun p hp => ?_⟩
  · zuggg
    zunkm; exact hr₁ r (by simp [BFR]; omega)
  · rw [rr₂ r (by simp only [BFR, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢; omega),
      rr₁]
  · zugwm
  · rw [r₂ _ by_decide by_decide, n₁]; config_simp
  · grind
  · -- the last store at the region of `p` is that of its first position
    obtain ⟨hf1, hf2, hf3⟩ := fpos_spec ρ p
    set q := fpos ρ p
    have hq : q < A := by_omega
    have := scat_at (m := c₁.nmem) (g := fun i => A₀ + ρ ztelo) (f := fun i => A - 1 - i)
      (n := A) (i := A - 1 - q) by_omega by_grind
    rw [show A - 1 - (A - 1 - q) = q by omega, hf1] at this
    rw [mm₂, this]

/-! ## The emission of the star chords -/

/-- The body: the region of `p`, its first position `f = FR[ρ p]`, the flag `f + 2 ≤ p`. -/
def iBody : Stmt :=
  .seq (.instr (.copyN 110063 110079))
    (.seq rgS (.seq (block [.addN 110070 110060 110065, .loadN 110076 110070, .copyN 110077 110063,
        .addN 110071 110076 120011])
      (.ifLtN 110071 110063 ztote ztotd)))

/-- The capacity of the chord arrays. -/
def chCap (A : ℕ) : ℕ := 3 * A + 5

/-- **The inner chords**: two chord arrays of capacity `3 A + 5` at the allocator (bases `110072`,
`110073`, capacity `110080`), and the star chords emitted into them (count `110074`). -/
def iS : Stmt :=
  .seq (block [.copyN 110072 9999, .addN 110073 120030 120030, .addN 110073 110073 120030,
      .constN 110071 5, .addN 110073 110073 110071, .copyN 110080 110073,
      .addN 110073 110073 110072, .addN 9999 110073 110080, .constN 110074 0])
    (emitS 110079 120030 120011 110078 110076 110077 110072 110073 110074 110075 iBody)

/-- The registers written by `iS`. -/
def BIS (r : ℕ) : Bool := decide ztyc || decide (110063 ≤ r ∧ r ≤ 110080)
theorem iS_exec (hw : WordsBounded W c) {AB SB A R FR A₀ : ℕ}
    {σ rg : ℕ → ℕ} (hM : RgMem c.nmem AB SB A σ rg) (hAB : c.nreg 120044 = AB)
    (hSB : c.nreg 120046 = SB) (hA : c.nreg 120030 = A) (h1 : c.nreg 120011 = 1)
    (hFR : c.nreg 110060 = FR) (hAl : c.nreg 9999 = A₀) (hSA : SB + A ≤ A₀) (hABA : AB + 5 * A ≤ A₀)
    (hFRA : FR + R ≤ A₀) (hρR : ∀ p, p < A → rg ztibw < R)
    (hfr : ∀ p, p < A → c.nmem (FR + rg ztibw) = fpos ztcdf p)
    (hW : A₀ + 2 * chCap A ≤ W) :
    ∃ c' k, Exec P W iS c c' k ∧ k ≤ 30 * A + 15 ∧ PF BIS A₀ c c' ∧
      c'.nreg 9999 = A₀ + 2 * chCap A ∧ c'.nreg 110072 = A₀ ∧ c'.nreg 110073 = A₀ + chCap A ∧
      c'.nreg 110080 = chCap A ∧
      c'.nreg 110074 = (starList ztcdf A).length ∧
      PairsAt c'.nmem A₀ ztrio ztzxy := by
  zuenh
  obtain ⟨c₁, k₁, e₁, hk₁, n₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 110072 9999,
      .addN 110073 120030 120030, .addN 110073 110073 120030, .constN 110071 5,
      .addN 110073 110073 110071, .copyN 110080 110073, .addN 110073 110073 110072,
      .addN 9999 110073 110080, .constN 110074 0]) c c₁ k₁ ∧ k₁ = 9 ∧
      c₁.nreg = upd (upd (upd (upd (upd (upd c.nreg 110072 A₀) 110073 ztrio) 110071 5)
        110080 (chCap A)) 9999 (A₀ + 2 * chCap A)) 110074 0 ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold chCap at hW ⊢
    exec_block
    · config_simp; omega
    · config_simp; omega
    · omega
    · config_simp; omega
    · config_simp; omega
    · config_simp; omega
    · omega
    · refine ztezb
      config_simp; rw [hA, hAl]
      funext r; zvmwf; grind
  have hr₁ : ∀ r, BIS r = false → c₁.nreg r = c.nreg r := fun r hr => by
    zuggh
    zulc
  have v72 : c₁.nreg 110072 = A₀ := by_simp_all
  have v73 : c₁.nreg 110073 = A₀ + chCap A := by_simp_all
  have v74 : c₁.nreg 110074 = 0 := by_simp_all
  have v80 : c₁.nreg 110080 = chCap A := by_simp_all
  have v9 : c₁.nreg 9999 = A₀ + 2 * chCap A := by_simp_all
  have v60 : c₁.nreg 110060 = FR := by_simp_all
  zucba

  let K : ℕ → Bool := fun r => decide zttxi || decide zttxk || decide ztogf ||
    decide ztoge
  zufxs
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, rr₂, cnt₂, pr₂, mm₂, rm₂, o₂, -⟩ := emitS_exec (P := P) (W := W)
    (ri := 110079) (rn := 120030) (r1 := 120011) (rf := 110078) (rv1 := 110076) (rv2 := 110077)
    (rR1 := 110072) (rR2 := 110073) (rc := 110074) (rt := 110075) (body := iBody)
    (B := fun r => decide (110063 ≤ r ∧ r ≤ 110071) || decide (110076 ≤ r ∧ r ≤ 110078))
    by_decide by_decide by_decide by_decide by_decide by_decide by_decide
    (R1 := A₀) (c₀ := 0) J
    (fun d d' hJ hr hm => JK.stable (rs := [110079, 110074, 110075]) (fun r hr' => by
      grind) hJ
      (fun r a b => hr r a by_grind by_grind by_grind)
      (fun a ha => hm a ztec))
    (n := A) (κ := 20) ztwfc
    (fun i d hi hJ hwd hri => by
      have g60 : d.nreg 110060 = FR := by zunzu
      zubnk

      have hMd : ztpld := ⟨fun p hp => by
          zuncd; exact hM.seq p hp, hM.σ_lt,
        fun j hj => by zuncd; exact hM.reg j hj⟩
      have e₀ := Exec.copyN (P := P) hwd 110063 110079
      set d₀ : Config := { d with nreg := upd d.nreg 110063 _ } with hd₀
      have f₀ : ∀ r, r ≠ 110063 → d₀.nreg r = d.nreg r := by_simp_all
      obtain ⟨d₂, k₂', e₂', hk₂', f₂', v₂'⟩ := rgS_exec (P := P) e₀.wb_right (p := i)
        hMd by_simp_all by_simp_all
        by_simp_all hi by_omega by_omega
      have hρl : ρ i < R := by_simp_all
      have hρl' : rg _ < R := hρR i hi
      have hfp : d₂.nmem (FR + ρ i) = fpos ρ i := by
        rw [f₂'.2.2.1, show d₀.nmem = d.nmem from rfl, hJ.2 _ by_omega, m₁]; simp_all
      have a60 : d₂.nreg 110060 = FR := by rw [f₂'.1 _ by_decide, f₀ _ by_decide, g60]
      have a63 : d₂.nreg 110063 = i := by rw [f₂'.1 _ by_decide, hd₀]; simp_all
      have a11 : d₂.nreg 120011 = 1 := by
        rw [f₂'.1 _ by_decide, f₀ _ by_decide, hJ.1 _ by_decide, v11]
      have hfi := (fpos_spec ρ i).2.1
      zumfy
      obtain ⟨d₃, k₃', e₃', hk₃', v76, v77, v71, v63⟩ : ∃ d₃ k₃', Exec P W
          (block [.addN 110070 110060 110065, .loadN 110076 110070, .copyN 110077 110063,
            .addN 110071 110076 120011]) d₂ d₃ k₃' ∧ k₃' = 4 ∧
          d₃.nreg 110076 = fpos ρ i ∧ d₃.nreg 110077 = i ∧ d₃.nreg 110071 = fpos ρ i + 1 ∧
          d₃.nreg 110063 = i := by
        exec_block
        · omega
        · config_simp; grind
        simp_all
      have w₃ := e₃'.wb_right
      have hcase : ∃ d₄ k₄', Exec P W (.ifLtN 110071 110063 ztote
          ztotd) d₃ d₄ k₄' ∧ k₄' ≤ 3 ∧
          d₄.nreg 110078 = (if fpos ρ i + 2 ≤ i then 1 else 0) ∧
          (∀ r, r ≠ 110078 → d₄.nreg r = d₃.nreg r) := by
        by_cases h : fpos ρ i + 2 ≤ i
        · have ht : d₃.nreg 110071 < d₃.nreg 110063 := by_omega
          exact ⟨_, _, .ifLtN_true ht (Exec.constN w₃ 110078 1 by_omega), by_omega,
            by simp_all, by_simp_all⟩
        · have ht : ¬ d₃.nreg 110071 < d₃.nreg 110063 := by_omega
          exact ⟨_, _, .ifLtN_false ht (Exec.constN w₃ 110078 0 ztbg), by_omega,
            by zvnoi; config_simp, by_simp_all⟩
      obtain ⟨d₄, k₄', e₄', hk₄', v78, r₄⟩ := hcase
      have ex : Exec P W iBody d d₄ _ := .seq e₀ ztnco
      refine ⟨d₄, _, ex, by_omega, exec_frameB ex by_decide, fun hn => ?_, fun x hx => ?_⟩
      · unfold starOf at hn
        grind
      · unfold starOf at hx
        grind)
    e₁.wb_right ztdkz v30 v11 v72 v73 v74
    ztqgi (by unfold chCap at hW ⊢; omega)
  zuewv

  refine ⟨c₂, _, .seq e₁ e₂, by_nlinarith, ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_,
    fun a ha => by_grind, by_grind⟩, ?_, ?_, ?_, ?_, cnt₂, pr₂⟩
  · zuggh
    rw [r₂ r by_grind by_omega by_omega by_omega]; exact hr₁ r (by simp [BIS]; omega)
  · rw [rr₂ r (by simp only [BIS, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢; omega),
      rr₁]
  · grind
  · grind
  · grind
  · grind
  grind
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Chazelle.Chain (sideInArc)
namespace OracleQ
variable (C : Chain) (Q : Polygon) (N : NF)

/-- The normalised pair of two spine positions, if it is not a spine edge or a loop. -/
def normP (a b : ℕ) : Option ztw :=
  if min a b + 2 ≤ max a b then some (min a b, max a b) else none
theorem normP_comm (a b : ℕ) : normP a b = normP b a := by
  zumtq
variable {a b : ℕ} {y : ℝ}
theorem normP_some {c : ℕ × ℕ} (h : normP a b = some c) :
    c.1 + 2 ≤ c.2 ∧ ((c.1 = a ∧ c.2 = b) ∨ (c.1 = b ∧ c.2 = a)) := by
  unfold normP at h
  grind
theorem normP_of_lt (h : a + 2 ≤ b) : normP a b = some ztvk := by
  zumtq
theorem normP_none_of_le_one {A a b : ℕ} (hA : A ≤ 1) (ha : a < max A 1) (hb : b < max A 1) :
    normP a b = none := by
  unfold normP; simp_all
open Classical in
/-- The arc containing the keys just before `y`. -/
noncomputable def befArc (y : ℝ) : ℕ :=
  if h : ∃ q, q < N.arcs.length ∧ Before C Q N q y then h.choose else 0
open Classical in
/-- The arc containing the keys just after `y`. -/
noncomputable def aftArc (y : ℝ) : ℕ :=
  if h : ∃ q, q < N.arcs.length ∧ After C Q N q y then h.choose else 0

/-- Some arc contains `y` in its interior. -/
def InArc (y : ℝ) : Prop :=
  ∃ q, q < N.arcs.length ∧
    sideInArc ztwlp ztwkp y
open Classical in
/-- The arc containing `y` in its interior. -/
noncomputable def inArcIdx (y : ℝ) : ℕ := if h : InArc C Q N y then h.choose else 0
theorem befArc_spec (h : ∃ q, q < N.arcs.length ∧ Before C Q N q y) :
    befArc C Q N y < N.arcs.length ∧ Before C Q N (befArc C Q N y) y := by
  unfold befArc; zunvj; grind
theorem aftArc_spec (h : ∃ q, q < N.arcs.length ∧ After C Q N q y) :
    aftArc C Q N y < N.arcs.length ∧ After C Q N (aftArc C Q N y) y := by
  unfold aftArc; zunvj; grind
theorem inArcIdx_spec (h : InArc C Q N y) :
    inArcIdx C Q N y < N.arcs.length ∧
      sideInArc (sk ztc Q N ztqrp) (ek ztc Q N ztqrp) y := by
  zumsx
theorem befArc_lt (y : ℝ) : befArc C Q N y < max N.arcs.length 1 := by
  unfold befArc; split_ifs with h
  · omega
  omega
theorem aftArc_lt (y : ℝ) : aftArc C Q N y < max N.arcs.length 1 := by
  unfold aftArc; split_ifs with h
  · omega
  omega
theorem inArcIdx_lt (y : ℝ) : inArcIdx C Q N y < max N.arcs.length 1 := by
  zumsx
open Classical in
/-- The pair of the start of arc `x`. -/
noncomputable def zipSk (x : ℕ) : Option ztw :=
  if InI C ztxya ∧
      ∃ q, q < N.arcs.length ∧ Before C Q N q ztbaro
  then normP x (befArc C Q N ztbaro) else none
open Classical in
/-- The pair of the end of arc `x`. -/
noncomputable def zipEk (x : ℕ) : Option ztw :=
  if InI C ztxwl ∧
      ∃ q, q < N.arcs.length ∧ After C Q N q ztbarn
  then normP (aftArc C Q N ztbarn) x else none
open Classical in
/-- The special pair after `6` and before `κT`. -/
noncomputable def sp1 : Option ztw :=
  if 0 < rT C ∧ (∃ p, p < N.arcs.length ∧ After C Q N p 6) ∧
      (∃ q, q < N.arcs.length ∧ Before C Q N q ztbgn)
    then normP (aftArc C Q N 6) (befArc C Q N ztbgn) else none
open Classical in
/-- The special pair after `κT` and before `2 m + 6`. -/
noncomputable def sp2 : Option ztw :=
  if (∃ p, p < N.arcs.length ∧ After C Q N p ztbgn) ∧
      (∃ q, q < N.arcs.length ∧ Before C Q N q ztcc)
    then normP (aftArc C Q N ztbgn) (befArc C Q N ztcc) else none
open Classical in
/-- The top pair at `6` and `κT`. -/
noncomputable def sp3 : Option ztw :=
  if 0 < rT C ∧ InArc C Q N 6 ∧ InArc C Q N ztbgn
    then normP ztqro ztzgf else none
open Classical in
/-- The top pair at `κT` and `2 m + 6`. -/
noncomputable def sp4 : Option ztw :=
  if InArc C Q N ztbgn ∧ InArc C Q N ztcc
    then normP ztzgf ztzgg else none
open Classical in
/-- The top pair at `6` and `2 m + 6`. -/
noncomputable def sp5 : Option ztw :=
  if InArc C Q N 6 ∧ InArc C Q N ztcc
    then normP ztqro ztzgg else none

/-- The five special pairs at the top of the tour. -/
noncomputable def zipSpO : List ztbaeq :=
  [sp1 C Q N, sp2 C Q N, sp3 C Q N, sp4 C Q N, sp5 C Q N]

/-- The special pairs. -/
noncomputable def zipSp : List ztw := (zipSpO C Q N).filterMap id

/-- **The raw zipper pairs.** -/
noncomputable def zipRaw : List ztw :=
  OracleR.emitted (zipSk C Q N) N.arcs.length ++ OracleR.emitted (zipEk C Q N) N.arcs.length ++
    zipSp C Q N
variable {C Q N}

/-- The pair of a generating case is a zipper pair, in both orders. -/
theorem pair_of_gen (hN : IsNF ztc Q N) (hP : C.P.Simple)
    (hne : (N.F ztc Q).Nonempty) {a b : ℕ} {c : ℕ × ℕ} (ha : a < N.arcs.length)
    (hb : b < N.arcs.length) (hG : ZipGen C Q N a b) (h : normP a b = some c) :
    c.1 + 2 ≤ c.2 ∧ c.2 < N.arcs.length ∧ ZipRel C Q N c.1 c.2 := by
  obtain ⟨h1, h2⟩ := normP_some h
  have hZ := zipRel_of_gen hN hP hne ha hb hG
  rcases h2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · simp_all
  · zvmws; exact ⟨by_omega, ha, hZ.symm⟩

/-- **Every raw pair is a zipper chord**: not a spine edge, in range, and a zipper pair. -/
theorem zipRaw_sound (hN : IsNF ztc Q N) (hP : C.P.Simple) {c : ℕ × ℕ}
    (hc : c ∈ zipRaw C Q N) : c.1 + 2 ≤ c.2 ∧ c.2 < N.arcs.length ∧ ZipRel C Q N c.1 c.2 := by
  zuiv
  zudgp
  swap
  · -- the empty family: at most one arc, so no pair
    exfalso
    zuivn
    zulcj
    simp only [List.mem_append, OracleR.mem_emitted, List.mem_filterMap, List.mem_cons,
      List.mem_nil_iff, or_false, id] at hc
    zubpq
    · unfold zipSk at hφ; split_ifs at hφ
      rw [normP_none_of_le_one hA by_omega (befArc_lt C Q N _)] at hφ; cases hφ
    · unfold zipEk at hφ; split_ifs at hφ
      rw [normP_none_of_le_one hA (aftArc_lt C Q N _) by_omega] at hφ; cases hφ
    · zucnc

      have n4 := normP_none_of_le_one hA ztxgz
        ztxha
      zujae
      zucef
      · unfold sp1 at ho'; simp_all
      · unfold sp2 at ho'; simp_all
      · unfold sp3 at ho'; simp_all
      · unfold sp4 at ho'; simp_all
      · unfold sp5 at ho'; simp_all
  zulcj
  simp only [List.mem_append, OracleR.mem_emitted, List.mem_filterMap, List.mem_cons,
    List.mem_nil_iff, or_false, id] at hc
  zubpq
  · unfold zipSk at hφ; split_ifs at hφ with h
    zuick
    obtain ⟨hb, hB⟩ := befArc_spec C Q N hex
    exact pair_of_gen hN hP hne hj hb ztcgy hφ
  · unfold zipEk at hφ; split_ifs at hφ with h
    zuick
    zufjk
    exact pair_of_gen hN hP hne ha hj ztcgy hφ
  · zudyp

    zucef
    · unfold sp1 at ho'; split_ifs at ho' with h
      zugpr
      zubcu
      zufjp
      have : (6 : ℝ) < κT C := by
        zugfq
        linarith
      zuhcv
    · unfold sp2 at ho'; split_ifs at ho' with h
      zuear
      zubcu
      zufjp
      zuhcv
    · unfold sp3 at ho'; split_ifs at ho' with h
      zugpr
      zupr

      have : (6 : ℝ) ≠ κT C := by
        zugfq
        grind
      exact pair_of_gen hN hP hne ha hb (Or.inl ⟨6, κT C, Or.inl rfl, Or.inr ztp, this,
        hA', hB⟩) ho'
    · unfold sp4 at ho'; split_ifs at ho' with h
      zuear
      zupr

      exact pair_of_gen hN hP hne ha hb (Or.inl ⟨κT C, 2 * C.m + 6, Or.inr ztp,
        Or.inr ztbt, by_grind, hA', hB⟩) ho'
    · unfold sp5 at ho'; split_ifs at ho' with h
      zuear
      zupr

      zukdl
      exact pair_of_gen hN hP hne ha hb (Or.inl ⟨6, 2 * C.m + 6, Or.inl rfl,
        Or.inr ztbt, by_grind, hA', hB⟩) ho'
theorem mem_zipSp {o : Option ztw} (ho : o ∈ zipSpO C Q N) {c : ℕ × ℕ} (h : o = some c) :
    c ∈ zipSp C Q N := by
  unfold zipSp; simp_all

/-- **Every zipper pair that is not a spine edge is raw.** -/
theorem zipRaw_complete (hN : IsNF ztc Q N) (hP : C.P.Simple) {p q : ℕ} (hpq : p < q)
    (hq : q < N.arcs.length) (hZ : ZipRel C Q N p q) : q = p + 1 ∨ ztkca ∈ zipRaw C Q N := by
  zuiv
  by_cases hq1 : q = p + 1
  · omega
  right
  have h2 : p + 2 ≤ q := by_omega
  have hp : p < N.arcs.length := by_omega
  have hne : (N.F ztc Q).Nonempty := by
    by_contra hF
    have := arcs_le_one_of_empty hN hGM (Set.not_nonempty_iff_eq_empty.1 hF)
    omega
  have hn := normP_of_lt h2
  have hn' : normP q p = some ztkca := by rw [normP_comm]; exact hn
  zudyp

  zukdl
  have inIdx : ∀ {r : ℕ} {y : ℝ}, r < N.arcs.length →
      sideInArc _ _ y →
      InArc C Q N y ∧ inArcIdx C Q N y = r := fun {r y} hr h => by
    have hin : InArc C Q N y := ⟨r, hr, h⟩
    zufio
    exact ⟨hin, interior_unique hN hGM hne a hr b h⟩
  have hr0 : ∀ {x : ℝ}, x ≠ κT C → x = 6 → 0 < rT C := fun {x} h1 h2 => by
    zuhqi
    zuccr
    simp_all
  unfold zipRaw
  simp only [List.mem_append, OracleR.mem_emitted]
  rcases zip_cases hN hP hne hp hq by_omega hZ with
    ⟨x, y, hx, hy, hxy, h1, h2'⟩ | ⟨hI, hB⟩ | ⟨hI, hA⟩ | ⟨h6, hA, hB⟩ | ⟨hA, hB⟩
  · right
    obtain ⟨ix, ex⟩ := inIdx hp h1
    obtain ⟨iy, ey⟩ := inIdx hq h2'
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · omega
    · exact mem_zipSp (o := sp3 C Q N) by_tauto (by
        unfold sp3; grind)
    · exact mem_zipSp (o := sp5 C Q N) by_tauto (by
        unfold sp5; simp_all)
    · exact mem_zipSp (o := sp3 C Q N) by_tauto (by
        unfold sp3; grind)
    · omega
    · exact mem_zipSp (o := sp4 C Q N) by_tauto (by
        unfold sp4; simp_all)
    · exact mem_zipSp (o := sp5 C Q N) by_tauto (by
        unfold sp5; simp_all)
    · exact mem_zipSp (o := sp4 C Q N) by_tauto (by
        unfold sp4; simp_all)
    omega
  · left; left
    refine ⟨p, hp, ?_⟩
    have hex : ztjbu :=
      ⟨q, hq, hB⟩
    obtain ⟨hb, hB'⟩ := befArc_spec C Q N hex
    unfold zipSk
    rw [ite_eq_left by_simp_all, before_unique hN hP hne hb hq hB' hB, hn]
  · left; right
    refine ⟨q, hq, ?_⟩
    have hex : ztjbt :=
      ⟨p, hp, hA⟩
    zufjk
    unfold zipEk
    rw [ite_eq_left by_simp_all, after_unique hN hP hne ha hp hA' hA, hn]
  · right
    have e1 : ∃ p', p' < N.arcs.length ∧ After C Q N p' 6 := by_grind
    have e2 : ztjbu := ztrdy
    have hr : 0 < rT C := by
      grind
    zubcu
    zufjo
    exact mem_zipSp by_tauto (by
      unfold sp1; rw [ite_eq_left by_simp_all, after_unique hN hP hne ha hp hA' hA,
        before_unique hN hP hne hb hq hB' hB, hn])
  · right
    have e1 : ztjbt := ⟨p, hp, hA⟩
    have e2 : ∃ q', q' < N.arcs.length ∧ Before C Q N q' ztcc := ztrdy
    zubcu
    zufjo
    exact mem_zipSp (o := sp2 C Q N) by_tauto (by
      unfold sp2; rw [ite_eq_left by_simp_all, after_unique hN hP hne ha hp hA' hA,
        before_unique hN hP hne hb hq hB' hB, hn])
end OracleQ
end
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ
@[expose] public section
def arcPosS : Stmt :=
  block [.addN 110200 120046 110203, .loadN 110201 110200, .addN 110202 110201 110201,
    .addN 110202 110202 110202, .addN 110202 110202 110201, .addN 110202 110202 120044,
    .addN 110202 110202 110204, .loadN 110100 110202, .addN 110202 110202 120011,
    .loadN 110101 110202]
variable {P : Polygon} {W : ℕ} {c : Config}
theorem arcPosS_exec (hw : WordsBounded W c) {AB SB A p o : ℕ}
    (hAB : c.nreg 120044 = AB) (hSB : c.nreg 120046 = SB) (h1 : c.nreg 120011 = 1)
    (hp : c.nreg 110203 = p) (hpA : p < A) (ho : c.nreg 110204 = o) (ho3 : o ≤ 3)
    (hj : c.nmem zteoc < A) (hSW : SB + A ≤ W) (hAW : AB + 5 * A ≤ W) :
    ∃ c' k, Exec P W arcPosS c c' k ∧ k = 10 ∧
      FrameB (fun r => decide (r = 110100 ∨ r = 110101 ∨ ztndz)) c c' ∧
      c'.nreg 110100 = c.nmem ztyhf ∧
      c'.nreg 110101 = c.nmem ztyao := by
  obtain ⟨c', k, e, hk, v1, v2⟩ : ∃ c' k, Exec P W arcPosS c c' k ∧ k = 10 ∧
      c'.nreg 110100 = c.nmem ztyhf ∧
      c'.nreg 110101 = c.nmem ztyao := by
    unfold arcPosS
    exec_block
    · omega
    · config_simp; grind
    · config_simp; grind
    · config_simp; grind
    · config_simp; grind
    · config_simp; grind
    · config_simp; grind
    · zuknv
      · config_simp; rw [hSB, hp, hAB, ho]; grind
      · config_simp; rw [hSB, hp, hAB, ho, h1]; grind
  exact ⟨c', k, e, hk, exec_frameB e by_decide, v1, v2⟩

/-- The flag of equal keys into `110213`. -/
def eqS : Stmt :=
  ifEq 110212 110210 (ifEq 110103 110211 ztbadl ztifq)
    ztifq
theorem eqS_exec (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W eqS c c' k ∧ k ≤ 9 ∧ FrameB ztlok c c' ∧
      c'.nreg 110213 = (if c.nreg 110212 = c.nreg 110210 ∧ c.nreg 110103 = c.nreg 110211
        then 1 else 0) := by
  have hwr : wr ztlok eqS = true := by_decide
  suffices H : ∃ c' k, Exec P W eqS c c' k ∧ k ≤ 9 ∧
      c'.nreg 110213 = (if c.nreg 110212 = c.nreg 110210 ∧ c.nreg 110103 = c.nreg 110211
        then 1 else 0) by
    zudqw

  unfold eqS
  by_cases h1 : c.nreg 110212 = c.nreg 110210
  · by_cases h2 : c.nreg 110103 = c.nreg 110211
    · exact ⟨_, _, ifEq_eq_exec h1 (ifEq_eq_exec h2 (Exec.constN hw 110213 1 hW)), by_omega,
        by simp_all⟩
    · obtain ⟨k', e', hk'⟩ := ifEq_ne_exec (P := P) (W := W) (S := .instr ztmzz) h2
        ztzbq
      exact ⟨_, _, ifEq_eq_exec h1 e', by_omega, by_simp_all⟩
  · obtain ⟨k', e', hk'⟩ := ifEq_ne_exec (P := P) (W := W)
      (S := ifEq 110103 110211 ztbadl ztifq) h1
      ztzbq
    exact ztlvg

/-- The arc before (`true`) or after (`false`) the located arc, when the flag is set, into
`110214`. -/
def adjS : Bool → Stmt
  | true => ifEq 110213 120011
      (.ifLtN 120012 120170 (.instr (.subN 110214 120170 120011))
        (.instr (.subN 110214 120030 120011)))
      ztous
  | false => ifEq 110213 120011
      (.seq (.instr (.addN 110214 120170 120011))
        (.ifLtN 110214 120030 .skip (.instr (.constN 110214 0))))
      ztous

/-- The adjusted arc. -/
def adjN (d : Bool) (A q e : ℕ) : ℕ :=
  if e = 1 then (if d then predP A q else succP A q) else q
theorem adjS_exec (hw : WordsBounded W c) (d : Bool) {A : ℕ}
    (h1 : c.nreg 120011 = 1) (h0 : c.nreg 120012 = 0) (hA : c.nreg 120030 = A)
    (hq : c.nreg 120170 < A) (hW : A + 1 ≤ W) :
    ∃ c' k, Exec P W ztjob c c' k ∧ k ≤ 12 ∧ FrameB ztlol c c' ∧
      c'.nreg 110214 = adjN d A ztvhm ztvhg := by
  have hwr : wr ztlol ztjob = true := by cases d <;> decide
  suffices H : ∃ c' k, Exec P W ztjob c c' k ∧ k ≤ 12 ∧
      c'.nreg 110214 = adjN d A ztvhm ztvhg by
    zudqw

  obtain ⟨q, hqd⟩ : ∃ q, c.nreg 120170 = q := zths
  rw [hqd] at hq ⊢
  unfold adjN
  by_cases he : c.nreg 110213 = 1
  · have he' : c.nreg 110213 = c.nreg 120011 := by_omega
    rw [ite_eq_left he]
    cases d
    · zuma
      unfold adjS
      have e1 := Exec.addN (P := P) hw 110214 120170 120011 by_omega
      zumfs
      unfold succP
      by_cases hs : q + 1 < A
      · have ht : ({ c with nreg := upd c.nreg 110214 (c.nreg 120170 + c.nreg 120011) } :
            Config).nreg 110214 < ({ c with nreg := upd c.nreg 110214 (c.nreg 120170 +
            c.nreg 120011) } : Config).nreg 120030 := by_simp_all
        exact ⟨_, _, ifEq_eq_exec he' (.seq e1 (.ifLtN_true ht (.skip w1))), by_omega,
          by simp_all⟩
      · have ht : ¬ ({ c with nreg := upd c.nreg 110214 (c.nreg 120170 + c.nreg 120011) } :
            Config).nreg 110214 < ({ c with nreg := upd c.nreg 110214 (c.nreg 120170 +
            c.nreg 120011) } : Config).nreg 120030 := by_simp_all
        exact ⟨_, _, ifEq_eq_exec he' (.seq e1 (.ifLtN_false ht
          (Exec.constN w1 110214 0 ztbg))), by_omega,
          by simp_all⟩
    · zuwa
      unfold adjS predP
      by_cases hz : q = 0
      · have ht : ¬ c.nreg 120012 < c.nreg 120170 := by_omega
        exact ⟨_, _, ifEq_eq_exec he' (.ifLtN_false ht (Exec.subN hw 110214 120030 120011)),
          by omega, by_simp_all⟩
      · have ht : c.nreg 120012 < c.nreg 120170 := by_omega
        exact ⟨_, _, ifEq_eq_exec he' (.ifLtN_true ht (Exec.subN hw 110214 120170 120011)),
          by omega, by_simp_all⟩
  · have he' : c.nreg 110213 ≠ c.nreg 120011 := by_omega
    zulqf
    cases d <;>
    · unfold adjS
      obtain ⟨k', e', hk'⟩ := ifEq_ne_exec (P := P) (W := W) he' (Exec.copyN hw 110214 120170)
      exact ztlvg

/-- The normalised pair of `110299` and `110214`: minimum `110291`, maximum `110292`, flag
`110290` (`1` iff the minimum plus two is at most the maximum). -/
def normS : Stmt :=
  .seq (.ifLtN 110299 110214 ztkrp
      ztkro)
    (.seq (.instr (.addN 110215 110291 120011))
      (.ifLtN 110215 110292 (.instr ztson) ztfel))
theorem normS_exec (hw : WordsBounded W c)
    (h1 : c.nreg 120011 = 1) (hW : c.nreg 110299 + 1 ≤ W) (hW' : c.nreg 110214 + 1 ≤ W) :
    ∃ c' k, Exec P W normS c c' k ∧ k ≤ 12 ∧
      FrameB (fun r => decide ztekh || decide ztogc) c c' ∧
      (normP ztfgn ztfgm = none → c'.nreg 110290 = 0) ∧
      ∀ x, normP ztfgn ztfgm = some x →
        c'.nreg 110290 = 1 ∧ c'.nreg 110291 = x.1 ∧ c'.nreg 110292 = x.2 := by
  have hwr : wr (fun r => decide ztekh || decide ztogc) normS = true := by
    decide
  obtain ⟨a, ha⟩ : ∃ a, c.nreg 110299 = a := zths
  obtain ⟨b, hb⟩ : ∃ b, c.nreg 110214 = b := zths
  rw [ha, hb]; rw [ha] at hW; rw [hb] at hW'
  -- the ordered pair
  obtain ⟨c₁, k₁, e₁, hk₁, v1, v2, r₁⟩ : ∃ c₁ k₁, Exec P W (.ifLtN 110299 110214
      ztkrp
      ztkro) c c₁ k₁ ∧ k₁ ≤ 4 ∧
      c₁.nreg 110291 = min a b ∧ c₁.nreg 110292 = max a b ∧
      (∀ r, r ≠ 110291 → r ≠ 110292 → c₁.nreg r = c.nreg r) := by
    by_cases h : a < b
    · have ht : c.nreg 110299 < c.nreg 110214 := by_omega
      refine spec_ifLtN_true ht ?_
      exec_block
      refine ztcqk
      · config_simp; omega
      · config_simp; omega
      simp_all
    · have ht : ¬ c.nreg 110299 < c.nreg 110214 := by_omega
      refine spec_ifLtN_false ht ?_
      exec_block
      simp_all
  zud
  zujxr
  have e₂ := Exec.addN (P := P) w₁ 110215 110291 120011 (by
    omega)
  zue
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg 110215 (c₁.nreg 110291 + c₁.nreg 120011) }
    with hc₂
  have x15 : c₂.nreg 110215 = min a b + 1 := by_simp_all
  have x92 : c₂.nreg 110292 = max a b := by_simp_all
  have x91 : c₂.nreg 110291 = min a b := by_simp_all
  by_cases hf : min a b + 2 ≤ max a b
  · have ht : c₂.nreg 110215 < c₂.nreg 110292 := by_omega
    have ex := Exec.seq e₁ (Exec.seq e₂ (Exec.ifLtN_true (e := .instr ztsom) ht
      (Exec.constN w₂ 110290 1 by_omega)))
    refine ⟨_, _, ex, by_omega, exec_frameB ex hwr, fun hn => ?_, fun x hx => ?_⟩
    · unfold normP at hn; grind
    · unfold normP at hx; rw [ite_eq_left hf] at hx; cases hx
      refine ⟨by config_simp, ?_, ?_⟩
      · simp_all
      tauto
  · have ht : ¬ c₂.nreg 110215 < c₂.nreg 110292 := by_omega
    have ex := Exec.seq e₁ (Exec.seq e₂ (Exec.ifLtN_false (t := .instr ztson) ht
      (Exec.constN w₂ 110290 0 ztbg)))
    refine ⟨_, _, ex, by_omega, exec_frameB ex hwr, fun _ => by config_simp, fun x hx => ?_⟩
    unfold normP at hx; grind
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open OracleQ
open Chazelle.Chain (sideInArc)
@[expose] public section
def endPos (N : NF) (d : Bool) (p : ℕ) : WPos :=
  if d then (N.arc ztmh).s else (N.arc ztmh).e
theorem key_endPos (C : Chain) (Q : Polygon) (N : NF) (d : Bool) (p : ℕ) :
    (chainModel C).key Q (endPos N d p) =
      if d then sk ztc Q N p else ek ztc Q N p := by
  unfold endPos sk ek; grind

/-- The register holding the offset of the end in an arc record. -/
def offR (d : Bool) : ℕ := if d then 120011 else 110205

/-- **The environment of the zipper.** -/
structure ZEnv (P : Polygon) (W lo : ℕ) (C : Chain) (N : NF) (V : QV) (c : Config) : Prop where
  good : GoodEnv P
  hW : 8 * P.n + 32 ≤ W
  CQ : C.P = Qof P
  simple : C.P.Simple
  s_lt : C.s < P.n
  isNF : IsNF ztc zta N
  loc : Robust lo c.nmem fun m => LocMemOK P V m W ztc N ∧ m ztfos = V.AB ∧
    m ztfot = V.SB
  pk : PosK P.n C.s C.m ztboi ztkdv c
  rMD : c.nreg 120040 = V.MD
  rNB : c.nreg 120014 = V.NB
  rTB : c.nreg 120041 = V.TB
  rL : c.nreg 120042 = V.L
  rA : c.nreg 120030 = V.A
  rAB : c.nreg 120044 = V.AB
  rSB : c.nreg 120046 = V.SB
  r3 : c.nreg 110205 = 3

/-- The registers the zipper environment reads. -/
def ZKeep (r : ℕ) : Bool :=
  decide ztgxn || decide ztndy || decide (r = 110205)
theorem ZEnv.stable {P : Polygon} {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c c' : Config}
    (h : ZEnv P W lo C N V c) (hr : ∀ r, ZKeep r = true → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < lo → c'.nmem a = c.nmem a) : ZEnv P W lo C N V c' where
  good := h.good
  hW := h.hW
  CQ := h.CQ
  simple := h.simple
  s_lt := h.s_lt
  isNF := h.isNF
  loc := h.loc.transport hm
  pk := h.pk.congr fun r hr' => hr r (by
    zvmwq; omega)
  rMD := by zumwn; exact h.rMD
  rNB := by zumwn; exact h.rNB
  rTB := by zumwn; exact h.rTB
  rL := by zumwn; exact h.rL
  rA := by zumwn; exact h.rA
  rAB := by zumwn; exact h.rAB
  rSB := by zumwn; exact h.rSB
  r3 := by zumwn; exact h.r3
section Facts
variable {P : Polygon} {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c : Config}
theorem ZEnv.mem (h : ZEnv P W lo C N V c) :
    LocMemOK P V c.nmem W ztc N ∧ c.nmem ztfos = V.AB ∧
      c.nmem ztfot = V.SB := h.loc.holds
theorem ZEnv.Qn (h : ZEnv P W lo C N V c) : C.P.n = P.n := by
  zuofs; exact shear_n _ _
theorem ZEnv.m_lt (h : ZEnv P W lo C N V c) : C.m < P.n := by
  have := C.m_lt; rw [h.Qn] at this; omega
theorem ZEnv.hD (h : ZEnv P W lo C N V c) : DistinctHeights C.P := by
  zuofs; exact distinctHeights_of_goodEnv h.good

/-- The ends of an arc are proper walk positions on the walk. -/
theorem ZEnv.arcEnd (h : ZEnv P W lo C N V c) {j : ℕ} (hj : j < N.arcs.length) (d : Bool) :
    let x := if d then (N.arc j).s else (N.arc j).e
    x.edge < 2 * C.m + 7 ∧ x.hgt ≤ C.P.n ∧ 0 ≤ (chainModel C).param C.P x ∧
      (chainModel C).param C.P x < 1 := by
  zuif

  zuru
  have hkey : ∀ (w : WPos), ProperPos ztc zta (Qof P).n w →
      (chainModel C).key zta w < (chainModel C).W.n → w.edge < 2 * C.m + 7 := by
    zujbr
    have : ztfkn := by
      have := hw.1
      zuckv
      linarith
    zukvd
    zufc
  zuofs
  cases d
  · exact ⟨hkey _ he harc.2.2.2.1, he.2.2, he.1, he.2.1⟩
  · exact ⟨hkey _ hs harc.2.1, hs.2.2, hs.1, hs.2.1⟩
end Facts

/-! ## The analysis of the end of the arc -/

/-- Copy the position and the offset, load the end, analyse it. -/
def prepS (d : Bool) : Stmt :=
  .seq ztihv (.seq arcPosS posA)

/-- The registers written by `prepS`. -/
def BPR (r : ℕ) : Bool := decide ztgxj || decide ztnea
theorem wr_prepS (d : Bool) : wr BPR ztmnc = true := by_rfl

/-- The end of an arc read from memory. -/
theorem ZEnv.endPos_mem {P : Polygon} {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c : Config}
    (h : ZEnv P W lo C N V c) {x : ℕ} (hx : x < V.A) (d : Bool) :
    c.nmem ztjno = sj N x ∧ sj N x < V.A ∧
      c.nmem (V.AB + 5 * c.nmem ztjno + ztdvb) = (endPos N d x).edge ∧
      c.nmem (V.AB + 5 * c.nmem ztjno + ztdvb + 1) = (endPos N d x).hgt := by
  obtain ⟨hL, hAB, hSB⟩ := h.mem
  zuivp
  zudnq
  have hnf := hL.nf
  have hlen := NFLoc.seq_length hN
  have hsq : c.nmem ztjno = sj N x := by
    rw [← hSB]; exact hnf.2.2.2.2.2.2.2.2.1 x by_omega
  have hjl : sj N x < V.A := by zvmze; exact NFLoc.seq_lt hN by_omega
  obtain ⟨-, a1, a2, a3, a4⟩ := hnf.2.2.2.2.2.2.1 (sj N x) by_omega
  refine ⟨hsq, hjl, ?_, ?_⟩ <;> rw [hsq, ← hAB] <;> cases d
  · tauto
  · tauto
  · tauto
  tauto
open Classical in
theorem prepS_exec {P : Polygon} {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c : Config}
    (hw : WordsBounded W c) (h : ZEnv P W lo C N V c) {x : ℕ} (hx : c.nreg 110299 = x)
    (hxA : x < V.A) (d : Bool) :
    ∃ c' k, Exec P W ztmnc c c' k ∧ k ≤ 80 ∧ FrameB BPR c c' ∧
      c'.nreg 110204 = ztdvb ∧ c'.nreg 110203 = x ∧
      c'.nreg 110104 = (if InI C ztxjg then 1 else 0) ∧
      ztggw =
        ((mirPos C (endPos N d x).edge (endPos N d x).hgt).edge,
          (mirPos C (endPos N d x).edge (endPos N d x).hgt).hgt) := by
  obtain ⟨hL, -, -⟩ := h.mem
  have hk := h.pk
  -- the copies
  obtain ⟨c₀, e₀, v03, v04, r₀⟩ : ∃ c₀, Exec P W (block [.copyN 110203 110299,
      .copyN 110204 (offR d)]) c c₀ 2 ∧ c₀.nreg 110203 = x ∧
      c₀.nreg 110204 = ztdvb ∧ FrameB BPR c c₀ := by
    have hwr : wr BPR ztihv = true := by
      rfl
    suffices H : ∃ c₀ k, Exec P W _ c c₀ k ∧
        k = 2 ∧ c₀.nreg 110203 = x ∧ c₀.nreg 110204 = ztdvb by
      obtain ⟨c₀, k, e, hk', a, b⟩ := H
      zujpq
      exact ⟨c₀, e, a, b, exec_frameB e hwr⟩
    cases d
    · simp only [offR, Bool.false_eq_true, ite_false]
      exec_block
      refine ztkw <;> config_simp
      · zufsg
      · exact h.r3
    · simp only [offR, ite_true]
      exec_block
      refine ztkw <;> config_simp
      · zufsg
      · exact hk.one
  have h₀ := h.stable (fun r hr => r₀.1 r (by
    zucqx
    zunwi; omega))
    (fun a _ => by rw [r₀.2.2.1])
  obtain ⟨hsq, hjl, hwv, hhv⟩ := h₀.endPos_mem hxA d
  have hTB := hL.TB_le
  have hSBl := hL.SB_le
  have hABl := hL.AB_le
  obtain ⟨-, hAB', hSB'⟩ := h.mem
  rw [hSB'] at hSBl
  rw [hAB'] at hABl
  zuivp
  -- the load
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, v₁, v₁'⟩ := arcPosS_exec (P := P) e₀.wb_right (AB := V.AB)
    (SB := V.SB) (A := V.A) (p := x) (o := if d then 1 else 3) h₀.rAB h₀.rSB h₀.pk.one v03 hxA v04
    by_grind by_omega by_omega by_omega
  rw [hwv] at v₁; rw [hhv] at v₁'
  have h₁ := h₀.stable (fun r hr => f₁.1 r (by
    zvmwq at hr; grind))
    ztdnq
  -- the analysis
  zubb
  zuiyk
  zuec
  zubwh
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, fl₂, rest₂⟩ := posA_exec (P := P) e₁.wb_right h₁.pk hm1 hmn h.s_lt hS
    hR (by have := h.hW; omega)
  set w := (endPos N d x).edge
  set hc := (endPos N d x).hgt
  obtain ⟨hw7, hh, hp0, hp1⟩ := h₀.arcEnd (j := sj N x) by_omega d
  have hwe : ztdrf := by
    rfl
  zuhma
  rw [v₁] at fl₂ rest₂
  obtain ⟨z₁, z₂, z₃⟩ := rest₂ by_omega
  rw [v₁'] at z₂ z₃
  have hz : c₂.nreg 110103 = nz C w hc := by rw [z₂, ← nzN_eq, h.Qn]
  have ex : Exec P W ztmnc c c₂ _ := .seq e₀ ztyv
  refine ⟨c₂, _, ex, by_omega, exec_frameB ex (wr_prepS d), ?_, ?_, ?_, ?_⟩
  · rw [f₂.1 _ by_decide, f₁.1 _ by_decide, v04]
  · rw [f₂.1 _ by_decide, f₁.1 _ by_decide, v03]
  · rw [fl₂, hz]
    have hiff := inI_iff C h.hD hw7 hh ztuhx
    have : (chainModel C).key C.P _ = (chainModel C).key C.P ztbfp := rfl
    zubk
    by_cases hI : InI C ztxjf
    · rw [ite_eq_left hI, ite_eq_left ((inT_eq C _ _).2 (hiff.1 hI))]
    · rw [ite_eq_right hI, ite_eq_right (fun h' => hI (hiff.2 ((inT_eq C _ _).1 h')))]
  · rw [z₃, hz, mirN_eq]

/-! ## The located part -/

/-- Locate the mirror, test the end of the located arc, adjust, normalise. -/
def locS (d : Bool) : Stmt :=
  .seq (block [.copyN 110210 110105, .copyN 110211 110106, .copyN 50000 120040,
      .copyN 50001 120014, .copyN 50002 110105, .copyN 50003 110106])
    (.seq myLoc (.seq (.instr (.copyN 110203 120170)) (.seq arcPosS
      (.seq ztkrn
        (.seq posA (.seq eqS (.seq ztjob normS)))))))

/-- The registers written by `locS`. -/
def BLS (r : ℕ) : Bool :=
  BL r || decide ztgxj || decide ztnea ||
    decide (110210 ≤ r ∧ r ≤ 110215) ||
    decide ztekh || decide ztgzd
theorem inTest_range {C : Chain} {z w : ℕ} (h : inTest C z w) : 6 ≤ w ∧ w < 2 * C.m + 6 := by
  have := rT_lt C
  unfold inTest at h; grind
theorem BL_keep {r : ℕ} (h : ZKeep r = true ∨ r = 110204 ∨ r = 110299 ∨ (110210 ≤ r ∧ r ≤ 110212)
    ∨ ztgxk) : BL r = false := by
  zubis
  zunfi
  omega
open Classical in
theorem locS_exec {P : Polygon} {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c : Config}
    (hw : WordsBounded W c) (h : ZEnv P W lo C N V c) {x : ℕ} (hx : c.nreg 110299 = x)
    (hxA : x < V.A) (d : Bool) (ho : c.nreg 110204 = if d then 1 else 3)
    (hI : InI C ztxjg)
    (hmir : (c.nreg 110105, c.nreg 110106) =
        ((mirPos C (endPos N d x).edge (endPos N d x).hgt).edge,
          (mirPos C (endPos N d x).edge (endPos N d x).hgt).hgt)) :
    ∃ c' k, Exec P W ztqtc c c' k ∧ k ≤ 5500 * ztbts + 300 ∧ FrameB BLS c c' ∧
      ∃ q, q < V.A ∧ ((N.F ztc zta).Nonempty →
        (if d then Before C zta N q ztbarm
          else After C zta N q ztbarm)) ∧
      (normP x q = none → c'.nreg 110290 = 0) ∧
      ∀ z, normP x q = some z → c'.nreg 110290 = 1 ∧ c'.nreg 110291 = z.1 ∧ c'.nreg 110292 = z.2 := by
  obtain ⟨hL, hAB', hSB'⟩ := h.mem
  zuhxe

  zuivp
  set w := (endPos N d x).edge with hwdef
  set hc := (endPos N d x).hgt with hcdef
  set Y := mirPos C w hc with hYdef
  -- the end and its mirror
  obtain ⟨hsq, hjl, -, -⟩ := h.endPos_mem hxA d
  obtain ⟨hw7, hh, hp0, hp1⟩ := h.arcEnd (j := sj N x) by_omega d
  have hwe : ztdrf := by
    rfl
  zuhma
  have hkey : (chainModel C).key C.P ztcdb = (chainModel C).key C.P ztbfp := rfl
  rw [hkey] at hI
  have hrange := inTest_range ((inI_iff C hD (w := w) hw7 hh by_simp_all).1 hI)
  obtain ⟨hYk, hYp0, hYp1, hYh, hY6, hY7, -⟩ := mir_key C hD hrange.1 hrange.2 hh ztuhx
  have hYnz := nz_mir C hD hrange.1 hrange.2 hh by_simp_all
  rw [← hYdef] at hYk hYp0 hYp1 hYh hY6 hY7 hYnz
  simp only [Prod.mk.injEq] at hmir
  obtain ⟨m5, m6⟩ := hmir
  -- 1. the copies
  obtain ⟨c₁, k₁, e₁, hk₁, n₁, mm₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 110210 110105,
      .copyN 110211 110106, .copyN 50000 120040, .copyN 50001 120014, .copyN 50002 110105,
      .copyN 50003 110106]) c c₁ k₁ ∧ k₁ = 6 ∧
      c₁.nreg = upd (upd (upd (upd (upd (upd c.nreg 110210 Y.edge) 110211 Y.hgt) 50000 V.MD)
        50001 V.NB) 50002 Y.edge) 50003 Y.hgt ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    refine ztezb
    config_simp; rw [m5, m6, h.rMD, h.rNB]
  have R₁ : ∀ r, r ≠ 110210 → r ≠ 110211 → (r < 50000 ∨ 50003 < r) → c₁.nreg r = c.nreg r :=
    fun r a b c' => by zuncb; zvmwf; grind
  have h₁ := h.stable (fun r hr => R₁ r (by
      zvmwq at hr; omega) (by
      zvmwq at hr; omega) (by
      zvmwq at hr; omega))
    by_simp_all
  zud
  -- 2. the double identification
  zuhxq

  zuc
  have hx50 : ProperPos ztc zta P.n ⟨c₁.nreg 50002, c₁.nreg 50003⟩ := by
    zuncb; config_simp; zvnoq
    exact ⟨hYp0, hYp1, by_simp_all⟩
  zuru
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hq₂, loc1, loc2⟩ := myLoc_exec arcCover (P := P) (W := W) (c := c₁)
    w₁ ⟨h.good, by_omega, by zuncb; config_simp; have := hL.md_le; omega,
      by zungp; config_simp; exact hL.chwf, chainModel C,
      by zungp; config_simp; exact hL.md, by zuncb; config_simp; omega⟩
    h.good by_omega (by rw [n₁, mm₁]; config_simp; exact hL.md) hL.good
    (by rw [n₁, mm₁]; config_simp; exact hL.nf) h.isNF hx50 hL.st
    (by zunzv; exact h.rTB)
    (by zunzv; exact h.rL) h₁.pk.zero h₁.pk.one
    ztmdu ztlje
    (by rw [n₁]; config_simp; exact hL.NB_le) (by rw [n₁, mm₁]; config_simp; rw [← hA]; exact hL.AB_le)
    (by rw [n₁, mm₁]; config_simp; rw [← hA]; exact hL.SB_le) hTB
  have g50 : c₁.nreg 50002 = Y.edge ∧ c₁.nreg 50003 = Y.hgt := by
    zuncb; simp
  rw [g50.1, g50.2] at loc1 loc2
  obtain ⟨q0, hq0d⟩ : ztprf := by_grind
  zuikn
  have hq0A : q0 < V.A := by_omega
  zumaq
  have h₂ := h₁.stable (fun r hr => R₂ r (BL_keep ztcgw))
    ztlnw
  have mm₂ := f₂.2.2.1.trans mm₁
  -- 3.–4. the end of the located arc
  have e₃ := Exec.copyN (P := P) e₂.wb_right 110203 120170
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 110203 _ } with hc₃
  have R₃ : ∀ r, r ≠ 110203 → c₃.nreg r = c₂.nreg r := fun r hr => by
    zumwr; exact upd_other _ _ _ hr
  have h₃ := h₂.stable (fun r hr => R₃ r (by
    zvmwq at hr; omega)) by_grind
  zueix
  have o₃ : c₃.nreg 110204 = if d then 1 else 3 := by
    rw [R₃ _ by_decide, R₂ _ ztmaj, R₁ _ by_decide by_decide
      by_decide, ho]
  obtain ⟨hL₃, -, -⟩ := h₃.mem
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, v₄, v₄'⟩ := arcPosS_exec (P := P) e₃.wb_right (AB := V.AB)
    (SB := V.SB) (A := V.A) (p := q0) (o := if d then 1 else 3) h₃.rAB h₃.rSB h₃.pk.one
    (by zumwr; config_simp; omega) hq0A o₃ by_grind
    by_grind
    (by have := hL₃.SB_le; grind)
    (by have := hL₃.AB_le; grind)
  rw [show c₃.nmem = c.nmem from mm₂, hwv'] at v₄
  rw [show c₃.nmem = c.nmem from mm₂, hhv'] at v₄'
  zucug

  have h₄ := h₃.stable (fun r hr => f₄.1 r (by
    zvmwq at hr; grind))
    ztfrj
  -- 5. the copies
  have y210 : c₄.nreg 110210 = Y.edge := by
    rw [f₄.1 _ by_decide, R₃ _ by_decide, R₂ _ ztmaj, n₁]; config_simp
  have y211 : c₄.nreg 110211 = Y.hgt := by
    rw [f₄.1 _ by_decide, R₃ _ by_decide, R₂ _ ztmaj, n₁]; config_simp
  obtain ⟨c₅, k₅, e₅, hk₅, n₅⟩ : ∃ c₅ k₅, Exec P W (block [.copyN 110212 110100,
      .copyN 110100 110210]) c₄ c₅ k₅ ∧ k₅ = 2 ∧
      c₅.nreg = upd ztrxw 110100 Y.edge := by
    zucc
    exec_block
    grind
  have hm₅ :=
    (exec_frameB e₅ (B := fun r => decide ztogb) by_decide).2.2.1
  have R₅ : zthpm := fun r a b => by
    rw [n₅, upd_other _ _ _ b, upd_other _ _ _ a]
  have h₅ := h₄.stable (fun r hr => R₅ r (by
      zvmwq at hr; omega) (by
      zvmwq at hr; omega))
    by_grind
  -- 6. the normalised code of the end at the mirror's walk edge
  zubb
  zuiyk
  zuec
  zubwh
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, -, rest₆⟩ := posA_exec (P := P) e₅.wb_right h₅.pk hm1 hmn h.s_lt hS hR
    by_omega
  have x100 : c₅.nreg 110100 = Y.edge := by rw [n₅]; config_simp
  have x101 : ztutb := by_grind
  zudaz

  have z₆' : c₆.nreg 110103 = nz C Y.edge hc2 := by zunwj
  -- 7. the flag of equal keys
  obtain ⟨c₇, k₇, e₇, hk₇, f₇, v₇⟩ := eqS_exec (P := P) e₆.wb_right by_omega
  have x212 : ztute := by rw [f₆.1 _ by_decide, n₅]; config_simp
  have x210 : c₆.nreg 110210 = Y.edge := by
    zuexm
  have x211 : c₆.nreg 110211 = Y.hgt := by
    zuexn
  zufos
  -- 8. the adjusted arc
  have g170 : ztutf := by
    rw [f₇.1 _ by_decide, f₆.1 _ by_decide, R₅ _ by_decide by_decide,
      f₄.1 _ by_decide, R₃ _ by_decide, hq0d]
  have h₇ := h₅.stable (fun r hr => by
      rw [f₇.1 r zthtx,
        f₆.1 r ztfpz])
    ztjvl
  have hAW : ztmty := by
    zuuq

    · grind
    · omega
  obtain ⟨c₈, k₈, e₈, hk₈, f₈, v₈⟩ := adjS_exec (P := P) e₇.wb_right d h₇.pk.one h₇.pk.zero h₇.rA
    by_omega hAW
  rw [g170, v₇] at v₈
  -- 9. the normalised pair
  have x299 : c₈.nreg 110299 = x := by
    rw [f₈.1 _ by_decide, f₇.1 _ by_decide, f₆.1 _ by_decide, R₅ _ by_decide by_decide,
      f₄.1 _ by_decide, R₃ _ by_decide, R₂ _ ztmaj,
      R₁ _ by_decide by_decide by_decide, hx]
  have h1₈ : c₈.nreg 120011 = 1 := by rw [f₈.1 _ by_decide]; exact h₇.pk.one
  set q := adjN d V.A q0 _ with hqdef
  have hqA : q < V.A := by
    zueyh
    split_ifs <;> first | exact predP_lt hq0A | exact succP_lt hq0A | exact hq0A
  obtain ⟨c₉, k₉, e₉, hk₉, f₉, n₉, s₉⟩ := normS_exec (P := P) e₈.wb_right h1₈
    by_omega by_omega
  rw [x299, v₈] at n₉ s₉
  have ex : Exec P W ztqtc c c₉ _ :=
    .seq e₁ ztqr
  refine ⟨c₉, _, ex, by_omega, ?_, q, hqA, fun hne => ?_, n₉, s₉⟩
  · -- the frame
    have fr₁ : FrameB BLS c c₁ := exec_frameB e₁ by_decide
    have fr₃ : FrameB BLS c₂ c₃ := exec_frameB e₃ by_decide
    have fr₅ : FrameB BLS c₄ c₅ := exec_frameB e₅ by_decide
    refine fr₁.trans ((FrameB.mono f₂ fun r hr => by simp [BLS, hr]).trans (fr₃.trans
      ((FrameB.mono f₄ fun r hr => ?_).trans (fr₅.trans ((FrameB.mono f₆ fun r hr => ?_).trans
      ((FrameB.mono f₇ fun r hr => ?_).trans ((FrameB.mono f₈ fun r hr => ?_).trans
      (FrameB.mono f₉ fun r hr => ?_))))))))
    all_goals
      simp only [BPA, Bool.or_eq_true, decide_eq_true_eq] at hr
      simp only [BLS, Bool.or_eq_true, decide_eq_true_eq]
      omega
  · -- the semantics
    zudnq
    zuiws
    have hkY : (chainModel C).key zta ⟨Y.edge, Y.hgt⟩ =
        mk C ztwyv := by
      have := hYk; zvnao at this; omega
    rw [hkY] at loc1 loc2
    have hq0N := hq₂
    have hkeq : (chainModel C).key zta ztlnm =
        mk C ztwyv ↔
        (w2 = Y.edge ∧ nz C Y.edge hc2 = Y.hgt) := by
      zucnw
      have hwe2 : ztdre := by
        rfl
      zuhlz
      have := key_eq_iff C hD (w2 := w2) (hc2 := hc2) hY6 hY7 hYh
        hh2 ⟨hYp0, hYp1⟩ ztuhy
      zuktm
      rw [← hkY, ← this]
      zuext
    have hl1 : ¬ (chainModel C).IsCut _
        _ →
        sideInArc _ _
          _ := fun hc' => by
      zujdv
      · exact absurd h0 (Set.nonempty_iff_ne_empty.1 hne)
      · zulyi
    cases d
    · -- the end: the arc just after
      zuma
      have := after_of_loc hN hP hne hq0N hl1 loc2
      have hek : ek ztc zta N q0 = (chainModel C).key zta ztlnn := by
        rfl
      rw [hek] at this
      convert this using 1
      zueyh
      by_cases he : (chainModel C).key zta ztlnn =
          mk C ((chainModel C).key zta (endPos N false x))
      · grind
      · zugvw
    · zuwa
      have := before_of_loc hN hP hne hq0N hl1 loc2
      have hsk : sk ztc zta N q0 = (chainModel C).key zta ztlno := by
        rfl
      rw [hsk] at this
      convert this using 1
      zueyh
      by_cases he : (chainModel C).key zta ztlno =
          mk C ((chainModel C).key zta (endPos N true x))
      · grind
      · zugvw
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open OracleQ
open Chazelle.Chain (sideInArc)
@[expose] public section
def zipBody (d : Bool) : Stmt :=
  .seq ztmnc (.ifLtN 120012 110104 ztqtc ztfel)

/-- The registers written by `zipBody`. -/
def BZB (r : ℕ) : Bool := BPR r || BLS r

/-- The pair function of a side. -/
noncomputable def zipF (C : Chain) (Q : Polygon) (N : NF) (d : Bool) : ℕ → Option ztw :=
  if d then zipSk C Q N else zipEk C Q N
variable {P : Polygon} {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c : Config}
theorem zipBody_exec
    (hw : WordsBounded W c) (h : ZEnv P W lo C N V c) {x : ℕ} (hx : c.nreg 110299 = x)
    (hxA : x < V.A) (d : Bool) :
    ∃ c' k, Exec P W ztqzj c c' k ∧ k ≤ 5500 * ztbts + 400 ∧ FrameB BZB c c' ∧
      (zipF C zta N d x = none → c'.nreg 110290 = 0) ∧
      ∀ z, zipF C zta N d x = some z →
        c'.nreg 110290 = 1 ∧ c'.nreg 110291 = z.1 ∧ c'.nreg 110292 = z.2 := by
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, o₁, -, fl₁, mir₁⟩ := prepS_exec hw h hx hxA d
  have h₁ := h.stable (fun r hr => f₁.1 r (by
    zucqx
    zunwi; omega))
    ztdnq
  have x₁ : c₁.nreg 110299 = x := by rw [f₁.1 _ by_decide, hx]
  have hA := h.mem.1.A
  have hkx : (chainModel C).key C.P ztcdb =
      if d then sk ztc zta N x else ek ztc zta N x := by
    rw [h.CQ, key_endPos]
  have hkx' : (chainModel C).key zta ztcdb =
      if d then sk ztc zta N x else ek ztc zta N x := by
    rw [key_endPos]
  have hGM : ztebh := Or.inl ztkiq
  by_cases hI : InI C ztxjg
  · rw [ite_eq_left hI] at fl₁
    have ht : c₁.nreg 120012 < c₁.nreg 110104 := by rw [h₁.pk.zero, fl₁]; omega
    obtain ⟨c₂, k₂, e₂, hk₂, f₂, q, hqA, hq, n₂, s₂⟩ := locS_exec e₁.wb_right h₁ x₁ hxA d o₁ hI mir₁
    have ex : Exec P W ztqzj c c₂ _ :=
      .seq e₁ (.ifLtN_true (e := .instr ztsom) ht e₂)
    have fr : FrameB BZB c c₂ := (FrameB.mono f₁ fun r hr => by zunpx).trans
      (FrameB.mono f₂ fun r hr => by zunpx)
    -- the pair function is `normP x q`
    suffices H : zipF C _ N d x = normP x q by
      rw [H]; exact by_grind
    zukus
    zuiad
    have hxN : x < N.arcs.length := by_omega
    zuhbr
    · have hq' := hq hne
      rw [hkx'] at hq'
      unfold zipF
      cases d
      · zvnhh at hI hq' ⊢
        have hex : ∃ p, p < N.arcs.length ∧
            After C _ N p _ := ztrdz
        obtain ⟨ha, hA'⟩ := aftArc_spec C _ N hex
        unfold zipEk
        rw [ite_eq_left by_simp_all, after_unique h.isNF h.simple hne ha hqN hA' hq', normP_comm]
      · simp only [ite_true] at hI hq' ⊢
        have hex : ∃ p, p < N.arcs.length ∧
            Before C _ N p _ := ztrdz
        obtain ⟨hb, hB'⟩ := befArc_spec C _ N hex
        unfold zipSk
        rw [ite_eq_left by_simp_all, before_unique h.isNF h.simple hne hb hqN hB' hq']
    · have hA1 := arcs_le_one_of_empty h.isNF hGM ztqcq
      rw [normP_none_of_le_one hA1 by_omega by_omega]
      unfold zipF
      cases d
      · zuma
        unfold zipEk; split_ifs
        · exact normP_none_of_le_one hA1 (aftArc_lt C _ N _) by_omega
        · rfl
      · zuwa
        unfold zipSk; split_ifs
        · exact normP_none_of_le_one hA1 by_omega (befArc_lt C _ N _)
        · rfl
  · rw [ite_eq_right hI] at fl₁
    have ht : ¬ c₁.nreg 120012 < c₁.nreg 110104 := by_omega
    have e₂ := Exec.constN (P := P) e₁.wb_right 110290 0 ztbg
    have ex : Exec P W ztqzj c _ _ := .seq e₁ (.ifLtN_false (t := locS d) ht e₂)
    have fr : FrameB BZB c _ := (FrameB.mono f₁ fun r hr => by zunpx).trans
      (FrameB.mono (exec_frameB e₂ (B := fun r => decide (r = 110290)) by_decide)
        fun r hr => by simp at hr; subst hr; decide)
    have hnone : zipF C zta N d x = none := by
      zukus
      unfold zipF
      cases d
      · zvnhh at hI ⊢
        unfold zipEk; simp_all
      · simp only [ite_true] at hI ⊢
        unfold zipSk; simp_all
    refine ⟨_, _, ex, by_omega, fr, by_simp_all, fun z hz => ?_⟩
    simp_all
theorem BZB_keep {r : ℕ} (h : ZKeep r = true ∨ ztgxk) : BZB r = false := by
  zubis
  simp [BZB, BPR, BLS, BL, Bdir, Bloc, Bcmp, Bk]
  omega

/-- The capacity of the raw pair arrays. -/
def zCap (A : ℕ) : ℕ := 2 * A + 5

/-- **The zipper loops.** -/
def zS : Stmt :=
  .seq (block [.copyN 110293 9999, .addN 110297 120030 120030, .constN 110298 5,
      .addN 110297 110297 110298, .addN 110294 110293 110297, .addN 9999 110294 110297,
      .constN 110295 0])
    (.seq (emitS 110299 120030 120011 110290 110291 110292 110293 110294 110295 110296 (zipBody true))
      (emitS 110299 120030 120011 110290 110291 110292 110293 110294 110295 110296 (zipBody false)))

/-- The registers written by `zS`. -/
def BZS (r : ℕ) : Bool := decide ztyc || BZB r || decide ztgxk
theorem zS_exec
    (hw : WordsBounded W c) (h : ZEnv P W lo C N V c) {A₀ : ℕ} (hAl : c.nreg 9999 = A₀)
    (hlo : lo ≤ A₀) (hW : A₀ + 2 * zCap V.A ≤ W) :
    ∃ c' k, Exec P W zS c c' k ∧ k ≤ 2 * V.A * ztzbg + 20 ∧ PF BZS A₀ c c' ∧
      c'.nreg 9999 = A₀ + 2 * zCap V.A ∧ c'.nreg 110293 = A₀ ∧
      c'.nreg 110294 = A₀ + zCap V.A ∧ c'.nreg 110297 = zCap V.A ∧
      c'.nreg 110295 = (emitted ztxpc V.A ++ emitted ztxpb V.A).length ∧
      PairsAt c'.nmem A₀ ztrip
        (emitted ztxpc V.A ++ emitted ztxpb V.A) ∧
      ZEnv P W lo C N V c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, n₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 110293 9999,
      .addN 110297 120030 120030, .constN 110298 5, .addN 110297 110297 110298,
      .addN 110294 110293 110297, .addN 9999 110294 110297, .constN 110295 0]) c c₁ k₁ ∧ k₁ = 7 ∧
      c₁.nreg = upd (upd (upd (upd (upd (upd c.nreg 110293 A₀) 110297 (zCap V.A)) 110298 5)
        110294 ztrip) 9999 (A₀ + 2 * zCap V.A)) 110295 0 ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold zCap at hW ⊢
    have hA := h.rA
    exec_block
    · config_simp; omega
    · omega
    · config_simp; omega
    · config_simp; omega
    · config_simp; omega
    · omega
    · refine ztezb
      config_simp; rw [hA, hAl]
      funext r; zvmwf; grind
  have R₁ : ∀ r, BZS r = false → c₁.nreg r = c.nreg r := fun r hr => by
    zuggn
    zulc
  have h₁ := h.stable (fun r hr => R₁ r (by
      simp only [BZS, Bool.or_eq_false_iff, decide_eq_false_iff_not]
      refine ⟨⟨?_, BZB_keep ztcgw⟩, ?_⟩ <;>
      zvmwq at hr <;> omega))
    by_simp_all
  have v93 : c₁.nreg 110293 = A₀ := by_simp_all
  have v94 : c₁.nreg 110294 = A₀ + zCap V.A := by_simp_all
  have v95 : c₁.nreg 110295 = 0 := by_simp_all
  have v97 : c₁.nreg 110297 = zCap V.A := by_simp_all
  have v9 : c₁.nreg 9999 = A₀ + 2 * zCap V.A := by_simp_all
  have hJs : ∀ d d', ZEnv P W lo C N V d →
      (∀ r, BZB r = false → r ≠ 110299 → r ≠ 110295 → r ≠ 110296 → d'.nreg r = d.nreg r) →
      ztno → ZEnv P W lo C N V d' := fun d d' hJ hr hm =>
    hJ.stable (fun r hr' => hr r (BZB_keep ztvcc) (by
        zvmwq at hr'; omega) (by
        zvmwq at hr'; omega) (by
        zvmwq at hr'; omega))
      by_grind
  -- the starts
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, rr₂, cnt₂, pr₂, mm₂, rm₂, o₂, J₂⟩ := emitS_exec (P := P) (W := W)
    (ri := 110299) (rn := 120030) (r1 := 120011) (rf := 110290) (rv1 := 110291) (rv2 := 110292)
    (rR1 := 110293) (rR2 := 110294) (rc := 110295) (rt := 110296) (body := zipBody true)
    (B := BZB) by_decide ztcgp ztyhg
    ztyhg ztcgp ztcgp
    ztcgp (R1 := A₀) ztnqm
    ztxbl (n := V.A)
    (κ := 5500 * ztbts + 400) ztxpc
    (fun i d hi hJ hwd hri => by
      obtain ⟨d', k, e, hk, f, a, b⟩ := zipBody_exec hwd hJ hri hi true
      exact ztiog)
    e₁.wb_right h₁ h₁.rA h₁.pk.one v93 v94 v95 ztqgs
    ztmfa
  zuewv

  set L1 := emitted ztxpc V.A
  have hL1 : L1.length ≤ V.A := emitted_length_le _ _
  -- the ends
  have g93 : c₂.nreg 110293 = A₀ := by
    rw [r₂ _ zthqr by_decide by_decide by_decide, v93]
  have g94 : c₂.nreg 110294 = A₀ + zCap V.A := by
    rw [r₂ _ zthqr by_decide by_decide by_decide, v94]
  obtain ⟨c₃, k₃, e₃, hk₃, r₃, rr₃, cnt₃, pr₃, mm₃, rm₃, o₃, J₃⟩ := emitS_exec (P := P) (W := W)
    (ri := 110299) (rn := 120030) (r1 := 120011) (rf := 110290) (rv1 := 110291) (rv2 := 110292)
    (rR1 := 110293) (rR2 := 110294) (rc := 110295) (rt := 110296) (body := zipBody false)
    (B := BZB) by_decide ztcgp ztyhg
    ztyhg ztcgp ztcgp
    ztcgp (R1 := A₀) ztnqm
    ztxbl (n := V.A)
    (κ := 5500 * ztbts + 400) ztxpb
    (fun i d hi hJ hwd hri => by
      obtain ⟨d', k, e, hk, f, a, b⟩ := zipBody_exec hwd hJ hri hi false
      exact ztiog)
    e₂.wb_right J₂ J₂.rA J₂.pk.one g93 g94 cnt₂ ztqgs
    ztmfa
  set L2 := emitted ztxpb V.A
  have hL2 : L2.length ≤ V.A := emitted_length_le _ _
  have hB : ∀ r, BZS r = false → BZB r = false ∧ r ≠ 110299 ∧ r ≠ 110295 ∧ r ≠ 110296 := by
    zuz
    zuggn
    grind
  refine ⟨c₃, _, .seq e₁ ztcr, ?_, ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_,
    by grind, by_grind⟩, ?_, ?_, ?_, ?_, ?_, ?_, J₃⟩
  · grind
  · grind
  · obtain ⟨a, -⟩ := hB r hr
    grind
  · grind
  · rw [r₃ _ by_decide by_decide by_decide by_decide,
      r₂ _ by_decide by_decide by_decide by_decide, v9]
  · rw [r₃ _ zthqr by_decide by_decide by_decide, g93]
  · rw [r₃ _ zthqr by_decide by_decide by_decide, g94]
  · rw [r₃ _ zthqr by_decide by_decide by_decide,
      r₂ _ zthqr by_decide by_decide by_decide, v97]
  · grind
  · refine PairsAt.append (PairsAt.congr pr₂ fun t ht => ⟨by_grind,
      mm₃ _ (Or.inr (Or.inl ⟨by unfold zCap at *; omega, by_omega⟩))⟩) pr₃
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open OracleQ
open Chazelle.Chain (sideInArc)
@[expose] public section
def locZ : Stmt := .seq (block [.copyN 50000 120040, .copyN 50001 120014]) myLoc

/-- The registers written by `locZ`. -/
def BLZ (r : ℕ) : Bool := BL r || decide ztgzd
variable {P : Polygon} {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c : Config}
theorem locZ_exec
    (hw : WordsBounded W c) (h : ZEnv P W lo C N V c) {pw ph : ℕ} (h2 : c.nreg 50002 = pw)
    (h3 : c.nreg 50003 = ph) (hpw : pw ≤ 2 * C.m + 6)
    (hp : ProperPos ztc zta P.n ztfwt) :
    ∃ c' k, Exec P W locZ c c' k ∧ k ≤ 5500 * ztbts + 2 ∧ FrameB BLZ c c' ∧
      c'.nreg 120170 < V.A ∧
      (¬ (chainModel C).IsCut ztwjq ztxjn →
        N.F ztc zta = ∅ ∨
          sideInArc (sk ztc zta N ztmfb)
            (ek ztc zta N ztmfb) ztxjn) ∧
      ((chainModel C).IsCut ztwjq ztxjn →
        sk ztc zta N ztmfb = (chainModel C).key zta ztfwt ∨
          ek ztc zta N ztmfb = (chainModel C).key zta ztfwt) := by
  zumn

  obtain ⟨c₁, k₁, e₁, hk₁, n₁, mm₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 50000 120040,
      .copyN 50001 120014]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg = upd (upd c.nreg 50000 V.MD) 50001 V.NB ∧ c₁.nmem = c.nmem := by
    exec_block
    refine ztrec
    config_simp; rw [h.rMD, h.rNB]
  have R₁ : ∀ r, (r < 50000 ∨ 50001 < r) → c₁.nreg r = c.nreg r :=
    fun r a => by zuncb; zvmwf; grind
  have h₁ := h.stable (fun r hr => R₁ r (by
      zvmwq at hr; omega))
    by_simp_all
  zuhxq

  zuru
  have g2 : c₁.nreg 50002 = pw := by_simp_all
  have g3 : c₁.nreg 50003 = ph := by_simp_all
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hq₂, loc1, loc2⟩ := myLoc_exec arcCover (P := P) (W := W) (c := c₁)
    e₁.wb_right ⟨h.good, by_omega, by zuncb; config_simp; have := hL.md_le; omega,
      by zungp; config_simp; exact hL.chwf, chainModel C,
      by zungp; config_simp; exact hL.md, by_omega⟩
    h.good by_omega (by rw [n₁, mm₁]; config_simp; exact hL.md) hL.good
    (by rw [n₁, mm₁]; config_simp; exact hL.nf) h.isNF by_simp_all hL.st
    h₁.rTB h₁.rL h₁.pk.zero h₁.pk.one
    ztmdu ztlje
    (by rw [n₁]; config_simp; exact hL.NB_le) (by rw [n₁, mm₁]; config_simp; rw [← hA]; exact hL.AB_le)
    (by rw [n₁, mm₁]; config_simp; rw [← hA]; exact hL.SB_le) hTB
  rw [g2, g3] at loc1 loc2
  have fr₁ : FrameB BLZ c c₁ := exec_frameB e₁ by_decide
  exact ⟨c₂, _, .seq e₁ e₂, by_omega, fr₁.trans (FrameB.mono f₂ fun r hr => by simp [BLZ, hr]),
    by omega, loc1, loc2⟩

/-- Test the end of the located arc against the reference position, adjust. -/
def tstS (d : Bool) : Stmt :=
  .seq arcPosS (.seq ztkrn
    (.seq posA (.seq eqS ztjob)))

/-- The registers written by `tstS`. -/
def BTS (r : ℕ) : Bool :=
  decide ztgxj || decide ztndz ||
    decide (110212 ≤ r ∧ r ≤ 110214)
open Classical in
theorem tstS_exec
    (hw : WordsBounded W c) (h : ZEnv P W lo C N V c) (d : Bool) {q0 : ℕ}
    (h03 : c.nreg 110203 = q0) (hq0A : q0 < V.A) (h170 : c.nreg 120170 = q0)
    (ho : c.nreg 110204 = if d then 1 else 3) {Yw Yz : ℕ} (h10 : c.nreg 110210 = Yw)
    (h11 : c.nreg 110211 = Yz) (hY6 : 6 ≤ Yw) (hY7 : Yw ≤ 2 * C.m + 6) (hYh : Yz ≤ C.P.n)
    (hYp : 0 ≤ (chainModel C).param C.P ztkiu ∧ (chainModel C).param C.P ztkiu < 1)
    (hYnz : nz C Yw Yz = Yz) :
    ∃ c' k, Exec P W ztwgx c c' k ∧ k ≤ 100 ∧ FrameB BTS c c' ∧
      c'.nreg 110213 = (if (chainModel C).key zta ztlnm =
        (chainModel C).key zta ztkiu then 1 else 0) ∧
      c'.nreg 110214 = adjN d V.A q0 (c'.nreg 110213) := by
  zumn

  zuhxe

  zueix
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, v₄, v₄'⟩ := arcPosS_exec (P := P) hw (AB := V.AB)
    (SB := V.SB) (A := V.A) (p := q0) (o := if d then 1 else 3) h.rAB h.rSB h.pk.one
    h03 hq0A ho by_grind by_omega
    (by have := hL.SB_le; have := hL.TB_le; rw [h.mem.2.2] at *; omega)
    (by have := hL.AB_le; have := hL.TB_le; rw [h.mem.2.1] at *; omega)
  rw [hwv'] at v₄
  rw [hhv'] at v₄'
  zucug

  have h₄ := h.stable (fun r hr => f₄.1 r (by
    zvmwq at hr; grind))
    ztfrj
  have y210 : c₄.nreg 110210 = Yw := by rw [f₄.1 _ by_decide, h10]
  have y211 : c₄.nreg 110211 = Yz := by rw [f₄.1 _ by_decide, h11]
  obtain ⟨c₅, k₅, e₅, hk₅, n₅⟩ : ∃ c₅ k₅, Exec P W (block [.copyN 110212 110100,
      .copyN 110100 110210]) c₄ c₅ k₅ ∧ k₅ = 2 ∧
      c₅.nreg = upd ztrxw 110100 Yw := by
    zucc
    exec_block
    simp_all
  have hm₅ :=
    (exec_frameB e₅ (B := fun r => decide ztogb) by_decide).2.2.1
  have R₅ : zthpm := by_simp_all
  have h₅ := h₄.stable (fun r hr => R₅ r (by
      zvmwq at hr; omega) (by
      zvmwq at hr; omega))
    by_simp_all
  zubb
  zuiyk
  zuec
  zubwh
  have hPW := h.hW
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, -, rest₆⟩ := posA_exec (P := P) e₅.wb_right h₅.pk hm1 hmn h.s_lt hS hR
    by_omega
  have x100 : c₅.nreg 110100 = Yw := by_simp_all
  have x101 : ztutb := by_simp_all
  zudaz

  have z₆' : c₆.nreg 110103 = nz C Yw hc2 := by zunwj
  obtain ⟨c₇, k₇, e₇, hk₇, f₇, v₇⟩ := eqS_exec (P := P) e₆.wb_right by_omega
  have x212 : ztute := by rw [f₆.1 _ by_decide, n₅]; config_simp
  have x210 : c₆.nreg 110210 = Yw := by
    zuexm
  have x211 : c₆.nreg 110211 = Yz := by
    zuexn
  zufos
  have g170 : ztutf := by
    rw [f₇.1 _ by_decide, f₆.1 _ by_decide, R₅ _ by_decide by_decide,
      f₄.1 _ by_decide, h170]
  have h₇ := h₅.stable (fun r hr => by
      rw [f₇.1 r zthtx,
        f₆.1 r ztfpz])
    ztjvl
  have hAW : ztmty := by
    zuuq

    · simp_all
    · omega
  obtain ⟨c₈, k₈, e₈, hk₈, f₈, v₈⟩ := adjS_exec (P := P) e₇.wb_right d h₇.pk.one h₇.pk.zero h₇.rA
    by_omega hAW
  rw [g170] at v₈
  -- the key test
  have hkeq : (chainModel C).key zta ztlnm = (chainModel C).key zta ztkiu ↔
      (w2 = Yw ∧ nz C Yw hc2 = Yz) := by
    zucnw
    have hwe2 : ztdre := by
      rfl
    zuhlz
    have := key_eq_iff C hD (w2 := w2) (hc2 := hc2) hY6 hY7 hYh
      hh2 hYp ztuhy
    zuktm
    rw [← this, ← hQ]
  have e13 : c₈.nreg 110213 = c₇.nreg 110213 := f₈.1 _ by_decide
  have ex : Exec P W ztwgx c c₈ _ := .seq e₄ zteka
  refine ⟨c₈, _, ex, by_omega, ?_, ?_, ?_⟩
  · have fr₅ : FrameB BTS c₄ c₅ := exec_frameB e₅ by_decide
    refine (FrameB.mono f₄ fun r hr => ?_).trans (fr₅.trans ((FrameB.mono f₆ fun r hr => ?_).trans
      ((FrameB.mono f₇ fun r hr => ?_).trans (FrameB.mono f₈ fun r hr => ?_))))
    all_goals
      simp only [BPA, decide_eq_true_eq] at hr
      simp only [BTS, Bool.or_eq_true, decide_eq_true_eq]
      omega
  · simp_all
  simp_all
theorem sideInArc_ne {s e x : ℝ} (h : sideInArc s e x) : x ≠ s ∧ x ≠ e := by
  zujqy
  grind

/-- **The analysis of a walk vertex `X`** (in `110220`). -/
def kiS : Stmt :=
  .seq (block [.copyN 50002 110220, .constN 50003 0, .copyN 110210 110220, .constN 110211 0])
    (.seq locZ (.seq (block [.copyN 110203 120170, .copyN 110204 120011])
      (.seq (tstS true) (.seq (block [.copyN 110223 110214, .copyN 110225 110213,
          .copyN 110204 110205])
        (.seq (tstS false) (block [.copyN 110224 110214, .addN 110228 110225 110213,
          .copyN 110227 120170]))))))

/-- The registers written by `kiS`. -/
def BKI (r : ℕ) : Bool := BLZ r || BTS r || decide (110203 ≤ r ∧ r ≤ 110204) ||
  decide (110210 ≤ r ∧ r ≤ 110211) || decide (110223 ≤ r ∧ r ≤ 110228)
theorem BKI_keep {r : ℕ} (h : ZKeep r = true ∨ (110229 ≤ r ∧ r ≤ 110299)) : BKI r = false := by
  zubis
  simp [BKI, BLZ, BTS, BL, Bdir, Bloc, Bcmp, Bk]
  omega
open Classical in
theorem kiS_exec
    (hw : WordsBounded W c) (h : ZEnv P W lo C N V c) {X : ℕ} (hX : c.nreg 110220 = X)
    (h6 : 6 ≤ X) (h7 : X ≤ 2 * C.m + 6) :
    ∃ c' k, Exec P W kiS c c' k ∧ k ≤ 5500 * ztbts + 250 ∧ FrameB BKI c c' ∧
      c'.nreg 110227 < V.A ∧ c'.nreg 110223 < V.A ∧ c'.nreg 110224 < V.A ∧
      c'.nreg 110228 ≤ 2 ∧ ((N.F ztc zta).Nonempty →
        Before C zta N (c'.nreg 110223) X ∧ After C zta N (c'.nreg 110224) X ∧
        (c'.nreg 110228 = 0 ↔ sideInArc (sk ztc zta N ztvfz)
          (ek ztc zta N ztvfz) X) ∧
        ∀ q, q < V.A → sideInArc (sk ztc zta N q) (ek ztc zta N q) X →
          q = c'.nreg 110227) := by
  zumn

  have hQ := h.CQ
  have hkX : (chainModel C).key zta ztomg = X := by zvnoq; exact key_zero C X
  have hp0 : (chainModel C).param C.P ztomg = 0 := by_rfl
  -- 1. the copies
  obtain ⟨c₁, k₁, e₁, hk₁, n₁, mm₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 50002 110220,
      .constN 50003 0, .copyN 110210 110220, .constN 110211 0]) c c₁ k₁ ∧ k₁ = 4 ∧
      c₁.nreg = upd (upd (upd (upd c.nreg 50002 X) 50003 0) 110210 X) 110211 0 ∧
      c₁.nmem = c.nmem := by
    exec_block
    · omega
    · omega
    simp_all
  have fr₁ : FrameB BKI c c₁ := exec_frameB e₁ by_decide
  have h₁ := h.stable (fun r hr => fr₁.1 r ztzbm)
    by_simp_all
  -- 2. the double identification
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hq₂, loc1, loc2⟩ := locZ_exec e₁.wb_right h₁ (pw := X) (ph := 0)
    by_simp_all by_simp_all h7
    ⟨by_rfl, by_simp_all, Nat.zero_le _⟩
  rw [hkX] at loc1 loc2
  obtain ⟨q0, hq0d⟩ : ztprf := by_simp_all
  zuikn
  have h₂ := h₁.stable (fun r hr => f₂.1 r (by
      have := BKI_keep ztcgw; simp only [BKI, Bool.or_eq_false_iff] at this; simp_all))
    ztlnw
  -- 3. the copies
  obtain ⟨c₃, k₃, e₃, hk₃, n₃⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 110203 120170,
      .copyN 110204 120011]) c₂ c₃ k₃ ∧ k₃ = 2 ∧
      c₃.nreg = upd (upd c₂.nreg 110203 q0) 110204 1 := by
    zue
    exec_block
    zubee
    config_simp; rw [hq0d, h₂.pk.one]
  have fr₃ : FrameB BKI c₂ c₃ := exec_frameB e₃ by_decide
  have h₃ := h₂.stable (fun r hr => fr₃.1 r ztzbm)
    (fun a _ => by rw [fr₃.2.2.1])
  have R₂₃ : ∀ r, r ≠ 110203 → r ≠ 110204 → c₃.nreg r = c₂.nreg r := by_simp_all
  have R₁₂ := f₂.1
  have g10 : c₃.nreg 110210 = X := by
    rw [R₂₃ _ by_decide by_decide, R₁₂ _ by_rfl, n₁]
    config_simp
  have g11 : c₃.nreg 110211 = 0 := by
    rw [R₂₃ _ by_decide by_decide, R₁₂ _ by_rfl, n₁]
    config_simp
  have hq0A := hq₂
  have hnz0 : nz C X 0 = 0 := by_rfl
  -- 4. the start
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, s₄, a₄⟩ := tstS_exec e₃.wb_right h₃ true (q0 := q0)
    by_simp_all hq0A by_simp_all
    by_simp_all g10 g11 h6 h7 ztbg ztoml
    hnz0
  rw [hkX] at s₄
  have h₄ := h₃.stable (fun r hr => f₄.1 r (by
      have := BKI_keep ztcgw; simp only [BKI, Bool.or_eq_false_iff] at this; simp_all))
    ztfrj
  -- 5. the copies
  obtain ⟨c₅, k₅, e₅, hk₅, n₅⟩ : ∃ c₅ k₅, Exec P W (block [.copyN 110223 110214,
      .copyN 110225 110213, .copyN 110204 110205]) c₄ c₅ k₅ ∧ k₅ = 3 ∧
      c₅.nreg = upd (upd (upd c₄.nreg 110223 (c₄.nreg 110214)) 110225 ztvno) 110204 3 := by
    zucc
    exec_block
    zubee
    config_simp; rw [h₄.r3]
  have fr₅ : FrameB BKI c₄ c₅ := exec_frameB e₅ by_decide
  have h₅ := h₄.stable (fun r hr => fr₅.1 r ztzbm)
    (fun a _ => by rw [fr₅.2.2.1])
  have R₄₅ : ∀ r, r ≠ 110223 → r ≠ 110225 → r ≠ 110204 → c₅.nreg r = c₄.nreg r := by_simp_all
  -- 6. the end
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, s₆, a₆⟩ := tstS_exec e₅.wb_right h₅ false (q0 := q0)
    (by rw [R₄₅ _ by_decide by_decide by_decide, f₄.1 _ by_decide, n₃]; config_simp)
    hq0A (by rw [R₄₅ _ by_decide by_decide by_decide, f₄.1 _ by_decide,
      R₂₃ _ by_decide by_decide, hq0d])
    by_simp_all
    (by rw [R₄₅ _ by_decide by_decide by_decide, f₄.1 _ by_decide, g10])
    (by rw [R₄₅ _ by_decide by_decide by_decide, f₄.1 _ by_decide, g11])
    h6 h7 ztbg ztoml hnz0
  rw [hkX] at s₆
  -- 7. the results
  obtain ⟨c₇, k₇, e₇, hk₇, n₇⟩ : ∃ c₇ k₇, Exec P W (block [.copyN 110224 110214,
      .addN 110228 110225 110213, .copyN 110227 120170]) c₆ c₇ k₇ ∧ k₇ = 3 ∧
      c₇.nreg = upd (upd (upd c₆.nreg 110224 (c₆.nreg 110214)) 110228
        (c₆.nreg 110225 + c₆.nreg 110213)) 110227 (c₆.nreg 120170) := by
    zujb
    have b1 : c₆.nreg 110225 ≤ 1 := by
      zunhz; config_simp; grind
    have b2 : c₆.nreg 110213 ≤ 1 := by_grind
    have hWW := h.hW
    exec_block
    · config_simp; omega
    simp
  have ex : Exec P W kiS c c₇ _ :=
    .seq e₁ ztfc
  have fr₇ : FrameB BKI c₆ c₇ := exec_frameB e₇ by_decide
  have g170 : c₆.nreg 120170 = q0 := by
    rw [f₆.1 _ by_decide, R₄₅ _ by_decide by_decide by_decide, f₄.1 _ by_decide,
      R₂₃ _ by_decide by_decide, hq0d]
  have v227 : c₇.nreg 110227 = q0 := by_simp_all
  have v223 : c₇.nreg 110223 = adjN true V.A q0 ztvno := by
    zupaa; config_simp; zunhz; simp_all
  have v224 : c₇.nreg 110224 = adjN false V.A q0 (c₆.nreg 110213) := by
    simp_all
  have v228 : c₇.nreg 110228 = c₄.nreg 110213 + c₆.nreg 110213 := by
    zupaa; config_simp; zunhz; config_simp
  have hadjlt : ∀ d e, adjN d V.A q0 e < V.A := fun d e => by
    unfold adjN; split_ifs
    · exact predP_lt hq0A
    · exact succP_lt hq0A
    omega
  have v228b : c₇.nreg 110228 ≤ 2 := by
    grind
  refine ⟨c₇, _, ex, by_omega, ?_, by_omega, by_simp_all,
    by simp_all, v228b, fun hne => ?_⟩
  · refine fr₁.trans ((FrameB.mono f₂ fun r hr => by zunpy).trans (fr₃.trans
      ((FrameB.mono f₄ fun r hr => by zunpy).trans (fr₅.trans
      ((FrameB.mono f₆ fun r hr => by zunpy).trans fr₇)))))
  · zudnq
    zuiws
    have hq0N : q0 < N.arcs.length := by_omega
    have hl1 : ¬ (chainModel C).IsCut _ (X : ℝ) →
        sideInArc _ _ X :=
      fun hc' => by
        zujdv
        · simp_all
        omega
    have hsk : (chainModel C).key zta ztlno = sk ztc zta N q0 := by
      rfl
    have hek : (chainModel C).key zta ztlnn = ek ztc zta N q0 := by
      rfl
    rw [hsk] at s₄
    rw [hek] at s₆
    refine ⟨?_, ?_, ?_, fun q hq hin => ?_⟩
    · rw [v223, s₄]
      convert before_of_loc hN hP hne hq0N hl1 loc2 using 1
      unfold adjN
      simp_all
    · rw [v224, s₆]
      convert after_of_loc hN hP hne hq0N hl1 loc2 using 1
      unfold adjN
      simp_all
    · rw [v228, v227, s₄, s₆]
      constructor
      · grind
      · zulmv
        obtain ⟨a, b⟩ := sideInArc_ne hin
        grind
    · zuiad
      have hnc := not_cut_of_int hN hne hqN hin
      rw [v227]
      exact interior_unique hN ztzz hne hqN hq0N hin (hl1 hnc)
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open OracleQ
open Chazelle.Chain (sideInArc)
@[expose] public section
def emit1 : Stmt :=
  .ifLtN 110290 120011 .skip
    (block [.addN 110296 110293 110295, .storeN 110296 110291, .addN 110296 110294 110295,
      .storeN 110296 110292, .addN 110295 110295 120011])
variable {P : Polygon} {W : ℕ} {c : Config} {C : Chain} {Q : Polygon} {N : NF}
theorem emit1_exec (hw : WordsBounded W c)
    (h1 : c.nreg 120011 = 1) {R1 R2 c₀ : ℕ} (hR1 : c.nreg 110293 = R1) (hR2 : c.nreg 110294 = R2)
    (hc : c.nreg 110295 = c₀) (o : Option ztw) (hn : o = none → c.nreg 110290 = 0)
    (hs : ∀ z, o = some z → c.nreg 110290 = 1 ∧ c.nreg 110291 = z.1 ∧ c.nreg 110292 = z.2)
    (hR12 : R1 + c₀ + 1 ≤ R2) (hRW : R2 + c₀ + 1 ≤ W) :
    ∃ c' k, Exec P W emit1 c c' k ∧ k ≤ 7 ∧
      (∀ r, r ≠ 110295 → r ≠ 110296 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧ c'.nreg 110295 = c₀ + o.toList.length ∧
      PairsAt c'.nmem ztfol ztenu o.toList ∧
      (∀ a, (a < R1 + c₀ ∨ (R1 + c₀ + o.toList.length ≤ a ∧ a < R2 + c₀) ∨
        R2 + c₀ + o.toList.length ≤ a) → c'.nmem a = c.nmem a) := by
  unfold emit1
  cases ho : o with
  | none =>
    have hf := hn ho
    have ht : c.nreg 110290 < c.nreg 120011 := by_omega
    exact ⟨c, 1, .ifLtN_true ht ztjd, by_omega, by_omega, rfl, rfl, rfl,
      by simp_all, fun t ht => by_simp_all, by_omega⟩
  | some z =>
    obtain ⟨hf, hv1, hv2⟩ := hs z ho
    have ht : ¬ c.nreg 110290 < c.nreg 120011 := by_omega
    obtain ⟨c', k, e, hk, n', m', rr', rm', o'⟩ : ∃ c' k, Exec P W (block [.addN 110296 110293 110295,
        .storeN 110296 110291, .addN 110296 110294 110295, .storeN 110296 110292,
        .addN 110295 110295 120011]) c c' k ∧ k = 5 ∧
        c'.nreg = upd (upd c.nreg 110296 ztenu) 110295 (c₀ + 1) ∧
        c'.nmem = upd (upd c.nmem ztfol z.1) ztenu z.2 ∧ c'.rreg = c.rreg ∧
        c'.rmem = c.rmem ∧ c'.output = c.output := by
      exec_block
      · omega
      · config_simp; omega
      · config_simp; omega
      simp_all
    refine ⟨c', _, .ifLtN_false ht e, by_omega, fun r a b => ?_, rr', rm', o', ?_, fun t ht' => ?_,
      fun a ha => ?_⟩
    · simp_all
    · simp_all
    · simp only [Option.toList_some, List.length_cons, List.length_nil] at ht'
      have : ztbhh := by_omega
      zumo
      zugwb
      simp only [Nat.add_zero, Option.toList_some, List.getD_cons_zero]
      exact ⟨by zunsi, by_simp⟩
    · simp only [Option.toList_some, List.length_cons, List.length_nil] at ha
      rw [m', upd_other _ _ _ by_omega, upd_other _ _ _ by_omega]

/-- **Normalise, guard, append.** -/
def emitG : Stmt :=
  .seq normS (.seq (.ifLtN 120012 110245 .skip ztfel) emit1)

/-- The option emitted by `emitG`. -/
def gOpt (g a b : ℕ) : Option ztw := if g = 0 then none else normP a b
theorem emitG_exec (hw : WordsBounded W c)
    (h1 : c.nreg 120011 = 1) (h0 : c.nreg 120012 = 0) {R1 R2 c₀ : ℕ} (hR1 : c.nreg 110293 = R1)
    (hR2 : c.nreg 110294 = R2) (hc : c.nreg 110295 = c₀) (hR12 : R1 + c₀ + 1 ≤ R2)
    (hRW : R2 + c₀ + 1 ≤ W) (ha : c.nreg 110299 + 1 ≤ W) (hb : c.nreg 110214 + 1 ≤ W) :
    ∃ c' k, Exec P W emitG c c' k ∧ k ≤ 25 ∧
      (∀ r, r ≠ 110295 → r ≠ 110296 → r ≠ 110215 → ztofi →
        c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      c'.nreg 110295 = c₀ + (gOpt ztqhj ztfgn ztfgm).toList.length ∧
      PairsAt c'.nmem ztfol ztenu (gOpt ztqhj ztfgn ztfgm).toList ∧
      (∀ a, (a < R1 + c₀ ∨ (R1 + c₀ + (gOpt ztqhj ztfgn
        ztfgm).toList.length ≤ a ∧ a < R2 + c₀) ∨ R2 + c₀ + (gOpt (c.nreg 110245)
        ztfgn ztfgm).toList.length ≤ a) → c'.nmem a = c.nmem a) := by
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, n₁, s₁⟩ := normS_exec (P := P) hw h1 ha hb
  have R₁ : ∀ r, ztofi → r ≠ 110215 → c₁.nreg r = c.nreg r := fun r a b =>
    f₁.1 r by_grind
  -- the guard
  obtain ⟨g, hg⟩ : ∃ g, c.nreg 110245 = g := by_simp_all
  obtain ⟨c₂, k₂, e₂, hk₂, n₂, s₂, R₂⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 120012 110245 .skip
      ztfel) c₁ c₂ k₂ ∧ k₂ ≤ 3 ∧
      (gOpt g ztfgn ztfgm = none → c₂.nreg 110290 = 0) ∧
      (∀ z, gOpt g ztfgn ztfgm = some z →
        c₂.nreg 110290 = 1 ∧ c₂.nreg 110291 = z.1 ∧ c₂.nreg 110292 = z.2) ∧
      (∀ r, r ≠ 110290 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem ∧ c₂.rreg = c₁.rreg ∧
      c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    zud
    unfold gOpt
    by_cases hg0 : g = 0
    · have ht : ¬ c₁.nreg 120012 < c₁.nreg 110245 := by
        simp_all
      refine ⟨_, _, .ifLtN_false ht (Exec.constN w₁ 110290 0 ztbg), by_omega,
        by_simp_all, by_simp_all,
        by_simp_all, rfl, rfl, rfl, rfl⟩
    · have ht : c₁.nreg 120012 < c₁.nreg 110245 := by
        grind
      refine ⟨_, _, .ifLtN_true ht ztwd, by_omega, fun hn => ?_, fun z hz => ?_,
        by omega, rfl, rfl, rfl, rfl⟩
      · simp_all
      grind
  zuguv
  have g1 : zthoq := by_grind
  have g93 : c₂.nreg 110293 = R1 := by_grind
  have g94 : c₂.nreg 110294 = R2 := by_grind
  have g95 : c₂.nreg 110295 = c₀ := by_grind
  obtain ⟨c₃, k₃, e₃, hk₃, r₃, rr₃, rm₃, o₃, cnt₃, pr₃, mm₃⟩ := emit1_exec (P := P) e₂.wb_right g1 g93
    g94 g95 _ n₂ s₂ hR12 hRW
  zugmw
  refine ⟨c₃, _, .seq e₁ ztcr, by_omega, fun r a b c' d => ?_, ?_, ?_, ?_, cnt₃, pr₃,
    fun x hx => ?_⟩
  · grind
  · rw [rr₃, R₂.2.2.1]; funext r
    exact WalkKey.exec_rframe e₁ (B := fun _ => false) by_decide r rfl
  · rw [rm₃, R₂.2.2.2.1, f₁.2.2.2.1]
  · rw [o₃, R₂.2.2.2.2, f₁.2.2.2.2]
  grind

/-! ## The special pairs from the analyses of the three top keys -/

/-- The facts of the analysis of a walk vertex `X`. -/
def KInfo (C : Chain) (Q : Polygon) (N : NF) (X : ℝ) (bef aft j s : ℕ) : Prop :=
  bef < N.arcs.length ∧ aft < N.arcs.length ∧ j < N.arcs.length ∧
    ((N.F ztc Q).Nonempty →
      Before C Q N bef X ∧ After C Q N aft X ∧
      (s = 0 ↔ sideInArc ztwvb ztwus X) ∧
      ∀ q, q < N.arcs.length → sideInArc ztwlp ztwkp X →
        q = j)

/-- The five options emitted. -/
def spRam (R _bef6 aft6 j6 s6 befT aftT jT sT bef2 _aft2 j2 s2 : ℕ) : List ztbaeq :=
  [gOpt ztgkh aft6 befT, gOpt 1 aftT bef2,
    gOpt (if 0 < R ∧ s6 + sT = 0 then 1 else 0) j6 jT,
    gOpt ztkwq jT j2, gOpt ztkwp j6 j2]
theorem inArc_iff {X : ℝ} {bef aft j s : ℕ}
    (hK : KInfo C Q N X bef aft j s) (hne : (N.F ztc Q).Nonempty) :
    (s = 0 ↔ InArc C Q N X) ∧ (InArc C Q N X → inArcIdx C Q N X = j) := by
  obtain ⟨-, -, hj, hK⟩ := hK
  obtain ⟨-, -, hs, hu⟩ := hK hne
  refine ⟨⟨fun h0 => ⟨j, hj, hs.1 h0⟩, fun ⟨q, hq, hin⟩ => by_grind⟩,
    fun hin => ?_⟩
  zufio
  grind

/-- **The special pairs**: the options of the analyses are those of `zipSpO`. -/
theorem spRam_eq (hN : IsNF ztc Q N)
    (hP : C.P.Simple) {bef6 aft6 j6 s6 befT aftT jT sT bef2 aft2 j2 s2 : ℕ}
    (h6 : KInfo C Q N 6 bef6 aft6 j6 s6) (hT : KInfo C Q N ztbgn befT aftT jT sT)
    (h2 : KInfo C Q N ztcc bef2 aft2 j2 s2) :
    (spRam ztkdv bef6 aft6 j6 s6 befT aftT jT sT bef2 aft2 j2 s2).filterMap id =
      zipSp C Q N := by
  zuiv
  unfold zipSp zipSpO spRam
  zudgp
  · obtain ⟨b6, a6, j6l, K6⟩ := h6
    obtain ⟨bT, aT, jTl, KT⟩ := hT
    obtain ⟨b2, a2, j2l, K2⟩ := h2
    obtain ⟨B6, A6, -, -⟩ := K6 hne
    obtain ⟨BT, AT, -, -⟩ := KT hne
    obtain ⟨B2, A2, -, -⟩ := K2 hne
    obtain ⟨i6, x6⟩ := inArc_iff ⟨b6, a6, j6l, K6⟩ hne
    obtain ⟨iT, xT⟩ := inArc_iff ⟨bT, aT, jTl, KT⟩ hne
    obtain ⟨i2, x2⟩ := inArc_iff ⟨b2, a2, j2l, K2⟩ hne
    have eA6 : aftArc C Q N 6 = aft6 := by
      obtain ⟨a, b⟩ := aftArc_spec C Q N ⟨aft6, a6, A6⟩
      exact after_unique hN hP hne a a6 b A6
    have eAT : aftArc C Q N ztbgn = aftT := by
      obtain ⟨a, b⟩ := aftArc_spec C Q N ⟨aftT, aT, AT⟩
      exact after_unique hN hP hne a aT b AT
    have eBT : befArc C Q N ztbgn = befT := by
      obtain ⟨a, b⟩ := befArc_spec C Q N ⟨befT, bT, BT⟩
      exact before_unique hN hP hne a bT b BT
    have eB2 : befArc C Q N ztcc = bef2 := by
      obtain ⟨a, b⟩ := befArc_spec C Q N ⟨bef2, b2, B2⟩
      exact before_unique hN hP hne a b2 b B2
    have e1 : gOpt (if 0 < rT C then 1 else 0) aft6 befT = sp1 C Q N := by
      unfold sp1 gOpt
      by_cases hr : 0 < rT C
      · rw [ite_eq_left hr, ite_eq_right one_ne_zero, ite_eq_left by_grind, eA6, eBT]
      grind
    have e2 : gOpt 1 aftT bef2 = sp2 C Q N := by
      unfold sp2 gOpt
      rw [ite_eq_right one_ne_zero, ite_eq_left by_grind, eAT, eB2]
    have e3 : gOpt (if 0 < rT C ∧ s6 + sT = 0 then 1 else 0) j6 jT = sp3 C Q N := by
      unfold sp3 gOpt
      grind
    have e4 : gOpt ztkwq jT j2 = sp4 C Q N := by
      unfold sp4 gOpt
      grind
    have e5 : gOpt ztkwp j6 j2 = sp5 C Q N := by
      unfold sp5 gOpt
      grind
    grind
  · zuivn
    obtain ⟨b6, a6, j6l, -⟩ := h6
    obtain ⟨bT, aT, jTl, -⟩ := hT
    obtain ⟨b2, a2, j2l, -⟩ := h2
    have hn : ∀ g a b, a < N.arcs.length → b < N.arcs.length → gOpt g a b = none := by
      intro g a b ha hb
      unfold gOpt; split_ifs
      · rfl
      · exact normP_none_of_le_one hA by_omega by_omega
    have hs : ∀ o : Option _, o ∈ zipSpO C Q N → o = none := by
      intro o ho
      zucnc

      have n4 := normP_none_of_le_one hA ztxgz
        ztxha
      zujae
      simp only [zipSpO, List.mem_cons, List.mem_nil_iff, or_false] at ho
      zucef
      · unfold sp1; simp_all
      · unfold sp2; simp_all
      · unfold sp3; simp_all
      · unfold sp4; simp_all
      · unfold sp5; simp_all
    have hz : (zipSpO C Q N).filterMap id = [] := by
      rw [List.filterMap_eq_nil_iff]; grind
    unfold zipSpO at hz
    rw [hz, hn _ _ _ a6 bT, hn _ _ _ aT b2, hn _ _ _ j6l jTl, hn _ _ _ jTl j2l, hn _ _ _ j6l j2l]
    rfl
