module

public import Chazelle.Golf

public import Chazelle.Core.SweepIoAsm2
public import Chazelle.Core.NFBuildPassRam

/-!
# The sweep RAM (WP-D), the assembly (piece I), part 3: the program and the cost

`asmProg ev init loop`: save the side `sw 7` into `sw 99` and set `sw 7 := 0`; stage 0 (`initS`);
stages 2/3 (`ev`); the initialisation of the answers (`ansInit`); the side-0 initialisation
(`init`); `sw 11 := ALLOC`; the query loop (`loop`).  `asm_cost`: the sum of the costs of the parts
is at most `κ D (K₁ + K₂ + L + 1) (F γ + ⌈log₂ (K₁ + K₂ + L + 1)⌉ + 1)`.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim

@[expose] public section

/-- Save the side and select side `0` for stages 0–3. -/
def preS : List Instr := [.copyN (sw 99) (sw 7), .constN (sw 7) 0]

/-- **The program of the sweep.** -/
def asmProg (ev init loop : Stmt) : Stmt :=
  .seq (block preS) (.seq initS (.seq ev (.seq ansInit (.seq init
    (.seq (.instr (.copyN (sw 11) ALLOC)) loop)))))

/-- The constant of the assembly. -/
def asmK (κE κ0 κL : ℕ → ℕ) (D : ℕ) : ℕ := κE D + 238 * κ0 D + 10 * κL D + 1000

variable {P : Polygon} {W : ℕ}

theorem preS_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W (block preS) c c' k ∧ k = 2 ∧ c'.nreg (sw 99) = c.nreg (sw 7) ∧
      c'.nreg (sw 7) = 0 ∧ (∀ r, r ≠ sw 99 → r ≠ sw 7 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold preS
  simp only [sw, Nat.reduceAdd] at *
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩ <;> config_simp
  Θ upd, h1, h2

/-- Stage 0 keeps `sw 99`. -/
theorem initS_keep99 {c c' : Config} {k : ℕ} (h : Exec P W initS c c' k) :
    c'.nreg (sw 99) = c.nreg (sw 99) := by
  have hw : BuildRam.wrM (fun r => decide (r ≠ 240099)) initS = true := ⌖
  exact (BuildRam.exec_frameM h hw).1 _ (⊚ sw)

/-! ## The cost -/

theorem clog_mono {a b : ℕ} (h : a ≤ b) : Nat.clog 2 a ≤ Nat.clog 2 b :=
  Nat.clog_mono_right 2 h

/-- **The cost of the assembly.** -/
theorem asm_cost {κE κ0 κL f Λ l₁ n₁ nT K₁ K₂ Lq S Lg TLR A₁ k₂ k₃ k₄ k₅ k₇ : ℕ}
    (hn₁ : n₁ = K₁ + K₂ + 1) (hnT : nT = n₁ + Lq) (hl : l₁ ≤ Λ) (hS : S ≤ 16 * n₁)
    (hLg : Lg ≤ 16 * n₁) (hT : TLR ≤ l₁ + 6) (hA₁ : A₁ ≤ 3 * K₁ + 1)
    (h₂ : k₂ ≤ 220) (h₃ : k₃ ≤ κE * n₁ * (f + l₁ + 1)) (h₄ : k₄ ≤ 100 + 6 * (l₁ + 6))
    (h₅ : k₅ ≤ κ0 * (S + Lg + 2 * K₂ + 1) * (TLR + 1))
    (h₇ : k₇ ≤ κL * (Lq + 1) * (f + TLR + 1) + κL * (A₁ + 1) * (f + 1)) :
    2 + (k₂ + (k₃ + (k₄ + (k₅ + (1 + k₇))))) ≤
      (κE + 238 * κ0 + 10 * κL + 1000) * nT * (f + Λ + 1) := by
  set X := nT * (f + Λ + 1) with hX
  have hnT1 : 1 ≤ nT := ⋄
  have hX1 : Λ + 1 ≤ X := by
    have : 1 * (f + Λ + 1) ≤ nT * (f + Λ + 1) := Nat.mul_le_mul_right _ hnT1
    omega
  have e3 : k₃ ≤ κE * X := by
    calc k₃ ≤ κE * n₁ * (f + l₁ + 1) := h₃
      _ ≤ κE * nT * (f + Λ + 1) := by
        apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (⋄)) (⋄)
      _ = κE * X := Ρ hX, Nat.mul_assoc
  have e5 : k₅ ≤ 238 * κ0 * X := by
    calc k₅ ≤ κ0 * (S + Lg + 2 * K₂ + 1) * (TLR + 1) := h₅
      _ ≤ κ0 * (34 * nT) * (7 * (f + Λ + 1)) := by
        apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (⋄)) (⋄)
      _ = 238 * κ0 * X := by rw [hX]; ring
  have e7 : k₇ ≤ 10 * κL * X := by
    have a : κL * (Lq + 1) * (f + TLR + 1) ≤ κL * nT * (7 * (f + Λ + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (⋄)) (⋄)
    have b : κL * (A₁ + 1) * (f + 1) ≤ κL * (3 * nT) * (f + Λ + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (⋄)) (⋄)
    calc k₇ ≤ κL * nT * (7 * (f + Λ + 1)) + κL * (3 * nT) * (f + Λ + 1) := ⋄
      _ = 10 * κL * X := by rw [hX]; ring
  have e0 : 2 + k₂ + k₄ + 1 ≤ 1000 * X := ⋄
  calc 2 + (k₂ + (k₃ + (k₄ + (k₅ + (1 + k₇))))) ≤
        κE * X + 238 * κ0 * X + 10 * κL * X + 1000 * X := ⋄
    _ = (κE + 238 * κ0 + 10 * κL + 1000) * nT * (f + Λ + 1) := by rw [hX]; ring

end

end SweepIo

end Chazelle.Core
